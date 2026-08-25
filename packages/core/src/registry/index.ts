import type { FunctionIR, Param, Predicate, Sort } from '../parser/ir.js'
import { resolveImportedFiles } from '../parser/module-consts.js'
import { isAbsolute } from 'node:path'

/**
 * A contract specification for a named function — the "API" that callers must respect.
 */
export interface FunctionContract {
  name: string
  params: Param[]
  returnSort: Sort
  requires: Predicate[]
  ensures: Predicate[]
  /** Defining file for inline-extracted contracts; undefined for declares
   *  (which are global by design). Used to prevent name collisions. */
  sourceFile?: string | undefined
}

/**
 * Maps function names to their contracts.
 * Built from all `proof()` calls across the codebase before verification begins.
 */
export type ContractRegistry = Map<string, FunctionContract>

/**
 * Builds a contract registry from a list of FunctionIR entries.
 * Typically called with all IRs from all files before verification.
 */
export function buildRegistry(irList: FunctionIR[]): ContractRegistry {
  const registry: ContractRegistry = new Map()

  for (const ir of irList) {
    if (ir.name === undefined) continue
    if (ir.contracts.length === 0) continue

    const requires: Predicate[] = []
    const ensures: Predicate[] = []

    for (const c of ir.contracts) {
      if (c.kind === 'requires') requires.push(c.predicate)
      if (c.kind === 'ensures')  ensures.push(c.predicate)
    }

    // Only register functions that have at least one requires or ensures
    if (requires.length > 0 || ensures.length > 0) {
      registry.set(ir.name, {
        name: ir.name,
        params: ir.params,
        returnSort: ir.returnSort,
        requires,
        ensures,
        sourceFile: ir.sourceFile,
      })
    }
  }

  return registry
}

/**
 * Restricts a global registry to the contracts VISIBLE from one file:
 *  - a function DEFINED in this file (top-level declaration or const arrow)
 *    shadows any same-named contract from another file — calls target the
 *    local, possibly uncontracted one;
 *  - an IMPORTED name only accepts a contract whose sourceFile matches the
 *    resolved import target (relative + tsconfig-alias, one hop);
 *  - contracts without a sourceFile (declare() packages) stay global;
 *  - prototype/method keys are never filtered (receiver-resolved).
 * Without this, `subtotal` in one file inherited `subtotal`'s contract from
 * an unrelated file — phantom failures AND unsound assumed ensures.
 */
export function filterRegistryForFile(
  source: string,
  fileName: string,
  registry: ContractRegistry,
): ContractRegistry {
  if (registry.size === 0) return registry
  // In-memory names (test.ts, input.ts) carry no identity — only real
  // absolute paths compare meaningfully (same rule as const facts).
  if (!isAbsolute(fileName)) return registry
  let localNames: Set<string>
  const importTargets = new Map<string, string | null>()
  try {
    // Lightweight syntactic scan — no ts-morph needed for names/imports.
    localNames = new Set<string>()
    const fnRe = /^\s*(?:export\s+)?(?:async\s+)?function\s+(\w+)/gm
    const constFnRe = /^\s*(?:export\s+)?const\s+(\w+)\s*=\s*(?:async\s*)?(?:\(|function\b|[\w$]+\s*=>)/gm
    let m: RegExpExecArray | null
    while ((m = fnRe.exec(source)) !== null) localNames.add(m[1]!)
    while ((m = constFnRe.exec(source)) !== null) localNames.add(m[1]!)

    const importRe = /import\s+(?:type\s+)?\{([^}]*)\}\s*from\s*['"]([^'"]+)['"]/g
    while ((m = importRe.exec(source)) !== null) {
      const spec = m[2]!
      let resolved: string | null = null
      try {
        resolved = resolveImportedFiles(`import {x} from '${spec}'`, fileName)[0] ?? null
      } catch { resolved = null }
      for (const piece of m[1]!.split(',')) {
        const name = (piece.split(' as ').pop() ?? '').trim()
        if (name.length > 0) importTargets.set(name, resolved)
      }
    }
  } catch {
    return registry
  }

  const out: ContractRegistry = new Map()
  for (const [key, contract] of registry) {
    if (!key.includes('.prototype.') && contract.sourceFile !== undefined && isAbsolute(contract.sourceFile) && contract.sourceFile !== fileName) {
      if (localNames.has(key)) continue
      const target = importTargets.get(key)
      if (target !== undefined && target !== null && target !== contract.sourceFile) continue
    }
    out.set(key, contract)
  }
  return out
}
