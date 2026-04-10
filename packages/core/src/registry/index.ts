import type { FunctionIR, Param, Predicate, Sort } from '../parser/ir.js'

/**
 * A contract specification for a named function — the "API" that callers must respect.
 */
export interface FunctionContract {
  name: string
  params: Param[]
  returnSort: Sort
  requires: Predicate[]
  ensures: Predicate[]
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
      })
    }
  }

  return registry
}
