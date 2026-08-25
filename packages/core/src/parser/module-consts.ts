import { readFileSync, existsSync } from 'node:fs'
import { resolve, dirname, join, isAbsolute } from 'node:path'
import { Project, Node, SyntaxKind, type SourceFile, type Expression } from 'ts-morph'
import type { Expr, FunctionIR } from './ir.js'

/**
 * Module-constant resolution — the fact that `ZERO` is zero, without asking.
 *
 * A module-scope `const` whose initializer is a TRUSTED literal shape
 * (numeric literal, `new Decimal(lit)`, or arithmetic over already-resolved
 * constants) is a value the verifier can know. This module resolves them:
 *   - same-file module-scope constants,
 *   - named imports followed ONE hop (relative specifiers and tsconfig
 *     `paths` aliases), no re-export chasing.
 *
 * The extractor injects the resolved values as assume facts
 * (`X === value`) into every function that references the name, replacing
 * the manual `assume(ZERO.equals(0))` ritual. Only `const` declarations
 * qualify — a `let` is not a constant, and any initializer outside the
 * trusted shapes is left opaque (free variable, honest as before).
 */

// Dedicated lightweight project for reading imported files
let constProject: Project | null = null
function getConstProject(): Project {
  if (constProject === null) {
    constProject = new Project({
      useInMemoryFileSystem: false,
      skipFileDependencyResolution: true,
      compilerOptions: { allowJs: false, skipLibCheck: true },
    })
  }
  return constProject
}

// Caches — per-process; verify runs are short-lived
const fileFactsCache = new Map<string, Map<string, ConstValue>>()
const tsconfigCache = new Map<string, { baseUrl: string; paths: Record<string, string[]> } | null>()

/** A resolved module constant: numeric or string literal. */
export type ConstValue = number | string

/** Folds a trusted-constant initializer to its value, or null. */
function foldConstExpr(node: Expression, known: Map<string, ConstValue>): ConstValue | null {
  if (Node.isParenthesizedExpression(node)) return foldConstExpr(node.getExpression(), known)
  if (Node.isAsExpression(node)) return foldConstExpr(node.getExpression(), known)
  if (Node.isNumericLiteral(node)) return Number(node.getLiteralValue())
  // String constants: `const STATUS = "paid"` — a fact usable wherever the
  // string field/param machinery compares against it.
  if (Node.isStringLiteral(node) || Node.isNoSubstitutionTemplateLiteral(node)) {
    return node.getLiteralValue()
  }
  if (Node.isPrefixUnaryExpression(node) && node.getOperatorToken() === SyntaxKind.MinusToken) {
    const inner = foldConstExpr(node.getOperand() as Expression, known)
    return inner === null || typeof inner !== 'number' ? null : -inner
  }
  if (Node.isIdentifier(node)) {
    const v = known.get(node.getText())
    return v ?? null
  }
  // new Decimal(lit) — numerically the constant itself
  if (Node.isNewExpression(node)) {
    const callee = node.getExpression().getText()
    const args = node.getArguments() ?? []
    if ((callee === "Decimal" || callee.endsWith(".Decimal")) && args.length === 1) {
      const inner = foldConstExpr(args[0] as Expression, known)
      return typeof inner === "number" ? inner : null
    }
    return null
  }
  if (Node.isBinaryExpression(node)) {
    const op = node.getOperatorToken().getText()
    if (op !== '+' && op !== '-' && op !== '*' && op !== '/') return null
    const l = foldConstExpr(node.getLeft(), known)
    const r = foldConstExpr(node.getRight(), known)
    if (typeof l !== "number" || typeof r !== "number") return null
    switch (op) {
      case '+': return l + r
      case '-': return l - r
      case '*': return l * r
      case '/': return r === 0 ? null : l / r
    }
  }
  return null
}

/** Module-scope `const NAME = <trusted literal>` facts declared in a file. */
function collectOwnConsts(file: SourceFile): Map<string, ConstValue> {
  const facts = new Map<string, ConstValue>()
  for (const stmt of file.getStatements()) {
    if (!Node.isVariableStatement(stmt)) continue
    if (stmt.getDeclarationKind() !== 'const') continue
    for (const decl of stmt.getDeclarations()) {
      const nameNode = decl.getNameNode()
      if (!Node.isIdentifier(nameNode)) continue
      const init = decl.getInitializer()
      if (init === undefined) continue
      const v = foldConstExpr(init, facts)
      if (v !== null && (typeof v === "string" || Number.isFinite(v))) facts.set(nameNode.getText(), v)
    }
  }
  return facts
}

/** Loads tsconfig `paths` mapping for alias resolution, walking up from dir. */
function loadTsconfigPaths(startDir: string): { baseUrl: string; paths: Record<string, string[]> } | null {
  const cached = tsconfigCache.get(startDir)
  if (cached !== undefined) return cached
  let dir = startDir
  for (let i = 0; i < 12; i++) {
    const cfgPath = join(dir, 'tsconfig.json')
    if (existsSync(cfgPath)) {
      try {
        const raw = readFileSync(cfgPath, 'utf-8')
        // Tolerant parse: strip comments if plain JSON.parse fails
        let cfg: { compilerOptions?: { baseUrl?: string; paths?: Record<string, string[]> } }
        try {
          cfg = JSON.parse(raw) as typeof cfg
        } catch {
          const stripped = raw.replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '')
          cfg = JSON.parse(stripped) as typeof cfg
        }
        const paths = cfg.compilerOptions?.paths
        if (paths !== undefined) {
          const result = { baseUrl: resolve(dir, cfg.compilerOptions?.baseUrl ?? '.'), paths }
          tsconfigCache.set(startDir, result)
          return result
        }
        // tsconfig without paths — may extend another; keep walking up
      } catch { /* unreadable config — keep walking */ }
    }
    const parent = dirname(dir)
    if (parent === dir) break
    dir = parent
  }
  tsconfigCache.set(startDir, null)
  return null
}

/** Resolves an import specifier to an absolute .ts file, or null. */
function resolveSpecifier(spec: string, fromFile: string): string | null {
  const tryFile = (base: string): string | null => {
    for (const cand of [`${base}.ts`, `${base}.tsx`, join(base, 'index.ts')]) {
      if (existsSync(cand)) return cand
    }
    return null
  }
  if (spec.startsWith('.')) {
    return tryFile(resolve(dirname(fromFile), spec))
  }
  const cfg = loadTsconfigPaths(dirname(fromFile))
  if (cfg !== null) {
    for (const [pattern, targets] of Object.entries(cfg.paths)) {
      const star = pattern.indexOf('*')
      if (star < 0) {
        if (spec === pattern && targets[0] !== undefined) {
          const hit = tryFile(resolve(cfg.baseUrl, targets[0].replace('*', '')))
          if (hit !== null) return hit
        }
        continue
      }
      const prefix = pattern.slice(0, star)
      const suffix = pattern.slice(star + 1)
      if (spec.startsWith(prefix) && spec.endsWith(suffix)) {
        const middle = spec.slice(prefix.length, spec.length - suffix.length)
        for (const target of targets) {
          const hit = tryFile(resolve(cfg.baseUrl, target.replace('*', middle)))
          if (hit !== null) return hit
        }
      }
    }
  }
  return null
}

/** Const facts exported by a real file on disk (cached). */
function collectFileConsts(absPath: string): Map<string, ConstValue> {
  const cached = fileFactsCache.get(absPath)
  if (cached !== undefined) return cached
  let facts = new Map<string, ConstValue>()
  try {
    const project = getConstProject()
    const file = project.getSourceFile(absPath) ?? project.addSourceFileAtPath(absPath)
    facts = collectOwnConsts(file)
  } catch { /* unreadable — no facts */ }
  fileFactsCache.set(absPath, facts)
  return facts
}

/**
 * All trusted-constant facts visible in `file`: its own module-scope consts
 * plus named imports resolved one hop through relative/alias specifiers.
 * `fileName` must be the file's real absolute path for import resolution;
 * in-memory names (input.ts) resolve nothing beyond same-file consts.
 */
/** Collects every identifier name occurring in an Expr tree (leaves of member chains included). */
function collectIdents(e: Expr | undefined, out: Set<string>): void {
  if (e === undefined || typeof e !== 'object') return
  switch (e.kind) {
    case 'ident':          out.add(e.name); break
    case 'binary':         collectIdents(e.left, out); collectIdents(e.right, out); break
    case 'unary':          collectIdents(e.operand, out); break
    case 'ternary':        collectIdents(e.condition, out); collectIdents(e.then, out); collectIdents(e.else, out); break
    case 'call':           e.args.forEach(a => collectIdents(a, out)); collectIdents(e.recv, out); out.add(e.callee.split('.')[0]!); break
    case 'member':         collectIdents(e.object, out); break
    case 'element-access': collectIdents(e.object, out); collectIdents(e.index, out); break
    case 'quantifier':     collectIdents(e.body, out); break
    case 'array':          e.elements.forEach(el => collectIdents(el, out)); break
    case 'object':         e.properties.forEach(p => collectIdents(p.value, out)); break
    case 'spread':         collectIdents(e.operand, out); break
    default: break
  }
}

/**
 * Injects resolved module-constant values as assume facts (`X === value`)
 * into every IR that references the constant's name — unless a parameter
 * shadows it. Facts are prepended so downstream snapshots see them.
 */
export function injectModuleConstFacts(file: SourceFile, fileName: string, irs: FunctionIR[]): void {
  if (irs.length === 0) return
  const facts = collectModuleConstFacts(file, fileName)
  if (facts.size === 0) return

  for (const ir of irs) {
    const used = new Set<string>()
    collectIdents(ir.body, used)
    for (const c of ir.contracts) {
      if ('predicate' in c && typeof c.predicate === 'object' && c.predicate !== null) {
        collectIdents(c.predicate as Expr, used)
      }
    }
    if (ir.bodySteps !== undefined) {
      for (const s of ir.bodySteps) {
        if (s.kind === 'check' || s.kind === 'assume') {
          if (typeof s.predicate === 'object' && s.predicate !== null) collectIdents(s.predicate as Expr, used)
        } else if (s.kind === 'assign') {
          collectIdents(s.value, used)
        } else if (s.kind === 'if-assign') {
          collectIdents(s.condition, used); collectIdents(s.value, used); collectIdents(s.defaultValue, used)
        }
      }
    }
    if (ir.loops !== undefined) {
      for (const loop of ir.loops) {
        collectIdents(loop.condition, used)
        collectIdents(loop.body, used)
        loop.invariants.forEach(inv => collectIdents(inv, used))
        collectIdents(loop.decreases, used)
        loop.initializations?.forEach(init => collectIdents(init.value, used))
      }
    }

    const paramNames = new Set(ir.params.map(p => p.name))
    for (const [name, value] of facts) {
      if (!used.has(name) || paramNames.has(name)) continue
      const predicate = {
        kind: 'binary', op: '===',
        left: { kind: 'ident', name },
        right: { kind: 'literal', value },
      } as const
      ir.contracts.unshift({ kind: 'assume', predicate })
      // Functions WITH positional check/assume steps skip top-level assume
      // contracts ("already processed positionally") and a check at position
      // 0 snapshots assumptions before the contract loop — the fact must
      // ALSO lead the steps or check-only functions lose it (same silent
      // drop as schema facts).
      if (ir.bodySteps !== undefined) {
        ir.bodySteps.unshift({ kind: 'assume', predicate })
      }
    }
  }
}

export function collectModuleConstFacts(file: SourceFile, fileName: string): Map<string, ConstValue> {
  const facts = collectOwnConsts(file)
  if (!isAbsolute(fileName)) return facts

  for (const imp of file.getImportDeclarations()) {
    const named = imp.getNamedImports()
    if (named.length === 0) continue
    const spec = imp.getModuleSpecifierValue()
    const target = resolveSpecifier(spec, fileName)
    if (target === null) continue
    const exported = collectFileConsts(target)
    if (exported.size === 0) continue
    for (const ni of named) {
      const importedName = ni.getName()             // original exported name
      const localName = ni.getAliasNode()?.getText() ?? importedName
      const v = exported.get(importedName)
      if (v !== undefined && !facts.has(localName)) facts.set(localName, v)
    }
  }
  return facts
}

/**
 * Absolute paths of files DIRECTLY imported by `source` (one hop): relative
 * specifiers and tsconfig `paths` aliases, same resolution as const facts.
 * Used to pull callee contracts into the registry for small verify runs —
 * a single-file verify then sees its imports' requires/ensures instead of
 * treating cross-file calls as unknown.
 */
export function resolveImportedFiles(source: string, fileName: string): string[] {
  if (!isAbsolute(fileName)) return []
  const out: string[] = []
  const seen = new Set<string>()
  const re = /(?:import|export)\s[^'"]*?from\s*['"]([^'"]+)['"]|import\s*['"]([^'"]+)['"]/g
  let m: RegExpExecArray | null
  while ((m = re.exec(source)) !== null) {
    const spec = m[1] ?? m[2]
    if (spec === undefined) continue
    const target = resolveSpecifier(spec, fileName)
    if (target !== null && !seen.has(target)) {
      seen.add(target)
      out.push(target)
    }
  }
  return out
}
