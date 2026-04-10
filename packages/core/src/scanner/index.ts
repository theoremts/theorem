import {
  Project,
  Node,
  SyntaxKind,
  type SourceFile,
  type Expression,
} from 'ts-morph'
import type { AnyExpr, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, Param, Predicate, Sort } from '../parser/ir.js'
import type { ContractRegistry } from '../registry/index.js'
import { parseExpr } from '../parser/expr.js'
import { prettyExpr } from '../parser/pretty.js'
import { substituteExpr } from '../translator/substitution.js'
import { makeConst } from '../translator/variables.js'
import { toZ3 } from '../translator/expr.js'
import { check } from '../solver/index.js'

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

export type RiskLevel = 'critical' | 'high' | 'low'

export type RiskKind =
  | 'division-by-zero'
  | 'modulo-by-zero'
  | 'negative-sqrt'
  | 'log-of-nonpositive'
  | 'contract-violation'
  | 'array-out-of-bounds'
  | 'null-access'
  | 'empty-array-reduce'
  | 'integer-overflow'

export interface ScanRisk {
  kind: RiskKind
  level: RiskLevel
  description: string
  line: number
  counterexample?: Record<string, unknown> | undefined
}

export interface ScanFunctionResult {
  name?: string | undefined
  risks: ScanRisk[]
}

export interface ScanFileResult {
  filePath: string
  functions: ScanFunctionResult[]
  totalMs: number
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

export async function scanSource(
  source: string,
  filePath: string,
  ctx: Z3Context,
  registry?: ContractRegistry,
): Promise<ScanFileResult> {
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  const file = project.createSourceFile(filePath, source, { overwrite: true })

  const t0 = Date.now()
  const candidates = [
    ...collectCandidates(file),
    ...(registry ? collectContractViolations(file, registry) : []),
  ]

  // Group by function name
  const byFn = new Map<string, RawCandidate[]>()
  for (const c of candidates) {
    const key = c.functionName ?? '(anonymous)'
    const group = byFn.get(key) ?? []
    group.push(c)
    byFn.set(key, group)
  }

  const functions: ScanFunctionResult[] = []

  for (const [, group] of byFn) {
    const confirmed = await checkCandidates(group, ctx)
    if (confirmed.length > 0) {
      functions.push({ name: group[0]!.functionName, risks: confirmed })
    }
  }

  return { filePath, functions, totalMs: Date.now() - t0 }
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

interface RawPathCondition {
  expr: Expression  // ts-morph node — parsed lazily
  negated: boolean
}

interface RawCandidate {
  functionName?: string | undefined
  params: Param[]
  kind: RiskKind
  level: RiskLevel
  description: string
  trigger: Expr | null
  line: number
  pathConditions: RawPathCondition[]
}

// ---------------------------------------------------------------------------
// AST walker
// ---------------------------------------------------------------------------

const MATH_LOG = new Set(['Math.log', 'Math.log2', 'Math.log10', 'Math.log1p'])

function collectCandidates(file: SourceFile): RawCandidate[] {
  const out: RawCandidate[] = []

  // ── Division / modulo ──────────────────────────────────────────────────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.BinaryExpression)) {
    const op = node.getOperatorToken().getText()
    if (op !== '/' && op !== '%') continue

    const denominator = node.getRight()
    if (Node.isNumericLiteral(denominator) && Number(denominator.getLiteralValue()) !== 0) continue

    const { functionName, params } = enclosingFnInfo(node)
    out.push({
      functionName,
      params,
      kind: op === '/' ? 'division-by-zero' : 'modulo-by-zero',
      level: 'critical',
      description: `${op === '/' ? 'division' : 'modulo'} by \`${denominator.getText().trim()}\``,
      trigger: parseExpr(denominator as Expression),
      line: node.getStartLineNumber(),
      pathConditions: collectPathConditions(node),
    })
  }

  // ── Math.sqrt / Math.log* ──────────────────────────────────────────────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const callee = node.getExpression().getText()
    const isSqrt = callee === 'Math.sqrt'
    const isLog  = MATH_LOG.has(callee)
    if (!isSqrt && !isLog) continue

    const argNode = node.getArguments()[0]
    if (argNode === undefined) continue
    if (Node.isNumericLiteral(argNode)) {
      const v = Number(argNode.getLiteralValue())
      if (isSqrt && v >= 0) continue
      if (isLog  && v > 0) continue
    }

    const { functionName, params } = enclosingFnInfo(node)
    out.push({
      functionName,
      params,
      kind: isSqrt ? 'negative-sqrt' : 'log-of-nonpositive',
      level: 'high',
      description: `${callee}(\`${argNode.getText().trim()}\`)`,
      trigger: parseExpr(argNode as Expression),
      line: node.getStartLineNumber(),
      pathConditions: collectPathConditions(node),
    })
  }

  // ── Array out of bounds: arr[i] where i is not a literal ──────────────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.ElementAccessExpression)) {
    const argNode = node.getArgumentExpression()
    if (argNode === undefined) continue
    // Skip literal indices (numeric or string)
    if (Node.isNumericLiteral(argNode) || Node.isStringLiteral(argNode)) continue

    const { functionName, params } = enclosingFnInfo(node)
    out.push({
      functionName,
      params,
      kind: 'array-out-of-bounds',
      level: 'high',
      description: `array access \`${node.getText().trim()}\` — index may be out of bounds`,
      trigger: parseExpr(argNode as Expression),
      line: node.getStartLineNumber(),
      pathConditions: collectPathConditions(node),
    })
  }

  // ── Null/undefined access: x.foo where x could be null/undefined ──────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.PropertyAccessExpression)) {
    // Skip optional chaining (x?.foo)
    if (node.hasQuestionDotToken()) continue

    const objExpr = node.getExpression()
    // Only check simple identifiers (parameters)
    if (!Node.isIdentifier(objExpr)) continue

    const paramName = objExpr.getText()
    const { functionName, params } = enclosingFnInfo(node)

    // Check if the parameter type includes null or undefined
    const fnNode = findEnclosingFunction(node)
    if (fnNode === undefined) continue

    const paramDecl = getParamDeclarations(fnNode).find(p => p.getName() === paramName)
    if (paramDecl === undefined) continue

    const typeNode = paramDecl.getTypeNode()
    if (typeNode === undefined) continue

    const typeText = typeNode.getText()
    const hasQuestionToken = paramDecl.hasQuestionToken()
    if (!hasQuestionToken && !typeText.includes('null') && !typeText.includes('undefined')) continue

    // Check if there's a guard before this access (early-exit on null/undefined)
    if (hasNullGuardBefore(node, paramName)) continue

    out.push({
      functionName,
      params,
      kind: 'null-access',
      level: 'critical',
      description: `\`${paramName}.${node.getName()}\` — \`${paramName}\` may be null/undefined (type: ${typeText})`,
      trigger: null,  // no Z3 check needed
      line: node.getStartLineNumber(),
      pathConditions: [],
    })
  }

  // ── Integer overflow: a ** b (non-small exponent) or a * b * c ────────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.BinaryExpression)) {
    const op = node.getOperatorToken().getText()

    if (op === '**') {
      // Flag exponentiation where the exponent is NOT a small literal (0-10)
      const exponent = node.getRight()
      if (Node.isNumericLiteral(exponent)) {
        const val = Number(exponent.getLiteralValue())
        if (val >= 0 && val <= 10) continue
      }
      const { functionName, params } = enclosingFnInfo(node)
      out.push({
        functionName,
        params,
        kind: 'integer-overflow',
        level: 'low',
        description: `exponentiation \`${node.getText().trim()}\` may overflow Number.MAX_SAFE_INTEGER`,
        trigger: null,  // pattern-only: Z3 overflow check is done separately
        line: node.getStartLineNumber(),
        pathConditions: [],
      })
      continue
    }

    if (op === '*') {
      // Flag chained multiplications: a * b * c (3+ terms)
      // Check if parent is also a multiplication — if so, the parent will be flagged
      const parent = node.getParent()
      if (Node.isBinaryExpression(parent) && parent.getOperatorToken().getText() === '*') continue

      // Count multiplication depth
      let depth = 1
      let cursor: Expression = node.getLeft() as Expression
      while (Node.isBinaryExpression(cursor) && cursor.getOperatorToken().getText() === '*') {
        depth++
        cursor = cursor.getLeft() as Expression
      }
      if (depth < 2) continue  // need 3+ terms (a * b * c)

      const { functionName, params } = enclosingFnInfo(node)
      out.push({
        functionName,
        params,
        kind: 'integer-overflow',
        level: 'low',
        description: `chained multiplication \`${node.getText().trim()}\` may overflow Number.MAX_SAFE_INTEGER`,
        trigger: null,
        line: node.getStartLineNumber(),
        pathConditions: [],
      })
    }
  }

  // ── Empty array reduce: arr.reduce(cb) without initial value ──────────────
  for (const node of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeExpr = node.getExpression()
    if (!Node.isPropertyAccessExpression(calleeExpr)) continue
    if (calleeExpr.getName() !== 'reduce') continue

    const args = node.getArguments()
    // .reduce() with only 1 argument (callback, no initial value) throws on empty arrays
    if (args.length !== 1) continue

    const { functionName, params } = enclosingFnInfo(node)
    const arrText = calleeExpr.getExpression().getText().trim()
    out.push({
      functionName,
      params,
      kind: 'empty-array-reduce',
      level: 'high',
      description: `\`${arrText}.reduce()\` called without initial value — throws if array is empty`,
      trigger: null,  // no Z3 check needed
      line: node.getStartLineNumber(),
      pathConditions: [],
    })
  }

  return out
}

// ---------------------------------------------------------------------------
// Contract violation detection — calls to proof() functions outside of proof()
// ---------------------------------------------------------------------------

function collectContractViolations(
  file: SourceFile,
  registry: ContractRegistry,
): RawCandidate[] {
  const out: RawCandidate[] = []

  for (const node of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeName = node.getExpression().getText()
    // Resolve dotted names: this.service.method → method, service.method → method
    const resolvedName = registry.has(calleeName)
      ? calleeName
      : calleeName.includes('.') ? calleeName.slice(calleeName.lastIndexOf('.') + 1) : null
    const contract = resolvedName ? registry.get(resolvedName) : undefined
    if (!contract) continue

    // Skip calls inside proof() — those are handled by the translator
    if (isInsideProof(node)) continue

    const args = node.getArguments()
    const { functionName, params } = enclosingFnInfo(node)

    // Build substitution: callee param names → argument expressions (parsed to IR)
    const mapping = new Map<string, Expr>()
    for (let i = 0; i < Math.min(contract.params.length, args.length); i++) {
      const parsed = parseExpr(args[i]! as Expression)
      if (parsed !== null) {
        mapping.set(contract.params[i]!.name, parsed)
      }
    }

    // For each requires, check if the arguments satisfy it
    for (const req of contract.requires) {
      if (typeof req === 'string') continue
      const substituted = substituteExpr(req, mapping)
      const argTexts = args.map(a => a.getText().trim()).join(', ')

      out.push({
        functionName,
        params,
        kind: 'contract-violation',
        level: 'critical',
        description: `${calleeName}(${argTexts}) may violate: ${prettyExpr(req)}`,
        trigger: substituted,
        line: node.getStartLineNumber(),
        pathConditions: collectPathConditions(node),
      })
    }
  }

  return out
}

/** Check if a node is inside a proof() or proof.fn() call. */
function isInsideProof(node: Node): boolean {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isCallExpression(current)) {
      const callee = current.getExpression().getText()
      if (callee === 'proof' || callee === 'proof.fn') return true
    }
    current = current.getParent()
  }
  return false
}

// ---------------------------------------------------------------------------
// Path condition collection — tracks guards that constrain the risky expression
// ---------------------------------------------------------------------------

/**
 * Walks up the AST from a risky node and collects conditions that must hold
 * for the node to be reached:
 *
 *   if (cond) { ... <node> ... }      →  assume cond
 *   if (cond) { ... } else { <node> } →  assume !cond
 *   if (cond) return/throw            →  assume !cond  (early-exit guard)
 */
function collectPathConditions(startNode: Node): RawPathCondition[] {
  const conditions: RawPathCondition[] = []
  let current = startNode
  let parent  = startNode.getParent()

  while (parent !== undefined) {
    // Stop at function boundaries
    if (
      Node.isFunctionDeclaration(parent) || Node.isArrowFunction(parent) ||
      Node.isMethodDeclaration(parent)   || Node.isFunctionExpression(parent)
    ) break

    // ── If-statement: determine which branch we're in ────────────────────────
    if (Node.isIfStatement(parent)) {
      const thenStmt = parent.getThenStatement()
      const elseStmt = parent.getElseStatement()
      const condExpr  = parent.getExpression() as Expression

      if (nodeContains(thenStmt, current)) {
        // Pre-split && so that one unparseable operand doesn't discard the others
        for (const part of splitAnd(condExpr)) {
          conditions.push({ expr: part, negated: false })
        }
      } else if (elseStmt !== undefined && nodeContains(elseStmt, current)) {
        for (const part of splitAnd(condExpr)) {
          conditions.push({ expr: part, negated: true })
        }
      }
    }

    // ── Block: collect early-exit guards before current ──────────────────────
    if (Node.isBlock(parent)) {
      for (const stmt of parent.getStatements()) {
        if (stmt.getEnd() > current.getStart()) break  // past current node

        if (Node.isIfStatement(stmt) && stmt.getElseStatement() === undefined) {
          if (isUnconditionalExit(stmt.getThenStatement())) {
            // if (cond) return/throw → !cond holds from here onward
            // Pre-split && for the same reason
            for (const part of splitAnd(stmt.getExpression() as Expression)) {
              conditions.push({ expr: part, negated: true })
            }
          }
        }
      }
    }

    current = parent
    parent  = current.getParent()
  }

  return conditions
}

function nodeContains(ancestor: Node, descendant: Node): boolean {
  return ancestor.getStart() <= descendant.getStart() &&
         descendant.getEnd()  <= ancestor.getEnd()
}

function isUnconditionalExit(stmt: Node): boolean {
  if (Node.isReturnStatement(stmt) || Node.isThrowStatement(stmt)) return true
  if (Node.isBlock(stmt)) {
    const stmts = stmt.getStatements()
    if (stmts.length === 0) return false
    const last = stmts[stmts.length - 1]!
    return Node.isReturnStatement(last) || Node.isThrowStatement(last)
  }
  return false
}

// ---------------------------------------------------------------------------
// Z3 check — confirms which candidates are actually reachable
// ---------------------------------------------------------------------------

async function checkCandidates(
  candidates: RawCandidate[],
  ctx: Z3Context,
): Promise<ScanRisk[]> {
  const confirmed: ScanRisk[] = []
  const seen = new Set<string>()

  for (const c of candidates) {
    // Pattern-only risks (no Z3 needed): report directly
    if (c.trigger === null) {
      const key = `${c.kind}::${c.line}`
      if (seen.has(key)) continue
      seen.add(key)
      confirmed.push({
        kind: c.kind,
        level: c.level,
        description: c.description,
        line: c.line,
      })
      continue
    }

    // Deduplicate: same kind + trigger text + line
    const key = `${c.kind}:${prettyExpr(c.trigger)}:${c.line}`
    if (seen.has(key)) continue
    seen.add(key)

    // Parse path conditions to IR (best-effort; unparseable ones are skipped)
    const parsedConditions: Array<{ expr: Expr; negated: boolean }> = []
    for (const raw of c.pathConditions) {
      const parsed = parseExpr(raw.expr)
      if (parsed !== null) parsedConditions.push({ expr: parsed, negated: raw.negated })
    }

    // Build Z3 variables (trigger + all path condition identifiers)
    const vars = buildVars(c.trigger, parsedConditions.map(p => p.expr), c.params, ctx)

    // Domain constraints: .length >= 0
    const domainConstraints: Bool<'main'>[] = []
    for (const [name, expr] of vars) {
      if (name.endsWith('.length')) {
        try { domainConstraints.push((expr as any).ge(ctx.Real.val(0))) } catch { /* skip */ }
      }
    }

    // Build assumptions from path conditions + domain constraints
    const assumptions: Bool<'main'>[] = [...domainConstraints]
    for (const pc of parsedConditions) {
      try {
        const z3 = toZ3(pc.expr, vars, ctx)
        if (z3 === null) continue
        assumptions.push(pc.negated ? ctx.Not(z3 as Bool<'main'>) : z3 as Bool<'main'>)
      } catch { /* skip untranslatable condition */ }
    }

    let goalZ3
    try { goalZ3 = riskCondition(c.kind, c.trigger, vars, ctx) } catch { continue }
    if (goalZ3 === null) continue

    let result
    try {
      result = await check({ variables: vars, assumptions, goal: goalZ3 as Bool<'main'> })
    } catch { continue }

    if (result.status === 'disproved') {
      confirmed.push({
        kind: c.kind,
        level: c.level,
        description: c.description,
        line: c.line,
        counterexample: result.counterexample,
      })
    }
  }

  return confirmed
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function riskCondition(
  kind: RiskKind,
  trigger: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
): AnyExpr<'main'> | null {
  const z3 = toZ3(trigger, vars, ctx)
  if (z3 === null) return null
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const a = z3 as any
  switch (kind) {
    case 'division-by-zero':
    case 'modulo-by-zero':        return a.eq(ctx.Real.val(0))
    case 'negative-sqrt':         return a.lt(ctx.Real.val(0))
    case 'log-of-nonpositive':    return a.le(ctx.Real.val(0))
    case 'contract-violation':    return ctx.Not(z3 as Bool<'main'>)  // can the requires be false?
    case 'array-out-of-bounds':   return a.lt(ctx.Real.val(0))        // can the index be negative?
    case 'null-access':           return null  // pattern-only, no Z3
    case 'empty-array-reduce':    return null  // pattern-only, no Z3
    case 'integer-overflow':      return null  // pattern-only, no Z3
  }
}

function buildVars(
  trigger: Expr,
  condExprs: Expr[],
  params: Param[],
  ctx: Z3Context,
): Map<string, AnyExpr<'main'>> {
  const vars = new Map<string, AnyExpr<'main'>>()
  for (const p of params) vars.set(p.name, makeConst(p.name, p.sort, ctx))
  for (const name of collectIdents(trigger)) {
    if (!vars.has(name)) vars.set(name, makeConst(name, 'real', ctx))
  }
  for (const expr of condExprs) {
    for (const name of collectIdents(expr)) {
      if (!vars.has(name)) vars.set(name, makeConst(name, 'real', ctx))
    }
  }
  return vars
}

/** Split ts-morph `a && b && c` → [a, b, c] before parsing to IR.
 *  Allows partial use when one operand is unparseable (e.g. `x != null`). */
function splitAnd(expr: Expression): Expression[] {
  if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === '&&') {
    return [
      ...splitAnd(expr.getLeft() as Expression),
      ...splitAnd(expr.getRight() as Expression),
    ]
  }
  return [expr]
}

function collectIdents(expr: Expr): string[] {
  const out: string[] = []
  walkIdents(expr, out)
  return out
}

function walkIdents(expr: Expr, out: string[]): void {
  switch (expr.kind) {
    case 'ident':          out.push(expr.name); break
    case 'binary':         walkIdents(expr.left, out); walkIdents(expr.right, out); break
    case 'unary':          walkIdents(expr.operand, out); break
    case 'ternary':        walkIdents(expr.condition, out); walkIdents(expr.then, out); walkIdents(expr.else, out); break
    case 'call':           expr.args.forEach(a => walkIdents(a, out)); break
    case 'member':         walkIdents(expr.object, out); break
    case 'element-access': walkIdents(expr.object, out); walkIdents(expr.index, out); break
    case 'quantifier':     walkIdents(expr.body, out); break
    case 'array':          expr.elements.forEach(e => walkIdents(e, out)); break
    case 'object':         expr.properties.forEach(p => walkIdents(p.value, out)); break
    case 'spread':         walkIdents(expr.operand, out); break
    case 'template':       expr.parts.forEach(p => { if (typeof p !== 'string') walkIdents(p, out) }); break
    case 'literal':        break
  }
}

function tsTypeToSort(type: string): Sort {
  switch (type.trim()) {
    case 'boolean': return 'bool'
    case 'bigint':  return 'int'
    case 'number':  return 'real'
    default:        return 'real'
  }
}

/** Find the enclosing function node (for accessing its parameter declarations). */
function findEnclosingFunction(node: Node): Node | undefined {
  let current = node.getParent()
  while (current !== undefined) {
    if (
      Node.isFunctionDeclaration(current) || Node.isMethodDeclaration(current) ||
      Node.isFunctionExpression(current) || Node.isArrowFunction(current)
    ) return current
    current = current.getParent()
  }
  return undefined
}

/** Get parameter declarations from a function node. */
function getParamDeclarations(fnNode: Node) {
  if (
    Node.isFunctionDeclaration(fnNode) || Node.isMethodDeclaration(fnNode) ||
    Node.isFunctionExpression(fnNode) || Node.isArrowFunction(fnNode)
  ) {
    return fnNode.getParameters()
  }
  return []
}

/**
 * Check if there's a null guard before the given node for the specified parameter.
 * Looks for patterns like: if (x == null) return; / if (!x) return; / if (x === undefined) return;
 */
function hasNullGuardBefore(node: Node, paramName: string): boolean {
  // Walk up to find the enclosing block
  let current: Node | undefined = node
  while (current !== undefined) {
    const parent = current.getParent()
    if (parent !== undefined && Node.isBlock(parent)) {
      for (const stmt of parent.getStatements()) {
        if (stmt.getEnd() > node.getStart()) break
        if (Node.isIfStatement(stmt) && stmt.getElseStatement() === undefined) {
          if (isUnconditionalExit(stmt.getThenStatement())) {
            const condText = stmt.getExpression().getText().trim()
            // Matches: x == null, x === null, x === undefined, x == undefined, !x
            if (
              condText === `${paramName} == null` ||
              condText === `${paramName} === null` ||
              condText === `${paramName} === undefined` ||
              condText === `${paramName} == undefined` ||
              condText === `!${paramName}` ||
              condText === `${paramName} == null || ${paramName} == undefined` ||
              condText === `${paramName} === null || ${paramName} === undefined`
            ) return true
          }
        }
      }
    }
    // Also check if we're inside an if-then where the condition guards against null
    if (parent !== undefined && Node.isIfStatement(parent)) {
      const thenStmt = parent.getThenStatement()
      if (nodeContains(thenStmt, node)) {
        const condText = parent.getExpression().getText().trim()
        // Inside if (x != null) / if (x !== null) / if (x) / if (x !== undefined)
        if (
          condText === `${paramName} != null` ||
          condText === `${paramName} !== null` ||
          condText === `${paramName} !== undefined` ||
          condText === `${paramName} != undefined` ||
          condText === paramName
        ) return true
      }
    }
    current = parent
  }
  return false
}

function enclosingFnInfo(node: Node): { functionName?: string | undefined; params: Param[] } {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isFunctionDeclaration(current) || Node.isMethodDeclaration(current) || Node.isFunctionExpression(current)) {
      return {
        functionName: current.getName() ?? undefined,
        params: current.getParameters().map(p => ({
          name: p.getName(),
          sort: p.getTypeNode() ? tsTypeToSort(p.getTypeNode()!.getText()) : 'real' as Sort,
        })),
      }
    }
    if (Node.isArrowFunction(current)) {
      const parent = current.getParent()
      const name = Node.isVariableDeclaration(parent) ? parent.getName() : undefined
      return {
        functionName: name,
        params: current.getParameters().map(p => ({
          name: p.getName(),
          sort: p.getTypeNode() ? tsTypeToSort(p.getTypeNode()!.getText()) : 'real' as Sort,
        })),
      }
    }
    current = current.getParent()
  }
  return { params: [] }
}
