import type { Bool, AnyExpr, Arith } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, FunctionIR, Param, Sort } from '../parser/ir.js'
import { prettyExpr } from '../parser/pretty.js'
import { createVariables } from '../translator/variables.js'
import { toZ3 } from '../translator/expr.js'
import { check } from '../solver/index.js'

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

export interface Suggestion {
  kind: 'requires' | 'ensures'
  text: string
  status: 'provable' | 'needs-precondition'
  description?: string | undefined
  counterexample?: Record<string, unknown> | undefined
}

export interface GuardSuggestion {
  kind: 'guard'
  condition: string
  action: 'throw' | 'return'
  equivalent: string
}

export interface ConditionalSuggestion {
  kind: 'conditional'
  requires: string
  enables: string
}

export interface SuggestFunctionResult {
  name?: string | undefined
  params: string[]
  suggestions: Suggestion[]
  conditionals: ConditionalSuggestion[]
  guards: GuardSuggestion[]
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

export async function suggestContracts(
  ir: FunctionIR,
  ctx: Z3Context,
): Promise<SuggestFunctionResult> {
  const empty: SuggestFunctionResult = { name: ir.name, params: ir.params.map(p => p.name), suggestions: [], conditionals: [], guards: [] }

  // Detect guards and null-safety even for non-number returns
  const guards: GuardSuggestion[] = ir.body ? detectGuards(ir.body) : []

  if (ir.body === undefined || ir.returnSort === 'string' || ir.returnSort === 'bool') {
    // For unknown sort: still check null-safety and guards
    if (ir.body !== undefined && ir.returnSort === 'unknown') {
      const suggestions: Suggestion[] = []
      if (!hasNullPath(ir.body)) {
        suggestions.push({ kind: 'ensures', text: 'result is always defined', status: 'provable', description: 'no branch returns null or undefined' })
      }
      return { ...empty, suggestions, guards }
    }
    return { ...empty, guards }
  }

  const vars = createVariables(ir.params, ir.returnSort, ctx)

  // Body constraint
  const bodyZ3 = toZ3(ir.body, vars, ctx)
  const resultVar = vars.get('result')
  const bodyAssumptions: Bool<'main'>[] = []
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  if (bodyZ3 !== null && resultVar !== undefined) {
    try { bodyAssumptions.push((resultVar as any).eq(bodyZ3)) } catch { /* sort mismatch */ }
  }

  // Domain constraints
  const domain: Bool<'main'>[] = []
  for (const [name, expr] of vars) {
    if (name.endsWith('.length')) {
      try { domain.push((expr as Arith<'main'>).ge(ctx.Real.val(0))) } catch {}
    }
  }

  const suggestions: Suggestion[] = []
  const conditionals: ConditionalSuggestion[] = []

  // ── Ensures: only show provable ones ───────────────────────────────────────
  const ensuresCandidates = [
    ...generateEnsuresCandidates(ir.params, vars, ir.returnSort, ctx),
    ...generateBodyDerivedCandidates(ir.body, ir.params, vars, ir.returnSort, ctx),
  ]

  const failingEnsures: Array<{ text: string; z3: Bool<'main'> }> = []

  for (const { text, z3 } of ensuresCandidates) {
    const result = await check({
      variables: vars,
      assumptions: [...bodyAssumptions],
      goal: ctx.Not(z3),
      domainConstraints: domain,
      timeout: 2000,
    })
    if (result.status === 'proved') {
      suggestions.push({ kind: 'ensures', text, status: 'provable' })
    } else if (result.status === 'disproved') {
      failingEnsures.push({ text, z3 })
    }
  }

  // ── Risk-guarding requires ─────────────────────────────────────────────────
  const riskCandidates = generateRiskCandidates(ir.body, vars, ctx)
  for (const { text, z3, description } of riskCandidates) {
    const result = await check({
      variables: vars,
      assumptions: [...bodyAssumptions],
      goal: ctx.Not(z3),
      domainConstraints: domain,
      timeout: 2000,
    })
    if (result.status === 'disproved') {
      suggestions.push({ kind: 'requires', text, status: 'needs-precondition', description, counterexample: result.counterexample })
    }
  }

  // ── "What-if" — for failing ensures, find requires that fix them ───────────
  const requiresCandidates = generateParamCandidates(ir.params, vars, ctx)

  for (const failing of failingEnsures.slice(0, 5)) {  // cap at 5
    for (const req of requiresCandidates.slice(0, 10)) {  // cap at 10
      try {
        const result = await check({
          variables: vars,
          assumptions: [...bodyAssumptions, req.z3],
          goal: ctx.Not(failing.z3),
          domainConstraints: domain,
          timeout: 1000,
        })
        if (result.status === 'proved') {
          conditionals.push({
            kind: 'conditional',
            requires: req.text,
            enables: failing.text,
          })
          break  // found a fix for this ensures, move to next
        }
      } catch { /* skip */ }
    }
  }

  // ── Null-safety ────────────────────────────────────────────────────────────
  if (ir.body && !hasNullPath(ir.body)) {
    suggestions.push({ kind: 'ensures', text: 'result is always defined', status: 'provable', description: 'no branch returns null or undefined' })
  }

  return {
    name: ir.name,
    params: ir.params.map(p => p.name),
    suggestions,
    conditionals,
    guards,
  }
}

// ---------------------------------------------------------------------------
// Candidate generation
// ---------------------------------------------------------------------------

interface Candidate {
  text: string
  z3: Bool<'main'>
  description?: string | undefined
}

/** Returns 0 in the correct sort (Int or Real) for the given sort name. */
function zeroVal(sort: Sort, ctx: Z3Context): Arith<'main'> {
  return sort === 'int' ? ctx.Int.val(0) as Arith<'main'> : ctx.Real.val(0)
}

function generateParamCandidates(params: Param[], vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): Candidate[] {
  const out: Candidate[] = []
  for (const p of params) {
    if (p.sort !== 'real' && p.sort !== 'int') continue
    const v = vars.get(p.name) as Arith<'main'> | undefined
    if (!v) continue
    const z = zeroVal(p.sort, ctx)
    out.push({ text: `positive(${p.name})`, z3: v.gt(z) })
    out.push({ text: `nonNegative(${p.name})`, z3: v.ge(z) })
  }
  // Also try relational: a <= b, a >= b for pairs (same sort only)
  for (let i = 0; i < params.length; i++) {
    for (let j = i + 1; j < params.length; j++) {
      const a = params[i]!, b = params[j]!
      if (a.sort !== b.sort) continue  // avoid Int/Real mix
      if (a.sort !== 'real' && a.sort !== 'int') continue
      const va = vars.get(a.name) as Arith<'main'> | undefined
      const vb = vars.get(b.name) as Arith<'main'> | undefined
      if (!va || !vb) continue
      out.push({ text: `${a.name} <= ${b.name}`, z3: va.le(vb) })
      out.push({ text: `${a.name} >= ${b.name}`, z3: va.ge(vb) })
    }
  }
  return out
}

function generateEnsuresCandidates(params: Param[], vars: Map<string, AnyExpr<'main'>>, returnSort: Sort, ctx: Z3Context): Candidate[] {
  const out: Candidate[] = []
  if (returnSort !== 'real' && returnSort !== 'int') return out
  const result = vars.get('result') as Arith<'main'> | undefined
  if (!result) return out

  const z = zeroVal(returnSort, ctx)
  out.push({ text: 'nonNegative(result)', z3: result.ge(z) })
  out.push({ text: 'positive(result)', z3: result.gt(z) })

  for (const p of params) {
    if (p.sort !== returnSort) continue  // avoid sort mismatch
    const v = vars.get(p.name) as Arith<'main'> | undefined
    if (!v) continue
    out.push({ text: `result <= ${p.name}`, z3: result.le(v) })
    out.push({ text: `result >= ${p.name}`, z3: result.ge(v) })
  }

  return out
}

/** Generates ensures candidates from body structure analysis. */
function generateBodyDerivedCandidates(
  body: Expr,
  params: Param[],
  vars: Map<string, AnyExpr<'main'>>,
  returnSort: Sort,
  ctx: Z3Context,
): Candidate[] {
  const out: Candidate[] = []
  if (returnSort !== 'real' && returnSort !== 'int') return out
  const result = vars.get('result') as Arith<'main'> | undefined
  if (!result) return out
  const z = zeroVal(returnSort, ctx)

  // If body is subtraction: result = a - b → result <= a
  if (body.kind === 'binary' && body.op === '-') {
    if (body.left.kind === 'ident') {
      const lhs = vars.get(body.left.name)
      if (lhs) {
        try { out.push({ text: `result <= ${body.left.name}`, z3: result.le(lhs as Arith<'main'>) }) } catch {}
      }
    }
  }

  // If body is multiplication → result could be non-negative
  if (body.kind === 'binary' && body.op === '*') {
    out.push({ text: 'nonNegative(result)', z3: result.ge(z) })
  }

  // If body is ternary → result may be bounded by params
  if (body.kind === 'ternary') {
    for (const p of params) {
      if (p.sort !== returnSort) continue
      const v = vars.get(p.name) as Arith<'main'> | undefined
      if (!v) continue
      out.push({ text: `result <= ${p.name}`, z3: result.le(v) })
      out.push({ text: `result >= ${p.name}`, z3: result.ge(v) })
    }
  }

  return out
}

function generateRiskCandidates(body: Expr, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): Candidate[] {
  const out: Candidate[] = []
  walkForRisks(body, vars, ctx, out)
  return out
}

function walkForRisks(expr: Expr, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context, out: Candidate[]): void {
  switch (expr.kind) {
    case 'binary':
      if (expr.op === '/' || expr.op === '%') {
        const denomZ3 = toZ3(expr.right, vars, ctx)
        if (denomZ3 !== null) {
          const denomText = prettyExpr(expr.right)
          const opName = expr.op === '/' ? 'division' : 'modulo'
          const fullExprText = prettyExpr(expr)
          out.push({
            text: `${denomText} !== 0`,
            z3: ctx.Not((denomZ3 as Arith<'main'>).eq(ctx.Real.val(0)) as Bool<'main'>),
            description: `guards ${opName} by \`${denomText}\` in \`${fullExprText}\``,
          })
        }
      }
      walkForRisks(expr.left, vars, ctx, out)
      walkForRisks(expr.right, vars, ctx, out)
      break
    case 'ternary':
      walkForRisks(expr.condition, vars, ctx, out)
      walkForRisks(expr.then, vars, ctx, out)
      walkForRisks(expr.else, vars, ctx, out)
      break
    case 'unary':
      walkForRisks(expr.operand, vars, ctx, out)
      break
    case 'call':
      for (const arg of expr.args) walkForRisks(arg, vars, ctx, out)
      break
    default:
      break
  }
}

// ---------------------------------------------------------------------------
// Guard detection — find if/throw or if/return patterns at top of function
// ---------------------------------------------------------------------------

function detectGuards(body: Expr): GuardSuggestion[] {
  const guards: GuardSuggestion[] = []
  detectGuardsRec(body, guards, true)
  return guards
}

function detectGuardsRec(expr: Expr, out: GuardSuggestion[], atTop: boolean): void {
  if (!atTop) return
  // Pattern: `cond ? null : realBody` → `if (cond) throw` → requires(NOT cond)
  // Also: `cond ? realBody : null` is less common but handle it
  if (expr.kind === 'ternary') {
    const thenIsNull = isNullOrUndefined(expr.then)
    const elseIsNull = isNullOrUndefined(expr.else)
    if (thenIsNull && !elseIsNull) {
      // Pattern: if (cond) throw/return null; else realBody
      // The guard condition is `cond`, the implicit requires is `NOT cond`
      const condText = prettyExpr(expr.condition)
      const negated = negateConditionText(expr.condition)
      out.push({
        kind: 'guard',
        condition: condText,
        action: 'throw',
        equivalent: negated,
      })
      // Continue looking for more guards in the else branch
      detectGuardsRec(expr.else, out, true)
    } else if (elseIsNull && !thenIsNull) {
      // Pattern: if (!cond) throw; else realBody → guard is !cond, requires is cond
      const condText = prettyExpr(expr.condition)
      out.push({
        kind: 'guard',
        condition: `!(${condText})`,
        action: 'throw',
        equivalent: condText,
      })
      detectGuardsRec(expr.then, out, true)
    }
  }
}

function isNullOrUndefined(expr: Expr): boolean {
  return expr.kind === 'literal' && expr.value === null
}

function negateConditionText(expr: Expr): string {
  // For simple comparisons, negate directly
  if (expr.kind === 'binary') {
    const l = prettyExpr(expr.left)
    const r = prettyExpr(expr.right)
    switch (expr.op) {
      case '<=': return `${l} > ${r}`
      case '<':  return `${l} >= ${r}`
      case '>=': return `${l} < ${r}`
      case '>':  return `${l} <= ${r}`
      case '===': return `${l} !== ${r}`
      case '!==': return `${l} === ${r}`
    }
  }
  if (expr.kind === 'unary' && expr.op === '!') {
    return prettyExpr(expr.operand)
  }
  return `!(${prettyExpr(expr)})`
}

// ---------------------------------------------------------------------------
// Null-safety — walk body to check if any branch returns null
// ---------------------------------------------------------------------------

function hasNullPath(expr: Expr): boolean {
  switch (expr.kind) {
    case 'literal':
      return expr.value === null
    case 'ternary':
      return hasNullPath(expr.then) || hasNullPath(expr.else)
    default:
      return false
  }
}
