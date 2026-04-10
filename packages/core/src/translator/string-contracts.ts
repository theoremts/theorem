import type { Bool, Arith, AnyExpr } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import { makeConst } from './variables.js'

type Z3Bool  = Bool<'main'>
type Z3Arith = Arith<'main'>
type Z3Expr  = AnyExpr<'main'>

/**
 * Translates a string contract to a Z3 Bool expression.
 *
 * Supported patterns (deterministic — no NLP):
 *
 *   "<var> is positive"               →  var > 0
 *   "<var> is non-negative"           →  var >= 0
 *   "<var> is negative"               →  var < 0
 *   "<var> is finite"                 →  true  (Z3 Real has no NaN/Inf)
 *   "<var> is between <n> and <m>"    →  n <= var <= m
 *   "<var> >= <number|var>"           →  comparison
 *   "<var> <= <number|var>"           →  comparison
 *   "<var> >  <number|var>"           →  comparison
 *   "<var> <  <number|var>"           →  comparison
 *   "<var> === <number|var>"          →  equality
 *
 * Variable names may include dot-access: "from.balance >= 0"
 * Unknown patterns return null (contract is skipped with a warning).
 */
export function translateStringContract(
  text: string,
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Bool | null {
  const s = text.trim()

  // ── "<var> is <predicate>" ────────────────────────────────────────────────
  const isPred = s.match(/^([\w.]+)\s+is\s+(positive|non-negative|negative|finite)$/)
  if (isPred) {
    const v = resolveVar(isPred[1]!, vars, ctx)
    if (!v) return null
    switch (isPred[2]) {
      case 'positive':     return (v as Z3Arith).gt(ctx.Real.val(0))
      case 'non-negative': return (v as Z3Arith).ge(ctx.Real.val(0))
      case 'negative':     return (v as Z3Arith).lt(ctx.Real.val(0))
      case 'finite':       return ctx.Bool.val(true)
    }
  }

  // ── "<var> is between <n> and <m>" ───────────────────────────────────────
  const isBetween = s.match(
    /^([\w.]+)\s+is\s+between\s+(-?\d+(?:\.\d+)?)\s+and\s+(-?\d+(?:\.\d+)?)$/,
  )
  if (isBetween) {
    const v = resolveVar(isBetween[1]!, vars, ctx)
    if (!v) return null
    const lo = ctx.Real.val(Number(isBetween[2]))
    const hi = ctx.Real.val(Number(isBetween[3]))
    return ctx.And(
      (v as Z3Arith).ge(lo) as Z3Bool,
      (v as Z3Arith).le(hi) as Z3Bool,
    )
  }

  // ── "<var> <op> <rhs>" — rhs is a number literal or another variable ──────
  const comp = s.match(/^([\w.]+)\s*(>=|<=|>|<|===?|!==?)\s*([\w.-]+)$/)
  if (comp) {
    const lhs = resolveVar(comp[1]!, vars, ctx)
    if (!lhs) return null

    const rhsToken = comp[3]!
    const rhsNum   = Number(rhsToken)
    const rhs: Z3Expr = Number.isFinite(rhsNum)
      ? ctx.Real.val(rhsNum)
      : (resolveVar(rhsToken, vars, ctx) ?? ctx.Real.val(0))

    return applyOp(comp[2]!, lhs as Z3Arith, rhs as Z3Arith, ctx)
  }

  return null
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Resolves a variable name (including dot-access) from the vars map. */
function resolveVar(
  name: string,
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  if (vars.has(name)) return vars.get(name)!

  // Auto-create flat Real variable for member access (e.g. "from.balance")
  if (name.includes('.')) {
    const v = makeConst(name, 'real', ctx)
    vars.set(name, v)
    return v
  }

  return null
}

function applyOp(
  op: string,
  l: Z3Arith,
  r: Z3Arith,
  ctx: Z3Context,
): Z3Bool | null {
  switch (op) {
    case '>':   return l.gt(r)
    case '>=':  return l.ge(r)
    case '<':   return l.lt(r)
    case '<=':  return l.le(r)
    case '===':
    case '==':  return l.eq(r) as Z3Bool
    case '!==':
    case '!=':  return ctx.Not(l.eq(r) as Z3Bool)
    default:    return null
  }
}
