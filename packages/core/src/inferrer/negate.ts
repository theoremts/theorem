import type { Expr, BinaryOp } from '../parser/ir.js'

const comparisonFlip: Partial<Record<BinaryOp, BinaryOp>> = {
  '<': '>=',
  '>=': '<',
  '<=': '>',
  '>': '<=',
  '===': '!==',
  '!==': '===',
}

/**
 * Produces the logical negation of an IR expression.
 *
 * - Comparison operators are flipped (e.g. `<` → `>=`).
 * - Logical NOT is unwrapped (`!x` → `x`).
 * - De Morgan's laws are applied to `&&` and `||`.
 * - Boolean literals are inverted.
 * - Everything else is wrapped in `{ kind: 'unary', op: '!', operand: expr }`.
 */
export function negateExpr(expr: Expr): Expr {
  // Comparison operators — flip them
  if (expr.kind === 'binary') {
    const flipped = comparisonFlip[expr.op]
    if (flipped) {
      return { kind: 'binary', op: flipped, left: expr.left, right: expr.right }
    }

    // De Morgan's laws
    if (expr.op === '&&') {
      return { kind: 'binary', op: '||', left: negateExpr(expr.left), right: negateExpr(expr.right) }
    }
    if (expr.op === '||') {
      return { kind: 'binary', op: '&&', left: negateExpr(expr.left), right: negateExpr(expr.right) }
    }
  }

  // Logical NOT — unwrap
  if (expr.kind === 'unary' && expr.op === '!') {
    return expr.operand
  }

  // Boolean literals
  if (expr.kind === 'literal' && typeof expr.value === 'boolean') {
    return { kind: 'literal', value: !expr.value }
  }

  // Fallback — wrap in NOT
  return { kind: 'unary', op: '!', operand: expr }
}

/**
 * Splits a top-level OR chain into individual disjuncts.
 *
 * `a || b || c` → `[a, b, c]`
 * `a && b`      → `[a && b]`
 * `a`           → `[a]`
 */
export function splitDisjunction(expr: Expr): Expr[] {
  if (expr.kind === 'binary' && expr.op === '||') {
    return [...splitDisjunction(expr.left), ...splitDisjunction(expr.right)]
  }
  return [expr]
}
