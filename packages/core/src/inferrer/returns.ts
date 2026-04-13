import type { Expr, FunctionIR } from '../parser/ir.js'
import type { Z3Context } from '../solver/context.js'
import type { InferredContract } from './index.js'
import { prettyExpr } from '../parser/pretty.js'

const outputCall: Expr = { kind: 'call', callee: 'output', args: [] }

function mkBinary(op: import('../parser/ir.js').BinaryOp, left: Expr, right: Expr): Expr {
  return { kind: 'binary', op, left, right }
}

function mkEnsures(predicate: Expr, source: string, confidence: 'proven' | 'derived' = 'derived'): InferredContract {
  return {
    kind: 'ensures',
    text: prettyExpr(predicate),
    predicate,
    confidence,
    source,
  }
}

/** Collect all leaf (non-ternary) nodes from a nested ternary tree. */
function collectTernaryLeaves(expr: Expr): Expr[] {
  if (expr.kind === 'ternary') {
    return [...collectTernaryLeaves(expr.then), ...collectTernaryLeaves(expr.else)]
  }
  return [expr]
}

/** Check if an expr is a reference to a parameter. */
function isParamRef(expr: Expr, params: Set<string>): boolean {
  return expr.kind === 'ident' && params.has(expr.name)
}

/** Check if two expressions are structurally identical identifiers. */
function sameIdent(a: Expr, b: Expr): boolean {
  return a.kind === 'ident' && b.kind === 'ident' && a.name === b.name
}

export async function analyzeReturns(ir: FunctionIR, ctx: Z3Context, requires: InferredContract[]): Promise<InferredContract[]> {
  if (!ir.body) return []
  if (ir.returnSort !== 'real' && ir.returnSort !== 'int' && ir.returnSort !== 'bool' && ir.returnSort !== 'string') return []

  const body = ir.body
  const results: InferredContract[] = []
  const paramNames = new Set(ir.params.map(p => p.name))

  // --- Numeric return analysis ---
  if (ir.returnSort === 'real' || ir.returnSort === 'int') {

    // 1. Bounds from ternary (clamp pattern)
    if (body.kind === 'ternary') {
      const allLeaves = collectTernaryLeaves(body)
      // Cap ternary leaf analysis at 4 leaves max for performance
      if (allLeaves.length > 4) return results
      const leaves = allLeaves
      const paramLeaves = leaves.filter(l => isParamRef(l, paramNames))
      const nonParamLeaves = leaves.filter(l => !isParamRef(l, paramNames))

      if (paramLeaves.length > 0 && nonParamLeaves.length > 0) {
        for (const bound of nonParamLeaves) {
          // output() >= bound (lower bound)
          results.push(mkEnsures(
            mkBinary('>=', outputCall, bound),
            'from clamp ternary lower bound',
          ))
          // output() <= bound (upper bound)
          results.push(mkEnsures(
            mkBinary('<=', outputCall, bound),
            'from clamp ternary upper bound',
          ))
        }
      }
    }

    // 2. Non-negative from known functions
    if (body.kind === 'call') {
      if (body.callee === 'Math.abs') {
        results.push(mkEnsures(
          mkBinary('>=', outputCall, { kind: 'literal', value: 0 }),
          'from Math.abs',
          'proven',
        ))
      }

      if (body.callee === 'Math.max' && body.args.length >= 2) {
        for (const arg of body.args) {
          results.push(mkEnsures(
            mkBinary('>=', outputCall, arg),
            'from Math.max',
            'proven',
          ))
        }
      }

      if (body.callee === 'Math.min' && body.args.length >= 2) {
        for (const arg of body.args) {
          results.push(mkEnsures(
            mkBinary('<=', outputCall, arg),
            'from Math.min',
            'proven',
          ))
        }
      }
    }

    // 3. Non-negative from structure
    // a * a (same ident multiplied by itself)
    if (body.kind === 'binary' && body.op === '*' && sameIdent(body.left, body.right)) {
      results.push(mkEnsures(
        mkBinary('>=', outputCall, { kind: 'literal', value: 0 }),
        'from squared expression',
      ))
    }

    // a ** 2
    if (body.kind === 'binary' && body.op === '**'
      && body.right.kind === 'literal' && body.right.value === 2) {
      results.push(mkEnsures(
        mkBinary('>=', outputCall, { kind: 'literal', value: 0 }),
        'from exponentiation by 2',
      ))
    }
  }

  // 4. Boolean return
  if (ir.returnSort === 'bool') {
    if (body.kind === 'binary' || body.kind === 'unary') {
      results.push(mkEnsures(
        mkBinary('===', outputCall, body),
        'from boolean return expression',
      ))
    }
  }

  // 5. Enum-like string return
  if (ir.returnSort === 'string' && body.kind === 'ternary') {
    const leaves = collectTernaryLeaves(body)
    const allStringLiterals = leaves.every(
      l => l.kind === 'literal' && typeof l.value === 'string'
    )
    if (allStringLiterals && leaves.length > 0 && leaves.length <= 10) {
      // Build: output() === "A" || output() === "B" || ...
      const clauses: Expr[] = leaves.map(l =>
        mkBinary('===', outputCall, l)
      )
      let combined: Expr = clauses[0]!
      for (let i = 1; i < clauses.length; i++) {
        combined = mkBinary('||', combined, clauses[i]!)
      }
      results.push(mkEnsures(combined, 'from enum-like string return'))
    }
  }

  return results
}
