import type { Expr, FunctionIR } from '../parser/ir.js'
import type { Z3Context } from '../solver/context.js'
import type { InferredContract } from './index.js'
import { prettyExpr } from '../parser/pretty.js'

/** Recursively measure the depth of an expression tree. */
function exprDepth(expr: Expr): number {
  switch (expr.kind) {
    case 'literal':
    case 'ident':
      return 1
    case 'member':
      return 1 + exprDepth(expr.object)
    case 'element-access':
      return 1 + Math.max(exprDepth(expr.object), exprDepth(expr.index))
    case 'unary':
      return 1 + exprDepth(expr.operand)
    case 'binary':
      return 1 + Math.max(exprDepth(expr.left), exprDepth(expr.right))
    case 'call':
      return 1 + Math.max(0, ...expr.args.map(exprDepth))
    case 'ternary':
      return 1 + Math.max(exprDepth(expr.condition), exprDepth(expr.then), exprDepth(expr.else))
    case 'quantifier':
      return 1 + exprDepth(expr.body)
    case 'array':
      return 1 + Math.max(0, ...expr.elements.map(exprDepth))
    case 'object':
      return 1 + Math.max(0, ...expr.properties.map(p => exprDepth(p.value)))
    case 'spread':
      return 1 + exprDepth(expr.operand)
    case 'template':
      return 1 + Math.max(0, ...expr.parts.filter((p): p is Expr => typeof p !== 'string').map(exprDepth))
  }
}

export { analyzeBody as analyzeBodyExpr }

export async function analyzeBody(ir: FunctionIR, _ctx: Z3Context, _requires: InferredContract[]): Promise<InferredContract[]> {
  if (!ir.body) return []

  const body = ir.body

  // Skip trivial bodies (just returning an identifier)
  if (body.kind === 'ident') return []

  // Skip guard-ternary bodies: if the parser converted `if (cond) throw; return expr`
  // to `cond ? null : expr`, the ensures would restate the guard + body which is confusing.
  // The guard is already extracted separately.
  if (body.kind === 'ternary' && body.then.kind === 'literal' && body.then.value === null) return []

  const results: InferredContract[] = []

  // Object return bodies: generate per-property ensures
  if (body.kind === 'object' && body.properties.length > 0) {
    for (const { key, value } of body.properties) {
      if (exprDepth(value) > 3) continue
      results.push({
        kind: 'ensures',
        text: `output().${key} === ${prettyExpr(value)}`,
        predicate: {
          kind: 'binary',
          op: '===',
          left: {
            kind: 'member',
            object: { kind: 'call', callee: 'output', args: [] },
            property: key,
          },
          right: value,
        },
        confidence: 'derived',
        source: `from return property ${key}`,
      })
    }
    return results
  }

  // Skip overly complex bodies
  if (exprDepth(body) > 3) return []

  // Direct ensures for simple bodies
  results.push({
    kind: 'ensures',
    text: `output() === ${prettyExpr(body)}`,
    predicate: {
      kind: 'binary',
      op: '===',
      left: { kind: 'call', callee: 'output', args: [] },
      right: body,
    },
    confidence: 'derived',
    source: 'from return expression',
  })

  return results
}
