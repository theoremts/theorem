import { Node } from 'ts-morph'
import type { Expr } from '../parser/ir.js'
import { extractZodContracts } from '../inferrer/zod.js'
import { extractEffectContracts } from '../inferrer/effect-schema.js'

/**
 * Collects Zod schema constraints that hold at a risky expression.
 *
 * If the enclosing function contains `const x = Schema.parse(input)`, the
 * parse throws on invalid data, so the schema's refinements (min/max/positive…)
 * hold for `x.*` in the rest of the function. These become Z3 assumptions,
 * eliminating false positives like flagging `total / quantity` when the schema
 * guarantees `quantity >= 1`.
 */
export function collectZodAssumptions(node: Node): Expr[] {
  let current = node.getParent()
  while (current !== undefined) {
    if (
      Node.isFunctionDeclaration(current) || Node.isArrowFunction(current) ||
      Node.isMethodDeclaration(current) || Node.isFunctionExpression(current)
    ) {
      const body = current.getBody()
      if (body !== undefined && Node.isBlock(body)) {
        try {
          return [
            ...extractZodContracts(body).map(c => c.predicate),
            ...extractEffectContracts(body).map(c => c.predicate),
          ]
        } catch {
          return []
        }
      }
      return []
    }
    current = current.getParent()
  }
  return []
}
