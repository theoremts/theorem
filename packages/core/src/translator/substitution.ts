import type { Expr } from '../parser/ir.js'

/**
 * Structurally replaces identifiers in an expression,
 * then simplifies (e.g. resolves array[literal_index] to the element).
 */
export function substituteExpr(expr: Expr, mapping: Map<string, Expr>): Expr {
  return simplifyExpr(substituteRaw(expr, mapping))
}

/**
 * Simplifies constant expressions after substitution:
 *   - `[1, 2, 3][0]` → `1`  (array literal + literal index)
 *   - `{ a: 1, b: 2 }.a` → `1`  (object literal + property)
 */
export function simplifyExpr(expr: Expr): Expr {
  switch (expr.kind) {
    case 'element-access': {
      const obj = simplifyExpr(expr.object)
      const idx = simplifyExpr(expr.index)
      // [a, b, c][1] → b
      if (obj.kind === 'array' && idx.kind === 'literal' && typeof idx.value === 'number') {
        const i = idx.value
        if (Number.isInteger(i) && i >= 0 && i < obj.elements.length) {
          return simplifyExpr(obj.elements[i]!)
        }
      }
      return obj === expr.object && idx === expr.index ? expr : { ...expr, object: obj, index: idx }
    }

    case 'member': {
      const obj = simplifyExpr(expr.object)
      // { a: 1, b: 2 }.a → 1
      if (obj.kind === 'object') {
        const prop = obj.properties.find(p => p.key === expr.property)
        if (prop) return simplifyExpr(prop.value)
      }
      // [1, 2].length → 2
      if (obj.kind === 'array' && expr.property === 'length') {
        return { kind: 'literal', value: obj.elements.length }
      }
      return obj === expr.object ? expr : { ...expr, object: obj }
    }

    case 'binary': {
      const left = simplifyExpr(expr.left)
      const right = simplifyExpr(expr.right)
      return left === expr.left && right === expr.right ? expr : { ...expr, left, right }
    }

    case 'unary': {
      const operand = simplifyExpr(expr.operand)
      // -5 → literal(-5)
      if (expr.op === '-' && operand.kind === 'literal' && typeof operand.value === 'number') {
        return { kind: 'literal', value: -operand.value }
      }
      return operand === expr.operand ? expr : { ...expr, operand }
    }

    case 'ternary': {
      const cond = simplifyExpr(expr.condition)
      const then = simplifyExpr(expr.then)
      const els = simplifyExpr(expr.else)
      return cond === expr.condition && then === expr.then && els === expr.else
        ? expr : { ...expr, condition: cond, then, else: els }
    }

    case 'call': {
      const args = expr.args.map(a => simplifyExpr(a))
      const changed = args.some((a, i) => a !== expr.args[i])
      return changed ? { ...expr, args } : expr
    }

    default:
      return expr
  }
}

/**
 * Replaces `output()` calls in an ensures expression with the given replacement
 * (e.g. the fresh variable standing for a callee's return value, or the
 * variable an assignment binds the call result to).
 */
export function substituteOutput(expr: Expr, replacement: Expr): Expr {
  switch (expr.kind) {
    case 'call':
      if (expr.callee === 'output' && expr.args.length === 0) return replacement
      return { ...expr, args: expr.args.map(a => substituteOutput(a, replacement)) }
    case 'binary':
      return { ...expr, left: substituteOutput(expr.left, replacement), right: substituteOutput(expr.right, replacement) }
    case 'unary':
      return { ...expr, operand: substituteOutput(expr.operand, replacement) }
    case 'ternary':
      return { ...expr, condition: substituteOutput(expr.condition, replacement), then: substituteOutput(expr.then, replacement), else: substituteOutput(expr.else, replacement) }
    case 'member':
      return { ...expr, object: substituteOutput(expr.object, replacement) }
    case 'element-access':
      return { ...expr, object: substituteOutput(expr.object, replacement), index: substituteOutput(expr.index, replacement) }
    default:
      return expr
  }
}

function substituteRaw(expr: Expr, mapping: Map<string, Expr>): Expr {
  switch (expr.kind) {
    case 'ident': return mapping.get(expr.name) ?? expr
    case 'literal': return expr

    case 'member': {
      const obj = substituteExpr(expr.object, mapping)
      return obj === expr.object ? expr : { ...expr, object: obj }
    }

    case 'element-access': {
      const obj = substituteExpr(expr.object, mapping)
      const idx = substituteExpr(expr.index, mapping)
      return obj === expr.object && idx === expr.index ? expr : { ...expr, object: obj, index: idx }
    }

    case 'unary': {
      const operand = substituteExpr(expr.operand, mapping)
      return operand === expr.operand ? expr : { ...expr, operand }
    }

    case 'binary': {
      const left  = substituteExpr(expr.left, mapping)
      const right = substituteExpr(expr.right, mapping)
      return left === expr.left && right === expr.right ? expr : { ...expr, left, right }
    }

    case 'call': {
      const args = expr.args.map(a => substituteExpr(a, mapping))
      const changed = args.some((a, i) => a !== expr.args[i])
      return changed ? { ...expr, args } : expr
    }

    case 'ternary': {
      const condition = substituteExpr(expr.condition, mapping)
      const then      = substituteExpr(expr.then, mapping)
      const els       = substituteExpr(expr.else, mapping)
      return condition === expr.condition && then === expr.then && els === expr.else
        ? expr : { ...expr, condition, then, else: els }
    }

    case 'quantifier': {
      const inner = mapping.has(expr.param) ? new Map(mapping) : mapping
      if (inner !== mapping) inner.delete(expr.param)
      const body = substituteExpr(expr.body, inner)
      return body === expr.body ? expr : { ...expr, body }
    }

    case 'array': {
      const elements = expr.elements.map(e => substituteExpr(e, mapping))
      return elements.some((e, i) => e !== expr.elements[i]) ? { ...expr, elements } : expr
    }

    case 'object': {
      const properties = expr.properties.map(p => {
        const value = substituteExpr(p.value, mapping)
        return value === p.value ? p : { key: p.key, value }
      })
      return properties.some((p, i) => p !== expr.properties[i]) ? { kind: 'object', properties } : expr
    }

    case 'spread': {
      const operand = substituteExpr(expr.operand, mapping)
      return operand === expr.operand ? expr : { kind: 'spread', operand }
    }

    case 'template': {
      const parts = expr.parts.map(p => typeof p === 'string' ? p : substituteExpr(p, mapping))
      return { kind: 'template', parts }
    }
  }
}
