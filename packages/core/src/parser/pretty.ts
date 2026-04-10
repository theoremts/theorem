import type { Expr } from './ir.js'

/** Converts an Expr IR back to a human-readable TypeScript-like string. */
export function prettyExpr(expr: Expr): string {
  switch (expr.kind) {
    case 'literal':
      if (expr.value === null) return 'null'
      if (typeof expr.value === 'string') return `"${expr.value}"`
      return String(expr.value)
    case 'ident':   return expr.name
    case 'member':  return `${prettyExpr(expr.object)}.${expr.property}`
    case 'element-access': return `${prettyExpr(expr.object)}[${prettyExpr(expr.index)}]`
    case 'unary':
      if (expr.op === 'typeof') return `typeof ${prettyExpr(expr.operand)}`
      if (expr.op === '-') return `-${prettyExpr(expr.operand)}`
      return `!${prettyExpr(expr.operand)}`
    case 'call':    return `${expr.callee}(${expr.args.map(prettyExpr).join(', ')})`
    case 'ternary':
      return `${prettyExpr(expr.condition)} ? ${prettyExpr(expr.then)} : ${prettyExpr(expr.else)}`
    case 'quantifier':
      return `${expr.quantifier}(${expr.param} => ${prettyExpr(expr.body)})`
    case 'array':
      return `[${expr.elements.map(prettyExpr).join(', ')}]`
    case 'object':
      return `{ ${expr.properties.map(p => p.key === '...' ? `...${prettyExpr(p.value)}` : `${p.key}: ${prettyExpr(p.value)}`).join(', ')} }`
    case 'spread':
      return `...${prettyExpr(expr.operand)}`
    case 'template': {
      const parts = expr.parts.map(p => typeof p === 'string' ? p : `\${${prettyExpr(p)}}`)
      return `\`${parts.join('')}\``
    }
    case 'binary': {
      const l = maybeParens(expr.left, expr.op)
      const r = maybeParens(expr.right, expr.op)
      return `${l} ${expr.op} ${r}`
    }
  }
}

// Add parens around lower-precedence sub-expressions
function maybeParens(child: Expr, parentOp: string): string {
  const text = prettyExpr(child)
  if (child.kind === 'binary' && precedence(child.op) < precedence(parentOp)) {
    return `(${text})`
  }
  return text
}

function precedence(op: string): number {
  if (op === '??') return 0
  if (op === '||') return 1
  if (op === '&&') return 2
  if (op === '===' || op === '!==') return 3
  if (op === '<' || op === '<=' || op === '>' || op === '>=') return 4
  if (op === '+' || op === '-') return 5
  if (op === '*' || op === '/' || op === '%') return 6
  if (op === '**') return 7
  return 8
}
