import type { Expr, FunctionIR } from '../parser/ir.js'
import { prettyExpr } from '../parser/pretty.js'
import { SyntaxKind, type Block } from 'ts-morph'
import type { InferredContract } from './index.js'

export function extractArithmeticSafety(ir: FunctionIR): InferredContract[] {
  if (!ir.body) return []
  const out: InferredContract[] = []
  walkExpr(ir.body, out)
  return out
}

function isNonZeroLiteral(expr: Expr): boolean {
  return expr.kind === 'literal' && typeof expr.value === 'number' && expr.value !== 0
}

function isNonNegativeLiteral(expr: Expr): boolean {
  return expr.kind === 'literal' && typeof expr.value === 'number' && expr.value >= 0
}

function isPositiveLiteral(expr: Expr): boolean {
  return expr.kind === 'literal' && typeof expr.value === 'number' && expr.value > 0
}

const LOG_CALLEES = new Set(['Math.log', 'Math.log2', 'Math.log10', 'Math.log1p'])

function addIfNew(out: InferredContract[], contract: InferredContract): void {
  if (!out.some(c => c.text === contract.text)) {
    out.push(contract)
  }
}

const LOG_AST_CALLEES = new Set(['Math.log', 'Math.log2', 'Math.log10', 'Math.log1p'])

function stripParens(text: string): string {
  let t = text.trim()
  while (t.startsWith('(') && t.endsWith(')')) {
    t = t.slice(1, -1).trim()
  }
  return t
}

export function extractArithmeticFromBlock(body: Block): InferredContract[] {
  const out: InferredContract[] = []

  // Check binary expressions for division/modulo by zero
  for (const node of body.getDescendantsOfKind(SyntaxKind.BinaryExpression)) {
    const opToken = node.getOperatorToken().getText()
    if (opToken !== '/' && opToken !== '%') continue

    const rhs = node.getRight()
    // Skip if rhs is a non-zero numeric literal
    if (rhs.getKind() === SyntaxKind.NumericLiteral) {
      const val = parseFloat(rhs.getText())
      if (val !== 0) continue
    }

    const rhsText = stripParens(rhs.getText())
    const label = opToken === '/' ? 'division' : 'modulo'
    const text = `${rhsText} !== 0`
    if (!out.some(c => c.text === text)) {
      out.push({
        kind: 'requires',
        text,
        predicate: {
          kind: 'binary',
          op: '!==',
          left: { kind: 'ident', name: rhsText },
          right: { kind: 'literal', value: 0 },
        },
        confidence: 'derived',
        source: `${label} by ${rhsText}`,
      })
    }
  }

  // Check call expressions for Math.sqrt, Math.log, etc.
  for (const node of body.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeText = node.getExpression().getText().trim()
    const args = node.getArguments()
    if (args.length === 0) continue

    const argText = args[0]!.getText().trim()

    if (calleeText === 'Math.sqrt') {
      // Skip if arg is a non-negative numeric literal
      if (args[0]!.getKind() === SyntaxKind.NumericLiteral) {
        const val = parseFloat(argText)
        if (val >= 0) continue
      }
      const text = `${argText} >= 0`
      if (!out.some(c => c.text === text)) {
        out.push({
          kind: 'requires',
          text,
          predicate: {
            kind: 'binary',
            op: '>=',
            left: { kind: 'ident', name: argText },
            right: { kind: 'literal', value: 0 },
          },
          confidence: 'derived',
          source: `Math.sqrt(${argText})`,
        })
      }
    } else if (LOG_AST_CALLEES.has(calleeText)) {
      // Skip if arg is a positive numeric literal
      if (args[0]!.getKind() === SyntaxKind.NumericLiteral) {
        const val = parseFloat(argText)
        if (val > 0) continue
      }
      const text = `${argText} > 0`
      if (!out.some(c => c.text === text)) {
        out.push({
          kind: 'requires',
          text,
          predicate: {
            kind: 'binary',
            op: '>',
            left: { kind: 'ident', name: argText },
            right: { kind: 'literal', value: 0 },
          },
          confidence: 'derived',
          source: `${calleeText}(${argText})`,
        })
      }
    }
  }

  return out
}

function walkExpr(expr: Expr, out: InferredContract[]): void {
  switch (expr.kind) {
    case 'binary': {
      if ((expr.op === '/' || expr.op === '%') && !isNonZeroLiteral(expr.right)) {
        const denomText = prettyExpr(expr.right)
        const label = expr.op === '/' ? 'division' : 'modulo'
        addIfNew(out, {
          kind: 'requires',
          text: `${denomText} !== 0`,
          predicate: { kind: 'binary', op: '!==', left: expr.right, right: { kind: 'literal', value: 0 } },
          confidence: 'derived',
          source: `${label} by ${denomText}`,
        })
      }
      walkExpr(expr.left, out)
      walkExpr(expr.right, out)
      break
    }

    case 'call': {
      if (expr.callee === 'Math.sqrt' && expr.args.length > 0) {
        const arg = expr.args[0]!
        if (!isNonNegativeLiteral(arg)) {
          const argText = prettyExpr(arg)
          addIfNew(out, {
            kind: 'requires',
            text: `${argText} >= 0`,
            predicate: { kind: 'binary', op: '>=', left: arg, right: { kind: 'literal', value: 0 } },
            confidence: 'derived',
            source: `Math.sqrt(${argText})`,
          })
        }
      } else if (LOG_CALLEES.has(expr.callee) && expr.args.length > 0) {
        const arg = expr.args[0]!
        if (!isPositiveLiteral(arg)) {
          const argText = prettyExpr(arg)
          addIfNew(out, {
            kind: 'requires',
            text: `${argText} > 0`,
            predicate: { kind: 'binary', op: '>', left: arg, right: { kind: 'literal', value: 0 } },
            confidence: 'derived',
            source: `${expr.callee}(${argText})`,
          })
        }
      }
      for (const a of expr.args) {
        walkExpr(a, out)
      }
      break
    }

    case 'unary':
      walkExpr(expr.operand, out)
      break

    case 'ternary':
      walkExpr(expr.condition, out)
      walkExpr(expr.then, out)
      walkExpr(expr.else, out)
      break

    case 'array':
      for (const el of expr.elements) walkExpr(el, out)
      break

    case 'object':
      for (const p of expr.properties) walkExpr(p.value, out)
      break

    case 'spread':
      walkExpr(expr.operand, out)
      break

    case 'template':
      for (const p of expr.parts) {
        if (typeof p !== 'string') walkExpr(p, out)
      }
      break

    case 'element-access':
      walkExpr(expr.object, out)
      walkExpr(expr.index, out)
      break

    case 'member':
      walkExpr(expr.object, out)
      break

    // literal, ident, quantifier — no arithmetic risk / no sub-expressions to walk
    default:
      break
  }
}
