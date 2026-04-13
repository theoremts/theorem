import type { FunctionIR, Expr } from '../parser/ir.js'
import { SyntaxKind, Node, type SourceFile, type Block } from 'ts-morph'
import type { InferredContract } from './index.js'

export function extractArraySafety(ir: FunctionIR, sourceFile: SourceFile): InferredContract[] {
  if (!ir.name) return []

  // Find the function body in the AST
  let body: Block | undefined

  const fnDecl = sourceFile.getFunction(ir.name)

  if (fnDecl) {
    const b = fnDecl.getBody()
    if (b && b.getKind() === SyntaxKind.Block) {
      body = b as Block
    }
  }

  if (!body) {
    const varDecl = sourceFile.getVariableDeclaration(ir.name)
    if (varDecl) {
      const init = varDecl.getInitializer()
      if (init) {
        if (init.getKind() === SyntaxKind.ArrowFunction || init.getKind() === SyntaxKind.FunctionExpression) {
          const fnNode = init as any
          const b = fnNode.getBody()
          if (b && b.getKind() === SyntaxKind.Block) {
            body = b as Block
          }
        }
      }
    }
  }

  if (!body) return []

  return extractArraySafetyFromBlock(body)
}

export function extractArraySafetyFromBlock(body: Block): InferredContract[] {
  const contracts: InferredContract[] = []
  const seen = new Set<string>()

  // ── .reduce() without initial value ──────────────────────────────────────
  for (const node of body.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeExpr = node.getExpression()
    if (!Node.isPropertyAccessExpression(calleeExpr)) continue
    if (calleeExpr.getName() !== 'reduce') continue

    const args = node.getArguments()
    if (args.length !== 1) continue

    const objName = calleeExpr.getExpression().getText().trim()
    const text = `${objName}.length > 0`
    if (seen.has(text)) continue
    seen.add(text)

    const predicate: Expr = {
      kind: 'binary',
      op: '>',
      left: {
        kind: 'member',
        object: { kind: 'ident', name: objName },
        property: 'length',
      },
      right: { kind: 'literal', value: 0 },
    }

    contracts.push({
      kind: 'requires',
      text,
      predicate,
      confidence: 'heuristic',
      source: `${objName}.reduce() without initial value`,
    })
  }

  // ── arr[i] with non-literal index ────────────────────────────────────────
  for (const node of body.getDescendantsOfKind(SyntaxKind.ElementAccessExpression)) {
    const argNode = node.getArgumentExpression()
    if (argNode === undefined) continue
    if (Node.isNumericLiteral(argNode) || Node.isStringLiteral(argNode)) continue

    const indexText = argNode.getText().trim()
    const text = `${indexText} >= 0`
    if (seen.has(text)) continue
    seen.add(text)

    const predicate: Expr = {
      kind: 'binary',
      op: '>=',
      left: { kind: 'ident', name: indexText },
      right: { kind: 'literal', value: 0 },
    }

    contracts.push({
      kind: 'requires',
      text,
      predicate,
      confidence: 'heuristic',
      source: `array index ${indexText} may be out of bounds`,
    })
  }

  return contracts
}
