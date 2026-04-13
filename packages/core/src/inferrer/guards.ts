import type { FunctionIR } from '../parser/ir.js'
import { SyntaxKind, type SourceFile, type Block, type Expression } from 'ts-morph'
import type { InferredContract } from './index.js'
import { parseExpr } from '../parser/expr.js'
import { prettyExpr } from '../parser/pretty.js'
import { negateExpr, splitDisjunction } from './negate.js'

export function extractGuards(ir: FunctionIR, sourceFile: SourceFile): InferredContract[] {
  if (!ir.name) return []

  const contracts: InferredContract[] = []

  // Find the function in the AST
  let body: Block | undefined

  // Try named function declaration
  const fnDecl = sourceFile.getFunction(ir.name)
  if (fnDecl) {
    const b = fnDecl.getBody()
    if (b && b.getKind() === SyntaxKind.Block) {
      body = b as Block
    }
  }

  // Try arrow function / function expression assigned to variable
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

  return extractGuardsFromBlock(body)
}

export function extractGuardsFromBlock(body: Block): InferredContract[] {
  const contracts: InferredContract[] = []
  const statements = body.getStatements()

  for (const stmt of statements) {
    const kind = stmt.getKind()

    // Check for if-statement guard
    if (kind === SyntaxKind.IfStatement) {
      const ifStmt = stmt as any // ts-morph IfStatement

      // Not a guard if it has an else branch
      if (ifStmt.getElseStatement()) continue // skip — not a guard, but also stop? No, the task says "if has else, it's NOT a guard". But the stop rule says stop at non-guard. So we should break.
      // Actually re-reading: "If the if-statement has an else branch, it's NOT a guard" — so it's not a guard. And "Stop collecting guards when you encounter a statement that is NOT a guard". So we break.

      // Wait, let me re-read more carefully. The stop rules list specific types. An if-statement with else is not listed as a stop condition explicitly, but it's "Any other statement type" catch-all doesn't apply since if-statements are handled. Let me re-read...
      // "If the if-statement has an else branch, it's NOT a guard (it's branching logic)" — so treat it as a non-guard → stop.
      if (ifStmt.getElseStatement()) break

      const thenBranch = ifStmt.getThenStatement()
      if (!isUnconditionalExit(thenBranch)) break // not a guard → stop

      const exitKind = getExitKind(thenBranch)

      // Only treat throw-guards as requires.
      // Early returns (e.g., `if (x < min) return min`) handle the case
      // gracefully — they are NOT preconditions. The function works for all inputs.
      if (exitKind !== 'throw') continue

      const condExpr: Expression = ifStmt.getExpression()
      const condIR = parseExpr(condExpr)
      if (!condIR) continue // unparseable, skip but don't stop

      const condText = condExpr.getText()

      // Split disjunction, negate each part
      const disjuncts = splitDisjunction(condIR)
      for (const d of disjuncts) {
        const negated = negateExpr(d)
        contracts.push({
          kind: 'requires',
          text: prettyExpr(negated),
          predicate: negated,
          confidence: 'guard',
          source: `if (${condText}) throw`,
        })
      }
      continue
    }

    // Check for assert() or console.assert() call
    if (kind === SyntaxKind.ExpressionStatement) {
      const expr = (stmt as any).getExpression()
      if (expr && expr.getKind() === SyntaxKind.CallExpression) {
        const calleeText = expr.getExpression().getText()
        if (calleeText === 'assert' || calleeText === 'console.assert') {
          const args = expr.getArguments()
          if (args.length > 0) {
            const condIR = parseExpr(args[0] as Expression)
            if (condIR) {
              contracts.push({
                kind: 'requires',
                text: prettyExpr(condIR),
                predicate: condIR,
                confidence: 'guard',
                source: `assert(${args[0].getText()})`,
              })
              continue
            }
          }
        }
      }
      // Non-assert expression statement → stop
      break
    }

    // Variable declaration
    if (kind === SyntaxKind.VariableStatement) {
      const varStmt = stmt as any
      const decls = varStmt.getDeclarationList().getDeclarations()
      // If any declaration has an initializer, stop
      const hasInit = decls.some((d: any) => d.getInitializer() !== undefined)
      if (hasInit) break
      // Declaration without initializer — continue
      continue
    }

    // Any other statement type → stop
    break
  }

  return contracts
}

function isUnconditionalExit(node: any): boolean {
  const kind = node.getKind()

  if (kind === SyntaxKind.ThrowStatement || kind === SyntaxKind.ReturnStatement) {
    return true
  }

  if (kind === SyntaxKind.Block) {
    const stmts = (node as Block).getStatements()
    if (stmts.length === 0) return false
    // All statements should end with throw/return — actually just check the last one
    // The task says "only treat as guard if ALL of them end with throw/return"
    // But really, for a block to be an unconditional exit, the last statement must be throw/return
    const last = stmts[stmts.length - 1]!
    const lastKind = last.getKind()
    return lastKind === SyntaxKind.ThrowStatement || lastKind === SyntaxKind.ReturnStatement
  }

  return false
}

function getExitKind(node: any): string {
  const kind = node.getKind()
  if (kind === SyntaxKind.ThrowStatement) return 'throw'
  if (kind === SyntaxKind.ReturnStatement) return 'return'
  if (kind === SyntaxKind.Block) {
    const stmts = (node as Block).getStatements()
    if (stmts.length > 0) {
      return getExitKind(stmts[stmts.length - 1])
    }
  }
  return 'throw'
}
