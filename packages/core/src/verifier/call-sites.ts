import {
  Node,
  SyntaxKind,
  type SourceFile,
  type Expression,
} from 'ts-morph'
import type { AnyExpr, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, Predicate } from '../parser/ir.js'
import type { ContractRegistry } from '../registry/index.js'
import type { VerificationTask } from '../translator/index.js'
import { parseExpr } from '../parser/expr.js'
import { prettyExpr } from '../parser/pretty.js'
import { substituteExpr } from '../translator/substitution.js'
import { makeConst } from '../translator/variables.js'
import { toZ3 } from '../translator/expr.js'

/**
 * Finds calls to registered (contracted) functions outside of proof() wrappers
 * and generates verification tasks to check that arguments satisfy the callee's requires.
 *
 * Used by both `verify` and `scan` to catch contract violations at call sites.
 */
export function extractCallSiteObligations(
  source: string,
  fileName: string,
  registry: ContractRegistry,
  ctx: Z3Context,
): VerificationTask[] {
  if (registry.size === 0) return []

  const { Project } = require('ts-morph') as typeof import('ts-morph')
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  const file = project.createSourceFile(fileName, source, { overwrite: true })

  const tasks: VerificationTask[] = []

  for (const node of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeName = node.getExpression().getText()
    const resolvedName = registry.has(calleeName)
      ? calleeName
      : calleeName.includes('.') ? calleeName.slice(calleeName.lastIndexOf('.') + 1) : null
    const contract = resolvedName ? registry.get(resolvedName) : undefined
    if (!contract) continue

    // Skip calls inside proof() / proof.fn() / requires() / ensures() — already handled by translator
    if (isInsideContractContext(node)) continue

    const args = node.getArguments()

    // Build substitution: callee param names → argument expressions
    const mapping = new Map<string, Expr>()
    for (let i = 0; i < Math.min(contract.params.length, args.length); i++) {
      const parsed = parseExpr(args[i]! as Expression)
      if (parsed !== null) {
        mapping.set(contract.params[i]!.name, parsed)
      }
    }

    // Collect variable assignments in scope before the call site (constant propagation)
    const scopeAssignments = collectScopeAssignments(node)

    // Collect path conditions — if-statement guards enclosing the call site
    const pathConditions = collectPathConditions(node)

    // For each requires, generate a verification task
    for (const req of contract.requires) {
      if (typeof req === 'string') continue
      const substituted = substituteExpr(req, mapping)

      // Create Z3 variables for all identifiers in the substituted expression
      const vars = new Map<string, AnyExpr<'main'>>()
      collectAndCreateVars(substituted, vars, ctx)

      // Add scope assignments as assumptions (constant propagation)
      const assumptions: Bool<'main'>[] = []
      const assumptionLabels: string[] = []
      for (const [varName, valueExpr] of scopeAssignments) {
        collectAndCreateVars(valueExpr, vars, ctx)
        const varZ3 = vars.get(varName)
        const valZ3 = toZ3(valueExpr, vars, ctx)
        if (varZ3 && valZ3) {
          try {
            assumptions.push((varZ3 as any).eq(valZ3) as Bool<'main'>)
            assumptionLabels.push(`scope: ${varName} = ${prettyExpr(valueExpr)}`)
          } catch { /* sort mismatch */ }
        }
      }

      // Add path conditions as assumptions (if-guards enclosing the call)
      for (const { expr: condExpr, negated } of pathConditions) {
        collectAndCreateVars(condExpr, vars, ctx)
        const condZ3 = toZ3(condExpr, vars, ctx)
        if (condZ3) {
          try {
            const assumption = negated ? ctx.Not(condZ3 as Bool<'main'>) : condZ3 as Bool<'main'>
            assumptions.push(assumption)
            assumptionLabels.push(`path: ${negated ? '!' : ''}${prettyExpr(condExpr)}`)
          } catch { /* skip */ }
        }
      }

      const z3 = toZ3(substituted, vars, ctx)
      if (z3 === null) continue

      const argTexts = args.map(a => a.getText().trim()).join(', ')

      tasks.push({
        functionName: `(call-site) ${calleeName}`,
        contractText: `${calleeName}(${argTexts}): ${prettyExpr(req)}`,
        variables: vars,
        assumptions,
        assumptionLabels,
        goal: ctx.Not(z3 as Bool<'main'>),
        domainConstraints: [],
      })
    }
  }

  return tasks
}

/** Check if a node is inside proof(), proof.fn(), requires(), ensures(), or other contract calls. */
function isInsideContractContext(node: Node): boolean {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isCallExpression(current)) {
      const callee = current.getExpression().getText()
      if (callee === 'proof' || callee === 'proof.fn' ||
          callee === 'requires' || callee === 'ensures' ||
          callee === 'check' || callee === 'assume' ||
          callee === 'invariant' || callee === 'decreases') return true
    }
    // Inside a decorated method — also handled by translator
    if (Node.isMethodDeclaration(current)) {
      const decorators = current.getDecorators()
      if (decorators.some(d => ['requires', 'ensures'].includes(d.getName()))) return true
    }
    // Inside a function with inline contracts
    if (Node.isFunctionDeclaration(current) || Node.isArrowFunction(current)) {
      // Check if the function body has requires/ensures statements
      const body = Node.isFunctionDeclaration(current) ? current.getBody() : current.getBody()
      if (body && Node.isBlock(body)) {
        for (const stmt of body.getStatements()) {
          if (Node.isExpressionStatement(stmt)) {
            const expr = stmt.getExpression()
            if (Node.isCallExpression(expr)) {
              const name = expr.getExpression().getText()
              if (name === 'requires' || name === 'ensures') return true
            }
          }
        }
      }
    }
    current = current.getParent()
  }
  return false
}

/**
 * Collects variable assignments (var/let/const with initializer) that are
 * in scope before the given call-site node. This enables constant propagation
 * so that `var a = 2; nextOdd(a)` knows `a === 2`.
 *
 * Walks backwards through sibling statements and up through parent blocks.
 * Only collects simple literal or expression initializers — no complex patterns.
 */
function collectScopeAssignments(callNode: Node): Map<string, Expr> {
  const assignments = new Map<string, Expr>()

  // Walk up to find containing block/source file
  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    // If parent is a Block or SourceFile, walk its statements before `current`
    if (Node.isBlock(parent) || Node.isSourceFile(parent)) {
      const statements = parent.getStatements()
      for (const stmt of statements) {
        // Stop at the statement containing our call
        if (stmt.getPos() >= callNode.getPos()) break

        // Variable declarations: var a = 2, const b = 3
        if (Node.isVariableStatement(stmt)) {
          for (const decl of stmt.getDeclarationList().getDeclarations()) {
            const name = decl.getName()
            const init = decl.getInitializer()
            if (init) {
              const parsed = parseExpr(init as Expression)
              if (parsed) {
                assignments.set(name, parsed)
              }
            }
          }
        }

        // Expression statement assignments: a = 5
        if (Node.isExpressionStatement(stmt)) {
          const expr = stmt.getExpression()
          if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === '=') {
            const left = expr.getLeft()
            if (Node.isIdentifier(left)) {
              const parsed = parseExpr(expr.getRight() as Expression)
              if (parsed) {
                assignments.set(left.getText(), parsed)
              }
            }
          }
        }
      }
    }

    current = parent
  }

  return assignments
}

/**
 * Collects if-statement conditions that guard the call site.
 * If the call is inside `if (cond) { call() }`, then `cond` is a path condition.
 * If the call is in the else branch, the condition is negated.
 * Also handles early-exit guards: `if (!cond) return; call()` → cond is assumed.
 */
function collectPathConditions(callNode: Node): Array<{ expr: Expr; negated: boolean }> {
  const conditions: Array<{ expr: Expr; negated: boolean }> = []

  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    if (Node.isIfStatement(parent)) {
      const condNode = parent.getExpression()
      const parsed = parseExpr(condNode as Expression)
      if (parsed) {
        const thenStmt = parent.getThenStatement()
        const elseStmt = parent.getElseStatement()

        // Is the call in the then-branch or else-branch?
        if (thenStmt && isDescendantOf(current, thenStmt)) {
          // In then-branch: condition is true
          conditions.push({ expr: parsed, negated: false })
        } else if (elseStmt && isDescendantOf(current, elseStmt)) {
          // In else-branch: condition is false (negated)
          conditions.push({ expr: parsed, negated: true })
        }
      }
    }

    // Early-exit guard: if (!cond) return/throw; ...call()
    // If we're in a block and there's an if/return before us, assume the guard
    if (Node.isBlock(parent)) {
      const statements = parent.getStatements()
      for (const stmt of statements) {
        // Stop at the statement containing our call
        if (stmt.getPos() >= callNode.getPos()) break

        if (Node.isIfStatement(stmt) && !stmt.getElseStatement()) {
          const thenBranch = stmt.getThenStatement()
          if (isUnconditionalExit(thenBranch)) {
            // Guard: if (BAD) return → after this, !BAD holds
            const condNode = stmt.getExpression()
            const parsed = parseExpr(condNode as Expression)
            if (parsed) {
              conditions.push({ expr: parsed, negated: true })
            }
          }
        }
      }
    }

    current = parent
  }

  return conditions
}

function isDescendantOf(node: Node, ancestor: Node): boolean {
  let current: Node | undefined = node
  while (current) {
    if (current === ancestor) return true
    current = current.getParent()
  }
  return false
}

function isUnconditionalExit(node: Node): boolean {
  if (Node.isReturnStatement(node) || Node.isThrowStatement(node)) return true
  if (Node.isBlock(node)) {
    const stmts = node.getStatements()
    if (stmts.length === 0) return false
    const last = stmts[stmts.length - 1]!
    return Node.isReturnStatement(last) || Node.isThrowStatement(last)
  }
  return false
}

/** Recursively collects identifiers from an expression and creates Z3 variables. */
function collectAndCreateVars(expr: Expr, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): void {
  switch (expr.kind) {
    case 'ident':
      if (!vars.has(expr.name)) vars.set(expr.name, makeConst(expr.name, 'real', ctx))
      break
    case 'binary':
      collectAndCreateVars(expr.left, vars, ctx)
      collectAndCreateVars(expr.right, vars, ctx)
      break
    case 'unary':
      collectAndCreateVars(expr.operand, vars, ctx)
      break
    case 'ternary':
      collectAndCreateVars(expr.condition, vars, ctx)
      collectAndCreateVars(expr.then, vars, ctx)
      collectAndCreateVars(expr.else, vars, ctx)
      break
    case 'call':
      for (const a of expr.args) collectAndCreateVars(a, vars, ctx)
      break
    case 'member':
      collectAndCreateVars(expr.object, vars, ctx)
      break
    case 'element-access':
      collectAndCreateVars(expr.object, vars, ctx)
      collectAndCreateVars(expr.index, vars, ctx)
      break
    default:
      break
  }
}
