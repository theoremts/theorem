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

    // Collect enclosing function's inline requires as assumptions
    const enclosingRequires = collectEnclosingRequires(node)

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

      // Add enclosing function's requires as assumptions
      for (const reqExpr of enclosingRequires) {
        collectAndCreateVars(reqExpr, vars, ctx)
        const reqZ3 = toZ3(reqExpr, vars, ctx)
        if (reqZ3) {
          try {
            assumptions.push(reqZ3 as Bool<'main'>)
            assumptionLabels.push(`enclosing requires: ${prettyExpr(reqExpr)}`)
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

/**
 * Check if a node is directly inside a proof() wrapper or a contract call.
 * Calls inside regular functions with inline contracts are NOT skipped —
 * those still need call-site verification.
 */
function isInsideContractContext(node: Node): boolean {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isCallExpression(current)) {
      const callee = current.getExpression().getText()
      // Skip calls that are arguments to proof(), requires(), ensures(), etc.
      if (callee === 'proof' || callee === 'proof.fn' ||
          callee === 'requires' || callee === 'ensures' ||
          callee === 'check' || callee === 'assume' ||
          callee === 'invariant' || callee === 'decreases') return true
    }
    // Inside a decorated method with @requires/@ensures — handled by translator
    if (Node.isMethodDeclaration(current)) {
      const decorators = current.getDecorators()
      if (decorators.some(d => ['requires', 'ensures'].includes(d.getName()))) return true
    }
    // NOTE: we deliberately do NOT skip calls inside functions with inline
    // requires/ensures. The translator verifies the function's own contracts,
    // but calls to other contracted functions inside the body still need
    // call-site verification.
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
 * Collects inline requires() calls from the enclosing function.
 * If the call is inside `function f(x) { requires(x > 0); ... call() }`,
 * then `x > 0` is an assumption for the call.
 */
function collectEnclosingRequires(callNode: Node): Expr[] {
  const requires: Expr[] = []

  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    if (Node.isFunctionDeclaration(parent) || Node.isArrowFunction(parent) || Node.isFunctionExpression(parent)) {
      const body = (parent as any).getBody()
      if (body && Node.isBlock(body)) {
        for (const stmt of body.getStatements()) {
          if (!Node.isExpressionStatement(stmt)) continue
          const expr = stmt.getExpression()
          if (!Node.isCallExpression(expr)) continue
          const callee = expr.getExpression().getText()
          if (callee !== 'requires') continue
          const args = expr.getArguments()
          if (args.length === 0) continue
          const firstArg = args[0]!
          // Handle arrow-wrapped: requires(({x}) => x > 0)
          if (Node.isArrowFunction(firstArg)) {
            const argBody = (firstArg as any).getBody()
            if (argBody) {
              const parsed = parseExpr(argBody as Expression)
              if (parsed) requires.push(parsed)
            }
          } else {
            const parsed = parseExpr(firstArg as Expression)
            if (parsed) requires.push(parsed)
          }
        }
      }
      break // only collect from the immediate enclosing function
    }

    current = parent
  }

  return requires
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
