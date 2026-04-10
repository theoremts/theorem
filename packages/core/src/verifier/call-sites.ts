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

    // For each requires, generate a verification task
    for (const req of contract.requires) {
      if (typeof req === 'string') continue
      const substituted = substituteExpr(req, mapping)

      // Create Z3 variables for all identifiers in the substituted expression
      const vars = new Map<string, AnyExpr<'main'>>()
      collectAndCreateVars(substituted, vars, ctx)

      const z3 = toZ3(substituted, vars, ctx)
      if (z3 === null) continue

      const argTexts = args.map(a => a.getText().trim()).join(', ')

      tasks.push({
        functionName: `(call-site) ${calleeName}`,
        contractText: `${calleeName}(${argTexts}): ${prettyExpr(req)}`,
        variables: vars,
        assumptions: [],
        assumptionLabels: [],
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
