import { SyntaxKind, Project, Node, type SourceFile } from 'ts-morph'
import type { Expr, Predicate } from '../parser/ir.js'
import type { InferredFunction, InferredContract } from './index.js'
import type { ContractRegistry } from '../registry/index.js'
import { prettyExpr } from '../parser/pretty.js'
import { parseExpr } from '../parser/expr.js'

export interface CallGraph {
  /** caller → list of callee names */
  edges: Map<string, string[]>
  /** topological order (leaves first) */
  order: string[]
}

/**
 * Recursively replaces identifiers named `oldName` with `newExpr` in the expression tree.
 */
function substituteIdent(expr: Expr, oldName: string, newExpr: Expr): Expr {
  switch (expr.kind) {
    case 'ident':
      return expr.name === oldName ? newExpr : expr
    case 'literal':
      return expr
    case 'member': {
      const obj = substituteIdent(expr.object, oldName, newExpr)
      return obj === expr.object ? expr : { kind: 'member', object: obj, property: expr.property }
    }
    case 'element-access': {
      const obj = substituteIdent(expr.object, oldName, newExpr)
      const idx = substituteIdent(expr.index, oldName, newExpr)
      return obj === expr.object && idx === expr.index ? expr : { kind: 'element-access', object: obj, index: idx }
    }
    case 'unary': {
      const operand = substituteIdent(expr.operand, oldName, newExpr)
      return operand === expr.operand ? expr : { kind: 'unary', op: expr.op, operand }
    }
    case 'binary': {
      const left = substituteIdent(expr.left, oldName, newExpr)
      const right = substituteIdent(expr.right, oldName, newExpr)
      return left === expr.left && right === expr.right ? expr : { kind: 'binary', op: expr.op, left, right }
    }
    case 'call': {
      const args = expr.args.map(a => substituteIdent(a, oldName, newExpr))
      const changed = args.some((a, i) => a !== expr.args[i])
      return changed ? { kind: 'call', callee: expr.callee, args } : expr
    }
    case 'ternary': {
      const condition = substituteIdent(expr.condition, oldName, newExpr)
      const then = substituteIdent(expr.then, oldName, newExpr)
      const els = substituteIdent(expr.else, oldName, newExpr)
      return condition === expr.condition && then === expr.then && els === expr.else
        ? expr : { kind: 'ternary', condition, then, else: els }
    }
    case 'quantifier': {
      if (expr.param === oldName) return expr // shadowed
      const body = substituteIdent(expr.body, oldName, newExpr)
      return body === expr.body ? expr : { kind: 'quantifier', quantifier: expr.quantifier, param: expr.param, body }
    }
    case 'array': {
      const elements = expr.elements.map(e => substituteIdent(e, oldName, newExpr))
      return elements.some((e, i) => e !== expr.elements[i]) ? { kind: 'array', elements } : expr
    }
    case 'object': {
      const properties = expr.properties.map(p => {
        const value = substituteIdent(p.value, oldName, newExpr)
        return value === p.value ? p : { key: p.key, value }
      })
      return properties.some((p, i) => p !== expr.properties[i]) ? { kind: 'object', properties } : expr
    }
    case 'spread': {
      const operand = substituteIdent(expr.operand, oldName, newExpr)
      return operand === expr.operand ? expr : { kind: 'spread', operand }
    }
    case 'template': {
      const parts = expr.parts.map(p => typeof p === 'string' ? p : substituteIdent(p, oldName, newExpr))
      return { kind: 'template', parts }
    }
  }
}

function createSourceFile(source: string, fileName: string): SourceFile {
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  return project.createSourceFile(fileName, source, { overwrite: true })
}

/**
 * Find the AST function node for a given function name.
 * Handles both `function foo(...)` and `const foo = (...)`.
 */
function findFunctionNode(sourceFile: SourceFile, name: string) {
  // Check function declarations
  for (const decl of sourceFile.getDescendantsOfKind(SyntaxKind.FunctionDeclaration)) {
    if (decl.getName() === name) return decl
  }
  // Check variable declarations: const foo = (...) => ...
  for (const decl of sourceFile.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
    if (decl.getName() === name) {
      const init = decl.getInitializer()
      if (init && (Node.isArrowFunction(init) || Node.isFunctionExpression(init))) {
        return init
      }
    }
  }
  return undefined
}

export function buildCallGraph(functions: InferredFunction[], source: string, fileName: string, registry?: ContractRegistry): CallGraph {
  const sourceFile = createSourceFile(source, fileName)
  const fnNames = new Set(functions.map(f => f.name))
  // Also consider external registry functions as known callees
  const knownNames = new Set([...fnNames, ...(registry?.keys() ?? [])])
  const edges = new Map<string, string[]>()

  for (const fn of functions) {
    const node = findFunctionNode(sourceFile, fn.name)
    if (!node) {
      edges.set(fn.name, [])
      continue
    }

    const callees: string[] = []
    for (const call of node.getDescendantsOfKind(SyntaxKind.CallExpression)) {
      const expr = call.getExpression()
      let calleeName: string | undefined

      if (Node.isIdentifier(expr)) {
        calleeName = expr.getText()
      } else if (Node.isPropertyAccessExpression(expr)) {
        // For method calls like price.dividedBy(x), use the full dotted name
        // AND the last segment — registry may have either
        calleeName = expr.getName()
        const fullName = expr.getText()
        if (fullName !== calleeName && knownNames.has(fullName)) {
          calleeName = fullName
        }
      }

      if (calleeName && knownNames.has(calleeName) && calleeName !== fn.name) {
        if (!callees.includes(calleeName)) {
          callees.push(calleeName)
        }
      }
    }

    edges.set(fn.name, callees)
  }

  // Topological sort via reverse post-order DFS (leaves first)
  const order: string[] = []
  const visited = new Set<string>()
  const visiting = new Set<string>() // for cycle detection

  function dfs(name: string) {
    if (visited.has(name)) return
    if (visiting.has(name)) return // back-edge (cycle), skip
    visiting.add(name)

    const deps = edges.get(name) ?? []
    for (const dep of deps) {
      dfs(dep)
    }

    visiting.delete(name)
    visited.add(name)
    order.push(name)
  }

  for (const fn of functions) {
    dfs(fn.name)
  }

  return { edges, order }
}

/**
 * Convert a registry Predicate to an InferredContract-compatible requires.
 */
function predicateToRequires(predicate: Predicate, calleeName: string): InferredContract | null {
  if (typeof predicate === 'string') return null // string predicates can't be substituted
  return {
    kind: 'requires',
    text: prettyExpr(predicate),
    predicate,
    confidence: 'propagated',
    source: `from calling ${calleeName}()`,
  }
}

export function propagateContracts(
  functions: InferredFunction[],
  callGraph: CallGraph,
  source: string,
  fileName: string,
  registry?: ContractRegistry,
): InferredFunction[] {
  const sourceFile = createSourceFile(source, fileName)
  const fnMap = new Map<string, InferredFunction>()
  for (const fn of functions) {
    fnMap.set(fn.name, { ...fn, contracts: [...fn.contracts] })
  }

  for (const name of callGraph.order) {
    const caller = fnMap.get(name)
    if (!caller) continue

    const node = findFunctionNode(sourceFile, name)
    if (!node) continue

    const existingTexts = new Set(caller.contracts.map(c => c.text))

    for (const call of node.getDescendantsOfKind(SyntaxKind.CallExpression)) {
      const expr = call.getExpression()
      let calleeName: string | undefined

      if (Node.isIdentifier(expr)) {
        calleeName = expr.getText()
      } else if (Node.isPropertyAccessExpression(expr)) {
        calleeName = expr.getName()
        const fullName = expr.getText()
        // Prefer full dotted name if registry knows it
        if (registry?.has(fullName)) {
          calleeName = fullName
        }
      }

      if (!calleeName || calleeName === name) continue

      // Look up callee in local functions OR external registry
      const localCallee = fnMap.get(calleeName)
      const externalContract = registry?.get(calleeName)

      // Collect requires to propagate
      let calleeRequires: InferredContract[] = []
      let calleeParams: Array<{ name: string }> = []

      if (localCallee) {
        calleeRequires = localCallee.contracts.filter(c => c.kind === 'requires')
        calleeParams = localCallee.params
      } else if (externalContract) {
        calleeRequires = externalContract.requires
          .map(p => predicateToRequires(p, calleeName!))
          .filter((c): c is InferredContract => c !== null)
        calleeParams = externalContract.params
      }

      if (calleeRequires.length === 0) continue

      const callArgs = call.getArguments()

      for (const req of calleeRequires) {
        let propagatedPredicate = req.predicate

        for (let i = 0; i < calleeParams.length && i < callArgs.length; i++) {
          const paramName = calleeParams[i]!.name
          const argNode = callArgs[i]!
          const argExpr = parseExpr(argNode as any)
          if (argExpr) {
            propagatedPredicate = substituteIdent(propagatedPredicate, paramName, argExpr)
          }
        }

        const text = prettyExpr(propagatedPredicate)

        if (!existingTexts.has(text)) {
          existingTexts.add(text)
          caller.contracts.push({
            kind: 'requires',
            text,
            predicate: propagatedPredicate,
            confidence: 'propagated',
            source: `from calling ${calleeName}()`,
          })
        }
      }
    }
  }

  return functions.map(f => fnMap.get(f.name) ?? f)
}
