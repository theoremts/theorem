import type { FunctionIR, Sort } from '../parser/ir.js'
import { SyntaxKind, Node, type SourceFile, type Block } from 'ts-morph'
import type { InferredContract } from './index.js'

export function extractNullSafety(ir: FunctionIR, sourceFile: SourceFile): InferredContract[] {
  if (!ir.name) return []

  const contracts: InferredContract[] = []

  // Find the function body in the AST
  let body: Block | undefined
  let paramDecls: ReturnType<typeof getParamDecls> = []

  // Try named function declaration
  const fnDecl = sourceFile.getFunction(ir.name)
  if (fnDecl) {
    const b = fnDecl.getBody()
    if (b && b.getKind() === SyntaxKind.Block) {
      body = b as Block
    }
    paramDecls = fnDecl.getParameters()
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
          paramDecls = fnNode.getParameters() ?? []
        }
      }
    }
  }

  if (!body || paramDecls.length === 0) return []

  // For each parameter, check if it's nullable
  for (const param of paramDecls) {
    const paramName = param.getName()
    const typeNode = param.getTypeNode()
    const typeText = typeNode?.getText() ?? ''
    const hasQuestionToken = param.hasQuestionToken()

    // Skip non-nullable params
    if (!hasQuestionToken && !typeText.includes('null') && !typeText.includes('undefined')) {
      continue
    }

    // Check if there's already a null guard in the body
    if (hasNullGuard(body, paramName)) continue

    // Check if all accesses use optional chaining or nullish coalescing
    const accesses = collectPropertyAccesses(body, paramName)
    if (accesses.length === 0) continue // no property accesses, no risk

    const allSafe = accesses.every(a => a.safe)
    if (allSafe) continue // all accesses use ?. or are inside null checks

    // There's at least one unsafe property access on a nullable param
    contracts.push({
      kind: 'requires',
      text: `${paramName} !== null`,
      predicate: {
        kind: 'binary',
        op: '!==',
        left: { kind: 'ident', name: paramName },
        right: { kind: 'literal', value: null },
      },
      confidence: 'heuristic',
      source: 'nullable parameter accessed without guard',
    })
  }

  return contracts
}

export function extractNullSafetyFromNode(
  params: Array<{ name: string; sort: Sort; isNullable: boolean }>,
  body: Block
): InferredContract[] {
  const contracts: InferredContract[] = []

  for (const param of params) {
    if (!param.isNullable) continue

    const paramName = param.name

    // Check if there's already a null guard in the body
    if (hasNullGuard(body, paramName)) continue

    // Check if all accesses use optional chaining or nullish coalescing
    const accesses = collectPropertyAccesses(body, paramName)
    if (accesses.length === 0) continue // no property accesses, no risk

    const allSafe = accesses.every(a => a.safe)
    if (allSafe) continue // all accesses use ?. or are inside null checks

    // There's at least one unsafe property access on a nullable param
    contracts.push({
      kind: 'requires',
      text: `${paramName} !== null`,
      predicate: {
        kind: 'binary',
        op: '!==',
        left: { kind: 'ident', name: paramName },
        right: { kind: 'literal', value: null },
      },
      confidence: 'heuristic',
      source: 'nullable parameter accessed without guard',
    })
  }

  return contracts
}

type ParamDecl = { getName(): string; getTypeNode(): any; hasQuestionToken(): boolean }
function getParamDecls(_fn: any): ParamDecl[] { return [] }

/**
 * Check if the function body has a null guard (early exit) for the given parameter.
 */
function hasNullGuard(body: Block, paramName: string): boolean {
  const statements = body.getStatements()

  for (const stmt of statements) {
    if (stmt.getKind() !== SyntaxKind.IfStatement) continue

    const ifStmt = stmt as any
    // Only check if-statements without else (guard pattern)
    if (ifStmt.getElseStatement()) continue

    const thenBranch = ifStmt.getThenStatement()
    if (!isUnconditionalExit(thenBranch)) continue

    const condText = ifStmt.getExpression().getText().trim()

    // Check if condition is a null check on this param
    if (
      condText === `${paramName} === null` ||
      condText === `${paramName} === undefined` ||
      condText === `${paramName} == null` ||
      condText === `${paramName} == undefined` ||
      condText === `!${paramName}` ||
      condText === `${paramName} === null || ${paramName} === undefined` ||
      condText === `${paramName} == null || ${paramName} == undefined`
    ) {
      return true
    }
  }

  return false
}

function isUnconditionalExit(node: any): boolean {
  const kind = node.getKind()
  if (kind === SyntaxKind.ThrowStatement || kind === SyntaxKind.ReturnStatement) return true
  if (kind === SyntaxKind.Block) {
    const stmts = (node as Block).getStatements()
    if (stmts.length === 0) return false
    const last = stmts[stmts.length - 1]!
    const lastKind = last.getKind()
    return lastKind === SyntaxKind.ThrowStatement || lastKind === SyntaxKind.ReturnStatement
  }
  return false
}

interface AccessInfo {
  safe: boolean // true if uses ?. or is inside a null check
}

/**
 * Collect all PropertyAccessExpression nodes where the object is the given param name.
 * Each is tagged as safe (uses optional chaining) or unsafe.
 */
function collectPropertyAccesses(body: Block, paramName: string): AccessInfo[] {
  const accesses: AccessInfo[] = []

  for (const node of body.getDescendantsOfKind(SyntaxKind.PropertyAccessExpression)) {
    const objExpr = node.getExpression()
    if (!Node.isIdentifier(objExpr)) continue
    if (objExpr.getText() !== paramName) continue

    // Optional chaining is safe
    if (node.hasQuestionDotToken()) {
      accesses.push({ safe: true })
      continue
    }

    // Check if inside a null-check guard (if (x !== null) { ... x.foo ... })
    if (isInsideNullCheck(node, paramName)) {
      accesses.push({ safe: true })
      continue
    }

    accesses.push({ safe: false })
  }

  return accesses
}

/**
 * Check if a node is inside an if-then branch that guards against null for the param.
 */
function isInsideNullCheck(node: Node, paramName: string): boolean {
  let current: Node | undefined = node.getParent()
  while (current !== undefined) {
    if (Node.isIfStatement(current)) {
      const thenStmt = current.getThenStatement()
      if (nodeContains(thenStmt, node)) {
        const condText = current.getExpression().getText().trim()
        if (
          condText === `${paramName} != null` ||
          condText === `${paramName} !== null` ||
          condText === `${paramName} !== undefined` ||
          condText === `${paramName} != undefined` ||
          condText === paramName
        ) {
          return true
        }
      }
    }
    current = current.getParent()
  }
  return false
}

function nodeContains(ancestor: Node, descendant: Node): boolean {
  return ancestor.getStart() <= descendant.getStart() &&
         descendant.getEnd() <= ancestor.getEnd()
}
