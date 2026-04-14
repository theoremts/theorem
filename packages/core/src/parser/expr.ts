import { Node, SyntaxKind, type Expression, type Statement, type Block } from 'ts-morph'
import type { BinaryOp, Expr, Loc, LoopInfo } from './ir.js'
import { substituteExpr } from '../translator/substitution.js'

/** Extract source location from a ts-morph node. */
function getLoc(node: { getStartLineNumber(): number; getStart(): number }): Loc {
  return { line: node.getStartLineNumber(), column: 0 }
}

/** Attach source location to an Expr if not already present. */
function withLoc(expr: Expr | null, node: { getStartLineNumber(): number; getStart(): number }): Expr | null {
  if (expr === null) return null
  if (expr.loc) return expr
  return { ...expr, loc: getLoc(node) } as Expr
}

/**
 * Converts a ts-morph expression node to our Expr IR.
 * Returns null when the node can't be represented.
 */
export function parseExpr(node: Expression): Expr | null {
  const result = parseExprInner(node)
  return withLoc(result, node)
}

function parseExprInner(node: Expression): Expr | null {
  // Parenthesised — unwrap
  if (Node.isParenthesizedExpression(node)) {
    return parseExpr(node.getExpression())
  }

  // Type assertion: x as T — unwrap
  if (Node.isAsExpression(node)) {
    return parseExpr(node.getExpression())
  }

  // Satisfies expression: x satisfies T — unwrap
  if (node.getKind() === SyntaxKind.SatisfiesExpression) {
    return parseExpr((node as any).getExpression())
  }

  // Non-null assertion: x! — unwrap
  if (Node.isNonNullExpression(node)) {
    return parseExpr(node.getExpression())
  }

  // ── Literals ────────────────────────────────────────────────────────────────

  // Numeric literal
  if (Node.isNumericLiteral(node)) {
    return { kind: 'literal', value: Number(node.getLiteralValue()) }
  }

  // Boolean literals
  if (node.getKind() === SyntaxKind.TrueKeyword) {
    return { kind: 'literal', value: true }
  }
  if (node.getKind() === SyntaxKind.FalseKeyword) {
    return { kind: 'literal', value: false }
  }

  // null
  if (node.getKind() === SyntaxKind.NullKeyword) {
    return { kind: 'literal', value: null }
  }

  // undefined
  if (Node.isIdentifier(node) && node.getText() === 'undefined') {
    return { kind: 'literal', value: null }  // treat undefined same as null
  }

  // String literal
  if (Node.isStringLiteral(node)) {
    return { kind: 'literal', value: node.getLiteralValue() }
  }

  // Template literal: `hello ${name}, you have ${count} items`
  if (Node.isTemplateExpression(node)) {
    const parts: Array<string | Expr> = []
    parts.push(node.getHead().getLiteralText())
    for (const span of node.getTemplateSpans()) {
      const expr = parseExpr(span.getExpression() as Expression)
      if (expr === null) return null
      parts.push(expr)
      parts.push(span.getLiteral().getLiteralText())
    }
    return { kind: 'template', parts }
  }

  // No-substitution template: `hello world`
  if (Node.isNoSubstitutionTemplateLiteral(node)) {
    return { kind: 'literal', value: node.getLiteralText() }
  }

  // Array literal: [1, 2, 3]
  if (Node.isArrayLiteralExpression(node)) {
    const elements: Expr[] = []
    for (const el of node.getElements()) {
      if (Node.isSpreadElement(el)) {
        const inner = parseExpr(el.getExpression() as Expression)
        if (inner === null) return null
        elements.push({ kind: 'spread', operand: inner })
      } else {
        const parsed = parseExpr(el as Expression)
        if (parsed === null) return null
        elements.push(parsed)
      }
    }
    return { kind: 'array', elements }
  }

  // Object literal: { a: 1, b: 2 }
  if (Node.isObjectLiteralExpression(node)) {
    const properties: Array<{ key: string; value: Expr }> = []
    for (const prop of node.getProperties()) {
      if (Node.isPropertyAssignment(prop)) {
        const key = prop.getName()
        const val = parseExpr(prop.getInitializer()! as Expression)
        if (val === null) return null
        properties.push({ key, value: val })
      } else if (Node.isShorthandPropertyAssignment(prop)) {
        const key = prop.getName()
        properties.push({ key, value: { kind: 'ident', name: key } })
      } else if (Node.isSpreadAssignment(prop)) {
        const inner = parseExpr(prop.getExpression() as Expression)
        if (inner === null) return null
        properties.push({ key: '...', value: { kind: 'spread', operand: inner } })
      } else {
        return null  // computed properties, methods, etc.
      }
    }
    return { kind: 'object', properties }
  }

  // ── Identifiers & access ────────────────────────────────────────────────────

  // Identifier
  if (Node.isIdentifier(node)) {
    return { kind: 'ident', name: node.getText() }
  }

  // Property access: obj.prop
  if (Node.isPropertyAccessExpression(node)) {
    const obj = parseExpr(node.getExpression())
    if (obj === null) return null
    return { kind: 'member', object: obj, property: node.getName() }
  }

  // Element access: arr[i]
  if (Node.isElementAccessExpression(node)) {
    const obj = parseExpr(node.getExpression())
    const idx = parseExpr(node.getArgumentExpression()! as Expression)
    if (obj === null || idx === null) return null
    return { kind: 'element-access', object: obj, index: idx }
  }

  // ── Unary expressions ──────────────────────────────────────────────────────

  if (Node.isPrefixUnaryExpression(node)) {
    const tok = node.getOperatorToken()

    // Logical NOT: !expr
    if (tok === SyntaxKind.ExclamationToken) {
      const operand = parseExpr(node.getOperand())
      if (operand === null) return null
      return { kind: 'unary', op: '!', operand }
    }

    // Unary minus: -5 → literal(-5), -x → 0 - x
    if (tok === SyntaxKind.MinusToken) {
      const inner = parseExpr(node.getOperand())
      if (inner === null) return null
      if (inner.kind === 'literal' && typeof inner.value === 'number') {
        return { kind: 'literal', value: -inner.value }
      }
      return { kind: 'unary', op: '-', operand: inner }
    }

    // Unary plus: +x → x (identity for numbers)
    if (tok === SyntaxKind.PlusToken) {
      return parseExpr(node.getOperand())
    }

    return null
  }

  // typeof
  if (Node.isTypeOfExpression(node)) {
    const operand = parseExpr(node.getExpression())
    if (operand === null) return null
    return { kind: 'unary', op: 'typeof', operand }
  }

  // Postfix: x++, x-- — treated as x (the value before increment)
  if (Node.isPostfixUnaryExpression(node)) {
    return parseExpr(node.getOperand())
  }

  // void expr — evaluates to undefined
  if (node.getKind() === SyntaxKind.VoidExpression) {
    return { kind: 'literal', value: null }
  }

  // ── Binary expression ──────────────────────────────────────────────────────

  if (Node.isBinaryExpression(node)) {
    const opText = node.getOperatorToken().getText()
    const op = binaryOp(opText)
    if (op === null) return null
    const left = parseExpr(node.getLeft())
    const right = parseExpr(node.getRight())
    if (left === null || right === null) return null
    return { kind: 'binary', op, left, right }
  }

  // ── Conditional / ternary: condition ? then : else ─────────────────────────

  if (Node.isConditionalExpression(node)) {
    const condition = parseExpr(node.getCondition())
    const then = parseExpr(node.getWhenTrue())
    const els  = parseExpr(node.getWhenFalse())
    if (condition === null || then === null || els === null) return null
    return { kind: 'ternary', condition, then, else: els }
  }

  // ── Call expression: callee(args...) ───────────────────────────────────────

  if (Node.isCallExpression(node)) {
    const calleeExpr = node.getExpression()
    let callee: string | null = null
    if (Node.isIdentifier(calleeExpr)) {
      callee = calleeExpr.getText()
    } else if (Node.isPropertyAccessExpression(calleeExpr)) {
      callee = calleeExpr.getText()
    }
    if (callee === null) return null

    // Quantifiers: forall(x => P(x)), exists(x => P(x))
    if (callee === 'forall' || callee === 'exists') {
      const firstArg = node.getArguments()[0]
      if (Node.isArrowFunction(firstArg)) {
        const boundParams = firstArg.getParameters()
        if (boundParams.length > 0) {
          const param = boundParams[0]!.getName()
          const arrowBody = firstArg.getBody()
          if (Node.isExpression(arrowBody)) {
            const bodyExpr = parseExpr(arrowBody)
            if (bodyExpr !== null) {
              return { kind: 'quantifier', quantifier: callee, param, body: bodyExpr }
            }
          }
        }
      }
    }

    const args: Expr[] = []
    for (const arg of node.getArguments()) {
      if (Node.isArrowFunction(arg)) {
        args.push({ kind: 'ident', name: '__fn__' })
        continue
      }
      if (Node.isSpreadElement(arg)) {
        const inner = parseExpr((arg as any).getExpression() as Expression)
        if (inner === null) return null
        args.push({ kind: 'spread', operand: inner })
        continue
      }
      const parsed = parseExpr(arg as Expression)
      if (parsed === null) return null
      args.push(parsed)
    }
    return { kind: 'call', callee, args }
  }

  // ── Arrow function (as expression value) ───────────────────────────────────

  if (Node.isArrowFunction(node)) {
    return { kind: 'ident', name: '__fn__' }
  }

  // ── Function expression ────────────────────────────────────────────────────

  if (Node.isFunctionExpression(node)) {
    return { kind: 'ident', name: '__fn__' }
  }

  // ── new expression: new Foo(args) ──────────────────────────────────────────

  if (Node.isNewExpression(node)) {
    const callee = node.getExpression().getText()
    const args: Expr[] = []
    for (const arg of node.getArguments() ?? []) {
      const parsed = parseExpr(arg as Expression)
      if (parsed === null) return null
      args.push(parsed)
    }
    return { kind: 'call', callee: `new ${callee}`, args }
  }

  // ── Comma expression: (a, b) — return last ────────────────────────────────

  if (Node.isCommaListExpression?.(node)) {
    const elements = (node as any).getElements() as Expression[]
    if (elements.length === 0) return null
    return parseExpr(elements[elements.length - 1]!)
  }

  // ── Await expression: await x — unwrap for IR ──────────────────────────────

  if (Node.isAwaitExpression(node)) {
    return parseExpr(node.getExpression())
  }

  // ── Yield expression — opaque ──────────────────────────────────────────────

  if (Node.isYieldExpression(node)) {
    const expr = node.getExpression()
    return expr ? parseExpr(expr as Expression) : null
  }

  // ── Tagged template — opaque call ──────────────────────────────────────────

  if (Node.isTaggedTemplateExpression(node)) {
    return { kind: 'call', callee: node.getTag().getText(), args: [] }
  }

  // ── this ───────────────────────────────────────────────────────────────────

  if (node.getKind() === SyntaxKind.ThisKeyword) {
    return { kind: 'ident', name: 'this' }
  }

  // ── super ──────────────────────────────────────────────────────────────────

  if (node.getKind() === SyntaxKind.SuperKeyword) {
    return { kind: 'ident', name: 'super' }
  }

  return null
}

// ---------------------------------------------------------------------------
// Block body parser — converts if/return/switch chains to nested ternaries
// ---------------------------------------------------------------------------

export function parseBlockToExpr(block: Block): Expr | null {
  return parseStmtList(block.getStatements(), new Map())
}

/**
 * Parses a list of statements into an expression.
 * Handles return, if/return chains, switch/case, const/let inlining,
 * let + if/else assignment, and loops.
 */
/** Collected positional check/assume with SSA bindings applied. */
let _resolvedPositionalContracts: Array<{ kind: 'check' | 'assume'; predicate: Expr }> = []
/** Final SSA bindings after processing all statements. */
let _finalSSABindings: Map<string, Expr> = new Map()

export function parseStmtListDirect(stmts: Statement[]): Expr | null {
  _resolvedPositionalContracts = []
  _finalSSABindings = new Map()
  return parseStmtList(stmts, new Map())
}

export function getResolvedPositionalContracts(): Array<{ kind: 'check' | 'assume'; predicate: Expr }> {
  return _resolvedPositionalContracts
}

/**
 * Returns the final SSA bindings from the last `parseStmtListDirect` call.
 * Used to resolve ensures predicates to see final variable values.
 */
export function getFinalSSABindings(): Map<string, Expr> {
  return _finalSSABindings
}

function parseStmtList(stmts: Statement[], bindings?: Map<string, Expr>): Expr | null {
  const b = bindings ?? new Map<string, Expr>()
  return parseWithBindings(stmts, b)
}

/**
 * Processes statements sequentially, maintaining a bindings map (SSA-style).
 *
 * Tracks: const/let declarations, let+if assignments, compound assignments
 * (x += y, x -= y, x *= y, etc.), postfix/prefix increment/decrement.
 *
 * All bindings are resolved eagerly: when creating binding N, all bindings
 * 0..N-1 are applied to the RHS first. This ensures correct mutation tracking.
 */
function parseWithBindings(stmts: Statement[], bindings: Map<string, Expr>): Expr | null {
  if (stmts.length === 0) return null

  const [first, ...rest] = stmts as [Statement, ...Statement[]]

  // ── return expr; — apply all bindings ─────────────────────────────────────
  if (Node.isReturnStatement(first)) {
    // Save final SSA bindings for ensures resolution
    _finalSSABindings = new Map(bindings)
    const expr = first.getExpression()
    if (!expr) return null
    const parsed = parseExpr(expr as Expression)
    if (parsed === null) return null
    return bindings.size > 0 ? substituteExpr(parsed, bindings) : parsed
  }

  // ── if (cond) ... — could be if/return (ternary) or if/assign (binding update) ──
  if (Node.isIfStatement(first)) {
    let cond = parseExpr(first.getExpression() as Expression)
    if (cond === null) return null
    if (bindings.size > 0) cond = substituteExpr(cond, bindings)

    // First try: if/return pattern → ternary expression
    const thenExpr = stmtToExprWithBindings(first.getThenStatement(), [], bindings)
    if (thenExpr !== null) {
      const elseNode = first.getElseStatement()
      const elseExpr = elseNode
        ? stmtToExprWithBindings(elseNode, rest, bindings)
        : parseWithBindings(rest, bindings)
      if (elseExpr !== null) {
        return { kind: 'ternary', condition: cond, then: thenExpr, else: elseExpr }
      }
    }

    // Second try: if/assign pattern → SSA binding update
    // `if (x > 100) x = 50` → update binding: x = cond ? 50 : x
    const ifAssignments = extractIfAssignments(first, bindings)
    if (ifAssignments !== null) {
      const newBindings = new Map(bindings)
      for (const [varName, value] of ifAssignments) {
        const current: Expr = newBindings.get(varName) ?? { kind: 'ident', name: varName }
        newBindings.set(varName, { kind: 'ternary', condition: cond, then: value, else: current })
      }
      return parseWithBindings(rest, newBindings)
    }

    // Fallback: skip the if and continue
    return parseWithBindings(rest, bindings)
  }

  // ── switch (expr) { ... } ─────────────────────────────────────────────────
  if (Node.isSwitchStatement(first)) {
    const result = parseSwitchToExpr(first, rest)
    return result && bindings.size > 0 ? substituteExpr(result, bindings) : result
  }

  // ── Variable declaration: const/let ────────────────────────────────────────
  if (Node.isVariableStatement(first)) {
    const newBindings = new Map(bindings)
    let consumedStmts = 0

    for (const decl of first.getDeclarations()) {
      // ── Array destructuring: const [a, b] = expr ────────────────────────
      try {
        const nameNode = decl.getNameNode()
        if (Node.isArrayBindingPattern(nameNode)) {
          const init = decl.getInitializer()
          const elements = nameNode.getElements()
          // Check if RHS is an array literal: const [a, b] = [expr1, expr2]
          if (init && Node.isArrayLiteralExpression(init)) {
            const rhsElements = init.getElements()
            for (let i = 0; i < elements.length; i++) {
              const el = elements[i]
              if (!el || Node.isOmittedExpression(el)) continue
              if (!Node.isBindingElement(el)) continue
              const elName = el.getNameNode().getText()
              if (i < rhsElements.length) {
                let parsed = parseExpr(rhsElements[i] as Expression)
                if (parsed !== null) {
                  if (newBindings.size > 0) parsed = substituteExpr(parsed, newBindings)
                  newBindings.set(elName, parsed)
                }
              }
            }
          } else {
            // RHS is a function call or other expression — treat destructured vars as free (unbound)
            // They will be created as free Z3 variables when referenced
            for (const el of elements) {
              if (!el || Node.isOmittedExpression(el)) continue
              if (!Node.isBindingElement(el)) continue
              const elName = el.getNameNode().getText()
              newBindings.set(elName, { kind: 'ident', name: elName })
            }
          }
          continue  // skip normal declaration handling for this decl
        }
      } catch {
        // If array destructuring parsing fails, fall through to normal handling
      }

      const varName = decl.getName()
      const init = decl.getInitializer()
      if (init) {
        let parsed = parseExpr(init as Expression)
        if (parsed !== null) {
          // Resolve with current bindings so mutations are tracked
          if (newBindings.size > 0) parsed = substituteExpr(parsed, newBindings)
          newBindings.set(varName, parsed)
          // Check for follow-up if-reassignment: let x = 0; if (...) x = a;
          const nextStmt = rest[consumedStmts]
          if (nextStmt && Node.isIfStatement(nextStmt)) {
            const resolved = resolveIfAssignmentWithDefault(varName, nextStmt, parsed)
            if (resolved !== null) {
              newBindings.set(varName, newBindings.size > 0 ? substituteExpr(resolved, newBindings) : resolved)
              consumedStmts++
            }
          }
        }
      } else {
        // let x; — look for if-assignment
        const nextStmt = rest[consumedStmts]
        if (nextStmt && Node.isIfStatement(nextStmt)) {
          let resolved = resolveIfAssignment(varName, nextStmt)
          if (resolved !== null) {
            if (newBindings.size > 0) resolved = substituteExpr(resolved, newBindings)
            newBindings.set(varName, resolved)
            consumedStmts++
          }
        }
      }
    }

    return parseWithBindings(rest.slice(consumedStmts), newBindings)
  }

  // ── Expression statement: assignments and mutations ────────────────────────
  if (Node.isExpressionStatement(first)) {
    const expr = first.getExpression()

    // Simple or compound assignment: x = expr, x += expr, x -= expr, etc.
    if (Node.isBinaryExpression(expr)) {
      const op = expr.getOperatorToken().getText()
      const left = expr.getLeft()

      if (Node.isIdentifier(left) && isAssignmentOp(op)) {
        const varName = left.getText()
        let rhs = parseAssignmentRHS(op, varName, expr.getRight() as Expression, bindings)
        if (rhs !== null) {
          const newBindings = new Map(bindings)
          newBindings.set(varName, rhs)
          return parseWithBindings(rest, newBindings)
        }
      }
    }

    // Postfix: x++, x--
    if (Node.isPostfixUnaryExpression(expr)) {
      const operand = expr.getOperand()
      if (Node.isIdentifier(operand)) {
        const varName = operand.getText()
        const tok = expr.getOperatorToken()
        const current: Expr = bindings.get(varName) ?? { kind: 'ident', name: varName }
        const one: Expr = { kind: 'literal', value: 1 }
        const newVal: Expr = tok === SyntaxKind.PlusPlusToken
          ? { kind: 'binary', op: '+', left: current, right: one }
          : { kind: 'binary', op: '-', left: current, right: one }
        const newBindings = new Map(bindings)
        newBindings.set(varName, newVal)
        return parseWithBindings(rest, newBindings)
      }
    }

    // Prefix: ++x, --x
    if (Node.isPrefixUnaryExpression(expr)) {
      const operand = expr.getOperand()
      if (Node.isIdentifier(operand)) {
        const tok = expr.getOperatorToken()
        if (tok === SyntaxKind.PlusPlusToken || tok === SyntaxKind.MinusMinusToken) {
          const varName = operand.getText()
          const current: Expr = bindings.get(varName) ?? { kind: 'ident', name: varName }
          const one: Expr = { kind: 'literal', value: 1 }
          const newVal: Expr = tok === SyntaxKind.PlusPlusToken
            ? { kind: 'binary', op: '+', left: current, right: one }
            : { kind: 'binary', op: '-', left: current, right: one }
          const newBindings = new Map(bindings)
          newBindings.set(varName, newVal)
          return parseWithBindings(rest, newBindings)
        }
      }
    }

    // check() / assume() — capture with current SSA bindings applied
    if (Node.isCallExpression(expr)) {
      const callee = expr.getExpression().getText()
      if (callee === 'check' || callee === 'assume') {
        const args = expr.getArguments()
        if (args.length > 0) {
          const firstArg = args[0]!
          let predicate: Expr | null = null

          if (Node.isArrowFunction(firstArg)) {
            // check(() => x >= 0) or check(x => positive(x))
            const arrowBody = firstArg.getBody()
            if (Node.isExpression(arrowBody)) {
              predicate = parseExpr(arrowBody)
            }
          } else {
            // check(x >= 0) or check(nonNegative(x)) — direct expression
            predicate = parseExpr(firstArg as Expression)
          }

          if (predicate !== null) {
            if (bindings.size > 0) predicate = substituteExpr(predicate, bindings)
            _resolvedPositionalContracts.push({ kind: callee, predicate })
          }
        }
      }
    }

    // Non-assignment expression — skip
    return parseWithBindings(rest, bindings)
  }

  // ── while / for — skip for expression body (loops handled separately) ─────
  if (Node.isWhileStatement(first) || Node.isForStatement(first)) {
    return parseWithBindings(rest, bindings)
  }

  // ── throw ─────────────────────────────────────────────────────────────────
  if (Node.isThrowStatement(first)) {
    return { kind: 'literal', value: null }
  }

  return null
}

// ── Assignment helpers ───────────────────────────────────────────────────────

/**
 * Extracts variable assignments from an if-statement (no return/no else).
 * `if (cond) x = a` → Map { x: a }
 * `if (cond) { x = a; y = b; }` → Map { x: a, y: b }
 */
function extractIfAssignments(
  ifStmt: Statement,
  bindings: Map<string, Expr>,
): Map<string, Expr> | null {
  if (!Node.isIfStatement(ifStmt)) return null
  const thenStmt = ifStmt.getThenStatement()
  const assignments = new Map<string, Expr>()

  const stmts = Node.isBlock(thenStmt) ? thenStmt.getStatements() : [thenStmt]
  for (const s of stmts) {
    if (!Node.isExpressionStatement(s)) return null
    const expr = s.getExpression()
    if (!Node.isBinaryExpression(expr)) return null
    const op = expr.getOperatorToken().getText()
    const left = expr.getLeft()
    if (!Node.isIdentifier(left)) return null

    const varName = left.getText()
    const rhs = parseAssignmentRHS(op, varName, expr.getRight() as Expression, bindings)
    if (rhs === null) return null
    assignments.set(varName, rhs)
  }

  return assignments.size > 0 ? assignments : null
}

const COMPOUND_OPS: Record<string, BinaryOp> = {
  '+=': '+', '-=': '-', '*=': '*', '/=': '/', '%=': '%',
}

function isAssignmentOp(op: string): boolean {
  return op === '=' || op in COMPOUND_OPS
}

function parseAssignmentRHS(
  op: string,
  varName: string,
  rhsNode: Expression,
  bindings: Map<string, Expr>,
): Expr | null {
  let rhs = parseExpr(rhsNode)
  if (rhs === null) return null
  // Resolve RHS with current bindings
  if (bindings.size > 0) rhs = substituteExpr(rhs, bindings)

  if (op === '=') return rhs

  // Compound: x += a → x_old + a
  const binaryOp = COMPOUND_OPS[op]
  if (!binaryOp) return null
  const current: Expr = bindings.get(varName) ?? { kind: 'ident', name: varName }
  return { kind: 'binary', op: binaryOp, left: current, right: rhs }
}

function stmtToExprWithBindings(stmt: Statement, fallthrough: Statement[], bindings: Map<string, Expr>): Expr | null {
  if (Node.isReturnStatement(stmt)) {
    const expr = stmt.getExpression()
    if (!expr) return null
    const parsed = parseExpr(expr as Expression)
    if (parsed === null) return null
    return bindings.size > 0 ? substituteExpr(parsed, bindings) : parsed
  }
  if (Node.isBlock(stmt)) {
    const inner = stmt.getStatements()
    const all = inner.some(s => Node.isReturnStatement(s) || Node.isIfStatement(s) || Node.isSwitchStatement(s))
      ? inner : [...inner, ...fallthrough]
    return parseWithBindings(all as Statement[], bindings)
  }
  if (Node.isIfStatement(stmt)) {
    return parseWithBindings([stmt, ...fallthrough], bindings)
  }
  if (Node.isThrowStatement(stmt)) {
    return { kind: 'literal', value: null }
  }
  return null
}

/**
 * Extracts the return value from a single statement used as an if-branch.
 */
function stmtToExpr(stmt: Statement, fallthrough: Statement[]): Expr | null {
  // return expr;
  if (Node.isReturnStatement(stmt)) {
    const expr = stmt.getExpression()
    return expr ? parseExpr(expr as Expression) : null
  }

  // { ... }
  if (Node.isBlock(stmt)) {
    const inner = stmt.getStatements()
    const all = inner.some(s => Node.isReturnStatement(s) || Node.isIfStatement(s) || Node.isSwitchStatement(s))
      ? inner
      : [...inner, ...fallthrough]
    return parseStmtList(all as Statement[])
  }

  // else if (cond) ... — IfStatement directly as else-branch
  if (Node.isIfStatement(stmt)) {
    return parseStmtList([stmt, ...fallthrough])
  }

  // throw — treat as undefined (error path)
  if (Node.isThrowStatement(stmt)) {
    return { kind: 'literal', value: null }
  }

  return null
}

// ---------------------------------------------------------------------------
// Switch → nested ternary
//
//   switch (x) {
//     case 1: return a
//     case 2: return b
//     default: return c
//   }
//   → x === 1 ? a : x === 2 ? b : c
// ---------------------------------------------------------------------------

function parseSwitchToExpr(switchStmt: any, fallthrough: Statement[]): Expr | null {
  const discriminant = parseExpr(switchStmt.getExpression() as Expression)
  if (discriminant === null) return null

  const clauses = switchStmt.getClauses()
  return buildSwitchChain(discriminant, clauses, 0, fallthrough)
}

function buildSwitchChain(
  discriminant: Expr,
  clauses: any[],
  index: number,
  fallthrough: Statement[],
): Expr | null {
  if (index >= clauses.length) {
    return parseStmtList(fallthrough)
  }

  const clause = clauses[index]

  // default:
  if (Node.isCaseClause(clause) === false) {
    // DefaultClause
    const stmts = clause.getStatements() as Statement[]
    return extractReturnFromClause(stmts) ?? parseStmtList(fallthrough)
  }

  // case value:
  const caseExpr = parseExpr(clause.getExpression() as Expression)
  if (caseExpr === null) return null

  const condition: Expr = { kind: 'binary', op: '===', left: discriminant, right: caseExpr }

  const stmts = clause.getStatements() as Statement[]
  const thenExpr = extractReturnFromClause(stmts)
  if (thenExpr === null) return null

  const elseExpr = buildSwitchChain(discriminant, clauses, index + 1, fallthrough)
  if (elseExpr === null) return null

  return { kind: 'ternary', condition, then: thenExpr, else: elseExpr }
}

function extractReturnFromClause(stmts: Statement[]): Expr | null {
  for (const s of stmts) {
    if (Node.isReturnStatement(s)) {
      const expr = s.getExpression()
      return expr ? parseExpr(expr as Expression) : null
    }
    if (Node.isBlock(s)) {
      const inner = extractReturnFromClause(s.getStatements())
      if (inner !== null) return inner
    }
    if (Node.isIfStatement(s)) {
      // Inline if inside case
      return stmtToExprWithBindings(s, [], new Map())
    }
    if (Node.isThrowStatement(s)) {
      return { kind: 'literal', value: null }
    }
  }
  return null
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const OPS: Record<string, BinaryOp> = {
  '+': '+', '-': '-', '*': '*', '/': '/', '%': '%', '**': '**',
  '<': '<', '<=': '<=', '>': '>', '>=': '>=',
  '===': '===', '!==': '!==',
  '&&': '&&', '||': '||',
  '??': '??',
  'in': 'in',
  // Also accept loose equality for convenience
  '==': '===', '!=': '!==',
}

function binaryOp(text: string): BinaryOp | null {
  return OPS[text] ?? null
}

/**
 * Resolves `let x; if (cond) x = a; else if (...) x = b; else x = c;`
 * into a ternary expression: `cond ? a : ... ? b : c`.
 */
function resolveIfAssignment(varName: string, ifStmt: Statement): Expr | null {
  if (!Node.isIfStatement(ifStmt)) return null

  const cond = parseExpr(ifStmt.getExpression() as Expression)
  if (cond === null) return null

  const thenValue = extractAssignmentValue(varName, ifStmt.getThenStatement())
  if (thenValue === null) return null

  const elseStmt = ifStmt.getElseStatement()
  let elseValue: Expr | null = null

  if (elseStmt) {
    if (Node.isIfStatement(elseStmt)) {
      // else if (...) → recurse
      elseValue = resolveIfAssignment(varName, elseStmt)
    } else {
      elseValue = extractAssignmentValue(varName, elseStmt)
    }
  }

  if (elseValue === null) return null
  return { kind: 'ternary', condition: cond, then: thenValue, else: elseValue }
}

/**
 * Resolves `let x = default; if (cond) x = a; else if (...) x = b;`
 * The default value fills in branches without assignment.
 */
function resolveIfAssignmentWithDefault(varName: string, ifStmt: Statement, defaultVal: Expr): Expr | null {
  if (!Node.isIfStatement(ifStmt)) return null

  const cond = parseExpr(ifStmt.getExpression() as Expression)
  if (cond === null) return null

  // Check if ANY branch assigns to the variable — if none do, this isn't an if-assignment
  const thenAssign = extractAssignmentValue(varName, ifStmt.getThenStatement())
  const elseStmt = ifStmt.getElseStatement()
  const elseAssign = elseStmt ? extractAssignmentValue(varName, elseStmt) : null

  // At least one branch must assign to the variable, otherwise this is an if/return or other pattern
  if (thenAssign === null && elseAssign === null) return null

  const thenValue = thenAssign ?? defaultVal
  let elseValue: Expr

  if (elseStmt) {
    if (Node.isIfStatement(elseStmt)) {
      elseValue = resolveIfAssignmentWithDefault(varName, elseStmt, defaultVal) ?? defaultVal
    } else {
      elseValue = elseAssign ?? defaultVal
    }
  } else {
    elseValue = defaultVal
  }

  return { kind: 'ternary', condition: cond, then: thenValue, else: elseValue }
}

/**
 * Extracts the assigned value from a branch: `x = expr` or `{ x = expr; }`.
 */
function extractAssignmentValue(varName: string, stmt: Statement): Expr | null {
  // Direct: x = expr;
  if (Node.isExpressionStatement(stmt)) {
    return extractAssignmentFromExpr(varName, stmt.getExpression() as Expression)
  }
  // Block: { x = expr; }
  if (Node.isBlock(stmt)) {
    const stmts = stmt.getStatements()
    for (const s of stmts) {
      if (Node.isExpressionStatement(s)) {
        const val = extractAssignmentFromExpr(varName, s.getExpression() as Expression)
        if (val !== null) return val
      }
    }
  }
  return null
}

function extractAssignmentFromExpr(varName: string, expr: Expression): Expr | null {
  if (!Node.isBinaryExpression(expr)) return null
  const op = expr.getOperatorToken().getText()
  if (op !== '=') return null
  const left = expr.getLeft()
  if (!Node.isIdentifier(left) || left.getText() !== varName) return null
  return parseExpr(expr.getRight())
}

// inlineBindings is now handled by substituteExpr from ../translator/substitution.js

// ---------------------------------------------------------------------------
// Loop extraction — finds while/for loops and extracts invariants/decreases
// ---------------------------------------------------------------------------

/**
 * Parses a block body, returning both the expression (for non-loop parts)
 * and any LoopInfo entries found inside.
 */
export function parseBlockWithLoops(block: Block): { body: Expr | null; loops: LoopInfo[] } {
  const loops: LoopInfo[] = []
  collectLoops(block.getStatements(), loops)
  const body = parseBlockToExpr(block)
  return { body, loops }
}

function collectLoops(stmts: Statement[], out: LoopInfo[]): void {
  // Track variable initializations preceding loops
  const varInits = new Map<string, Expr>()

  for (const stmt of stmts) {
    // Track variable declarations: let x = expr
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarations()) {
        const init = decl.getInitializer()
        if (init) {
          const parsed = parseExpr(init as Expression)
          if (parsed !== null) {
            varInits.set(decl.getName(), parsed)
          }
        }
      }
      continue
    }

    if (Node.isWhileStatement(stmt)) {
      const cond = parseExpr(stmt.getExpression() as Expression)
      if (cond === null) continue

      const loopBody = stmt.getStatement()
      const bodyStmts = Node.isBlock(loopBody)
        ? loopBody.getStatements()
        : [loopBody]

      const invariants: Expr[] = []
      let decreases: Expr | undefined

      extractLoopContracts(bodyStmts, invariants, (d) => { decreases = d })

      // Collect initializations relevant to this loop's invariants/condition
      const initList = varInitsForLoop(varInits, invariants, cond, decreases)

      out.push({ condition: cond, invariants, decreases, body: undefined, initializations: initList.length > 0 ? initList : undefined })

      // Recurse into nested loops
      if (Node.isBlock(loopBody)) {
        collectLoops(loopBody.getStatements(), out)
      }
      continue
    }

    if (Node.isForStatement(stmt)) {
      const condExpr = stmt.getCondition()
      const cond = condExpr ? parseExpr(condExpr as Expression) : null
      if (cond === null) continue

      const loopBody = stmt.getStatement()
      const bodyStmts = Node.isBlock(loopBody)
        ? loopBody.getStatements()
        : [loopBody]

      const invariants: Expr[] = []
      let decreases: Expr | undefined

      extractLoopContracts(bodyStmts, invariants, (d) => { decreases = d })

      const initList = varInitsForLoop(varInits, invariants, cond, decreases)

      out.push({ condition: cond, invariants, decreases, body: undefined, initializations: initList.length > 0 ? initList : undefined })

      // Recurse into nested loops
      if (Node.isBlock(loopBody)) {
        collectLoops(loopBody.getStatements(), out)
      }
      continue
    }

    // Recurse into blocks, if/else, etc.
    if (Node.isBlock(stmt)) {
      collectLoops(stmt.getStatements(), out)
    }
    if (Node.isIfStatement(stmt)) {
      const thenStmt = stmt.getThenStatement()
      if (Node.isBlock(thenStmt)) collectLoops(thenStmt.getStatements(), out)
      const elseStmt = stmt.getElseStatement()
      if (elseStmt && Node.isBlock(elseStmt)) collectLoops((elseStmt as Block).getStatements(), out)
    }
  }
}

/** Collect all tracked variable initializations (all of them — the translator filters). */
function varInitsForLoop(
  varInits: Map<string, Expr>,
  _invariants: Expr[],
  _cond: Expr,
  _decreases: Expr | undefined,
): Array<{ name: string; value: Expr }> {
  const result: Array<{ name: string; value: Expr }> = []
  for (const [name, value] of varInits) {
    result.push({ name, value })
  }
  return result
}

/**
 * Scans statements inside a loop body for invariant() and decreases() calls.
 */
function extractLoopContracts(
  stmts: Statement[],
  invariants: Expr[],
  setDecreases: (d: Expr) => void,
): void {
  for (const stmt of stmts) {
    if (!Node.isExpressionStatement(stmt)) continue
    const expr = stmt.getExpression()
    if (!Node.isCallExpression(expr)) continue

    const callee = expr.getExpression().getText()
    const args = expr.getArguments()

    if (callee === 'invariant' && args.length > 0) {
      const arg = args[0]!
      if (Node.isArrowFunction(arg)) {
        const body = arg.getBody()
        if (Node.isExpression(body)) {
          const parsed = parseExpr(body)
          if (parsed !== null) invariants.push(parsed)
        }
      }
    }

    if (callee === 'decreases' && args.length > 0) {
      const arg = args[0]!
      if (Node.isArrowFunction(arg)) {
        const body = arg.getBody()
        if (Node.isExpression(body)) {
          const parsed = parseExpr(body)
          if (parsed !== null) setDecreases(parsed)
        }
      } else if (Node.isExpression(arg)) {
        const parsed = parseExpr(arg as Expression)
        if (parsed !== null) setDecreases(parsed)
      }
    }
  }
}
