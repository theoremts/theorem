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
    // this.x is normalized to a flat identifier so SSA bindings and
    // substitution treat instance fields like ordinary variables
    if (node.getExpression().getKind() === SyntaxKind.ThisKeyword) {
      return { kind: 'ident', name: `this.${node.getName()}` }
    }
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

    // Regex test: /pattern/.test(x) or RE.test(x) with `const RE = /pattern/`
    if (Node.isPropertyAccessExpression(calleeExpr) && calleeExpr.getName() === 'test') {
      let target: Node = calleeExpr.getExpression()
      if (Node.isIdentifier(target)) {
        const decl = target.getSourceFile().getVariableDeclaration(target.getText())
        const init = decl?.getInitializer()
        if (init !== undefined && Node.isRegularExpressionLiteral(init)) target = init
      }
      if (Node.isRegularExpressionLiteral(target)) {
        const literalText = target.getText()
        const lastSlash = literalText.lastIndexOf('/')
        const patternText = literalText.slice(1, lastSlash)
        const flagsText = literalText.slice(lastSlash + 1)
        const strArg = node.getArguments()[0]
        if (strArg !== undefined) {
          const parsed = parseExpr(strArg as Expression)
          if (parsed !== null) {
            return {
              kind: 'call',
              callee: '__reTest',
              args: [parsed, { kind: 'literal', value: patternText }, { kind: 'literal', value: flagsText }],
            }
          }
        }
      }
    }

    // Quantifiers: forall(x => P(x)), exists(x => P(x))
    if (callee === 'forall' || callee === 'exists') {
      const callArgs = node.getArguments()
      // Array-scoped form: forall(arr, (x, i) => P) — quantifies an INT index
      // over [0, arr.length); x becomes arr[i]. This is the fragment where
      // quantifiers are well-behaved (select-term triggers).
      if (callArgs.length === 2 && Node.isArrowFunction(callArgs[1])) {
        const arrExpr = parseExpr(callArgs[0] as Expression)
        const arrow = callArgs[1]
        const arrowBody = arrow.getBody()
        if (arrExpr !== null && Node.isExpression(arrowBody)) {
          const rawBody = parseExpr(arrowBody)
          const params = arrow.getParameters()
          if (rawBody !== null && params.length >= 1) {
            const qi = nextQuantifierIndexName()
            const bindings = new Map<string, Expr>()
            bindings.set(params[0]!.getName(), { kind: 'element-access', object: arrExpr, index: { kind: 'ident', name: qi } })
            if (params.length >= 2) bindings.set(params[1]!.getName(), { kind: 'ident', name: qi })
            const body = substituteIdents(rawBody, bindings)
            const inRange: Expr = {
              kind: 'binary', op: '&&',
              left: { kind: 'binary', op: '>=', left: { kind: 'ident', name: qi }, right: { kind: 'literal', value: 0 } },
              right: { kind: 'binary', op: '<', left: { kind: 'ident', name: qi }, right: { kind: 'member', object: arrExpr, property: 'length' } },
            }
            return {
              kind: 'quantifier', quantifier: callee, param: qi, sort: 'int',
              display: node.getText().replace(/\s+/g, ' '),
              body: callee === 'forall'
                ? { kind: 'binary', op: '==>', left: inRange, right: body }
                : { kind: 'binary', op: '&&', left: inRange, right: body },
            }
          }
        }
      }
      const firstArg = callArgs[0]
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

    // sumBy(arr, (x) => x.field) / countBy(arr, (x) => P(x)) — fold symbols.
    // sumBy keeps the simple-projection restriction (a named field); countBy
    // stores the predicate with the element replaced by the __cell marker.
    if ((callee === 'sumBy' || callee === 'countBy') && node.getArguments().length === 2) {
      const argsF = node.getArguments()
      const arrExpr = parseExpr(argsF[0] as Expression)
      const arrow = argsF[1]
      if (arrExpr !== null && Node.isArrowFunction(arrow)) {
        const arrowBody = arrow.getBody()
        const params = arrow.getParameters()
        if (Node.isExpression(arrowBody) && params.length >= 1) {
          const display = node.getText().replace(/\s+/g, ' ')
          if (callee === 'sumBy') {
            const proj = parseExpr(arrowBody)
            if (proj !== null && proj.kind === 'member' && proj.object.kind === 'ident'
                && proj.object.name === params[0]!.getName()) {
              return {
                kind: 'call', callee: '__sumBy',
                args: [arrExpr, { kind: 'literal', value: proj.property }, { kind: 'literal', value: display }],
              }
            }
          } else {
            const rawPred = parseExpr(arrowBody)
            if (rawPred !== null) {
              const pred = substituteIdents(rawPred, new Map([[params[0]!.getName(), { kind: 'ident', name: '__cell' } as Expr]]))
              return {
                kind: 'call', callee: '__countBy',
                args: [arrExpr, pred, { kind: 'literal', value: display }],
              }
            }
          }
        }
      }
    }

    // Array.prototype.reduce as a fold — `arr.reduce((acc, x) => acc + x.f, 0)`
    // and the Decimal variant `arr.reduce((acc, x) => acc.add(x.f || 0), new Decimal(0))`
    // desugar to the __sumBy fold symbol. A `|| 0` / `?? 0` projection guard is
    // recorded (4th arg) — bound derivation from CONDITIONAL element facts is
    // only sound for guarded folds (an unguarded nullish field is NaN poison).
    if (Node.isPropertyAccessExpression(calleeExpr) && calleeExpr.getName() === 'reduce'
        && node.getArguments().length === 2) {
      const [arrowArg, initArg] = node.getArguments()
      const arrRecv = parseExpr(calleeExpr.getExpression())
      if (arrRecv !== null && arrowArg !== undefined && Node.isArrowFunction(arrowArg)) {
        const rParams = arrowArg.getParameters()
        // Expression body, or a block whose single statement is `return <expr>`
        let rBody: Node | undefined = arrowArg.getBody()
        if (rBody !== undefined && Node.isBlock(rBody)) {
          const stmts = rBody.getStatements()
          rBody = stmts.length === 1 && Node.isReturnStatement(stmts[0]!)
            ? stmts[0]!.getExpression()
            : undefined
        }
        if (rParams.length >= 2 && rBody !== undefined && Node.isExpression(rBody)) {
          const accName = rParams[0]!.getName()
          const elemName = rParams[1]!.getName()
          const init = parseExpr(initArg as Expression)
          const zeroInit = init !== null && (
            (init.kind === 'literal' && init.value === 0) ||
            (init.kind === 'call' && init.callee === 'new Decimal' && init.args.length === 1
              && init.args[0]!.kind === 'literal' && (init.args[0] as { value: unknown }).value === 0))
          if (zeroInit) {
            const rParsed = parseExpr(rBody)
            let proj: Expr | null = null
            if (rParsed !== null) {
              if (rParsed.kind === 'binary' && rParsed.op === '+'
                  && rParsed.left.kind === 'ident' && rParsed.left.name === accName) {
                proj = rParsed.right
              } else if (rParsed.kind === 'call' && rParsed.args.length === 1
                  && rParsed.recv?.kind === 'ident' && rParsed.recv.name === accName
                  && (rParsed.callee === `${accName}.add` || rParsed.callee === `${accName}.plus`)) {
                proj = rParsed.args[0]!
              }
            }
            if (proj !== null) {
              let guarded = false
              if (proj.kind === 'binary' && (proj.op === '||' || proj.op === '??')
                  && proj.right.kind === 'literal' && proj.right.value === 0) {
                proj = proj.left
                guarded = true
              }
              if (proj.kind === 'member' && proj.object.kind === 'ident' && proj.object.name === elemName) {
                const display = node.getText().replace(/\s+/g, ' ')
                return {
                  kind: 'call', callee: '__sumBy',
                  args: [
                    arrRecv,
                    { kind: 'literal', value: proj.property },
                    { kind: 'literal', value: display },
                    { kind: 'literal', value: guarded ? 1 : 0 },
                  ],
                }
              }
            }
          }
        }
      }
    }

    // sortedBy(arr, (x) => x.field) — ∀ i: 0 ≤ i ∧ i+1 < len ⟹ proj(arr[i]) <= proj(arr[i+1])
    // (adjacent pairs: the form that composes well with the solver)
    if (callee === 'sortedBy' && node.getArguments().length === 2) {
      const argsSB = node.getArguments()
      const arrExpr = parseExpr(argsSB[0] as Expression)
      const arrow = argsSB[1]
      if (arrExpr !== null && Node.isArrowFunction(arrow)) {
        const arrowBody = arrow.getBody()
        const params = arrow.getParameters()
        if (Node.isExpression(arrowBody) && params.length >= 1) {
          const rawProj = parseExpr(arrowBody)
          if (rawProj !== null) {
            const qi = nextQuantifierIndexName()
            const projAt = (idx: Expr): Expr => substituteIdents(rawProj, new Map([[
              params[0]!.getName(),
              { kind: 'element-access', object: arrExpr, index: idx } as Expr,
            ]]))
            const len: Expr = { kind: 'member', object: arrExpr, property: 'length' }
            const iVar: Expr = { kind: 'ident', name: qi }
            const iNext: Expr = { kind: 'binary', op: '+', left: iVar, right: { kind: 'literal', value: 1 } }
            return {
              kind: 'quantifier', quantifier: 'forall', param: qi, sort: 'int',
              display: node.getText().replace(/\s+/g, ' '),
              body: {
                kind: 'binary', op: '==>',
                left: {
                  kind: 'binary', op: '&&',
                  left: { kind: 'binary', op: '>=', left: iVar, right: { kind: 'literal', value: 0 } },
                  right: { kind: 'binary', op: '<', left: iNext, right: len },
                },
                right: { kind: 'binary', op: '<=', left: projAt(iVar), right: projAt(iNext) },
              },
            }
          }
        }
      }
    }

    // uniqueBy(arr, (x) => x.field) — ∀ i j: in-range ∧ i ≠ j ⟹ proj(arr[i]) !== proj(arr[j])
    if (callee === 'uniqueBy' && node.getArguments().length === 2) {
      const args2 = node.getArguments()
      const arrExpr = parseExpr(args2[0] as Expression)
      const arrow = args2[1]
      if (arrExpr !== null && Node.isArrowFunction(arrow)) {
        const arrowBody = arrow.getBody()
        const params = arrow.getParameters()
        if (Node.isExpression(arrowBody) && params.length >= 1) {
          const rawProj = parseExpr(arrowBody)
          if (rawProj !== null) {
            const qi = nextQuantifierIndexName()
            const qj = nextQuantifierIndexName()
            const projAt = (name: string): Expr => substituteIdents(rawProj, new Map([[
              params[0]!.getName(),
              { kind: 'element-access', object: arrExpr, index: { kind: 'ident', name } } as Expr,
            ]]))
            const len: Expr = { kind: 'member', object: arrExpr, property: 'length' }
            const inRange = (name: string): Expr => ({
              kind: 'binary', op: '&&',
              left: { kind: 'binary', op: '>=', left: { kind: 'ident', name }, right: { kind: 'literal', value: 0 } },
              right: { kind: 'binary', op: '<', left: { kind: 'ident', name }, right: len },
            })
            return {
              kind: 'quantifier', quantifier: 'forall', param: qi, sort: 'int',
              display: node.getText().replace(/\s+/g, ' '),
              body: {
                kind: 'quantifier', quantifier: 'forall', param: qj, sort: 'int',
                body: {
                  kind: 'binary', op: '==>',
                  left: {
                    kind: 'binary', op: '&&',
                    left: { kind: 'binary', op: '&&', left: inRange(qi), right: inRange(qj) },
                    right: { kind: 'binary', op: '!==', left: { kind: 'ident', name: qi }, right: { kind: 'ident', name: qj } },
                  },
                  right: { kind: 'binary', op: '!==', left: projAt(qi), right: projAt(qj) },
                },
              },
            }
          }
        }
      }
    }

    // defined(x) — presence assertion (TS type guard in the runtime typing);
    // desugars to x !== null so the existing null machinery applies.
    if (callee === 'defined' && node.getArguments().length === 1) {
      const inner = parseExpr(node.getArguments()[0] as Expression)
      if (inner !== null) {
        return { kind: 'binary', op: '!==', left: inner, right: { kind: 'literal', value: null } }
      }
    }

    // Comparison vocabulary — gt/gte/lt/lte/eq/neq(a, b) desugar to plain
    // binary comparisons. The runtime typing accepts nullable and Decimal-like
    // values, so `gte(rate, 0)` covers number AND Decimal parameters without
    // the method-contract machinery.
    {
      const CMP_HELPERS: Record<string, BinaryOp> = {
        gt: '>', gte: '>=', lt: '<', lte: '<=', eq: '===', neq: '!==',
      }
      const cmpOp = CMP_HELPERS[callee]
      if (cmpOp !== undefined && node.getArguments().length === 2) {
        const a = parseExpr(node.getArguments()[0] as Expression)
        const b = parseExpr(node.getArguments()[1] as Expression)
        if (a !== null && b !== null) {
          return { kind: 'binary', op: cmpOp, left: a, right: b }
        }
      }
    }

    // sorted(arr) — ∀ i j: 0 ≤ i ≤ j < len ⟹ arr[i] <= arr[j]
    // unique(arr) — ∀ i j: in-range ∧ i ≠ j ⟹ arr[i] !== arr[j]
    if ((callee === 'sorted' || callee === 'unique') && node.getArguments().length === 1) {
      const arrExpr = parseExpr(node.getArguments()[0] as Expression)
      if (arrExpr !== null) {
        const qi = nextQuantifierIndexName()
        const qj = nextQuantifierIndexName()
        const len: Expr = { kind: 'member', object: arrExpr, property: 'length' }
        const at = (name: string): Expr => ({ kind: 'element-access', object: arrExpr, index: { kind: 'ident', name } })
        const ge0 = (name: string): Expr => ({ kind: 'binary', op: '>=', left: { kind: 'ident', name }, right: { kind: 'literal', value: 0 } })
        const ltLen = (name: string): Expr => ({ kind: 'binary', op: '<', left: { kind: 'ident', name }, right: len })
        const hyp: Expr = callee === 'sorted'
          ? { kind: 'binary', op: '&&',
              left: { kind: 'binary', op: '&&', left: ge0(qi), right: { kind: 'binary', op: '<=', left: { kind: 'ident', name: qi }, right: { kind: 'ident', name: qj } } },
              right: ltLen(qj) }
          : { kind: 'binary', op: '&&',
              left: { kind: 'binary', op: '&&', left: { kind: 'binary', op: '&&', left: ge0(qi), right: ltLen(qi) }, right: { kind: 'binary', op: '&&', left: ge0(qj), right: ltLen(qj) } },
              right: { kind: 'binary', op: '!==', left: { kind: 'ident', name: qi }, right: { kind: 'ident', name: qj } } }
        const concl: Expr = callee === 'sorted'
          ? { kind: 'binary', op: '<=', left: at(qi), right: at(qj) }
          : { kind: 'binary', op: '!==', left: at(qi), right: at(qj) }
        return {
          kind: 'quantifier', quantifier: 'forall', param: qi, sort: 'int',
          display: node.getText().replace(/\s+/g, ' '),
          body: {
            kind: 'quantifier', quantifier: 'forall', param: qj, sort: 'int',
            body: { kind: 'binary', op: '==>', left: hyp, right: concl },
          },
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
    // Method calls keep their receiver as a structured expression so the
    // translator can match `x.plus(y)` against a declared
    // `Type.prototype.plus` contract with x as the first contract argument.
    if (Node.isPropertyAccessExpression(calleeExpr)) {
      const recvParsed = parseExpr(calleeExpr.getExpression())
      if (recvParsed !== null) return { kind: 'call', callee, args, recv: recvParsed }
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
/**
 * True for schema-decode initializers that must stay FREE variables:
 *   <schema>.parse(x) / .safeParse(x)                     (Zod)
 *   Schema.decodeUnknownSync(S)(x) / decodeSync(S)(x)     (Effect Schema)
 */
function isSchemaParseCall(init: Node): boolean {
  if (!Node.isCallExpression(init)) return false
  const callee = init.getExpression()

  if (Node.isPropertyAccessExpression(callee)) {
    const name = callee.getName()
    return name === 'parse' || name === 'safeParse'
  }

  // Curried Effect decode: decodeUnknownSync(S)(input)
  if (Node.isCallExpression(callee)) {
    const text = callee.getExpression().getText()
    const last = text.includes('.') ? text.slice(text.lastIndexOf('.') + 1) : text
    return last === 'decodeUnknownSync' || last === 'decodeSync'
  }

  return false
}

function parseWithBindings(stmts: Statement[], bindings: Map<string, Expr>): Expr | null {
  if (stmts.length === 0) {
    // Void bodies (e.g. mutating methods) never hit a return statement —
    // save the final SSA state here so exit invariants see the mutations
    _finalSSABindings = new Map(bindings)
    return null
  }

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

      // Zod parse results stay FREE variables: `const x = Schema.parse(input)`
      // is opaque to Z3 (binding x to the call would make x.field untranslatable),
      // and the schema constraints on x.* are injected as assume contracts.
      if (init && isSchemaParseCall(init)) continue

      // Dedup idioms as TRUSTED contracts (like Array.prototype.sort):
      //   [...new Map(arr.map(x => [x.key, x])).values()]  → uniqueBy(v, key)
      //   [...new Set(arr)] / Array.from(new Set(arr))     → unique(v)
      // The variable stays FREE (content havoc'd) and the distinctness fact
      // plus `v.length <= arr.length` are granted as positional assumes —
      // the JS semantics of Map/Set collapsing duplicate keys, stated once.
      if (init) {
        const dedup = tryDedupIdiom(init as Expression)
        if (dedup !== null) {
          const varIdent: Expr = { kind: 'ident', name: varName }
          const srcExpr = newBindings.size > 0 ? substituteIdents(dedup.src, newBindings) : dedup.src
          const facts: Expr[] = [
            buildPairwiseDistinctFact(varIdent, dedup.field, `dedup(${varName})`),
            {
              kind: 'binary', op: '<=',
              left: { kind: 'member', object: varIdent, property: 'length' },
              right: { kind: 'member', object: srcExpr, property: 'length' },
            },
          ]
          for (const p of facts) {
            _resolvedPositionalContracts.push({ kind: 'assume', predicate: p })
          }
          continue  // variable deliberately left unbound (havoc)
        }
      }

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

      const isThisField = Node.isPropertyAccessExpression(left) &&
        left.getExpression().getKind() === SyntaxKind.ThisKeyword
      if ((Node.isIdentifier(left) || isThisField) && isAssignmentOp(op)) {
        const varName = left.getText()  // 'x' or 'this.x' — matches the normalized ident
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

  // ── for-of accumulation: `for (const x of arr) acc = acc.add(x.f ?? 0)` ──
  // Recognized loops become SSA fold bindings (acc := init + Σ). Anything
  // outside the shape keeps today's behavior (body unextracted).
  if (Node.isForOfStatement(first)) {
    const folds = tryFoldForOf(first, bindings)
    if (folds !== null) {
      for (const [name, boundExpr] of folds) bindings.set(name, boundExpr)
      return parseWithBindings(rest, bindings)
    }
    return null
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

// ── Dedup idiom recognition ─────────────────────────────────────────────────

/**
 * Recognizes JS dedup idioms whose RESULT is pairwise-distinct by
 * construction: `[...new Map(src.map(x => [x.key, x])).values()]` (distinct
 * by key) and `[...new Set(src)]` / `Array.from(new Set(src))` (distinct
 * elements). Returns the source array and the projected field (null = whole
 * element).
 */
export function tryDedupIdiom(init: Expression): { src: Expr; field: string | null } | null {
  let inner: Expression | undefined
  if (Node.isArrayLiteralExpression(init)) {
    const els = init.getElements()
    if (els.length === 1 && Node.isSpreadElement(els[0]!)) {
      inner = els[0]!.getExpression()
    }
  } else if (Node.isCallExpression(init) && init.getExpression().getText() === 'Array.from'
      && init.getArguments().length === 1) {
    inner = init.getArguments()[0] as Expression
  }
  if (inner === undefined) return null

  // new Set(src)
  if (Node.isNewExpression(inner) && inner.getExpression().getText() === 'Set'
      && (inner.getArguments() ?? []).length === 1) {
    const src = parseExpr(inner.getArguments()![0] as Expression)
    return src === null ? null : { src, field: null }
  }

  // new Map(src.map(x => [x.key, x])).values()
  if (Node.isCallExpression(inner)) {
    const ce = inner.getExpression()
    if (Node.isPropertyAccessExpression(ce) && ce.getName() === 'values') {
      const mapNew = ce.getExpression()
      if (Node.isNewExpression(mapNew) && mapNew.getExpression().getText() === 'Map'
          && (mapNew.getArguments() ?? []).length === 1) {
        const mapArg = mapNew.getArguments()![0]!
        if (Node.isCallExpression(mapArg)) {
          const mc = mapArg.getExpression()
          if (Node.isPropertyAccessExpression(mc) && mc.getName() === 'map' && mapArg.getArguments().length === 1) {
            const src = parseExpr(mc.getExpression())
            const arrow = mapArg.getArguments()[0]!
            if (src !== null && Node.isArrowFunction(arrow)) {
              const b = arrow.getBody()
              const p0 = arrow.getParameters()[0]?.getName()
              if (p0 !== undefined && Node.isArrayLiteralExpression(b) && b.getElements().length === 2) {
                const keyEl = parseExpr(b.getElements()[0] as Expression)
                if (keyEl !== null && keyEl.kind === 'member'
                    && keyEl.object.kind === 'ident' && keyEl.object.name === p0) {
                  return { src, field: keyEl.property }
                }
              }
            }
          }
        }
      }
    }
  }
  return null
}

/**
 * Builds the pairwise-distinct forall over `arr` — by a projected field
 * (uniqueBy shape) or over the elements themselves (unique shape).
 */
export function buildPairwiseDistinctFact(arrExpr: Expr, field: string | null, display: string): Expr {
  const qi = nextQuantifierIndexName()
  const qj = nextQuantifierIndexName()
  const len: Expr = { kind: 'member', object: arrExpr, property: 'length' }
  const at = (name: string): Expr => {
    const elem: Expr = { kind: 'element-access', object: arrExpr, index: { kind: 'ident', name } }
    return field === null ? elem : { kind: 'member', object: elem, property: field }
  }
  const inRange = (name: string): Expr => ({
    kind: 'binary', op: '&&',
    left: { kind: 'binary', op: '>=', left: { kind: 'ident', name }, right: { kind: 'literal', value: 0 } },
    right: { kind: 'binary', op: '<', left: { kind: 'ident', name }, right: len },
  })
  return {
    kind: 'quantifier', quantifier: 'forall', param: qi, sort: 'int',
    display,
    body: {
      kind: 'quantifier', quantifier: 'forall', param: qj, sort: 'int',
      body: {
        kind: 'binary', op: '==>',
        left: {
          kind: 'binary', op: '&&',
          left: { kind: 'binary', op: '&&', left: inRange(qi), right: inRange(qj) },
          right: { kind: 'binary', op: '!==', left: { kind: 'ident', name: qi }, right: { kind: 'ident', name: qj } },
        },
        right: { kind: 'binary', op: '!==', left: at(qi), right: at(qj) },
      },
    },
  }
}

// ── for-of fold recognition ─────────────────────────────────────────────────

/**
 * Recognizes `for (const x of arr) { [if (cond) continue;]* acc = acc + x.f; ... }`
 * and returns SSA bindings mapping each accumulator to `init + __sumBy(arr, f)`.
 *
 * The fold's 4th argument encodes the soundness mode for bound derivation:
 *   0 — exact terms (bare `x.f`, or `?? IDENT` fallback that a direct fact
 *       makes unreachable): unconditional facts apply unclamped.
 *   1 — zero-guarded (`x.f ?? 0` / `|| 0`): conditional facts apply, clamped.
 *   2 — subset (continue-guard) + zero-guarded: everything clamped.
 *   3 — subset, bare projection: unconditional facts only, clamped.
 *   4 — subset with unknown fallback: no bounds (only the empty-array axiom).
 */
function tryFoldForOf(stmt: Statement, bindings: Map<string, Expr>): Map<string, Expr> | null {
  if (!Node.isForOfStatement(stmt)) return null
  const init = stmt.getInitializer()
  if (!Node.isVariableDeclarationList(init)) return null
  const decls = init.getDeclarations()
  if (decls.length !== 1) return null
  const elemNode = decls[0]!.getNameNode()
  if (!Node.isIdentifier(elemNode)) return null
  const elemName = elemNode.getText()

  const arrRaw = parseExpr(stmt.getExpression())
  if (arrRaw === null) return null
  const arrExpr = bindings.size > 0 ? substituteIdents(arrRaw, bindings) : arrRaw

  const bodyNode = stmt.getStatement()
  const stmts: Statement[] = Node.isBlock(bodyNode) ? [...bodyNode.getStatements()] : [bodyNode as Statement]

  // Leading `if (cond) continue;` guards — the fold sums a SUBSET
  let hasContinue = false
  while (stmts.length > 0 && Node.isIfStatement(stmts[0]!)) {
    const ifs = stmts[0]!
    if (ifs.getElseStatement() !== undefined) return null
    const then = ifs.getThenStatement()
    const thenStmts = Node.isBlock(then) ? then.getStatements() : [then]
    if (thenStmts.length !== 1 || !Node.isContinueStatement(thenStmts[0]!)) return null
    hasContinue = true
    stmts.shift()
  }
  if (stmts.length === 0) return null

  const display = stmt.getText().replace(/\s+/g, ' ').slice(0, 80)
  const out = new Map<string, Expr>()

  for (const s of stmts) {
    if (!Node.isExpressionStatement(s)) return null
    const e = s.getExpression()
    if (!Node.isBinaryExpression(e)) return null
    const lhs = e.getLeft()
    if (!Node.isIdentifier(lhs)) return null
    const accName = lhs.getText()
    const opKind = e.getOperatorToken().getKind()

    let addend: Expr | null = null
    if (opKind === SyntaxKind.PlusEqualsToken) {
      addend = parseExpr(e.getRight())
    } else if (opKind === SyntaxKind.EqualsToken) {
      const rhs = parseExpr(e.getRight())
      if (rhs === null) return null
      if (rhs.kind === 'binary' && rhs.op === '+' && rhs.left.kind === 'ident' && rhs.left.name === accName) {
        addend = rhs.right
      } else if (rhs.kind === 'call' && rhs.args.length === 1
          && rhs.recv?.kind === 'ident' && rhs.recv.name === accName
          && (rhs.callee === `${accName}.add` || rhs.callee === `${accName}.plus`)) {
        addend = rhs.args[0]!
      } else {
        return null
      }
    } else {
      return null
    }
    if (addend === null) return null

    // Classify the projection and its fallback
    let proj = addend
    let zeroFallback = false
    let identFallback = false
    if (proj.kind === 'binary' && (proj.op === '??' || proj.op === '||')) {
      const fb = proj.right
      if (fb.kind === 'literal' && fb.value === 0) zeroFallback = true
      else if (fb.kind === 'call' && fb.callee === 'new Decimal' && fb.args.length === 1
          && fb.args[0]!.kind === 'literal' && (fb.args[0] as { value: unknown }).value === 0) zeroFallback = true
      else if (fb.kind === 'ident') identFallback = true
      else return null
      proj = proj.left
    }
    if (!(proj.kind === 'member' && proj.object.kind === 'ident' && proj.object.name === elemName)) return null

    const mode = identFallback
      ? (hasContinue ? 4 : 0)
      : zeroFallback
        ? (hasContinue ? 2 : 1)
        : (hasContinue ? 3 : 0)

    const fold: Expr = {
      kind: 'call', callee: '__sumBy',
      args: [
        arrExpr,
        { kind: 'literal', value: proj.property },
        { kind: 'literal', value: display },
        { kind: 'literal', value: mode },
      ],
    }
    const prev = out.get(accName) ?? bindings.get(accName) ?? { kind: 'ident' as const, name: accName }
    const isZeroInit = prev.kind === 'literal' && prev.value === 0
    out.set(accName, isZeroInit ? fold : { kind: 'binary', op: '+', left: prev, right: fold })
  }

  return out
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
    const isThisField = Node.isPropertyAccessExpression(left) &&
      left.getExpression().getKind() === SyntaxKind.ThisKeyword
    if (!Node.isIdentifier(left) && !isThisField) return null

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
  '|': '|', '&': '&', '^': '^', '<<': '<<', '>>': '>>', '>>>': '>>>',
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

// ---------------------------------------------------------------------------
// Quantifier support: fresh bound-index names + ident substitution
// ---------------------------------------------------------------------------

let _quantifierIndexCounter = 0

function nextQuantifierIndexName(): string {
  return `__qi${_quantifierIndexCounter++}`
}

/** Replaces free identifiers by expressions (used to bind lambda params). */
function substituteIdents(expr: Expr, bindings: Map<string, Expr>): Expr {
  switch (expr.kind) {
    case 'ident': {
      const replacement = bindings.get(expr.name)
      return replacement !== undefined ? replacement : expr
    }
    case 'binary':
      return { ...expr, left: substituteIdents(expr.left, bindings), right: substituteIdents(expr.right, bindings) }
    case 'unary':
      return { ...expr, operand: substituteIdents(expr.operand, bindings) }
    case 'ternary':
      return { ...expr, condition: substituteIdents(expr.condition, bindings), then: substituteIdents(expr.then, bindings), else: substituteIdents(expr.else, bindings) }
    case 'call':
      return {
        ...expr,
        args: expr.args.map(a => substituteIdents(a, bindings)),
        ...(expr.recv !== undefined ? { recv: substituteIdents(expr.recv, bindings) } : {}),
      }
    case 'member':
      return { ...expr, object: substituteIdents(expr.object, bindings) }
    case 'element-access':
      return { ...expr, object: substituteIdents(expr.object, bindings), index: substituteIdents(expr.index, bindings) }
    case 'quantifier': {
      const inner = new Map(bindings)
      inner.delete(expr.param)
      return { ...expr, body: substituteIdents(expr.body, inner) }
    }
    case 'array':
      return { ...expr, elements: expr.elements.map(e => substituteIdents(e, bindings)) }
    case 'spread':
      return { ...expr, operand: substituteIdents(expr.operand, bindings) }
    default:
      return expr
  }
}
