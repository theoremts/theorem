import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { negateExpr, splitDisjunction } from './negate.js'
import type { Expr } from '../parser/ir.js'

function ident(name: string): Expr { return { kind: 'ident', name } }
function binary(op: string, left: Expr, right: Expr): Expr { return { kind: 'binary', op: op as any, left, right } }
function unary(op: string, operand: Expr): Expr { return { kind: 'unary', op: op as any, operand } }
function lit(value: number | boolean | null | string): Expr { return { kind: 'literal', value } }

describe('negateExpr', () => {
  const x = ident('x')
  const zero = lit(0)

  it('flips < to >=', () => {
    assert.deepStrictEqual(negateExpr(binary('<', x, zero)), binary('>=', x, zero))
  })

  it('flips <= to >', () => {
    assert.deepStrictEqual(negateExpr(binary('<=', x, zero)), binary('>', x, zero))
  })

  it('flips > to <=', () => {
    assert.deepStrictEqual(negateExpr(binary('>', x, zero)), binary('<=', x, zero))
  })

  it('flips >= to <', () => {
    assert.deepStrictEqual(negateExpr(binary('>=', x, zero)), binary('<', x, zero))
  })

  it('flips === to !==', () => {
    assert.deepStrictEqual(negateExpr(binary('===', x, zero)), binary('!==', x, zero))
  })

  it('flips !== to ===', () => {
    assert.deepStrictEqual(negateExpr(binary('!==', x, zero)), binary('===', x, zero))
  })

  it('unwraps logical NOT', () => {
    assert.deepStrictEqual(negateExpr(unary('!', x)), x)
  })

  it('applies De Morgan to &&', () => {
    const a = ident('a')
    const b = ident('b')
    assert.deepStrictEqual(
      negateExpr(binary('&&', a, b)),
      binary('||', unary('!', a), unary('!', b)),
    )
  })

  it('applies De Morgan to ||', () => {
    const a = ident('a')
    const b = ident('b')
    assert.deepStrictEqual(
      negateExpr(binary('||', a, b)),
      binary('&&', unary('!', a), unary('!', b)),
    )
  })

  it('negates true to false', () => {
    assert.deepStrictEqual(negateExpr(lit(true)), lit(false))
  })

  it('negates false to true', () => {
    assert.deepStrictEqual(negateExpr(lit(false)), lit(true))
  })

  it('wraps identifier in NOT as fallback', () => {
    assert.deepStrictEqual(negateExpr(x), unary('!', x))
  })

  it('double negation via negateExpr on !x yields x', () => {
    const notX = unary('!', x)
    // negateExpr(!x) should unwrap to x, then negateExpr(x) wraps back — but
    // the spec says negateExpr on !x → x (unwrap). So double negation:
    // negateExpr(negateExpr(x)) = negateExpr(!x) = x
    assert.deepStrictEqual(negateExpr(negateExpr(x)), x)
  })
})

describe('splitDisjunction', () => {
  const a = ident('a')
  const b = ident('b')
  const c = ident('c')

  it('splits a || b into [a, b]', () => {
    assert.deepStrictEqual(splitDisjunction(binary('||', a, b)), [a, b])
  })

  it('splits a || b || c into [a, b, c]', () => {
    // a || b || c is parsed as (a || b) || c
    const expr = binary('||', binary('||', a, b), c)
    assert.deepStrictEqual(splitDisjunction(expr), [a, b, c])
  })

  it('does not split a && b', () => {
    const expr = binary('&&', a, b)
    assert.deepStrictEqual(splitDisjunction(expr), [expr])
  })

  it('returns [a] for a plain identifier', () => {
    assert.deepStrictEqual(splitDisjunction(a), [a])
  })
})
