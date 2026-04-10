import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { prettyExpr } from './pretty.js'
import type { Expr } from './ir.js'

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

describe('literal', () => {
  test('numeric literal', () => {
    const expr: Expr = { kind: 'literal', value: 42 }
    assert.strictEqual(prettyExpr(expr), '42')
  })

  test('negative numeric literal', () => {
    const expr: Expr = { kind: 'literal', value: -3 }
    assert.strictEqual(prettyExpr(expr), '-3')
  })

  test('zero literal', () => {
    const expr: Expr = { kind: 'literal', value: 0 }
    assert.strictEqual(prettyExpr(expr), '0')
  })

  test('boolean literal true', () => {
    const expr: Expr = { kind: 'literal', value: true }
    assert.strictEqual(prettyExpr(expr), 'true')
  })

  test('boolean literal false', () => {
    const expr: Expr = { kind: 'literal', value: false }
    assert.strictEqual(prettyExpr(expr), 'false')
  })
})

// ---------------------------------------------------------------------------
// Ident
// ---------------------------------------------------------------------------

describe('ident', () => {
  test('simple identifier', () => {
    const expr: Expr = { kind: 'ident', name: 'price' }
    assert.strictEqual(prettyExpr(expr), 'price')
  })

  test('result identifier', () => {
    const expr: Expr = { kind: 'ident', name: 'result' }
    assert.strictEqual(prettyExpr(expr), 'result')
  })
})

// ---------------------------------------------------------------------------
// Member access
// ---------------------------------------------------------------------------

describe('member access', () => {
  test('object.property', () => {
    const expr: Expr = {
      kind: 'member',
      object: { kind: 'ident', name: 'from' },
      property: 'balance',
    }
    assert.strictEqual(prettyExpr(expr), 'from.balance')
  })

  test('nested member access', () => {
    const expr: Expr = {
      kind: 'member',
      object: {
        kind: 'member',
        object: { kind: 'ident', name: 'a' },
        property: 'b',
      },
      property: 'c',
    }
    assert.strictEqual(prettyExpr(expr), 'a.b.c')
  })
})

// ---------------------------------------------------------------------------
// Unary !
// ---------------------------------------------------------------------------

describe('unary !', () => {
  test('negates an identifier', () => {
    const expr: Expr = {
      kind: 'unary',
      op: '!',
      operand: { kind: 'ident', name: 'flag' },
    }
    assert.strictEqual(prettyExpr(expr), '!flag')
  })

  test('negates a boolean literal', () => {
    const expr: Expr = {
      kind: 'unary',
      op: '!',
      operand: { kind: 'literal', value: true },
    }
    assert.strictEqual(prettyExpr(expr), '!true')
  })
})

// ---------------------------------------------------------------------------
// Binary ops
// ---------------------------------------------------------------------------

describe('binary +', () => {
  test('a + b', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '+',
      left: { kind: 'ident', name: 'a' },
      right: { kind: 'ident', name: 'b' },
    }
    assert.strictEqual(prettyExpr(expr), 'a + b')
  })
})

describe('binary -', () => {
  test('price - discount', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '-',
      left: { kind: 'ident', name: 'price' },
      right: { kind: 'ident', name: 'discount' },
    }
    assert.strictEqual(prettyExpr(expr), 'price - discount')
  })
})

describe('binary <=', () => {
  test('x <= 100', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '<=',
      left: { kind: 'ident', name: 'x' },
      right: { kind: 'literal', value: 100 },
    }
    assert.strictEqual(prettyExpr(expr), 'x <= 100')
  })
})

describe('binary ===', () => {
  test('a === b', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '===',
      left: { kind: 'ident', name: 'a' },
      right: { kind: 'ident', name: 'b' },
    }
    assert.strictEqual(prettyExpr(expr), 'a === b')
  })
})

describe('binary &&', () => {
  test('a && b', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '&&',
      left: { kind: 'ident', name: 'a' },
      right: { kind: 'ident', name: 'b' },
    }
    assert.strictEqual(prettyExpr(expr), 'a && b')
  })
})

describe('binary ||', () => {
  test('a || b', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '||',
      left: { kind: 'ident', name: 'a' },
      right: { kind: 'ident', name: 'b' },
    }
    assert.strictEqual(prettyExpr(expr), 'a || b')
  })
})

// ---------------------------------------------------------------------------
// Call expressions
// ---------------------------------------------------------------------------

describe('call expressions', () => {
  test('positive(x)', () => {
    const expr: Expr = {
      kind: 'call',
      callee: 'positive',
      args: [{ kind: 'ident', name: 'x' }],
    }
    assert.strictEqual(prettyExpr(expr), 'positive(x)')
  })

  test('between(x, 0, 100)', () => {
    const expr: Expr = {
      kind: 'call',
      callee: 'between',
      args: [
        { kind: 'ident', name: 'x' },
        { kind: 'literal', value: 0 },
        { kind: 'literal', value: 100 },
      ],
    }
    assert.strictEqual(prettyExpr(expr), 'between(x, 0, 100)')
  })

  test('call with no args', () => {
    const expr: Expr = {
      kind: 'call',
      callee: 'check',
      args: [],
    }
    assert.strictEqual(prettyExpr(expr), 'check()')
  })
})

// ---------------------------------------------------------------------------
// Precedence — lower-precedence sub-expressions get parentheses
// ---------------------------------------------------------------------------

describe('precedence parenthesisation', () => {
  test('(a + b) * c — addition inside multiplication gets parens', () => {
    // * has higher precedence than +, so left sub-expr (a + b) needs parens
    const expr: Expr = {
      kind: 'binary',
      op: '*',
      left: {
        kind: 'binary',
        op: '+',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'c' },
    }
    assert.strictEqual(prettyExpr(expr), '(a + b) * c')
  })

  test('a * b + c — multiplication inside addition does NOT get parens', () => {
    // + has lower precedence than *, so left sub-expr (a * b) does not need parens
    const expr: Expr = {
      kind: 'binary',
      op: '+',
      left: {
        kind: 'binary',
        op: '*',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'c' },
    }
    assert.strictEqual(prettyExpr(expr), 'a * b + c')
  })

  test('(a || b) && c — || inside && gets parens', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '&&',
      left: {
        kind: 'binary',
        op: '||',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'c' },
    }
    assert.strictEqual(prettyExpr(expr), '(a || b) && c')
  })

  test('a && b || c — && inside || does NOT get parens', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '||',
      left: {
        kind: 'binary',
        op: '&&',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'c' },
    }
    assert.strictEqual(prettyExpr(expr), 'a && b || c')
  })

  test('(a + b) <= limit — addition inside comparison gets parens', () => {
    const expr: Expr = {
      kind: 'binary',
      op: '<=',
      left: {
        kind: 'binary',
        op: '+',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'limit' },
    }
    // + has higher precedence than <=, so no parens needed
    assert.strictEqual(prettyExpr(expr), 'a + b <= limit')
  })

  test('(a === b) && c — === inside && gets parens when === < &&', () => {
    // === has precedence 3, && has precedence 2 → === > && so no parens
    const expr: Expr = {
      kind: 'binary',
      op: '&&',
      left: {
        kind: 'binary',
        op: '===',
        left: { kind: 'ident', name: 'a' },
        right: { kind: 'ident', name: 'b' },
      },
      right: { kind: 'ident', name: 'c' },
    }
    // === (prec 3) > && (prec 2) → no parens needed
    assert.strictEqual(prettyExpr(expr), 'a === b && c')
  })
})
