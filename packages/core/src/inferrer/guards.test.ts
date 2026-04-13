import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('extractGuards', () => {
  it('simple if/throw', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (x <= 0) throw new Error('bad'); return x * 2 }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1, 'should have at least one guard')
    assert.equal(guards[0]!.kind, 'requires')
    assert.equal(guards[0]!.text, 'x > 0')
  })

  it('if/return (not a throw) is NOT treated as a requires guard', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (x < 0) return -1; return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    // Early returns handle the case gracefully — they are not preconditions
    assert.equal(guards.length, 0, 'if/return should not produce guard requires')
  })

  it('multiple guards', async () => {
    const result = await inferContracts(
      `function f(a: number, b: number) { if (a < 0) throw new Error(); if (b === 0) throw new Error(); return a / b }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 2, `expected >= 2 guards, got ${guards.length}`)
    assert.equal(guards[0]!.text, 'a >= 0')
    assert.equal(guards[1]!.text, 'b !== 0')
  })

  it('OR guard splits into multiple requires', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (x < 0 || x > 100) throw new Error(); return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 2, `expected >= 2 guards, got ${guards.length}`)
    assert.equal(guards[0]!.text, 'x >= 0')
    assert.equal(guards[1]!.text, 'x <= 100')
  })

  it('null check', async () => {
    const result = await inferContracts(
      `function f(x: number | null) { if (x === null) throw new Error(); return x * 2 }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1)
    assert.equal(guards[0]!.text, 'x !== null')
  })

  it('NOT guard', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (!x) throw new Error(); return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1)
    // negateExpr of unary ! unwraps: !x → x
    assert.equal(guards[0]!.text, 'x')
  })

  it('stops at variable declaration with initializer', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (x < 0) throw new Error(); const y = x + 1; if (y > 100) throw new Error(); return y }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    // Only the first guard should be collected; second is after assignment
    const guardTexts = guards.map(g => g.text)
    assert.ok(guardTexts.includes('x >= 0'), `should have x >= 0, got: ${guardTexts}`)
    assert.ok(!guardTexts.includes('y <= 100'), 'should NOT have y <= 100')
  })

  it('if with else is not a guard (stops)', async () => {
    const result = await inferContracts(
      `function f(x: number) { if (x < 0) { throw new Error() } else { console.log('ok') } return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.equal(guards.length, 0, 'should have no guards when if has else')
  })

  it('assert() call', async () => {
    const result = await inferContracts(
      `function f(x: number) { assert(x > 0); return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1, `expected at least 1 guard, got ${guards.length}`)
    assert.equal(guards[0]!.text, 'x > 0')
  })

  it('empty function — no guards', async () => {
    const result = await inferContracts(
      `function f(x: number) { return x }`,
      'test.ts',
    )
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.equal(guards.length, 0)
  })

  it('arrow function guard', async () => {
    const result = await inferContracts(
      `const f = (x: number) => { if (x < 0) throw new Error(); return x }`,
      'test.ts',
    )
    const fn = result.functions.find(f => f.name === 'f')
    const guards = fn?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1, `expected at least 1 guard, got ${guards.length}`)
    assert.equal(guards[0]!.text, 'x >= 0')
  })
})
