import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('extractNullSafety', () => {
  it('nullable param WITH guard does not add duplicate requires', async () => {
    const result = await inferContracts(
      `function f(x: number | null) { if (x === null) throw new Error(); return x * 2 }`,
      'test.ts',
    )
    // Guard extraction already produces requires(x !== null)
    const guards = result.functions[0]?.contracts.filter(c => c.confidence === 'guard') ?? []
    assert.ok(guards.length >= 1, 'should have guard-based requires')
    // Null-safety should NOT add another requires
    const nullSafety = result.functions[0]?.contracts.filter(c => c.source === 'nullable parameter accessed without guard') ?? []
    assert.equal(nullSafety.length, 0, 'should not add duplicate null-safety requires when guard exists')
  })

  it('nullable param WITHOUT guard, accessing property', async () => {
    const result = await inferContracts(
      `function f(x: { value: number } | null) { return x.value * 2 }`,
      'test.ts',
    )
    const nullSafety = result.functions[0]?.contracts.filter(c => c.source === 'nullable parameter accessed without guard') ?? []
    assert.ok(nullSafety.length >= 1, `expected null-safety requires, got ${nullSafety.length}`)
    assert.equal(nullSafety[0]!.kind, 'requires')
    assert.equal(nullSafety[0]!.text, 'x !== null')
    assert.equal(nullSafety[0]!.confidence, 'heuristic')
  })

  it('optional chaining is safe, no requires', async () => {
    const result = await inferContracts(
      `function f(x: { value: number } | null) { return x?.value ?? 0 }`,
      'test.ts',
    )
    const nullSafety = result.functions[0]?.contracts.filter(c => c.source === 'nullable parameter accessed without guard') ?? []
    assert.equal(nullSafety.length, 0, 'should not add requires when optional chaining is used')
  })

  it('non-nullable param, no requires', async () => {
    const result = await inferContracts(
      `function f(x: number) { return x * 2 }`,
      'test.ts',
    )
    const nullSafety = result.functions[0]?.contracts.filter(c => c.source === 'nullable parameter accessed without guard') ?? []
    assert.equal(nullSafety.length, 0, 'should not add requires for non-nullable param')
  })

  it('optional param with nullish coalescing, no requires', async () => {
    const result = await inferContracts(
      `function f(x?: number) { return x ?? 0 }`,
      'test.ts',
    )
    const nullSafety = result.functions[0]?.contracts.filter(c => c.source === 'nullable parameter accessed without guard') ?? []
    assert.equal(nullSafety.length, 0, 'should not add requires when ?? handles the optional param')
  })
})
