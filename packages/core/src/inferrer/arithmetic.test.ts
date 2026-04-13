import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('extractArithmeticSafety', () => {
  it('division by parameter', async () => {
    const result = await inferContracts(
      `function f(a: number, b: number) { return a / b }`,
      'test.ts',
    )
    const derived = result.functions[0]?.contracts.filter(c => c.confidence === 'derived') ?? []
    assert.ok(derived.length >= 1, `expected at least 1 derived, got ${derived.length}`)
    assert.ok(derived.some(c => c.text === 'b !== 0'), `expected 'b !== 0', got: ${derived.map(c => c.text)}`)
  })

  it('division by non-zero literal is safe', async () => {
    const result = await inferContracts(
      `function f(a: number) { return a / 2 }`,
      'test.ts',
    )
    const derived = (result.functions[0]?.contracts ?? []).filter(c => c.confidence === 'derived' && c.text.includes('!== 0'))
    assert.equal(derived.length, 0, `expected no division safety, got: ${derived.map(c => c.text)}`)
  })

  it('modulo by parameter', async () => {
    const result = await inferContracts(
      `function f(a: number, b: number) { return a % b }`,
      'test.ts',
    )
    const derived = result.functions[0]?.contracts.filter(c => c.confidence === 'derived') ?? []
    assert.ok(derived.some(c => c.text === 'b !== 0'), `expected 'b !== 0', got: ${derived.map(c => c.text)}`)
  })

  it('nested division with complex denominator', async () => {
    const result = await inferContracts(
      `function f(a: number, b: number, c: number) { return (a * b) / (c - a) }`,
      'test.ts',
    )
    const derived = result.functions[0]?.contracts.filter(c => c.confidence === 'derived') ?? []
    assert.ok(
      derived.some(c => c.text === 'c - a !== 0'),
      `expected 'c - a !== 0', got: ${derived.map(c => c.text)}`,
    )
  })

  it('Math.sqrt requires non-negative', async () => {
    const result = await inferContracts(
      `function f(x: number) { return Math.sqrt(x) }`,
      'test.ts',
    )
    const derived = result.functions[0]?.contracts.filter(c => c.confidence === 'derived') ?? []
    assert.ok(derived.some(c => c.text === 'x >= 0'), `expected 'x >= 0', got: ${derived.map(c => c.text)}`)
  })

  it('Math.log requires positive', async () => {
    const result = await inferContracts(
      `function f(x: number) { return Math.log(x) }`,
      'test.ts',
    )
    const derived = result.functions[0]?.contracts.filter(c => c.confidence === 'derived') ?? []
    assert.ok(derived.some(c => c.text === 'x > 0'), `expected 'x > 0', got: ${derived.map(c => c.text)}`)
  })

  it('no arithmetic risks for addition', async () => {
    const result = await inferContracts(
      `function f(a: number, b: number) { return a + b }`,
      'test.ts',
    )
    const arithSafety = (result.functions[0]?.contracts ?? []).filter(
      c => c.confidence === 'derived' && c.kind === 'requires' &&
        (c.text.includes('!== 0') || c.text.includes('>= 0') || c.text.includes('> 0')),
    )
    assert.equal(arithSafety.length, 0, `expected no arithmetic safety contracts, got: ${arithSafety.map(c => c.text)}`)
  })
})
