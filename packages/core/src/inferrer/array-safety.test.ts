import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('extractArraySafety', () => {
  it('reduce without initial value requires non-empty array', async () => {
    const result = await inferContracts(
      `function f(arr: number[]) { return arr.reduce((a, b) => a + b) }`,
      'test.ts',
    )
    const heuristics = result.functions[0]?.contracts.filter(c => c.confidence === 'heuristic') ?? []
    assert.ok(
      heuristics.some(c => c.text === 'arr.length > 0'),
      `expected 'arr.length > 0', got: ${heuristics.map(c => c.text)}`,
    )
  })

  it('reduce with initial value is safe', async () => {
    const result = await inferContracts(
      `function f(arr: number[]) { return arr.reduce((a, b) => a + b, 0) }`,
      'test.ts',
    )
    const heuristics = (result.functions[0]?.contracts ?? []).filter(
      c => c.confidence === 'heuristic' && c.text.includes('arr.length'),
    )
    assert.equal(heuristics.length, 0, `expected no array length requirement, got: ${heuristics.map(c => c.text)}`)
  })

  it('array index with variable requires non-negative', async () => {
    const result = await inferContracts(
      `function f(arr: number[], i: number) { return arr[i] }`,
      'test.ts',
    )
    const heuristics = result.functions[0]?.contracts.filter(c => c.confidence === 'heuristic') ?? []
    assert.ok(
      heuristics.some(c => c.text === 'i >= 0'),
      `expected 'i >= 0', got: ${heuristics.map(c => c.text)}`,
    )
  })

  it('array index with literal is safe', async () => {
    const result = await inferContracts(
      `function f(arr: number[]) { return arr[0] }`,
      'test.ts',
    )
    const heuristics = (result.functions[0]?.contracts ?? []).filter(
      c => c.confidence === 'heuristic' && c.text.includes('>= 0'),
    )
    assert.equal(heuristics.length, 0, `expected no index safety, got: ${heuristics.map(c => c.text)}`)
  })

  it('no array operations produces no contracts', async () => {
    const result = await inferContracts(
      `function f(x: number) { return x + 1 }`,
      'test.ts',
    )
    const heuristics = (result.functions[0]?.contracts ?? []).filter(c => c.confidence === 'heuristic')
    assert.equal(heuristics.length, 0, `expected no heuristic contracts, got: ${heuristics.map(c => c.text)}`)
  })
})
