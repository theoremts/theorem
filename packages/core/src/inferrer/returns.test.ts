import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { analyzeReturns } from './returns.js'
import { extractFunctionsFromSource } from '../parser/extractor.js'
import { getContext } from '../solver/context.js'

describe('analyzeReturns', () => {
  it('Math.abs generates ensures output() >= 0', async () => {
    const irs = extractFunctionsFromSource(
      `function f(x: number) { return Math.abs(x) }`,
      'test.ts',
    )
    const ctx = await getContext()
    const ir = irs[0]!
    const results = await analyzeReturns(ir, ctx, [])
    const geZero = results.filter(c =>
      c.kind === 'ensures' && c.text === 'output() >= 0'
    )
    assert.ok(geZero.length >= 1, `expected ensures output() >= 0, got: ${results.map(c => c.text).join(', ')}`)
    assert.equal(geZero[0]!.confidence, 'proven')
  })

  it('Math.max generates ensures output() >= each arg', async () => {
    const irs = extractFunctionsFromSource(
      `function f(a: number, b: number) { return Math.max(a, b) }`,
      'test.ts',
    )
    const ctx = await getContext()
    const ir = irs[0]!
    const results = await analyzeReturns(ir, ctx, [])
    const geA = results.filter(c => c.kind === 'ensures' && c.text === 'output() >= a')
    const geB = results.filter(c => c.kind === 'ensures' && c.text === 'output() >= b')
    assert.ok(geA.length >= 1, `expected ensures output() >= a, got: ${results.map(c => c.text).join(', ')}`)
    assert.ok(geB.length >= 1, `expected ensures output() >= b, got: ${results.map(c => c.text).join(', ')}`)
    assert.equal(geA[0]!.confidence, 'proven')
    assert.equal(geB[0]!.confidence, 'proven')
  })

  it('Math.min generates ensures output() <= each arg', async () => {
    const irs = extractFunctionsFromSource(
      `function f(a: number, b: number) { return Math.min(a, b) }`,
      'test.ts',
    )
    const ctx = await getContext()
    const ir = irs[0]!
    const results = await analyzeReturns(ir, ctx, [])
    const leA = results.filter(c => c.kind === 'ensures' && c.text === 'output() <= a')
    const leB = results.filter(c => c.kind === 'ensures' && c.text === 'output() <= b')
    assert.ok(leA.length >= 1, `expected ensures output() <= a, got: ${results.map(c => c.text).join(', ')}`)
    assert.ok(leB.length >= 1, `expected ensures output() <= b, got: ${results.map(c => c.text).join(', ')}`)
    assert.equal(leA[0]!.confidence, 'proven')
    assert.equal(leB[0]!.confidence, 'proven')
  })

  it('x * x generates ensures output() >= 0', async () => {
    const irs = extractFunctionsFromSource(
      `function f(x: number) { return x * x }`,
      'test.ts',
    )
    const ctx = await getContext()
    const ir = irs[0]!
    const results = await analyzeReturns(ir, ctx, [])
    const geZero = results.filter(c =>
      c.kind === 'ensures' && c.text === 'output() >= 0'
    )
    assert.ok(geZero.length >= 1, `expected ensures output() >= 0, got: ${results.map(c => c.text).join(', ')}`)
  })

  it('no special ensures for plain addition', async () => {
    const irs = extractFunctionsFromSource(
      `function f(a: number, b: number) { return a + b }`,
      'test.ts',
    )
    const ctx = await getContext()
    const ir = irs[0]!
    const results = await analyzeReturns(ir, ctx, [])
    assert.equal(results.length, 0, `expected no results from returns analysis for a + b, got: ${results.map(c => c.text).join(', ')}`)
  })
})
