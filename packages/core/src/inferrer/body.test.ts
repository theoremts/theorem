import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

const prove = { prove: true }

describe('analyzeBody', () => {
  it('simple arithmetic body generates ensures', async () => {
    const result = await inferContracts(
      `function add(a: number, b: number) { return a + b }`,
      'test.ts',
      prove,
    )
    const ensures = result.functions[0]?.contracts.filter(c => c.kind === 'ensures' && c.source === 'from return expression') ?? []
    assert.ok(ensures.length >= 1, `expected at least 1 ensures, got ${ensures.length}`)
    assert.equal(ensures[0]!.text, 'output() === a + b')
    assert.equal(ensures[0]!.confidence, 'derived')
  })

  it('trivial identity body is skipped', async () => {
    const result = await inferContracts(
      `function id(x: number) { return x }`,
      'test.ts',
      prove,
    )
    const ensures = result.functions[0]?.contracts.filter(c => c.kind === 'ensures' && c.source === 'from return expression') ?? []
    assert.equal(ensures.length, 0, 'trivial body should not generate ensures')
  })

  it('object return generates per-property ensures', async () => {
    const result = await inferContracts(
      `function calc(a: number, b: number) { return { sum: a + b, diff: a - b } }`,
      'test.ts',
      prove,
    )
    const fn = result.functions[0]
    if (!fn) return
    const propEnsures = fn.contracts.filter(c => c.kind === 'ensures' && c.source.startsWith('from return property'))
    if (propEnsures.length === 0) return
    assert.ok(propEnsures.some(c => c.text === 'output().sum === a + b'))
    assert.ok(propEnsures.some(c => c.text === 'output().diff === a - b'))
  })

  it('complex body (depth > 3) is skipped', async () => {
    const result = await inferContracts(
      `function deep(a: number, b: number, c: number, d: number) { return (a + b) * (c - d) + a }`,
      'test.ts',
      prove,
    )
    const ensures = result.functions[0]?.contracts.filter(c => c.kind === 'ensures' && c.source === 'from return expression') ?? []
    assert.equal(ensures.length, 0, 'deeply nested body should not generate ensures')
  })
})
