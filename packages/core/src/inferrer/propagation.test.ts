import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('propagation', () => {
  it('propagates requires from callee to caller', async () => {
    const source = `
      function divide(a: number, b: number) {
        if (b === 0) throw new Error('division by zero')
        return a / b
      }
      function compute(x: number, y: number) {
        return divide(x, y) + 1
      }
    `
    const result = await inferContracts(source)

    const divide = result.functions.find(f => f.name === 'divide')
    assert.ok(divide, 'should find divide function')
    const divideReq = divide.contracts.find(c => c.kind === 'requires' && c.text.includes('b') && c.text.includes('0'))
    assert.ok(divideReq, 'divide should have requires about b !== 0')

    const compute = result.functions.find(f => f.name === 'compute')
    assert.ok(compute, 'should find compute function')
    const propagated = compute.contracts.find(
      c => c.kind === 'requires' && c.confidence === 'propagated'
    )
    assert.ok(propagated, 'compute should have a propagated requires contract')
    assert.ok(propagated.text.includes('y'), 'propagated contract should reference y (substituted from b)')
    assert.ok(propagated.source.includes('divide'), 'propagated contract source should mention divide')
  })

  it('does not propagate between unrelated functions', async () => {
    const source = `
      function foo(a: number) {
        if (a < 0) throw new Error('negative')
        return a
      }
      function bar(b: number) {
        return b * 2
      }
    `
    const result = await inferContracts(source)

    const bar = result.functions.find(f => f.name === 'bar')
    // bar should have no propagated contracts
    const propagated = bar?.contracts.filter(c => c.confidence === 'propagated') ?? []
    assert.equal(propagated.length, 0, 'bar should not have propagated contracts')
  })

  it('handles self-recursion without hanging', async () => {
    const source = `
      function f(n: number) {
        if (n <= 0) return 0
        return f(n - 1)
      }
    `
    const result = await inferContracts(source)
    // Should complete without hanging; just verify it returns
    assert.ok(result, 'should complete without infinite loop')
  })
})
