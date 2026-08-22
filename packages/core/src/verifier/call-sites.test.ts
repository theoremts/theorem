import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from '../parser/index.js'
import { buildRegistry } from '../registry/index.js'
import { extractCallSiteObligations } from './call-sites.js'
import { getContext, check } from '../solver/index.js'

async function checkCallSites(source: string) {
  const ctx = await getContext()
  const registry = buildRegistry(extractFromSource(source))
  const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
  const results = []
  for (const task of tasks) {
    const result = await check(task)
    results.push({
      text: task.contractText,
      status: result.status,
      labels: task.assumptionLabels,
    })
  }
  return results
}

const safeAddSource = `
  function safeAdd(a: number, b: number): number {
    requires(nonNegative(a))
    requires(nonNegative(b))
    ensures(output() >= a)
    ensures(output() >= b)
    return a + b
  }

  var a = safeAdd(1, 2)
  safeAdd(1, a)
`

describe('call-site: ensures propagation through variable assignment', () => {
  test('safeAdd(1, a) proves nonNegative(a) via safeAdd(1, 2) ensures', async () => {
    const results = await checkCallSites(safeAddSource)
    const target = results.find(r => r.text.includes('safeAdd(1, a)') && r.text.includes('nonNegative(b)'))
    assert.ok(target, `Expected an obligation for safeAdd(1, a): nonNegative(b), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      `Expected proved via instantiated ensures, got ${target.status} (assumptions: ${target.labels.join(', ')})`)
  })

  test('instantiated ensures appear as assumption labels', async () => {
    const results = await checkCallSites(safeAddSource)
    const target = results.find(r => r.text.includes('safeAdd(1, a)'))
    assert.ok(target)
    assert.ok(target.labels.some(l => l.startsWith('ensures(safeAdd)')),
      `Expected an ensures(safeAdd) assumption, got: ${target.labels.join(', ')}`)
  })

  test('a genuinely bad argument still fails', async () => {
    const source = `
      function safeAdd(a: number, b: number): number {
        requires(nonNegative(a))
        requires(nonNegative(b))
        ensures(output() >= a)
        return a + b
      }

      var x = safeAdd(1, 2)
      safeAdd(1, x - 10)
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('safeAdd(1, x - 10)') && r.text.includes('nonNegative(b)'))
    assert.ok(target, `Expected an obligation for safeAdd(1, x - 10), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'disproved',
      'x >= 1 does not imply x - 10 >= 0 — must still be disproved')
  })

  test('call nested in an expression: safeAdd(1, 2) - 10 is disproved', async () => {
    const source = `
      function safeAdd(a: number, b: number): number {
        requires(nonNegative(a))
        requires(nonNegative(b))
        ensures(output() >= a)
        ensures(output() >= b)
        return a + b
      }

      var a = safeAdd(1, 2) - 10
      safeAdd(1, a)
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('safeAdd(1, a)') && r.text.includes('nonNegative(b)'))
    assert.ok(target, `Expected an obligation for safeAdd(1, a), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'disproved',
      'ensures only guarantee result >= 2, so a = result - 10 can be negative')
    assert.ok(target.labels.some(l => l.startsWith('ensures(safeAdd)')),
      `Expected the nested call ensures to be tracked, got: ${target.labels.join(', ')}`)
  })

  test('call nested in an expression: safeAdd(1, 2) + 10 is proved', async () => {
    const source = `
      function safeAdd(a: number, b: number): number {
        requires(nonNegative(a))
        requires(nonNegative(b))
        ensures(output() >= a)
        ensures(output() >= b)
        return a + b
      }

      var a = safeAdd(1, 2) + 10
      safeAdd(1, a)
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('safeAdd(1, a)') && r.text.includes('nonNegative(b)'))
    assert.ok(target, `Expected an obligation for safeAdd(1, a), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      `result >= 2 implies a = result + 10 >= 12 (assumptions: ${target.labels.join(', ')})`)
  })

  test('call inside an early-exit if must not assume the negated guard', async () => {
    const source = `
      function needsPositive(n: number): number {
        requires(positive(n))
        return n * 2
      }

      function f(x: number): number {
        requires(nonNegative(x))
        if (x === 0) return needsPositive(x)
        return x
      }
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('needsPositive(x)'))
    assert.ok(target, `Expected an obligation for needsPositive(x), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'disproved',
      `x === 0 violates positive(x) — contradictory path assumptions would mask this (assumptions: ${target.labels.join(', ')})`)
  })

  test('recursive call with decreases proves via integer counter assumption', async () => {
    const source = `
      function countdown(n: number): number {
        requires(n >= 0)
        decreases(n)
        if (n === 0) return 0
        return countdown(n - 1)
      }
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('countdown(n - 1)'))
    assert.ok(target, `Expected an obligation for countdown(n - 1), got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      `n >= 0 ∧ n integer ∧ n !== 0 implies n - 1 >= 0 (assumptions: ${target.labels.join(', ')})`)
  })

  test('unknown call initializers still leave the variable unconstrained', async () => {
    const source = `
      function needsPositive(n: number): number {
        requires(positive(n))
        return n * 2
      }

      var y = mystery()
      needsPositive(y)
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('needsPositive(y)'))
    assert.ok(target)
    assert.strictEqual(target.status, 'disproved',
      'mystery() has no contract — y must stay unconstrained')
  })
})

describe('call-site: early-exit guard stability', () => {
  test('a guard over a reassigned variable is NOT assumed', async () => {
    const results = await checkCallSites(`
      function callee(x: number): number {
        requires(nonNegative(x))
        return x
      }
      function reassigned(v: number): number {
        let w = v
        if (w < 0) return 0
        w = -5
        return callee(w)
      }
      function stable(v: number): number {
        if (v < 0) return 0
        return callee(v)
      }
    `)
    const bad = results.find(r => r.text.includes('callee(w)'))
    const good = results.find(r => r.text.includes('callee(v)'))
    assert.ok(bad && good, `Expected both obligations, got: ${results.map(r => r.text).join('; ')}`)
    assert.notStrictEqual(bad.status, 'proved', 'the stale guard must not prove w >= 0')
    assert.strictEqual(good.status, 'proved', 'the stable guard discharges the requires')
  })
})
