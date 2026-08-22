import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// String-keyed records (Record<string, T> as uninterpreted String→Real maps)
// and exact decimal rounding (toDecimalPlaces with literal digits).
// ---------------------------------------------------------------------------

async function verifyAll(source: string) {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string }> = []
  for (const ir of extractFromSource(source)) {
    for (const task of translate(ir, ctx)) {
      results.push({ fn: ir.name ?? '?', text: task.contractText, status: (await check(task)).status })
    }
  }
  return results
}

describe('string-keyed records', () => {
  test('same key reads the same value (congruence)', async () => {
    const results = await verifyAll(`
      export function lookup(rates: Record<string, number>, currency: string): number {
        requires(rates[currency] > 0)
        ensures(output() > 0)
        return rates[currency]
      }
      export function viaEquality(rates: Record<string, number>, a: string, b: string): number {
        requires(a === b)
        requires(rates[a] > 0)
        ensures(output() > 0)
        return rates[b]
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'lookup')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'viaEquality')?.status, 'proved')
  })

  test('different keys stay independent — no fake congruence', async () => {
    const results = await verifyAll(`
      export function differentKeys(rates: Record<string, number>, a: string, b: string): number {
        requires(rates[a] > 0)
        ensures(output() > 0)
        return rates[b]
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'differentKeys')?.status, 'disproved',
      'rates[a] > 0 must not imply rates[b] > 0')
  })
})

describe('exact decimal rounding: toDecimalPlaces', () => {
  test('HALF_EVEN ties go to the even neighbour', async () => {
    const results = await verifyAll(`
      export function f(x: number): number {
        requires(x === 2.125)
        ensures(output() === 2.12)
        return x.toDecimalPlaces(2, Decimal.ROUND_HALF_EVEN)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('2.12'))?.status, 'proved')
  })

  test('HALF_UP ties go away from zero — both signs', async () => {
    const results = await verifyAll(`
      export function pos(x: number): number {
        requires(x === 2.125)
        ensures(output() === 2.13)
        return x.toDecimalPlaces(2, Decimal.ROUND_HALF_UP)
      }
      export function neg(x: number): number {
        requires(x === -2.125)
        ensures(output() === -2.13)
        return x.toDecimalPlaces(2, Decimal.ROUND_HALF_UP)
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'pos')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'neg')?.status, 'proved')
  })

  test('rounded-of-sum vs sum-of-rounded is REFUTABLE (money conservation)', async () => {
    const results = await verifyAll(`
      export function taxConservation(a: number, b: number, r: number): number {
        requires(a > 0 && b > 0 && r > 0 && r < 1)
        ensures(((a + b) * r).toDecimalPlaces(2, Decimal.ROUND_HALF_EVEN) === (a * r).toDecimalPlaces(2, Decimal.ROUND_HALF_EVEN) + (b * r).toDecimalPlaces(2, Decimal.ROUND_HALF_EVEN))
        return 0
      }
    `)
    const target = results.find(r => r.fn === 'taxConservation')
    assert.ok(target, 'Expected the conservation obligation — silent drops are the enemy')
    assert.strictEqual(target.status, 'disproved',
      'per-line rounding diverges from rounding the sum — must produce a counterexample')
  })
})
