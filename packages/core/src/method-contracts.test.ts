import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource, extractDeclareContracts } from './parser/index.js'
import { buildRegistry } from './registry/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Method contracts — `declare(Type.prototype.method, ...)` matched against
// `x.method(y)` call sites, with the receiver bound as the first contract
// parameter. This is the bridge that makes @theoremts/contracts-decimal work.
// ---------------------------------------------------------------------------

const DECIMAL_DECLARES = `
  declare(Decimal.prototype.add, (a: number, b: number): number => {
    ensures(output() === a + b)
  })
  declare(Decimal.prototype.div, (a: number, b: number): number => {
    requires(b !== 0)
    ensures(output() === a / b)
  })
  declare(Decimal.prototype.mul, (a: number, b: number): number => {
    ensures(output() === a * b)
  })
  declare(Decimal.prototype.greaterThanOrEqualTo, (a: number, b: number): boolean => {
    ensures(output() === (a >= b))
  })
  declare(Decimal.prototype.toNumber, (a: number): number => {
    ensures(output() === a)
  })
  declare(Decimal, (a: number): number => {
    ensures(output() === a)
  })
`

async function verifyWithDeclares(source: string) {
  const ctx = await getContext()
  const declares = extractDeclareContracts(DECIMAL_DECLARES, 'decimal.contracts.ts')
  const fns = extractFromSource(source)
  const registry = buildRegistry([...declares, ...fns])
  const results: Array<{ fn: string; text: string; status: string }> = []
  for (const ir of fns) {
    for (const task of translate(ir, ctx, registry)) {
      const result = await check(task)
      results.push({ fn: ir.name ?? '?', text: task.contractText, status: result.status })
    }
  }
  return results
}

describe('method contracts: Decimal chains', () => {
  test('rate-to-share chain proves under a non-negative requires', async () => {
    const results = await verifyWithDeclares(`
      export function convertRateToShare(ratePercent: Decimal): Decimal {
        requires(ratePercent.greaterThanOrEqualTo(0))
        ensures(output().greaterThanOrEqualTo(0))
        return ratePercent.div(ratePercent.add(100)).mul(100)
      }
    `)
    const goal = results.find(r => r.text.includes('output().greaterThanOrEqualTo(0)'))
    assert.strictEqual(goal?.status, 'proved')
    // The declared div contract emits its b !== 0 obligation at the call site,
    // discharged by the requires (ratePercent + 100 >= 100).
    const divSafety = results.find(r => r.text.includes('!== 0'))
    assert.strictEqual(divSafety?.status, 'proved')
  })

  test('without the requires, the div-by-zero obligation is refuted at -100', async () => {
    const results = await verifyWithDeclares(`
      export function convertRateToShare(ratePercent: Decimal): Decimal {
        ensures(output().greaterThanOrEqualTo(0))
        return ratePercent.div(ratePercent.add(100)).mul(100)
      }
    `)
    const divSafety = results.find(r => r.text.includes('!== 0'))
    assert.strictEqual(divSafety?.status, 'disproved')
  })

  test('guarded division proves through ternary branches with method calls', async () => {
    const results = await verifyWithDeclares(`
      export function half(x: Decimal, y: Decimal): number {
        requires(y.greaterThanOrEqualTo(1))
        ensures(output() >= 0)
        return x.greaterThanOrEqualTo(0) ? x.div(y).toNumber() : 0
      }
    `)
    const goal = results.find(r => r.text.includes('output() >= 0'))
    assert.strictEqual(goal?.status, 'proved')
  })

  test('new Decimal(n) is the numeric identity', async () => {
    const results = await verifyWithDeclares(`
      export function one(): number {
        ensures(output() === 1)
        return new Decimal(1).toNumber()
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('=== 1'))?.status, 'proved')
  })

  test('quantified field contract with a Decimal method projection', async () => {
    const results = await verifyWithDeclares(`
      export function first(users: Account[]): number {
        requires(forall(users, (u) => u.balance.greaterThanOrEqualTo(100)))
        requires(users.length >= 1)
        ensures(output() >= 100)
        return users[0]!.balance
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 100'))?.status, 'proved')
  })

  test('a wrong postcondition on a chain is refuted, not skipped', async () => {
    const results = await verifyWithDeclares(`
      export function addTen(x: Decimal): number {
        requires(x.greaterThanOrEqualTo(0))
        ensures(output() >= 11)
        return x.add(10).toNumber()
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 11'))?.status, 'disproved')
  })
})
