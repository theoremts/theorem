import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource, extractDeclareContracts } from './parser/index.js'
import { buildRegistry } from './registry/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Array.prototype.reduce as a fold — the numeric-accumulation pattern
// (`arr.reduce((acc, x) => acc + x.f, 0)`, Decimal `acc.add(x.f || 0)`)
// desugars to __sumBy with boundary axioms: len === 0 ⟹ sum === 0, and
// bounds from quantified element facts (forall proj >= c ⟹ sum >= c·len).
// ---------------------------------------------------------------------------

const DECIMAL_DECLARES = `
  declare(Decimal.prototype.add, (a: number, b: number): number => {
    ensures(output() === a + b)
  })
  declare(Decimal, (a: number): number => {
    ensures(output() === a)
  })
`

async function verifyAll(source: string) {
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

describe('reduce folds: numeric accumulation', () => {
  test('non-negative elements prove a non-negative sum', async () => {
    const results = await verifyAll(`
      export function totalAmount(items: Item[]): number {
        requires(forall(items, (i) => i.amount >= 0))
        ensures(output() >= 0)
        return items.reduce((acc, i) => acc + i.amount, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
  })

  test('without the element fact the sum is refuted, not skipped', async () => {
    const results = await verifyAll(`
      export function totalAmount(items: Item[]): number {
        ensures(output() >= 0)
        return items.reduce((acc, i) => acc + i.amount, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'disproved')
  })

  test('empty array folds to exactly zero', async () => {
    const results = await verifyAll(`
      export function totalAmount(items: Item[]): number {
        requires(items.length === 0)
        ensures(output() === 0)
        return items.reduce((acc, i) => acc + i.amount, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('=== 0'))?.status, 'proved')
  })

  test('an upper element bound gives an upper sum bound', async () => {
    const results = await verifyAll(`
      export function totalAmount(items: Item[]): number {
        requires(forall(items, (i) => i.amount <= 10))
        requires(items.length <= 3)
        ensures(output() <= 30)
        return items.reduce((acc, i) => acc + i.amount, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('<= 30'))?.status, 'proved')
  })

  test('Decimal accumulation with a nullish guard proves under a conditional fact', async () => {
    const results = await verifyAll(`
      export function balance(items: Item[]): Decimal {
        requires(forall(items, (i) => !i.balanceRemaining || i.balanceRemaining >= 0))
        ensures(output() >= 0)
        return items.reduce((acc, i) => acc.add(i.balanceRemaining || 0), new Decimal(0))
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
  })

  test('an UNGUARDED fold does not borrow the conditional fact (NaN poison)', async () => {
    const results = await verifyAll(`
      export function balance(items: Item[]): number {
        requires(forall(items, (i) => !i.balanceRemaining || i.balanceRemaining >= 0))
        ensures(output() >= 0)
        return items.reduce((acc, i) => acc + i.balanceRemaining, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'disproved')
  })

  test('a stronger claim than the bound justifies is refuted', async () => {
    const results = await verifyAll(`
      export function totalAmount(items: Item[]): number {
        requires(forall(items, (i) => i.amount >= 0))
        ensures(output() >= 1)
        return items.reduce((acc, i) => acc + i.amount, 0)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 1'))?.status, 'disproved')
  })
})

describe('for-of accumulation folds', () => {
  test('let acc = 0 accumulation proves non-negativity', async () => {
    const results = await verifyAll(`
      export function total(items: Item[]): number {
        requires(forall(items, (i) => i.amount >= 0))
        ensures(output() >= 0)
        let acc = 0
        for (const item of items) {
          acc = acc + item.amount
        }
        return acc
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
  })

  test('a continue-guard makes the loop a SUBSET — strong bounds are clamped', async () => {
    const results = await verifyAll(`
      export function totalTop(items: Item[]): number {
        requires(forall(items, (i) => i.amount >= 5))
        requires(items.length >= 1)
        ensures(output() >= 5)
        let acc = 0
        for (const item of items) {
          if (item.parentId) continue;
          acc = acc + item.amount
        }
        return acc
      }
    `)
    // All items could be skipped: the sum is only >= 0, never >= 5.
    assert.strictEqual(results.find(r => r.text.includes('>= 5'))?.status, 'disproved')
  })

  test('the same subset loop still proves the clamped bound', async () => {
    const results = await verifyAll(`
      export function totalTop(items: Item[]): number {
        requires(forall(items, (i) => i.amount >= 5))
        ensures(output() >= 0)
        let acc = 0
        for (const item of items) {
          if (item.parentId) continue;
          acc = acc + item.amount
        }
        return acc
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
  })

  test('Decimal accumulators with a free-const init prove under assume', async () => {
    const results = await verifyAll(`
      export function summary(items: Item[]): number {
        assume(ZERO === 0)
        requires(forall(items, (i) => i.baseCost >= 0))
        ensures(output() >= 0)
        let baseCostTotal = ZERO
        for (const item of items) {
          baseCostTotal = baseCostTotal.add(item.baseCost)
        }
        return baseCostTotal
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
  })

  test('two accumulators in one loop each get their own fold', async () => {
    const results = await verifyAll(`
      export function totals(items: Item[]): { cost: number; tax: number } {
        requires(forall(items, (i) => i.cost >= 0))
        requires(forall(items, (i) => i.tax >= 0))
        ensures(output().cost >= 0)
        ensures(output().tax >= 0)
        let cost = 0
        let tax = 0
        for (const item of items) {
          cost = cost + item.cost
          tax = tax + item.tax
        }
        return { cost, tax }
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('cost >= 0'))?.status, 'proved')
    assert.strictEqual(results.find(r => r.text.includes('tax >= 0'))?.status, 'proved')
  })

  test('unknown-fallback subset derives NO bounds', async () => {
    const results = await verifyAll(`
      export function total(items: Item[]): number {
        requires(forall(items, (i) => !i.amount || i.amount >= 0))
        ensures(output() >= 0)
        let acc = 0
        for (const item of items) {
          if (item.skip) continue;
          acc = acc + (item.amount ?? FALLBACK)
        }
        return acc
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'disproved')
  })
})

describe('fold bounds from vocabulary predicates', () => {
  test('forall(arr, it => nonNegative(it.f)) bounds the sum', async () => {
    const results = await verifyAll(`
      interface Entry { hours: number }
      export function totalHours(entries: Entry[]): number {
        requires(forall(entries, (it) => nonNegative(it.hours)))
        ensures(nonNegative(output()))
        return entries.reduce((acc, it) => acc + it.hours, 0)
      }
    `)
    const target = results.find(r => r.text.includes('output'))
    assert.ok(target, 'Expected the ensures task')
    assert.strictEqual(target.status, 'proved', 'vocabulary bound must feed the fold axiom')
  })
})
