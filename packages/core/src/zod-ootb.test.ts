import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'
import { scanSource } from './scanner/index.js'

// Zod schemas as first-class contracts: `const x = Schema.parse(input)` makes
// the schema's refinements hold for x.* — with zero requires/ensures annotations.

const zodSource = `
  const OrderSchema = z.object({
    total: z.number().positive(),
    quantity: z.number().min(1),
  })

  export function unitPrice(input: unknown): number {
    const order = OrderSchema.parse(input)
    return order.total / order.quantity
  }

  export function unitAdjustment(input: unknown): number {
    const order = OrderSchema.parse(input)
    return order.total / (order.quantity - 1)
  }
`

async function verifyAll(source: string) {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string }> = []
  for (const ir of extractFromSource(source)) {
    for (const task of translate(ir, ctx)) {
      const result = await check(task)
      results.push({ fn: ir.name ?? '?', text: task.contractText, status: result.status })
    }
  }
  return results
}

describe('zod schemas as out-of-the-box contracts', () => {
  test('verify: division guarded by schema min(1) is proved safe', async () => {
    const results = await verifyAll(zodSource)
    const safe = results.find(r => r.fn === 'unitPrice' && r.text.includes('safe division'))
    assert.ok(safe, `Expected a safe-division obligation for unitPrice, got: ${results.map(r => `${r.fn}: ${r.text}`).join('; ')}`)
    assert.strictEqual(safe.status, 'proved', 'schema guarantees quantity >= 1, so quantity !== 0')
  })

  test('verify: division the schema does NOT guard is disproved', async () => {
    const results = await verifyAll(zodSource)
    const unsafe = results.find(r => r.fn === 'unitAdjustment' && r.text.includes('safe division'))
    assert.ok(unsafe, 'Expected a safe-division obligation for unitAdjustment')
    assert.strictEqual(unsafe.status, 'disproved', 'quantity can be exactly 1, making quantity - 1 zero')
  })

  test('scan: schema constraints eliminate the false positive', async () => {
    const ctx = await getContext()
    const result = await scanSource(zodSource, 'test.ts', ctx)
    const flagged = result.functions.map(f => f.name)
    assert.ok(!flagged.includes('unitPrice'),
      `unitPrice must not be flagged (schema guards the division), flagged: ${flagged.join(', ')}`)
    assert.ok(flagged.includes('unitAdjustment'), 'unitAdjustment must still be flagged')
  })

  test('verify: sqrt/log guarded by positive() are proved safe', async () => {
    const results = await verifyAll(`
      const S = z.object({ total: z.number().positive() })
      export function volatility(input: unknown): number {
        const order = S.parse(input)
        return Math.sqrt(order.total) + Math.log(order.total)
      }
    `)
    const sqrt = results.find(r => r.text.includes('safe sqrt'))
    const log = results.find(r => r.text.includes('safe log'))
    assert.ok(sqrt && log, `Expected sqrt and log obligations, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(sqrt.status, 'proved')
    assert.strictEqual(log.status, 'proved')
  })

  test('verify: top-level schema constrains a plain identifier', async () => {
    const results = await verifyAll(`
      const RateSchema = z.number().gt(0).lte(1)
      export function applyRate(amount: number, input: unknown): number {
        const rate = RateSchema.parse(input)
        return amount / rate
      }
    `)
    const div = results.find(r => r.text.includes('safe division: rate'))
    assert.ok(div, `Expected a division obligation on rate, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(div.status, 'proved', 'rate > 0 makes the division safe')
  })

  test('functions without contracts or zod parse are not verified', async () => {
    const results = await verifyAll(`
      export function plain(a: number, b: number): number {
        return a / b
      }
    `)
    assert.strictEqual(results.length, 0, 'no contracts and no schema → no verification tasks')
  })
})

describe('zod dedup transforms as uniqueness guarantees', () => {
  test('.transform Map-dedup grants uniqueBy on the parsed value', async () => {
    const results = await verifyAll(`
      const RulesSchema = z.array(z.object({ key: z.string() }))
        .transform((arr) => [...new Map(arr.map((m) => [m.key, m])).values()])
      export function useRules(input: unknown): number {
        const rules = RulesSchema.parse(input)
        check(uniqueBy(rules, (m) => m.key))
        return 0
      }
    `)
    const target = results.find(r => r.text.includes('uniqueBy') && !r.text.includes('forall'))
    assert.ok(target, `Expected the uniqueBy check, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved', 'the schema transform guarantees deduplication')
  })

  test('.transform Set-dedup grants unique() — and refine-less schema does NOT', async () => {
    const granted = await verifyAll(`
      const IdsSchema = z.array(z.number()).transform((ids) => [...new Set(ids)])
      export function useIds(input: unknown): number {
        const ids = IdsSchema.parse(input)
        check(unique(ids))
        return 0
      }
    `)
    const g = granted.find(r => r.text.includes('unique'))
    assert.ok(g, 'Expected the unique check')
    assert.strictEqual(g.status, 'proved')

    const bare = await verifyAll(`
      const IdsSchema = z.array(z.number())
      export function useIds(input: unknown): number {
        const ids = IdsSchema.parse(input)
        check(unique(ids))
        return 0
      }
    `)
    const b = bare.find(r => r.text.includes('unique'))
    assert.ok(b, 'Expected the unique check')
    assert.strictEqual(b.status, 'disproved', 'no transform, no uniqueness')
  })
})
