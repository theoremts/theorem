import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { extractFromSource } from '../parser/index.js'
import { translate } from '../translator/index.js'
import { getContext, check } from '../solver/index.js'
import { scanSource } from '../scanner/index.js'

async function verifyAll(source: string, fileName = 'input.ts') {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string }> = []
  for (const ir of extractFromSource(source, fileName)) {
    for (const task of translate(ir, ctx)) {
      const result = await check(task)
      results.push({ fn: ir.name ?? '?', text: task.contractText, status: result.status })
    }
  }
  return results
}

const effectSource = `
  import { Schema } from 'effect'

  const OrderSchema = Schema.Struct({
    total: Schema.Number.pipe(Schema.positive()),
    quantity: Schema.Number.pipe(Schema.int(), Schema.greaterThanOrEqualTo(1)),
    discount: Schema.Number.pipe(Schema.between(0, 0.5)),
  }).pipe(Schema.filter((o) => o.total >= o.discount))

  type Order = typeof OrderSchema.Type

  export function unitPrice(input: unknown): number {
    const order = Schema.decodeUnknownSync(OrderSchema)(input)
    return order.total / order.quantity
  }

  export function buggyAdjustment(input: unknown): number {
    const order = Schema.decodeUnknownSync(OrderSchema)(input)
    return order.total / (order.quantity - 1)
  }

  export function makeOrder(total: number): Order {
    requires(positive(total))
    return { total, quantity: 1, discount: 0 }
  }

  export function buggyOrder(total: number): Order {
    requires(positive(total))
    return { total, quantity: 1, discount: total + 1 }
  }
`

describe('effect schema as out-of-the-box contracts', () => {
  test('decode: schema-guarded division is proved safe', async () => {
    const results = await verifyAll(effectSource)
    const safe = results.find(r => r.fn === 'unitPrice' && r.text.includes('safe division'))
    assert.ok(safe, `Expected safe-division obligation, got: ${results.map(r => `${r.fn}: ${r.text}`).join('; ')}`)
    assert.strictEqual(safe.status, 'proved')
  })

  test('decode: unguarded arithmetic is disproved', async () => {
    const results = await verifyAll(effectSource)
    const bad = results.find(r => r.fn === 'buggyAdjustment' && r.text.includes('safe division'))
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })

  test('filter invariant: producer maintaining it is proved', async () => {
    const results = await verifyAll(effectSource)
    const ok = results.find(r => r.fn === 'makeOrder')
    assert.ok(ok, 'Expected filter-invariant obligation on makeOrder')
    assert.strictEqual(ok.status, 'proved')
  })

  test('filter invariant: producer breaking it is disproved', async () => {
    const results = await verifyAll(effectSource)
    const bad = results.find(r => r.fn === 'buggyOrder')
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })

  test('aliased import (import * as S) works', async () => {
    const results = await verifyAll(`
      import * as S from 'effect/Schema'
      const RateSchema = S.Struct({
        rate: S.Number.pipe(S.greaterThan(0), S.lessThanOrEqualTo(1)),
      })
      export function applyRate(amount: number, input: unknown): number {
        const r = S.decodeUnknownSync(RateSchema)(input)
        return amount / r.rate
      }
    `)
    const div = results.find(r => r.fn === 'applyRate' && r.text.includes('safe division'))
    assert.ok(div, `Expected division obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(div.status, 'proved', 'rate > 0 guards the division')
  })

  test('scan consumes effect schema constraints', async () => {
    const ctx = await getContext()
    const result = await scanSource(effectSource, 'test.ts', ctx)
    const flagged = result.functions.map(f => f.name)
    assert.ok(!flagged.includes('unitPrice'), `unitPrice must not be flagged, flagged: ${flagged.join(', ')}`)
    assert.ok(flagged.includes('buggyAdjustment'), 'buggyAdjustment must still be flagged')
  })

  test('cross-file: struct schema resolves through relative imports', async () => {
    const dir = mkdtempSync(join(tmpdir(), 'theorem-effect-'))
    writeFileSync(join(dir, 'schemas.ts'), `
      import { Schema } from 'effect'
      export const InvoiceSchema = Schema.Struct({
        subtotal: Schema.Number.pipe(Schema.positive()),
        tax: Schema.Number.pipe(Schema.nonNegative()),
        total: Schema.Number,
      }).pipe(Schema.filter((i) => i.total === i.subtotal + i.tax))
    `)
    const results = await verifyAll(`
      import { InvoiceSchema } from './schemas'
      import { Schema } from 'effect'
      type Invoice = typeof InvoiceSchema.Type

      export function makeInvoice(subtotal: number, tax: number): Invoice {
        requires(positive(subtotal))
        requires(nonNegative(tax))
        return { subtotal, tax, total: subtotal + tax }
      }
      export function taxRate(input: unknown): number {
        const inv = Schema.decodeUnknownSync(InvoiceSchema)(input)
        return inv.tax / inv.subtotal
      }
    `, join(dir, 'billing.ts'))

    const ok = results.find(r => r.fn === 'makeInvoice')
    assert.ok(ok, `Expected cross-file filter obligation, got: ${results.map(r => r.fn).join(', ')}`)
    assert.strictEqual(ok.status, 'proved')

    const div = results.find(r => r.fn === 'taxRate' && r.text.includes('safe division'))
    assert.ok(div)
    assert.strictEqual(div.status, 'proved')
  })
})
