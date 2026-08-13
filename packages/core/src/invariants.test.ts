import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

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

// ---------------------------------------------------------------------------
// Schema .refine() invariants
// ---------------------------------------------------------------------------

const refineSource = `
  declare const z: any
  const TaxRecordSchema = z.object({
    gross: z.number().positive(),
    tax: z.number().nonnegative(),
    net: z.number(),
  }).refine(t => t.gross === t.tax + t.net)
  type TaxRecord = z.output<typeof TaxRecordSchema>

  export function computeTax(income: number, rate: number): TaxRecord {
    requires(positive(income))
    requires(between(rate, 0, 0.5))
    const tax = income * rate
    return { gross: income, tax, net: income - tax }
  }

  export function buggyRebate(income: number): TaxRecord {
    requires(positive(income))
    return { gross: income, tax: 10, net: income }
  }
`

describe('schema .refine() invariants', () => {
  test('producer maintaining the invariant is proved', async () => {
    const results = await verifyAll(refineSource)
    const ok = results.find(r => r.fn === 'computeTax' && r.text.includes('output().gross'))
    assert.ok(ok, `Expected invariant obligation on computeTax, got: ${results.map(r => `${r.fn}: ${r.text}`).join('; ')}`)
    assert.strictEqual(ok.status, 'proved')
  })

  test('producer breaking the invariant is disproved', async () => {
    const results = await verifyAll(refineSource)
    const bad = results.find(r => r.fn === 'buggyRebate' && r.text.includes('output().gross'))
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })

  test('destructured refine param is supported', async () => {
    const results = await verifyAll(`
      declare const z: any
      const S = z.object({ a: z.number(), b: z.number() }).refine(({ a, b }) => a >= b)
      type T = z.output<typeof S>
      export function make(x: number): T {
        return { a: x, b: x }
      }
    `)
    const t = results.find(r => r.fn === 'make')
    assert.ok(t, 'Expected invariant obligation from destructured refine')
    assert.strictEqual(t.status, 'proved', 'a === b satisfies a >= b')
  })

  test('parse() assumes the refine invariant for consumers', async () => {
    const results = await verifyAll(`
      declare const z: any
      const S = z.object({
        total: z.number().positive(),
        used: z.number().nonnegative(),
        free: z.number(),
      }).refine(s => s.total === s.used + s.free)
      export function freeRatio(input: unknown): number {
        const s = S.parse(input)
        return s.free / s.total
      }
    `)
    const div = results.find(r => r.fn === 'freeRatio' && r.text.includes('safe division'))
    assert.ok(div)
    assert.strictEqual(div.status, 'proved', 'total > 0 from the schema guards the division')
  })
})

// ---------------------------------------------------------------------------
// Class @invariant
// ---------------------------------------------------------------------------

const accountSource = `
  import { invariant, requires, positive } from 'theoremts'

  @invariant((self) => self.balance >= 0)
  class Account {
    balance: number
    constructor(initial: number) {
      requires(positive(initial))
      this.balance = initial
    }
    deposit(amount: number): void {
      requires(positive(amount))
      this.balance = this.balance + amount
    }
    withdraw(amount: number): void {
      requires(positive(amount))
      if (amount <= this.balance) {
        this.balance = this.balance - amount
      }
    }
    overdraw(amount: number): void {
      requires(positive(amount))
      this.balance = this.balance - amount
    }
  }
`

describe('class @invariant', () => {
  test('constructor must establish the invariant', async () => {
    const results = await verifyAll(accountSource)
    const ctor = results.find(r => r.fn === 'Account.constructor')
    assert.ok(ctor, `Expected constructor obligation, got: ${results.map(r => r.fn).join(', ')}`)
    assert.strictEqual(ctor.status, 'proved')
  })

  test('mutating methods that preserve the invariant are proved', async () => {
    const results = await verifyAll(accountSource)
    for (const fn of ['deposit', 'withdraw']) {
      const r = results.find(x => x.fn === fn)
      assert.ok(r, `Expected obligation for ${fn}`)
      assert.strictEqual(r.status, 'proved', `${fn}: ${r.text}`)
    }
  })

  test('unguarded mutation violating the invariant is disproved', async () => {
    const results = await verifyAll(accountSource)
    const bad = results.find(r => r.fn === 'overdraw')
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// Cross-file schema resolution
// ---------------------------------------------------------------------------

describe('cross-file schema resolution', () => {
  test('invariants and constraints resolve through relative imports', async () => {
    const dir = mkdtempSync(join(tmpdir(), 'theorem-xfile-'))
    writeFileSync(join(dir, 'schemas.ts'), `
      declare const z: any
      export const InvoiceSchema = z.object({
        subtotal: z.number().positive(),
        tax: z.number().nonnegative(),
        total: z.number(),
      }).refine(i => i.total === i.subtotal + i.tax)
    `)
    const billing = `
      import { InvoiceSchema } from './schemas'
      declare const z: any
      type Invoice = z.output<typeof InvoiceSchema>

      export function makeInvoice(subtotal: number, tax: number): Invoice {
        requires(positive(subtotal))
        requires(nonNegative(tax))
        return { subtotal, tax, total: subtotal + tax }
      }
      export function buggyInvoice(subtotal: number, tax: number): Invoice {
        requires(positive(subtotal))
        requires(nonNegative(tax))
        return { subtotal, tax, total: subtotal }
      }
      export function taxRate(input: unknown): number {
        const inv = InvoiceSchema.parse(input)
        return inv.tax / inv.subtotal
      }
    `
    const results = await verifyAll(billing, join(dir, 'billing.ts'))

    const ok = results.find(r => r.fn === 'makeInvoice')
    assert.ok(ok, `Expected cross-file invariant obligation, got: ${results.map(r => r.fn).join(', ')}`)
    assert.strictEqual(ok.status, 'proved')

    const bad = results.find(r => r.fn === 'buggyInvoice')
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')

    const div = results.find(r => r.fn === 'taxRate' && r.text.includes('safe division'))
    assert.ok(div, 'Expected division safety from imported schema constraint')
    assert.strictEqual(div.status, 'proved')
  })
})
