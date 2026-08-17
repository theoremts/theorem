import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { buildRegistry } from './registry/index.js'
import { extractCallSiteObligations } from './verifier/call-sites.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Destructured object parameters — `function f({ a, b }: Input)` verifies
// like `function f(a, b)`: bindings become params (typed from the same-file
// interface/type literal), and call sites map object-literal arguments per
// property, plain idents as member accesses, and missing props to defaults.
// ---------------------------------------------------------------------------

async function verifySource(source: string) {
  const ctx = await getContext()
  const results: Array<{ text: string; status: string }> = []
  for (const ir of extractFromSource(source, 'test.ts')) {
    for (const task of translate(ir, ctx)) {
      results.push({ text: task.contractText, status: (await check(task)).status })
    }
  }
  return results
}

async function checkCallSites(source: string) {
  const ctx = await getContext()
  const registry = buildRegistry(extractFromSource(source))
  const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
  const results = []
  for (const task of tasks) {
    results.push({ text: task.contractText, status: (await check(task)).status })
  }
  return results
}

describe('destructured params: function bodies', () => {
  test('bindings verify like positional params (inline type literal)', async () => {
    const source = `
      export function total({ price, qty }: { price: number; qty: number }): number {
        requires(price >= 0)
        requires(qty >= 1)
        ensures(output() >= price)
        return price * qty
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('>= price'))
    assert.ok(target, `Expected the ensures task, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })

  test('same-file interface supplies sorts and renames bind', async () => {
    const source = `
      interface LineItem {
        amount: number
        taxRate: number
      }
      export function withTax({ amount, taxRate: rate }: LineItem): number {
        requires(amount >= 0)
        requires(rate >= 0 && rate <= 1)
        ensures(output() >= amount)
        return amount * (1 + rate)
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('>= amount'))
    assert.ok(target, `Expected the ensures task, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })

  test('binding default participates in the proof', async () => {
    const source = `
      export function scaled({ x, factor = 2 }: { x: number; factor?: number }): number {
        requires(x >= 0)
        requires(factor >= 1)
        ensures(output() >= 0)
        return x * factor
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('>= 0') && r.text.includes('output'))
    assert.ok(target, `Expected the ensures task, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })
})

const destructuredCalleeSource = `
  interface Order {
    subtotal: number
    discount: number
  }
  function netTotal({ subtotal, discount }: Order): number {
    requires(subtotal >= 0)
    requires(discount >= 0 && discount <= subtotal)
    ensures(output() >= 0)
    return subtotal - discount
  }
`

describe('destructured params: call sites', () => {
  test('object-literal argument maps per property — good values prove', async () => {
    const source = destructuredCalleeSource + `
      var ok = netTotal({ subtotal: 100, discount: 30 })
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('discount <= subtotal'))
    assert.ok(target, `Expected the cross-prop obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })

  test('object-literal argument — violating values disprove', async () => {
    const source = destructuredCalleeSource + `
      var bad = netTotal({ subtotal: 10, discount: 30 })
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('discount <= subtotal'))
    assert.ok(target, `Expected the cross-prop obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'disproved')
  })

  test('plain ident argument maps bindings to member accesses', async () => {
    const source = destructuredCalleeSource + `
      function caller(order: Order): number {
        requires(order.subtotal >= 0)
        requires(order.discount >= 0 && order.discount <= order.subtotal)
        return netTotal(order)
      }
    `
    const results = await checkCallSites(source)
    const target = results.find(r => r.text.includes('discount <= subtotal') || r.text.includes('discount') && r.text.includes('subtotal'))
    assert.ok(target, `Expected the cross-prop obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      'caller requires on order.discount/order.subtotal must discharge the callee requires')
  })
})
