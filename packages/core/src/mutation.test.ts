import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { buildRegistry } from './registry/index.js'
import { extractCallSiteObligations } from './index.js'
import { getContext, check } from './solver/index.js'

async function verifyAll(source: string) {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string; labels: string[]; ce?: Record<string, unknown> | undefined }> = []
  for (const ir of extractFromSource(source)) {
    for (const task of translate(ir, ctx)) {
      const result = await check(task)
      results.push({
        fn: ir.name ?? '?',
        text: task.contractText,
        status: result.status,
        labels: task.assumptionLabels,
        ce: result.status === 'disproved' ? result.counterexample : undefined,
      })
    }
  }
  return results
}

// ---------------------------------------------------------------------------
// Heap mode (mutation levels 1–3)
// ---------------------------------------------------------------------------

const drainSource = `
  interface Acc { value: number }

  export function drainUnsafe(from: Acc, to: Acc): void {
    requires(nonNegative(from.value))
    requires(nonNegative(to.value))
    ensures(to.value === old(to.value) + old(from.value))
    to.value = to.value + from.value
    from.value = 0
  }

  export function drainSafe(from: Acc, to: Acc): void {
    requires(from !== to)
    requires(nonNegative(from.value))
    requires(nonNegative(to.value))
    ensures(to.value === old(to.value) + old(from.value))
    ensures(from.value === 0)
    to.value = to.value + from.value
    from.value = 0
  }
`

describe('heap mode: mutation with aliasing (L2)', () => {
  test('aliased references refute the transfer ensures', async () => {
    const results = await verifyAll(drainSource)
    const bad = results.find(r => r.fn === 'drainUnsafe' && r.text.includes('old(to.value)'))
    assert.ok(bad, 'Expected transfer ensures obligation')
    assert.strictEqual(bad.status, 'disproved')
    // The counterexample must be the ALIASED case: same reference value
    assert.strictEqual(bad.ce?.['from'], bad.ce?.['to'], 'counterexample must alias from and to')
  })

  test('explicit anti-aliasing precondition makes it prove (L1)', async () => {
    const results = await verifyAll(drainSource)
    for (const text of ['old(to.value)', 'from.value === 0']) {
      const r = results.find(x => x.fn === 'drainSafe' && x.text.includes(text))
      assert.ok(r, `Expected obligation matching ${text}`)
      assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
    }
  })

  test('unmodeled mutation shapes surface a visible warning (L1 fallback)', async () => {
    const results = await verifyAll(`
      interface Acc { value: number }
      export function loopy(a: Acc, n: number): void {
        requires(positive(n))
        ensures(nonNegative(a.value))
        while (n > 0) {
          a.value = a.value + 1
          n = n - 1
        }
      }
    `)
    const anyTask = results.find(r => r.fn === 'loopy')
    assert.ok(anyTask, 'Expected at least one task for loopy')
    assert.ok(
      anyTask.labels.some(l => l.includes('unmodeled field mutation: a.value')),
      `Expected unmodeled-mutation warning, labels: ${anyTask.labels.join(', ')}`,
    )
  })
})

describe('modifies framing (L3)', () => {
  const source = `
    interface Acc { value: number }
    export function sneaky(a: Acc, b: Acc): void {
      modifies(a)
      requires(a !== b)
      ensures(a.value === 1)
      a.value = 1
      b.value = 2
    }
    export function honest(a: Acc, b: Acc): void {
      modifies(a, b)
      requires(a !== b)
      ensures(a.value === 1)
      a.value = 1
      b.value = 2
    }
  `

  test('undeclared write is a violation', async () => {
    const results = await verifyAll(source)
    const violation = results.find(r => r.fn === 'sneaky' && r.text.includes('modifies violation'))
    assert.ok(violation, 'Expected a modifies violation task')
    assert.strictEqual(violation.status, 'disproved')
    assert.ok(violation.text.includes('b.value'))
  })

  test('declared writes are clean', async () => {
    const results = await verifyAll(source)
    assert.ok(!results.some(r => r.fn === 'honest' && r.text.includes('modifies violation')))
    const ens = results.find(r => r.fn === 'honest')
    assert.strictEqual(ens?.status, 'proved')
  })
})

// ---------------------------------------------------------------------------
// Refinement types on parameters
// ---------------------------------------------------------------------------

describe('refinement types', () => {
  const source = `
    declare const z: any
    declare namespace z { type output<_S> = any }
    const RateSchema = z.number().gt(0).lte(1).brand<'Rate'>()
    type Rate = z.output<typeof RateSchema>

    export function applyRate(amount: number, rate: Rate): number {
      return amount / rate
    }
    export function bad(): number {
      return applyRate(100, 0 as Rate)
    }
  `

  test('parameter type alone makes the function verifiable', async () => {
    const results = await verifyAll(source)
    const div = results.find(r => r.fn === 'applyRate' && r.text.includes('safe division'))
    assert.ok(div, 'Expected division obligation from the refined param type')
    assert.strictEqual(div.status, 'proved', 'rate > 0 comes from the TYPE')
  })

  test('call sites must prove the refinement — casts do not fool the solver', async () => {
    const ctx = await getContext()
    const irs = extractFromSource(source)
    const registry = buildRegistry(irs)
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const results = []
    for (const t of tasks) results.push({ text: t.contractText, status: (await check(t)).status })

    const violated = results.find(r => r.text.includes('applyRate(100, 0 as Rate)') && r.text.includes('rate > 0'))
    assert.ok(violated, `Expected call-site obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(violated.status, 'disproved', 'as-cast satisfies tsc, not Z3')
  })
})
