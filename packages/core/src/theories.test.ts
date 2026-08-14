import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

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

// ---------------------------------------------------------------------------
// Regular expressions — /re/.test(s) and z.string().regex() become Z3
// regular-expression membership, integrated with sequence lengths.
// ---------------------------------------------------------------------------

describe('regex: contracts', () => {
  test('digits-only implies non-empty', async () => {
    const results = await verifyAll(`
      export function f(s: string): number {
        requires(/^\\d+$/.test(s))
        ensures(output() >= 1)
        return s.length
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 1'))?.status, 'proved')
  })

  test('digits-only does NOT imply length two — counterexample', async () => {
    const results = await verifyAll(`
      export function f(s: string): number {
        requires(/^\\d+$/.test(s))
        ensures(output() >= 2)
        return s.length
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 2'))?.status, 'disproved')
  })

  test('unanchored test is substring search', async () => {
    const results = await verifyAll(`
      export function f(s: string): number {
        requires(/\\d/.test(s))
        ensures(output() >= 1)
        return s.length
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('>= 1'))?.status, 'proved')
  })

  test('zod .regex with a bounded quantifier pins the length', async () => {
    const results = await verifyAll(`
      const S = z.object({ zip: z.string().regex(/^\\d{5}$/) })
      export function f(input: unknown): number {
        const user = S.parse(input)
        ensures(output() === 5)
        return user.zip.length
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('=== 5'))?.status, 'proved')
  })

  test('unsupported constructs are dropped, not approximated', async () => {
    const results = await verifyAll(`
      export function f(s: string): number {
        requires(/^(?=a)a+$/.test(s))
        ensures(output() >= 1)
        return s.length
      }
    `)
    // Lookahead unsupported → constraint dropped → ensures must be REFUTED
    assert.strictEqual(results.find(r => r.text.includes('>= 1'))?.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// Bitwise — Int-classified state maps through BV32 (JS ToInt32 semantics)
// ---------------------------------------------------------------------------

describe('bitwise: BV32 over integer state', () => {
  const lowBits = (expected: number) => `
    export function setLowBits(): number {
      ensures(output() === ${expected})
      let flags = 0
      let i = 0
      while (i < 3) {
        invariant(() => i >= 0 && i <= 3)
        invariant(() => flags === (1 << i) - 1)
        decreases(() => 3 - i)
        flags = flags | (1 << i)
        i = i + 1
      }
      return flags
    }
  `

  test('OR-accumulation of shifted bits proves through the loop', async () => {
    const results = await verifyAll(lowBits(7))
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  test('wrong constant is refuted', async () => {
    const results = await verifyAll(lowBits(8))
    assert.strictEqual(results.find(r => r.text.includes('=== 8'))?.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// Loop-invariant inference (CHC/Spacer) — the tool writes the invariants
// ---------------------------------------------------------------------------

import { inferLoopInvariants } from './verifier/invariant-inference.js'

describe('invariant inference: Spacer round-trip', () => {
  const payoutSource = (invariantLines: string) => `
    export function payout(total: number): number {
      requires(Number.isInteger(total))
      requires(nonNegative(total))
      ensures(output() === 3 * total)
      let remaining = total
      let paid = 0
      while (remaining > 0) {
        ${invariantLines}
        decreases(() => remaining)
        paid = paid + 3
        remaining = remaining - 1
      }
      return paid
    }
  `

  test('infers invariants that protect the ensures', async () => {
    const ctx = await getContext()
    const ir = extractFromSource(payoutSource('')).find(f => f.name === 'payout')
    assert.ok(ir?.heapSteps, 'Expected heap-mode routing')
    const inferred = await inferLoopInvariants(ir, ctx)
    assert.ok(inferred, 'Expected Spacer to find an invariant')
    assert.ok(inferred.invariants.length >= 2, `Got: ${inferred.invariants.join('; ')}`)
    // The load-bearing linear fact must be among them
    assert.ok(
      inferred.invariants.some(i => i.includes('paid') && i.includes('remaining') && i.includes('total')),
      `Expected the linear combination, got: ${inferred.invariants.join('; ')}`,
    )
  })

  test('round-trip: pasted inferred invariants make verify prove everything', async () => {
    const ctx = await getContext()
    const ir = extractFromSource(payoutSource('')).find(f => f.name === 'payout')
    const inferred = await inferLoopInvariants(ir!, ctx)
    assert.ok(inferred)
    const lines = inferred.invariants.map(i => `invariant(() => ${i})`).join('\n        ')
    const results = await verifyAll(payoutSource(lines))
    assert.ok(results.length >= 8, `Expected the full task set, got ${results.length}`)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  test('stays silent when the user already wrote invariants', async () => {
    const ctx = await getContext()
    const ir = extractFromSource(payoutSource('invariant(() => paid >= 0)')).find(f => f.name === 'payout')
    assert.ok(ir?.heapSteps)
    const inferred = await inferLoopInvariants(ir!, ctx)
    assert.strictEqual(inferred, null, 'Inference must not override user invariants')
  })
})

// ---------------------------------------------------------------------------
// Discriminated unions — exhaustiveness as a provable fact
// ---------------------------------------------------------------------------

describe('discriminated unions', () => {
  const payment = (cases: string) => `
    type Payment =
      | { kind: 'pix'; amount: number }
      | { kind: 'boleto'; amount: number }
      | { kind: 'card'; amount: number }
    export function fee(p: Payment): number {
      ensures(nonNegative(output()))
      ${cases}
      return -1
    }
  `

  test('exhaustive handling proves the fallback dead', async () => {
    const results = await verifyAll(payment(`
      if (p.kind === 'pix') return 0
      if (p.kind === 'boleto') return 2
      if (p.kind === 'card') return 1
    `))
    assert.strictEqual(results.find(r => r.text.includes('nonNegative'))?.status, 'proved')
  })

  test('a forgotten variant is a counterexample', async () => {
    const results = await verifyAll(payment(`
      if (p.kind === 'pix') return 0
      if (p.kind === 'boleto') return 2
    `))
    assert.strictEqual(results.find(r => r.text.includes('nonNegative'))?.status, 'disproved')
  })

  test('discriminant narrowing flows into contracts', async () => {
    const results = await verifyAll(`
      type Shape = { kind: 'circle'; r: number } | { kind: 'square'; side: number }
      export function pick(s: Shape, x: number): number {
        requires(positive(x))
        requires(s.kind === 'circle')
        ensures(output() === x)
        if (s.kind === 'circle') return x
        return x + 1
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('=== x'))?.status, 'proved')
  })
})
