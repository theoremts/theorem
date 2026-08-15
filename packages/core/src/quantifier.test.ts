import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { buildRegistry } from './registry/index.js'
import { extractCallSiteObligations } from './index.js'
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
// Quantified array contracts — forall/exists/sorted over Int indices
//
// The quarantined quantifier fragment: bound Int indices instantiating
// select terms. Recursive spec predicates and the heap stay ground.
// ---------------------------------------------------------------------------

describe('quantifiers: straight-line array contracts', () => {
  test('forall requires constrains elements', async () => {
    const results = await verifyAll(`
      export function firstOfPositives(arr: number[]): number {
        requires(arr.length >= 1)
        requires(forall(arr, (x) => x > 0))
        ensures(output() > 0)
        return arr[0]!
      }
    `)
    const ens = results.find(r => r.text.includes('output() > 0'))
    assert.ok(ens, 'Expected the ensures task')
    assert.strictEqual(ens.status, 'proved', 'forall must flow into the proof')
  })

  test('without the forall the same ensures is disproved (no silent dropping)', async () => {
    const results = await verifyAll(`
      export function firstUnconstrained(arr: number[]): number {
        requires(arr.length >= 1)
        ensures(output() > 0)
        return arr[0]!
      }
    `)
    const ens = results.find(r => r.text.includes('output() > 0'))
    assert.strictEqual(ens?.status, 'disproved')
  })

  test('sorted(arr) instantiates at concrete indices', async () => {
    const results = await verifyAll(`
      export function firstIsMin(arr: number[]): number {
        requires(sorted(arr))
        requires(arr.length >= 2)
        ensures(output() <= arr[1]!)
        return arr[0]!
      }
    `)
    const ens = results.find(r => r.text.includes('arr[1]'))
    assert.ok(ens, 'Expected the ensures task')
    assert.strictEqual(ens.status, 'proved')
  })
})

const lowerBoundSource = `
  export function lowerBound(arr: number[], target: number): number {
    requires(sorted(arr))
    ensures(output() >= 0)
    ensures(output() <= arr.length)
    ensures(forall(arr, (x, i) => i < output() ? x < target : x >= target))

    let lo = 0
    let hi = arr.length

    while (lo < hi) {
      invariant(() => lo >= 0 && lo <= hi && hi <= arr.length)
      invariant(() => forall(arr, (x, i) => i < lo ? x < target : true))
      invariant(() => forall(arr, (x, i) => i >= hi ? x >= target : true))
      decreases(() => hi - lo)

      const mid = Math.floor((lo + hi) / 2)
      if (arr[mid]! < target) {
        lo = mid + 1
      } else {
        hi = mid
      }
    }

    return lo
  }
`

describe('quantifiers: binary search (lower bound)', () => {
  test('every obligation proves — invariants, termination, quantified ensures', async () => {
    const results = await verifyAll(lowerBoundSource)
    assert.ok(results.length >= 10, `Expected the full heap-mode task set, got ${results.length}`)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  test('the textbook bug (lo = mid) is refuted on termination', async () => {
    const results = await verifyAll(lowerBoundSource.replace('lo = mid + 1', 'lo = mid'))
    const dec = results.find(r => r.text.includes('strictly decreases'))
    assert.ok(dec, 'Expected the decrease obligation')
    assert.strictEqual(dec.status, 'disproved')
  })

  test('dropping requires(sorted) refutes the left-half invariant', async () => {
    const results = await verifyAll(lowerBoundSource.replace('requires(sorted(arr))', ''))
    const preserved = results.find(r => r.text.includes('preserved') && r.text.includes('< target'))
    assert.ok(preserved, 'Expected the left-half preservation obligation')
    assert.strictEqual(preserved.status, 'disproved')
  })

  test('variance gate: 10 consecutive runs, identical verdicts, no divergence', async () => {
    // Bound-index names carry a global counter — normalize before comparing
    const sigOf = (rs: Array<{ text: string; status: string }>): string =>
      rs.map(r => `${r.text.replace(/__qi\d+/g, '__qi')}:${r.status}`).join('|')
    const signature = sigOf(await verifyAll(lowerBoundSource))
    for (let run = 1; run < 10; run++) {
      assert.strictEqual(sigOf(await verifyAll(lowerBoundSource)), signature, `Run ${run} diverged from run 0`)
    }
  })
})

// ---------------------------------------------------------------------------
// Arrays of objects — Account[] as Array(Int → Int): references composing
// with the field heaps. In-array aliasing (two slots, same object) is a
// solver case, not an assumption.
// ---------------------------------------------------------------------------

describe('ref-arrays: arrays of objects', () => {
  const payBonus = (distinct: boolean) => `
    interface Account { balance: number }
    export function payBonus(users: Account[], bonus: number): void {
      requires(users.length >= 2)
      ${distinct ? 'requires(users[0]! !== users[1]!)' : ''}
      requires(positive(bonus))
      ensures(users[0]!.balance === old(users[0]!.balance) + bonus)
      ensures(users[1]!.balance === old(users[1]!.balance) + bonus)
      users[0]!.balance = users[0]!.balance + bonus
      users[1]!.balance = users[1]!.balance + bonus
    }
  `

  test('in-array aliasing refutes per-slot ensures', async () => {
    const results = await verifyAll(payBonus(false))
    const slot0 = results.find(r => r.text.includes('users[0]'))
    assert.ok(slot0, 'Expected the slot-0 ensures task')
    assert.strictEqual(slot0.status, 'disproved', 'users[0] === users[1] doubles the credit')
  })

  test('slot distinctness makes both ensures prove', async () => {
    const results = await verifyAll(payBonus(true))
    assert.ok(results.length >= 2)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  const creditLoop = (op: string) => `
    interface Account { balance: number }
    export function touchAll(users: Account[], amount: number, n: number): void {
      requires(positive(amount))
      requires(nonNegative(n))
      requires(forall(users, (u) => u.balance >= 0))
      ensures(forall(users, (u) => u.balance >= 0))
      let k = 0
      while (k < n) {
        invariant(() => forall(users, (u) => u.balance >= 0))
        decreases(() => n - k)
        users[k]!.balance = users[k]!.balance ${op} amount
        k = k + 1
      }
    }
  `

  test('quantified field invariant preserved by a crediting loop (aliasing-robust)', async () => {
    const results = await verifyAll(creditLoop('+'))
    assert.ok(results.length >= 5, `Expected the loop task set, got ${results.length}`)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  test('the debiting loop refutes invariant preservation', async () => {
    const results = await verifyAll(creditLoop('-'))
    const preserved = results.find(r => r.text.includes('preserved'))
    assert.ok(preserved, 'Expected the preservation task')
    assert.strictEqual(preserved.status, 'disproved')
  })

  test('variance gate: 5 runs of the crediting loop, identical verdicts', async () => {
    const sigOf = (rs: Array<{ text: string; status: string }>): string =>
      rs.map(r => `${r.text.replace(/__qi\d+/g, '__qi')}:${r.status}`).join('|')
    const signature = sigOf(await verifyAll(creditLoop('+')))
    for (let run = 1; run < 5; run++) {
      assert.strictEqual(sigOf(await verifyAll(creditLoop('+'))), signature, `Run ${run} diverged`)
    }
  })
})

// ---------------------------------------------------------------------------
// Array.prototype.sort as a trusted contract: havoc + sortedness for the
// numeric ascending comparator; NOTHING for bare .sort() (lexicographic).
// ---------------------------------------------------------------------------

describe('sort: havoc + trusted sortedness', () => {
  test('numeric comparator establishes ensures(sorted)', async () => {
    const results = await verifyAll(`
      export function normalize(data: number[]): void {
        ensures(sorted(data))
        data.sort((a, b) => a - b)
      }
    `)
    const ens = results.find(r => r.text.includes('sorted('))
    assert.ok(ens, 'Expected the sorted ensures task')
    assert.strictEqual(ens.status, 'proved')
  })

  test('bare .sort() grants nothing — the lexicographic footgun', async () => {
    const results = await verifyAll(`
      export function footgun(data: number[]): void {
        ensures(sorted(data))
        data.sort()
      }
    `)
    const ens = results.find(r => r.text.includes('sorted('))
    assert.ok(ens, 'Expected the sorted ensures task')
    assert.strictEqual(ens.status, 'disproved')
  })

  test('havoc is honest: pre-sort content facts die', async () => {
    const results = await verifyAll(`
      export function stale(data: number[]): void {
        requires(data.length >= 1)
        ensures(data[0]! === old(data[0]!))
        data.sort((a, b) => a - b)
      }
    `)
    const ens = results.find(r => r.text.includes('old'))
    assert.ok(ens, 'Expected the stale-fact ensures task')
    assert.strictEqual(ens.status, 'disproved')
  })

  const searchSource = (withSort: string) => `
    export function lowerBound(arr: number[], target: number): number {
      requires(sorted(arr))
      ensures(output() >= 0)
      return 0
    }
    export function find(data: number[], target: number): number {
      ${withSort}
      return lowerBound(data, target)
    }
  `

  test('call site: a preceding numeric sort satisfies requires(sorted)', async () => {
    const ctx = await getContext()
    const source = searchSource('data.sort((a, b) => a - b)')
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const results = []
    for (const t of tasks) results.push({ text: t.contractText, status: (await check(t)).status })
    const sortedReq = results.find(r => r.text.includes('lowerBound(data'))
    assert.ok(sortedReq, `Expected the call-site obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(sortedReq.status, 'proved')
  })

  test('call site: without the sort the requires is refuted', async () => {
    const ctx = await getContext()
    const source = searchSource('')
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const results = []
    for (const t of tasks) results.push({ text: t.contractText, status: (await check(t)).status })
    const sortedReq = results.find(r => r.text.includes('lowerBound(data'))
    assert.ok(sortedReq, 'Expected the call-site obligation')
    assert.strictEqual(sortedReq.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// Array literals establish structural facts at call sites
// ---------------------------------------------------------------------------

describe('call sites: array-literal facts', () => {
  test('ident elements bound to fresh literals count as distinct allocations', async () => {
    const ctx = await getContext()
    const source = `
      interface Account { balance: number }
      export function payBonusSafe(users: Account[], bonus: number): void {
        requires(users.length >= 2)
        requires(users[0]! !== users[1]!)
        requires(positive(bonus))
        users[0]!.balance = users[0]!.balance + bonus
        users[1]!.balance = users[1]!.balance + bonus
      }
      export function caller(amount: number): void {
        requires(positive(amount))
        var a = { balance: 100 }
        let users: Account[] = [a, { balance: 200 }]
        payBonusSafe(users, amount)
      }
    `
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    for (const t of tasks) {
      const r = await check(t)
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${t.contractText}`)
    }
  })

  test('the SAME ident twice is the same object — distinctness refuted', async () => {
    const ctx = await getContext()
    const source = `
      interface Account { balance: number }
      export function payBonusSafe(users: Account[], bonus: number): void {
        requires(users.length >= 2)
        requires(users[0]! !== users[1]!)
        users[0]!.balance = users[0]!.balance + bonus
      }
      export function caller(amount: number): void {
        var a = { balance: 100 }
        let users: Account[] = [a, a]
        payBonusSafe(users, amount)
      }
    `
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const distinct = []
    for (const t of tasks) {
      if (!t.contractText.includes('!==')) continue
      distinct.push({ text: t.contractText, status: (await check(t)).status })
    }
    assert.ok(distinct.length >= 1, 'Expected the distinctness obligation')
    assert.strictEqual(distinct[0]!.status, 'disproved', '[a, a] aliases both slots')
  })

  test('quantified field requires checked at call sites against literal facts', async () => {
    const ctx = await getContext()
    const source = (bal: number) => `
      interface Account { balance: number }
      export function payBonusSafe(users: Account[], bonus: number): void {
        requires(forall(users, (u) => u.balance >= 0))
        requires(positive(bonus))
        users[0]!.balance = users[0]!.balance + bonus
      }
      export function caller(amount: number): void {
        requires(positive(amount))
        let users: Account[] = [{ balance: 100 }, { balance: ${bal} }]
        payBonusSafe(users, amount)
      }
    `
    for (const [bal, expected] of [[-100, 'disproved'], [200, 'proved']] as const) {
      const registry = buildRegistry(extractFromSource(source(bal)))
      const tasks = extractCallSiteObligations(source(bal), 'test.ts', registry, ctx)
      const quantified = tasks.find(t => t.contractText.includes('balance'))
      assert.ok(quantified, `Expected the forall obligation (balance ${bal}) — silent drops are the enemy`)
      assert.strictEqual((await check(quantified)).status, expected, `balance ${bal}`)
    }
  })

  test('a fresh two-object literal satisfies length and distinctness requires', async () => {
    const ctx = await getContext()
    const source = `
      interface Account { balance: number }
      export function payBonusSafe(users: Account[], bonus: number): void {
        requires(users.length >= 2)
        requires(users[0]! !== users[1]!)
        requires(positive(bonus))
        users[0]!.balance = users[0]!.balance + bonus
        users[1]!.balance = users[1]!.balance + bonus
      }
      export function caller(amount: number): void {
        requires(positive(amount))
        let users: Account[] = [{ balance: 100 }, { balance: 200 }]
        payBonusSafe(users, amount)
      }
    `
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const results = []
    for (const t of tasks) results.push({ text: t.contractText, status: (await check(t)).status })
    assert.ok(results.length >= 3, `Expected 3 obligations, got: ${results.length}`)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })
})

// ---------------------------------------------------------------------------
// Monotonicity of element fields: temporal (never shrinks across the call)
// and spatial (array sorted BY a field)
// ---------------------------------------------------------------------------

describe('ref-arrays: balance monotonicity', () => {
  test('quantified two-state ensures: crediting never shrinks any balance', async () => {
    const results = await verifyAll(`
      interface Account { balance: number }
      export function creditAll(users: Account[], bonus: number, n: number): void {
        requires(positive(bonus))
        requires(nonNegative(n))
        ensures(forall(users, (u) => u.balance >= old(u.balance)))
        let k = 0
        while (k < n) {
          invariant(() => forall(users, (u) => u.balance >= old(u.balance)))
          decreases(() => n - k)
          users[k]!.balance = users[k]!.balance + bonus
          k = k + 1
        }
      }
    `)
    assert.ok(results.length >= 5, `Expected the full task set, got ${results.length}`)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })

  test('debiting refutes the two-state invariant preservation', async () => {
    const results = await verifyAll(`
      interface Account { balance: number }
      export function debitAll(users: Account[], fee: number, n: number): void {
        requires(positive(fee))
        requires(nonNegative(n))
        ensures(forall(users, (u) => u.balance >= old(u.balance)))
        let k = 0
        while (k < n) {
          invariant(() => forall(users, (u) => u.balance >= old(u.balance)))
          decreases(() => n - k)
          users[k]!.balance = users[k]!.balance - fee
          k = k + 1
        }
      }
    `)
    const preserved = results.find(r => r.text.includes('preserved'))
    assert.ok(preserved, 'Expected the preservation task — silent drops are the enemy')
    assert.strictEqual(preserved.status, 'disproved')
  })

  test('spatial: adjacent-pairs sortedBy makes users[0] the minimum', async () => {
    const results = await verifyAll(`
      interface Account { balance: number }
      export function poorest(users: Account[]): number {
        requires(users.length >= 2)
        requires(forall(users, (u, i) => i + 1 < users.length ? u.balance <= users[i + 1]!.balance : true))
        ensures(output() <= users[1]!.balance)
        return users[0]!.balance
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('users[1]'))?.status, 'proved')
  })
})

describe('loop contracts: header position', () => {
  test('invariant()/decreases() directly before the while attach to it', async () => {
    const results = await verifyAll(`
      interface Account { balance: number }
      export function creditAll(users: Account[], bonus: number, n: number): void {
        requires(positive(bonus))
        requires(nonNegative(n))
        requires(forall(users, (u) => u.balance >= 0))
        ensures(forall(users, (u) => u.balance >= 0))
        let k = 0
        invariant(() => forall(users, (u) => u.balance >= 0))
        decreases(() => n - k)
        while (k < n) {
          users[k]!.balance = users[k]!.balance + bonus
          k = k + 1
        }
      }
    `)
    const preserved = results.find(r => r.text.includes('preserved'))
    assert.ok(preserved, 'Header-position invariant must attach to the loop')
    assert.strictEqual(preserved.status, 'proved')
    const decrease = results.find(r => r.text.includes('strictly decreases'))
    assert.ok(decrease, 'Header-position decreases must attach too')
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
  })
})
