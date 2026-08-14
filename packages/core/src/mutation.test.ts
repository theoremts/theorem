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
// Pointer surgery (L4 spike): pointer fields, null, writes through pointers
// ---------------------------------------------------------------------------

describe('heap mode: pointer-valued fields', () => {
  const linkSource = `
    interface Node { value: number; next: Node | null; prev: Node | null }

    export function linkFront(head: Node, node: Node): void {
      requires(head !== node)
      requires(node.next === null)
      requires(node.prev === null)
      ensures(node.next === head)
      ensures(head.prev === node)
      ensures(node.prev === null)
      node.next = head
      head.prev = node
    }

    export function buggyLink(head: Node, node: Node): void {
      requires(head !== node)
      requires(node.next === null)
      ensures(head.prev === node)
      node.next = head
    }

    export function aliasedLink(head: Node, node: Node): void {
      requires(node.prev === null)
      ensures(node.prev === null)
      node.next = head
      head.prev = node
    }

    export function unlinkSecond(head: Node): void {
      requires(head.next !== null)
      requires(head.next.prev === head)
      requires(head.next.next === null)
      ensures(head.next === null)
      const second = head.next
      head.next = second.next
      second.prev = null
    }
  `

  test('correct doubly-linked insertion is proved', async () => {
    const results = await verifyAll(linkSource)
    for (const r of results.filter(x => x.fn === 'linkFront')) {
      assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
    }
  })

  test('forgotten back-pointer is refuted', async () => {
    const results = await verifyAll(linkSource)
    const bad = results.find(r => r.fn === 'buggyLink' && r.text.includes('head.prev'))
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })

  test('aliased references clobber fields — counterexample has head === node', async () => {
    const results = await verifyAll(linkSource)
    const bad = results.find(r => r.fn === 'aliasedLink' && r.text.includes('node.prev === null'))
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
    assert.strictEqual(bad.ce?.['head'], bad.ce?.['node'], 'counterexample must alias head and node')
  })

  test('reads and writes through pointers are encoded (select of select)', async () => {
    const results = await verifyAll(linkSource)
    const r = results.find(x => x.fn === 'unlinkSecond')
    assert.ok(r, 'Expected unlinkSecond obligation')
    assert.strictEqual(r.status, 'proved')
  })
})

// ---------------------------------------------------------------------------
// F1: branches + early returns over the heap
// ---------------------------------------------------------------------------

describe('heap mode: branches and early returns', () => {
  const source = `
    interface Acc { value: number }
    interface Node { value: number; next: Node | null; prev: Node | null }

    export function withdraw(acc: Acc, amount: number): void {
      requires(nonNegative(acc.value))
      requires(positive(amount))
      ensures(nonNegative(acc.value))
      if (amount <= acc.value) {
        acc.value = acc.value - amount
      }
    }

    export function clampTransfer(from: Acc, to: Acc, amount: number): void {
      requires(from !== to)
      requires(nonNegative(from.value))
      requires(nonNegative(to.value))
      requires(positive(amount))
      ensures(nonNegative(from.value))
      ensures(to.value === old(to.value) + old(from.value) - from.value)
      if (amount <= from.value) {
        from.value = from.value - amount
        to.value = to.value + amount
      } else {
        to.value = to.value + from.value
        from.value = 0
      }
    }

    export function moveToFront(head: Node, node: Node): void {
      requires(head.prev === null)
      requires(node !== head)
      ensures(node === head || node.prev === null)
      if (node === head) return
      node.prev = null
      node.next = head
      head.prev = node
    }
  `

  test('if-guarded mutation preserves the ensures', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'withdraw')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
  })

  test('if/else merge: relational two-state ensures holds across both branches', async () => {
    const results = await verifyAll(source)
    for (const r of results.filter(x => x.fn === 'clampTransfer')) {
      assert.strictEqual(r.status, 'proved', `${r.text}`)
    }
  })

  test('early return + pointer surgery (moveToFront skeleton)', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'moveToFront')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved')
  })
})

// ---------------------------------------------------------------------------
// F2: spec functions with fuel-bounded definitional axioms
// ---------------------------------------------------------------------------

describe('spec functions (F2)', () => {
  const source = `
    interface Node { value: number; next: Node | null }
    function allPositive(n: Node | null): boolean {
      return n === null ? true : n.value > 0 && allPositive(n.next)
    }
    export function consPositive(x: number, tail: Node | null): Node {
      requires(positive(x))
      requires(tail === null || allPositive(tail))
      ensures(allPositive(output()))
      return { value: x, next: tail }
    }
    export function buggyCons(x: number, tail: Node | null): Node {
      requires(tail === null || allPositive(tail))
      ensures(allPositive(output()))
      return { value: x, next: tail }
    }
    function isSorted(p: { lo: number; hi: number }): boolean {
      return p.lo <= p.hi
    }
    export function makeSorted(a: number, b: number): { lo: number; hi: number } {
      ensures(isSorted(output()))
      return a <= b ? { lo: a, hi: b } : { lo: b, hi: a }
    }
  `

  test('recursive spec function: cons preserves the inductive invariant', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'consPositive')
    assert.ok(r, 'Expected consPositive obligation')
    assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
  })

  test('missing hypothesis is refuted, not vacuously proved', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'buggyCons')
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })

  test('ternary-of-objects body + non-recursive spec predicate', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'makeSorted')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved')
  })
})

// ---------------------------------------------------------------------------
// F3: sequence theory — the full Dafny Cons
// ---------------------------------------------------------------------------

describe('sequences (F3): the Cons example', () => {
  const source = `
    interface Node { readonly value: number; readonly next: Node | null }
    function list(n: Node | null): number[] {
      return n === null ? [] : [n.value, ...list(n.next)]
    }
    export function single(x: number): Node {
      ensures(seqEq(list(output()), [x]))
      return { value: x, next: null }
    }
    export function cons(x: number, tail: Node | null): Node {
      ensures(tail === null
        ? seqEq(list(output()), [x])
        : seqEq(list(output()), [x, ...list(tail)]))
      return { value: x, next: tail }
    }
    export function buggyCons(x: number, tail: Node | null): Node {
      ensures(tail === null
        ? seqEq(list(output()), [x])
        : seqEq(list(output()), [x, ...list(tail)]))
      return { value: x, next: null }
    }
  `

  test('base case: list(single(x)) === [x]', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'single')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
  })

  test('the defining equation of cons proves for all inputs', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'cons')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved')
  })

  test('dropping the tail is refuted', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'buggyCons')
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// F4: recursive spec predicates over the mutable heap
// ---------------------------------------------------------------------------

describe('heap invariants (F4)', () => {
  const source = `
    interface Node { value: number; next: Node | null; prev: Node | null }
    function validChain(n: Node | null): boolean {
      return n === null ? true
        : n.next === null ? true
        : n.next.prev === n && validChain(n.next)
    }
    export function linkFront(head: Node, node: Node): void {
      requires(head !== node)
      requires(head.next === null)
      requires(node.next === null)
      requires(node.prev === null)
      ensures(validChain(node))
      node.next = head
      head.prev = node
    }
    export function buggyLink(head: Node, node: Node): void {
      requires(head !== node)
      requires(head.next === null)
      requires(node.next === null)
      ensures(validChain(node))
      node.next = head
    }
    export function touchValue(head: Node, v: number): void {
      requires(validChain(head))
      ensures(validChain(head))
      head.value = v
    }
    export function buggyTouch(head: Node, other: Node): void {
      requires(validChain(head))
      ensures(validChain(head))
      other.prev = null
    }
  `

  test('pointer surgery establishes the recursive invariant', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'linkFront')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
  })

  test('missing back-pointer write is refuted', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'buggyLink')
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })

  test('frame bridge: disjoint-field writes preserve the invariant', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'touchValue')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved')
  })

  test('frame bridge refuses when a read field is written', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'buggyTouch')
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// F5: ownership via footprint pairing (Repr-lite)
// ---------------------------------------------------------------------------

describe('ownership footprints (F5)', () => {
  const source = `
    interface Node { value: number; next: Node | null; prev: Node | null }
    function validChain(n: Node | null): boolean {
      return n === null ? true : n.next === null ? true : n.next.prev === n && validChain(n.next)
    }
    function inChain(n: Node | null, x: Node): boolean {
      return n === null ? false : n === x || inChain(n.next, x)
    }
    footprint(validChain, inChain)

    export function safeTouch(head: Node, other: Node): void {
      requires(validChain(head))
      requires(!inChain(head, other))
      ensures(validChain(head))
      other.prev = null
    }
    export function unsafeTouch(head: Node, other: Node): void {
      requires(validChain(head))
      ensures(validChain(head))
      other.prev = null
    }
  `

  test('writes outside the declared footprint preserve the invariant', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'safeTouch')
    assert.ok(r)
    assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.join(', ')}`)
  })

  test('without the disjointness hypothesis the bridge cannot fire', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'unsafeTouch')
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// F6: loops over the heap (havoc + invariant)
// ---------------------------------------------------------------------------

describe('heap loops (F6)', () => {
  const source = `
    interface Acc { value: number }
    export function drainSlowly(acc: Acc, n: number): void {
      requires(nonNegative(acc.value))
      requires(nonNegative(n))
      ensures(nonNegative(acc.value))
      while (n > 0) {
        invariant(() => acc.value >= 0)
        decreases(() => n)
        if (acc.value >= 1) {
          acc.value = acc.value - 1
        }
        n = n - 1
      }
    }
    export function drainBuggy(acc: Acc, n: number): void {
      requires(nonNegative(acc.value))
      requires(nonNegative(n))
      ensures(nonNegative(acc.value))
      while (n > 0) {
        invariant(() => acc.value >= 0)
        decreases(() => n)
        acc.value = acc.value - 1
        n = n - 1
      }
    }
    export function spinForever(acc: Acc, n: number): void {
      requires(nonNegative(acc.value))
      requires(nonNegative(n))
      ensures(nonNegative(acc.value))
      while (n > 0) {
        invariant(() => acc.value >= 0)
        decreases(() => n)
        acc.value = acc.value + 1
      }
    }
  `

  test('guarded heap loop: entry, preservation, termination, ensures all prove', async () => {
    const results = await verifyAll(source)
    const mine = results.filter(x => x.fn === 'drainSlowly')
    assert.ok(mine.length >= 4, `Expected ≥4 obligations, got ${mine.length}`)
    for (const r of mine) {
      assert.strictEqual(r.status, 'proved', `${r.text}`)
    }
  })

  test('unguarded decrement fails invariant preservation', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'drainBuggy' && x.text.includes('preserved'))
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })

  test('non-decreasing measure fails termination', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'spinForever' && x.text.includes('decrease'))
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// F7: the LRU flagship — full composition
// ---------------------------------------------------------------------------

describe('LRU flagship (F7): full composition', () => {
  const source = `
    interface Node { value: number; next: Node | null; prev: Node | null }
    function validChain(n: Node | null): boolean {
      return n === null ? true : n.next === null ? true : n.next.prev === n && validChain(n.next)
    }
    function inChain(n: Node | null, x: Node): boolean {
      return n === null ? false : n === x || inChain(n.next, x)
    }
    footprint(validChain, inChain)

    export function moveToFront(head: Node, node: Node, prevN: Node): void {
      requires(head !== node)
      requires(prevN !== node)
      requires(prevN !== head)
      requires(head.prev === null)
      requires(head.next === null)
      requires(prevN.next === node)
      requires(node.prev === prevN)
      requires(node.next === null)
      ensures(node === head || validChain(node))
      if (node === head) return
      prevN.next = node.next
      node.prev = null
      node.next = head
      head.prev = node
    }
    export function buggyMoveToFront(head: Node, node: Node, prevN: Node): void {
      requires(head !== node)
      requires(prevN !== node)
      requires(prevN !== head)
      requires(head.prev === null)
      requires(head.next === null)
      requires(prevN.next === node)
      requires(node.prev === prevN)
      requires(node.next === null)
      ensures(node === head || validChain(node))
      if (node === head) return
      prevN.next = node.next
      node.prev = null
      node.next = head
    }
    export function evictOthers(head: Node, victim: Node, n: number): void {
      requires(validChain(head))
      requires(!inChain(head, victim))
      requires(nonNegative(n))
      ensures(validChain(head))
      while (n > 0) {
        invariant(() => validChain(head))
        decreases(() => n)
        victim.prev = null
        victim.value = 0
        n = n - 1
      }
    }
    export function evictBuggy(head: Node, victim: Node, n: number): void {
      requires(validChain(head))
      requires(nonNegative(n))
      ensures(validChain(head))
      while (n > 0) {
        invariant(() => validChain(head))
        decreases(() => n)
        victim.prev = null
        n = n - 1
      }
    }
  `

  test('moveToFront: early return + pointer unlink + relink preserves the chain', async () => {
    const results = await verifyAll(source)
    for (const r of results.filter(x => x.fn === 'moveToFront')) {
      assert.strictEqual(r.status, 'proved', `${r.text}`)
    }
  })

  test('the classic LRU bug (missing head back-pointer) is refuted', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'buggyMoveToFront' && x.text.includes('validChain'))
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })

  test('recursive invariant survives a heap-mutating LOOP via ownership', async () => {
    const results = await verifyAll(source)
    const mine = results.filter(x => x.fn === 'evictOthers')
    assert.ok(mine.length >= 4, `Expected ≥4 obligations, got ${mine.length}`)
    for (const r of mine) {
      assert.strictEqual(r.status, 'proved', `${r.text}: ${r.labels.slice(-3).join(', ')}`)
    }
  })

  test('without disjointness the loop invariant preservation fails', async () => {
    const results = await verifyAll(source)
    const r = results.find(x => x.fn === 'evictBuggy' && x.text.includes('preserved'))
    assert.ok(r)
    assert.strictEqual(r.status, 'disproved')
  })

  test('performance budget: the whole flagship verifies under 2s', async () => {
    const t0 = Date.now()
    await verifyAll(source)
    const elapsed = Date.now() - t0
    assert.ok(elapsed < 2000, `flagship took ${elapsed}ms (budget 2000ms)`)
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

// ---------------------------------------------------------------------------
// Class methods with loops route through heap mode (this.x as mutable state)
//
// Regression: the SSA path cannot see through while loops — the class
// invariant's exit obligation was checked against the ENTRY state (trivially
// proved), and __old_x = x equations contradicted the post-loop invariants,
// making every ensures vacuously provable. Heap mode havocs loop-written
// state and re-executes the body for preservation, so both bugs are gone.
// ---------------------------------------------------------------------------

describe('class-method loops: heap-mode routing', () => {
  const vault = (loopBody: string, extraInvariant: string) => `
    @invariant((self: Vault) =>
      self.balance >= 0 &&
      self.totalDistributed === self.initialDeposit - self.balance
    )
    class Vault {
      balance: number
      initialDeposit: number
      totalDistributed: number

      constructor(deposit: number) {
        requires(positive(deposit))
        this.balance = deposit
        this.initialDeposit = deposit
        this.totalDistributed = 0
      }

      processBatch(txCount: number, amountPerTx: number): number {
        requires(Number.isInteger(txCount))
        requires(positive(txCount))
        requires(positive(amountPerTx))
        requires(txCount * amountPerTx <= this.balance)
        ensures(this.balance === old(this.balance) - (txCount * amountPerTx))
        ensures(output() === txCount * amountPerTx)

        let remaining = txCount
        let totalSent = 0

        while (remaining > 0) {
          invariant(() => Number.isInteger(remaining))
          invariant(() => remaining >= 0)
          invariant(() => totalSent === (txCount - remaining) * amountPerTx)
          invariant(() => this.balance === old(this.balance) - totalSent)
          ${extraInvariant}
          decreases(() => remaining)
          ${loopBody}
          totalSent += amountPerTx
          remaining--
        }

        return totalSent
      }
    }
  `

  const correctBody = `
    this.balance -= amountPerTx
    this.totalDistributed += amountPerTx
  `
  const distributedInvariant =
    'invariant(() => this.totalDistributed === old(this.totalDistributed) + totalSent)'

  test('complete invariants: everything proves, including the class invariant at exit', async () => {
    const results = await verifyAll(vault(correctBody, distributedInvariant))
    const method = results.filter(r => r.fn === 'processBatch')
    assert.ok(method.length >= 10, `Expected heap-mode task set, got ${method.length}`)
    for (const r of method) {
      assert.strictEqual(r.status, 'proved', `Expected proved for: ${r.text}`)
    }
    const exitInv = method.find(r => r.text.includes('this.totalDistributed === this.initialDeposit'))
    assert.ok(exitInv, 'Expected class-invariant exit obligation')
    // The exit obligation must NOT prove from the entry assumption alone —
    // it needs the post-loop invariants (the old SSA path's trivial proof).
    assert.ok(
      exitInv.labels.some(l => l.includes('post-loop')),
      'Class-invariant exit task must see the post-loop state',
    )
  })

  test('missing loop invariant for a mutated field: class invariant at exit is DISPROVED', async () => {
    const results = await verifyAll(vault(correctBody, ''))
    const exitInv = results.find(
      r => r.fn === 'processBatch' && r.text.includes('this.totalDistributed === this.initialDeposit'),
    )
    assert.ok(exitInv, 'Expected class-invariant exit obligation')
    assert.strictEqual(exitInv.status, 'disproved',
      'totalDistributed is havoced by the loop and unconstrained — must not prove')
  })

  test('vacuity regression: a blatantly false ensures is DISPROVED, not proved', async () => {
    const source = vault(correctBody, distributedInvariant)
      .replace('ensures(output() === txCount * amountPerTx)',
               'ensures(output() === txCount * amountPerTx + 999)')
    const results = await verifyAll(source)
    const bogus = results.find(r => r.fn === 'processBatch' && r.text.includes('999'))
    assert.ok(bogus, 'Expected the false ensures task')
    assert.strictEqual(bogus.status, 'disproved', 'post-loop assumptions must be satisfiable')
  })

  test('buggy loop body: invariant preservation catches the drift', async () => {
    const buggyBody = `
      this.balance -= amountPerTx
      this.totalDistributed += amountPerTx + 1
    `
    const results = await verifyAll(vault(buggyBody, distributedInvariant))
    const preserved = results.find(
      r => r.fn === 'processBatch'
        && r.text.includes('preserved')
        && r.text.includes('this.totalDistributed'),
    )
    assert.ok(preserved, 'Expected preservation task for the totalDistributed invariant')
    assert.strictEqual(preserved.status, 'disproved', 'the +1 drift breaks the invariant')
  })
})
