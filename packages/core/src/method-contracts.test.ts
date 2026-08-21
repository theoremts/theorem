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
  declare(Decimal.prototype.sub, (a: number, b: number): number => {
    ensures(output() === a - b)
  })
  declare(Decimal.prototype.equals, (a: number, b: number): boolean => {
    ensures(output() === (a === b))
  })
  declare(Decimal, (a: number): number => {
    ensures(output() === a)
  })
`

async function verifyWithDeclares(source: string) {
  const ctx = await getContext()
  const declares = extractDeclareContracts(DECIMAL_DECLARES, 'decimal.contracts.ts')
  const inlineDeclares = extractDeclareContracts(source, 'input.ts')
  const fns = extractFromSource(source)
  const registry = buildRegistry([...declares, ...inlineDeclares, ...fns])
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

  test('comparison vocabulary covers Decimal parameters without the method bridge', async () => {
    const results = await verifyWithDeclares(`
      export function convertRateToShare(ratePercent: Decimal): Decimal {
        requires(gte(ratePercent, 0))
        ensures(gte(output(), 0) && lt(output(), 100))
        return ratePercent.div(ratePercent.add(100)).mul(100)
      }
    `)
    assert.strictEqual(results.find(r => r.text.includes('output() >= 0'))?.status, 'proved')
    assert.strictEqual(results.find(r => r.text.includes('!== 0'))?.status, 'proved')
  })

  test('nullable-tolerant helpers: defined narrows, nonNegative implies presence', async () => {
    const results = await verifyWithDeclares(`
      export function pay(minutes: number | null): number {
        requires(nonNegative(minutes))
        ensures(output() >= 0)
        return minutes === null ? 0 : minutes * 2
      }
      export function guard(x: number | null): number {
        requires(defined(x) && x >= 1)
        ensures(output() >= 1)
        return x === null ? 0 : x
      }
      export function tooStrong(x: number | null): number {
        requires(nonNegative(x))
        ensures(output() >= 1)
        return x === null ? 0 : x
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'pay')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'guard')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'tooStrong')?.status, 'disproved')
  })

  test('Map-dedup idiom grants uniqueBy — the constructor obligation proves', async () => {
    const results = await verifyWithDeclares(`
      declare(FeeCalculator, (ruleSet: FeeRule[], _item: unknown): number => {
        requires(uniqueBy(ruleSet, (m) => m.key));
        return 0;
      });
      export function calc(rules: FeeRule[], cost: Decimal): number {
        requires(cost.greaterThanOrEqualTo(0))
        const deduped = [...new Map(rules.map((m) => [m.key, m])).values()]
        const c = new FeeCalculator(deduped, { baseCost: cost })
        return c
      }
    `)
    const obligation = results.find(r => r.text.includes('uniqueBy'))
    assert.ok(obligation, `Expected the constructor obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(obligation.status, 'proved')
  })

  test('without the dedup the constructor obligation is refuted', async () => {
    const results = await verifyWithDeclares(`
      declare(FeeCalculator, (ruleSet: FeeRule[], _item: unknown): number => {
        requires(uniqueBy(ruleSet, (m) => m.key));
        return 0;
      });
      export function calc(rules: FeeRule[], cost: Decimal): number {
        requires(cost.greaterThanOrEqualTo(0))
        const c = new FeeCalculator(rules, { baseCost: cost })
        return c
      }
    `)
    const obligation = results.find(r => r.text.includes('uniqueBy'))
    assert.ok(obligation, 'Expected the constructor obligation')
    assert.notStrictEqual(obligation.status, 'proved')
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

describe('call sites: module consts and method-call early-exit guards', () => {
  const LTE_DECLARE = `
    declare(Decimal.prototype.lte, (a: number, b: number): boolean => {
      ensures(output() === (a <= b))
    })
  `

  async function checkCallSitesWithDeclares(source: string) {
    const ctx = await getContext()
    const { extractCallSiteObligations } = await import('./verifier/call-sites.js')
    const declares = extractDeclareContracts(LTE_DECLARE, 'decimal.contracts.ts')
    const registry = buildRegistry([...declares, ...extractFromSource(source)])
    const results = []
    for (const task of extractCallSiteObligations(source, 'test.ts', registry, ctx)) {
      results.push({ text: task.contractText, status: (await check(task)).status, labels: task.assumptionLabels })
    }
    return results
  }

  test('a Decimal method early-exit guard discharges the callee requires', async () => {
    const results = await checkCallSitesWithDeclares(`
      function scale(amount: Decimal): Decimal {
        requires(!(amount.lte(0)))
        return amount
      }
      export function caller(value: Decimal): Decimal {
        if (value.lte(0)) return value
        return scale(value)
      }
    `)
    const target = results.find(r => r.text.includes('lte'))
    assert.ok(target, `Expected the guard obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      `early-return guard must inline and prove (assumptions: ${target.labels.join(', ')})`)
  })

  test('module constants are facts at call sites', async () => {
    const results = await checkCallSitesWithDeclares(`
      const MIN_QTY = 10;
      function order(qty: number): number {
        requires(qty >= 10)
        return qty
      }
      export function good(): number { return order(MIN_QTY) }
      export function bad(): number { return order(MIN_QTY - 5) }
    `)
    assert.strictEqual(results.length, 2, `Expected 2 obligations, got: ${results.map(r => r.text).join('; ')}`)
    const good = results.find(r => r.text.includes('order(MIN_QTY)'))
    const bad = results.find(r => r.text.includes('MIN_QTY - 5'))
    assert.strictEqual(good?.status, 'proved', 'MIN_QTY === 10 discharges qty >= 10')
    assert.strictEqual(bad?.status, 'disproved', 'MIN_QTY - 5 === 5 violates qty >= 10')
  })
})

describe('method contracts: object-literal returns keep body equations', () => {
  test('an alias of a method-computed local proves the tautological ensures', async () => {
    // The classic false positive: `second` IS `first`, but an untranslatable
    // initializer used to drop BOTH prop equations, leaving two free vars.
    const results = await verifyWithDeclares(`
      export function delta(a: Decimal, b: Decimal) {
        ensures(output().locked === true);
        ensures(output().second.equals(output().first));
        const first: Decimal = a.sub(b);
        const second: Decimal = first;
        return { locked: true, first, second };
      }
    `)
    const target = results.find(r => r.text.includes('second'))
    assert.ok(target, `Expected the equality ensures, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved', 'second === first by construction')
  })

  test('the method-computed prop value itself is provable', async () => {
    const results = await verifyWithDeclares(`
      export function delta(a: Decimal, b: Decimal) {
        ensures(output().first.equals(a.sub(b)));
        const first: Decimal = a.sub(b);
        return { locked: true, first };
      }
    `)
    const target = results.find(r => r.text.includes('first'))
    assert.ok(target, 'Expected the value ensures')
    assert.strictEqual(target.status, 'proved', 'result.first === a - b must flow through the inlined sub')
  })

  test('a genuinely wrong prop equality is still refuted', async () => {
    const results = await verifyWithDeclares(`
      export function delta(a: Decimal, b: Decimal) {
        ensures(output().second.equals(output().first.add(1)));
        const first: Decimal = a.sub(b);
        const second: Decimal = first;
        return { locked: true, first, second };
      }
    `)
    const target = results.find(r => r.text.includes('add(1)'))
    assert.ok(target, 'Expected the wrong ensures')
    assert.strictEqual(target.status, 'disproved', 'second !== first + 1 — must not become vacuous')
  })
})

describe('object-literal returns: modular calls in props', () => {
  test('aliased props built from a multi-ensures registered call stay equal', async () => {
    // The profit-locked shape: props computed through a registered function
    // (conditional ensures — goes through __ret, not inlining) plus an alias.
    // Memoized rewrites must give both props the SAME __ret.
    const results = await verifyWithDeclares(`
      function orZero(value: Decimal | undefined | null): Decimal {
        ensures(value != null || output().equals(0));
        ensures(value == null || output().equals(value));
        return value ? value : ZERO;
      }
      export function delta(view: View) {
        ensures(output().locked === true);
        ensures(output().second.equals(output().first));
        const prev: Decimal = orZero(view.previous?.cost || view.original);
        const next: Decimal = orZero(view.current?.cost);
        const first: Decimal = next.sub(prev);
        const second: Decimal = first;
        return { locked: true, first, second };
      }
    `)
    const target = results.find(r => r.fn === 'delta' && r.text.includes('second'))
    assert.ok(target, `Expected the equality ensures, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved',
      'second === first by construction — even with untranslatable optional-chain args')
  })
})
