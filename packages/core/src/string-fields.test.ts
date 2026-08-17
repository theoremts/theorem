import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { buildRegistry } from './registry/index.js'
import { extractCallSiteObligations } from './verifier/call-sites.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// String-valued fields in quantified facts — `m.appliesTo === "baseCost"`
// inside a forall over a ref-array routes through an Int→String field view
// (__sfield_) instead of sort-mismatching against the Real field heap.
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

describe('string fields: inside function bodies', () => {
  test('quantified string fact instantiates at a literal index', async () => {
    const source = `
      interface FeeRule { appliesTo: string; rate: number }
      export function firstBase(rules: FeeRule[]): number {
        requires(rules.length >= 1)
        requires(forall(rules, (m) => m.appliesTo === "baseCost"))
        check(rules[0]!.appliesTo === "baseCost")
        return 0
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('appliesTo'))
    assert.ok(target, `Expected the check obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })

  test('a disjunctive string domain does NOT prove a specific member', async () => {
    const source = `
      interface FeeRule { appliesTo: string }
      export function firstBase(rules: FeeRule[]): number {
        requires(rules.length >= 1)
        requires(forall(rules, (m) => m.appliesTo === "baseCost" || m.appliesTo === "totalCost"))
        check(rules[0]!.appliesTo === "baseCost")
        return 0
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('appliesTo'))
    assert.ok(target, `Expected the check obligation, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'disproved', 'could be totalCost — must not prove')
  })

  test('plain string param comparison still proves', async () => {
    const source = `
      export function isPaid(status: string): boolean {
        requires(status === "paid")
        ensures(output() === true)
        return status === "paid"
      }
    `
    const results = await verifySource(source)
    const target = results.find(r => r.text.includes('true'))
    assert.ok(target, `Expected the ensures task, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(target.status, 'proved')
  })
})

describe('string fields: call sites', () => {
  const calleeSource = `
    interface FeeRule { appliesTo: string; rate: number }
    export function applyRules(rules: FeeRule[]): void {
      requires(forall(rules, (m) => m.appliesTo === "baseCost" || m.appliesTo === "totalCost"))
    }
  `

  test('object-literal string props discharge the quantified requires', async () => {
    const ctx = await getContext()
    const source = calleeSource + `
      export function caller(): void {
        let rules: FeeRule[] = [
          { appliesTo: "baseCost", rate: 10 },
          { appliesTo: "totalCost", rate: 20 },
        ]
        applyRules(rules)
      }
    `
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const target = tasks.find(t => t.contractText.includes('appliesTo'))
    assert.ok(target, 'Expected the forall obligation — silent drops are the enemy')
    assert.strictEqual((await check(target)).status, 'proved')
  })

  test('a value outside the string domain is disproved', async () => {
    const ctx = await getContext()
    const source = calleeSource + `
      export function caller(): void {
        let rules: FeeRule[] = [
          { appliesTo: "baseCost", rate: 10 },
          { appliesTo: "laborCost", rate: 20 },
        ]
        applyRules(rules)
      }
    `
    const registry = buildRegistry(extractFromSource(source))
    const tasks = extractCallSiteObligations(source, 'test.ts', registry, ctx)
    const target = tasks.find(t => t.contractText.includes('appliesTo'))
    assert.ok(target, 'Expected the forall obligation')
    assert.strictEqual((await check(target)).status, 'disproved', 'laborCost is not in the domain')
  })
})
