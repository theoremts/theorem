import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Body shapes that used to drop silently and refute true properties with
// free results: try/catch, arr.filter(f).length, arr.map(f).length, find().
// ---------------------------------------------------------------------------

async function verifyAll(source: string) {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string }> = []
  for (const ir of extractFromSource(source)) {
    for (const task of translate(ir, ctx)) {
      results.push({ fn: ir.name ?? '?', text: task.contractText, status: (await check(task)).status })
    }
  }
  return results
}

describe('try/catch bodies', () => {
  test('both completions reachable — branch-structure ensures prove', async () => {
    const results = await verifyAll(`
      export function safeInc(x: number): number {
        requires(x >= 0)
        ensures(output() >= 0)
        try {
          return x + 1
        } catch {
          return 0
        }
      }
      export function catchCanViolate(x: number): number {
        requires(x >= 0)
        ensures(output() >= 1)
        try {
          return x + 1
        } catch {
          return 0
        }
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'safeInc')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'catchCanViolate')?.status, 'disproved',
      'the catch branch returns 0 — must stay reachable')
  })
})

describe('filter/map lengths', () => {
  test('filter length is bounded by the base length', async () => {
    const results = await verifyAll(`
      export function countBig(xs: number[]): number {
        ensures(output() >= 0)
        return xs.filter((v) => v > 10).length
      }
      export function boundedAbove(xs: number[]): number {
        ensures(output() <= xs.length)
        return xs.filter((v) => v > 10).length
      }
      export function strictBoundWrong(xs: number[]): number {
        ensures(output() < xs.length)
        return xs.filter((v) => v > 10).length
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'countBig')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'boundedAbove')?.status, 'proved')
    assert.strictEqual(results.find(r => r.fn === 'strictBoundWrong')?.status, 'disproved',
      'filter can keep everything — strict bound must refute')
  })

  test('map preserves length exactly', async () => {
    const results = await verifyAll(`
      export function doubledCount(xs: number[]): number {
        ensures(output() === xs.length)
        return xs.map((v) => v * 2).length
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'doubledCount')?.status, 'proved')
  })
})

describe('find() symbolic elements', () => {
  test('quantified element facts apply to the found value', async () => {
    const results = await verifyAll(`
      export function findPositive(xs: number[], t: number): number {
        requires(forall(xs, (v) => v >= 0))
        ensures(output() >= -1)
        const hit = xs.find((v) => v > t)
        return hit === undefined ? -1 : hit
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'findPositive')?.status, 'proved')
  })

  test('without the element facts the found value is honestly free', async () => {
    const results = await verifyAll(`
      export function findAny(xs: number[], t: number): number {
        ensures(output() >= -1)
        const hit = xs.find((v) => v > t)
        return hit === undefined ? -1 : hit
      }
    `)
    assert.strictEqual(results.find(r => r.fn === 'findAny')?.status, 'disproved',
      'no forall fact — the element can be anything')
  })
})
