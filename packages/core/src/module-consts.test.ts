import { test, describe, before, after } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync, rmSync, mkdirSync } from 'node:fs'
import { join } from 'node:path'
import { tmpdir } from 'node:os'
import { readFileSync } from 'node:fs'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Module-constant resolution — `ZERO` is zero without asking. Trusted const
// initializers (numeric literal, new Decimal(lit), folded arithmetic) become
// assume facts in every referencing function: same-file, relative imports,
// and tsconfig `paths` aliases.
// ---------------------------------------------------------------------------

let dir: string

before(() => {
  dir = mkdtempSync(join(tmpdir(), 'theorem-consts-'))
  mkdirSync(join(dir, 'src', 'utils'), { recursive: true })
  writeFileSync(join(dir, 'tsconfig.json'), JSON.stringify({
    compilerOptions: { baseUrl: '.', paths: { '@/*': ['./src/*'] } },
  }))
  writeFileSync(join(dir, 'src', 'utils', 'consts.ts'), `
    export const ZERO = new Decimal(0);
    export const MS_PER_HOUR = 3_600_000;
    export const MS_PER_DAY = 24 * MS_PER_HOUR;
    export let MUTABLE = 5;
  `)
})

after(() => { rmSync(dir, { recursive: true, force: true }) })

async function verifyFileSource(source: string, fileName: string) {
  const ctx = await getContext()
  const results: Array<{ text: string; status: string }> = []
  for (const ir of extractFromSource(source, fileName)) {
    for (const task of translate(ir, ctx)) {
      results.push({ text: task.contractText, status: (await check(task)).status })
    }
  }
  return results
}

describe('module constants: resolved, not assumed by hand', () => {
  test('same-file const proves through a guard', async () => {
    const source = `
      const LIMIT = 100;
      export function clamp(x: number): number {
        ensures(output() <= 100)
        return x > LIMIT ? LIMIT : x
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'a.ts'))
    assert.strictEqual(results.find(r => r.text.includes('<= 100'))?.status, 'proved')
  })

  test('relative import resolves new Decimal(0)', async () => {
    const source = `
      import { ZERO } from "./utils/consts";
      export function positiveOrZero(x: number): number {
        ensures(output() >= 0)
        return x > ZERO ? x : 0
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'b.ts'))
    assert.strictEqual(results.find(r => r.text.includes('>= 0'))?.status, 'proved')
  })

  test('tsconfig alias import resolves folded arithmetic constants', async () => {
    const source = `
      import { MS_PER_DAY } from "@/utils/consts";
      export function days(ms: number): number {
        requires(ms >= 0)
        ensures(output() >= 0)
        return ms / MS_PER_DAY
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'c.ts'))
    // Both the ensures AND the division-safety obligation need MS_PER_DAY's value
    assert.strictEqual(results.find(r => r.text.includes('>= 0') && !r.text.includes('MS_PER_DAY'))?.status, 'proved')
    const divSafety = results.find(r => r.text.includes('MS_PER_DAY'))
    assert.ok(divSafety, 'Expected the division-safety obligation')
    assert.strictEqual(divSafety.status, 'proved')
  })

  test('a `let` is not a constant — stays free and refutes', async () => {
    const source = `
      import { MUTABLE } from "@/utils/consts";
      export function f(x: number): number {
        ensures(output() === x + 5)
        return x + MUTABLE
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'd.ts'))
    assert.strictEqual(results.find(r => r.text.includes('x + 5'))?.status, 'disproved')
  })

  test('a parameter shadowing the const name wins', async () => {
    const source = `
      const LIMIT = 100;
      export function f(LIMIT: number): number {
        ensures(output() === LIMIT)
        return LIMIT
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'e.ts'))
    assert.strictEqual(results.find(r => r.text.includes('=== LIMIT'))?.status, 'proved')
  })
})

describe('string module constants', () => {
  test('a string const is a fact in bodies and at call sites', async () => {
    const source = `
      const PAID = "paid";
      export function isPaid(status: string): boolean {
        ensures(output() === (status === "paid"))
        return status === PAID
      }
    `
    const results = await verifyFileSource(source, join(dir, 'src', 'f.ts'))
    assert.strictEqual(results.find(r => r.text.includes('status'))?.status, 'proved')
  })
})
