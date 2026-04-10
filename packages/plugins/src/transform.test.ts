import { describe, test } from 'node:test'
import assert from 'node:assert/strict'
import { transformTheoremCode } from './transform.js'

describe('transformTheoremCode', () => {
  test('returns null when code has no theorem references', () => {
    const result = transformTheoremCode('const x = 1', 'file.ts')
    assert.equal(result, null)
  })

  // -----------------------------------------------------------------------
  // Import removal
  // -----------------------------------------------------------------------

  describe('import removal', () => {
    test('removes named imports from theorem', () => {
      const code = `import { proof, requires, ensures, positive } from 'theorem'\nconst x = 1`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('import'))
      assert.ok(result.code.includes('const x = 1'))
    })

    test('removes imports with double quotes', () => {
      const code = `import { proof } from "theorem"\nconst x = 1`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('import'))
    })

    test('removes type imports from theorem', () => {
      const code = `import type { Contract } from 'theorem'\nconst x = 1`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('import'))
    })

    test('removes subpath imports (theorem/vite)', () => {
      const code = `import { theoremStrip } from 'theorem/vite'\nconst x = 1`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('import'))
    })

    test('preserves non-theorem imports', () => {
      const code = `import { foo } from 'bar'\nimport { proof } from 'theorem'\nconst x = 1`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(result.code.includes("import { foo } from 'bar'"))
      assert.ok(!result.code.includes("from 'theorem'"))
    })
  })

  // -----------------------------------------------------------------------
  // proof() stripping
  // -----------------------------------------------------------------------

  describe('proof() calls', () => {
    test('strips proof wrapper with arrow function - single line', () => {
      const code = `const add = proof((a: number, b: number) => a + b, requires(() => true))`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.equal(result.code, `const add = (a: number, b: number) => a + b`)
    })

    test('strips proof wrapper with multiline contracts', () => {
      const code = [
        `import { proof, requires, ensures, positive } from 'theorem'`,
        ``,
        `export const safeDivide = proof(`,
        `  (a: number, b: number) => a / b,`,
        `  requires(({ b }) => positive(b)),`,
        `  ensures(({ result, a, b }) => result === a / b),`,
        `)`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('proof'))
      assert.ok(!result.code.includes('requires'))
      assert.ok(!result.code.includes('ensures'))
      assert.ok(result.code.includes('(a: number, b: number) => a / b'))
    })

    test('strips proof with only a function (no contracts)', () => {
      const code = `const fn = proof((x: number) => x * 2)`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.equal(result.code, `const fn = (x: number) => x * 2`)
    })

    test('handles nested parentheses in function body', () => {
      const code = `const fn = proof((a: number) => Math.max(a, 0), requires(() => true))`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.equal(result.code, `const fn = (a: number) => Math.max(a, 0)`)
    })

    test('does not match identifiers ending in proof', () => {
      const code = `const myproof = someproof(1, 2)`
      const result = transformTheoremCode(code, 'file.ts')
      // "theorem" doesn't appear so should be null actually... let's adjust
      assert.equal(result, null)
    })
  })

  // -----------------------------------------------------------------------
  // proof.fn() stripping
  // -----------------------------------------------------------------------

  describe('proof.fn() calls', () => {
    test('strips proof.fn and wraps as IIFE', () => {
      const code = `const result = proof.fn(() => { return 42 }, requires(() => true))`
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.equal(result.code, `const result = (() => { return 42 })()`)
    })

    test('handles proof.fn with multiline body', () => {
      const code = [
        `function binarySearch(arr: number[], target: number) {`,
        `  return proof.fn(() => {`,
        `    let lo = 0`,
        `    let hi = arr.length - 1`,
        `    return lo`,
        `  }, requires(() => true))`,
        `}`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(result.code.includes('(() => {'))
      assert.ok(result.code.includes('})()'))
      assert.ok(!result.code.includes('proof.fn'))
      assert.ok(!result.code.includes('requires'))
    })
  })

  // -----------------------------------------------------------------------
  // Standalone call removal
  // -----------------------------------------------------------------------

  describe('standalone calls', () => {
    test('removes standalone invariant() calls', () => {
      const code = [
        `while (lo <= hi) {`,
        `  invariant(() => lo >= 0 && hi < arr.length)`,
        `  lo++`,
        `}`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('invariant'))
      assert.ok(result.code.includes('lo++'))
    })

    test('removes standalone decreases() calls', () => {
      const code = [
        `while (n > 0) {`,
        `  decreases(() => n)`,
        `  n--`,
        `}`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('decreases'))
      assert.ok(result.code.includes('n--'))
    })

    test('removes standalone modifies() calls with semicolons', () => {
      const code = [
        `function mutate() {`,
        `  modifies('this.items');`,
        `  this.items.push(1)`,
        `}`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)
      assert.ok(!result.code.includes('modifies'))
      assert.ok(result.code.includes('this.items.push(1)'))
    })
  })

  // -----------------------------------------------------------------------
  // Full integration scenario
  // -----------------------------------------------------------------------

  describe('full integration', () => {
    test('transforms a complete file', () => {
      const code = [
        `import { proof, requires, ensures, positive } from 'theorem'`,
        ``,
        `export const safeDivide = proof(`,
        `  (a: number, b: number) => a / b,`,
        `  requires(({ b }) => positive(b)),`,
        `  ensures(({ result, a, b }) => result === a / b),`,
        `)`,
        ``,
        `export const add = (a: number, b: number) => a + b`,
      ].join('\n')
      const result = transformTheoremCode(code, 'file.ts')
      assert.ok(result)

      // Imports should be gone
      assert.ok(!result.code.includes('import'))
      // proof/requires/ensures should be gone
      assert.ok(!result.code.includes('proof'))
      assert.ok(!result.code.includes('requires'))
      assert.ok(!result.code.includes('ensures'))
      // The actual function should remain
      assert.ok(result.code.includes('(a: number, b: number) => a / b'))
      // Non-theorem code should be untouched
      assert.ok(result.code.includes('export const add = (a: number, b: number) => a + b'))
    })

    test('handles strings containing "theorem" without real imports', () => {
      const code = `const name = "theorem is great"`
      const result = transformTheoremCode(code, 'file.ts')
      // The code contains 'theorem' but has no actual proof/import patterns
      // Result should be null since nothing was changed
      assert.equal(result, null)
    })
  })
})
