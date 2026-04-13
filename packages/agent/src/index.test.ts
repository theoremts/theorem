import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { verify, createVerifier, formatFeedback, audit } from './index.js'

describe('theoremts-agent', () => {
  it('proves a correct function', async () => {
    const result = await verify(`
      import { requires, ensures, output } from 'theoremts'

      function abs(x: number) {
        ensures(output() >= 0)
        return x >= 0 ? x : -x
      }
    `)

    assert.equal(result.proved, true)
    assert.equal(result.failedCount, 0)
    assert.ok(result.provedCount > 0)
  })

  it('finds a counterexample for an incorrect function', async () => {
    const result = await verify(`
      import { requires, ensures, output } from 'theoremts'

      function badAbs(x: number) {
        ensures(output() >= 0)
        return x
      }
    `)

    assert.equal(result.proved, false)
    assert.ok(result.failedCount > 0)
    assert.ok(result.failures.length > 0)
    assert.ok(result.failures[0]!.counterexample !== undefined)
  })

  it('formats feedback for AI agents', async () => {
    const result = await verify(`
      import { requires, ensures, output } from 'theoremts'

      function divide(a: number, b: number) {
        requires(b !== 0)
        ensures(output() === a / b)
        return a + b
      }
    `)

    assert.equal(result.proved, false)
    const feedback = formatFeedback(result)
    assert.ok(feedback.includes('divide'))
    assert.ok(feedback.includes('fails when'))
  })

  it('works with createVerifier for multiple calls', async () => {
    const verifier = createVerifier({ timeout: 5000 })

    const r1 = await verifier.verify(`
      import { ensures, output } from 'theoremts'

      function positive() {
        ensures(output() > 0)
        return 42
      }
    `)
    assert.equal(r1.proved, true)

    const r2 = await verifier.verify(`
      import { ensures, output } from 'theoremts'

      function alwaysOne(x: number) {
        ensures(output() === 1)
        return x
      }
    `)
    assert.equal(r2.proved, false)
  })

  it('proves all contracts pass → proved: true', async () => {
    const result = await verify(`
      import { requires, ensures, output, positive } from 'theoremts'

      function safeDivide(a: number, b: number) {
        requires(b !== 0)
        ensures(output() === a / b)
        return a / b
      }
    `)

    assert.equal(result.proved, true)
    assert.equal(result.failures.length, 0)
  })

  it('verifyMultiple verifies multiple files together', async () => {
    const verifier = createVerifier()

    const result = await verifier.verifyMultiple([
      {
        source: `
          import { ensures, output } from 'theoremts'

          function double(x: number) {
            ensures(output() === x * 2)
            return x * 2
          }
        `,
        fileName: 'a.ts',
      },
      {
        source: `
          import { ensures, output } from 'theoremts'

          function triple(x: number) {
            ensures(output() === x * 3)
            return x * 3
          }
        `,
        fileName: 'b.ts',
      },
    ])

    assert.equal(result.proved, true)
    assert.equal(result.provedCount, 2)
  })

  it('formatFeedback returns success message when proved', async () => {
    const result = await verify(`
      import { ensures, output } from 'theoremts'

      function one() {
        ensures(output() === 1)
        return 1
      }
    `)

    assert.equal(formatFeedback(result), 'All contracts proved.')
  })
})

describe('audit', () => {
  it('detects risks and infers contracts from unannotated code', async () => {
    const result = await audit(`
      function divide(a: number, b: number) {
        if (b === 0) throw new Error('division by zero')
        return a / b
      }
    `)

    // Should have inferred contracts from guard
    assert.ok(result.inferredContracts.length > 0)
    const divideContracts = result.inferredContracts.find(f => f.name === 'divide')
    assert.ok(divideContracts)
    assert.ok(divideContracts.contracts.some(c => c.kind === 'requires'))

    // Summary should be non-empty
    assert.ok(result.summary.length > 0)
  })

  it('returns empty results for safe code', async () => {
    const result = await audit(`
      function add(a: number, b: number) {
        return a + b
      }
    `)

    // No risks for simple addition
    assert.equal(result.risks.length, 0)
    assert.ok(result.summary.includes('No risks'))
  })

  it('detects division by zero risk in unannotated code', async () => {
    const result = await audit(`
      function unsafe(a: number, b: number) {
        return a / b
      }
    `)

    // Should detect division-by-zero risk
    assert.ok(result.risks.some(r => r.kind === 'division-by-zero'))
  })
})
