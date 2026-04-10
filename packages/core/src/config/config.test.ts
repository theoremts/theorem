import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { resolveConfig, DEFAULT_CONFIG } from './index.js'
import type { TheoremConfig } from './index.js'

describe('resolveConfig', () => {
  test('returns defaults when null is passed', () => {
    const result = resolveConfig(null)
    assert.deepEqual(result.include, DEFAULT_CONFIG.include)
    assert.deepEqual(result.exclude, DEFAULT_CONFIG.exclude)
    assert.strictEqual(result.solver.timeout, 10_000)
    assert.strictEqual(result.solver.maxCounterexamples, 3)
    assert.strictEqual(result.solver.minimizeCounterexamples, false)
    assert.strictEqual(result.reporter.format, 'cli')
    assert.strictEqual(result.reporter.showUsedAssumptions, true)
  })

  test('returns defaults when empty object is passed', () => {
    const result = resolveConfig({})
    assert.deepEqual(result.include, ['**/*.ts'])
    assert.deepEqual(result.exclude, ['**/*.d.ts', '**/*.test.ts', '**/*.spec.ts'])
    assert.strictEqual(result.solver.timeout, 10_000)
  })

  test('user values override defaults', () => {
    const config: TheoremConfig = {
      include: ['src/**/*.ts'],
      exclude: ['**/*.test.ts'],
      solver: {
        timeout: 5000,
        maxCounterexamples: 1,
      },
      reporter: {
        format: 'sarif',
      },
    }
    const result = resolveConfig(config)
    assert.deepEqual(result.include, ['src/**/*.ts'])
    assert.deepEqual(result.exclude, ['**/*.test.ts'])
    assert.strictEqual(result.solver.timeout, 5000)
    assert.strictEqual(result.solver.maxCounterexamples, 1)
    // Unset fields keep defaults
    assert.strictEqual(result.solver.minimizeCounterexamples, false)
    assert.strictEqual(result.reporter.format, 'sarif')
    assert.strictEqual(result.reporter.showUsedAssumptions, true)
  })

  test('partial solver overrides keep other defaults', () => {
    const result = resolveConfig({ solver: { timeout: 20_000 } })
    assert.strictEqual(result.solver.timeout, 20_000)
    assert.strictEqual(result.solver.maxCounterexamples, 3)
    assert.strictEqual(result.solver.minimizeCounterexamples, false)
  })

  test('custom skipDirs override defaults', () => {
    const result = resolveConfig({ scan: { skipDirs: ['vendor', 'tmp'] } })
    assert.deepEqual(result.scan.skipDirs, ['vendor', 'tmp'])
  })

  test('custom risks are preserved', () => {
    const risks = { 'division-by-zero': 'critical', 'custom-rule': 'low' }
    const result = resolveConfig({ scan: { risks } })
    assert.deepEqual(result.scan.risks, risks)
  })
})
