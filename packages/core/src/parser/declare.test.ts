import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractDeclareContracts } from './extractor.js'
import type { FunctionIR, RequiresContract, EnsuresContract, Expr } from './ir.js'

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function requiresContracts(ir: FunctionIR): RequiresContract[] {
  return ir.contracts.filter((c): c is RequiresContract => c.kind === 'requires')
}

function ensuresContracts(ir: FunctionIR): EnsuresContract[] {
  return ir.contracts.filter((c): c is EnsuresContract => c.kind === 'ensures')
}

// ---------------------------------------------------------------------------
// declare() extraction
// ---------------------------------------------------------------------------

describe('extractDeclareContracts', () => {
  test('extracts declare(Math.sqrt, ...) with requires and ensures', () => {
    const source = `
      declare(Math.sqrt, (x: number): number => {
        requires(x >= 0)
        ensures(nonNegative(output()))
      })
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 1)
    const ir = results[0]!
    assert.strictEqual(ir.name, 'Math.sqrt')
    assert.strictEqual(ir.params.length, 1)
    assert.strictEqual(ir.params[0]!.name, 'x')
    assert.strictEqual(ir.params[0]!.sort, 'real')
    assert.strictEqual(ir.returnSort, 'real')
    assert.strictEqual(requiresContracts(ir).length, 1)
    assert.strictEqual(ensuresContracts(ir).length, 1)
    assert.strictEqual(ir.body, undefined)
  })

  test('extracts declare with only ensures', () => {
    const source = `
      declare(Math.abs, (x: number): number => {
        ensures(nonNegative(output()))
      })
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 1)
    const ir = results[0]!
    assert.strictEqual(ir.name, 'Math.abs')
    assert.strictEqual(requiresContracts(ir).length, 0)
    assert.strictEqual(ensuresContracts(ir).length, 1)
  })

  test('extracts declare with simple identifier target', () => {
    const source = `
      declare(getBalance, (userId: string): number => {
        ensures(nonNegative(output()))
      })
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 1)
    const ir = results[0]!
    assert.strictEqual(ir.name, 'getBalance')
    assert.strictEqual(ir.params.length, 1)
    assert.strictEqual(ir.params[0]!.name, 'userId')
    assert.strictEqual(ir.params[0]!.sort, 'string')
  })

  test('extracts multiple declare() calls from one file', () => {
    const source = `
      declare(Math.sqrt, (x: number): number => {
        requires(x >= 0)
        ensures(nonNegative(output()))
      })

      declare(Math.abs, (x: number): number => {
        ensures(nonNegative(output()))
      })
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 2)
    assert.strictEqual(results[0]!.name, 'Math.sqrt')
    assert.strictEqual(results[1]!.name, 'Math.abs')
  })

  test('skips declare calls with no contracts in body', () => {
    const source = `
      declare(foo, (x: number): number => {
        return x
      })
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 0)
  })

  test('skips declare calls with non-arrow second argument', () => {
    const source = `
      declare(Math.sqrt, someVar)
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 0)
  })

  test('skips declare calls with fewer than 2 arguments', () => {
    const source = `
      declare(Math.sqrt)
    `
    const results = extractDeclareContracts(source)
    assert.strictEqual(results.length, 0)
  })

  test('requires predicate is parsed as an Expr', () => {
    const source = `
      declare(Math.sqrt, (x: number): number => {
        requires(x >= 0)
      })
    `
    const results = extractDeclareContracts(source)
    const req = requiresContracts(results[0]!)[0]!
    // The predicate should be parsed as a binary expression
    assert.ok(typeof req.predicate !== 'string')
    const pred = req.predicate as Expr
    assert.strictEqual(pred.kind, 'binary')
  })

  test('declare contracts can be registered via buildRegistry', async () => {
    // Integration: ensure the IRs from extractDeclareContracts work with buildRegistry
    const { buildRegistry } = await import('../registry/index.js')
    const source = `
      declare(Math.sqrt, (x: number): number => {
        requires(x >= 0)
        ensures(nonNegative(output()))
      })
    `
    const irs = extractDeclareContracts(source)
    const registry = buildRegistry(irs)
    assert.ok(registry.has('Math.sqrt'))
    const contract = registry.get('Math.sqrt')!
    assert.strictEqual(contract.name, 'Math.sqrt')
    assert.strictEqual(contract.requires.length, 1)
    assert.strictEqual(contract.ensures.length, 1)
  })
})
