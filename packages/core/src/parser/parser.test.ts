import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './extractor.js'
import type { FunctionIR, RequiresContract, EnsuresContract, ModifiesContract, Expr } from './ir.js'

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function getFirst(source: string): FunctionIR {
  const results = extractFromSource(source)
  assert.ok(results.length > 0, 'Expected at least one FunctionIR')
  return results[0] as FunctionIR
}

function requiresContracts(ir: FunctionIR): RequiresContract[] {
  return ir.contracts.filter((c): c is RequiresContract => c.kind === 'requires')
}

function ensuresContracts(ir: FunctionIR): EnsuresContract[] {
  return ir.contracts.filter((c): c is EnsuresContract => c.kind === 'ensures')
}

// ---------------------------------------------------------------------------
// Name inference
// ---------------------------------------------------------------------------

describe('name inference', () => {
  test('infers function name from const name = proof(...)', () => {
    const source = `
      const applyDiscount = proof(
        (price: number, discount: number) => price - discount,
        requires(({ price }) => price > 0),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.name, 'applyDiscount')
  })

  test('name is undefined when not assigned to a variable', () => {
    const source = `
      proof(
        (x: number) => x,
        requires(({ x }) => x > 0),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.name, undefined)
  })
})

// ---------------------------------------------------------------------------
// TypeScript type → sort mapping
// ---------------------------------------------------------------------------

describe('TypeScript type → sort mapping', () => {
  test('number maps to real', () => {
    const source = `
      const fn = proof(
        (x: number) => x,
        ensures(({ result }) => result > 0),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.params[0]?.sort, 'real')
  })

  test('boolean maps to bool', () => {
    const source = `
      const fn = proof(
        (flag: boolean) => flag,
        ensures(({ result }) => result),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.params[0]?.sort, 'bool')
  })

  test('bigint maps to int', () => {
    const source = `
      const fn = proof(
        (n: bigint) => n,
        ensures(({ result }) => result > 0n),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.params[0]?.sort, 'int')
  })

  test('unknown maps to unknown', () => {
    const source = `
      const fn = proof(
        (x: unknown) => x,
        ensures(() => true),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.params[0]?.sort, 'unknown')
  })

  test('untyped param defaults to real', () => {
    const source = `
      const fn = proof(
        (x) => x,
        ensures(() => true),
      )
    `
    const ir = getFirst(source)
    assert.strictEqual(ir.params[0]?.sort, 'real')
  })
})

// ---------------------------------------------------------------------------
// requires extraction
// ---------------------------------------------------------------------------

describe('requires extraction', () => {
  test('extracts requires contract with kind requires', () => {
    const source = `
      const fn = proof(
        (price: number) => price,
        requires(({ price }) => price > 0),
      )
    `
    const ir = getFirst(source)
    const reqs = requiresContracts(ir)
    assert.strictEqual(reqs.length, 1)
    assert.strictEqual(reqs[0]?.kind, 'requires')
  })

  test('requires predicate is an Expr IR (not a string)', () => {
    const source = `
      const fn = proof(
        (price: number) => price,
        requires(({ price }) => price > 0),
      )
    `
    const ir = getFirst(source)
    const req = requiresContracts(ir)[0]
    assert.ok(req !== undefined)
    assert.ok(typeof req.predicate !== 'string', 'Expected an Expr, not a string')
  })

  test('requires predicate has correct binary op structure', () => {
    const source = `
      const fn = proof(
        (price: number) => price,
        requires(({ price }) => price > 0),
      )
    `
    const ir = getFirst(source)
    const req = requiresContracts(ir)[0]
    assert.ok(req !== undefined)
    const pred = req.predicate as Expr
    assert.strictEqual(pred.kind, 'binary')
    assert.ok(pred.kind === 'binary')
    assert.strictEqual(pred.op, '>')
  })
})

// ---------------------------------------------------------------------------
// ensures extraction
// ---------------------------------------------------------------------------

describe('ensures extraction', () => {
  test('extracts ensures contract with kind ensures', () => {
    const source = `
      const fn = proof(
        (price: number) => price * 2,
        ensures(({ result }) => result > 0),
      )
    `
    const ir = getFirst(source)
    const ens = ensuresContracts(ir)
    assert.strictEqual(ens.length, 1)
    assert.strictEqual(ens[0]?.kind, 'ensures')
  })

  test('ensures predicate is an Expr IR', () => {
    const source = `
      const fn = proof(
        (price: number) => price * 2,
        ensures(({ result }) => result > 0),
      )
    `
    const ir = getFirst(source)
    const ens = ensuresContracts(ir)[0]
    assert.ok(ens !== undefined)
    assert.ok(typeof ens.predicate !== 'string', 'Expected an Expr, not a string')
  })

  test('ensures predicate has correct structure for result > 0', () => {
    const source = `
      const fn = proof(
        (x: number) => x,
        ensures(({ result }) => result > 0),
      )
    `
    const ir = getFirst(source)
    const ens = ensuresContracts(ir)[0]
    assert.ok(ens !== undefined)
    const pred = ens.predicate as Expr
    assert.strictEqual(pred.kind, 'binary')
    assert.ok(pred.kind === 'binary')
    assert.strictEqual(pred.op, '>')
    assert.deepEqual(pred.right, { kind: 'literal', value: 0 })
  })
})

// ---------------------------------------------------------------------------
// Expression body
// ---------------------------------------------------------------------------

describe('expression body extraction', () => {
  test('single-expression arrow function body is extracted', () => {
    const source = `
      const fn = proof(
        (price: number, discount: number) => price - discount,
        ensures(({ result }) => result >= 0),
      )
    `
    const ir = getFirst(source)
    assert.ok(ir.body !== undefined, 'Expected body to be extracted')
    assert.strictEqual(ir.body?.kind, 'binary')
  })

  test('block-body arrow function parses body from return statement', () => {
    const source = `
      const fn = proof(
        (price: number) => { return price * 2 },
        ensures(({ result }) => result > 0),
      )
    `
    const ir = getFirst(source)
    assert.deepStrictEqual(ir.body, {
      kind: 'binary', op: '*',
      left: { kind: 'ident', name: 'price' },
      right: { kind: 'literal', value: 2 },
    })
  })
})

// ---------------------------------------------------------------------------
// String contracts
// ---------------------------------------------------------------------------

describe('string contracts', () => {
  test('string requires is preserved as a string predicate', () => {
    const source = `
      const fn = proof(
        (x: number) => x,
        requires('price must be positive'),
      )
    `
    const ir = getFirst(source)
    const req = requiresContracts(ir)[0]
    assert.ok(req !== undefined)
    assert.strictEqual(req.predicate, 'price must be positive')
  })

  test('string ensures is preserved as a string predicate', () => {
    const source = `
      const fn = proof(
        (x: number) => x,
        ensures('result is valid'),
      )
    `
    const ir = getFirst(source)
    const ens = ensuresContracts(ir)[0]
    assert.ok(ens !== undefined)
    assert.strictEqual(ens.predicate, 'result is valid')
  })
})

// ---------------------------------------------------------------------------
// Member access predicates
// ---------------------------------------------------------------------------

describe('member access predicates', () => {
  test('from.balance >= amount produces correct Expr IR', () => {
    const source = `
      const transfer = proof(
        (from: unknown, amount: number) => from,
        requires(({ from, amount }) => from.balance >= amount),
      )
    `
    const ir = getFirst(source)
    const req = requiresContracts(ir)[0]
    assert.ok(req !== undefined)
    const pred = req.predicate as Expr
    // from.balance >= amount  →  binary(>=, member(ident(from), balance), ident(amount))
    assert.strictEqual(pred.kind, 'binary')
    assert.ok(pred.kind === 'binary')
    assert.strictEqual(pred.op, '>=')
    assert.strictEqual(pred.left.kind, 'member')
    assert.ok(pred.left.kind === 'member')
    assert.deepEqual(pred.left.object, { kind: 'ident', name: 'from' })
    assert.strictEqual(pred.left.property, 'balance')
    assert.deepEqual(pred.right, { kind: 'ident', name: 'amount' })
  })
})

// ---------------------------------------------------------------------------
// modifies contract
// ---------------------------------------------------------------------------

describe('modifies contract', () => {
  test('extracts refs array from modifies contract', () => {
    const source = `
      const fn = proof(
        (account: unknown) => account,
        modifies('balance', 'total'),
      )
    `
    const ir = getFirst(source)
    const mod = ir.contracts.find((c): c is ModifiesContract => c.kind === 'modifies')
    assert.ok(mod !== undefined)
    assert.deepEqual(mod.refs, ['balance', 'total'])
  })

  test('modifies with single ref', () => {
    const source = `
      const fn = proof(
        (account: unknown) => account,
        modifies('count'),
      )
    `
    const ir = getFirst(source)
    const mod = ir.contracts.find((c): c is ModifiesContract => c.kind === 'modifies')
    assert.ok(mod !== undefined)
    assert.deepEqual(mod.refs, ['count'])
  })
})

// ---------------------------------------------------------------------------
// Multiple proof() calls
// ---------------------------------------------------------------------------

describe('multiple proof() calls in one file', () => {
  test('returns one FunctionIR per proof() call', () => {
    const source = `
      const add = proof(
        (a: number, b: number) => a + b,
        ensures(({ result }) => result >= 0),
      )

      const subtract = proof(
        (a: number, b: number) => a - b,
        ensures(({ result }) => result <= 0),
      )
    `
    const results = extractFromSource(source)
    assert.strictEqual(results.length, 2)
  })

  test('each FunctionIR has the correct name', () => {
    const source = `
      const alpha = proof(
        (x: number) => x,
        ensures(({ result }) => result > 0),
      )

      const beta = proof(
        (y: number) => y,
        ensures(({ result }) => result > 0),
      )
    `
    const results = extractFromSource(source)
    assert.strictEqual(results[0]?.name, 'alpha')
    assert.strictEqual(results[1]?.name, 'beta')
  })

  test('each FunctionIR contains its own contracts', () => {
    const source = `
      const fn1 = proof(
        (x: number) => x,
        requires(({ x }) => x > 0),
      )

      const fn2 = proof(
        (y: number) => y * 2,
        ensures(({ result }) => result > 0),
      )
    `
    const results = extractFromSource(source)
    assert.strictEqual(requiresContracts(results[0] as FunctionIR).length, 1)
    assert.strictEqual(ensuresContracts(results[1] as FunctionIR).length, 1)
  })
})

// ---------------------------------------------------------------------------
// proof() with fewer than 2 args — should not produce an IR
// ---------------------------------------------------------------------------

describe('non-matching proof() calls', () => {
  test('proof() with only one arg (no contracts) is ignored', () => {
    const source = `
      const fn = proof((x: number) => x)
    `
    const results = extractFromSource(source)
    assert.strictEqual(results.length, 0)
  })
})
