import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import {
  proof,
  of,
  requires,
  ensures,
  invariant,
  decreases,
  modifies,
  old,
  forall,
  exists,
  positive,
  nonNegative,
  negative,
  finite,
  between,
  sorted,
  unique,
  conserved,
  defineConfig,
} from './index.js'

// ---------------------------------------------------------------------------
// proof()
// ---------------------------------------------------------------------------

describe('proof(fn, contracts)', () => {
  test('returns fn unchanged when contracts are provided', () => {
    const add = (a: number, b: number) => a + b
    const wrapped = proof(add, requires(() => true))
    assert.strictEqual(wrapped, add)
  })

  test('returned function still works correctly', () => {
    const double = (x: number) => x * 2
    const wrapped = proof(double, requires(() => true))
    assert.strictEqual(wrapped(5), 10)
  })

  test('returns fn unchanged with multiple contracts', () => {
    const fn = (x: number) => x
    const wrapped = proof(
      fn,
      requires(() => true),
      ensures(() => true),
    )
    assert.strictEqual(wrapped, fn)
  })
})

describe('proof(fn) with no contracts', () => {
  test('returns undefined when no contracts are passed', () => {
    const fn = (x: number) => x
    // No contracts — second overload (attach mode), returns void
    const result = proof(fn)
    assert.strictEqual(result, undefined)
  })
})

describe('proof(target, contracts) — attach mode', () => {
  test('returns undefined (no-op)', () => {
    const fn = (x: number) => x
    const result = proof(fn, requires(() => true))
    // attach overload returns void but the fn-overload returns fn —
    // because fn is a function and first contract isContract, it returns fn
    assert.strictEqual(result, fn)
  })

  test('non-function target returns undefined', () => {
    const obj = { method: 'doSomething' }
    const result = proof(obj, requires(() => true))
    assert.strictEqual(result, undefined)
  })
})

describe('proof(reducer, action, contracts) — reducer mode', () => {
  test('action is not a contract, returns undefined', () => {
    const reducer = (state: number) => state
    const action = { type: 'INCREMENT' }
    const result = proof(reducer, action, requires(() => true))
    assert.strictEqual(result, undefined)
  })
})

describe('proof.fn(body, contracts)', () => {
  test('calls body and returns its result', () => {
    const result = proof.fn(() => 42, requires(() => true))
    assert.strictEqual(result, 42)
  })

  test('calls body with no contracts', () => {
    const result = proof.fn(() => 'hello')
    assert.strictEqual(result, 'hello')
  })

  test('side effects in body are executed', () => {
    let called = false
    proof.fn(() => { called = true; return undefined }, ensures(() => true))
    assert.ok(called)
  })
})

// ---------------------------------------------------------------------------
// of()
// ---------------------------------------------------------------------------

describe('of(Class) proxy', () => {
  test('property access returns the property name as a string', () => {
    class MyService {
      transfer(_amount: number): void {}
    }
    const proxy = of(MyService)
    assert.strictEqual((proxy as unknown as Record<string, unknown>)['transfer'], 'transfer')
  })

  test('accessing arbitrary property returns its name', () => {
    class Foo {
      bar = 0
      baz(): void {}
    }
    const proxy = of(Foo)
    const p = proxy as unknown as Record<string, unknown>
    assert.strictEqual(p['bar'], 'bar')
    assert.strictEqual(p['baz'], 'baz')
  })
})

// ---------------------------------------------------------------------------
// requires / ensures / invariant / decreases / modifies
// ---------------------------------------------------------------------------

describe('requires', () => {
  test('returns contract with __type: requires (arrow function form)', () => {
    const contract = requires(({ x }: { x: number }) => x > 0) as any
    assert.strictEqual(contract.__type, 'requires')
  })

  test('returns contract with __type: requires (string form)', () => {
    const contract = requires('price must be positive') as any
    assert.strictEqual(contract.__type, 'requires')
  })

  test('is usable as a decorator (returns function)', () => {
    const contract = requires(({ x }: { x: number }) => x > 0) as any
    assert.strictEqual(typeof contract, 'function')
  })
})

describe('ensures', () => {
  test('returns contract with __type: ensures (arrow function form)', () => {
    const contract = ensures(({ result }: { result: number }) => result > 0) as any
    assert.strictEqual(contract.__type, 'ensures')
  })

  test('returns contract with __type: ensures (string form)', () => {
    const contract = ensures('result is positive') as any
    assert.strictEqual(contract.__type, 'ensures')
  })

  test('is usable as a decorator (returns function)', () => {
    const contract = ensures(({ result }: { result: number }) => result > 0) as any
    assert.strictEqual(typeof contract, 'function')
  })
})

describe('invariant', () => {
  test('returns object with __type: invariant (arrow function form)', () => {
    const contract = invariant(() => true)
    assert.deepEqual(contract, { __type: 'invariant' })
  })

  test('returns object with __type: invariant (string form)', () => {
    const contract = invariant('state is valid')
    assert.deepEqual(contract, { __type: 'invariant' })
  })
})

describe('decreases', () => {
  test('returns object with __type: decreases', () => {
    const contract = decreases(() => 10)
    assert.deepEqual(contract, { __type: 'decreases' })
  })
})

describe('modifies', () => {
  test('returns object with __type: modifies and refs array', () => {
    const contract = modifies('balance', 'total')
    assert.deepEqual(contract, { __type: 'modifies', refs: ['balance', 'total'] })
  })

  test('returns empty refs array when no args', () => {
    const contract = modifies()
    assert.deepEqual(contract, { __type: 'modifies', refs: [] })
  })

  test('returns single ref', () => {
    const contract = modifies('count')
    assert.deepEqual(contract, { __type: 'modifies', refs: ['count'] })
  })
})

// ---------------------------------------------------------------------------
// old()
// ---------------------------------------------------------------------------

describe('old(x)', () => {
  test('returns the value unchanged for a number', () => {
    assert.strictEqual(old(42), 42)
  })

  test('returns the value unchanged for an object (same reference)', () => {
    const obj = { balance: 100 }
    assert.strictEqual(old(obj), obj)
  })

  test('returns the value unchanged for a string', () => {
    assert.strictEqual(old('hello'), 'hello')
  })
})

// ---------------------------------------------------------------------------
// forall / exists
// ---------------------------------------------------------------------------

describe('forall', () => {
  test('returns true when all elements satisfy predicate', () => {
    assert.ok(forall([1, 2, 3], (x) => x > 0))
  })

  test('returns false when some element fails predicate', () => {
    assert.ok(!forall([1, -1, 3], (x) => x > 0))
  })

  test('returns true for empty array', () => {
    assert.ok(forall([], () => false))
  })

  test('passes index to predicate', () => {
    const indices: number[] = []
    forall([10, 20, 30], (_x, i) => { indices.push(i); return true })
    assert.deepEqual(indices, [0, 1, 2])
  })
})

describe('exists', () => {
  test('returns true when at least one element satisfies predicate', () => {
    assert.ok(exists([1, -1, 3], (x) => x < 0))
  })

  test('returns false when no element satisfies predicate', () => {
    assert.ok(!exists([1, 2, 3], (x) => x < 0))
  })

  test('returns false for empty array', () => {
    assert.ok(!exists([], () => true))
  })

  test('passes index to predicate', () => {
    const indices: number[] = []
    exists([10, 20, 30], (_x, i) => { indices.push(i); return false })
    assert.deepEqual(indices, [0, 1, 2])
  })
})

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

describe('positive', () => {
  test('returns true for positive number', () => {
    assert.ok(positive(1))
  })

  test('returns false for zero', () => {
    assert.ok(!positive(0))
  })

  test('returns false for negative number', () => {
    assert.ok(!positive(-1))
  })
})

describe('nonNegative', () => {
  test('returns true for zero', () => {
    assert.ok(nonNegative(0))
  })

  test('returns true for positive number', () => {
    assert.ok(nonNegative(5))
  })

  test('returns false for negative number', () => {
    assert.ok(!nonNegative(-1))
  })
})

describe('negative', () => {
  test('returns true for negative number', () => {
    assert.ok(negative(-1))
  })

  test('returns false for zero', () => {
    assert.ok(!negative(0))
  })

  test('returns false for positive number', () => {
    assert.ok(!negative(1))
  })
})

describe('finite', () => {
  test('returns true for a regular number', () => {
    assert.ok(finite(42))
  })

  test('returns false for Infinity', () => {
    assert.ok(!finite(Infinity))
  })

  test('returns false for -Infinity', () => {
    assert.ok(!finite(-Infinity))
  })

  test('returns false for NaN', () => {
    assert.ok(!finite(NaN))
  })
})

describe('between', () => {
  test('returns true when value is within bounds (inclusive)', () => {
    assert.ok(between(5, 0, 10))
  })

  test('returns true when value equals min', () => {
    assert.ok(between(0, 0, 10))
  })

  test('returns true when value equals max', () => {
    assert.ok(between(10, 0, 10))
  })

  test('returns false when value is below min', () => {
    assert.ok(!between(-1, 0, 10))
  })

  test('returns false when value is above max', () => {
    assert.ok(!between(11, 0, 10))
  })
})

describe('sorted', () => {
  test('returns true for sorted array', () => {
    assert.ok(sorted([1, 2, 3, 4]))
  })

  test('returns true for array with equal elements', () => {
    assert.ok(sorted([2, 2, 2]))
  })

  test('returns true for single element array', () => {
    assert.ok(sorted([5]))
  })

  test('returns true for empty array', () => {
    assert.ok(sorted([]))
  })

  test('returns false for unsorted array', () => {
    assert.ok(!sorted([3, 1, 2]))
  })
})

describe('unique', () => {
  test('returns true for array with unique values', () => {
    assert.ok(unique([1, 2, 3]))
  })

  test('returns false for array with duplicate values', () => {
    assert.ok(!unique([1, 2, 1]))
  })

  test('returns true for empty array', () => {
    assert.ok(unique([]))
  })

  test('uses key function when provided', () => {
    const items = [{ id: 1 }, { id: 2 }, { id: 1 }]
    assert.ok(!unique(items, (item) => item.id))
  })

  test('returns true when key function produces all unique values', () => {
    const items = [{ id: 1 }, { id: 2 }, { id: 3 }]
    assert.ok(unique(items, (item) => item.id))
  })
})

describe('conserved', () => {
  test('always returns true at runtime', () => {
    assert.ok(conserved(100, 200, 300))
  })

  test('returns true with no arguments', () => {
    assert.ok(conserved())
  })

  test('returns true with single argument', () => {
    assert.ok(conserved(42))
  })
})

// ---------------------------------------------------------------------------
// defineConfig
// ---------------------------------------------------------------------------

describe('defineConfig', () => {
  test('returns the config object unchanged', () => {
    const config = {
      include: ['src/**/*.ts'],
      exclude: ['**/*.test.ts'],
      solver: { timeout: 5000 },
    }
    const result = defineConfig(config)
    assert.strictEqual(result, config)
  })

  test('returns empty config unchanged', () => {
    const config = {}
    const result = defineConfig(config)
    assert.strictEqual(result, config)
  })

  test('returns full config unchanged', () => {
    const config = {
      include: ['src/**/*.ts'],
      exclude: ['**/*.test.ts', '**/*.spec.ts'],
      solver: {
        timeout: 10000,
        maxCounterexamples: 3,
        minimizeCounterexamples: false,
      },
      scan: {
        skipDirs: ['node_modules', 'dist'],
        risks: { 'division-by-zero': 'critical' },
      },
      reporter: {
        format: 'cli' as const,
        showUsedAssumptions: true,
      },
    }
    const result = defineConfig(config)
    assert.strictEqual(result, config)
  })
})
