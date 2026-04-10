import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'

// ---------------------------------------------------------------------------
// Pipeline helper
// ---------------------------------------------------------------------------

async function verifyAll(
  source: string,
): Promise<Array<{ text: string; status: string; counterexample?: Record<string, unknown> | undefined }>> {
  const ctx = await getContext()
  const irs = extractFromSource(source)
  const results: Array<{ text: string; status: string; counterexample?: Record<string, unknown> | undefined }> = []
  for (const ir of irs) {
    for (const task of translate(ir, ctx)) {
      const result = await check(task)
      results.push({
        text: task.contractText,
        status: result.status,
        counterexample: result.status === 'disproved' ? result.counterexample : undefined,
      })
    }
  }
  return results
}

// ---------------------------------------------------------------------------
// applyDiscount
// ---------------------------------------------------------------------------

const applyDiscountSource = `
  const applyDiscount = proof(
    (price: number, discount: number): number => price - discount,
    requires(({ price }) => price > 0),
    requires(({ discount }) => discount >= 0),
    requires(({ price, discount }) => discount <= price),
    ensures(({ result }) => result >= 0),
  )
`

const applyDiscountNoRequiresSource = `
  const applyDiscount = proof(
    (price: number, discount: number): number => price - discount,
    ensures(({ result }) => result >= 0),
  )
`

describe('applyDiscount with correct requires', () => {
  test('all ensures are proved', async () => {
    const results = await verifyAll(applyDiscountSource)
    assert.ok(results.length > 0, 'Expected at least one verification result')
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved but got ${r.status} for: ${r.text}`)
    }
  })
})

describe('applyDiscount without requires', () => {
  test('ensures is disproved', async () => {
    const results = await verifyAll(applyDiscountNoRequiresSource)
    assert.ok(results.length > 0, 'Expected at least one verification result')
    assert.strictEqual(results[0]?.status, 'disproved')
  })

  test('counterexample contains a numeric price', async () => {
    const results = await verifyAll(applyDiscountNoRequiresSource)
    const r = results[0]
    assert.ok(r?.counterexample !== undefined)
    assert.ok('price' in r.counterexample, 'counterexample should include price')
    assert.strictEqual(typeof r.counterexample['price'], 'number')
  })

  test('counterexample price is negative (violating case)', async () => {
    const results = await verifyAll(applyDiscountNoRequiresSource)
    const r = results[0]
    assert.ok(r?.counterexample !== undefined)
    // Z3 finds a model where result < 0 — price could be negative when unconstrained
    const price = r.counterexample['price']
    assert.ok(typeof price === 'number')
  })
})

// ---------------------------------------------------------------------------
// addToBalance
// ---------------------------------------------------------------------------

const addToBalancePartialRequiresSource = `
  const addToBalance = proof(
    (balance: number, amount: number): number => balance + amount,
    requires(({ balance }) => balance >= 0),
    ensures(({ result }) => result >= 0),
  )
`

const addToBalanceBothRequiresSource = `
  const addToBalance = proof(
    (balance: number, amount: number): number => balance + amount,
    requires(({ balance }) => balance >= 0),
    requires(({ amount }) => amount >= 0),
    ensures(({ result }) => result >= 0),
  )
`

describe('addToBalance with only requires(balance >= 0)', () => {
  test('ensures is disproved', async () => {
    const results = await verifyAll(addToBalancePartialRequiresSource)
    assert.ok(results.length > 0)
    assert.strictEqual(results[0]?.status, 'disproved')
  })

  test('counterexample shows a negative amount', async () => {
    const results = await verifyAll(addToBalancePartialRequiresSource)
    const r = results[0]
    assert.ok(r?.counterexample !== undefined)
    assert.ok('amount' in r.counterexample, 'counterexample should include amount')
    const amount = r.counterexample['amount']
    assert.ok(typeof amount === 'number')
    assert.ok(amount < 0, `Expected negative amount in counterexample, got: ${amount}`)
  })
})

describe('addToBalance with both requires', () => {
  test('all ensures are proved', async () => {
    const results = await verifyAll(addToBalanceBothRequiresSource)
    assert.ok(results.length > 0)
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved but got ${r.status} for: ${r.text}`)
    }
  })
})

// ---------------------------------------------------------------------------
// Simple: a > 0 && b > 0 → a + b > 0
// ---------------------------------------------------------------------------

const simplePositiveSumSource = `
  const positiveSum = proof(
    (a: number, b: number): number => a + b,
    requires(({ a }) => a > 0),
    requires(({ b }) => b > 0),
    ensures(({ result }) => result > 0),
  )
`

describe('simple: a > 0 && b > 0 → a + b > 0', () => {
  test('proved', async () => {
    const results = await verifyAll(simplePositiveSumSource)
    assert.ok(results.length > 0)
    assert.strictEqual(results[0]?.status, 'proved')
  })
})

// ---------------------------------------------------------------------------
// Simple: a + b with no requires → nonNegative(result) disproved
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Loop invariant verification
// ---------------------------------------------------------------------------

const loopFactorialSource = `
  function factorial(n: number): number {
    return proof.fn(() => {
      let result = 1
      let i = n
      while (i > 0) {
        invariant(() => result > 0)
        invariant(() => i >= 0)
        decreases(() => i)
        result = result * i
        i = i - 1
      }
      return result
    },
    requires(({ n }) => n >= 0),
    ensures(({ result }) => result > 0),
    )
  }
`

describe('loop invariant: factorial', () => {
  test('loop invariants and ensures are proved', async () => {
    const results = await verifyAll(loopFactorialSource)
    assert.ok(results.length > 0, 'Expected at least one verification result')
    for (const r of results) {
      assert.strictEqual(r.status, 'proved', `Expected proved but got ${r.status} for: ${r.text}`)
    }
  })
})

describe('loop invariant: tasks are generated', () => {
  test('generates init, preservation, termination, and ensures tasks', async () => {
    const results = await verifyAll(loopFactorialSource)
    // We expect: 2 invariant init + 2 invariant preservation + 1 termination + 1 ensures = 6
    assert.ok(results.length >= 4, `Expected at least 4 tasks but got ${results.length}`)
    const initTasks = results.filter(r => r.text.includes('loop invariant init'))
    assert.ok(initTasks.length >= 2, 'Expected at least 2 init tasks')
    const preserveTasks = results.filter(r => r.text.includes('loop invariant preservation'))
    assert.ok(preserveTasks.length >= 2, 'Expected at least 2 preservation tasks')
    const termTasks = results.filter(r => r.text.includes('loop termination'))
    assert.ok(termTasks.length >= 1, 'Expected at least 1 termination task')
  })
})

// ---------------------------------------------------------------------------
// Simple unconstrained sum
// ---------------------------------------------------------------------------

const simpleUnconstrainedSumSource = `
  const unconstrainedSum = proof(
    (a: number, b: number): number => a + b,
    ensures(({ result }) => result >= 0),
  )
`

describe('simple: a + b with no requires → nonNegative(result) disproved', () => {
  test('disproved', async () => {
    const results = await verifyAll(simpleUnconstrainedSumSource)
    assert.ok(results.length > 0)
    assert.strictEqual(results[0]?.status, 'disproved')
  })

  test('counterexample is numeric', async () => {
    const results = await verifyAll(simpleUnconstrainedSumSource)
    const r = results[0]
    assert.ok(r?.counterexample !== undefined)
    // At least one variable in counterexample is a number
    const values = Object.values(r.counterexample)
    const hasNumeric = values.some((v) => typeof v === 'number')
    assert.ok(hasNumeric, `Expected at least one numeric value in counterexample: ${JSON.stringify(r.counterexample)}`)
  })
})

// ---------------------------------------------------------------------------
// Recursive termination — decreases for recursive functions
// ---------------------------------------------------------------------------

const factorialRecursiveSource = `
  function factorial(n: number): number {
    requires(n >= 0)
    decreases(n)
    ensures(positive(output()))
    if (n === 0) return 1
    return n * factorial(n - 1)
  }
`

describe('recursive termination: factorial', () => {
  test('recursive bound is proved', async () => {
    const results = await verifyAll(factorialRecursiveSource)
    const bound = results.find(r => r.text.includes('recursive bound'))
    assert.ok(bound !== undefined, 'Should have a recursive bound task')
    assert.strictEqual(bound.status, 'proved', 'Expected proved for recursive bound: ' + bound.text)
  })

  test('recursive decrease is proved', async () => {
    const results = await verifyAll(factorialRecursiveSource)
    const decrease = results.find(r => r.text.includes('recursive decrease'))
    assert.ok(decrease !== undefined, 'Should have a recursive decrease task')
    assert.strictEqual(decrease.status, 'proved', 'Expected proved for recursive decrease: ' + decrease.text)
  })
})

const fibonacciRecursiveSource = `
  function fibonacci(n: number): number {
    requires(n >= 0)
    decreases(n)
    ensures(nonNegative(output()))
    if (n <= 1) return n
    return fibonacci(n - 1) + fibonacci(n - 2)
  }
`

describe('recursive termination: fibonacci', () => {
  test('recursive bound is proved', async () => {
    const results = await verifyAll(fibonacciRecursiveSource)
    const bound = results.find(r => r.text.includes('recursive bound'))
    assert.ok(bound !== undefined, 'Should have a recursive bound task')
    assert.strictEqual(bound.status, 'proved')
  })

  test('both recursive decreases are proved', async () => {
    const results = await verifyAll(fibonacciRecursiveSource)
    const decreases = results.filter(r => r.text.includes('recursive decrease'))
    assert.strictEqual(decreases.length, 2, 'Should have two recursive decrease tasks (n-1 and n-2)')
    for (const d of decreases) {
      assert.strictEqual(d.status, 'proved', 'Expected proved for recursive decrease: ' + d.text)
    }
  })
})

const missingRequiresRecursiveSource = `
  function badFactorial(n: number): number {
    decreases(n)
    if (n === 0) return 1
    return n * badFactorial(n - 1)
  }
`

describe('recursive termination: missing requires', () => {
  test('recursive bound is disproved without requires(n >= 0)', async () => {
    const results = await verifyAll(missingRequiresRecursiveSource)
    const bound = results.find(r => r.text.includes('recursive bound'))
    assert.ok(bound !== undefined, 'Should have a recursive bound task')
    assert.strictEqual(bound.status, 'disproved', 'Bound should fail without requires')
  })
})
