import { describe, it } from 'node:test'
import assert from 'node:assert/strict'
import { inferContracts } from './index.js'

describe('extractZodContracts', () => {
  it('inline parse with positive() extracts > 0', async () => {
    const result = await inferContracts(
      `function process(input: unknown) {
        const data = z.object({ amount: z.number().positive() }).parse(input)
        return data.amount * 2
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.amount > 0'),
      `expected 'data.amount > 0', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('schema variable + parse with min/max', async () => {
    const result = await inferContracts(
      `const schema = z.object({ age: z.number().min(18).max(120) })
      function validate(input: unknown) {
        const data = schema.parse(input)
        return data.age
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.age >= 18'),
      `expected 'data.age >= 18', got: ${contracts.map(c => c.text)}`,
    )
    assert.ok(
      contracts.some(c => c.text === 'data.age <= 120'),
      `expected 'data.age <= 120', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('nonnegative() extracts >= 0', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ count: z.number().nonnegative() }).parse(input)
        return data.count
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.count >= 0'),
      `expected 'data.count >= 0', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('negative() extracts < 0', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ offset: z.number().negative() }).parse(input)
        return data.offset
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.offset < 0'),
      `expected 'data.offset < 0', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('string min/max extracts length constraints', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ name: z.string().min(1).max(100) }).parse(input)
        return data.name
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.name.length >= 1'),
      `expected 'data.name.length >= 1', got: ${contracts.map(c => c.text)}`,
    )
    assert.ok(
      contracts.some(c => c.text === 'data.name.length <= 100'),
      `expected 'data.name.length <= 100', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('array nonempty() extracts length > 0', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ items: z.array(z.string()).nonempty() }).parse(input)
        return data.items
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.items.length > 0'),
      `expected 'data.items.length > 0', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('multiple fields in one schema', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ price: z.number().positive(), qty: z.number().min(1) }).parse(input)
        return data.price * data.qty
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    assert.ok(
      contracts.some(c => c.text === 'data.price > 0'),
      `expected 'data.price > 0', got: ${contracts.map(c => c.text)}`,
    )
    assert.ok(
      contracts.some(c => c.text === 'data.qty >= 1'),
      `expected 'data.qty >= 1', got: ${contracts.map(c => c.text)}`,
    )
  })

  it('safeParse is skipped (does not throw)', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const result = z.object({ amount: z.number().positive() }).safeParse(input)
        if (!result.success) return null
        return result.data
      }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    const zodContracts = contracts.filter(c => c.source?.includes('Zod'))
    assert.equal(
      zodContracts.length,
      0,
      `expected no Zod contracts for safeParse, got: ${zodContracts.map(c => c.text)}`,
    )
  })

  it('no Zod patterns produces no Zod contracts', async () => {
    const result = await inferContracts(
      `function add(a: number, b: number) { return a + b }`,
      'test.ts',
    )
    const contracts = result.functions[0]?.contracts ?? []
    const zodContracts = contracts.filter(c => c.source?.includes('Zod'))
    assert.equal(
      zodContracts.length,
      0,
      `expected no Zod contracts, got: ${zodContracts.map(c => c.text)}`,
    )
  })

  it('contracts have guard confidence', async () => {
    const result = await inferContracts(
      `function f(input: unknown) {
        const data = z.object({ x: z.number().positive() }).parse(input)
        return data.x
      }`,
      'test.ts',
    )
    const zodContracts = (result.functions[0]?.contracts ?? []).filter(c => c.source?.includes('Zod'))
    for (const c of zodContracts) {
      assert.equal(c.confidence, 'guard', `expected guard confidence, got: ${c.confidence}`)
      assert.equal(c.kind, 'requires', `expected requires kind, got: ${c.kind}`)
    }
  })
})
