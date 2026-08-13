import { test, describe } from 'node:test'
import assert from 'node:assert/strict'
import { extractFromSource } from './parser/index.js'
import { translate } from './translator/index.js'
import { getContext, check } from './solver/index.js'
import { parsePrismaSchema, generateTheoremSchemas } from './prisma/index.js'

async function verifyAll(source: string, fileName = 'input.ts') {
  const ctx = await getContext()
  const results: Array<{ fn: string; text: string; status: string; informational: boolean }> = []
  for (const ir of extractFromSource(source, fileName)) {
    for (const task of translate(ir, ctx)) {
      const result = await check(task)
      results.push({
        fn: ir.name ?? '?',
        text: task.contractText,
        status: result.status,
        informational: task.informational === true,
      })
    }
  }
  return results
}

// ---------------------------------------------------------------------------
// .brand() + .int()
// ---------------------------------------------------------------------------

describe('zod .brand() and .int()', () => {
  test('branded chains still extract constraints; int() feeds Z3', async () => {
    const results = await verifyAll(`
      declare const z: any
      const S = z.object({
        id: z.string().brand<'OrderId'>(),
        quantity: z.number().int().min(1).brand<'Qty'>(),
      })
      export function step(input: unknown): number {
        const o = S.parse(input)
        return 100 / (o.quantity - 0.5)
      }
    `)
    const div = results.find(r => r.fn === 'step' && r.text.includes('safe division'))
    assert.ok(div, 'Expected division obligation despite .brand() in chains')
    assert.strictEqual(div.status, 'proved', 'integer >= 1 minus 0.5 is never zero')
  })
})

// ---------------------------------------------------------------------------
// Path-sensitive safety + dead error branches
// ---------------------------------------------------------------------------

describe('path-sensitive safety obligations', () => {
  test('early-return guard protects the division', async () => {
    const results = await verifyAll(`
      export function guarded(a: number, b: number): number {
        requires(nonNegative(a))
        if (b === 0) return 0
        return a / b
      }
    `)
    const div = results.find(r => r.text.includes('safe division'))
    assert.ok(div)
    assert.strictEqual(div.status, 'proved', 'the b === 0 branch exits before the division')
  })
})

describe('dead error branches (Effect.fail)', () => {
  const source = `
    import { Effect, Schema } from 'effect'
    const AmountSchema = Schema.Struct({ value: Schema.Number.pipe(Schema.positive()) })

    export function deadBranch(amount: unknown, divisor: number) {
      const a = Schema.decodeUnknownSync(AmountSchema)(amount)
      if (a.value <= 0) return Effect.fail('impossible')
      return Effect.succeed(divisor / a.value)
    }

    export function liveBranch(a: number, b: number) {
      requires(nonNegative(a))
      if (b === 0) return Effect.fail('div by zero')
      return Effect.succeed(a / b)
    }
  `

  test('schema-contradicted fail branch is proved unreachable', async () => {
    const results = await verifyAll(source)
    const dead = results.find(r => r.fn === 'deadBranch' && r.text.includes('unreachable error branch'))
    assert.ok(dead, `Expected unreachable-branch task, got: ${results.map(r => r.text).join('; ')}`)
    assert.strictEqual(dead.status, 'proved')
    assert.strictEqual(dead.informational, true)
  })

  test('reachable fail branch is informational-disproved (not a failure)', async () => {
    const results = await verifyAll(source)
    const live = results.find(r => r.fn === 'liveBranch' && r.text.includes('unreachable error branch'))
    assert.ok(live)
    assert.strictEqual(live.status, 'disproved')
    assert.strictEqual(live.informational, true, 'must be informational so the CLI hides it')
  })
})

// ---------------------------------------------------------------------------
// tRPC .input(Schema)
// ---------------------------------------------------------------------------

describe('tRPC input schemas', () => {
  const source = `
    import { z } from 'zod'
    declare const t: any
    const OrderInput = z.object({
      total: z.number().positive(),
      quantity: z.number().int().min(1),
    }).refine(o => o.total >= o.quantity)

    export const router = t.router({
      unitPrice: t.procedure.input(OrderInput).query(({ input }) => {
        return input.total / input.quantity
      }),
      buggyAdjust: t.procedure.input(OrderInput).mutation(({ input: order }) => {
        return order.total / (order.quantity - 1)
      }),
    })
  `

  test('resolver named from router key; schema guards the division', async () => {
    const results = await verifyAll(source)
    const ok = results.find(r => r.fn === 'unitPrice' && r.text.includes('safe division'))
    assert.ok(ok, `Expected unitPrice obligation, got: ${results.map(r => `${r.fn}: ${r.text}`).join('; ')}`)
    assert.strictEqual(ok.status, 'proved')
  })

  test('renamed destructuring ({ input: order }) works; bug found', async () => {
    const results = await verifyAll(source)
    const bad = results.find(r => r.fn === 'buggyAdjust' && r.text.includes('safe division'))
    assert.ok(bad)
    assert.strictEqual(bad.status, 'disproved')
  })
})

// ---------------------------------------------------------------------------
// Prisma generator
// ---------------------------------------------------------------------------

describe('prisma generator', () => {
  const prismaSource = `
    enum Status { ACTIVE INACTIVE }

    model User {
      id      String  @id
      age     Int
      balance Decimal
      bio     String?
      status  Status
      posts   Post[]
    }

    model Post {
      id     String @id
      userId String
      user   User   @relation(fields: [userId], references: [id])
    }
  `

  test('parses models, enums, skips relations and lists', () => {
    const schema = parsePrismaSchema(prismaSource)
    assert.strictEqual(schema.models.length, 2)
    assert.strictEqual(schema.enums.length, 1)
    const user = schema.models.find(m => m.name === 'User')!
    assert.ok(user.fields.some(f => f.name === 'age' && f.type === 'Int'))
    assert.ok(user.fields.some(f => f.name === 'bio' && f.optional))
  })

  test('generated schema carries Int facts into proofs', async () => {
    const generated = generateTheoremSchemas(parsePrismaSchema(prismaSource))
    assert.ok(generated.includes('age: z.number().int()'), 'Int must map to .int()')
    assert.ok(generated.includes('bio: z.string().nullable()'), 'optional must map to .nullable()')
    assert.ok(!generated.includes('posts:'), 'relations/lists must be skipped')
    assert.ok(!/user:/.test(generated), 'model relations must be skipped')

    // End-to-end: inline the generated schema and prove via the Int fact
    const results = await verifyAll(`
      declare const z: any
      ${generated.split('\n').filter(l => !l.startsWith('//') && !l.startsWith('declare')).join('\n')}
      export function step(input: unknown): number {
        const u = UserRowSchema.parse(input)
        return 100 / (u.age - 0.5)
      }
    `)
    const div = results.find(r => r.fn === 'step' && r.text.includes('safe division'))
    assert.ok(div, 'Expected division obligation from generated schema')
    assert.strictEqual(div.status, 'proved', 'integer age minus 0.5 is never zero')
  })
})
