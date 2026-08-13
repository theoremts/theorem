// Effect Schema as out-of-the-box contracts — full parity with the Zod
// integration, in Effect idioms:
//
//   theorem verify examples/effect-demo.ts
//
// decodeUnknownSync throws on invalid input (same guard semantics as Zod's
// parse), Struct field refinements become assumptions, filter() cross-field
// predicates are model invariants, and `typeof S.Type` aliases put producer
// functions under proof obligation. Schema.int() even gives Z3 the integer
// constraint TypeScript's `number` can't express.

import { requires, positive } from 'theoremts'

declare const Schema: any

const OrderSchema = Schema.Struct({
  total: Schema.Number.pipe(Schema.positive()),
  quantity: Schema.Number.pipe(Schema.int(), Schema.greaterThanOrEqualTo(1)),
  discount: Schema.Number.pipe(Schema.between(0, 0.5)),
}).pipe(Schema.filter((o: any) => o.total >= o.discount))

type Order = typeof OrderSchema.Type

// ── PROVED: schema constraints guard the arithmetic ──────────────────────────

export function unitPrice(input: unknown): number {
  const order = Schema.decodeUnknownSync(OrderSchema)(input)
  // quantity >= 1 ⇒ division safe
  return order.total / order.quantity
}

export function makeOrder(total: number): Order {
  requires(positive(total))
  // filter invariant (total >= discount) proved: discount is 0
  return { total, quantity: 1, discount: 0 }
}

// ── DISPROVED ────────────────────────────────────────────────────────────────

export function buggyAdjustment(input: unknown): number {
  const order = Schema.decodeUnknownSync(OrderSchema)(input)
  // BUG: quantity === 1 is schema-valid → division by zero.
  return order.total / (order.quantity - 1)
}

export function buggyOrder(total: number): Order {
  requires(positive(total))
  // BUG: discount exceeds total — violates the filter invariant.
  return { total, quantity: 1, discount: total + 1 }
}

// ── DEAD ERROR BRANCH: the schema makes this Effect.fail unreachable ─────────
// Effect's types force you to handle the error; Theorem proves the handler
// is dead code. Reported as "✓ unreachable error branch" — reachable fail
// branches are normal and stay silent.

declare const Effect: any

export function guardedRate(input: unknown, amount: number) {
  const order = Schema.decodeUnknownSync(OrderSchema)(input)
  if (order.total <= 0) return Effect.fail('NonPositiveTotal')  // provably dead
  return Effect.succeed(amount / order.total)
}
