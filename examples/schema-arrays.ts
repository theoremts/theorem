// Schema arrays — element constraints and uniqueness flow from Zod and
// Effect Schema into quantified facts, zero annotations.
//
//   theorem verify examples/schema-arrays.ts

import { requires, ensures, output } from 'theoremts'
import { z } from 'zod'
import * as Schema from 'effect/Schema'

const OrderSchema = z.object({
  scores: z.array(z.number().min(1)),                                     // → forall(scores, v => v >= 1)
  users: z.array(z.object({ balance: z.number().nonnegative() })),        // → forall(users, u => u.balance >= 0)
  ids: z.array(z.number()).refine(a => new Set(a).size === a.length),     // → unique(ids)
})

// ✓ PROVED — the element schema guarantees every score >= 1
export function scoreAt(input: unknown, k: number): number {
  const order = OrderSchema.parse(input)
  requires(Number.isInteger(k))
  requires(k >= 0)
  requires(k < order.scores.length)
  ensures(output() >= 1)
  return order.scores[k]!
}

// ✓ PROVED — object elements carry their field constraints
export function balanceAt(input: unknown, k: number): number {
  const order = OrderSchema.parse(input)
  requires(Number.isInteger(k))
  requires(k >= 0)
  requires(k < order.users.length)
  ensures(output() >= 0)
  return order.users[k]!.balance
}

// ✓ PROVED — the canonical Set-size refine means pairwise-distinct ids
export function idsDiffer(input: unknown): boolean {
  const order = OrderSchema.parse(input)
  requires(order.ids.length >= 2)
  ensures(output() === true)
  return order.ids[0]! !== order.ids[1]!
}

// ✗ DISPROVED (or unknown) — min(1) does NOT imply >= 2; facts are exact
export function tooStrong(input: unknown, k: number): number {
  const order = OrderSchema.parse(input)
  requires(Number.isInteger(k))
  requires(k >= 0)
  requires(k < order.scores.length)
  ensures(output() >= 2)
  return order.scores[k]!
}

// ── Effect Schema: full parity ──────────────────────────────────────────────

const EffectOrderSchema = Schema.Struct({
  scores: Schema.Array(Schema.Number.pipe(Schema.greaterThanOrEqualTo(1))),
  users: Schema.Array(Schema.Struct({ balance: Schema.Number.pipe(Schema.nonNegative()) })),
})

// ✓ PROVED — same facts, Effect flavor
export function effectScoreAt(input: unknown, k: number): number {
  const order = Schema.decodeUnknownSync(EffectOrderSchema)(input)
  requires(Number.isInteger(k))
  requires(k >= 0)
  requires(k < order.scores.length)
  ensures(output() >= 1)
  return order.scores[k]!
}
