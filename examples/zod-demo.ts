// Zod schemas as out-of-the-box contracts — zero annotations needed.
//
//   theorem verify examples/zod-demo.ts
//   theorem scan   examples/zod-demo.ts
//
// EVERY function below passes `tsc --strict` — every value is a plain
// `number`, so the type system sees nothing wrong. The bugs here live in
// the ARITHMETIC, not in the types:
//
//   - `quantity: number` cannot say "quantity - 1 might be zero"
//   - `discount: number` cannot say "0.5 - discount might be zero"
//   - branded/narrowed types can't express relationships BETWEEN values
//
// Theorem reads the Zod schema (`parse` throws on invalid data, so the
// refinements are facts afterwards) and asks Z3: "does there EXIST any
// schema-valid input that breaks this expression?" UNSAT = proved safe
// for all inputs. SAT = here is the exact input that breaks it.

declare const z: any

const OrderSchema = z.object({
  total: z.number().positive(),        // total > 0
  quantity: z.number().min(1),         // quantity >= 1
  discount: z.number().min(0).max(0.5) // 0 <= discount <= 0.5
})

// ── PROVED safe for ALL schema-valid inputs ──────────────────────────────────
// TS also compiles these — but it compiles the broken ones below identically.

export function unitPrice(input: unknown): number {
  const order = OrderSchema.parse(input)
  // quantity >= 1 ⇒ can never divide by zero
  return order.total / order.quantity
}

export function discountedTotal(input: unknown): number {
  const order = OrderSchema.parse(input)
  // discount <= 0.5 ⇒ (1 - discount) >= 0.5 ⇒ division safe
  return order.total / (1 - order.discount)
}

export function priceVolatility(input: unknown): number {
  const order = OrderSchema.parse(input)

  // total > 0 ⇒ sqrt of a negative andlog(0) are impossible
  return Math.sqrt(order.total) + Math.log(order.total)
}

// ── DISPROVED: the schema admits an input that breaks the math ───────────────
// tsc --strict is equally happy with these. Z3 is not.

export function unitAdjustment(input: unknown): number {
  const order = OrderSchema.parse(input)
  // BUG: quantity === 1 is schema-valid and divides by zero.
  //      Theorem reports: counterexample order.quantity = 1
  return order.total / (order.quantity - 1)
}

export function marginAfterMaxDiscount(input: unknown): number {
  const order = OrderSchema.parse(input)
  // BUG: discount === 0.5 is schema-valid and divides by zero.
  //      No type narrowing can catch this — it's a relationship
  //      between a literal (0.5) and a runtime value's admitted range.
  return order.total / (0.5 - order.discount)
}

// ── Top-level schemas work too ───────────────────────────────────────────────

const RateSchema = z.number().gt(0).lte(1)

export function applyRate(amount: number, input: unknown): number {
  const rate = RateSchema.parse(input)
  // rate > 0 ⇒ division proved safe
  return amount / rate
}
