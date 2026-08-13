// Schema .refine() as a MODEL INVARIANT — the schema-first equivalent of a
// class invariant, in the idiom of schema-first codebases:
//
//   schema defines the rule once → every producer of the type must prove it.
//
//   theorem verify examples/zod-invariant.ts
//
// The cross-field rule (gross === tax + net) is invisible to TypeScript:
// `TaxRecord` only knows three numbers. A `.refine()` checks it at runtime,
// at the boundary, for one value. Theorem proves it statically, for every
// function that RETURNS the type, over all inputs.

import { requires, positive, between, nonNegative } from 'theoremts'

declare const z: any
declare namespace z { type output<_S> = any; type infer<_S> = any }

const TaxRecordSchema = z.object({
  gross: z.number().positive(),
  tax: z.number().nonnegative(),
  net: z.number(),
}).refine((t: any) => t.gross === t.tax + t.net)

type TaxRecord = z.output<typeof TaxRecordSchema>

// ── PROVED: every producer of TaxRecord maintains the invariant ──────────────

export function computeTax(income: number, rate: number): TaxRecord {
  requires(positive(income))
  requires(between(rate, 0, 0.5))
  const tax = income * rate
  return { gross: income, tax, net: income - tax }
}

// ── DISPROVED: this "quick fix" silently breaks the model ────────────────────

export function buggyRebate(income: number, rebate: number): TaxRecord {
  requires(positive(income))
  requires(nonNegative(rebate))
  // BUG: rebate applied to net but not to tax — gross ≠ tax + net.
  // TypeScript compiles this happily; the invariant refutes it.
  return { gross: income, tax: income * 0.2, net: income * 0.8 - rebate }
}

// ── Consumers get the invariant as an assumption via parse() ─────────────────

export function effectiveRate(input: unknown): number {
  const rec = TaxRecordSchema.parse(input)
  // gross > 0 comes from the schema — division proved safe
  return rec.tax / rec.gross
}
