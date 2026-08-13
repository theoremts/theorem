// Cross-file schema invariants: InvoiceSchema lives in billing-schemas.ts —
// Theorem follows the import, lifts the field constraints AND the .refine()
// invariant, and holds every producer in THIS file to them.
//
//   theorem verify examples/billing.ts

import { InvoiceSchema } from './billing-schemas'
import { requires, positive, nonNegative } from 'theoremts'

declare const z: any
declare namespace z { type output<_S> = any; type infer<_S> = any }
type Invoice = z.output<typeof InvoiceSchema>

// ── PROVED ───────────────────────────────────────────────────────────────────

export function makeInvoice(subtotal: number, tax: number): Invoice {
  requires(positive(subtotal))
  requires(nonNegative(tax))
  return { subtotal, tax, total: subtotal + tax }
}

// ── DISPROVED: forgot to add tax into the total ──────────────────────────────

export function buggyDiscounted(subtotal: number, tax: number): Invoice {
  requires(positive(subtotal))
  requires(nonNegative(tax))
  return { subtotal, tax, total: subtotal }
}

// ── Consumer: schema constraints from the OTHER file prove safety here ───────

export function taxRate(input: unknown): number {
  const inv = InvoiceSchema.parse(input)
  return inv.tax / inv.subtotal
}
