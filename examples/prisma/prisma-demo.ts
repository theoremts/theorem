// Database schema → proofs, end to end:
//
//   theorem prisma examples/prisma/schema.prisma     (generates theorem-schemas.ts)
//   theorem verify examples/prisma/prisma-demo.ts
//
// `quantity Int` in schema.prisma became z.number().int() — an integer fact
// TypeScript's `number` cannot express, and exactly what Z3 needs.

import { OrderRowSchema } from './theorem-schemas'

// ── PROVED: an integer minus 0.5 can never be zero ───────────────────────────
export function safeStep(input: unknown): number {
  const row = OrderRowSchema.parse(input)
  return 100 / (row.quantity - 0.5)
}

// ── DISPROVED: nothing prevents quantity === 0 in the database ───────────────
export function perUnit(input: unknown): number {
  const row = OrderRowSchema.parse(input)
  return 100 / row.quantity
}
