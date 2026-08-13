// Refinement types: the TYPE of a parameter carries its constraints.
//
//   theorem verify examples/refinement-types.ts
//
// `type Rate = z.output<typeof RateSchema>` turns any `rate: Rate` parameter
// into a refined value: the schema's constraints become requires — assumed
// inside the function, and PROVED at every call site. TypeScript sees only
// `number`; Theorem sees `0 < rate <= 1`.

declare const z: any
declare namespace z { type output<_S> = any }

const RateSchema = z.number().gt(0).lte(1).brand()  // .brand<'Rate'>() with real zod
type Rate = z.output<typeof RateSchema>

// The parameter type alone makes this function verifiable:
// division proved safe because the TYPE says rate > 0.
export function applyRate(amount: number, rate: Rate): number {
  return amount / rate
}

// ── Call sites are held to the refinement ────────────────────────────────────

// ✓ PROVED: 0.5 satisfies 0 < rate <= 1
export function goodCaller(): number {
  return applyRate(100, 0.5 as Rate)
}

// ✗ DISPROVED at the call site: 0 violates rate > 0.
// The `as Rate` cast satisfies TypeScript — but not the solver.
export function badCaller(): number {
  return applyRate(100, 0 as Rate)
}
