import { proof, requires, ensures, positive, nonNegative, between, output } from 'theorem'

// ─────────────────────────────────────────────────────────────────────────────
// proof() wrapper style — for const/arrow functions
//
// Use when you can't use inline style (const declarations, arrow functions).
// Note: requires/ensures inside proof() need arrow functions for param access.
// ─────────────────────────────────────────────────────────────────────────────

export const safeDivide = proof(
  (a: number, b: number) => a / b,
  requires(b => positive(b)),
  ensures(r => nonNegative(r)),
)

export const clamp = proof(
  (value: number, min: number, max: number) =>
    value < min ? min : value > max ? max : value,
  requires(({ min, max }) => min <= max),
  ensures(({ result, min }) => result >= min),
  ensures(({ result, max }) => result <= max),
)

export const toPercent = proof(
  (value: number, total: number) => (value / total) * 100,
  requires('value is non-negative'),
  requires('total is positive'),
  requires(({ value, total }) => value <= total),
  ensures('result is between 0 and 100'),
)
