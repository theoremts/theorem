// ─────────────────────────────────────────────────────────────────────────────
// Unannotated functions — for `theorem scan` and `theorem suggest`
//
// No imports, no contracts. Theorem detects risks automatically.
// Run: theorem scan examples/scan.ts
//      theorem suggest examples/scan.ts
// ─────────────────────────────────────────────────────────────────────────────

// CRITICAL: b could be 0
export const divide = (a: number, b: number) => a / b

// CRITICAL: denominator can be zero
export const priceAfterDiscount = (price: number, discount: number) =>
  (price - discount) / price

// Safe: x^2 + y^2 is always >= 0 — Z3 proves sqrt arg can't be negative
export const hypotenuse = (x: number, y: number) => Math.sqrt(x * x + y * y)

// Safe: denominator is literal 2
export const average = (a: number, b: number) => (a + b) / 2

// Guarded: path-sensitive scan detects the guard
export const safeDivide = (a: number, b: number) => b !== 0 ? a / b : 0
