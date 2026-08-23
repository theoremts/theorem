/**
 * Placeholder for the function's return value in contracts.
 *
 *   ensures(nonNegative(output()))
 *   ensures(output() > 0)
 *   ensures(output() <= price)
 */
// output() must be SAFE to evaluate at runtime: expression-form contracts
// (`ensures(output().total.equals(x))`) evaluate their argument eagerly, so
// returning undefined crashes the annotated function the first time it runs
// for real. The absorbing proxy swallows any property access, call, or
// coercion and keeps returning itself — the whole chain evaluates to inert
// junk that ensures() ignores.
/* eslint-disable @typescript-eslint/no-unsafe-return, @typescript-eslint/no-explicit-any */
const absorbing: any = new Proxy(function () { /* inert */ }, {
  get(_target, prop) {
    if (prop === Symbol.toPrimitive || prop === 'valueOf') return () => 0
    if (prop === 'toString' || prop === Symbol.toStringTag) return () => '__theorem_output__'
    if (prop === 'then') return undefined  // never thenable — await must not hang
    return absorbing
  },
  apply() { return absorbing },
  has() { return true },
})
/* eslint-enable @typescript-eslint/no-unsafe-return, @typescript-eslint/no-explicit-any */

export function output(): any {
  return absorbing
}

// Numeric domain helpers accept nullable values AND Decimal-like objects
// (anything with toNumber()) by TYPE, so contracts over optional or Decimal
// parameters read as one word — `requires(gte(rate, 0))` — with the
// semantics "present AND in the domain". At runtime a nullish value fails
// the check; the engine translates the plain numeric comparison.

/** A contract-comparable value: number, Decimal-like, or absent. */
export type ComparableValue = number | { toNumber(): number } | null | undefined

function numValue(v: ComparableValue): number | null {
  if (v == null) return null
  return typeof v === 'number' ? v : v.toNumber()
}

export function gt(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a > b
}

export function gte(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a >= b
}

export function lt(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a < b
}

export function lte(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a <= b
}

export function eq(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a === b
}

export function neq(value: ComparableValue, bound: ComparableValue): boolean {
  const a = numValue(value); const b = numValue(bound)
  return a != null && b != null && a !== b
}

export function positive(value: ComparableValue): boolean {
  return gt(value, 0)
}

export function nonNegative(value: ComparableValue): boolean {
  return gte(value, 0)
}

export function negative(value: ComparableValue): boolean {
  return lt(value, 0)
}

export function finite(value: ComparableValue): boolean {
  const n = numValue(value)
  return n != null && Number.isFinite(n)
}

export function between(value: ComparableValue, min: ComparableValue, max: ComparableValue): boolean {
  return gte(value, min) && lte(value, max)
}

/**
 * Presence assertion usable as a TypeScript type guard: after
 * `requires(defined(x) && x.balance >= 0)` the `&&` narrows `x` for the rest
 * of the predicate. The engine translates it to `x !== null`.
 */
export function defined<T>(value: T | null | undefined): value is T {
  return value != null
}

export function sorted(_arr: number[]): boolean {
  // TRUE no-op — evaluating at runtime costs O(n) per contracted call. Z3 evaluates.
  return true
}

export function unique<T>(_arr: T[], _key?: (item: T) => unknown): boolean {
  // TRUE no-op — see sorted.
  return true
}

/**
 * Constrains a value to be an integer.
 * At runtime, checks Number.isInteger(x).
 * The engine translates this to Z3: x === ToInt(x).
 *
 *   requires(integer(n))  // n must be a whole number
 */
export function integer(x: number): boolean {
  return Number.isInteger(x)
}

/**
 * Asserts that the sum of all listed values is unchanged after mutation.
 * At runtime this is always true — the engine reads it statically and compares
 * sum(old(values)) === sum(values) using Z3.
 */
export function conserved(..._values: number[]): boolean {
  return true
}

/**
 * Structural equality of sequences in specifications.
 * At runtime performs an element-wise comparison; the engine translates it
 * to Z3 sequence equality (`[x, ...list(tail)]` becomes seq.concat).
 *
 *   ensures(seqEq(list(output()), [x, ...list(tail)]))
 */
export function seqEq<T>(_a: readonly T[], _b: readonly T[]): boolean {
  // TRUE no-op — arguments may be spec-only expressions (list(output())).
  return true
}

/**
 * Declares that `membership(root, x)` characterizes the FOOTPRINT of the
 * spec predicate `spec(root)` — i.e., `spec` only reads fields of objects
 * `x` for which `membership(root, x)` holds. The engine uses this pairing
 * for frame reasoning: writes to objects provably OUTSIDE the footprint
 * cannot change the predicate's value. The pairing itself is TRUSTED
 * (like a Dafny reads-clause); no-op at runtime.
 *
 *   footprint(validChain, inChain)
 */
export function footprint(_spec: unknown, _membership: unknown): void {
  // no-op — read statically by the engine
}

/**
 * Pairwise distinctness of a projected field: `uniqueBy(users, u => u.balance)`
 * holds when no two elements share the projected value. No-op at runtime.
 */
export function uniqueBy<T>(_arr: readonly T[], _by: (x: T) => unknown): boolean {
  return true
}

/**
 * Order by a projected field: `sortedBy(users, u => u.balance)` holds when
 * the projection is non-decreasing across adjacent elements. No-op at runtime.
 */
export function sortedBy<T>(_arr: readonly T[], _by: (x: T) => number): boolean {
  return true
}

/**
 * Sum of a projected numeric field: `sumBy(users, u => u.balance)`.
 * In contracts, writes through DISTINCT elements (requires(unique(arr)))
 * update the sum by exactly their delta — conservation becomes provable.
 * No-op at runtime.
 */
export function sumBy<T>(_arr: readonly T[], _by: (x: T) => number): number {
  return 0
}

/**
 * Count of elements satisfying a predicate: `countBy(users, u => u.balance > 0)`.
 * Always between 0 and arr.length. No-op at runtime.
 */
export function countBy<T>(_arr: readonly T[], _by: (x: T) => boolean): number {
  return 0
}
