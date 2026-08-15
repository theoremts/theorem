/**
 * Placeholder for the function's return value in contracts.
 *
 *   ensures(nonNegative(output()))
 *   ensures(output() > 0)
 *   ensures(output() <= price)
 */
export function output(): any {
  return undefined
}

export function positive(value: number): boolean {
  return value > 0
}

export function nonNegative(value: number): boolean {
  return value >= 0
}

export function negative(value: number): boolean {
  return value < 0
}

export function finite(value: number): boolean {
  return Number.isFinite(value)
}

export function between(value: number, min: number, max: number): boolean {
  return value >= min && value <= max
}

export function sorted(arr: number[]): boolean {
  return arr.every((item, i) => i === 0 || (arr[i - 1] as number) <= item)
}

export function unique<T>(arr: T[], key?: (item: T) => unknown): boolean {
  const values = key ? arr.map(key) : arr
  return new Set(values).size === values.length
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
export function seqEq<T>(a: readonly T[], b: readonly T[]): boolean {
  return a.length === b.length && a.every((v, i) => v === b[i])
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
