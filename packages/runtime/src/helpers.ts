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
