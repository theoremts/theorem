import {
  requires, ensures, check,
  positive, nonNegative, between, output,
  invariant, decreases,
  integer,
} from 'theoremts'

// ─────────────────────────────────────────────────────────────────────────────
// Theorem basics — inline style (recommended)
//
// requires() = what the function demands from callers
// ensures()  = what the function guarantees about its output
// ─────────────────────────────────────────────────────────────────────────────

// ── Arithmetic ───────────────────────────────────────────────────────────────

function nextOdd(n: number) {
  requires(integer(n))
  requires(n % 2 === 0)
  ensures(output() % 2 !== 0)
  return n + 1
}

var a = 2;
var b = 4;




function nextOdd2e(n: number) {
  if (n % 2 === 0) {
    nextOdd(n);
  }
}

export function applyDiscount(price: number, percent: number): number {
  requires(positive(price))
  requires(between(percent, 0, 100))
  ensures(nonNegative(output()))
  ensures(output() <= price)

  return price * (1 - percent / 100)
}

export function splitEvenly(total: number, parts: number): number {
  requires(nonNegative(total))
  requires(positive(parts))
  ensures(nonNegative(output()))

  return total / parts
}

// ── Conditions: if/else ──────────────────────────────────────────────────────

export function tieredDiscount(basePrice: number, quantity: number): number {
  requires(positive(basePrice))
  requires(positive(quantity))
  ensures(positive(output()))
  ensures(output() <= basePrice)

  if (quantity >= 100) return basePrice * 0.7
  if (quantity >= 10) return basePrice * 0.9
  return basePrice
}

export function clamp(value: number, min: number, max: number): number {
  requires(min <= max)
  ensures(output() >= min)
  ensures(output() <= max)

  if (value < min) return min
  if (value > max) return max
  return value
}

// ── Let/if assignment + const ────────────────────────────────────────────────

export function shippingCost(weight: number, distance: number, memberYears: number): number {
  requires(positive(weight))
  requires(positive(distance))
  requires(nonNegative(memberYears))
  ensures(output() > 0)

  let rate: number
  if (weight > 30) rate = weight * 2.5
  else if (weight > 10) rate = weight * 1.5
  else rate = weight * 1.0

  let surcharge = 0
  if (distance > 1000) surcharge = distance * 0.01
  else if (distance > 500) surcharge = distance * 0.005

  const discount = Math.min(memberYears * 0.02, 0.5)

  return (rate + surcharge) * (1 - discount)
}

// ── SSA-aware check: sees state after mutation ───────────────────────────────

export function processPayroll(baseSalary: number, hoursWorked: number): number {
  requires(positive(baseSalary))
  requires(nonNegative(hoursWorked))
  ensures(nonNegative(output()))

  if (baseSalary > 10000) baseSalary = 10000  // cap

  check(between(baseSalary, 0, 10000))  // sees capped value

  return baseSalary * (hoursWorked / 160)
}

// ── Loop with invariant + decreases ──────────────────────────────────────────

export function factorial(n: number): number {
  requires(n >= 0)
  ensures(positive(output()))

  let result = 1
  let i = n
  while (i > 0) {
    invariant(() => result > 0)
    invariant(() => i >= 0)
    decreases(() => i)
    result = result * i
    i = i - 1
  }
  return result
}

// ── Recursive termination ────────────────────────────────────────────────────

export function fibonacci(n: number): number {
  requires(n >= 0)
  decreases(n)
  ensures(nonNegative(output()))

  if (n <= 1) return n
  return fibonacci(n - 1) + fibonacci(n - 2)
}

// ── ✗ Intentional bug: missing requires ──────────────────────────────────────

export function buggySubtract(price: number, discount: number): number {
  requires(positive(price))
  // missing: requires(discount <= price)
  ensures(nonNegative(output()))

  return price - discount
}
