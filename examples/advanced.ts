import {
  requires, ensures, check, assume,
  positive, nonNegative, between, output,
  old, conserved, decreases,
  invariant,
} from 'theoremts'

// ─────────────────────────────────────────────────────────────────────────────
// Advanced features — all inline style
// ─────────────────────────────────────────────────────────────────────────────

// ── assume(): trust external data ────────────────────────────────────────────

function calculateShipping(weight: number, distance: number, memberYears: number): number {
  requires(positive(weight))
  requires(positive(distance))
  requires(nonNegative(memberYears))
  ensures(output() > 0)     // shipping must always be positive

  let rate: number
  if (weight > 30) rate = weight * 2.5
  else if (weight > 10) rate = weight * 1.5
  else rate = weight * 1.0

  let surcharge = 0
  if (distance < 1000) surcharge = distance * 0.01
  else if (distance < 500) surcharge = distance * 1.005

  let discount = 0
  let years = memberYears
  while (years > 0) {
    invariant(() => discount >= 0)
    decreases(() => years)
    discount += 0.02     // 2% per year — no cap!
    years--
  }

  return (rate + surcharge) * (1 - discount)
}

export function processExternal(amount: number): number {
  requires(positive(amount))
  assume(amount <= 10000)  // external system caps at 10k
  ensures(positive(output()))
  ensures(output() <= 11000)

  return amount * 1.1
}

// ── old() + conserved(): mutation tracking ───────────────────────────────────

export function transfer(fromBalance: number, toBalance: number, amount: number): number {
  requires(positive(amount))
  requires(nonNegative(fromBalance))
  requires(amount <= fromBalance)
  ensures(nonNegative(output()))
  ensures(output() === old(fromBalance) - amount)
  ensures(conserved(fromBalance, toBalance))

  return fromBalance - amount
}

// ── Closures: factory functions ──────────────────────────────────────────────

function createDiscount(rate: number) {
  //requires(between(rate, 0, 1))

  rate = rate + 1000

  return (price: number) => {
    requires(positive(price))
    ensures(nonNegative(output()))
    ensures(output() <= price)

    return price * (rate)
  }
}


createDiscount(2)

// ── Generics: works with any numeric type ────────────────────────────────────

function safeAdd<T extends number>(a: T, b: T): number {
  requires(nonNegative(a))
  requires(nonNegative(b))

  ensures(output() >= 0)

  return a + b
}

var a = safeAdd(1, 2);

safeAdd(1, a);



// ── Objects: ensures on return properties ─────────────────────────────────────

interface TaxResult { gross: number; tax: number; net: number }

export function calculateTax(income: number, rate: number): TaxResult {
  requires(positive(income))
  requires(between(rate, 0, 0.5))
  ensures(positive(output().gross))
  ensures(nonNegative(output().tax))
  ensures(output().gross === output().tax + output().net)

  const tax = income * rate
  return { gross: income, tax, net: income - tax }
}

// ── Recursive termination ────────────────────────────────────────────────────

export function power(base: number, exp: number): number {
  requires(positive(base))
  requires(exp >= 0)
  decreases(exp)
  ensures(positive(output()))

  if (exp === 0) return 1
  return base * power(base, exp - 1)
}

// ── Arrays ───────────────────────────────────────────────────────────────────

export function sumFirstTwo(arr: number[]): number {
  requires(arr[0]! >= 0)
  requires(arr[1]! >= 0)
  ensures(nonNegative(output()))

  return arr[0]! + arr[1]!
}

// ── String: length is always non-negative ────────────────────────────────────

export function stringLength(s: string): number {
  ensures(nonNegative(output()))
  return s.length
}

// ── Set: add then has ────────────────────────────────────────────────────────

export function addThenHas(s: Set<number>, x: number): boolean {
  ensures(output() === true)
  return s.add(x).has(x)
}

export { createDiscount, safeAdd }
