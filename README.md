# Theorem

**Formal verification for TypeScript.** Prove your code is correct for *all* possible inputs — not by testing samples, but by mathematical proof using the Z3 SMT solver.

```typescript
import { requires, ensures, positive, nonNegative, output } from 'theorem'

function safeDivide(a: number, b: number): number {
  requires(positive(b))
  ensures(nonNegative(output()))
  return a / b
}
```

```
$ theorem verify src/
  safeDivide
    ✓  nonNegative(output())    — proved for ALL inputs
       using: requires: positive(b)
    ✓  safe division: b !== 0
       using: requires: positive(b)
```

## Why Theorem?

**Tests check examples. Theorem checks all inputs.**

```
Unit test:   tests safeDivide(10, 2) → 5           (1 case)
fast-check:  tests 1000 random combinations          (1000 cases)
Theorem/Z3:  proves NO input can violate the contract (all cases)
```

If there's a bug, Z3 finds the exact input:

```
  buggyDiscount
    ✗  nonNegative(output())
       counterexample: price = 0.25, discount = 0.5, result = -0.25
```

### The Bug Tests Won't Catch

A shipping calculator with tiers, surcharges, and a loyalty discount:

```typescript
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
  if (distance > 1000) surcharge = distance * 0.01
  else if (distance > 500) surcharge = distance * 0.005

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
```

5 unit tests pass. Then:

```
$ theorem verify shipping.ts

  calculateShipping
    ✗  output() > 0
       counterexample: weight = 1, distance = 1, memberYears = 51, result = -0.02
```

A 60-year member gets 120% discount → negative shipping cost. Z3 finds it in 0.01s. No developer writes a test for a 60-year member — but the code allows it.

## Installation

```bash
npm install theorem
npm install -D theorem-cli
```

## Usage

```bash
theorem verify src/     # prove contracts with Z3
```

```
  applyDiscount
    ✓  nonNegative(output())
       using: requires: positive(price), requires: between(percent, 0, 100)

  transfer
    ✓  nonNegative(output())
       using: requires: amount <= fromBalance
```

## Writing Contracts

**`requires`** = what the function demands (precondition)
**`ensures`** = what the function guarantees (postcondition)

```typescript
function applyDiscount(price: number, percent: number): number {
  requires(positive(price))
  requires(between(percent, 0, 100))
  ensures(nonNegative(output()))
  ensures(output() <= price)
  return price * (1 - percent / 100)
}
```

If `requires` is not satisfied → **caller's fault**. If `ensures` is not satisfied → **implementation bug**.

### Caller Verification

Theorem automatically verifies that callers satisfy the callee's `requires`:

```typescript
function safeDivide(a: number, b: number): number {
  requires(positive(b))
  return a / b
}

// Inside verified code — cross-function check
function unitPrice(total: number, quantity: number): number {
  requires(positive(quantity))
  return safeDivide(total, quantity)  // ✓ quantity satisfies positive(b)
}

// Outside verified code — call-site check
safeDivide(100, 0)   // ✗ violates requires: positive(b)
safeDivide(100, -5)  // ✗ violates requires: positive(b)
```

```
$ theorem verify src/
  unitPrice
    ✓  call safeDivide(total, quantity): positive(b)
       using: requires: positive(quantity)

  (call-site checks)
    ✗  safeDivide(100, 0): positive(b)
       violation confirmed (literal values)
```

Works with any call pattern — `service.calculate(x)`, `this.payments.process(x)`:

```typescript
class OrderProcessor {
  @requires(positive(total))
  processFee(total: number): number {
    return this.payments.calculateFee(total, 5)  // ✓ verified against calculateFee's requires
  }
}
```

### Bugs Theorem Catches

**Uncapped discount — result goes negative:**
```typescript
function applyBonus(salary: number, bonusPercent: number): number {
  requires(positive(salary))
  // missing: requires(nonNegative(bonusPercent))
  ensures(nonNegative(output()))
  return salary + salary * bonusPercent / 100
}
// ✗ counterexample: salary = 1, bonusPercent = -200, result = -1
```

**Commission exceeds sales — missing rate cap:**
```typescript
function commission(sales: number, years: number): number {
  requires(positive(sales))
  requires(nonNegative(years))
  ensures(output() <= sales)  // commission shouldn't exceed sales
  
  let rate: number
  if (sales > 100000) rate = 0.10
  else rate = 0.05
  
  const bonus = years * 0.01  // 1% per year, no cap!
  return sales * (rate + bonus)
}
// ✗ counterexample: sales = 1, years = 96, result = 1.01
```

**Rebalancing without weight check — allocation exceeds 100%:**
```typescript
function allocate(total: number, w1: number, w2: number, w3: number): number {
  requires(positive(total))
  requires(nonNegative(w1))
  requires(nonNegative(w2))
  requires(nonNegative(w3))
  // missing: requires(w1 + w2 + w3 === 1)
  ensures(output() <= total)
  return total * w1 + total * w2 + total * w3
}
// ✗ counterexample: total = 1, w1 = 2, w2 = 0, w3 = 0, result = 2
```

### SSA-Aware Check

`check()` sees the state **after** mutations — like Dafny's `assert`:

```typescript
function processPayroll(baseSalary: number): number {
  requires(positive(baseSalary))
  
  if (baseSalary > 10000) baseSalary = 10000  // cap

  check(between(baseSalary, 0, 10000))  // ✓ sees value after cap
  
  return baseSalary * 0.9
}
```

### All Contract Functions

| Function | Purpose | Example |
|---|---|---|
| `requires(pred)` | Precondition | `requires(positive(x))` |
| `ensures(pred)` | Postcondition (sees final state) | `ensures(nonNegative(output()))` |
| `output()` | Return value placeholder | `ensures(output() > 0)` |
| `check(pred)` | Mid-point assertion (SSA-aware) | `check(between(x, 0, 100))` |
| `assume(pred)` | Assume without proof | `assume(balance >= 0)` |
| `invariant(pred)` | Loop invariant | `invariant(() => i >= 0)` |
| `decreases(expr)` | Loop/recursive termination | `decreases(n)` |
| `old(expr)` | Value at function entry | `old(balance)` |
| `conserved(...vals)` | Sum preserved across mutation | `conserved(from, to)` |
| `declare(fn, spec)` | External library contract | `declare(Math.sqrt, ...)` |

### Helpers

| Function | Meaning |
|---|---|
| `positive(x)` | `x > 0` |
| `nonNegative(x)` | `x >= 0` |
| `between(x, min, max)` | `min <= x <= max` |
| `integer(x)` | `x` is a whole number |

### Advanced Features

**Pre/post mutation with `old()` and `conserved()`:**
```typescript
function withdraw(balance: number, amount: number): number {
  requires(positive(amount))
  requires(balance >= amount)
  
  balance -= amount  // mutation
  
  ensures(output() >= 0)
  ensures(output() === old(balance) - amount)  // old() = value before mutation
  return balance
}
```

**Closures — factory functions with captured variables:**
```typescript
function createDiscount(rate: number) {
  requires(between(rate, 0, 1))
  return (price: number) => {
    requires(positive(price))
    ensures(output() <= price)
    return price * (1 - rate)
  }
}
```

**Recursive termination:**
```typescript
function fibonacci(n: number): number {
  requires(n >= 0)
  requires(integer(n))
  decreases(n)
  ensures(nonNegative(output()))
  if (n <= 1) return n
  return fibonacci(n - 1) + fibonacci(n - 2)
}
```

**Object return types:**
```typescript
function calculateTax(income: number, rate: number): { gross: number; tax: number; net: number } {
  requires(positive(income))
  requires(between(rate, 0, 0.5))
  ensures(output().gross === output().tax + output().net)
  const tax = income * rate
  return { gross: income, tax, net: income - tax }
}
```

**Separate proof files** — keep proofs out of source code:
```typescript
// payment.proof.ts — proves contracts for functions in payment.ts
import { requires, ensures, positive, nonNegative, output } from 'theorem'

function processPayment(amount: number, fee: number): number {
  requires(positive(amount))
  requires(between(fee, 0, 0.1))
  ensures(positive(output()))
  return amount * (1 - fee)
}
```

Both source and `.proof.ts` files are picked up automatically by `theorem verify`.

### Alternative Styles

**Decorators** (class methods only):
```typescript
class Calculator {
  @requires(positive(b))
  @ensures(nonNegative(output()))
  divide(a: number, b: number): number { return a / b }
}
```

**proof() wrapper** (const/arrow functions):
```typescript
export const clamp = proof(
  (value: number, min: number, max: number) =>
    value < min ? min : value > max ? max : value,
  requires(({ min, max }) => min <= max),
  ensures(({ result, min }) => result >= min),
)
```

**String contracts:**
```typescript
requires('total is positive')
ensures('result is between 0 and 100')
```

## VS Code Integration

```bash
npm install -D theorem-ts-plugin
```

```json
// tsconfig.json
{ "compilerOptions": { "plugins": [{ "name": "theorem-ts-plugin" }] } }
```

Shows contract violations inline — squiggly lines, hover tooltips, Problems panel.

## External Library Contracts

Declare contracts for functions you don't own — like `.d.ts` for types, but for logic:

```typescript
// contracts/math.contracts.ts
import { declare, requires, ensures, nonNegative, output } from 'theorem'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})
```

```typescript
// contracts/api.contracts.ts
import { declare, ensures, nonNegative, output } from 'theorem'

declare(getBalance, (userId: string): number => {
  ensures(nonNegative(output()))
})
```

Auto-discovered from `node_modules/@theorem-contracts/*` or configured:

```typescript
// theorem.config.ts
import { defineConfig } from 'theorem'
export default defineConfig({
  contracts: ['contracts/*.contracts.ts'],
})
```

Publishable as npm packages — `@theorem-contracts/bignumber`, `@theorem-contracts/decimal`, etc.

## Configuration

```typescript
// theorem.config.ts
import { defineConfig } from 'theorem'
export default defineConfig({
  include: ['src/**/*.ts'],
  exclude: ['**/*.test.ts'],
  contracts: ['contracts/*.contracts.ts'],
  solver: { timeout: 10000, maxCounterexamples: 3 },
})
```

## CI Integration

```yaml
# GitHub Actions
- run: npx theorem verify --strict src/
- run: npx theorem scan --strict --format sarif src/ > theorem.sarif
- uses: github/codeql-action/upload-sarif@v3
  with: { sarif_file: theorem.sarif }
```

## Bundler Plugins

Strip contracts at build time — zero runtime overhead:

```typescript
// vite.config.ts
import { theoremVite } from 'theorem/vite'
export default { plugins: [theoremVite()] }
```

Also available: `theorem/esbuild`, `theorem/tsup`.

## How It Works

```
TypeScript → PARSER (ts-morph + SSA) → TRANSLATOR → Z3 WASM → REPORTER
```

To prove `ensures(P)`, Z3 tries to find an input where all `requires` hold but `P` is violated. UNSAT = proved. SAT = counterexample.

Inspired by [Dafny](https://dafny.org), [Ada/SPARK](https://www.adacore.com/about-spark), and [Frama-C](https://frama-c.com).

## Alpha Features

### scan — detect risks without annotations

```bash
theorem scan src/
```

```
  divide
    CRITICAL  division by `b`  line 12
             example: b = 0

  processOrder
    CRITICAL  safeDivide(total, quantity) may violate: positive(b)
             example: quantity = 0

  getValue
    CRITICAL  `data.value` — `data` may be null/undefined (type: Data | null)
```

Walks the AST, finds risky operations (division by zero, null access, array bounds, empty reduce, contract violations at call sites), then uses Z3 to confirm reachability. Path-sensitive — filters false positives from guards.

### suggest — auto-generate contracts

```bash
theorem suggest src/
```

```
  safeDivide(a, b)
    ?  requires(b !== 0)  — guards division

  average(a, b)
    →  if you add requires(a >= b), then ensures(output() <= a) becomes provable

  subtract(a, b)
    →  if you add requires(a >= b), then ensures(nonNegative(output())) becomes provable
```

Analyzes unannotated functions and suggests contracts that hold or would hold with specific preconditions.

## License

MIT
