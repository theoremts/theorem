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

A 60-year member gets 120% discount → negative shipping cost. Z3 finds it in 0.01s.

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
    ✓  conserved(from, to)
       using: old: __old_from = from, old: __old_to = to

  safeDivide(100, 0)
    ✗  positive(b) — violation confirmed
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

### All Contract Functions

| Function | Purpose | Example |
|---|---|---|
| `requires(pred)` | Precondition | `requires(positive(x))` |
| `ensures(pred)` | Postcondition | `ensures(nonNegative(output()))` |
| `output()` | Return value placeholder | `ensures(output() > 0)` |
| `check(pred)` | Mid-point assertion (SSA-aware) | `check(between(x, 0, 100))` |
| `assume(pred)` | Assume without proof | `assume(balance >= 0)` |
| `invariant(pred)` | Loop invariant | `invariant(() => i >= 0)` |
| `decreases(expr)` | Loop/recursive termination | `decreases(n)` |
| `old(expr)` | Value at function entry | `old(balance)` |
| `conserved(...vals)` | Sum preserved | `conserved(from, to)` |
| `declare(fn, spec)` | External library contract | `declare(Math.sqrt, ...)` |

### Helpers

| Function | Meaning |
|---|---|
| `positive(x)` | `x > 0` |
| `nonNegative(x)` | `x >= 0` |
| `between(x, min, max)` | `min <= x <= max` |
| `integer(x)` | `x` is a whole number |

### Advanced Features

**Mutation tracking:**
```typescript
function transfer(from: number, to: number, amount: number): number {
  requires(amount > 0 && from >= amount)
  ensures(output() === old(from) - amount)
  ensures(conserved(from, to))
  return from - amount
}
```

**Closures:**
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
  decreases(n)
  ensures(nonNegative(output()))
  if (n <= 1) return n
  return fibonacci(n - 1) + fibonacci(n - 2)
}
```

**Objects:**
```typescript
function calculateTax(income: number, rate: number): { gross: number; tax: number; net: number } {
  requires(positive(income))
  requires(between(rate, 0, 0.5))
  ensures(output().gross === output().tax + output().net)
  const tax = income * rate
  return { gross: income, tax, net: income - tax }
}
```

**Caller verification:**
```typescript
function safeDivide(a: number, b: number): number {
  requires(positive(b))
  return a / b
}

safeDivide(100, 0)  // ✗ theorem verify catches: 0 violates positive(b)
```

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

Declare contracts for functions you don't own — libraries, APIs, builtins:

```typescript
// contracts/math.contracts.ts
import { declare, requires, ensures, nonNegative, output } from 'theorem'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})

declare(Math.abs, (x: number): number => {
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

Register in config:

```typescript
// theorem.config.ts
import { defineConfig } from 'theorem'
export default defineConfig({
  contracts: ['contracts/*.contracts.ts'],
})
```

Now Theorem knows `getBalance()` returns `>= 0` and uses it when verifying your code. Like `.d.ts` for types, but for logic.

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

  calculatePercentage
    CRITICAL  division by `total`  line 45
             example: total = 0
```

Walks the AST, finds risky operations (division by zero, null access, array bounds, empty reduce), then uses Z3 to confirm if the risk is reachable. Path-sensitive — filters false positives from guards.

### suggest — auto-generate contracts

```bash
theorem suggest src/
```

```
  safeDivide(a, b)
    ?  requires(b !== 0)  — guards division

  average(a, b)
    →  if you add requires(a >= b), then ensures(output() <= a) becomes provable
```

Analyzes unannotated functions and suggests contracts that hold or would hold with specific preconditions.

## License

MIT
