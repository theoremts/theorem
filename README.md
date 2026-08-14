# Theorem

**Formal verification for TypeScript.** Prove your code is correct for *all* possible inputs — not by testing samples, but by mathematical proof using the Z3 SMT solver.

```typescript
import { requires, ensures, positive, nonNegative, output } from 'theoremts'

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
npm install -D theoremts theoremts-cli
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
import { requires, ensures, positive, nonNegative, output } from 'theoremts'

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

## Schemas as Contracts — zero annotations

Your validation schemas already state your invariants. Theorem reads them:
`Schema.parse()` throws on invalid data, so after the parse the schema's
refinements are mathematical facts. No imports, no annotations — the schema
IS the contract.

```typescript
const OrderSchema = z.object({
  total: z.number().positive(),
  quantity: z.number().int().min(1),
  discount: z.number().min(0).max(0.5),
})

export function unitPrice(input: unknown): number {
  const order = OrderSchema.parse(input)
  return order.total / order.quantity        // ✓ proved: quantity >= 1
}

export function unitAdjustment(input: unknown): number {
  const order = OrderSchema.parse(input)
  return order.total / (order.quantity - 1)  // ✗ counterexample: quantity = 1
}
```

Every function here passes `tsc --strict` — the bug lives in the arithmetic,
not the types. Only the solver separates safe from broken. Effect Schema has
full parity (`Schema.decodeUnknownSync`, `Schema.Struct`, `Schema.filter`),
and `Schema.int()` gives Z3 the integer fact `number` can't express.

### Cross-field model invariants — `.refine()`

A `.refine()` predicate is a **model invariant**: assumed wherever the schema
is parsed, and **proved for every function that returns the type**.

```typescript
const TaxRecordSchema = z.object({
  gross: z.number().positive(),
  tax: z.number().nonnegative(),
  net: z.number(),
}).refine(t => t.gross === t.tax + t.net)

type TaxRecord = z.output<typeof TaxRecordSchema>

export function buggyRebate(income: number, rebate: number): TaxRecord {
  requires(positive(income))
  // ✗ counterexample: rebate applied to net but not tax — gross ≠ tax + net
  return { gross: income, tax: income * 0.2, net: income * 0.8 - rebate }
}
```

Schemas imported from other files are resolved through relative imports.

### Refinement types — the parameter type is the contract

```typescript
const RateSchema = z.number().gt(0).lte(1).brand()
type Rate = z.output<typeof RateSchema>

export function applyRate(amount: number, rate: Rate): number {
  return amount / rate            // ✓ proved: the TYPE says rate > 0
}

applyRate(100, 0 as Rate)         // ✗ caught at the CALL SITE:
                                  //   `as` satisfies tsc — not Z3
```

### tRPC boundaries

`t.procedure.input(Schema).mutation(handler)` — the handler assumes the input
schema's constraints and invariants automatically (tRPC validates before
invoking it). Zod or Effect Schema.

### Database facts — `theorem prisma`

```bash
theorem prisma prisma/schema.prisma    # → theorem-schemas.ts
```

Generates row schemas from your database schema: `Int` columns become
integer facts, nullability maps to `.nullable()`, enums are documented.
Column constraints flow into proofs.

## Object Invariants

### Class invariants — Design by Contract

Declared once on the class; assumed at every method entry, proved at every
exit (mutations of `this.*` are tracked), and the constructor must establish
it:

```typescript
@invariant((self: Account) => self.balance >= 0)
class Account {
  balance: number

  constructor(initial: number) {
    requires(positive(initial))
    this.balance = initial              // ✓ establishes the invariant
  }

  withdraw(amount: number): void {
    requires(positive(amount))
    if (amount <= this.balance) {
      this.balance = this.balance - amount   // ✓ guarded — preserved
    }
  }

  overdraw(amount: number): void {
    requires(positive(amount))
    this.balance = this.balance - amount     // ✗ balance = 0, amount = 0.5
  }
}
```

## Verifying Mutation — heap, aliasing, and pointers

When a function mutates fields of object parameters, Theorem switches to a
heap encoding (Z3 arrays): object references become solver values, so
**aliasing is a case the solver explores** rather than an assumption it
silently makes.

```typescript
export function drainUnsafe(from: Account, to: Account): void {
  requires(nonNegative(from.value))
  requires(nonNegative(to.value))
  ensures(to.value === old(to.value) + old(from.value))
  to.value = to.value + from.value
  from.value = 0
}
// ✗ counterexample: from = 2, to = 2  — the SAME reference!
//   Aliased, the two writes hit one cell: the value doubles, then zeroes.
//   Add requires(from !== to) and it proves.
```

`modifies(a, b)` restricts which objects a function may write (undeclared
writes are violations), and `old(x.f)` reads the pre-state.

### Recursive invariants over linked structures

User-defined recursive predicates work over the mutable heap — the full
Dafny-style workflow, in plain TypeScript functions:

```typescript
interface Node { value: number; next: Node | null; prev: Node | null }

// The doubly-linked coherence invariant — a plain recursive function
function validChain(n: Node | null): boolean {
  return n === null ? true
    : n.next === null ? true
    : n.next.prev === n && validChain(n.next)
}

// Which nodes validChain reads — enables frame reasoning
function inChain(n: Node | null, x: Node): boolean {
  return n === null ? false : n === x || inChain(n.next, x)
}
footprint(validChain, inChain)

// The LRU cache's core operation: unlink + relink at front
export function moveToFront(head: Node, node: Node, prevN: Node): void {
  requires(/* bounded window: head.prev === null, prevN.next === node, ... */)
  ensures(node === head || validChain(node))
  if (node === head) return
  prevN.next = node.next     // write THROUGH a pointer
  node.prev = null
  node.next = head
  head.prev = node           // forget this line → refuted with a counterexample
}

// A LOOP mutating a field the invariant READS — preserved because the
// victim is provably OUTSIDE the chain (ownership via footprint)
export function evictOthers(head: Node, victim: Node, n: number): void {
  requires(validChain(head))
  requires(!inChain(head, victim))
  requires(nonNegative(n))
  ensures(validChain(head))
  while (n > 0) {
    invariant(() => validChain(head))
    decreases(() => n)
    victim.prev = null
    n = n - 1
  }
}
```

Each loop produces four obligations: invariant at entry, invariant preserved
by an arbitrary iteration, termination measure bounded and decreasing, and
the code after the loop resumes under `invariant ∧ ¬condition`. The classic
LRU bug — forgetting the head back-pointer, whose symptom appears operations
later as silently dropped entries — is refuted at the source. See
[`examples/lru.ts`](examples/lru.ts).

Sequences close the abstraction-function loop from the Dafny playbook
([`examples/cons.ts`](examples/cons.ts)):

```typescript
function list(n: Node | null): number[] {
  return n === null ? [] : [n.value, ...list(n.next)]
}

export function cons(x: number, tail: Node | null): Node {
  ensures(tail === null
    ? seqEq(list(output()), [x])
    : seqEq(list(output()), [x, ...list(tail)]))   // ✓ list(cons(x,t)) = [x] ++ list(t)
  return { value: x, next: tail }
}
```

All of this runs on ground instantiation — no quantifiers — so solve times
stay in single-digit milliseconds and results are deterministic.

## Counterexamples as Regression Tests

```bash
theorem verify --gen-tests src/
```

Every disproved obligation carries the exact input that breaks the contract.
`--gen-tests` turns each one into a `node:test` case calling the real
function with those values and asserting the contract — **RED until the bug
is fixed**, then a permanent regression guard:

```typescript
// .theorem/regressions/basics.regression.test.ts (auto-generated)
test('buggySubtract: nonNegative(output())', () => {
  const __r = buggySubtract(0.25, 0.5)
  assert.ok(__r >= 0, "contract violated: nonNegative(output())")
})
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
import { declare, requires, ensures, nonNegative, output } from 'theoremts'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})
```

```typescript
// contracts/api.contracts.ts
import { declare, ensures, nonNegative, output } from 'theoremts'

declare(getBalance, (userId: string): number => {
  ensures(nonNegative(output()))
})
```

Auto-discovered from `node_modules/@theorem-contracts/*` or configured:

```typescript
// theorem.config.ts
import { defineConfig } from 'theoremts'
export default defineConfig({
  contracts: ['contracts/*.contracts.ts'],
})
```

Publishable as npm packages — `@theorem-contracts/bignumber`, `@theorem-contracts/decimal`, etc.

## Configuration

```typescript
// theorem.config.ts
import { defineConfig } from 'theoremts'
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
import { theoremVite } from 'theoremts/vite'
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
