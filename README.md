# Theorem

**Formal verification for TypeScript.** Prove your code is correct for *all* possible inputs — not by testing samples, but by mathematical proof with the [Z3](https://github.com/Z3Prover/z3) SMT solver.

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

Every contract is a **no-op at runtime**. Theorem is pure static analysis: your bundles ship exactly the code you wrote.

---

## Table of contents

- [Why Theorem](#why-theorem)
- [Quick start](#quick-start)
- [The five commands](#the-five-commands)
- [Writing contracts](#writing-contracts)
- [Cross-function verification](#cross-function-verification)
- [Loops](#loops)
- [Schemas as contracts](#schemas-as-contracts)
- [Class invariants](#class-invariants)
- [Verified mutation](#verified-mutation)
- [Counterexamples as regression tests](#counterexamples-as-regression-tests)
- [Zero-annotation analysis: scan, suggest, infer](#zero-annotation-analysis-scan-suggest-infer)
- [Editor integration](#editor-integration)
- [External library contracts](#external-library-contracts)
- [Configuration, CI, bundlers](#configuration-ci-bundlers)
- [How it works](#how-it-works)

---

## Why Theorem

**Tests check examples. Theorem checks all inputs.**

```
Unit test:   checks safeDivide(10, 2) → 5             (1 case)
fast-check:  checks 1000 random combinations           (1000 cases)
Theorem:     proves NO input can violate the contract  (all cases)
```

The difference matters for the bugs nobody writes a test for. A shipping calculator with tiers, surcharges, and a loyalty discount:

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

Five unit tests pass. Then:

```
$ theorem verify shipping.ts
  calculateShipping
    ✗  output() > 0
       counterexample: weight = 1, distance = 1, memberYears = 51, result = -0.02
```

A 51-year member gets a 102% discount → negative shipping cost. Z3 finds the exact input in milliseconds. No developer writes a test for a 51-year member — but the code allows it.

Everything in this README passes `tsc --strict`. The bugs live in the arithmetic, not the types — only the solver separates safe from broken.

## Quick start

```bash
npm install -D theoremts theoremts-cli
```

```bash
theorem verify src/            # prove annotated contracts
theorem scan src/              # find risks with zero annotations
```

For inline squiggles in VS Code / Cursor, see [Editor integration](#editor-integration).

## The five commands

| Command | Annotations needed | What it does |
|---|---|---|
| `theorem verify` | contracts | Proves `requires`/`ensures`/`invariant` with Z3; counterexamples on failure |
| `theorem scan` | none | Detects division by zero, negative sqrt, null access, contract violations at call sites |
| `theorem suggest` | none | Proposes contracts: "if you add `requires(X)`, then `ensures(Y)` becomes provable" |
| `theorem infer` | none | Extracts contracts from existing guards, throws, and schemas into `.theorem/contracts/` |
| `theorem prisma` | none | Generates schemas from `schema.prisma` — DB column facts flow into proofs |

Useful flags: `--strict` (exit 1 on failure, for CI), `--watch`, `--format sarif`, `--gen-tests`, `--debug`.

## Writing contracts

**`requires`** — what the function demands (precondition).
**`ensures`** — what the function guarantees (postcondition).

```typescript
function applyDiscount(price: number, percent: number): number {
  requires(positive(price))
  requires(between(percent, 0, 100))
  ensures(nonNegative(output()))
  ensures(output() <= price)
  return price * (1 - percent / 100)
}
```

If `requires` is violated → **caller's fault**. If `ensures` doesn't hold → **implementation bug**. A missing precondition is itself a finding:

```typescript
function applyBonus(salary: number, bonusPercent: number): number {
  requires(positive(salary))
  // missing: requires(nonNegative(bonusPercent))
  ensures(nonNegative(output()))
  return salary + salary * bonusPercent / 100
}
// ✗ counterexample: salary = 1, bonusPercent = -200, result = -1
```

### Reference

| Function | Purpose |
|---|---|
| `requires(pred)` | Precondition |
| `ensures(pred)` | Postcondition — sees the final state |
| `output()` | The return value, inside `ensures` |
| `check(pred)` | Mid-body assertion — sees the state *after* mutations (SSA-aware) |
| `assume(pred)` | Taken as fact without proof (external guarantees) |
| `invariant(() => pred)` | Loop invariant |
| `decreases(expr)` | Termination measure for loops and recursion |
| `old(expr)` | Value at function entry |
| `conserved(...vals)` | Sum preserved across mutation |
| `modifies(...objs)` | Which objects a function may write ([Verified mutation](#verified-mutation)) |
| `footprint(spec, member)` | Pairs an invariant with its read-set ([Verified mutation](#verified-mutation)) |
| `declare(fn, spec)` | Contract for a function you don't own ([External library contracts](#external-library-contracts)) |

Predicate helpers: `positive(x)`, `nonNegative(x)`, `negative(x)`, `between(x, min, max)`, `integer(x)` / `Number.isInteger(x)`.

### State, before and after

`old()` refers to values at function entry; `check()` sees the current SSA state, like Dafny's `assert`:

```typescript
function processPayroll(baseSalary: number): number {
  requires(positive(baseSalary))

  if (baseSalary > 10000) baseSalary = 10000    // cap

  check(between(baseSalary, 0, 10000))          // ✓ sees the value after the cap

  return baseSalary * 0.9
}
```

### Recursion terminates

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

### Object returns and closures

```typescript
function calculateTax(income: number, rate: number): { gross: number; tax: number; net: number } {
  requires(positive(income))
  requires(between(rate, 0, 0.5))
  ensures(output().gross === output().tax + output().net)
  const tax = income * rate
  return { gross: income, tax, net: income - tax }
}

function createDiscount(rate: number) {
  requires(between(rate, 0, 1))
  return (price: number) => {
    requires(positive(price))
    ensures(output() <= price)
    return price * (1 - rate)      // captured variable carries its contract
  }
}
```

### Alternative styles

```typescript
// Decorators (class methods)
class Calculator {
  @requires(positive(b))
  @ensures(nonNegative(output()))
  divide(a: number, b: number): number { return a / b }
}

// proof() wrapper (const/arrow functions)
export const clamp = proof(
  (value: number, min: number, max: number) =>
    value < min ? min : value > max ? max : value,
  requires(({ min, max }) => min <= max),
  ensures(({ result, min }) => result >= min),
)
```

Contracts can also live in separate `*.proof.ts` files, keeping source untouched — `theorem verify` picks up both.

## Cross-function verification

Theorem is modular, like Dafny: when `A` calls `B`, it proves `A`'s arguments satisfy `B`'s `requires`, and assumes `B`'s `ensures` for `A`'s own proof. Call sites outside verified code are checked too:

```typescript
function unitPrice(total: number, quantity: number): number {
  requires(positive(quantity))
  return safeDivide(total, quantity)   // ✓ quantity satisfies positive(b)
}

safeDivide(100, 0)                     // ✗ call-site check: violates positive(b)
```

```
  unitPrice
    ✓  call safeDivide(total, quantity): positive(b)
       using: requires: positive(quantity)

  (call-site checks)
    ✗  safeDivide(100, 0): positive(b)
       violation confirmed (literal values)
```

Any call pattern works — `service.calculate(x)`, `this.payments.process(x)`.

## Loops

A `while` loop is verified by **havoc + invariant**: each `invariant` must hold at loop entry, be preserved by one arbitrary iteration, and after the loop the *only* known facts are `invariant ∧ ¬condition`. `decreases` proves termination. Four obligations per loop, all discharged by the solver:

```typescript
processUniformBatch(txCount: number, amountPerTx: number): number {
  requires(Number.isInteger(txCount))
  requires(positive(txCount))
  requires(positive(amountPerTx))
  requires(txCount * amountPerTx <= this.balance)
  ensures(this.balance === old(this.balance) - (txCount * amountPerTx))
  ensures(output() === txCount * amountPerTx)

  let remaining = txCount
  let totalSent = 0
  while (remaining > 0) {
    invariant(() => Number.isInteger(remaining))
    invariant(() => remaining >= 0)
    invariant(() => totalSent === (txCount - remaining) * amountPerTx)
    invariant(() => this.balance === old(this.balance) - totalSent)
    invariant(() => this.totalDistributed === old(this.totalDistributed) + totalSent)
    decreases(() => remaining)

    this.balance -= amountPerTx
    this.totalDistributed += amountPerTx
    totalSent += amountPerTx
    remaining--
  }
  return totalSent
}
```

The discipline is honest: state the loop writes is havoced, so an invariant you forget is a counterexample, not a silent assumption. Drop the `totalDistributed` invariant above and the class invariant at method exit is refuted with concrete values. See [`examples/advanced.ts`](examples/advanced.ts).

Loop contracts may also sit directly **before** the `while` (Dafny-style header) — same semantics as the first statements of the body.

### Invariants that write themselves

Two engines take the boilerplate away:

- **Houdini (automatic, default on)** — the requires/ensures conjuncts that mention loop-written state become guess-and-check invariant candidates. Each must prove loop entry *and* preservation; failures are dropped and the check reiterates; survivors show up marked `(auto)`:

  ```
  ✓  loop invariant (entry): forall(users, (u) => u.balance >= 0)  (auto)
  ✓  loop invariant (preserved): forall(users, (u) => u.balance >= 0)  (auto)
  ```

  Nothing is ever assumed without both obligations proved — a debiting loop simply loses its candidate and refutes honestly.

- **Spacer inference (CHC)** — for invariants that appear in *no* contract (linear combinations like `paid + 3 * remaining === 3 * total`), the loop is encoded as Horn clauses and Z3's Spacer engine synthesizes the inductive invariant. Surfaced two ways: `theorem suggest` prints it, and in the editor the failing loop gets a **quick-fix (💡) that inserts the inferred invariants** one click away.

## Schemas as contracts

Your validation schemas already state your invariants — Theorem reads them. `Schema.parse()` throws on invalid data, so after the parse the schema's refinements are mathematical facts. **Zero annotations needed**:

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

`z.number().int()` gives Z3 the integer fact TypeScript's `number` can't express. Schemas imported from other files are resolved automatically. **Effect Schema** has full parity: `Schema.decodeUnknownSync`, `Schema.Struct` refinements, `Schema.filter`.

### `.refine()` is a model invariant

A `.refine()` predicate is assumed wherever the schema is parsed — and **proved for every function that returns the type**:

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

### Refinement types

A parameter typed with a schema-derived alias carries the schema as its contract — assumed inside the function, **proved at every call site**:

```typescript
const RateSchema = z.number().gt(0).lte(1).brand()
type Rate = z.output<typeof RateSchema>

export function applyRate(amount: number, rate: Rate): number {
  return amount / rate            // ✓ proved: the TYPE says rate > 0
}

applyRate(100, 0 as Rate)         // ✗ caught at the call site —
                                  //   `as` satisfies tsc, not Z3
```

### Arrays in schemas

Element-level constraints become quantified facts, and the canonical Set-size refine becomes distinctness:

```typescript
const OrderSchema = z.object({
  scores: z.array(z.number().min(1)),                                // → forall(scores, v => v >= 1)
  users:  z.array(z.object({ balance: z.number().nonnegative() })),  // → forall(users, u => u.balance >= 0)
  ids:    z.array(z.number()).refine(a => new Set(a).size === a.length),  // → unique(ids)
})
```

After the parse, `order.scores[k] >= 1` proves (with `k` in bounds), and `order.ids[0] !== order.ids[1]` follows from the refine. Effect Schema mirrors all of it (`Schema.Array(Schema.Number.pipe(Schema.positive()))`, `Schema.Array(Schema.Struct({...}))`).

### Boundaries: tRPC and Prisma

`t.procedure.input(Schema).mutation(handler)` — the handler assumes the input schema's constraints automatically (tRPC validates before invoking it). Zod or Effect Schema.

```bash
theorem prisma prisma/schema.prisma    # → theorem-schemas.ts
```

Generates row schemas from your database schema: `Int` columns become integer facts, nullable columns become `.nullable()`. Column constraints flow into proofs.

## Class invariants

Declared once on the class — assumed at every method entry, **proved at every exit** (mutations of `this.*` are tracked, including through loops), and the constructor must establish it:

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

## Verified mutation

When a function mutates fields of object parameters, Theorem switches to a heap encoding (Z3 arrays). Object references become solver values, so **aliasing is a case the solver explores** — not an assumption it silently makes:

```typescript
export function drainUnsafe(from: Account, to: Account): void {
  requires(nonNegative(from.value))
  requires(nonNegative(to.value))
  ensures(to.value === old(to.value) + old(from.value))
  to.value = to.value + from.value
  from.value = 0
}
// ✗ counterexample: from = 2, to = 2  — the SAME reference!
//   Aliased, both writes hit one cell: the value doubles, then zeroes.
//   Add requires(from !== to) and it proves.
```

`old(x.f)` reads the pre-state heap; `modifies(a, b)` declares which objects may be written — an undeclared write is a violation.

### Recursive invariants over linked structures

Plain recursive TypeScript functions serve as spec predicates over the mutable heap — the full Dafny-style workflow:

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
  prevN.next = node.next     // a write THROUGH a pointer
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

The classic LRU bug — forgetting the head back-pointer, whose symptom appears operations later as silently dropped entries — is refuted at the source ([`examples/lru.ts`](examples/lru.ts)).

Sequences close the abstraction-function loop from the Dafny playbook ([`examples/cons.ts`](examples/cons.ts)):

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

All of this runs on ground instantiation — **no quantifiers** — so solve times stay in single-digit milliseconds and results are deterministic.

## Collection vocabulary

One word per property, over arrays of numbers or objects:

```typescript
requires(unique(users))                         // pairwise-distinct OBJECTS — the anti-aliasing hypothesis
requires(uniqueBy(users, (u) => u.id))          // pairwise-distinct field values
requires(sortedBy(users, (u) => u.balance))     // ordered by a field
requires(exists(users, (u) => u.id === wanted)) // membership
requires(forall(users, (u) => u.balance >= 0))  // every element
```

And the folds — `sumBy` / `countBy` — make conservation provable:

```typescript
export function transfer(users: Account[], i: number, j: number, amt: number): void {
  requires(unique(users))
  // ... bounds on i, j ...
  ensures(sumBy(users, (u) => u.balance) === old(sumBy(users, (u) => u.balance)))
  users[i]!.balance = users[i]!.balance - amt
  users[j]!.balance = users[j]!.balance + amt      // ✓ conserves — even when i === j
}
// change the credit to `+ amt + 1` → refuted: money out of thin air
```

Every indexed write moves the sum by exactly its cell delta — an axiom valid only under `requires(unique(users))` (a duplicated reference would count its delta twice; without uniqueness the sum is honestly unconstrained). Two-state quantified contracts compose with loops: `ensures(forall(users, (u) => u.balance >= old(u.balance)))` proves through a crediting loop regardless of aliasing. The full tour: [`examples/collections.ts`](examples/collections.ts) and [`examples/schema-arrays.ts`](examples/schema-arrays.ts).

## Proof-backed editor experience

The TS plugin does more than squiggles:

- **Readable failures** — labeled multi-line messages (`Contract violated:` / `Unmet requires:` / `Call:` / `Counterexample:`), counterexamples that name aliasing (`users[1] = same object as users[0]`) and show per-element fields (`users[1].balance = -100`), and the execution path (`path: line 33: p.kind === "boleto" → not taken`).
- **tsc errors suppressed by proof** — for each `arr[i]`, Theorem proves `0 <= i < arr.length` from your requires; proved accesses have tsc's possibly-undefined error (2532/18048) filtered at exactly that spot. The unverified `!` gives way to a proof — and the error comes back by itself if a requires weakens.
- **Quick-fix invariants** — a failing loop offers a 💡 code action that inserts the Spacer-inferred `invariant(() => ...)` lines.

## Counterexamples as regression tests

```bash
theorem verify --gen-tests src/
```

Every disproved obligation carries the exact input that breaks the contract. `--gen-tests` turns each into a `node:test` case calling the real function with those values — **RED until the bug is fixed**, then a permanent regression guard:

```typescript
// .theorem/regressions/basics.regression.test.ts (auto-generated)
test('buggySubtract: nonNegative(output())', () => {
  const __r = buggySubtract(0.25, 0.5)
  assert.ok(__r >= 0, "contract violated: nonNegative(output())")
})
```

## Zero-annotation analysis: scan, suggest, infer

### scan — find risks now

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

Walks the AST for risky operations (division/modulo by zero, negative sqrt, log of non-positives, null access, contract violations at call sites), then uses Z3 to confirm reachability. Path-sensitive: `if (x > 0) { ... / x }` is encoded as an assumption, not reported.

### suggest — see what would become provable

```bash
theorem suggest src/
```

```
  safeDivide(a, b)
    ?  requires(b !== 0)  — guards division

  average(a, b)
    →  if you add requires(a >= b), then ensures(output() <= a) becomes provable
```

### infer — extract the contracts your code already implies

```bash
theorem infer src/                 # writes to .theorem/contracts/ (gitignored)
theorem infer --dry-run src/       # preview
theorem infer --prove src/         # Z3-verify inferred ensures (slower)
```

Nine strategies: if/throw guards, sentinel returns, arithmetic safety, null safety, array safety, Zod schemas, cross-function propagation, return analysis, relational contracts. Without `--prove` it never touches Z3 — safe to run on any codebase.

## Editor integration

```bash
npm install -D theoremts-ts-plugin
```

```jsonc
// tsconfig.json
{ "compilerOptions": { "plugins": [{ "name": "theoremts-ts-plugin" }] } }
```

Contract violations appear as squiggles with counterexamples in the tooltip, live as you type (VS Code, Cursor, any tsserver editor). Verification runs in a child process — it never blocks the editor.

## External library contracts

Declare contracts for functions you don't own — like `.d.ts` for types, but for logic:

```typescript
// contracts/math.contracts.ts
import { declare, requires, ensures, nonNegative, output } from 'theoremts'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})
```

When both the `declare()` and an implementation exist in the codebase, the contract is **verified against the implementation**. Contract packages (`@theoremts/contracts-*`) are auto-discovered from `node_modules`.

## Configuration, CI, bundlers

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

```yaml
# GitHub Actions
- run: npx theorem verify --strict src/
- run: npx theorem scan --strict --format sarif src/ > theorem.sarif
- uses: github/codeql-action/upload-sarif@v3
  with: { sarif_file: theorem.sarif }
```

Contracts are already no-ops, but bundler plugins can strip them entirely:

```typescript
// vite.config.ts
import { theoremVite } from 'theoremts/vite'
export default { plugins: [theoremVite()] }
// also: theoremts/esbuild, theoremts/tsup
```

## How it works

```
TypeScript source
      ↓
  PARSER      ts-morph + SSA — contracts, function IR, schemas, heap steps
      ↓
  TRANSLATOR  IR → Z3 assertions; cross-function obligations; safety obligations
      ↓
  SOLVER      Z3 (WASM) — UNSAT = proved, SAT = counterexample
      ↓
  REPORTER    CLI / SARIF, with concrete counterexample values
```

To prove `ensures(P)`, Z3 searches for an input where every `requires` holds but `P` fails. If no such input exists (UNSAT), the contract is proved — for all inputs, not a sample. Division safety obligations are generated automatically (Z3 treats division as total; Theorem doesn't let that hide `x / 0`).

The [`examples/`](examples/) directory is a tour of everything above, each file with passing *and* failing cases.

Inspired by [Dafny](https://dafny.org), [Ada/SPARK](https://www.adacore.com/about-spark), and [Frama-C](https://frama-c.com).

## License

MIT
