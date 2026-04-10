# Theorem

Formal verification for TypeScript. Finds bugs your tests miss — mathematically.

```bash
$ theorem scan src/

  src/payments/transfer.ts
    ❌ balance can become negative (amount > balance)
       Counterexample: balance=100, amount=150 → balance=-50
    ❌ amount=NaN causes data corruption
       balance -= NaN → balance becomes NaN

  src/orders/discount.ts
    ❌ discount=150% makes final price negative
       Counterexample: price=100, discount=150 → returns -50

  3 bugs found in 1.2 seconds.
  Your 312 Jest tests caught 0 of these.
```

---

## What is this?

A static analysis tool that uses Z3 (SMT solver) to **prove** TypeScript code is correct — not by testing inputs one at a time, but by mathematically proving properties hold for **all possible inputs**.

```
Jest:          tests specific inputs you think of
               → "these 10 cases pass"

Theorem:       proves properties for ALL possible inputs
               → "no input can ever violate this" (or finds one that does)

TypeScript:    proves types are correct        → removes types from JS output
Theorem:       proves logic is correct          → removes contracts from JS output
```

---

## API

### Installation

```bash
npm install theorem --save-dev
```

### Exports

```typescript
import {
  // Core
  proof,       // wrap/reference a function with contracts
  of,          // create a typed proxy of a class for proof references

  // Contracts
  requires,    // precondition — must be true before execution
  ensures,     // postcondition — must be true after execution
  invariant,   // loop invariant — must be true every iteration
  decreases,   // termination proof — must decrease every iteration
  modifies,    // declares what the function may mutate

  // Quantifiers
  forall,      // universal quantifier — true for ALL items
  exists,      // existential quantifier — true for at least ONE item

  // Helpers
  old,         // value of expression at function entry (before mutation)
  positive,    // x > 0
  nonNegative, // x >= 0
  negative,    // x < 0
  finite,      // !NaN && !Infinity
  between,     // min <= x <= max
  sorted,      // array is sorted ascending
  unique,      // all elements (or element.key) are distinct
  conserved,   // sum of values unchanged after mutation
} from 'theorem'
```

### What each function does

```
proof(fn, ...)       Wrap a function with contracts, or attach contracts to existing function/method.
                     Returns the function unchanged. Contracts exist only for static verification.

of(Class)            Create a typed proxy of a class for referencing methods in proof().
                     No instantiation, just type-safe references with autocomplete.

requires(fn)         Precondition. Must be true BEFORE the function runs.
requires(str)        "This function only works if..."

ensures(fn)          Postcondition. Must be true AFTER the function runs.
ensures(str)         "This function guarantees that..."

invariant(fn)        Loop invariant. Must be true at EVERY iteration.
                     Placed inside while/for loops (needs access to local variables).

decreases(fn)        Termination proof. This expression gets smaller each iteration.
                     If it decreases and is >= 0, the loop must terminate.
                     Placed inside while/for loops.

forall(arr, fn)      Universal quantifier. True if fn(item) is true for ALL items.
                     Used inside requires/ensures/invariant.

exists(arr, fn)      Existential quantifier. True if fn(item) is true for at least ONE item.
                     Used inside requires/ensures/invariant.

old(value)           The value of an expression at function entry (before mutation).
                     Used inside ensures() to compare before/after state.

modifies(...refs)    Declares what the function is allowed to mutate.
                     Anything not listed must remain unchanged.

positive(x)          x > 0. Sugar for common numeric checks.
nonNegative(x)       x >= 0. Balance should never go below zero.
negative(x)          x < 0.
finite(x)            !NaN && !Infinity. Guards against corrupt number values.
between(x, min, max) min <= x <= max. Range check.
sorted(arr)          Array is sorted ascending. Expands to forall with i-1 <= i.
unique(arr, fn?)     All elements are distinct. Optional key extractor.
conserved(...vals)    Sum of values is unchanged after mutation (uses old() internally).
```

### All contracts are removed from JS output

```typescript
// TypeScript source
import { proof, requires, ensures } from 'theorem'

const add = proof(
  (a: number, b: number) => a + b,
  requires(({ a }) => a >= 0),
  ensures(({ result }) => result >= 0),
)

// JavaScript output (contracts stripped, like type annotations)
const add = (a, b) => a + b
```

---

## Usage

### Inline — const/arrow functions

```typescript
import { proof, requires, ensures, forall, positive, nonNegative, between, conserved, finite } from 'theorem'

const applyDiscount = proof(
  (price: number, percent: number) => price * (1 - percent / 100),
  requires(({ price }) => positive(price)),
  requires(({ percent }) => between(percent, 0, 100)),
  ensures(({ result }) => nonNegative(result)),
  ensures(({ result, price }) => result <= price),
)

const transfer = proof(
  (from: Account, to: Account, amount: number) => {
    from.balance -= amount
    to.balance += amount
  },
  requires(({ amount }) => positive(amount)),
  requires(({ amount }) => finite(amount)),
  requires(({ from, amount }) => from.balance >= amount),
  modifies('from', 'to'),
  ensures(({ from }) => nonNegative(from.balance)),
  ensures(({ from, to }) => conserved(from.balance, to.balance)),
)

const processOrder = proof(
  (items: OrderItem[]) =>
    items
      .filter(i => i.quantity > 0)
      .map(i => i.price * i.quantity)
      .reduce((sum, val) => sum + val, 0),
  requires(({ items }) => items.length > 0),
  requires(({ items }) => forall(items, i => positive(i.price))),
  ensures(({ result }) => positive(result)),
)
```

### Inline — function declarations with proof.fn()

```typescript
import { proof, requires, ensures, invariant, decreases, forall } from 'theorem'

function binarySearch(a: number[], key: number): number {
  return proof.fn(
    () => {
      let lo = 0
      let hi = a.length
      while (lo < hi) {
        invariant(() => lo >= 0 && hi <= a.length)
        invariant(() => lo <= hi)
        decreases(() => hi - lo)

        const mid = Math.floor(lo + (hi - lo) / 2)
        if (a[mid] < key) lo = mid + 1
        else if (a[mid] > key) hi = mid
        else return mid
      }
      return -1
    },
    requires(() => a.length > 0),
    requires(() => forall(a, (item, i) => i === 0 || a[i - 1] <= a[i])),
    ensures(({ result }) => result === -1 || a[result] === key),
  )
}
```

### Inline — class methods with proof.fn()

```typescript
class PaymentService {
  transfer(from: Account, to: Account, amount: number) {
    return proof.fn(
      () => {
        from.balance -= amount
        to.balance += amount
      },
      requires(() => amount > 0),
      requires(() => from.balance >= amount),
      ensures(() => from.balance >= 0),
      ensures("money is conserved"),
    )
  }

  applyDiscount(price: number, percent: number) {
    return proof.fn(
      () => price * (1 - percent / 100),
      requires(() => price > 0),
      requires(() => percent >= 0 && percent <= 100),
      ensures(({ result }) => result >= 0),
    )
  }
}
```

### Separate file — functions

```typescript
// discount.ts — clean code, no theorem imports
export function applyDiscount(price: number, percent: number) {
  return price * (1 - percent / 100)
}

// discount.proof.ts — contracts
import { proof, requires, ensures } from 'theorem'
import { applyDiscount } from './discount'

proof(applyDiscount,
  requires(({ price }) => price > 0),
  requires(({ percent }) => percent >= 0 && percent <= 100),
  ensures(({ result }) => result >= 0),
  ensures(({ result, price }) => result <= price),
)
```

### Separate file — classes

```typescript
// payment.service.ts — clean code
export class PaymentService {
  transfer(from: Account, to: Account, amount: number) {
    from.balance -= amount
    to.balance += amount
  }

  refund(order: Order, account: Account) {
    account.balance += order.total
    order.status = 'refunded'
  }
}

// payment.service.proof.ts — contracts
import { proof, of, requires, ensures, modifies, positive, nonNegative, conserved } from 'theorem'
import { PaymentService } from './payment.service'

const service = of(PaymentService)

proof(service.transfer,
  requires(({ amount }) => positive(amount)),
  requires(({ from, amount }) => from.balance >= amount),
  modifies('from', 'to'),
  ensures(({ from }) => nonNegative(from.balance)),
  ensures(({ from, to }) => conserved(from.balance, to.balance)),
)

proof(service.refund,
  requires(({ order }) => order.status === 'paid'),
  requires(({ order }) => positive(order.total)),
  ensures(({ account }) => nonNegative(account.balance)),
  ensures(({ order }) => order.status === 'refunded'),
)
```

### Separate file — NgRx reducers

```typescript
// book.reducer.proof.ts
import { proof, ensures } from 'theorem'
import { bookReducer, addBook, removeBook } from './book.reducer'

proof(bookReducer, addBook,
  ensures(({ next, prev }) => next.books.length === prev.books.length + 1),
  ensures("no duplicate ids"),
)

proof(bookReducer, removeBook,
  ensures(({ next, prev, id }) => !next.books.some(b => b.id === id)),
  ensures(({ next, prev }) => next.books.length === prev.books.length - 1),
)
```

### String contracts

For complex properties that are hard to express as code:

```typescript
proof(service.transfer,
  requires(({ amount }) => amount > 0),          // expression — precise
  ensures("money is conserved"),                   // string — engine parses
  ensures("no side effects beyond from and to"),   // string — complex property
)
```

The engine translates known phrases to Z3 formulas internally:

```
"money is conserved"                → sum of all balances unchanged
"a is sorted"                       → forall(a, (x, i) => i === 0 || a[i-1] <= a[i])
"no duplicate ids"                  → forall(a, (x, i) => forall(a, (y, j) => i === j || x.id !== y.id))
"result contains no duplicates"     → all elements are unique
"all items have positive price"     → forall(items, i => i.price > 0)
```

Pattern matching on known phrases. Expandable dictionary.

---

## Branches and Loops

### Branches — the engine handles automatically

The engine analyzes every branch via AST. No labels or annotations needed:

```typescript
const processPayment = proof(
  (order: Order, account: Account) => {
    if (order.type === 'credit') {
      const fee = order.total * 0.03
      account.balance -= (order.total + fee)
      return { charged: order.total + fee, fee }
    }

    if (order.type === 'pix') {
      const discount = order.total * 0.05
      account.balance -= (order.total - discount)
      return { charged: order.total - discount, discount }
    }

    account.balance -= order.total
    return { charged: order.total, fee: 0 }
  },
  requires(({ order }) => order.total > 0),
  requires(({ account, order }) => account.balance >= order.total),
  ensures(({ account }) => account.balance >= 0),
  ensures(({ result }) => result.charged > 0),
)

// Engine verifies EACH branch automatically:
//
// branch "credit":  charged = total + fee, fee = total * 0.03
//   → total > 0, so fee > 0, so charged > total > 0 ✅
//
// branch "pix":     charged = total - discount, discount = total * 0.05
//   → charged = total * 0.95, total > 0, so charged > 0 ✅
//
// branch default:   charged = total
//   → total > 0 ✅
//
// If any branch violates ensures, the engine shows which:
//   ❌ ensures(result.charged > 0) FAILED
//      in branch: order.type === 'pix' (line 8)
//      counterexample: ...
```

### Loops — invariant/decreases inline (needs local variables)

```typescript
const binarySearch = proof(
  (a: number[], key: number) => {
    let lo = 0
    let hi = a.length
    while (lo < hi) {
      invariant(() => lo >= 0 && hi <= a.length)
      invariant(() => lo <= hi)
      decreases(() => hi - lo)

      const mid = Math.floor(lo + (hi - lo) / 2)
      if (a[mid] < key) lo = mid + 1
      else if (a[mid] > key) hi = mid
      else return mid
    }
    return -1
  },
  requires(({ a }) => a.length > 0),
  requires(({ a }) => forall(a, (item, i) => i === 0 || a[i - 1] <= a[i])),
  ensures(({ result, a, key }) => result === -1 || a[result] === key),
)
```

The engine encourages array methods over loops when possible:

```bash
$ theorem scan src/

  src/orders/process.ts:14
    ⚠️ while loop could be replaced with:
       items.filter(i => i.active).map(i => i.total).reduce((s, t) => s + t, 0)
       Array methods are easier to verify and prove correct.
       
  src/search/binary.ts:5
    ✅ while loop cannot be simplified — invariant/decreases recommended
```

---

## Three Modes

### 1. Scan (zero effort)

No annotations needed. Engine infers risks from types and operations.

```bash
$ theorem scan src/
```

Engine knows:
- `number` in TS allows negative, NaN, Infinity, fractional values
- Subtraction can produce negative results
- Division can produce NaN (0/0) or Infinity (n/0)
- Array access can be out of bounds
- `.sort()` mutates original array
- Property access on possibly-null values crashes

Classifies functions by risk:
- 🔴 CRITICAL: manipulates money (balance, amount, price, total) or auth (role, permission) without guards
- 🟡 HIGH: complex arithmetic/branching without bounds checking
- 🟢 LOW: simple operations with minor edge cases

### 2. Suggest (low effort)

Engine generates guards and contracts automatically.

```bash
$ theorem suggest src/payments/transfer.ts

  transfer() needs validation. Apply?

  + requires(({ amount }) => amount > 0)
  + requires(({ amount }) => Number.isFinite(amount))
  + requires(({ from, amount }) => from.balance >= amount)
  ... (body unchanged)
  + ensures(({ from }) => from.balance >= 0)

  [A]ccept  [E]dit  [S]kip  [C]ustomize
```

`C` accepts natural language rules:
```
> "maximum transfer amount is 50000"
> "cannot transfer to same account"
```

### 3. Verify (full contracts)

Developer writes contracts. Engine proves them with Z3.

```bash
$ theorem verify src/
```

---

## CLI

```bash
# Scan — find risks without any annotations
theorem scan src/
theorem scan src/payments/

# Suggest — auto-generate contracts
theorem suggest src/payments/transfer.ts

# Verify — prove annotated contracts
theorem verify src/
theorem verify src/payments/transfer.ts

# Watch — verify on file change
theorem verify --watch src/

# CI mode — exit code 1 if any proof fails
theorem verify --strict src/
```

---

## Architecture

### Pipeline

```
TypeScript source (.ts / .proof.ts)
       │
       ▼
  ┌──────────┐
  │  PARSER   │  ts-morph reads AST
  │           │  extracts: functions, params, types, operations
  │           │  extracts: proof() / proof.fn() calls
  │           │  extracts: requires/ensures/invariant/decreases
  │           │  extracts: .proof.ts files and maps to source
  └────┬──────┘
       │  Function IR (intermediate representation)
       ▼
  ┌──────────────┐
  │  TRANSLATOR   │  converts TS operations → Z3 assertions
  │               │  converts contracts → Z3 formulas
  │               │  converts string contracts → Z3 (pattern matching)
  │               │  converts destructured params → Z3 variables
  └──────┬───────┘
         │  Z3 assertions
         ▼
  ┌──────────┐
  │  SOLVER   │  Z3 checks: can any input violate the contracts?
  │  (Z3)     │  UNSAT = proved (no violation possible)
  │           │  SAT = disproved (counterexample found)
  └────┬─────┘
       │  Results
       ▼
  ┌──────────────┐
  │  REPORTER     │  formats results as CLI output
  │               │  counterexamples with concrete values
  │               │  identifies which branch failed
  │               │  suggested fixes
  │               │  SARIF format for GitHub code scanning
  └──────────────┘
```

### Project structure

```
theorem/
├── packages/
│   ├── core/                      # core library
│   │   ├── src/
│   │   │   ├── parser/
│   │   │   │   ├── extractor.ts   # ts-morph: extract proof()/proof.fn() calls
│   │   │   │   ├── ir.ts          # intermediate representation types
│   │   │   │   ├── proof-file.ts  # parse .proof.ts files, map to source
│   │   │   │   ├── ignore.ts      # parse .theoremignore
│   │   │   │   └── strings.ts     # parse string contracts to structured form
│   │   │   │
│   │   │   ├── translator/
│   │   │   │   ├── index.ts       # orchestrate translation
│   │   │   │   ├── arithmetic.ts  # number ops → Z3
│   │   │   │   ├── comparison.ts  # comparisons → Z3
│   │   │   │   ├── boolean.ts     # logical ops → Z3
│   │   │   │   ├── branch.ts      # if/else → Z3 ITE (automatic branch analysis)
│   │   │   │   ├── loop.ts        # while/for → Z3 (invariant + decreases)
│   │   │   │   ├── array.ts       # array ops → Z3 array theory
│   │   │   │   ├── null.ts        # null/undefined → Z3 option type
│   │   │   │   ├── string.ts      # string ops → Z3 string theory
│   │   │   │   └── quantifier.ts  # forall/exists → Z3 quantifiers
│   │   │   │
│   │   │   ├── solver/
│   │   │   │   ├── z3.ts          # Z3 interface via z3-solver npm
│   │   │   │   └── result.ts      # proved / disproved / unknown types
│   │   │   │
│   │   │   ├── scanner/
│   │   │   │   ├── risk.ts        # classify functions by risk level
│   │   │   │   ├── heuristics.ts  # detect financial/auth/arithmetic patterns
│   │   │   │   └── infer.ts       # infer contracts from types + operations
│   │   │   │
│   │   │   ├── suggester/
│   │   │   │   ├── guards.ts      # generate runtime guards
│   │   │   │   ├── contracts.ts   # generate contract annotations
│   │   │   │   └── natural.ts     # parse natural language rules
│   │   │   │
│   │   │   └── reporter/
│   │   │       ├── cli.ts         # terminal output formatting
│   │   │       ├── json.ts        # machine-readable output
│   │   │       └── sarif.ts       # SARIF format for GitHub code scanning
│   │   │
│   │   ├── package.json
│   │   └── tsconfig.json
│   │
│   ├── runtime/                   # npm package developers import
│   │   ├── src/
│   │   │   ├── index.ts           # no-op core functions
│   │   │   └── helpers.ts         # positive, nonNegative, sorted, etc.
│   │   ├── index.d.ts             # type declarations
│   │   └── package.json           # published as 'theorem'
│   │
│   ├── cli/                       # CLI binary
│   │   ├── src/
│   │   │   ├── commands/
│   │   │   │   ├── scan.ts
│   │   │   │   ├── suggest.ts
│   │   │   │   ├── verify.ts
│   │   │   │   └── watch.ts
│   │   │   └── index.ts
│   │   └── package.json           # published as 'theorem-cli'
│   │
│   ├── plugins/                   # bundler plugins
│   │   ├── vite.ts                # theorem/vite
│   │   ├── esbuild.ts             # theorem/esbuild
│   │   └── tsup.ts                # theorem/tsup
│   │
│   ├── eslint-plugin/             # ESLint integration (later)
│   │
│   └── vscode-extension/          # VSCode extension (later)
│
├── test/
│   ├── fixtures/                  # TS files with known bugs for testing
│   │   ├── transfer.ts
│   │   ├── discount.ts
│   │   ├── permissions.ts
│   │   ├── binary-search.ts
│   │   └── null-deref.ts
│   │
│   └── expected/                  # expected verification results
│
├── docs/
│   ├── getting-started.md
│   ├── api-reference.md
│   ├── how-it-works.md
│   └── examples/
│
├── turbo.json
├── package.json
└── README.md
```

### Runtime package (what developers import)

```typescript
// packages/runtime/src/index.ts

// All functions are no-ops at runtime.
// They exist for: type checking (tsc), static analysis (theorem), stripping at build.

export function proof<TArgs extends any[], TReturn>(
  fn: (...args: TArgs) => TReturn,
  ...contracts: Contract[]
): (...args: TArgs) => TReturn
export function proof<T>(
  target: T,
  ...contracts: Contract[]
): void
export function proof(
  reducer: any,
  action: any,
  ...contracts: Contract[]
): void
export function proof(targetOrFn: any, ...rest: any[]): any {
  if (typeof targetOrFn === 'function' && rest.length > 0 && rest[0]?.__type) {
    // proof(fn, requires(...), ensures(...)) — return fn unchanged
    return targetOrFn
  }
  // proof(existingFn, ...) or proof(Class, method, ...) — no-op
}

proof.fn = <TReturn>(
  fn: () => TReturn,
  ...contracts: Contract[]
): TReturn => {
  return fn()
}

export function of<T>(cls: new (...args: any[]) => T): T {
  return new Proxy({} as T, {
    get: (_, prop) => prop,
  })
}

export function requires(condition: (params: any) => boolean): PreCondition
export function requires(fn: () => boolean): PreCondition
export function requires(description: string): PreCondition
export function requires(_: any): PreCondition {
  return { __type: 'requires' } as any
}

export function ensures(condition: (params: any) => boolean): PostCondition
export function ensures(fn: () => boolean): PostCondition
export function ensures(description: string): PostCondition
export function ensures(_: any): PostCondition {
  return { __type: 'ensures' } as any
}

export function invariant(condition: () => boolean): Invariant
export function invariant(description: string): Invariant
export function invariant(_: any): Invariant {
  return { __type: 'invariant' } as any
}

export function decreases(expression: () => number): Decreases
export function decreases(_: any): Decreases {
  return { __type: 'decreases' } as any
}

export function modifies(...refs: string[]): Modification {
  return { __type: 'modifies', refs } as any
}

export function old<T>(value: T): T {
  return value
}

export function forall<T>(arr: T[], predicate: (item: T, index: number) => boolean): boolean {
  return arr.every(predicate)
}

export function exists<T>(arr: T[], predicate: (item: T, index: number) => boolean): boolean {
  return arr.some(predicate)
}
```

### Helpers (convenience functions)

Typed functions that compose naturally inside contracts. Not strings — real values with autocomplete and refactor support.

```typescript
// packages/runtime/src/helpers.ts

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
  return arr.every((item, i) => i === 0 || arr[i - 1] <= item)
}

export function unique<T>(arr: T[], key?: (item: T) => any): boolean {
  const values = key ? arr.map(key) : arr
  return new Set(values).size === values.length
}

export function conserved(...values: number[]): boolean {
  // Engine reads this statically and compares sum(old(values)) === sum(values)
  // At runtime, always returns true (no-op — can't access old values)
  return true
}
```

Helpers compose naturally because they're just boolean functions:

```typescript
// Compose with &&
requires(({ amount }) => positive(amount) && finite(amount))

// Use in forall
requires(({ items }) => forall(items, i => positive(i.price)))

// Reusable contract groups
const financialSafety = [
  requires(({ amount }) => positive(amount) && finite(amount)),
  ensures(({ from }) => nonNegative(from.balance)),
  ensures(({ from, to }) => conserved(from.balance, to.balance)),
]

proof(service.transfer, ...financialSafety)
proof(service.withdraw, ...financialSafety)
proof(service.deposit, ...financialSafety)
```

---

## Configuration

### .theoremignore

File-based ignore, like `.gitignore`. No inline comments in code.

```gitignore
# .theoremignore

# Ignore generated code
src/generated/**

# Ignore test files (they have their own assertions)
**/*.test.ts
**/*.spec.ts

# Ignore specific files
src/legacy/old-module.ts

# Ignore specific functions (file:function format)
src/utils/debug.ts:debugLog
src/utils/debug.ts:prettyPrint

# Ignore specific rules
[NaN-propagation]
src/math/fuzzy.ts

[negative-result]
src/accounting/adjustments.ts:applyCredit
```

The engine reads `.theoremignore` from the project root. Patterns follow `.gitignore` syntax. Function-level ignores use `file:function` format. Rule-level ignores use `[rule-name]` sections.

### theorem.config.ts

```typescript
// theorem.config.ts
import { defineConfig } from 'theorem'

export default defineConfig({
  // What to scan
  include: ['src/**/*.ts'],
  exclude: ['src/generated/**', '**/*.test.ts'],
  proofFiles: ['**/*.proof.ts'],  // where to look for .proof.ts files

  // Scan mode settings
  scan: {
    severity: {
      financial: 'error',     // balance, amount, price → always error
      auth: 'error',          // role, permission → always error
      arithmetic: 'warning',  // division, overflow → warning
      nullability: 'warning', // null/undefined access → warning
    },
    // Custom variable name patterns for risk classification
    patterns: {
      financial: ['balance', 'amount', 'price', 'total', 'cost', 'fee', 'saldo', 'valor'],
      auth: ['role', 'permission', 'privilege', 'admin', 'token', 'permissao'],
    },
  },

  // Verify mode settings
  verify: {
    timeout: 10000,          // ms per function (Z3 can hang on complex proofs)
    strict: false,           // true = exit 1 on any unproved
  },

  // String contract dictionary (extend built-in phrases)
  dictionary: {
    "money is conserved": "sum of all balance fields unchanged",
    "saldo conservado": "sum of all balance fields unchanged",
    "sem duplicatas": "all elements are unique by id",
  },

  // Output
  reporter: 'cli',           // 'cli' | 'json' | 'sarif'
})
```

---

## Build Integration

### Bundler plugin — remove theorem from production builds

Theorem contracts are stripped at build time. Zero runtime overhead.

**Vite:**
```typescript
// vite.config.ts
import { theoremStrip } from 'theorem/vite'

export default {
  plugins: [theoremStrip()],
}
```

**esbuild:**
```typescript
// esbuild.config.ts
import { theoremStrip } from 'theorem/esbuild'

await build({
  plugins: [theoremStrip()],
})
```

**tsup:**
```typescript
// tsup.config.ts
import { theoremStrip } from 'theorem/tsup'

export default {
  esbuildPlugins: [theoremStrip()],
}
```

The plugin:
- Removes all `proof()` wrappers, returning the original function
- Removes all `requires()`, `ensures()`, `invariant()`, `decreases()` calls
- Removes imports from `theorem`
- Removes `.proof.ts` files from the bundle
- Result: zero theorem code in production

### GitHub Action

```yaml
# .github/workflows/theorem.yml
name: Theorem Verification
on: [pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '22'
      - run: npm ci
      - run: npx theorem verify --strict src/
      - run: npx theorem scan src/ --reporter sarif --output theorem.sarif
      - uses: github/codeql-action/upload-sarif@v3
        with:
          sarif_file: theorem.sarif
```

SARIF integration shows findings inline in the GitHub PR diff view.

---

## CLI Output Examples

### theorem scan

```
$ theorem scan src/

  Scanning 347 files, 12,483 functions...

  🔴 CRITICAL

  src/payments/transfer.ts:14  transfer()
    ❌ balance can become negative
       amount: number accepts values > balance
       Counterexample: balance=100, amount=150 → balance=-50
    ❌ amount=NaN corrupts data
       balance -= NaN → balance becomes NaN
       Counterexample: amount=NaN → balance=NaN

  src/auth/permissions.ts:22  setUserRole()
    ❌ privilege escalation possible
       admin can set role to 'superadmin'
       Counterexample: actor.role='admin', newRole='superadmin'

  🟡 HIGH

  src/orders/discount.ts:8  applyDiscount()
    ⚠️ result can be negative
       no upper bound on percent parameter
       Counterexample: price=100, percent=150 → result=-50

  src/orders/shipping.ts:31  calculateShipping()
    ⚠️ division by zero possible
       distance parameter has no guard
       Counterexample: distance=0 → rate/0 = Infinity

  🟢 LOW

  src/utils/format.ts:4  formatCurrency()
    ⚠️ NaN input produces "NaN" string output

  ────────────────────────────────────
  Summary: 4 critical, 2 high, 1 low
  Run 'theorem suggest' to auto-generate fixes
```

### theorem verify

```
$ theorem verify src/

  src/payments/transfer.ts
    ✅ PROVED  transfer()
       ✓ requires: amount > 0
       ✓ requires: from.balance >= amount
       ✓ ensures: from.balance >= 0
       ✓ ensures: money conserved

  src/orders/discount.ts
    ❌ FAILED  applyDiscount()
       ✓ requires: price > 0
       ✓ requires: percent in [0, 100]
       ✗ ensures: result >= 0
         Counterexample: price=0.001, percent=100 → result=0.00
         Note: result is 0, not > 0. Did you mean nonNegative(result)?

  src/search/binary.ts
    ✅ PROVED  binarySearch()
       ✓ requires: array is sorted
       ✓ requires: array not empty
       ✓ ensures: result is -1 or valid index
       ✓ invariant: bounds maintained
       ✓ terminates: hi-lo decreases

  ────────────────────────────────────
  3 functions verified: 2 proved, 1 failed
```

### theorem suggest

```
$ theorem suggest src/payments/transfer.ts

  transfer(from: Account, to: Account, amount: number)

  No contracts found. Detected: financial operation (balance mutation).
  Suggested contracts:

  const transfer = proof(
    (from: Account, to: Account, amount: number) => {
      from.balance -= amount
      to.balance += amount
    },
  + requires(({ amount }) => positive(amount)),
  + requires(({ amount }) => finite(amount)),
  + requires(({ from, amount }) => from.balance >= amount),
  + modifies('from', 'to'),
  + ensures(({ from }) => nonNegative(from.balance)),
  + ensures(({ from, to }) => conserved(from.balance, to.balance)),
  )

  [A]ccept  [E]dit  [S]kip  [C]ustomize

  > C
  Add custom rules (natural language):
  > maximum transfer amount is 50000
  > cannot transfer to same account

  + requires(({ amount }) => amount <= 50000),
  + requires(({ from, to }) => from.id !== to.id),

---

## Translation: TypeScript → Z3

### Arithmetic

```
TS:     a + b                    Z3:  (+ a b)
TS:     a - b                    Z3:  (- a b)
TS:     a * b                    Z3:  (* a b)
TS:     a / b                    Z3:  (/ a b)
TS:     a % b                    Z3:  (mod a b)
TS:     Math.floor(x)            Z3:  (to_int x)
TS:     Math.max(a, b)           Z3:  (ite (> a b) a b)
TS:     Math.min(a, b)           Z3:  (ite (< a b) a b)
TS:     Math.abs(x)              Z3:  (ite (>= x 0) x (- x))
```

### Comparisons

```
TS:     a > b                    Z3:  (> a b)
TS:     a >= b                   Z3:  (>= a b)
TS:     a === b                  Z3:  (= a b)
TS:     a !== b                  Z3:  (not (= a b))
```

### Boolean logic

```
TS:     a && b                   Z3:  (and a b)
TS:     a || b                   Z3:  (or a b)
TS:     !a                       Z3:  (not a)
```

### Branching

```typescript
if (x > 0) { y = x * 2 } else { y = 0 }
// Z3: y = (ite (> x 0) (* x 2) 0)
```

Engine analyzes ALL branches automatically. When ensures() fails, it reports which branch caused the failure with line number and counterexample.

### Loops

```typescript
while (lo < hi) {
  invariant(() => lo >= 0 && hi <= a.length)
  decreases(() => hi - lo)
  // body
}

// Z3 verification strategy:
// 1. Prove: invariant holds BEFORE loop (base case)
// 2. Prove: if invariant + loop condition true → invariant holds after body
// 3. Prove: decreases expression gets smaller each iteration (termination)
// 4. Prove: invariant + negated condition → postcondition
```

### Variables and mutation (SSA)

```typescript
function transfer(from, to, amount) {
  from.balance -= amount
  to.balance += amount
}

// Z3 uses SSA (single static assignment):
// from_balance_0 = symbolic initial value
// from_balance_1 = from_balance_0 - amount
// to_balance_0 = symbolic initial value
// to_balance_1 = to_balance_0 + amount
//
// ensures(({ from }) => from.balance >= 0) becomes:
// (assert (not (>= from_balance_1 0)))
// check-sat → UNSAT means proved
```

### Number type handling

```
TypeScript 'number' is IEEE 754 double. Engine handles:

Finite values:      Z3 Real sort (rational arithmetic)
NaN:                Z3 separate boolean flag (isNaN_x)
Infinity:           Z3 separate boolean flag (isInf_x)
Integer check:      (= x (to_int x))

In scan mode (no annotations):
  Every 'number' parameter is assumed to potentially be NaN/Infinity
  Engine checks: "can NaN/Infinity reach this operation?"
```

### Array methods semantics

```
Engine has built-in understanding of:

.sort()          → result is sorted, MUTATES original
[...a].sort()    → result is sorted, original intact
.filter(fn)      → result is subset, length <= original, all items match fn
.map(fn)         → result has same length, each item is fn(original)
.reduce(fn, init)→ result is accumulation
.find(fn)        → result matches fn or is undefined
.push(x)         → length increases by 1, MUTATES
.slice(a, b)     → length = b - a, does not mutate
.includes(x)     → boolean, equivalent to exists()
```

### Destructured params translation

```typescript
requires(({ price }) => price > 0)
// Engine reads AST, sees destructured 'price' from function params
// Maps to the actual parameter position
// Translates to Z3: (> price 0)

ensures(({ result, price }) => result <= price)
// 'result' maps to function return value
// 'price' maps to input parameter
// Z3: (<= result_value price)
```

---

## Scan: Risk Classification

When running without annotations, the engine classifies by analyzing:

### Variable name patterns

```
FINANCIAL:  balance, amount, price, total, cost, fee, tax, revenue, profit
AUTH:       role, permission, privilege, admin, superadmin, owner, access, token
IDENTITY:   user, account, customer, email, password, cpf, cnpj
```

### Operation patterns

```
CRITICAL:   x.balance -= y     (financial subtraction without guard)
CRITICAL:   x.role = y         (auth mutation without check)
HIGH:       a / b              (division without zero check)
HIGH:       arr[i]             (array access without bounds check)
MEDIUM:     x * y              (multiplication without overflow check)
LOW:        str.trim()         (safe string operation)
```

### Type patterns

```
RISKY:      number without constraints (allows NaN, Infinity, negative)
RISKY:      string | null without narrowing
RISKY:      any (defeats all analysis)
SAFE:       literal types, enums, branded types
```

---

## Development Roadmap

### Phase 1 — Proof of Concept (weeks 1-2)

Goal: one function → Z3 → counterexample

```
[ ] Setup monorepo (turborepo)
[ ] Install dependencies: ts-morph, z3-solver, commander
[ ] Parser: extract single function with params and body
[ ] Parser: extract proof() calls and contracts
[ ] Translator: arithmetic operations → Z3
[ ] Solver: send to Z3, get sat/unsat + model
[ ] Reporter: print counterexample to terminal
[ ] Test: transfer() finds "balance can be negative"
```

Milestone: `theorem verify test/transfer.ts` shows counterexample.

### Phase 2 — Contracts (weeks 3-4)

Goal: requires/ensures/old/destructuring working

```
[ ] Parser: detect requires(), ensures() with destructured params
[ ] Parser: detect string contracts
[ ] Translator: requires → Z3 precondition
[ ] Translator: ensures → Z3 postcondition
[ ] Translator: old(x) → SSA variable mapping
[ ] Translator: if/else → Z3 ITE (automatic branch analysis)
[ ] Translator: null checks → Z3 option sort
[ ] Runtime: publish no-op package to npm
[ ] Test: transfer with contracts → PROVED
[ ] Test: transfer with bug → DISPROVED + counterexample
```

### Phase 3 — Scan Mode (weeks 5-6)

Goal: find bugs without annotations

```
[ ] Scanner: classify functions by risk level
[ ] Scanner: infer potential issues from types
[ ] Scanner: detect common patterns
[ ] Reporter: format scan results with risk levels
[ ] CLI: theorem scan src/
[ ] Test: run on real-world project, find real bugs
```

### Phase 4 — Loops & Arrays (weeks 7-8)

Goal: invariant, decreases, forall, exists

```
[ ] Parser: detect invariant(), decreases() inside loops
[ ] Translator: loop verification (base case, inductive, termination)
[ ] Translator: forall() → Z3 universal quantifier
[ ] Translator: exists() → Z3 existential quantifier
[ ] Translator: array method semantics
[ ] Translator: modifies() → frame conditions
[ ] Test: binary search → PROVED
```

### Phase 5 — Separate Files & Classes (weeks 9-10)

Goal: .proof.ts files, of(), proof.fn()

```
[ ] Parser: discover and parse .proof.ts files
[ ] Parser: map proof(fn, ...) to source function
[ ] Parser: resolve of(Class).method references
[ ] Parser: handle proof.fn() inside function declarations
[ ] Suggester: generate contracts interactively
[ ] Suggester: parse natural language rules
[ ] CLI: theorem suggest (interactive)
```

### Phase 6 — Polish & Launch (weeks 11-12)

Goal: production-ready CLI + beta launch

```
[ ] String contracts: pattern matching dictionary
[ ] Reporter: SARIF output for GitHub code scanning
[ ] CI: GitHub Action
[ ] Docs: getting-started, api-reference, examples
[ ] Landing page + README
[ ] Beta launch: Hacker News post
```

### Future

```
[ ] ESLint plugin: inline warnings in editor
[ ] VSCode extension: diagnostics + quick fixes
[ ] GitHub App: comment on PRs with proof results
[ ] NgRx adapter: proofReducer, proofEffect
[ ] Effect-ts adapter
[ ] String contracts: LLM-powered translation
[ ] Inter-procedural analysis (verify call sites match requires)
[ ] Config file: theorem.config.ts
```

---

## Tech Stack

```
Core:
  TypeScript          — implementation language
  ts-morph            — parse TypeScript AST
  z3-solver           — Z3 SMT solver (npm, WASM build)
  commander           — CLI framework

Build:
  turborepo           — monorepo management
  tsup                — build packages
  vitest              — testing

Publish:
  theorem             — runtime package (no-op functions)
  theorem-cli         — CLI binary
  @theorem/core       — core library (programmatic use)
```

---

## References

### Tools to study

```
Dafny (Microsoft)         — closest concept, but separate language
                            https://dafny.org/dafny/OnlineTutorial/guide
                            https://github.com/dafny-lang/dafny
                            Compiles to JS: dafny.org/v3.10.0/DafnyRef/integration-js/IntegrationJS

Solidity SMTChecker       — formal verification embedded in compiler
                            https://docs.soliditylang.org/en/latest/smtchecker.html

SPARK/Ada                 — what airplanes use
                            https://learn.adacore.com/courses/intro-to-spark/index.html

LiquidHaskell             — refinement types via Z3
                            https://github.com/ucsd-progsys/liquidhaskell
```

### Z3 resources

```
Z3 GitHub                   https://github.com/Z3Prover/z3
Z3 TypeScript binding       https://www.npmjs.com/package/z3-solver
Z3 Guide                    https://microsoft.github.io/z3guide/
SMT-LIB standard            https://smtlib.cs.uiowa.edu/
```

### Competitive landscape

```
NONE of these use SMT solvers for TypeScript:

ESLint / typescript-eslint  — pattern matching rules
SonarQube ($150M+ ARR)      — code quality + basic security
DeepScan                    — data flow analysis
Snyk Code ($300M+ ARR)      — ML-based security scanning
ts-code-contracts           — runtime assertions only
contracts-typescript         — runtime assertions only

Theorem is the FIRST formal verification tool for TypeScript.
```

---

## Key Design Decisions

1. **One API: `proof()`.** Works inline with implementation, in separate .proof.ts files, with class methods via `of()`, and with library-specific patterns (NgRx reducers). Same function, same contract syntax everywhere.

2. **Destructured params.** `requires(({ price }) => price > 0)` instead of `requires((price, _, percent) => ...)`. Pick only what you need, no underscores.

3. **Contracts are not runtime code.** Like TypeScript types, they exist for verification and are removed from output. Zero overhead in production.

4. **Scan works without annotations.** The tool provides value from `npx theorem scan` with zero setup. Contracts add precision, not necessity.

5. **Engine handles branches automatically.** No labels, no `on.branch()`. The engine analyzes all paths via AST and reports which branch failed.

6. **Loops need inline contracts.** `invariant()` and `decreases()` stay inside the loop body because they reference local variables. Everything else stays in `proof()`.

7. **Helpers are real functions, not strings.** `positive(amount)` instead of `is.positive('amount')`. Typed, autocomplete, refactor-safe. Compose with `&&` and `forall()`.

8. **File-based ignores only.** `.theoremignore` file, no inline `// @theorem-ignore` comments. Code stays clean.

9. **Not a new language.** Theorem is an external tool, like ESLint. The developer writes TypeScript. No new syntax, no new paradigm, no lock-in.

10. **Counterexamples over proofs.** When verification fails, show concrete values (`amount=150, balance=100 → balance=-50`). Developers understand examples, not logical formulas.

11. **Incremental adoption.** Scan (zero effort) → Suggest (low effort) → Verify (full contracts). Each level works independently.
