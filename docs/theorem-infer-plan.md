# theorem infer — Contract Inference Engine

## Vision

`theorem infer` reads an existing TypeScript codebase — with zero annotations — and generates a `.contracts.ts` file containing `declare()` contracts for every function it can analyze. These contracts capture the implicit specification that developers already expressed through guards, validations, control flow, and arithmetic patterns.

The output serves two purposes:
1. **Safety net** — `theorem scan` uses the inferred contracts as a registry, catching contract violations at call sites across the codebase
2. **AI guardrail** — any tool that generates code (Cursor, Claude, Copilot) can be validated against these contracts without the AI knowing anything about Theorem

The developer never writes `requires()` or `ensures()`. Theorem reads their code and tells them what their code already guarantees.

---

## Core Idea: Inference by Exclusion

Instead of asking "what should this function do?", we ask "what can this function NOT do?"

Given:
```typescript
function withdraw(account: Account, amount: number) {
  if (amount <= 0) throw new Error('invalid amount')
  if (amount > account.balance) throw new Error('insufficient funds')
  account.balance -= amount
  return account.balance
}
```

By exclusion:
- `amount` can never be `<= 0` (guard rejects it) → `requires(amount > 0)`
- `amount` can never exceed `account.balance` (guard rejects it) → `requires(amount <= account.balance)`
- After both guards, `account.balance - amount >= 0` always → `ensures(output() >= 0)`
- The return is `account.balance - amount` exactly → `ensures(output() === account.balance - amount)`

None of this was annotated. It was extracted from the code structure.

---

## Inference Strategies

### Strategy 1: Guard Extraction (requires)

Every `if/throw` and `if/return-early` at the top of a function is an implicit precondition. The function refuses to run unless the negated guard holds.

**Patterns to extract:**

```typescript
// Pattern: if (BAD_CONDITION) throw → requires(!BAD_CONDITION)
if (x <= 0) throw new Error(...)           // → requires(x > 0)
if (x === null) throw ...                  // → requires(x !== null)
if (!Array.isArray(arr)) throw ...         // → requires(Array.isArray(arr))
if (typeof x !== 'number') throw ...       // → requires(typeof x === 'number')

// Pattern: if (BAD_CONDITION) return SENTINEL → requires(!BAD_CONDITION)
if (arr.length === 0) return null          // → requires(arr.length > 0)  
if (index < 0) return -1                   // → requires(index >= 0)
if (!user) return undefined                // → requires(user is truthy)

// Pattern: assertion-style (no else, continues after)
if (amount <= 0) throw new Error(...)
if (amount > balance) throw new Error(...)
// after both: amount > 0 AND amount <= balance
// → requires(amount > 0)
// → requires(amount <= balance)

// Pattern: early return chains
if (!config) return defaults
if (!config.timeout) return { ...config, timeout: 30000 }
// from here: config exists AND config.timeout exists

// Pattern: typeof narrowing
if (typeof value !== 'string' && typeof value !== 'number') throw ...
// → requires(typeof value === 'string' || typeof value === 'number')

// Pattern: range validation
if (port < 0 || port > 65535) throw ...    // → requires(port >= 0 && port <= 65535)

// Pattern: length checks
if (password.length < 8) throw ...         // → requires(password.length >= 8)

// Pattern: assert() / console.assert()
assert(x > 0)                             // → requires(x > 0)
console.assert(arr.length > 0)            // → requires(arr.length > 0)
```

**Implementation notes:**
- Walk function body top-down
- Stop collecting guards when first non-guard statement is found (assignment, function call, etc.)
- Compound guards (`if (a || b) throw`) must be split — the negation is `!a && !b`
- Nested guards accumulate: guard 2 already assumes guard 1 passed
- Only extract from UNCONDITIONAL exits (throw or return without else branch)

---

### Strategy 2: Body Analysis (ensures)

Read the function body after guards and derive what must be true about the return value.

**Patterns to extract:**

```typescript
// Pattern: direct return expression
return a / b
// → ensures(output() === a / b)  (if b !== 0 is already a requires)

// Pattern: ternary return
return x >= 0 ? x : -x
// → ensures(output() >= 0)
// → ensures(output() === x || output() === -x)

// Pattern: bounded return
return Math.max(0, Math.min(100, value))
// → ensures(output() >= 0)
// → ensures(output() <= 100)

// Pattern: arithmetic return
return a + b
// → ensures(output() === a + b)

return price * (1 - discount)
// → ensures(output() === price * (1 - discount))
// if requires(discount >= 0 && discount <= 1) and requires(price >= 0):
// → ensures(output() >= 0)
// → ensures(output() <= price)

// Pattern: conditional return
if (x > threshold) return x - fee
return x
// → ensures(output() <= x)  (either branch returns <= x, assuming fee >= 0)

// Pattern: accumulator
let sum = 0
for (const item of items) sum += item.value
return sum
// → ensures(output() is the final sum)  (limited — loop body analysis)

// Pattern: filter/find
return arr.find(x => x.id === id) ?? null
// → ensures(output() === null || output().id === id)
// (limited — higher-order functions are opaque)

// Pattern: object return
return { tax: price * rate, total: price + price * rate }
// → ensures(output().tax === price * rate)
// → ensures(output().total === price + output().tax)
// → ensures(output().total === price * (1 + rate))
```

**Two levels of body analysis:**

**Level 1 — Direct (already feasible):**
The IR already represents the body as expressions. For simple bodies (arithmetic, ternaries, comparisons), we can directly assert `output() === bodyExpr` and then test derived properties.

**Level 2 — Derived (requires Z3):**
For complex bodies, generate candidate ensures and test them with Z3:
- Take the body expression as a constraint: `result = f(params)`
- Generate candidates: `result >= 0`, `result <= param`, `result === expr`
- Check each candidate with Z3 under the inferred requires
- Keep the ones that are provable (UNSAT when negated)

---

### Strategy 3: Arithmetic Safety (requires + ensures)

Detect operations that have implicit domain constraints.

```typescript
// Division → denominator != 0
return revenue / months           // → requires(months !== 0)

// Modulo → divisor != 0
return index % size               // → requires(size !== 0)

// Square root → non-negative
return Math.sqrt(variance)        // → requires(variance >= 0)
                                  // → ensures(output() >= 0)

// Logarithm → positive
return Math.log(probability)      // → requires(probability > 0)

// Exponentiation with negative base
return base ** exponent           // (pattern-only risk for overflow)

// Chained operations
return (a * b) / (c - d)         // → requires(c !== d)  (c - d != 0)
                                  // → ensures(output() === (a * b) / (c - d))
```

**Implementation notes:**
- Walk the body expression tree recursively
- For every `/` and `%`, extract the right operand as a `requires(rhs !== 0)`
- For `Math.sqrt`, extract `requires(arg >= 0)` and `ensures(output() >= 0)`
- For `Math.log`, `Math.log2`, `Math.log10`, extract `requires(arg > 0)`
- Check if the requires is already implied by a guard (avoid duplicates)

---

### Strategy 4: Cross-Function Propagation

When function A calls function B (which has inferred contracts), A inherits obligations.

```typescript
// B's inferred contract: requires(amount > 0), requires(amount <= balance)
function withdraw(account, amount) { ... }

// A calls B:
function transfer(from, to, amount) {
  withdraw(from, amount)    // → A needs: amount > 0, amount <= from.balance
  deposit(to, amount)       // → A needs: whatever deposit requires
}
// Inferred for transfer:
// → requires(amount > 0)           (from withdraw)
// → requires(amount <= from.balance) (from withdraw)
```

**Implementation:**
1. First pass: infer contracts for all leaf functions (functions that don't call other inferred functions)
2. Second pass: propagate through the call graph
3. Repeat until fixed point (or max depth)
4. The ContractRegistry already supports this — we just need to populate it with inferred contracts

**Edge cases:**
- Recursive functions: infer from guards only, don't propagate ensures through recursion
- Conditional calls: `if (cond) f(x)` — the requires of f is only needed when cond is true
- Chained calls: `f(g(x))` — g's ensures become f's argument constraints

---

### Strategy 5: Null/Undefined Safety

Extract null-safety contracts from type annotations and usage patterns.

```typescript
// Pattern: nullable parameter with guard
function process(data: Data | null) {
  if (!data) throw new Error('missing data')
  return data.value * 2
}
// → requires(data !== null)
// → ensures(output() === data.value * 2)

// Pattern: nullable return
function find(arr: Item[], id: string): Item | null {
  for (const item of arr) {
    if (item.id === id) return item
  }
  return null
}
// → ensures(output() === null || output().id === id)

// Pattern: optional property access with fallback
function getTimeout(config?: Config) {
  return config?.timeout ?? 30000
}
// → ensures(output() >= 0)  (if we know timeout is numeric)
// → ensures(output() === 30000 || output() === config.timeout)
```

---

### Strategy 6: Array/Collection Safety

```typescript
// Pattern: index bounds
function get(arr: number[], i: number) {
  if (i < 0 || i >= arr.length) throw new RangeError()
  return arr[i]
}
// → requires(i >= 0)
// → requires(i < arr.length)

// Pattern: non-empty check
function first(arr: number[]) {
  if (arr.length === 0) throw new Error('empty')
  return arr[0]
}
// → requires(arr.length > 0)

// Pattern: reduce without initial
const sum = values.reduce((a, b) => a + b)
// → requires(values.length > 0)

// Pattern: pop/shift
const last = stack.pop()
// → requires(stack.length > 0)  (if no undefined check after)
```

---

### Strategy 7: Return Type Guarantees

Derive ensures from what the return type and body structure guarantee.

```typescript
// Pattern: all branches return same type
function classify(score: number): string {
  if (score >= 90) return 'A'
  if (score >= 80) return 'B'
  if (score >= 70) return 'C'
  return 'F'
}
// → ensures(output() === 'A' || output() === 'B' || output() === 'C' || output() === 'F')

// Pattern: boolean return
function isValid(x: number): boolean {
  return x > 0 && x < 100
}
// → ensures(output() === (x > 0 && x < 100))

// Pattern: numeric bounds from ternary
function clamp(x: number, min: number, max: number) {
  if (x < min) return min
  if (x > max) return max
  return x
}
// → requires(min <= max)  (inferred from body — otherwise both guards could fire)
// → ensures(output() >= min)
// → ensures(output() <= max)

// Pattern: Math.abs / Math.max / Math.min
function distance(a: number, b: number) {
  return Math.abs(a - b)
}
// → ensures(output() >= 0)

function larger(a: number, b: number) {
  return Math.max(a, b)
}
// → ensures(output() >= a)
// → ensures(output() >= b)
// → ensures(output() === a || output() === b)
```

---

### Strategy 8: Relational Contracts (Cross-Parameter)

```typescript
// Pattern: parameter ordering
function range(start: number, end: number) {
  if (start > end) throw new Error('invalid range')
  // ...
}
// → requires(start <= end)

// Pattern: bounded parameter
function setOpacity(value: number) {
  if (value < 0 || value > 1) throw ...
  // ...
}
// → requires(value >= 0)
// → requires(value <= 1)

// Pattern: percentage
function applyDiscount(price: number, discount: number) {
  if (discount < 0 || discount > 100) throw ...
  return price * (1 - discount / 100)
}
// → requires(discount >= 0)
// → requires(discount <= 100)
// → ensures(output() >= 0)  (if price >= 0)
// → ensures(output() <= price)  (if price >= 0)
```

---

## Output Format

`theorem infer` generates a `.contracts.ts` file:

```typescript
// Auto-generated by theorem infer
// Source: src/accounting/transactions.ts
// Generated: 2026-04-10T21:00:00Z
//
// Review these contracts and adjust if needed.
// Then add to theorem.config.ts:
//   contracts: ['src/accounting/transactions.contracts.ts']

import { declare, requires, ensures, output, positive, nonNegative } from 'theoremts'

declare(withdraw, (account: { balance: number }, amount: number): number => {
  requires(amount > 0)
  requires(amount <= account.balance)
  ensures(nonNegative(output()))
  ensures(output() === account.balance - amount)
})

declare(deposit, (account: { balance: number }, amount: number): number => {
  requires(amount > 0)
  ensures(output() === account.balance + amount)
  ensures(output() > account.balance)
})

declare(transfer, (from: { balance: number }, to: { balance: number }, amount: number): void => {
  requires(amount > 0)
  requires(amount <= from.balance)
})

declare(clamp, (value: number, min: number, max: number): number => {
  requires(min <= max)
  ensures(output() >= min)
  ensures(output() <= max)
})

declare(divide, (a: number, b: number): number => {
  requires(b !== 0)
  ensures(output() === a / b)
})
```

---

## Confidence Levels

Not all inferred contracts are equal. Each gets a confidence level:

| Level | Source | Example |
|-------|--------|---------|
| **proven** | Z3 verified the contract holds for all inputs | `ensures(output() >= 0)` for `Math.abs(x)` |
| **guard** | Directly negated from an if/throw or if/return guard | `requires(x > 0)` from `if (x <= 0) throw` |
| **derived** | Follows from body analysis + guards | `ensures(output() <= balance)` from `return balance - amount` with `requires(amount >= 0)` |
| **propagated** | Inherited from a callee's inferred contract | `requires(x > 0)` because function calls `sqrt(x)` |
| **heuristic** | Pattern-based, not Z3-verified | `requires(arr.length > 0)` from `arr.reduce(...)` |

The output file includes confidence as comments:

```typescript
declare(withdraw, (account, amount) => {
  requires(amount > 0)                              // [guard] if (amount <= 0) throw
  requires(amount <= account.balance)                // [guard] if (amount > account.balance) throw
  ensures(nonNegative(output()))                     // [proven] Z3 verified
  ensures(output() === account.balance - amount)     // [derived] from return expression
})
```

---

## Architecture

```
Source files (.ts)
       |
       v
  extractFunctionsFromSource()      ← already exists
       |
       v
  FunctionIR[] (no contracts)
       |
       v
  INFERENCE ENGINE (NEW)
       |
       |─── guardExtractor          ← if/throw, if/return → requires
       |─── bodyAnalyzer            ← return expr → ensures  
       |─── arithmeticSafety        ← div/mod/sqrt/log → requires
       |─── nullSafety              ← nullable params + guards → requires
       |─── arraySafety             ← index/reduce/pop → requires
       |─── returnAnalyzer          ← bounds, types, relations → ensures
       |─── candidateVerifier       ← Z3 proves/disproves candidates
       |
       v
  InferredContract[]
       |
       v
  CROSS-FUNCTION PROPAGATION
       |
       |─── buildCallGraph()        ← who calls whom
       |─── propagateRequires()     ← callee requires → caller requires
       |─── propagateEnsures()      ← callee ensures → caller assumptions
       |
       v
  InferredContract[] (enriched)
       |
       v
  CONTRACT WRITER
       |─── generateDeclareFile()   ← .contracts.ts output
       |─── generateReport()        ← human-readable summary
```

### New modules needed:

```
packages/core/src/inferrer/
  index.ts              ← main entry: inferContracts(source, fileName)
  guards.ts             ← Strategy 1: guard extraction
  body.ts               ← Strategy 2: body analysis  
  arithmetic.ts         ← Strategy 3: arithmetic safety
  null-safety.ts        ← Strategy 5: null/undefined
  array-safety.ts       ← Strategy 6: array/collection
  returns.ts            ← Strategy 7: return type guarantees
  relations.ts          ← Strategy 8: cross-parameter relations
  propagation.ts        ← Strategy 4: cross-function
  candidates.ts         ← candidate generation + Z3 verification
  writer.ts             ← .contracts.ts file generator

packages/cli/src/commands/
  infer.ts              ← CLI command
```

---

## Implementation Phases

### Phase 1: Guard Extraction
Extract `requires` from if/throw and if/return patterns. This is the highest-value, lowest-risk inference — guards are explicit intent from the developer.

**What already exists:**
- `detectGuards()` in suggester (basic ternary pattern)
- `hasNullGuardBefore()` in scanner (null-specific)
- `collectPathConditions()` in scanner (path-sensitive)
- `isUnconditionalExit()` in scanner

**What needs to be built:**
- Walk function body as AST (not IR) to preserve if/throw structure
- Collect all top-level guards before the "real body" starts
- Negate compound conditions correctly (De Morgan's)
- Deduplicate: if guard A implies guard B, only keep A
- Handle `assert()` and `console.assert()` as guards

### Phase 2: Body → Ensures (Direct)
For simple return expressions, generate `ensures(output() === bodyExpr)`.

**What already exists:**
- `parseBlockToExpr()` converts body to single IR expression
- `toZ3()` translates IR to Z3

**What needs to be built:**
- For each function with a parseable body, generate `ensures(output() === body)`
- Simplify the ensures text: `output() === a + b` not `output() === binary(+, ident(a), ident(b))`
- Use `prettyExpr()` to render the IR back to readable TypeScript

### Phase 3: Derived Ensures (Z3-Powered)
Generate candidate ensures, verify with Z3, keep the provable ones.

**What already exists:**
- `suggestContracts()` with candidate generation and Z3 checking
- `generateEnsuresCandidates()` and `generateBodyDerivedCandidates()`

**What needs to be built:**
- Richer candidate generation:
  - `output() >= 0` for functions returning Math.abs, Math.max, squared values
  - `output() >= param` / `output() <= param` for functions with bounds
  - `output() === param_a OP param_b` for arithmetic functions
- Prove candidates under the inferred requires (not globally)
- Rank by specificity: `output() === a + b` is stronger than `output() >= a`

### Phase 4: Cross-Function Propagation
Build call graph, propagate requires upward.

**What already exists:**
- `ContractRegistry` for storing function contracts
- `extractCallSiteObligations()` for checking calls against registry
- `buildRegistry()` from FunctionIR[]

**What needs to be built:**
- Call graph extraction (ts-morph: find all CallExpressions, resolve callee)
- Topological sort: infer leaf functions first, then their callers
- Propagation: if A calls B, A inherits B's requires (substituted with A's args)
- Fixed-point iteration for mutual dependencies

### Phase 5: Writer + CLI
Output `.contracts.ts` and integrate into the CLI.

**What needs to be built:**
- `generateDeclareFile()` that produces valid TypeScript with `declare()` calls
- `theorem infer src/` CLI command
- `--output` flag for specifying output file
- `--confidence` flag for filtering by confidence level
- `--dry-run` flag for preview without writing

---

## Candidate Verification Pipeline

For each function:

```
1. Extract guards → requires[]

2. Parse body → Expr

3. Generate ensures candidates:
   a. Direct: output() === bodyExpr (if body is simple)
   b. Bounds: output() >= 0, output() <= param, etc.
   c. Relations: output() === a + b, output() === a * b, etc.
   d. From known functions: Math.abs → >= 0, Math.max → >= both args

4. For each candidate:
   assumes = [body_constraint, ...inferred_requires, ...domain_constraints]
   goal = NOT(candidate)
   result = Z3.check(assumes, goal)
   
   if UNSAT → candidate is proven (keep it)
   if SAT   → candidate is false (discard)
   if TIMEOUT → unknown (discard or mark heuristic)

5. Filter redundant:
   if ensures(output() === a + b) is proven,
   then ensures(output() >= a) is redundant (implied)
   keep the strongest provable contract
```

---

## Edge Cases and Limitations

### What we CAN'T infer:
- **Semantic intent**: "this function calculates tax" — only structural properties
- **Implicit business rules**: "balance should never be negative across the whole system"
- **Higher-order function behavior**: `arr.map(fn)` — fn is opaque
- **Async side effects**: promises, callbacks, event handlers
- **Global state**: functions that read/write module-level variables
- **Complex loop invariants**: only simple accumulator patterns
- **String content**: regex patterns, format validation (unless explicit guard)

### What we SHOULD NOT infer:
- **Implementation details as contracts**: `ensures(output() === arr[0] + arr[1] + arr[2])` for a sum function — this couples the contract to the implementation. Prefer `ensures(output() >= 0)` (a property) over `ensures(output() === exact_body)` (a tautology).
- **Trivially true**: `ensures(output() === output())` — filter these out
- **Overly specific bounds from literals**: `ensures(output() <= 2147483647)` — not useful

### How to handle ambiguity:
- If a function throws on `x <= 0`, is that `requires(x > 0)` or just error handling?
  → Default: treat as requires (conservative). The developer can remove it.
- If a function returns `null` on some path, is that an error or valid?
  → Default: don't infer `requires` that eliminates the null path. Instead infer `ensures(output() === null || output().prop === ...)`.
- If a guard checks something already guaranteed by the type system?
  → Include it anyway. Types can lie (any, type assertions). Guards are ground truth.

---

## Success Metrics

The feature is valuable if:
1. **Accuracy**: >= 95% of inferred `requires` match developer intent (guards are nearly 100%)
2. **Coverage**: >= 60% of exported functions get at least one inferred contract
3. **Actionability**: running `theorem scan` with inferred contracts catches real bugs that the scan alone misses
4. **Performance**: inference completes in < 30 seconds for a 1000-file project
5. **Readability**: the generated `.contracts.ts` is understandable without explanation
