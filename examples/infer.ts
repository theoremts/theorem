// ─────────────────────────────────────────────────────────────────────────────
// theorem infer — example file
//
// This file has NO annotations and NO imports from theoremts.
// All contracts are inferred automatically by running:
//
//   theorem infer examples/infer.ts
//
// Expected inferred contracts are shown in comments for reference.
// ─────────────────────────────────────────────────────────────────────────────

// ── 1. Guard extraction: if/throw → requires ────────────────────────────────

// Expected: requires(amount > 0), requires(amount <= balance)
//           ensures(output() >= 0)
function withdraw(balance: number, amount: number): number {
  if (amount <= 0) throw new Error('invalid amount')
  if (amount > balance) throw new Error('insufficient funds')
  return balance - amount
}

// ── 2. Arithmetic safety: division → requires denominator !== 0 ─────────────

// Expected: requires(b !== 0)
//           ensures(output() === a / b)
function divide(a: number, b: number): number {
  if (b === 0) throw new Error('division by zero')
  return a / b
}

// ── 3. Math domain: sqrt → requires non-negative ────────────────────────────

// Expected: requires(x >= 0)
//           ensures(output() >= 0)
function squareRoot(x: number): number {
  if (x < 0) throw new Error('negative input')
  return Math.sqrt(x)
}

// ── 4. Return analysis: Math.abs → ensures non-negative ─────────────────────

// Expected: ensures(output() >= 0)
function distance(a: number, b: number): number {
  return Math.abs(a - b)
}

// ── 5. Return analysis: Math.max → ensures >= both args ─────────────────────

// Expected: ensures(output() >= a)
//           ensures(output() >= b)
function larger(a: number, b: number): number {
  return Math.max(a, b)
}

// ── 6. Clamp pattern: bounded return ────────────────────────────────────────

// Expected: requires(min <= max)
//           ensures(output() >= min)
//           ensures(output() <= max)
function clampValue(value: number, min: number, max: number): number {
  if (value < min) return min
  if (value > max) return max
  return value
}

// ── 7. Range validation: relational guard ───────────────────────────────────

// Expected: requires(start <= end)
//           ensures(output() >= 0)
function rangeSize(start: number, end: number): number {
  if (start > end) throw new Error('invalid range')
  return end - start
}

// ── 8. Cross-function propagation: calls divide() ───────────────────────────

// Expected: requires(count !== 0)   [propagated from divide]
function average(total: number, count: number): number {
  return divide(total, count)
}

// ── 9. Array safety: reduce without initial value ───────────────────────────

// Expected: requires(values.length > 0)
function sum(values: number[]): number {
  return values.reduce((acc, v) => acc + v)
}

// ── 10. Null safety: nullable param with guard ──────────────────────────────

// Expected: requires(data !== null)
//           ensures(output() === data.value * 2)
function processData(data: { value: number } | null): number {
  if (!data) throw new Error('missing data')
  return data.value * 2
}
