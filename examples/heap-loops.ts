// F6 — while loops over the mutable heap, verified via havoc + invariant.
//
//   theorem verify examples/heap-loops.ts
//
// Each loop produces four proof obligations: the invariant holds at ENTRY,
// is PRESERVED by an arbitrary iteration (heap havoced, invariant+condition
// assumed, body executed, invariant re-proved), the decreases measure is
// BOUNDED below and STRICTLY DECREASES (termination), and the code after
// the loop runs under invariant ∧ ¬condition.

import { requires, ensures, nonNegative, invariant, decreases } from 'theoremts'

interface Acc { value: number }

// ✓ PROVED (all four obligations) — note the guard is `>= 1`, not `> 0`:
// over the reals, value = 0.5 passes `> 0` and 0.5 - 1 breaks the
// invariant. The solver caught exactly that during development.
export function drainSlowly(acc: Acc, n: number): void {
  requires(nonNegative(acc.value))
  requires(nonNegative(n))
  ensures(nonNegative(acc.value))
  while (n > 0) {
    invariant(() => acc.value >= 0)
    decreases(() => n)
    if (acc.value >= 1) {
      acc.value = acc.value - 1
    }
    n = n - 1
  }
}

// ✗ DISPROVED (invariant not preserved) — the unguarded decrement can
// drive the balance below zero.
export function drainBuggy(acc: Acc, n: number): void {
  requires(nonNegative(acc.value))
  requires(nonNegative(n))
  ensures(nonNegative(acc.value))
  while (n > 0) {
    invariant(() => acc.value >= 0)
    decreases(() => n)
    acc.value = acc.value - 1
    n = n - 1
  }
}

// ✗ DISPROVED (termination) — the measure never decreases: infinite loop.
export function spinForever(acc: Acc, n: number): void {
  requires(nonNegative(acc.value))
  requires(nonNegative(n))
  ensures(nonNegative(acc.value))
  while (n > 0) {
    invariant(() => acc.value >= 0)
    decreases(() => n)
    acc.value = acc.value + 1
  }
}
