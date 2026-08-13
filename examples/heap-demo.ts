// Mutable objects with ALIASING — heap-as-map encoding.
//
//   theorem verify examples/heap-demo.ts
//
// When a function mutates fields of object parameters, Theorem switches to a
// heap encoding (Z3 arrays): object references become solver values, so
// `from === to` is a case the solver EXPLORES rather than an assumption it
// silently makes. The classic bug this catches: a transfer where both
// references point to the same account.

import { requires, ensures, nonNegative, old, modifies } from 'theoremts'

interface Account { value: number }

// ✗ DISPROVED — counterexample: from === to (same reference!).
// Aliased, the two writes hit the same cell: value doubles, then zeroes.
export function drainUnsafe(from: Account, to: Account): void {
  requires(nonNegative(from.value))
  requires(nonNegative(to.value))
  ensures(to.value === old(to.value) + old(from.value))
  ensures(from.value === 0)

  to.value = to.value + from.value
  from.value = 0
}

// ✓ PROVED — the anti-aliasing precondition rules the bad case out.
export function drainSafe(from: Account, to: Account): void {
  requires(from !== to)
  requires(nonNegative(from.value))
  requires(nonNegative(to.value))
  ensures(to.value === old(to.value) + old(from.value))
  ensures(from.value === 0)
  to.value = to.value + from.value
  from.value = 0
}

// ── Level 3: modifies() framing ──────────────────────────────────────────────

// ✗ modifies violation: writes b.value without declaring it.
export function sneakyWrite(a: Account, b: Account): void {
  modifies(a)
  requires(a !== b)
  ensures(a.value === 1)
  a.value = 1
  b.value = 2
}

// ✓ PROVED — every write declared.
export function honestWrite(a: Account, b: Account): void {
  modifies(a, b)
  requires(a !== b)
  ensures(a.value === 1)
  a.value = 1
  b.value = 2
}
