// Discriminated unions — the discriminant ranges over its declared literals,
// so EXHAUSTIVENESS is a provable fact, not a type-checker courtesy.
//
//   theorem verify examples/discriminated-unions.ts
//
// TypeScript's own never-checks catch missing cases at compile time — but
// only if you remember to write them. Here, any contract that RELIES on
// exhaustiveness is proved, and a forgotten case comes back as a
// counterexample naming the exact variant.

import { requires, ensures, output, nonNegative, positive } from 'theoremts'

type Payment =
  | { kind: 'pix'; amount: number }
  | { kind: 'boleto'; amount: number }
  | { kind: 'card'; amount: number }

// ✓ PROVED — all three kinds handled: the -1 fallback is provably DEAD,
// so the ensures holds even though the code appears to return -1.
export function fee(p: Payment): number {
  ensures(nonNegative(output()))
  if (p.kind === 'pix') return 0
  if (p.kind === 'boleto') return 2
  if (p.kind === 'card') return 1
  return -1
}

// ✗ DISPROVED — 'card' forgotten. The counterexample names the variant:
//   p.kind = card, result = -1
export function feeForgotten(p: Payment): number {
  ensures(nonNegative(output()))
  if (p.kind === 'pix') return 0
  if (p.kind === 'boleto') return 2
  return -1
}

// ✓ PROVED — narrowing works in contracts too: under kind === 'pix'
// the fee-free path is guaranteed.
export function total(p: Payment, tip: number): number {
  requires(positive(p.amount))
  requires(nonNegative(tip))
  requires(p.kind === 'pix')
  ensures(output() === p.amount + tip)
  if (p.kind === 'pix') return p.amount + tip
  return p.amount + tip + 2
}
