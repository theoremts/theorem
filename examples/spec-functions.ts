// Spec functions — user-defined predicates, including RECURSIVE ones.
//
//   theorem verify examples/spec-functions.ts
//
// Any pure same-file function usable in contracts becomes a DEFINITION the
// solver knows: calls stay as uninterpreted applications (so equal arguments
// give equal results — congruence), and ground definitional axioms unfold
// each call instance up to a fuel bound. This is the Dafny predicate
// mechanism, sized for TypeScript.

import { requires, ensures, positive, output } from 'theoremts'

interface Node { value: number; next: Node | null }

// A recursive spec function over an unbounded structure:
function allPositive(n: Node | null): boolean {
  return n === null ? true : n.value > 0 && allPositive(n.next)
}

// ✓ PROVED — the inductive step of a cons: pushing a positive head onto an
// all-positive tail keeps the WHOLE list all-positive. The proof connects
// allPositive(output()) to allPositive(tail) through result.next = tail.
export function consPositive(x: number, tail: Node | null): Node {
  requires(positive(x))
  requires(tail === null || allPositive(tail))
  ensures(allPositive(output()))
  return { value: x, next: tail }
}

// ✗ DISPROVED — nothing guarantees x > 0: counterexample x = 0.
export function buggyCons(x: number, tail: Node | null): Node {
  requires(tail === null || allPositive(tail))
  ensures(allPositive(output()))
  return { value: x, next: tail }
}

// Non-recursive spec predicates work anywhere:
function isSorted(p: { lo: number; hi: number }): boolean {
  return p.lo <= p.hi
}

// ✓ PROVED — both branches of the ternary produce a sorted pair.
export function makeSorted(a: number, b: number): { lo: number; hi: number } {
  ensures(isSorted(output()))
  return a <= b ? { lo: a, hi: b } : { lo: b, hi: a }
}

// ✗ DISPROVED — counterexample: a = 0, b = -0.5.
export function buggySorted(a: number, b: number): { lo: number; hi: number } {
  ensures(isSorted(output()))
  return { lo: a, hi: b }
}
