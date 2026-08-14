// The Dafny Cons example, in TypeScript — sequences + spec functions.
//
//   theorem verify examples/cons.ts
//
// `list()` is the ABSTRACTION FUNCTION: it maps the linked structure to the
// mathematical sequence it represents. The ensures states the defining
// property of cons — list(cons(x, tail)) === [x] ++ list(tail) — and the
// solver proves it via Z3 sequence theory + fuel-bounded definitional
// axioms. Immutable (readonly-style) structures need no Repr/ownership
// bookkeeping: this is the Dafny example minus its hardest 40%.

import { ensures, output, seqEq } from 'theoremts'

interface Node { readonly value: number; readonly next: Node | null }

// Abstraction: structure → sequence. Recursive; the solver sees it as an
// uninterpreted function plus ground definitional axioms (fuel 2).
function list(n: Node | null): number[] {
  return n === null ? [] : [n.value, ...list(n.next)]
}

// ✓ PROVED — the single-node base case: list(single(x)) === [x]
export function single(x: number): Node {
  ensures(seqEq(list(output()), [x]))
  return { value: x, next: null }
}

// ✓ PROVED — the defining equation of cons, for ALL x and ALL tails:
//   tail === null  ⇒  list(result) === [x]
//   tail !== null  ⇒  list(result) === [x, ...list(tail)]
export function cons(x: number, tail: Node | null): Node {
  ensures(tail === null
    ? seqEq(list(output()), [x])
    : seqEq(list(output()), [x, ...list(tail)]))
  return { value: x, next: tail }
}

// ✗ DISPROVED — drops the tail: list(result) === [x] even when tail exists.
export function buggyCons(x: number, tail: Node | null): Node {
  ensures(tail === null
    ? seqEq(list(output()), [x])
    : seqEq(list(output()), [x, ...list(tail)]))
  return { value: x, next: null }
}
