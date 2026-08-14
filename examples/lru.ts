// F7 — the LRU flagship: everything composed.
//
//   theorem verify examples/lru.ts
//
// The operations of an LRU cache's doubly-linked chain, verified with every
// mechanism of the mutation roadmap working together:
//
//   - heap encoding with aliasing            (L2/spike)
//   - branches + early returns               (F1)
//   - recursive spec predicates              (F2, over the heap: F4)
//   - ownership via footprint()              (F5)
//   - loops with invariants over the heap    (F6)
//
// The classic LRU bug — moveToFront forgetting the head back-pointer, whose
// symptom appears operations later as silently dropped entries — is refuted
// at the source, with a counterexample.

import { requires, ensures, nonNegative, invariant, decreases, footprint } from 'theoremts'

interface Node { value: number; next: Node | null; prev: Node | null }

// The chain invariant: every link is back-linked. A plain recursive
// TypeScript function — the solver sees definitional axioms per heap state.
function validChain(n: Node | null): boolean {
  return n === null ? true : n.next === null ? true : n.next.prev === n && validChain(n.next)
}

// The chain's FOOTPRINT: which nodes validChain reads. Pairing it via
// footprint() enables frame reasoning for writes outside the structure.
function inChain(n: Node | null, x: Node): boolean {
  return n === null ? false : n === x || inChain(n.next, x)
}
footprint(validChain, inChain)

// ✓ PROVED — the LRU's core operation on a bounded window: early return if
// already front, unlink (a write THROUGH a pointer), relink at the front.
// The chain is valid again afterwards.
export function moveToFront(head: Node, node: Node, prevN: Node): void {
  requires(head !== node)
  requires(prevN !== node)
  requires(prevN !== head)
  requires(head.prev === null)
  requires(head.next === null)
  requires(prevN.next === node)
  requires(node.prev === prevN)
  requires(node.next === null)
  ensures(node === head || (node.next === head && head.prev === node && prevN.next === null))
  ensures(node === head || validChain(node))
  if (node === head) return
  prevN.next = node.next
  node.prev = null
  node.next = head
  head.prev = node
}

// ✗ DISPROVED — THE classic LRU bug: the head back-pointer write is
// missing. The list "works" until an eviction walks prev and drops the
// wrong entry. The solver catches it here, not three operations later.
export function buggyMoveToFront(head: Node, node: Node, prevN: Node): void {
  requires(head !== node)
  requires(prevN !== node)
  requires(prevN !== head)
  requires(head.prev === null)
  requires(head.next === null)
  requires(prevN.next === node)
  requires(node.prev === prevN)
  requires(node.next === null)
  ensures(node === head || validChain(node))
  if (node === head) return
  prevN.next = node.next
  node.prev = null
  node.next = head
  // BUG: missing `head.prev = node`
}

// ✓ PROVED — the monster: a LOOP mutating a field the invariant READS
// (victim.prev), across arbitrarily many iterations, with the RECURSIVE
// invariant preserved because the victim is provably OUTSIDE the chain.
// Entry, preservation, termination, and the final ensures all prove.
export function evictOthers(head: Node, victim: Node, n: number): void {
  requires(validChain(head))
  requires(!inChain(head, victim))
  requires(nonNegative(n))
  ensures(validChain(head))
  while (n > 0) {
    invariant(() => validChain(head))
    decreases(() => n)
    victim.prev = null
    victim.value = 0
    n = n - 1
  }
}

// ✗ DISPROVED — without the disjointness hypothesis, the victim may be a
// chain node: the loop's invariant preservation fails.
export function evictBuggy(head: Node, victim: Node, n: number): void {
  requires(validChain(head))
  requires(nonNegative(n))
  ensures(validChain(head))
  while (n > 0) {
    invariant(() => validChain(head))
    decreases(() => n)
    victim.prev = null
    n = n - 1
  }
}
