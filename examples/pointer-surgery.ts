// Pointer surgery — the L4 spike, shipped: pointer-valued fields, null, and
// reads/writes THROUGH pointers, with aliasing explored by the solver.
//
//   theorem verify examples/pointer-surgery.ts
//
// This is bounded verification of linked-structure mutations (fixed windows
// of 2-3 nodes). Unbounded invariants over whole chains (the full Dafny
// Valid()/Repr) need recursive spec functions — future work, shared with the
// immutable sequences path.

import { requires, ensures } from 'theoremts'

interface Node { value: number; next: Node | null; prev: Node | null }

// ✓ PROVED — correct doubly-linked front insertion.
export function linkFront(head: Node, node: Node): void {
  requires(head !== node)
  requires(node.next === null)
  requires(node.prev === null)
  ensures(node.next === head)
  ensures(head.prev === node)
  ensures(node.prev === null)
  node.next = head
  head.prev = node
}

// ✗ DISPROVED — the classic bug: forgot the back-pointer.
// Symptom appears operations later; the solver catches it at the source.
export function buggyLink(head: Node, node: Node): void {
  requires(head !== node)
  requires(node.next === null)
  ensures(node.next === head)
  ensures(head.prev === node)
  node.next = head
  // BUG: missing `head.prev = node`
}

// ✗ DISPROVED — aliasing: with head === node, writing head.prev clobbers
// node.prev. Counterexample: node = 1, head = 1 (same reference).
export function aliasedLink(head: Node, node: Node): void {
  requires(node.prev === null)
  ensures(node.next === head)
  ensures(head.prev === node)
  ensures(node.prev === null)   // ← dies when head === node
  node.next = head
  head.prev = node
}

// ✓ PROVED — reads and writes THROUGH a pointer: unlink the second node.
export function unlinkSecond(head: Node): void {
  requires(head.next !== null)
  requires(head.next!.prev === head)
  requires(head.next!.next === null)
  ensures(head.next === null)
  const second = head.next!
  head.next = second.next
  second.prev = null
}
