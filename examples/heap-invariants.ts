// F4 — recursive spec predicates over the MUTABLE heap.
//
//   theorem verify examples/heap-invariants.ts
//
// `validChain` is a user-defined recursive invariant (doubly-linked
// coherence). Its definitional axioms are instantiated PER HEAP VERSION:
// requires read the initial heap (@pre), ensures read the final one (@post),
// and select-over-store connects them through the written window. A ground
// frame bridge closes the preservation case: a predicate whose read-set is
// disjoint from the written fields cannot change value.
//
// Scope: bounded windows (fuel 2). Whole-chain framing beyond the window is
// F5 (ownership) territory.

import { requires, ensures, footprint } from 'theoremts'

interface Node { value: number; next: Node | null; prev: Node | null }

// The invariant, as a plain recursive TypeScript function:
function validChain(n: Node | null): boolean {
  return n === null ? true
    : n.next === null ? true
    : n.next.prev === n && validChain(n.next)
}

// ✓ PROVED — pointer surgery ESTABLISHES the invariant: after linking,
// the two-node chain is back-linked and valid.
export function linkFront(head: Node, node: Node): void {
  requires(head !== node)
  requires(head.next === null)
  requires(node.next === null)
  requires(node.prev === null)
  ensures(validChain(node))
  node.next = head
  head.prev = node
}

// ✗ DISPROVED — the classic bug: without the back-pointer write, the
// chain violates n.next.prev === n.
export function buggyLink(head: Node, node: Node): void {
  requires(head !== node)
  requires(head.next === null)
  requires(node.next === null)
  ensures(validChain(node))
  node.next = head
}

// ✓ PROVED — PRESERVATION via the frame bridge: writing `value` cannot
// affect a predicate that only reads `next`/`prev`.
export function touchValue(head: Node, v: number): void {
  requires(validChain(head))
  ensures(validChain(head))
  head.value = v
}

// ✗ DISPROVED — writing `prev` on an arbitrary node MAY break the chain
// (nothing says `other` is outside it) — the bridge correctly refuses.
export function buggyTouch(head: Node, other: Node): void {
  requires(validChain(head))
  ensures(validChain(head))
  other.prev = null
}

// ── F5: ownership (Repr-lite) ────────────────────────────────────────────────
// `inChain` characterizes validChain's FOOTPRINT (which objects it reads).
// The footprint() pairing lets writes provably OUTSIDE the structure
// preserve the invariant even when they touch fields the invariant reads.

function inChain(n: Node | null, x: Node): boolean {
  return n === null ? false : n === x || inChain(n.next, x)
}
footprint(validChain, inChain)

// ✓ PROVED — same write as buggyTouch, but ownership is stated: `other`
// is outside the chain, so the invariant cannot be affected.
export function safeTouch(head: Node, other: Node): void {
  requires(validChain(head))
  requires(!inChain(head, other))
  ensures(validChain(head))
  other.prev = null
}
