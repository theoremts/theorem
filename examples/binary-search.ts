// Quantified array contracts — forall/exists/sorted over Int indices.
//
//   theorem verify examples/binary-search.ts
//
// The classic lower-bound binary search (C++ std::lower_bound): returns the
// first index whose element is >= target. Sortedness and the two quantified
// loop invariants are everything the proof needs — including that a missing
// `+ 1` (the textbook non-termination/off-by-one bug) is refuted.

import { requires, ensures, invariant, decreases, sorted, forall, output, old } from 'theoremts'

// ✓ PROVED — all five obligations per invariant + the quantified ensures
export function lowerBound(arr: number[], target: number): number {
  requires(sorted(arr))
  ensures(output() >= 0)
  ensures(output() <= arr.length)
  // Everything left of the answer is < target; everything from it on is >= target
  ensures(forall(arr, (x, i) => i < output() ? x < target : x >= target))

  let lo = 0
  let hi = arr.length

  while (lo < hi) {
    invariant(() => lo >= 0 && lo <= hi && hi <= arr.length)
    invariant(() => forall(arr, (x, i) => i < lo ? x < target : true))
    invariant(() => forall(arr, (x, i) => i >= hi ? x >= target : true))
    decreases(() => hi - lo)

    const mid = Math.floor((lo + hi) / 2)
    if (arr[mid]! < target) {
      lo = mid + 1
    } else {
      hi = mid
    }
  }

  return lo
}

// ✗ DISPROVED — the textbook bug: `lo = mid` instead of `lo = mid + 1`.
// With lo === mid the loop can stop shrinking; the decreases measure is
// refuted (hi - lo no longer strictly decreases).
export function lowerBoundStuck(arr: number[], target: number): number {
  requires(sorted(arr))
  ensures(output() >= 0)

  let lo = 0
  let hi = arr.length

  while (lo < hi) {
    invariant(() => lo >= 0 && lo <= hi && hi <= arr.length)
    decreases(() => hi - lo)

    const mid = Math.floor((lo + hi) / 2)
    if (arr[mid]! < target) {
      lo = mid          // BUG: must be mid + 1
    } else {
      hi = mid
    }
  }

  return lo
}

// ✗ DISPROVED — without requires(sorted(arr)) the left-half invariant is
// not preserved: skipping the left half is only justified by order.
export function lowerBoundUnsorted(arr: number[], target: number): number {
  ensures(output() >= 0)

  let lo = 0
  let hi = arr.length

  while (lo < hi) {
    invariant(() => lo >= 0 && lo <= hi && hi <= arr.length)
    invariant(() => forall(arr, (x, i) => i < lo ? x < target : true))
    decreases(() => hi - lo)

    const mid = Math.floor((lo + hi) / 2)
    if (arr[mid]! < target) {
      lo = mid + 1
    } else {
      hi = mid
    }
  }

  return lo
}

// ── Array.prototype.sort as a trusted contract ───────────────────────────────
// `data.sort((a, b) => a - b)` HAVOCS the array (element positions changed —
// every prior content fact dies) and grants sortedness, the trusted
// postcondition of the numeric ascending comparator.

// ✓ PROVED — the sort establishes lowerBound's requires(sorted(arr))
export function findAnywhere(data: number[], target: number): number {
  data.sort((a, b) => a - b)
  return lowerBound(data, target)
}

// ✗ DISPROVED at the call site — nothing establishes sortedness
export function findUnsorted(data: number[], target: number): number {
  return lowerBound(data, target)
}

// ✗ DISPROVED — the classic JS footgun: bare .sort() is LEXICOGRAPHIC
// ([10, 9].sort() stays [10, 9]). No comparator, no sortedness granted.
export function sortFootgun(data: number[]): void {
  ensures(sorted(data))
  data.sort()
}

// ✗ DISPROVED — havoc is honest: after sorting, pre-sort content facts die
export function staleAfterSort(data: number[]): void {
  requires(data.length >= 1)
  ensures(data[0]! === old(data[0]!))
  data.sort((a, b) => a - b)
}
