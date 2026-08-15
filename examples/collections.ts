// Collection vocabulary — one word per property, plus folds.
//
//   theorem verify examples/collections.ts
//
// unique / uniqueBy / sortedBy / forall / exists quantify over elements;
// sumBy / countBy are FOLDS: heap-versioned symbols whose delta axioms make
// conservation provable. Loops with no invariant() at all are handled by
// Houdini: requires/ensures conjuncts are guess-and-checked and survivors
// show up marked (auto).

import {
  requires, ensures, invariant, decreases,
  unique, uniqueBy, sortedBy, forall, sumBy, countBy,
  positive, nonNegative, old, output,
} from 'theoremts'

interface Account { id: number; balance: number }

// ── The fintech property: transfer conserves the total ──────────────────────

// ✓ PROVED — even when i === j (debit and credit hit the same cell and
// cancel; the solver explores the aliasing case by itself). The delta
// axioms REQUIRE unique(users): a duplicated reference would count its
// delta twice.
export function transfer(users: Account[], i: number, j: number, amt: number): void {
  requires(unique(users))
  requires(Number.isInteger(i))
  requires(Number.isInteger(j))
  requires(i >= 0)
  requires(i < users.length)
  requires(j >= 0)
  requires(j < users.length)
  requires(positive(amt))
  ensures(sumBy(users, (u) => u.balance) === old(sumBy(users, (u) => u.balance)))

  users[i]!.balance = users[i]!.balance - amt
  users[j]!.balance = users[j]!.balance + amt
}

// ✗ DISPROVED — the phantom fee: credited but never debited. Money out of
// thin air is exactly what sum conservation refuses to prove.
export function transferWithPhantomFee(users: Account[], i: number, j: number, amt: number): void {
  requires(unique(users))
  requires(Number.isInteger(i))
  requires(Number.isInteger(j))
  requires(i >= 0)
  requires(i < users.length)
  requires(j >= 0)
  requires(j < users.length)
  requires(positive(amt))
  ensures(sumBy(users, (u) => u.balance) === old(sumBy(users, (u) => u.balance)))

  users[i]!.balance = users[i]!.balance - amt
  users[j]!.balance = users[j]!.balance + amt + 1
}

// ── countBy: predicate cardinality with exact deltas ────────────────────────

// ✓ PROVED — zeroing a positive account drops the positive-count by exactly 1
export function zeroOut(users: Account[], k: number): void {
  requires(unique(users))
  requires(Number.isInteger(k))
  requires(k >= 0)
  requires(k < users.length)
  requires(users[k]!.balance > 0)
  ensures(countBy(users, (u) => u.balance > 0) === old(countBy(users, (u) => u.balance > 0)) - 1)

  users[k]!.balance = 0
}

// ── sum invariants THROUGH loops ────────────────────────────────────────────

// ✓ PROVED — crediting 1 per iteration grows the total by exactly n
export function creditLoop(users: Account[], n: number): void {
  requires(unique(users))
  requires(Number.isInteger(n))
  requires(nonNegative(n))
  requires(n <= users.length)
  ensures(sumBy(users, (u) => u.balance) === old(sumBy(users, (u) => u.balance)) + n)

  let k = 0
  invariant(() => Number.isInteger(k))
  invariant(() => k >= 0)
  invariant(() => k <= n)
  invariant(() => sumBy(users, (u) => u.balance) === old(sumBy(users, (u) => u.balance)) + k)
  decreases(() => n - k)
  while (k < n) {
    users[k]!.balance = users[k]!.balance + 1
    k = k + 1
  }
}

// ── Houdini: the invariant writes itself ────────────────────────────────────

// ✓ PROVED with ZERO written invariants — the requires/ensures conjunct
// forall(u.balance >= 0) is guess-and-checked and survives, shown as (auto).
export function creditAllAuto(users: Account[], bonus: number, n: number): void {
  requires(positive(bonus))
  requires(nonNegative(n))
  requires(forall(users, (u) => u.balance >= 0))
  ensures(forall(users, (u) => u.balance >= 0))

  let k = 0
  while (k < n) {
    decreases(() => n - k)
    users[k]!.balance = users[k]!.balance + bonus
    k = k + 1
  }
}

// ── uniqueBy / sortedBy: projected fields ───────────────────────────────────

// ✓ PROVED — pairwise-distinct ids make slot inequality provable
export function idsDiffer(users: Account[]): boolean {
  requires(users.length >= 2)
  requires(uniqueBy(users, (u) => u.id))
  ensures(output() === true)
  return users[0]!.id !== users[1]!.id
}

// ✓ PROVED — ordered by balance: the first element is the minimum
export function poorestFirst(users: Account[]): number {
  requires(users.length >= 2)
  requires(sortedBy(users, (u) => u.balance))
  ensures(output() <= users[1]!.balance)
  return users[0]!.balance
}
