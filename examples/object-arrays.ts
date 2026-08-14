// Arrays of OBJECTS — Account[] is an array of references.
//
//   theorem verify examples/object-arrays.ts
//
// users[i].balance composes the two theories: Select(heap_balance,
// Select(users, i)). Two slots holding the SAME object — in-array aliasing,
// invisible to any type system — is a case the solver explores, exactly
// like the drainUnsafe aliasing example, now inside an array.

import { requires, ensures, invariant, decreases, forall, positive, nonNegative, old } from 'theoremts'

interface Account { balance: number }

// ✗ DISPROVED — the classic in-array aliasing bug: if users[0] and users[1]
// are the same object, the second write lands on the same cell and slot 0's
// ensures reads old + 2*bonus.
export function payBonusUnsafe(users: Account[], bonus: number): void {
  requires(users.length >= 2)
  requires(positive(bonus))
  ensures(users[0]!.balance === old(users[0]!.balance) + bonus)
  ensures(users[1]!.balance === old(users[1]!.balance) + bonus)

  users[0]!.balance = users[0]!.balance + bonus
  users[1]!.balance = users[1]!.balance + bonus
}

// ✓ PROVED — with distinct slots both ensures hold.
export function payBonusSafe(users: Account[], bonus: number): void {
  requires(users.length >= 2)
  requires(users[0]! !== users[1]!)
  requires(positive(bonus))
  ensures(users[0]!.balance === old(users[0]!.balance) + bonus)
  ensures(users[1]!.balance === old(users[1]!.balance) + bonus)

  users[0]!.balance = users[0]!.balance + bonus
  users[1]!.balance = users[1]!.balance + bonus
}

// ✓ PROVED — a quantified invariant over element FIELDS, preserved by a
// loop of writes WITHOUT any distinctness hypothesis: crediting a positive
// amount keeps every balance non-negative no matter which slots alias.
export function creditAll(users: Account[], bonus: number, n: number): void {
  requires(positive(bonus))
  requires(nonNegative(n))
  requires(forall(users, (u) => u.balance >= 0))
  ensures(forall(users, (u) => u.balance >= 0))

  let k = 0
  while (k < n) {
    invariant(() => forall(users, (u) => u.balance >= 0))
    decreases(() => n - k)

    users[k]!.balance = users[k]!.balance + bonus
    k = k + 1
  }
}

// ✗ DISPROVED — same loop, but debiting: nothing guarantees the balance
// stays non-negative once you subtract.
export function debitAll(users: Account[], fee: number, n: number): void {
  requires(positive(fee))
  requires(nonNegative(n))
  requires(forall(users, (u) => u.balance >= 0))
  ensures(forall(users, (u) => u.balance >= 0))

  let k = 0
  while (k < n) {
    invariant(() => forall(users, (u) => u.balance >= 0))
    decreases(() => n - k)

    users[k]!.balance = users[k]!.balance - fee
    k = k + 1
  }
}

// ── Call sites ───────────────────────────────────────────────────────────────
// Cross-function: a verified caller must PROVE the callee's requires from
// its own; bare calls are checked against literal arguments.

// ✓ PROVED — every requires of payBonusSafe flows from the enclosing ones
// (including positive(amount * 3) from positive(amount)).
export function quarterlyBonus(users: Account[], amount: number): void {
  requires(users.length >= 2)
  requires(users[0]! !== users[1]!)
  requires(positive(amount))

  payBonusSafe(users, amount * 3)
}

// ✓ PROVED — an array LITERAL establishes structural facts: exact length,
// and object literals are fresh, pairwise-DISTINCT references. Both of
// payBonusSafe's array requires follow with no requires of our own.
export function quarterlyBonusFresh(amount: number): void {
  requires(positive(amount))

  let users: Account[] = [{ balance: 100 }, { balance: 200 }]

  payBonusSafe(users, amount)
}

// ✗ DISPROVED at the call site — the caller never established the array
// facts: users.length >= 2 and users[0] !== users[1] are both refuted.
export function quarterlyBonusSloppy(users: Account[], amount: number): void {
  requires(positive(amount))

  payBonusSafe(users, amount)
}

// ✗ DISPROVED — bare call with a literal: positive(bonus) is violated
// outright ("violation confirmed"), and nothing establishes the array facts.
declare const accounts: Account[]
payBonusUnsafe(accounts, -5)
