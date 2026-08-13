// Class @invariant — Design by Contract for class-based models.
//
//   theorem verify examples/class-invariant.ts
//
// The invariant is declared ONCE on the class and Theorem checks it against
// every method: assumed on entry, proved on exit (mutations of `this.*` are
// tracked), and the constructor must establish it.

import { invariant, requires, positive } from 'theoremts'

@invariant((self: Account) => self.balance >= 0)
class Account {
  balance: number

  // Must ESTABLISH the invariant — proved
  constructor(initial: number) {
    requires(positive(initial))
    this.balance = initial
  }

  // Preserves: balance >= 0 ∧ amount > 0 ⇒ balance + amount >= 0 — proved
  deposit(amount: number): void {
    requires(positive(amount))
    this.balance = this.balance + amount
  }

  // Guarded mutation — the if-condition is part of the proof — proved
  withdraw(amount: number): void {
    requires(positive(amount))
    if (amount <= this.balance) {
      this.balance = this.balance - amount
    }
  }

  // ✗ BUG: no guard. balance = 0, amount = 0.5 → balance becomes -0.5.
  // TypeScript sees nothing wrong; the invariant refutes it.
  overdraw(amount: number): void {
    requires(positive(amount))
    this.balance = this.balance - amount
  }
}

export { Account }
