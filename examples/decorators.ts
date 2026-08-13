import { requires, ensures, positive, nonNegative, between, output } from 'theoremts'

// ─────────────────────────────────────────────────────────────────────────────
// Decorator style — for class methods (arrow form, valid TypeScript)
//
// Predicates receive the method's parameters as a destructured object;
// `output()` refers to the return value.
// ─────────────────────────────────────────────────────────────────────────────

class Calculator {
  @requires(({ b }) => positive(b))
  @ensures(() => output() >= 0 || output() < 0)  // always defined
  divide(a: number, b: number): number {
    return a / b
  }

  @requires(({ price }) => positive(price), ({ percent }) => between(percent, 0, 100))
  @ensures(() => nonNegative(output()))
  applyDiscount(price: number, percent: number): number {
    return price * (1 - percent / 100)
  }
}

class PaymentService {
  @requires(({ amount }) => positive(amount), ({ rate }) => between(rate, 0, 100))
  @ensures(({ amount }) => nonNegative(output()) && output() <= amount)
  calculateFee(amount: number, rate: number): number {
    return amount * rate / 100
  }

  // ✗ Bug: discount not capped
  @requires(({ price }) => positive(price), ({ discount }) => positive(discount))
  @ensures(() => nonNegative(output()))
  buggyApply(price: number, discount: number): number {
    return price - discount
  }
}

export { Calculator, PaymentService }
