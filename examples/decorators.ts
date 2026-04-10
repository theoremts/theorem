import { requires, ensures, positive, nonNegative, between, output } from 'theorem'

// ─────────────────────────────────────────────────────────────────────────────
// Decorator style — for class methods only (TypeScript limitation)
// ─────────────────────────────────────────────────────────────────────────────

class Calculator {
  @requires(positive(b))
  @ensures(output() >= 0 || output() < 0)  // always defined
  divide(a: number, b: number): number {
    return a / b
  }

  @requires(positive(price), between(percent, 0, 100))
  @ensures(nonNegative(output()))
  applyDiscount(price: number, percent: number): number {
    return price * (1 - percent / 100)
  }
}

class PaymentService {
  @requires(positive(amount), between(rate, 0, 100))
  @ensures(nonNegative(output()), output() <= amount)
  calculateFee(amount: number, rate: number): number {
    return amount * rate / 100
  }

  // ✗ Bug: discount not capped
  @requires(positive(price), positive(discount))
  @ensures(nonNegative(output()))
  buggyApply(price: number, discount: number): number {
    return price - discount
  }
}

export { Calculator, PaymentService }
