import { ensures, nonNegative, output } from 'theoremts'

// Clamping guards instead of requires: the function accepts ANY input and
// normalizes it, so the ensures holds unconditionally — and Theorem proves it.
// The parser tracks branch reassignment SSA-style: `if (a < 0) a = 0` becomes
// the binding a := (a < 0 ? 0 : a), and ensures sees the final state.
function clampedAdd(a: number, b: number): number {
  if (a < 0) {
    a = 0
  }

  if (b < 0) {
    b = 0
  }

  ensures(nonNegative(output()))
  return a + b
}

export { clampedAdd }
