# theoremts

Formal verification for TypeScript — prove your code is correct for all inputs using Z3 SMT solver.

```typescript
import { requires, ensures, positive, nonNegative, output } from 'theoremts'

function safeDivide(a: number, b: number): number {
  requires(positive(b))
  ensures(nonNegative(output()))
  return a / b
}
```

Zero runtime overhead — all exports are no-ops, stripped at build time by bundler plugins.

See [full documentation](https://github.com/theoremts/theorem).
