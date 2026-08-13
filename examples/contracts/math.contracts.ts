// @ts-nocheck — declare() mirrors the target's signature; the body only holds
// contracts, so TS would (correctly) complain about the missing return value.
import { declare, requires, ensures, nonNegative, output } from 'theoremts'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})

declare(Math.abs, (x: number): number => {
  ensures(nonNegative(output()))
})
