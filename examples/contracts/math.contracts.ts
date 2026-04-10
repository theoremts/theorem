import { declare, requires, ensures, nonNegative, output } from 'theorem'

declare(Math.sqrt, (x: number): number => {
  requires(x >= 0)
  ensures(nonNegative(output()))
})

declare(Math.abs, (x: number): number => {
  ensures(nonNegative(output()))
})
