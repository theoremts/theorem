import { init } from 'z3-solver'
import type { Context } from 'z3-solver'

export type Z3Context = Context<'main'>

let ctx: Z3Context | null = null

/**
 * Returns the singleton Z3 context, initializing it on first call.
 * Subsequent calls return the cached instance (WASM init is expensive).
 */
export async function getContext(): Promise<Z3Context> {
  if (ctx === null) {
    const { Context } = await init()
    ctx = Context('main')
  }
  return ctx
}
