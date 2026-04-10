import type { AnyExpr } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Param, Sort } from '../parser/ir.js'

/**
 * Creates a Z3 constant for every function parameter plus a `result` variable.
 * Member-access variables (e.g. `from.balance`) are added lazily by the
 * expression translator when it first encounters them.
 */
export function createVariables(
  params: Param[],
  returnSort: Sort,
  ctx: Z3Context,
): Map<string, AnyExpr<'main'>> {
  const vars = new Map<string, AnyExpr<'main'>>()

  for (const param of params) {
    vars.set(param.name, makeConst(param.name, param.sort, ctx))
    if (param.sort === 'set') registerSetVariable(param.name)
  }

  // `result` is the return value referenced in `ensures` contracts
  vars.set('result', makeConst('result', returnSort, ctx))
  if (returnSort === 'set') registerSetVariable('result')

  return vars
}

export function makeConst(name: string, sort: Sort, ctx: Z3Context): AnyExpr<'main'> {
  if (typeof sort === 'object' && sort.kind === 'numeric-union') {
    // Numeric union types use Int sort — domain constraints are added separately
    return ctx.Int.const(name)
  }
  switch (sort) {
    case 'int':    return ctx.Int.const(name)
    case 'bool':   return ctx.Bool.const(name)
    case 'string': return ctx.String.const(name) as unknown as AnyExpr<'main'>
    case 'array':  return makeArrayConst(name, ctx)
    case 'set':    return makeSetConst(name, ctx)
    default:       return ctx.Real.const(name)
  }
}

/**
 * Creates a Z3 SMT Array constant: Array(Int → Real).
 * This models TypeScript number arrays where indices are integers
 * and values are reals.
 */
export function makeArrayConst(name: string, ctx: Z3Context): AnyExpr<'main'> {
  try {
    return ctx.Array.const(name, ctx.Int.sort(), ctx.Real.sort()) as unknown as AnyExpr<'main'>
  } catch {
    // Fallback: if Array creation fails, use a free Real variable
    return ctx.Real.const(name)
  }
}

/**
 * Checks whether a Z3 expression is an SMT Array.
 */
export function isArrayExpr(expr: AnyExpr<'main'>, ctx: Z3Context): boolean {
  try {
    return ctx.isArray(expr)
  } catch {
    return false
  }
}

/**
 * Creates a Z3 Set constant: Set(Real).
 * This models TypeScript Set<number> where elements are reals.
 * Z3 Sets are implemented as Arrays (Elem → Bool).
 */
export function makeSetConst(name: string, ctx: Z3Context): AnyExpr<'main'> {
  try {
    return ctx.Set.const(name, ctx.Real.sort()) as unknown as AnyExpr<'main'>
  } catch {
    // Fallback: if Set creation fails, use a free Real variable
    return ctx.Real.const(name)
  }
}

/** Names of variables created as Z3 Sets (tracked for method dispatch). */
const setVariableNames = new Set<string>()

/**
 * Registers a variable name as a Z3 Set.
 * Called when creating Set constants so isSetExpr can identify them.
 */
export function registerSetVariable(name: string): void {
  setVariableNames.add(name)
}

/**
 * Checks whether a variable name was registered as a Z3 Set.
 */
export function isSetVariable(name: string): boolean {
  return setVariableNames.has(name)
}

/**
 * Checks whether a Z3 expression is a Seq (string).
 */
export function isStringExpr(expr: AnyExpr<'main'>, ctx: Z3Context): boolean {
  try {
    return ctx.isString(expr)
  } catch {
    return false
  }
}
