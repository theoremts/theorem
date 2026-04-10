import type { Assume, Check, Contract, Decreases, Invariant, LoopDecreases, LoopInvariant, Modification, PostCondition, PreCondition, TheoremConfig, Unreachable } from './types.js'

export type { Assume, Check, Contract, Decreases, Invariant, LoopDecreases, LoopInvariant, Modification, PostCondition, PreCondition, TheoremConfig, Unreachable }
export type { Contract as default }

// ---------------------------------------------------------------------------
// proof
// ---------------------------------------------------------------------------

type NamedParams<TArgs extends unknown[]> = TArgs extends [infer First, ...unknown[]]
  ? First extends object
    ? First
    : Record<string, unknown>
  : Record<string, unknown>

type EnsuresParams<TArgs extends unknown[], TReturn> =
  NamedParams<TArgs> & { result: TReturn }

/**
 * Wrap an arrow/const function with contracts.
 * The function is returned unchanged — contracts exist only for static analysis.
 */
export function proof<TArgs extends unknown[], TReturn>(
  fn: (...args: TArgs) => TReturn,
  ...contracts: Contract[]
): (...args: TArgs) => TReturn
/**
 * Attach contracts to an existing function or class method reference.
 * No-op at runtime.
 */
export function proof(target: unknown, ...contracts: Contract[]): void
/**
 * Attach contracts to a reducer + action pair (e.g. NgRx).
 * No-op at runtime.
 */
export function proof(reducer: unknown, action: unknown, ...contracts: Contract[]): void
export function proof(targetOrFn: unknown, ...rest: unknown[]): unknown {
  if (
    typeof targetOrFn === 'function' &&
    rest.length > 0 &&
    isContract(rest[0])
  ) {
    return targetOrFn
  }
}

proof.fn = <TReturn>(fn: () => TReturn, ...contracts: Contract[]): TReturn => {
  return fn()
}

function isContract(value: unknown): value is Contract {
  return (
    value !== null &&
    (typeof value === 'object' || typeof value === 'function') &&
    '__type' in (value as any)
  )
}

// ---------------------------------------------------------------------------
// of — typed proxy for referencing class methods in proof()
// ---------------------------------------------------------------------------

/**
 * Creates a typed proxy of a class for referencing methods in proof().
 * No instantiation happens — property access returns the property name as a string.
 */
export function of<T extends object>(cls: new (...args: unknown[]) => T): T {
  return new Proxy<T>({} as T, {
    get: (_, prop) => prop,
  })
}

// ---------------------------------------------------------------------------
// requires
// ---------------------------------------------------------------------------

/**
 * Precondition contract. Accepts one or more predicates. Can be used as:
 *   - proof() argument: `proof(fn, requires(pred))`
 *   - Inline statement: `requires(() => x > 0)`
 *   - Method decorator: `@requires(({ x }) => x > 0)`
 *   - Multi-predicate:  `@requires(({ a }) => a > 0, ({ b }) => b > 0)`
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function requires(...conditions: Array<((params: any) => boolean) | (() => boolean) | string | boolean>): PreCondition {
  const decorator: any = (target: any, _context: any) => target
  decorator.__type = 'requires'
  return decorator as PreCondition
}

// ---------------------------------------------------------------------------
// ensures
// ---------------------------------------------------------------------------

/**
 * Postcondition contract. Accepts one or more predicates. Can be used as:
 *   - proof() argument: `proof(fn, ensures(pred))`
 *   - Inline statement: `ensures(({ result }) => result > 0)`
 *   - Method decorator: `@ensures(({ result }) => result > 0)`
 *   - Compound: `@ensures(({ result, x }) => result >= 0 && result <= x)`
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function ensures(...conditions: Array<((params: any) => boolean) | (() => boolean) | string | boolean>): PostCondition {
  const decorator: any = (target: any, _context: any) => target
  decorator.__type = 'ensures'
  return decorator as PostCondition
}

// ---------------------------------------------------------------------------
// invariant
// ---------------------------------------------------------------------------

export function invariant(condition: () => boolean): Invariant
export function invariant(description: string): Invariant
export function invariant(_: unknown): Invariant {
  return { __type: 'invariant' }
}

// ---------------------------------------------------------------------------
// decreases
// ---------------------------------------------------------------------------

export function decreases(expression: (() => number) | number): Decreases
export function decreases(_: unknown): Decreases {
  return { __type: 'decreases' }
}

// ---------------------------------------------------------------------------
// modifies
// ---------------------------------------------------------------------------

export function modifies(...refs: string[]): Modification {
  return { __type: 'modifies', refs }
}

// ---------------------------------------------------------------------------
// loop — fluent API for loop contracts: loop(0).invariant(() => ...).decreases(() => ...)
// ---------------------------------------------------------------------------

interface LoopBuilder {
  invariant(condition: ((params: any) => boolean) | (() => boolean)): LoopBuilder & LoopInvariant
  decreases(expression: () => number): LoopBuilder & LoopDecreases
}

/**
 * References a loop by index (0-based) for attaching invariants and termination measures.
 *
 *   loop(0).invariant(() => x > 0)
 *   loop(0).decreases(() => n - i)
 */
export function loop(index: number): LoopBuilder {
  const builder: any = {
    __type: 'loop-invariant',
    loopIndex: index,
    invariant(_: any) {
      return { ...builder, __type: 'loop-invariant' }
    },
    decreases(_: any) {
      return { ...builder, __type: 'loop-decreases' }
    },
  }
  return builder
}

// ---------------------------------------------------------------------------
// check — mid-point verification (no-op at runtime)
// ---------------------------------------------------------------------------

/**
 * Proves a condition holds at a specific point in the function body.
 * No-op at runtime — the engine verifies statically.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function check(condition: (() => boolean) | ((params: any) => boolean) | boolean): Check {
  return { __type: 'check' }
}

// ---------------------------------------------------------------------------
// assume — assume without proof (no-op at runtime)
// ---------------------------------------------------------------------------

/**
 * Adds a fact to the solver without proving it. Used for integration with
 * external code whose behavior Theorem cannot analyze.
 * No-op at runtime — the engine uses it as an assumption.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function assume(condition: (() => boolean) | ((params: any) => boolean) | boolean): Assume {
  return { __type: 'assume' }
}

// ---------------------------------------------------------------------------
// unreachable — prove dead code (no-op at runtime)
// ---------------------------------------------------------------------------

/**
 * Proves that a code point can never be reached given the preceding constraints.
 * No-op at runtime — the engine verifies by asserting `false` (expecting UNSAT).
 */
export function unreachable(): Unreachable {
  return { __type: 'unreachable' }
}

// ---------------------------------------------------------------------------
// old — value of expression at function entry (no-op at runtime)
// ---------------------------------------------------------------------------

export function old<T>(value: T): T {
  return value
}

// ---------------------------------------------------------------------------
// Quantifiers
// ---------------------------------------------------------------------------

/** Z3 quantifier form: `forall(x => P(x))` — always true at runtime. */
export function forall(predicate: (x: any) => boolean): boolean
/** Array form: `forall(arr, (item) => P(item))` — checks every element. */
export function forall<T>(arr: T[], predicate: (item: T, index: number) => boolean): boolean
export function forall(...args: unknown[]): boolean {
  if (args.length === 1) return true  // Z3 quantifier — no-op at runtime
  const [arr, pred] = args as [unknown[], (...a: unknown[]) => boolean]
  return arr.every(pred)
}

/** Z3 quantifier form: `exists(x => P(x))` — always true at runtime. */
export function exists(predicate: (x: any) => boolean): boolean
/** Array form: `exists(arr, (item) => P(item))` — checks some element. */
export function exists<T>(arr: T[], predicate: (item: T, index: number) => boolean): boolean
export function exists(...args: unknown[]): boolean {
  if (args.length === 1) return true  // Z3 quantifier — no-op at runtime
  const [arr, pred] = args as [unknown[], (...a: unknown[]) => boolean]
  return arr.some(pred)
}

// ---------------------------------------------------------------------------
// defineConfig — identity helper for typed config files
// ---------------------------------------------------------------------------

/**
 * Identity function that provides type-checking for `theorem.config.ts`.
 * Returns the config object unchanged.
 */
export function defineConfig(config: TheoremConfig): TheoremConfig {
  return config
}

// ---------------------------------------------------------------------------
// declare — attach contracts to external functions (no-op at runtime)
// ---------------------------------------------------------------------------

/**
 * Declare contracts for external functions (libraries, APIs, builtins).
 * Used in `.contracts.ts` files to specify preconditions and postconditions
 * for functions that Theorem cannot analyze directly.
 *
 * No-op at runtime — contracts exist for static analysis only.
 *
 *   declare(Math.sqrt, (x: number): number => {
 *     requires(x >= 0)
 *     ensures(nonNegative(output()))
 *   })
 */
export function declare(_fn: unknown, _contract: unknown): void {
  // no-op at runtime — contracts exist for static analysis only
}

export * from './helpers.js'
