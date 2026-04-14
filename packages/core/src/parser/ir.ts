// ---------------------------------------------------------------------------
// Sorts — the type system understood by the translator/solver
// ---------------------------------------------------------------------------

/**
 * Sort represents the type system understood by the translator/solver.
 * A NumericUnionSort constrains a variable to a finite set of numeric literals
 * (e.g. TypeScript type `0 | 1 | 2` for enums or status codes).
 */
export type Sort = 'int' | 'real' | 'bool' | 'string' | 'array' | 'set' | 'unknown' | NumericUnionSort

export interface NumericUnionSort {
  kind: 'numeric-union'
  values: number[]
}

// ---------------------------------------------------------------------------
// Expression IR — subset of TypeScript expressible as Z3 formulas
// ---------------------------------------------------------------------------

export type BinaryOp =
  | '+' | '-' | '*' | '/' | '%' | '**'
  | '<' | '<=' | '>' | '>='
  | '===' | '!=='
  | '&&' | '||'
  | '??'
  | 'in'

export type UnaryOp = '!' | '-' | 'typeof'

export type Expr =
  | { kind: 'literal';        value: number | boolean | null | string }
  | { kind: 'ident';          name: string }
  | { kind: 'member';         object: Expr; property: string }
  | { kind: 'element-access'; object: Expr; index: Expr }
  | { kind: 'unary';          op: UnaryOp; operand: Expr }
  | { kind: 'binary';         op: BinaryOp; left: Expr; right: Expr }
  | { kind: 'call';           callee: string; args: Expr[] }
  | { kind: 'ternary';        condition: Expr; then: Expr; else: Expr }
  | { kind: 'quantifier';     quantifier: 'forall' | 'exists'; param: string; body: Expr }
  | { kind: 'array';          elements: Expr[] }
  | { kind: 'object';         properties: Array<{ key: string; value: Expr }> }
  | { kind: 'spread';         operand: Expr }
  | { kind: 'template';       parts: Array<string | Expr> }

// ---------------------------------------------------------------------------
// Contracts
// ---------------------------------------------------------------------------

export type Predicate = Expr | string   // string = unparsed string contract

export interface RequiresContract { kind: 'requires'; predicate: Predicate }
export interface EnsuresContract  { kind: 'ensures';  predicate: Predicate }
export interface InvariantContract { kind: 'invariant'; predicate: Predicate; loopIndex?: number | undefined }
export interface DecreasesContract { kind: 'decreases'; expression: Expr; loopIndex?: number | undefined }
export interface ModifiesContract  { kind: 'modifies';  refs: string[] }
export interface CheckContract     { kind: 'check';     predicate: Predicate }
export interface AssumeContract    { kind: 'assume';    predicate: Predicate }
export interface UnreachableContract { kind: 'unreachable' }

export type Contract =
  | RequiresContract
  | EnsuresContract
  | InvariantContract
  | DecreasesContract
  | ModifiesContract
  | CheckContract
  | AssumeContract
  | UnreachableContract

// ---------------------------------------------------------------------------
// Loop IR — captures while/for loops with invariants and termination measures
// ---------------------------------------------------------------------------

export interface LoopInfo {
  /** The loop condition (e.g. `i > 0`). */
  condition: Expr
  /** The loop body as an expression, if parseable. */
  body?: Expr | undefined
  /** Invariants declared inside the loop via `invariant(() => ...)`. */
  invariants: Expr[]
  /** Termination measure declared via `decreases(() => ...)`. */
  decreases?: Expr | undefined
  /** Variable initializations preceding the loop (e.g. `let result = 1`). */
  initializations?: Array<{ name: string; value: Expr }> | undefined
}

// ---------------------------------------------------------------------------
// Function IR — everything the translator needs about one proved function
// ---------------------------------------------------------------------------

export interface Param {
  name: string
  sort: Sort
}

/**
 * A step in the body — either a code operation or a positional contract.
 * Processed in order by the translator for SSA-aware check/assume.
 */
export type BodyStep =
  | { kind: 'assign'; name: string; value: Expr }
  | { kind: 'if-assign'; name: string; condition: Expr; value: Expr; defaultValue: Expr }
  | { kind: 'check'; predicate: Predicate }
  | { kind: 'assume'; predicate: Predicate }

export interface FunctionIR {
  /** Variable name the result is bound to, or method name, if known. */
  name?: string | undefined
  params: Param[]
  returnSort: Sort
  /**
   * Expression body of the function, if it's a single-expression arrow.
   * Used by the translator to derive `result = body(params)`.
   */
  body?: Expr | undefined
  contracts: Contract[]
  /** Loops found inside the function body (for invariant/termination proofs). */
  loops?: LoopInfo[] | undefined
  /** Ordered body steps — code operations + positional check/assume. */
  bodySteps?: BodyStep[] | undefined
}
