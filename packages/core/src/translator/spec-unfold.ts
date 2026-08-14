import type { Expr } from '../parser/ir.js'
import { substituteExpr } from './substitution.js'
import { prettyExpr } from '../parser/pretty.js'

/**
 * Spec functions via ground definitional axioms (Dafny-style fuel).
 *
 * A spec function is any pure same-file function whose body folds to a
 * single expression — including RECURSIVE ones:
 *
 *   function allPositive(n: Node | null): boolean {
 *     return n === null ? true : n.value > 0 && allPositive(n.next)
 *   }
 *
 * Calls in contract predicates are NOT substituted away. Instead every call
 * becomes an uninterpreted application (`__ufb_f` / `__ufr_f`), and for each
 * distinct call term we emit a GROUND definitional axiom, recursively up to
 * FUEL levels:
 *
 *   __ufb_allPositive(tail) === (tail === null ? true
 *                                : tail.value > 0 && __ufb_allPositive(tail.next))
 *   __ufb_allPositive(tail.next) === (...)          // fuel level 2
 *
 * Keeping the application preserves CONGRUENCE: `allPositive(result.next)`
 * equals `allPositive(tail)` whenever `result.next = tail` holds — which is
 * exactly how a producer's body equation connects its output to the
 * hypothesis about the input. Ground instantiation (no quantifiers) keeps
 * the solver behavior predictable.
 */

export interface SpecDef {
  params: string[]
  body: Expr
  /** Whether the definition's root expression is boolean-valued. */
  isBool: boolean
  /** Whether the definition's root expression is sequence-valued. */
  isSeq: boolean
}

export type SpecDefs = Map<string, SpecDef>

export const DEFAULT_FUEL = 2

/** Marker prefixes consumed by the translator's call handler. */
export const UF_BOOL_PREFIX = '__ufb_'
export const UF_REAL_PREFIX = '__ufr_'
export const UF_SEQ_PREFIX = '__ufs_'

export interface UnfoldResult {
  /** The predicate with spec calls turned into uninterpreted applications. */
  expr: Expr
  /** Ground definitional axioms for every call instance, fuel-bounded. */
  axioms: Array<{ text: string; predicate: Expr }>
}

export function unfoldSpecCalls(expr: Expr, defs: SpecDefs, fuel = DEFAULT_FUEL): UnfoldResult {
  const axioms: Array<{ text: string; predicate: Expr }> = []
  const seen = new Set<string>()

  const toUF = (e: Expr): Expr => {
    switch (e.kind) {
      case 'call': {
        const args = e.args.map(toUF)
        const def = defs.get(e.callee)
        if (def === undefined) return { kind: 'call', callee: e.callee, args }
        instantiate(e.callee, def, args, fuel)
        return { kind: 'call', callee: ufName(e.callee, def), args }
      }
      case 'binary':
        return { kind: 'binary', op: e.op, left: toUF(e.left), right: toUF(e.right) }
      case 'unary':
        return { kind: 'unary', op: e.op, operand: toUF(e.operand) }
      case 'ternary':
        return { kind: 'ternary', condition: toUF(e.condition), then: toUF(e.then), else: toUF(e.else) }
      case 'member':
        return { kind: 'member', object: toUF(e.object), property: e.property }
      case 'element-access':
        return { kind: 'element-access', object: toUF(e.object), index: toUF(e.index) }
      case 'array':
        return { kind: 'array', elements: e.elements.map(toUF) }
      case 'spread':
        return { kind: 'spread', operand: toUF(e.operand) }
      default:
        return e
    }
  }

  const instantiate = (name: string, def: SpecDef, args: Expr[], remaining: number): void => {
    if (remaining <= 0) return
    const call: Expr = { kind: 'call', callee: ufName(name, def), args }
    const key = prettyExpr(call)
    if (seen.has(key)) return
    seen.add(key)

    const mapping = new Map<string, Expr>()
    for (let i = 0; i < Math.min(def.params.length, args.length); i++) {
      mapping.set(def.params[i]!, args[i]!)
    }
    const instantiated = substituteExpr(def.body, mapping)

    // Convert the instantiated body's own spec calls to UF applications,
    // recursively instantiating THEIR axioms with one less fuel
    const body = convertBody(instantiated, remaining - 1)

    axioms.push({
      text: `def ${name}(${args.map(a => prettyExpr(a)).join(', ')})`,
      predicate: { kind: 'binary', op: '===', left: call, right: body },
    })
  }

  const convertBody = (e: Expr, remaining: number): Expr => {
    switch (e.kind) {
      case 'call': {
        const args = e.args.map(a => convertBody(a, remaining))
        const def = defs.get(e.callee)
        if (def === undefined) return { kind: 'call', callee: e.callee, args }
        instantiate(e.callee, def, args, remaining)
        return { kind: 'call', callee: ufName(e.callee, def), args }
      }
      case 'binary':
        return { kind: 'binary', op: e.op, left: convertBody(e.left, remaining), right: convertBody(e.right, remaining) }
      case 'unary':
        return { kind: 'unary', op: e.op, operand: convertBody(e.operand, remaining) }
      case 'ternary':
        return { kind: 'ternary', condition: convertBody(e.condition, remaining), then: convertBody(e.then, remaining), else: convertBody(e.else, remaining) }
      case 'member':
        return { kind: 'member', object: convertBody(e.object, remaining), property: e.property }
      case 'element-access':
        return { kind: 'element-access', object: convertBody(e.object, remaining), index: convertBody(e.index, remaining) }
      case 'array':
        return { kind: 'array', elements: e.elements.map(el => convertBody(el, remaining)) }
      case 'spread':
        return { kind: 'spread', operand: convertBody(e.operand, remaining) }
      default:
        return e
    }
  }

  return { expr: toUF(expr), axioms }
}

function ufName(name: string, def: SpecDef): string {
  const prefix = def.isSeq ? UF_SEQ_PREFIX : def.isBool ? UF_BOOL_PREFIX : UF_REAL_PREFIX
  return `${prefix}${name}`
}

/**
 * Rewrites null comparisons into VALUE comparisons against `__nullref`.
 *
 * The default encoding models `x === null` as an independent boolean
 * variable per NAME — which breaks congruence in spec reasoning:
 * `result.next = tail` would not propagate nullness. Within spec-function
 * tasks, null must be a VALUE so equalities carry it.
 */
export function rewriteNullToRef(expr: Expr): Expr {
  switch (expr.kind) {
    case 'binary': {
      if ((expr.op === '===' || expr.op === '!==')) {
        const leftNull = expr.left.kind === 'literal' && expr.left.value === null
        const rightNull = expr.right.kind === 'literal' && expr.right.value === null
        if (leftNull || rightNull) {
          const subject = rewriteNullToRef(leftNull ? expr.right : expr.left)
          return { kind: 'binary', op: expr.op, left: subject, right: { kind: 'ident', name: '__nullref' } }
        }
      }
      return { kind: 'binary', op: expr.op, left: rewriteNullToRef(expr.left), right: rewriteNullToRef(expr.right) }
    }
    case 'unary':
      return { kind: 'unary', op: expr.op, operand: rewriteNullToRef(expr.operand) }
    case 'ternary':
      return { kind: 'ternary', condition: rewriteNullToRef(expr.condition), then: rewriteNullToRef(expr.then), else: rewriteNullToRef(expr.else) }
    case 'call':
      return { kind: 'call', callee: expr.callee, args: expr.args.map(rewriteNullToRef) }
    case 'member':
      return { kind: 'member', object: rewriteNullToRef(expr.object), property: expr.property }
    case 'element-access':
      return { kind: 'element-access', object: rewriteNullToRef(expr.object), index: rewriteNullToRef(expr.index) }
    case 'array':
      return { kind: 'array', elements: expr.elements.map(rewriteNullToRef) }
    case 'spread':
      return { kind: 'spread', operand: rewriteNullToRef(expr.operand) }
    default:
      return expr
  }
}
