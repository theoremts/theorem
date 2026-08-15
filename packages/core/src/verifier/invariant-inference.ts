import type { AnyExpr, Arith, Bool, FuncDecl } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, FunctionIR, HeapStep } from '../parser/ir.js'
import { prettyExpr } from '../parser/pretty.js'

/**
 * Loop-invariant INFERENCE via constrained Horn clauses (Spacer/PDR).
 *
 * The loop becomes a transition system over its mutable numeric state:
 *
 *   init:  requires(params) ∧ entry values          →  Inv(state)
 *   step:  Inv(state) ∧ condition                   →  Inv(body(state))
 *   bad:   Inv(state) ∧ ¬condition ∧ ¬ensures       →  Err
 *
 * `query(Err) === unsat` means the ensures is protected by SOME inductive
 * invariant — and Spacer's cover of Inv IS that invariant. We read it back,
 * name the de Bruijn variables, and print it as a TypeScript predicate the
 * user can paste into `invariant(() => ...)`.
 *
 * v1 fragment: one top-level while loop whose body is straight-line numeric
 * assignments, integer-shaped state (LIA is Spacer's home turf), ensures
 * without old()/quantifiers. Anything else returns null — a suggestion
 * engine must stay silent rather than guess.
 */

export interface LoopInvariantSuggestion {
  /** TS-syntax predicates, one per conjunct, ready for invariant(() => ...) */
  invariants: string[]
  /** The ensures they make provable (pretty text). */
  protects: string
}

interface NumLoop {
  preAssigns: Array<{ name: string; value: Expr }>
  condition: Expr
  body: HeapStep[]
  resultExpr: Expr | null
}

export async function inferLoopInvariants(
  ir: FunctionIR,
  ctx: Z3Context,
): Promise<LoopInvariantSuggestion | null> {
  const shape = eligibleShape(ir.heapSteps)
  if (shape === null) return null

  const ensures = ir.contracts.filter((c): c is { kind: 'ensures'; predicate: Expr } => c.kind === 'ensures' && 'predicate' in c && typeof c.predicate === 'object' && c.predicate !== null)
  if (ensures.length === 0) return null

  // Mutable state: assigned in the loop body. Params: referenced anywhere.
  const mutableSet = new Set<string>()
  const collectMutables = (steps: HeapStep[]): void => {
    for (const st of steps) {
      if (st.kind === 'num-assign') mutableSet.add(st.name)
      else if (st.kind === 'branch') { collectMutables(st.then); collectMutables(st.else) }
    }
  }
  collectMutables(shape.body)
  const mutables = [...mutableSet]
  const paramNames = ir.params.map(p => p.name)
  const referenced = new Set<string>()
  const collectIdents = (e: Expr): void => {
    if (e.kind === 'ident') referenced.add(e.name)
    else if (e.kind === 'binary') { collectIdents(e.left); collectIdents(e.right) }
    else if (e.kind === 'unary') collectIdents(e.operand)
    else if (e.kind === 'ternary') { collectIdents(e.condition); collectIdents(e.then); collectIdents(e.else) }
    else if (e.kind === 'call') e.args.forEach(collectIdents)
  }
  collectIdents(shape.condition)
  const collectBodyIdents = (steps: HeapStep[]): void => {
    for (const st of steps) {
      if (st.kind === 'num-assign') collectIdents(st.value)
      else if (st.kind === 'branch') { collectIdents(st.condition); collectBodyIdents(st.then); collectBodyIdents(st.else) }
    }
  }
  collectBodyIdents(shape.body)
  shape.preAssigns.forEach(b => collectIdents(b.value))
  for (const c of ensures) collectIdents(c.predicate)
  if (shape.resultExpr !== null) collectIdents(shape.resultExpr)
  const usedParams = paramNames.filter(p => referenced.has(p))

  // Inv argument order: mutables then params (params pass through unchanged)
  const stateNames = [...mutables, ...usedParams]

  // All state must be integer-shaped — LIA keeps Spacer fast and complete
  // enough; anything Real-shaped bails.
  const consts = new Map<string, Arith<'main'>>()
  for (const n of stateNames) consts.set(n, ctx.Int.const(`__chc_${n}`))

  const toZ3 = (e: Expr): AnyExpr<'main'> | null => {
    switch (e.kind) {
      case 'literal':
        if (typeof e.value === 'number' && Number.isInteger(e.value)) return ctx.Int.val(e.value) as unknown as AnyExpr<'main'>
        if (typeof e.value === 'boolean') return ctx.Bool.val(e.value)
        return null
      case 'ident':
        return (consts.get(e.name) as unknown as AnyExpr<'main'>) ?? null
      case 'unary': {
        const o = toZ3(e.operand)
        if (o === null) return null
        if (e.op === '-') return (o as Arith<'main'>).neg()
        if (e.op === '!') return ctx.Not(o as Bool<'main'>)
        return null
      }
      case 'binary': {
        const l = toZ3(e.left)
        const r = toZ3(e.right)
        if (l === null || r === null) return null
        const a = l as Arith<'main'>, b = r as Arith<'main'>
        try {
          switch (e.op) {
            case '+': return a.add(b)
            case '-': return a.sub(b)
            case '*': return a.mul(b)
            case '<': return a.lt(b)
            case '<=': return a.le(b)
            case '>': return a.gt(b)
            case '>=': return a.ge(b)
            case '===': return a.eq(b)
            case '!==': return ctx.Not(a.eq(b))
            case '&&': return ctx.And(l as Bool<'main'>, r as Bool<'main'>)
            case '||': return ctx.Or(l as Bool<'main'>, r as Bool<'main'>)
            default: return null
          }
        } catch { return null }
      }
      case 'call': {
        const a0 = e.args[0] !== undefined ? toZ3(e.args[0]) : null
        if (e.callee === 'positive' && a0 !== null) return (a0 as Arith<'main'>).gt(ctx.Int.val(0))
        if (e.callee === 'nonNegative' && a0 !== null) return (a0 as Arith<'main'>).ge(ctx.Int.val(0))
        if (e.callee === 'Number.isInteger' && a0 !== null) return ctx.Bool.val(true)  // Int-sorted already
        if (e.callee === 'output' && e.args.length === 0 && shape.resultExpr !== null) return toZ3(shape.resultExpr)
        return null
      }
      default:
        return null
    }
  }

  // ── Rules ────────────────────────────────────────────────────────────────
  let fp
  let Inv: FuncDecl<'main'>
  let Err: FuncDecl<'main'>
  try {
    fp = new ctx.Fixedpoint()
    fp.set('engine', 'spacer')
    const sorts = stateNames.map(() => ctx.Int.sort())
    Inv = ctx.Function.declare('__Inv', ...sorts, ctx.Bool.sort())
    Err = ctx.Function.declare('__Err', ctx.Bool.sort())
    fp.registerRelation(Inv)
    fp.registerRelation(Err)
  } catch { return null }

  const stateConsts = stateNames.map(n => consts.get(n)!)
  const boundVars = stateConsts as unknown as Parameters<typeof ctx.ForAll>[0]

  // init: requires ∧ pre-assignments (applied in order) → Inv(entry state)
  const initConstraints: Bool<'main'>[] = []
  for (const c of ir.contracts) {
    if (c.kind !== 'requires' || !('predicate' in c) || typeof c.predicate !== 'object' || c.predicate === null) continue
    const z = toZ3(c.predicate)
    if (z !== null) initConstraints.push(z as Bool<'main'>)
    // untranslatable requires weaken the antecedent — harder, never wrong
  }
  const entryValue = new Map<string, AnyExpr<'main'>>()
  for (const pre of shape.preAssigns) {
    const v = substituted(pre.value, entryValue, toZ3, consts)
    if (v === null) return null
    entryValue.set(pre.name, v)
  }
  const initArgs = stateNames.map(n => entryValue.get(n) ?? (consts.get(n) as unknown as AnyExpr<'main'>))
  try {
    const initBody = initConstraints.length > 0
      ? ctx.Implies(ctx.And(...initConstraints), Inv.call(...initArgs) as Bool<'main'>)
      : Inv.call(...initArgs) as Bool<'main'>
    fp.addRule(ctx.ForAll(boundVars, initBody), 'init')
  } catch { return null }

  // step: Inv(state) ∧ cond → Inv(state')  (body applied sequentially)
  const condZ3 = toZ3(shape.condition)
  if (condZ3 === null) return null
  const stepValue = new Map<string, AnyExpr<'main'>>()
  const toZ3Shadowed = (e: Expr, shadow: Map<string, AnyExpr<'main'>>): AnyExpr<'main'> | null => {
    if (e.kind === 'ident' && shadow.has(e.name)) return shadow.get(e.name)!
    if (e.kind === 'binary') {
      const l = toZ3Shadowed(e.left, shadow), r = toZ3Shadowed(e.right, shadow)
      if (l === null || r === null) return null
      const a = l as Arith<'main'>, b = r as Arith<'main'>
      try {
        switch (e.op) {
          case '+': return a.add(b)
          case '-': return a.sub(b)
          case '*': return a.mul(b)
          case '<': return a.lt(b)
          case '<=': return a.le(b)
          case '>': return a.gt(b)
          case '>=': return a.ge(b)
          case '===': return a.eq(b)
          case '!==': return ctx.Not(a.eq(b))
          case '&&': return ctx.And(l as Bool<'main'>, r as Bool<'main'>)
          case '||': return ctx.Or(l as Bool<'main'>, r as Bool<'main'>)
          default: return null
        }
      } catch { return null }
    }
    if (e.kind === 'unary') {
      const o = toZ3Shadowed(e.operand, shadow)
      if (o === null) return null
      if (e.op === '-') return (o as Arith<'main'>).neg()
      if (e.op === '!') return ctx.Not(o as Bool<'main'>)
      return null
    }
    if (e.kind === 'ternary') {
      const c = toZ3Shadowed(e.condition, shadow)
      const t = toZ3Shadowed(e.then, shadow)
      const el = toZ3Shadowed(e.else, shadow)
      if (c === null || t === null || el === null) return null
      try { return ctx.If(c as Bool<'main'>, t, el) } catch { return null }
    }
    return toZ3(e)
  }
  let stepOk = true
  const applySteps = (steps: HeapStep[], pc: Bool<'main'> | null): void => {
    for (const st of steps) {
      if (!stepOk) return
      if (st.kind === 'num-assign') {
        const v = toZ3Shadowed(st.value, stepValue)
        if (v === null) { stepOk = false; return }
        const prev = stepValue.get(st.name) ?? (consts.get(st.name) as unknown as AnyExpr<'main'> | undefined)
        if (pc !== null && prev !== undefined) {
          try { stepValue.set(st.name, ctx.If(pc, v, prev)) } catch { stepOk = false }
        } else {
          stepValue.set(st.name, v)
        }
      } else if (st.kind === 'branch') {
        const c = toZ3Shadowed(st.condition, stepValue)
        if (c === null) { stepOk = false; return }
        const cond = c as Bool<'main'>
        applySteps(st.then, pc === null ? cond : ctx.And(pc, cond))
        applySteps(st.else, pc === null ? ctx.Not(cond) : ctx.And(pc, ctx.Not(cond)))
      }
    }
  }
  applySteps(shape.body, null)
  if (!stepOk) return null
  const stepArgs = stateNames.map(n => stepValue.get(n) ?? (consts.get(n) as unknown as AnyExpr<'main'>))
  try {
    fp.addRule(ctx.ForAll(boundVars, ctx.Implies(
      ctx.And(Inv.call(...stateConsts) as Bool<'main'>, condZ3 as Bool<'main'>),
      Inv.call(...stepArgs) as Bool<'main'>,
    )), 'step')
  } catch { return null }

  // bad: Inv ∧ ¬cond ∧ ¬(ensures) → Err
  const ensuresZ3: Bool<'main'>[] = []
  for (const c of ensures) {
    const z = toZ3(c.predicate)
    if (z === null) return null  // can't protect what we can't express
    ensuresZ3.push(z as Bool<'main'>)
  }
  try {
    fp.addRule(ctx.ForAll(boundVars, ctx.Implies(
      ctx.And(
        Inv.call(...stateConsts) as Bool<'main'>,
        ctx.Not(condZ3 as Bool<'main'>),
        ctx.Not(ensuresZ3.length === 1 ? ensuresZ3[0]! : ctx.And(...ensuresZ3)),
      ),
      Err.call() as Bool<'main'>,
    )), 'bad')
  } catch { return null }

  // ── Query + cover extraction ─────────────────────────────────────────────
  let result: string
  try {
    result = await fp.query(Err.call() as Bool<'main'>)
  } catch { return null }
  if (result !== 'unsat') return null

  try {
    const cover = fp.getCoverDelta(-1, Inv)
    if (cover === null) return null
    // Cover uses de Bruijn indices in Inv-argument order — name them, using
    // readable consts (no __chc_ prefix) for the printed form
    const printNames = stateNames.map(n => ctx.Int.const(n))
    const named = ctx.substituteVars(cover as AnyExpr<'main'>, ...(printNames as unknown as AnyExpr<'main'>[]))
    const simplified = await ctx.simplify(named)
    const conjuncts = splitConjuncts(simplified)
    const printed = printInvariants(conjuncts)
    if (printed.length === 0) return null
    // The CHC world is LIA — the Real-typed verifier needs the integrality
    // of loop counters stated explicitly to replay these invariants.
    const intFacts = mutables.map(m => `Number.isInteger(${m})`)
    return {
      invariants: [...intFacts, ...printed],
      protects: ensures.map(c => prettyExpr(c.predicate)).join(' && '),
    }
  } catch { return null }
}

/** Applies earlier same-block assignments when translating a RHS. */
function substituted(
  e: Expr,
  current: Map<string, AnyExpr<'main'>>,
  toZ3: (e: Expr) => AnyExpr<'main'> | null,
  consts: Map<string, Arith<'main'>>,
): AnyExpr<'main'> | null {
  // Translate with a one-off shadow: idents already assigned in this block
  // resolve to their computed value
  const shadow = (expr: Expr): AnyExpr<'main'> | null => {
    if (expr.kind === 'ident' && current.has(expr.name)) return current.get(expr.name)!
    if (expr.kind === 'binary') {
      const l = shadow(expr.left), r = shadow(expr.right)
      if (l === null || r === null) return null
      const rebuiltL = l, rebuiltR = r
      // Rebuild via toZ3 operators by delegating: easiest is to inline here
      const a = rebuiltL as Arith<'main'>, b = rebuiltR as Arith<'main'>
      try {
        switch (expr.op) {
          case '+': return a.add(b)
          case '-': return a.sub(b)
          case '*': return a.mul(b)
          default: return null
        }
      } catch { return null }
    }
    if (expr.kind === 'ident' || expr.kind === 'literal') return toZ3(expr)
    return null
  }
  const viaShadow = shadow(e)
  if (viaShadow !== null) return viaShadow
  void consts
  return toZ3(e)
}

function eligibleShape(steps: HeapStep[] | undefined): NumLoop | null {
  if (steps === undefined) return null
  const preAssigns: Array<{ name: string; value: Expr }> = []
  let loop: { condition: Expr; body: HeapStep[] } | null = null
  let resultExpr: Expr | null = null
  for (const s of steps) {
    if (s.kind === 'num-assign') {
      if (loop === null) preAssigns.push({ name: s.name, value: s.value })
      else if (s.name === '__result') resultExpr = s.value
      else return null
    } else if (s.kind === 'loop') {
      if (loop !== null) return null   // one loop only
      if (s.invariants.length > 0) return null  // user already wrote some
      loop = { condition: s.condition, body: s.body }
    } else if (s.kind === 'exit') {
      continue
    } else if (s.kind === 'alias') {
      if (loop !== null) return null
      preAssigns.push({ name: s.name, value: { kind: 'ident', name: s.of } })
    } else {
      return null
    }
  }
  if (loop === null) return null
  if (!bodyIsNumeric(loop.body)) return null
  return { preAssigns, condition: loop.condition, body: loop.body, resultExpr }
}

/** Loop bodies may be num-assigns and branches of num-assigns. */
function bodyIsNumeric(steps: HeapStep[]): boolean {
  return steps.every(s =>
    s.kind === 'num-assign' ||
    (s.kind === 'branch' && bodyIsNumeric(s.then) && bodyIsNumeric(s.else)))
}

// ── Z3 → TypeScript predicate printing ─────────────────────────────────────
//
// Spacer covers arrive as clauses like  ¬(s + (-2)·i ≤ -1). We flip the
// negation into the comparison, move negative terms across the relation,
// tighten strict integer bounds (> -1 ⇒ >= 0), and merge ≤/≥ pairs into
// equalities — turning solver output into a predicate worth pasting.

// eslint-disable-next-line @typescript-eslint/no-explicit-any
function splitConjuncts(e: any): any[] {
  /* eslint-disable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-assignment */
  try {
    if (e.decl().name() === 'and') {
      const out = []
      for (let i = 0; i < e.numArgs(); i++) out.push(...splitConjuncts(e.arg(i)))
      return out
    }
  } catch { /* not an app */ }
  return [e]
  /* eslint-enable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-assignment */
}

interface Cmp { op: string; terms: Map<string, number>; constant: number }

const FLIP: Record<string, string> = { '<=': '>', '<': '>=', '>=': '<', '>': '<=' }
const MIRROR: Record<string, string> = { '<=': '>=', '<': '>', '>=': '<=', '>': '<' }

/* eslint-disable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any, @typescript-eslint/no-unsafe-assignment, @typescript-eslint/no-unsafe-argument */

/** Numeral value of an Int term, or null. */
function numeralOf(e: any): number | null {
  const t = String(e)
  if (/^-?\d+$/.test(t)) return parseInt(t, 10)
  const m = /^\(- (\d+)\)$/.exec(t)
  return m ? -parseInt(m[1]!, 10) : null
}

/** Collects additive terms of a LIA expression into coefficient form. */
function collectTerms(e: any, sign: number, into: Cmp): boolean {
  const num = numeralOf(e)
  if (num !== null) { into.constant += sign * num; return true }
  let name: string
  try { name = e.decl().name() } catch { return false }
  if (name === '+') {
    for (let i = 0; i < e.numArgs(); i++) if (!collectTerms(e.arg(i), sign, into)) return false
    return true
  }
  if (name === '-' && e.numArgs() === 1) return collectTerms(e.arg(0), -sign, into)
  if (name === '-' && e.numArgs() === 2) {
    return collectTerms(e.arg(0), sign, into) && collectTerms(e.arg(1), -sign, into)
  }
  if (name === '*' && e.numArgs() === 2) {
    const k = numeralOf(e.arg(0))
    if (k !== null && e.arg(1).numArgs() === 0) {
      const v = e.arg(1).decl().name()
      into.terms.set(v, (into.terms.get(v) ?? 0) + sign * k)
      return true
    }
    return false
  }
  if (e.numArgs() === 0) {
    into.terms.set(name, (into.terms.get(name) ?? 0) + sign)
    return true
  }
  return false
}

/** Parses a (possibly negated) linear comparison into normal form:
 *  terms  op  constant. Returns null for anything non-linear. */
function parseCmp(e: any, negated: boolean): Cmp | null {
  let name: string
  try { name = e.decl().name() } catch { return null }
  if (name === 'not') return parseCmp(e.arg(0), !negated)
  if (!(name in MIRROR) && name !== '=') return null
  const cmp: Cmp = { op: name, terms: new Map(), constant: 0 }
  if (!collectTerms(e.arg(0), 1, cmp)) return null
  if (!collectTerms(e.arg(1), -1, cmp)) return null
  // now: terms + constant  op  0
  if (negated) {
    if (cmp.op === '=') return null   // disequalities rarely make invariants
    cmp.op = FLIP[cmp.op]!
  }
  // integer tightening: t > c  ⇒  t >= c+1 ;  t < c  ⇒  t <= c-1
  // (constant currently on the LEFT as +constant; keep normal form t op -constant)
  return cmp
}

/** Renders "terms op constant" with negative-coefficient terms moved right. */
function renderCmp(c: Cmp): string {
  let op = c.op
  let rhs = -c.constant
  if (op === '>') { op = '>='; rhs += 1 }
  if (op === '<') { op = '<='; rhs -= 1 }
  const lhsParts: string[] = []
  const rhsParts: string[] = []
  for (const [v, k] of [...c.terms].sort((a, b) => a[0].localeCompare(b[0]))) {
    if (k === 0) continue
    if (k > 0) lhsParts.push(k === 1 ? v : `${k} * ${v}`)
    else rhsParts.push(k === -1 ? v : `${-k} * ${v}`)
  }
  if (rhs > 0) rhsParts.push(String(rhs))
  if (rhs < 0) lhsParts.push(String(-rhs))
  const lhs = lhsParts.length > 0 ? lhsParts.join(' + ') : '0'
  const right = rhsParts.length > 0 ? rhsParts.join(' + ') : '0'
  const tsOp = op === '=' ? '===' : op
  return `${lhs} ${tsOp} ${right}`
}

/** Canonical key ignoring direction, used to merge <= / >= pairs into ===. */
function cmpKey(c: Cmp): string {
  const entries = [...c.terms.entries()].filter(([, k]) => k !== 0).sort((a, b) => a[0].localeCompare(b[0]))
  if (entries.length === 0) return `const:${c.constant}`
  const flip = entries[0]![1] < 0 ? -1 : 1
  return entries.map(([v, k]) => `${v}:${flip * k}`).join(',') + `|${flip * c.constant}`
}

function directionOf(c: Cmp): 1 | -1 | 0 {
  if (c.op === '=') return 0
  const entries = [...c.terms.entries()].filter(([, k]) => k !== 0).sort((a, b) => a[0].localeCompare(b[0]))
  const flip = entries.length > 0 && entries[0]![1] < 0 ? -1 : 1
  const upper = c.op === '<=' || c.op === '<'
  return (upper ? 1 : -1) * flip as 1 | -1
}

/** Full pipeline: conjunct expressions → readable TS predicates. */
function printInvariants(conjuncts: any[]): string[] {
  const parsed: Cmp[] = []
  const opaque: string[] = []
  for (const e of conjuncts) {
    const c = parseCmp(e, false)
    if (c !== null) {
      // normalize strict ops away for merging (form: terms + constant op 0)
      // t + c > 0  ⟺  t + (c - 1) >= 0 ;  t + c < 0  ⟺  t + (c + 1) <= 0
      if (c.op === '>') { c.op = '>='; c.constant -= 1 }
      if (c.op === '<') { c.op = '<='; c.constant += 1 }
      parsed.push(c)
    } else {
      const raw = String(e)
      if (raw.length < 120) opaque.push(raw)
    }
  }
  // merge <= / >= pairs over identical term vectors into =
  const byKey = new Map<string, Cmp[]>()
  for (const c of parsed) {
    const k = cmpKey(c)
    const arr = byKey.get(k) ?? []
    arr.push(c)
    byKey.set(k, arr)
  }
  const out: string[] = []
  for (const group of byKey.values()) {
    const dirs = new Set(group.map(directionOf))
    if (group.length >= 2 && dirs.has(1) && dirs.has(-1)) {
      const eq: Cmp = { op: '=', terms: group[0]!.terms, constant: group[0]!.constant }
      out.push(renderCmp(eq))
    } else {
      for (const c of group) out.push(renderCmp(c))
    }
  }
  return [...out, ...opaque]
}
/* eslint-enable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any, @typescript-eslint/no-unsafe-assignment, @typescript-eslint/no-unsafe-argument */
