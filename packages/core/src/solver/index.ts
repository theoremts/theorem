import type { Bool, AnyExpr, Arith } from 'z3-solver'
import { getContext } from './context.js'
import type { SolverResult } from './result.js'

export type { Z3Context } from './context.js'
export type { SolverResult, ProvedResult, DisprovedResult, UnknownResult } from './result.js'
export { getContext }

type Z3Bool = Bool<'main'>

const DEFAULT_TIMEOUT_MS = 10_000

export interface CheckInput {
  variables: Map<string, AnyExpr<'main'>>
  assumptions: Z3Bool[]
  /**
   * Labels for each assumption — when provided, the solver tracks which
   * were used and reports them via unsat cores.  Must be same length as
   * `assumptions` or omitted entirely.
   */
  assumptionLabels?: string[]
  goal: Z3Bool
  timeout?: number
  /** Domain constraints (e.g. `.length >= 0`). Always asserted, never tracked. */
  domainConstraints?: Z3Bool[]
  /** Number of distinct counterexamples to find (default 1). */
  maxCounterexamples?: number
  /** Use Optimize solver to produce the smallest counterexample. */
  minimizeCounterexample?: boolean
  /** Named intermediate expressions to evaluate in counterexamples. */
  traceExprs?: Map<string, AnyExpr<'main'>> | undefined
  /** Source locations of trace expressions for error highlighting. */
  traceLocs?: Map<string, { line: number; column: number }> | undefined
}

// ---------------------------------------------------------------------------
// Main check
// ---------------------------------------------------------------------------

export async function check(input: CheckInput): Promise<SolverResult> {
  const {
    variables,
    assumptions,
    assumptionLabels,
    goal,
    timeout = DEFAULT_TIMEOUT_MS,
    domainConstraints = [],
    maxCounterexamples = 1,
    minimizeCounterexample = false,
  } = input

  const Z3 = await getContext()
  const solver = new Z3.Solver()
  solver.set('timeout', timeout)

  // ── Domain constraints (always asserted, not tracked) ────────────────────
  for (const dc of domainConstraints) solver.add(dc)

  // ── Assumptions — optionally tracked for unsat cores ─────────────────────
  const tracked = assumptionLabels !== undefined && assumptionLabels.length === assumptions.length
  const trackingLabels: Z3Bool[] = []

  if (tracked) {
    for (let i = 0; i < assumptions.length; i++) {
      const label = Z3.Bool.const(`__req_${i}`)
      solver.addAndTrack(assumptions[i]!, label)
      trackingLabels.push(label)
    }
  } else {
    for (const a of assumptions) solver.add(a)
  }

  // ── Check — goal passed as temporary assumption (not permanently added) ──
  const status = await solver.check(goal)

  // ── UNSAT → proved ───────────────────────────────────────────────────────
  if (status === 'unsat') {
    let usedAssumptions: string[] | undefined
    if (tracked && assumptionLabels) {
      try {
        const core = solver.unsatCore()
        const coreStrs = new Set<string>()
        for (let i = 0; i < core.length(); i++) coreStrs.add(core.get(i).toString())
        usedAssumptions = []
        for (let i = 0; i < trackingLabels.length; i++) {
          if (coreStrs.has(trackingLabels[i]!.toString())) {
            usedAssumptions.push(assumptionLabels[i]!)
          }
        }
      } catch { /* core extraction is best-effort */ }
    }
    return { status: 'proved', usedAssumptions }
  }

  // ── Unknown ──────────────────────────────────────────────────────────────
  if (status === 'unknown') {
    return { status: 'unknown', reason: solver.reasonUnknown() }
  }

  // ── SAT → counterexample ─────────────────────────────────────────────────
  let counterexample = extractModel(solver, variables)

  // Evaluate trace expressions IMMEDIATELY from the first model (before blocking changes it)
  let trace: Record<string, unknown> | undefined
  if (input.traceExprs && input.traceExprs.size > 0) {
    trace = {}
    const firstModel = solver.model()
    for (const [name, expr] of input.traceExprs) {
      try {
        trace[name] = parseZ3Value(firstModel.eval(expr, true).toString())
      } catch { /* skip */ }
    }
    if (Object.keys(trace).length === 0) trace = undefined
  }

  // Optionally minimize counterexample values via Optimize
  if (minimizeCounterexample) {
    try {
      const minimized = await findMinimalCounterexample(input, Z3)
      if (minimized) counterexample = minimized
    } catch { /* fallback to original */ }
  }

  // Optionally find additional counterexamples via blocking
  let allCounterexamples: Record<string, unknown>[] | undefined
  if (maxCounterexamples > 1) {
    allCounterexamples = [counterexample]
    for (let n = 1; n < maxCounterexamples; n++) {
      try {
        const model = solver.model()
        const blockTerms = [...variables.values()].map(v => {
          try { return v.neq(model.eval(v, true)) } catch { return Z3.Bool.val(false) }
        })
        solver.add(Z3.Or(...blockTerms))
        const next = await solver.check(goal)
        if (next !== 'sat') break
        allCounterexamples.push(extractModel(solver, variables))
      } catch { break }
    }
  }

  // Convert traceLocs from Map to Record for the result
  let traceLocs: Record<string, { line: number; column: number }> | undefined
  if (input.traceLocs && input.traceLocs.size > 0) {
    traceLocs = {}
    for (const [name, loc] of input.traceLocs) {
      traceLocs[name] = loc
    }
  }

  return { status: 'disproved', counterexample, allCounterexamples, trace, traceLocs }
}

// ---------------------------------------------------------------------------
// Counterexample minimization via Optimize
// ---------------------------------------------------------------------------

async function findMinimalCounterexample(
  input: CheckInput,
  Z3: Awaited<ReturnType<typeof getContext>>,
): Promise<Record<string, unknown> | null> {
  const opt = new Z3.Optimize()

  for (const dc of input.domainConstraints ?? []) opt.add(dc)
  for (const a of input.assumptions) opt.add(a)
  opt.add(input.goal)

  // Minimize sum of |x_i| for all numeric variables
  const terms: Arith<'main'>[] = []
  for (const [, expr] of input.variables) {
    try {
      const a = expr as Arith<'main'>
      terms.push(Z3.If(a.ge(Z3.Real.val(0)), a, a.neg()) as unknown as Arith<'main'>)
    } catch { /* skip non-arithmetic */ }
  }
  if (terms.length > 0) {
    opt.minimize(terms.reduce((acc, t) => acc.add(t)))
  }

  const status = await opt.check()
  if (status !== 'sat') return null

  return extractModelFrom(opt.model(), input.variables)
}

// ---------------------------------------------------------------------------
// Model extraction
// ---------------------------------------------------------------------------

function extractModel(
  solver: { model(): { eval(e: AnyExpr<'main'>, c?: boolean): AnyExpr<'main'> } },
  variables: Map<string, AnyExpr<'main'>>,
): Record<string, unknown> {
  return extractModelFrom(solver.model(), variables)
}

function extractModelFrom(
  model: { eval(e: AnyExpr<'main'>, c?: boolean): AnyExpr<'main'> },
  variables: Map<string, AnyExpr<'main'>>,
): Record<string, unknown> {
  const ce: Record<string, unknown> = {}
  for (const [name, expr] of variables) {
    // Internal machinery — noise in a counterexample
    if (name.startsWith('__field_') || name === '__fn__' || name.startsWith('__chc_') || name.startsWith('__qs') || name.startsWith('__qi')) continue
    const displayName = name.startsWith('__old_') ? `old(${name.slice(6)})` : name
    try {
      ce[displayName] = parseZ3Value(model.eval(expr, true).toString())
    } catch {
      ce[displayName] = '?'
    }
  }
  // old(x) identical to x says nothing — drop it
  for (const key of Object.keys(ce)) {
    if (key.startsWith('old(') && key.endsWith(')')) {
      const plain = key.slice(4, -1)
      if (plain in ce && String(ce[plain]) === String(ce[key])) delete ce[key]
    }
  }

  // Reference arrays (Account[] etc): raw slot→ref maps mean nothing to a
  // reader. Compose the view that does: each element's FIELD values via the
  // __field_ maps, plus an explicit alias note when two slots hold the same
  // object. Numeric arrays keep the slot map — there the values ARE the data.
  try {
    const fieldArrays = [...variables].filter(([n]) => n.startsWith('__field_'))
    for (const [name, expr] of variables) {
      if (name.startsWith('__') || name.includes('.')) continue
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const anyExpr = expr as any
      let isRefArray = false
      try {
        // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
        const sort = anyExpr.sort
        // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
        isRefArray = String(sort.domain()) === 'Int' && String(sort.range()) === 'Int'
      } catch { /* not an array */ }
      if (!isRefArray) continue
      // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any
      const ctx = anyExpr.ctx as any
      if (ctx === undefined) continue
      const lenVar = variables.get(`${name}.length`)
      let len = 2   // the common obligation arity when length is unconstrained
      if (lenVar !== undefined) {
        const l = Number(parseZ3Value(model.eval(lenVar, true).toString()))
        if (Number.isFinite(l) && l > 0) len = l
      }
      len = Math.min(len, 6)
      const refOf: string[] = []
      let emitted = 0
      for (let i = 0; i < len; i++) {
        // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
        const ref = model.eval(ctx.Select(anyExpr, ctx.Int.val(i)) as AnyExpr<'main'>, true)
        const aliasOf = refOf.findIndex(r => r === ref.toString())
        refOf.push(ref.toString())
        if (aliasOf >= 0) {
          ce[`${name}[${i}]`] = `same object as ${name}[${aliasOf}]`
          emitted++
          continue
        }
        for (const [fname, farr] of fieldArrays) {
          try {
            // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
            const v = model.eval(ctx.Select(farr as AnyExpr<'main'>, ref) as AnyExpr<'main'>, true)
            ce[`${name}[${i}].${fname.slice('__field_'.length)}`] = parseZ3Value(v.toString())
            emitted++
          } catch { /* skip field */ }
        }
      }
      // Only hide the raw ref map when the composed view says something
      if (emitted > 0) delete ce[name]
    }
  } catch { /* enrichment is display-only — never break extraction */ }
  return ce
}

// ---------------------------------------------------------------------------
// Z3 value parser
// ---------------------------------------------------------------------------

function parseZ3Value(raw: string): unknown {
  const s = raw.trim()

  // Z3 array models: (store (store ((as const (Array ...)) D) IDX V) ...)
  // Render as a readable slot map: "[0 → 4, 1 → 4, resto → 3]"
  if (s.startsWith('(store ') || s.startsWith('((as const (Array')) {
    const pretty = prettyArrayModel(s)
    if (pretty !== null) return pretty
  }

  if (/^-?\d+$/.test(s)) return Number(s)
  if (/^-?\d+\.\d+$/.test(s)) return Number(s)
  if (s === 'true') return true
  if (s === 'false') return false

  // Prefix expressions: "(op ...)"
  const inner = s.match(/^\((.+)\)$/)
  if (inner) {
    const body = inner[1] as string
    const neg = body.match(/^-\s+(.+)$/)
    if (neg) {
      const val = parseZ3Value(neg[1] as string)
      if (typeof val === 'number') return -val
    }
    const div = body.match(/^\/\s+(.+?)\s+(.+)$/)
    if (div) {
      const num = parseZ3Value(div[1] as string)
      const den = parseZ3Value(div[2] as string)
      if (typeof num === 'number' && typeof den === 'number' && den !== 0) {
        return num / den
      }
    }
  }

  // Bare rational: "1/3"
  if (/^-?\d+\/\d+$/.test(s)) {
    const [num, den] = s.split('/').map(Number) as [number, number]
    return num / den
  }

  // String value (Z3 returns quoted strings)
  if (s.startsWith('"') && s.endsWith('"')) return s.slice(1, -1)

  return s
}

// ---------------------------------------------------------------------------
// Array-model formatting — store chains become slot maps
// ---------------------------------------------------------------------------

/**
 * Parses Z3's array model syntax into "[0 → v0, 1 → v1, else → d]".
 * Returns null when the syntax doesn't match (leave the raw string).
 */
function prettyArrayModel(s: string): string | null {
  // Peel store wrappers from the outside in
  const entries: Array<[string, string]> = []
  let cur = s.trim()
  for (;;) {
    if (cur.startsWith('(store ')) {
      const inner = cur.slice(7, -1)   // drop "(store " and final ")"
      // inner = <array-expr> <idx> <val> — array-expr is balanced-parenthesized
      const arrEnd = balancedEnd(inner)
      if (arrEnd === -1) return null
      const rest = inner.slice(arrEnd).trim()
      const parts = splitTopLevel(rest)
      if (parts.length !== 2) return null
      entries.push([parts[0]!, parts[1]!])
      cur = inner.slice(0, arrEnd).trim()
      continue
    }
    break
  }
  const base = /^\(\(as const \(Array [^)]*\)+\)\s+(.+)\)$/.exec(cur)
  if (base === null) return null
  const defaultVal = String(parseZ3Value(base[1]!))
  // Later stores override earlier ones; entries were collected outermost-first
  const slots = new Map<string, string>()
  for (let i = entries.length - 1; i >= 0; i--) {
    const [idx, val] = entries[i]!
    slots.set(String(parseZ3Value(idx)), String(parseZ3Value(val)))
  }
  const shown = [...slots.entries()]
    .sort((a, b) => Number(a[0]) - Number(b[0]))
    .map(([i, v]) => `${i} → ${v}`)
  shown.push(`else → ${defaultVal}`)
  return `[${shown.join(', ')}]`
}

/** Index just past the end of a leading balanced-paren (or bare) token. */
function balancedEnd(s: string): number {
  if (!s.startsWith('(')) {
    const sp = s.indexOf(' ')
    return sp === -1 ? s.length : sp
  }
  let depth = 0
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '(') depth++
    else if (s[i] === ')') { depth--; if (depth === 0) return i + 1 }
  }
  return -1
}

/** Splits "A B" where A and B are balanced tokens. */
function splitTopLevel(s: string): string[] {
  const out: string[] = []
  let rest = s.trim()
  while (rest.length > 0) {
    const end = balancedEnd(rest)
    if (end <= 0) return out
    out.push(rest.slice(0, end))
    rest = rest.slice(end).trim()
  }
  return out
}
