import type { AnyExpr, Arith, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, FunctionIR } from '../parser/ir.js'
import type { VerificationTask } from './index.js'
import { prettyExpr } from '../parser/pretty.js'
import { unfoldSpecCalls } from './spec-unfold.js'

/**
 * Heap-as-map encoding — mutation levels 2 and 3, plus the L4 spike:
 * pointer-valued fields and reads/writes THROUGH pointers.
 *
 *   read  a.x         →  Select(heap_x, refA)
 *   write a.x = v     →  heap_x' = Store(heap_x, refA, v)
 *   read  a.next.prev →  Select(heap_prev, Select(heap_next, refA))
 *   write a.next.prev →  heap_prev' = Store(heap_prev, Select(heap_next, refA), v)
 *
 * Object roots are Int constants ("references"); aliasing is refA === refB,
 * explored by the solver. Fields are sorted by inference: a field is a
 * POINTER field (Int→Int array) when it is dereferenced (`x.f.g`), assigned
 * null/a reference, or compared against one; otherwise numeric (Int→Real).
 * `null` is the reference 0; named roots are assumed non-null.
 *
 * Level 3: a `modifies(a, b)` contract restricts writable base roots.
 */
export function translateHeapMode(ir: FunctionIR, ctx: Z3Context): VerificationTask[] {
  const steps = ir.heapSteps ?? []
  const declaredRoots = new Set(ir.heapRoots ?? [])
  const tasks: VerificationTask[] = []

  // F4: spec predicates over the mutable heap. Contract predicates are
  // unfolded (F2 machinery); their definitional axioms are translated PER
  // HEAP VERSION — requires-side axioms read the INITIAL heap (@pre), while
  // ensures-side axioms read the FINAL heap (@post). Select-over-store then
  // connects the two versions automatically for the written window.
  let requiresAxioms: Expr[] = []
  let ensuresAxioms: Expr[] = []
  if (ir.specDefs !== undefined && ir.specDefs.size > 0) {
    const defs = ir.specDefs
    const reqAx: Expr[] = []
    const ensAx: Expr[] = []
    ir = {
      ...ir,
      contracts: ir.contracts.map(c => {
        if (!('predicate' in c) || typeof c.predicate !== 'object' || c.predicate === null) return c
        const unfolded = unfoldSpecCalls(c.predicate as Expr, defs)
        if (unfolded.axioms.length === 0) return c
        const bucket = c.kind === 'ensures' ? ensAx : reqAx
        for (const a of unfolded.axioms) bucket.push(a.predicate)
        return { ...c, predicate: unfolded.expr } as typeof c
      }),
    }
    const dedupe = (list: Expr[]): Expr[] => {
      const seen = new Set<string>()
      return list.filter(p => {
        const k = prettyExpr(p)
        if (seen.has(k)) return false
        seen.add(k)
        return true
      })
    }
    requiresAxioms = dedupe(reqAx)
    ensuresAxioms = dedupe(ensAx)
  }

  // ── References: one Int constant per object root; aliases share ──────────
  const refs = new Map<string, Arith<'main'>>()
  const aliasOf = new Map<string, string>()
  for (const step of steps) {
    if (step.kind === 'alias') aliasOf.set(step.name, resolveAlias(step.of, aliasOf))
  }
  const rootNames = new Set<string>(declaredRoots)
  for (const step of steps) if (step.kind === 'field-write') rootNames.add(resolveAlias(step.root, aliasOf))
  // Spec predicates dereference their arguments (validChain(node) reads
  // node.next inside the axioms) — those bases are references too
  const memberRootsOf = (e: Expr): void => {
    if (e.kind === 'member') {
      let base: Expr = e.object
      while (base.kind === 'member') base = base.object
      if (base.kind === 'ident') rootNames.add(resolveAlias(base.name, aliasOf))
      memberRootsOf(e.object)
    } else if (e.kind === 'binary') { memberRootsOf(e.left); memberRootsOf(e.right) }
    else if (e.kind === 'unary') memberRootsOf(e.operand)
    else if (e.kind === 'ternary') { memberRootsOf(e.condition); memberRootsOf(e.then); memberRootsOf(e.else) }
    else if (e.kind === 'call') for (const a of e.args) memberRootsOf(a)
  }
  for (const c of ir.contracts) {
    if ('predicate' in c && typeof c.predicate === 'object' && c.predicate !== null) memberRootsOf(c.predicate as Expr)
  }
  for (const ax of [...requiresAxioms, ...ensuresAxioms]) memberRootsOf(ax)
  for (const name of rootNames) refs.set(name, ctx.Int.const(name))

  const NULL_REF = ctx.Int.val(0)

  // ── Collect fields and infer their sorts (pointer vs numeric) ────────────
  const fields = new Set<string>()
  const contractPredicates: Expr[] = []
  for (const c of ir.contracts) {
    if ('predicate' in c && typeof c.predicate === 'object') contractPredicates.push(c.predicate as Expr)
  }
  const collectStepFields = (list: typeof steps): void => {
    for (const step of list) {
      if (step.kind === 'field-write') {
        fields.add(step.field)
        collectFields(step.object, fields)
        collectFields(step.value, fields)
      } else if (step.kind === 'local') {
        collectFields(step.value, fields)
      } else if (step.kind === 'branch') {
        collectFields(step.condition, fields)
        collectStepFields(step.then)
        collectStepFields(step.else)
      }
    }
  }
  collectStepFields(steps)
  for (const ax of [...requiresAxioms, ...ensuresAxioms]) contractPredicates.push(ax)
  for (const p of contractPredicates) collectFields(p, fields)

  const refFields = inferRefFields(steps, contractPredicates, rootNames, aliasOf)

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const initialHeap = new Map<string, any>()
  for (const f of fields) {
    const range = refFields.has(f) ? ctx.Int.sort() : ctx.Real.sort()
    initialHeap.set(f, ctx.Array.const(`__heap_${f}`, ctx.Int.sort(), range))
  }

  // Numeric parameters (non-root) as Real constants
  const numericVars = new Map<string, AnyExpr<'main'>>()
  for (const p of ir.params) {
    if (!rootNames.has(p.name)) numericVars.set(p.name, ctx.Real.const(p.name))
  }

  interface Env {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    heap: Map<string, any>
    locals: Map<string, AnyExpr<'main'>>
    /** Heap version tag — spec UFs are distinct per version (@pre/@post). */
    tag: 'pre' | 'post'
  }

  // Frame bridge (ground, sound): a spec predicate whose READ-SET is
  // disjoint from the WRITTEN fields cannot change value across the body —
  // its @post application IS its @pre application. Read-sets are transitive
  // over called spec definitions.
  const writtenFields = new Set<string>()
  const collectWritten = (list: typeof steps): void => {
    for (const s of list) {
      if (s.kind === 'field-write') writtenFields.add(s.field)
      else if (s.kind === 'branch') { collectWritten(s.then); collectWritten(s.else) }
    }
  }
  collectWritten(steps)

  const readSetCache = new Map<string, Set<string>>()
  const readSetOf = (defName: string, visiting = new Set<string>()): Set<string> => {
    const cached = readSetCache.get(defName)
    if (cached !== undefined) return cached
    if (visiting.has(defName)) return new Set()
    visiting.add(defName)
    const out = new Set<string>()
    const def = ir.specDefs?.get(defName)
    if (def !== undefined) {
      const walk = (e: Expr): void => {
        switch (e.kind) {
          case 'member': out.add(e.property); walk(e.object); break
          case 'binary': walk(e.left); walk(e.right); break
          case 'unary': walk(e.operand); break
          case 'ternary': walk(e.condition); walk(e.then); walk(e.else); break
          case 'call': {
            for (const sub of readSetOf(e.callee, visiting)) out.add(sub)
            for (const a of e.args) walk(a)
            break
          }
          case 'array': for (const el of e.elements) walk(el); break
          case 'spread': walk(e.operand); break
          default: break
        }
      }
      walk(def.body)
    }
    readSetCache.set(defName, out)
    return out
  }

  const specUFTag = (callee: string, tag: 'pre' | 'post'): 'pre' | 'post' => {
    if (tag === 'pre') return 'pre'
    const defName = callee.replace(/^__uf[brs]_/, '')
    const reads = readSetOf(defName)
    for (const f of reads) if (writtenFields.has(f)) return 'post'
    return 'pre'  // reads nothing that was written — value cannot change
  }

  const translate = (expr: Expr, env: Env, oldEnv: Env): AnyExpr<'main'> | null => {
    switch (expr.kind) {
      case 'literal':
        if (typeof expr.value === 'number') return ctx.Real.val(expr.value)
        if (typeof expr.value === 'boolean') return ctx.Bool.val(expr.value)
        if (expr.value === null) return NULL_REF
        return null
      case 'ident': {
        if (expr.name === 'null') return NULL_REF
        const resolved = resolveAlias(expr.name, aliasOf)
        return env.locals.get(expr.name) ?? refs.get(resolved) ?? numericVars.get(expr.name) ?? null
      }
      case 'member': {
        const objRef = translate(expr.object, env, oldEnv)
        const heap = env.heap.get(expr.property)
        if (objRef === null || heap === undefined) return null
        // eslint-disable-next-line @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
        return heap.select(objRef)
      }
      case 'unary': {
        const operand = translate(expr.operand, env, oldEnv)
        if (operand === null) return null
        if (expr.op === '!') return ctx.Not(operand as Bool<'main'>)
        if (expr.op === '-') return (operand as Arith<'main'>).neg()
        return null
      }
      case 'binary': {
        const l = translate(expr.left, env, oldEnv)
        const r = translate(expr.right, env, oldEnv)
        if (l === null || r === null) return null
        const a = l as Arith<'main'>
        const b = r as Arith<'main'>
        try {
          switch (expr.op) {
            case '+': return a.add(b)
            case '-': return a.sub(b)
            case '*': return a.mul(b)
            case '/': return a.div(b)
            case '===': return a.eq(b)
            case '!==': return ctx.Not(a.eq(b))
            case '<': return a.lt(b)
            case '<=': return a.le(b)
            case '>': return a.gt(b)
            case '>=': return a.ge(b)
            case '&&': return ctx.And(l as Bool<'main'>, r as Bool<'main'>)
            case '||': return ctx.Or(l as Bool<'main'>, r as Bool<'main'>)
            default: return null
          }
        } catch { return null /* sort mismatch (Int ref vs Real) */ }
      }
      case 'ternary': {
        const c = translate(expr.condition, env, oldEnv)
        const t = translate(expr.then, env, oldEnv)
        const e = translate(expr.else, env, oldEnv)
        if (c === null || t === null || e === null) return null
        return ctx.If(c as Bool<'main'>, t, e)
      }
      case 'call': {
        // Spec-function UF applications, versioned by heap tag: the same
        // predicate reads DIFFERENT heaps at entry vs exit, so @pre and
        // @post are distinct uninterpreted functions
        if (expr.callee.startsWith('__ufb_') || expr.callee.startsWith('__ufr_')) {
          const args = expr.args.map(a => translate(a, env, oldEnv))
          if (args.some(a => a === null)) return null
          const isBool = expr.callee.startsWith('__ufb_')
          try {
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            const anyCtx = ctx as any
            // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
            const cache: Map<string, unknown> = anyCtx.__ufCache ?? (anyCtx.__ufCache = new Map())
            // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
            const argSorts = args.map(a => (a as any).sort)
            const key = `${expr.callee}@${specUFTag(expr.callee, env.tag)}(${argSorts.map((s: unknown) => String(s)).join(',')})`
            let decl = cache.get(key)
            if (decl === undefined) {
              // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
              decl = ctx.Function.declare(key.replace(/[^\w]/g, '_'), ...argSorts, isBool ? ctx.Bool.sort() : ctx.Real.sort())
              cache.set(key, decl)
            }
            // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-return
            return (decl as any).call(...args)
          } catch { return null }
        }

        // old(x.f): value in the INITIAL heap
        if (expr.callee === 'old' && expr.args.length === 1) {
          return translate(expr.args[0]!, oldEnv, oldEnv)
        }
        const arg0 = expr.args[0] !== undefined ? translate(expr.args[0]!, env, oldEnv) : null
        if (expr.callee === 'positive' && arg0 !== null) return (arg0 as Arith<'main'>).gt(ctx.Real.val(0))
        if (expr.callee === 'nonNegative' && arg0 !== null) return (arg0 as Arith<'main'>).ge(ctx.Real.val(0))
        if (expr.callee === 'negative' && arg0 !== null) return (arg0 as Arith<'main'>).lt(ctx.Real.val(0))
        if (expr.callee === 'between' && expr.args.length === 3 && arg0 !== null) {
          const lo = translate(expr.args[1]!, env, oldEnv)
          const hi = translate(expr.args[2]!, env, oldEnv)
          if (lo === null || hi === null) return null
          const x = arg0 as Arith<'main'>
          return ctx.And(x.ge(lo as Arith<'main'>), x.le(hi as Arith<'main'>))
        }
        return null
      }
      default:
        return null
    }
  }

  const oldEnv: Env = { heap: initialHeap, locals: new Map(), tag: 'pre' }

  // ── Requires: hold in the initial state; named roots are non-null ────────
  const assumptions: Bool<'main'>[] = []
  const assumptionLabels: string[] = []
  for (const [name, ref] of refs) {
    assumptions.push(ref.gt(NULL_REF))
    assumptionLabels.push(`${name} is a live reference`)
  }
  for (const c of ir.contracts) {
    if (c.kind !== 'requires' || typeof c.predicate === 'string') continue
    const z3 = translate(c.predicate, oldEnv, oldEnv)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`requires: ${prettyExpr(c.predicate)}`)
    }
  }
  for (const ax of requiresAxioms) {
    const z3 = translate(ax, oldEnv, oldEnv)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`def@pre: ${prettyExpr(ax).slice(0, 60)}`)
    }
  }

  // ── Execute steps over the heap ──────────────────────────────────────────
  //
  // Branches use the guarded-command encoding: every write becomes a
  // conditional store `heap' = ITE(pathCond ∧ alive, Store(...), heap)`.
  // Sequential processing composes correctly — a then-branch mutation read
  // from the else-branch resolves to the original value because its ITE
  // guard is false there. Early returns clear `alive` for their paths.
  const env: Env = { heap: new Map(initialHeap), locals: new Map(), tag: 'post' }
  const modifiesContract = ir.contracts.find(c => c.kind === 'modifies')
  const allowedWrites = modifiesContract !== undefined
    ? new Set((modifiesContract as { refs: string[] }).refs.map(r => resolveAlias(r, aliasOf)))
    : null

  let alive: Bool<'main'> = ctx.Bool.val(true)

  const processSteps = (list: import('../parser/ir.js').HeapStep[], pc: Bool<'main'> | null): void => {
    for (const step of list) {
      if (step.kind === 'alias') continue

      if (step.kind === 'local') {
        const v = translate(step.value, env, oldEnv)
        if (v !== null) env.locals.set(step.name, v)
        continue
      }

      if (step.kind === 'exit') {
        alive = pc === null ? ctx.Bool.val(false) : ctx.And(alive, ctx.Not(pc))
        continue
      }

      if (step.kind === 'branch') {
        // Condition evaluated against the state at branch ENTRY
        const condZ3 = translate(step.condition, env, oldEnv)
        // Untranslatable condition → fresh unconstrained Bool: the solver
        // explores both branches, which over-approximates soundly for proofs
        const cond = condZ3 !== null
          ? condZ3 as Bool<'main'>
          : ctx.Bool.const(`__cond_${branchCounter++}`)
        const pcThen = pc === null ? cond : ctx.And(pc, cond)
        const pcElse = pc === null ? ctx.Not(cond) : ctx.And(pc, ctx.Not(cond))
        processSteps(step.then, pcThen)
        processSteps(step.else, pcElse)
        continue
      }

      // field-write (possibly through a pointer path)
      const target = translate(step.object, env, oldEnv)
      const heap = env.heap.get(step.field)
      const value = translate(step.value, env, oldEnv)
      if (target === null || heap === undefined || value === null) continue

      // Level 3: framing — undeclared BASE roots are contract violations
      const root = resolveAlias(step.root, aliasOf)
      if (allowedWrites !== null && !allowedWrites.has(root)) {
        tasks.push({
          functionName: ir.name,
          contractText: `modifies violation: writes through ${step.root} (${prettyExpr(step.object)}.${step.field}), not declared in modifies(${[...allowedWrites].join(', ')})`,
          variables: new Map(refs as unknown as Map<string, AnyExpr<'main'>>),
          assumptions: [],
          assumptionLabels: [],
          goal: ctx.Bool.val(true),
          domainConstraints: [],
        })
      }

      // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
      const stored = heap.store(target, value)
      const guard = pc === null ? alive : ctx.And(alive, pc)
      // eslint-disable-next-line @typescript-eslint/no-unsafe-argument
      env.heap.set(step.field, ctx.If(guard, stored, heap))
    }
  }

  let branchCounter = 0
  processSteps(steps, null)

  // Ensures-side definitional axioms read the FINAL heap (@post) — the
  // select-over-store chains connect them to the @pre facts automatically
  for (const ax of ensuresAxioms) {
    const z3 = translate(ax, env, oldEnv)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`def@post: ${prettyExpr(ax).slice(0, 60)}`)
    }
  }

  // ── Ensures: hold in the final state ─────────────────────────────────────
  const variables = new Map<string, AnyExpr<'main'>>()
  for (const [name, ref] of refs) variables.set(name, ref as unknown as AnyExpr<'main'>)
  for (const [name, v] of numericVars) variables.set(name, v)

  for (const c of ir.contracts) {
    if (c.kind !== 'ensures' || typeof c.predicate === 'string') continue
    const z3 = translate(c.predicate, env, oldEnv)
    if (z3 === null) continue
    tasks.push({
      functionName: ir.name,
      contractText: prettyExpr(c.predicate),
      variables,
      assumptions: [...assumptions],
      assumptionLabels: [...assumptionLabels],
      goal: ctx.Not(z3 as Bool<'main'>),
      domainConstraints: [],
    })
  }

  return tasks
}

function resolveAlias(name: string, aliasOf: Map<string, string>): string {
  let current = name
  const seen = new Set<string>()
  while (aliasOf.has(current) && !seen.has(current)) {
    seen.add(current)
    current = aliasOf.get(current)!
  }
  return current
}

/**
 * Field-sort inference to a fixpoint: a field is a POINTER field when it is
 * dereferenced (appears as the object of another member access), assigned
 * null or a reference expression, or equality-compared against one.
 */
function inferRefFields(
  steps: FunctionIR['heapSteps'] & object,
  predicates: Expr[],
  roots: Set<string>,
  aliasOf: Map<string, string>,
): Set<string> {
  const refFields = new Set<string>()

  const isRefExpr = (e: Expr): boolean => {
    if (e.kind === 'literal' && e.value === null) return true
    if (e.kind === 'ident') {
      return e.name === 'null' || roots.has(resolveAlias(e.name, aliasOf))
    }
    if (e.kind === 'member') return refFields.has(e.property)
    return false
  }

  const walk = (e: Expr): void => {
    switch (e.kind) {
      case 'member':
        // x.f.g — f is dereferenced, so f is a pointer field
        if (e.object.kind === 'member') refFields.add(e.object.property)
        walk(e.object)
        break
      case 'binary':
        if ((e.op === '===' || e.op === '!==')) {
          if (e.left.kind === 'member' && isRefExpr(e.right)) refFields.add(e.left.property)
          if (e.right.kind === 'member' && isRefExpr(e.left)) refFields.add(e.right.property)
        }
        walk(e.left); walk(e.right)
        break
      case 'unary': walk(e.operand); break
      case 'ternary': walk(e.condition); walk(e.then); walk(e.else); break
      case 'call': for (const a of e.args) walk(a); break
      default: break
    }
  }

  const walkSteps = (list: typeof steps): void => {
    for (const step of list) {
      if (step.kind === 'field-write') {
        if (isRefExpr(step.value)) refFields.add(step.field)
        if (step.object.kind === 'member') refFields.add(step.object.property)
        walk(step.object); walk(step.value)
      } else if (step.kind === 'local') {
        walk(step.value)
      } else if (step.kind === 'branch') {
        walk(step.condition)
        walkSteps(step.then)
        walkSteps(step.else)
      }
    }
  }

  // Two passes reach the fixpoint for practical chains
  for (let pass = 0; pass < 2; pass++) {
    walkSteps(steps)
    for (const p of predicates) walk(p)
  }

  return refFields
}

function collectFields(expr: Expr, fields: Set<string>): void {
  switch (expr.kind) {
    case 'member':
      fields.add(expr.property)
      collectFields(expr.object, fields)
      break
    case 'binary':
      collectFields(expr.left, fields); collectFields(expr.right, fields); break
    case 'unary':
      collectFields(expr.operand, fields); break
    case 'ternary':
      collectFields(expr.condition, fields); collectFields(expr.then, fields); collectFields(expr.else, fields); break
    case 'call':
      for (const a of expr.args) collectFields(a, fields); break
    default:
      break
  }
}