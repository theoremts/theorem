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
  let specAxioms: Expr[] = []
  if (ir.specDefs !== undefined && ir.specDefs.size > 0) {
    const defs = ir.specDefs
    const pool: Expr[] = []
    const unfoldPred = (e: Expr): Expr => {
      const unfolded = unfoldSpecCalls(e, defs)
      for (const a of unfolded.axioms) pool.push(a.predicate)
      return unfolded.expr
    }
    // Contracts
    let contracts = ir.contracts.map(c => {
      if (!('predicate' in c) || typeof c.predicate !== 'object' || c.predicate === null) return c
      return { ...c, predicate: unfoldPred(c.predicate as Expr) } as typeof c
    })
    // Loop invariants inside heap steps (F7): unfold in place
    const unfoldSteps = (list: typeof steps): typeof steps => list.map(s => {
      if (s.kind === 'loop') {
        return {
          ...s,
          invariants: s.invariants.map(unfoldPred),
          body: unfoldSteps(s.body),
        }
      }
      if (s.kind === 'branch') {
        return { ...s, then: unfoldSteps(s.then), else: unfoldSteps(s.else) }
      }
      return s
    })
    const newSteps = unfoldSteps(steps)
    steps.length = 0
    steps.push(...newSteps)
    ir = { ...ir, contracts }

    const seen = new Set<string>()
    specAxioms = pool.filter(pr => {
      const k = prettyExpr(pr)
      if (seen.has(k)) return false
      seen.add(k)
      return true
    })
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
    else if (e.kind === 'quantifier') memberRootsOf(e.body)
    else if (e.kind === 'element-access') { memberRootsOf(e.object); memberRootsOf(e.index) }
  }
  for (const c of ir.contracts) {
    if ('predicate' in c && typeof c.predicate === 'object' && c.predicate !== null) memberRootsOf(c.predicate as Expr)
  }
  for (const ax of specAxioms) memberRootsOf(ax)
  for (const name of rootNames) {
    if (ir.params.some(p => p.name === name && (p.sort === 'array' || p.sort === 'ref-array'))) continue
    refs.set(name, ctx.Int.const(name))
  }

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
      } else if (step.kind === 'loop') {
        collectFields(step.condition, fields)
        for (const inv of step.invariants) collectFields(inv, fields)
        if (step.decreases !== undefined) collectFields(step.decreases, fields)
        collectStepFields(step.body)
      } else if (step.kind === 'num-assign') {
        collectFields(step.value, fields)
      }
    }
  }
  collectStepFields(steps)
  for (const ax of specAxioms) contractPredicates.push(ax)
  for (const p of contractPredicates) collectFields(p, fields)

  const refFields = inferRefFields(steps, contractPredicates, rootNames, aliasOf)

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const initialHeap = new Map<string, any>()
  for (const f of fields) {
    const range = refFields.has(f) ? ctx.Int.sort() : ctx.Real.sort()
    initialHeap.set(f, ctx.Array.const(`__heap_${f}`, ctx.Int.sort(), range))
  }

  // Array parameters: Z3 Array(Int → range) + a paired Int length constant.
  // number[] ranges over Real; Account[] ranges over Int — an array of
  // REFERENCES, composing with the field heaps: users[i].balance is
  // Select(heap_balance, Select(users, i)). Two slots holding the same
  // reference (in-array aliasing) is a case the solver explores.
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const arrayVars = new Map<string, { arr: any; len: Arith<'main'>; ref: boolean }>()
  for (const p of ir.params) {
    if (p.sort === 'array' || p.sort === 'ref-array') {
      const isRef = p.sort === 'ref-array'
      arrayVars.set(p.name, {
        arr: ctx.Array.const(p.name, ctx.Int.sort(), isRef ? ctx.Int.sort() : ctx.Real.sort()),
        len: ctx.Int.const(`${p.name}.length`),
        ref: isRef,
      })
    }
  }

  // Numeric parameters (non-root) as Real constants
  const numericVars = new Map<string, AnyExpr<'main'>>()
  for (const p of ir.params) {
    if (!rootNames.has(p.name) && !arrayVars.has(p.name)) numericVars.set(p.name, ctx.Real.const(p.name))
  }

  // Mutable numeric state (`this.x` fields, let-locals): the entry-state
  // constant doubles as the old() value — num-assigns update env.nums, so
  // reads fall back here only before the first write.
  const numTargets = new Set<string>()
  const collectNumTargets = (list: typeof steps): void => {
    for (const s of list) {
      if (s.kind === 'num-assign') numTargets.add(s.name)
      else if (s.kind === 'branch') { collectNumTargets(s.then); collectNumTargets(s.else) }
      else if (s.kind === 'loop') collectNumTargets(s.body)
    }
  }
  collectNumTargets(steps)
  // `this.*` idents read by contracts but never assigned (e.g. a field the
  // invariant relates others to) also need entry constants.
  const collectThisIdents = (e: Expr): void => {
    switch (e.kind) {
      case 'ident': if (e.name.startsWith('this.')) numTargets.add(e.name); break
      case 'binary': collectThisIdents(e.left); collectThisIdents(e.right); break
      case 'unary': collectThisIdents(e.operand); break
      case 'ternary': collectThisIdents(e.condition); collectThisIdents(e.then); collectThisIdents(e.else); break
      case 'call': for (const a of e.args) collectThisIdents(a); break
      case 'member': collectThisIdents(e.object); break
      default: break
    }
  }
  for (const p of contractPredicates) collectThisIdents(p)

  // Int classification: a mutable numeric is Int-sorted iff EVERY expression
  // assigned to it is integer-shaped (int literals, other Int vars, +/-/* of
  // those, Math.floor, array .length). Int-sorted state is what lets array
  // indices instantiate quantified facts — and keeps `lo := mid + 1` inside
  // pure integer arithmetic, away from the solver's fragile to_int mixing.
  const assignedNums = new Set<string>()
  const localNames = new Set<string>()
  const collectAssigned = (list: typeof steps): void => {
    for (const s of list) {
      if (s.kind === 'num-assign') assignedNums.add(s.name)
      else if (s.kind === 'local') localNames.add(s.name)
      else if (s.kind === 'branch') { collectAssigned(s.then); collectAssigned(s.else) }
      else if (s.kind === 'loop') collectAssigned(s.body)
    }
  }
  collectAssigned(steps)
  // Locals participate too: `const mid = Math.floor(...)` must classify Int
  // for `lo = mid + 1` to stay integer-sorted.
  const intVars = new Set<string>([...assignedNums, ...localNames])
  intVars.delete('__result')
  const isIntShaped = (e: Expr): boolean => {
    switch (e.kind) {
      case 'literal': return typeof e.value === 'number' && Number.isInteger(e.value)
      case 'ident': return intVars.has(e.name)
      case 'binary':
        // Bitwise results are int32 by construction
        if (e.op === '|' || e.op === '&' || e.op === '^' || e.op === '<<' || e.op === '>>' || e.op === '>>>') {
          return isIntShaped(e.left) && isIntShaped(e.right)
        }
        return (e.op === '+' || e.op === '-' || e.op === '*') && isIntShaped(e.left) && isIntShaped(e.right)
      case 'ternary': return isIntShaped(e.then) && isIntShaped(e.else)
      case 'member': return e.property === 'length' && e.object.kind === 'ident' && arrayVars.has(e.object.name)
      case 'call': return e.callee === 'Math.floor' && e.args.length === 1
      default: return false
    }
  }
  const eachAssignment = (list: typeof steps, visit: (name: string, value: Expr) => void): void => {
    for (const s of list) {
      if (s.kind === 'num-assign') visit(s.name, s.value)
      else if (s.kind === 'local') visit(s.name, s.value)
      else if (s.kind === 'alias') visit(s.name, { kind: 'ident', name: s.of })
      else if (s.kind === 'branch') { eachAssignment(s.then, visit); eachAssignment(s.else, visit) }
      else if (s.kind === 'loop') eachAssignment(s.body, visit)
    }
  }
  for (let changed = true; changed;) {
    changed = false
    eachAssignment(steps, (name, value) => {
      if (intVars.has(name) && !isIntShaped(value)) { intVars.delete(name); changed = true }
    })
  }

  for (const n of numTargets) {
    if (n !== '__result' && !rootNames.has(n) && !numericVars.has(n)) {
      numericVars.set(n, intVars.has(n) ? (ctx.Int.const(n) as unknown as AnyExpr<'main'>) : ctx.Real.const(n))
    }
  }

  interface Env {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    heap: Map<string, any>
    locals: Map<string, AnyExpr<'main'>>
    /** Mutable numeric variables (loop counters) — override numericVars. */
    nums: Map<string, AnyExpr<'main'>>
    /** Array state — versioned by array-sort havoc (length is preserved). */
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    arrays: Map<string, any>
    /** Heap version tag — spec UFs are distinct per version (@pre/@post). */
    tag: 'pre' | 'post'
  }

  const initialArrays = new Map<string, unknown>([...arrayVars].map(([n, v]) => [n, v.arr as unknown]))

  // Frame bridge (ground, sound): a spec predicate whose READ-SET is
  // disjoint from the WRITTEN fields cannot change value across the body —
  // its @post application IS its @pre application. Read-sets are transitive
  // over called spec definitions.
  const writtenFields = new Set<string>()
  const collectWritten = (list: typeof steps): void => {
    for (const s of list) {
      if (s.kind === 'field-write') writtenFields.add(s.field)
      else if (s.kind === 'branch') { collectWritten(s.then); collectWritten(s.else) }
      else if (s.kind === 'loop') collectWritten(s.body)
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

  // Heap-state signatures: UF applications are keyed by the IDENTITY of the
  // heap arrays the predicate's read-set touches. Two states whose relevant
  // arrays are the same JS objects share the UF — the F4 read-set frame
  // bridge falls out automatically, at every state (entry, loop iterations,
  // post-loop), not just pre/post.
  const heapObjIds = new Map<object, number>()
  let nextHeapId = 1
  const heapId = (o: object): number => {
    let id = heapObjIds.get(o)
    if (id === undefined) { id = nextHeapId++; heapObjIds.set(o, id) }
    return id
  }
  const specSignature = (callee: string, env: { heap: Map<string, unknown> }): string => {
    const defName = callee.replace(/^__uf[brs]_/, '')
    const reads = [...readSetOf(defName)].sort()
    return reads.map(f => {
      const arr = env.heap.get(f)
      return arr === undefined ? '?' : String(heapId(arr as object))
    }).join('.')
  }

  const isIntSorted = (t: AnyExpr<'main'>): boolean => {
    // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any
    try { return String((t as any).sort) === 'Int' } catch { return false }
  }
  /** Int/Real coercion for mixed arithmetic (TS numbers are one type; Z3's aren't). */
  const coerce2 = (l: AnyExpr<'main'>, r: AnyExpr<'main'>): [AnyExpr<'main'>, AnyExpr<'main'>] => {
    const li = isIntSorted(l), ri = isIntSorted(r)
    if (li && !ri) return [ctx.ToReal(l as Arith<'main'>) as unknown as AnyExpr<'main'>, r]
    if (!li && ri) return [l, ctx.ToReal(r as Arith<'main'>) as unknown as AnyExpr<'main'>]
    return [l, r]
  }

  const translate = (expr: Expr, env: Env, oldEnv: Env): AnyExpr<'main'> | null => {
    switch (expr.kind) {
      case 'literal':
        // Integral literals are Int-sorted so integer state (`lo = 0`,
        // `mid + 1`) stays in pure Int arithmetic; coerce2 lifts to Real
        // whenever the other operand demands it.
        if (typeof expr.value === 'number') {
          return Number.isInteger(expr.value)
            ? (ctx.Int.val(expr.value) as unknown as AnyExpr<'main'>)
            : ctx.Real.val(expr.value)
        }
        if (typeof expr.value === 'boolean') return ctx.Bool.val(expr.value)
        if (expr.value === null) return NULL_REF
        return null
      case 'ident': {
        if (expr.name === 'null') return NULL_REF
        const resolved = resolveAlias(expr.name, aliasOf)
        return env.locals.get(expr.name) ?? env.nums.get(expr.name) ?? refs.get(resolved)
          ?? numericVars.get(expr.name)
          ?? (env.arrays.get(expr.name) as AnyExpr<'main'> | undefined)
          ?? (arrayVars.get(expr.name)?.arr as AnyExpr<'main'> | undefined) ?? null
      }
      case 'member': {
        // arr.length → the paired Int length constant, not a heap field
        if (expr.object.kind === 'ident' && expr.property === 'length') {
          const av = arrayVars.get(expr.object.name)
          if (av !== undefined) return av.len as unknown as AnyExpr<'main'>
        }
        const objRef = translate(expr.object, env, oldEnv)
        const heap = env.heap.get(expr.property)
        if (objRef === null || heap === undefined) return null
        // eslint-disable-next-line @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
        return heap.select(objRef)
      }
      case 'element-access': {
        if (expr.object.kind !== 'ident') return null
        const av = arrayVars.get(expr.object.name)
        if (av === undefined) return null
        const arrState = env.arrays.get(expr.object.name) ?? av.arr
        const idx = translate(expr.index, env, oldEnv)
        if (idx === null || !isIntSorted(idx)) return null
        // eslint-disable-next-line @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
        try { return arrState.select(idx) } catch { return null }
      }
      case 'quantifier': {
        try {
          const boundVar = expr.sort === 'int' ? ctx.Int.const(expr.param) : ctx.Real.const(expr.param)
          const innerEnv: Env = { ...env, locals: new Map(env.locals) }
          innerEnv.locals.set(expr.param, boundVar as unknown as AnyExpr<'main'>)
          const body = translate(expr.body, innerEnv, oldEnv)
          if (body === null) return null
          return expr.quantifier === 'forall'
            ? ctx.ForAll([boundVar], body as Bool<'main'>) as unknown as AnyExpr<'main'>
            : ctx.Exists([boundVar], body as Bool<'main'>) as unknown as AnyExpr<'main'>
        } catch { return null }
      }
      case 'unary': {
        const operand = translate(expr.operand, env, oldEnv)
        if (operand === null) return null
        if (expr.op === '!') return ctx.Not(operand as Bool<'main'>)
        if (expr.op === '-') return (operand as Arith<'main'>).neg()
        return null
      }
      case 'binary': {
        const lRaw = translate(expr.left, env, oldEnv)
        const rRaw = translate(expr.right, env, oldEnv)
        if (lRaw === null || rRaw === null) return null
        // TS `/` is real division even on integers
        const [l, r] = expr.op === '/'
          ? [
              isIntSorted(lRaw) ? ctx.ToReal(lRaw as Arith<'main'>) as unknown as AnyExpr<'main'> : lRaw,
              isIntSorted(rRaw) ? ctx.ToReal(rRaw as Arith<'main'>) as unknown as AnyExpr<'main'> : rRaw,
            ]
          : coerce2(lRaw, rRaw)
        const a = l as Arith<'main'>
        const b = r as Arith<'main'>
        // Bitwise: JS coerces via ToInt32 — modeled as Int→BV32→op→Int.
        // Only INT-sorted operands are supported (mixing to_int over Reals
        // is where this solver build diverges). Shift counts mask & 31,
        // matching JS; >>> reads the result back unsigned.
        if (expr.op === '|' || expr.op === '&' || expr.op === '^' || expr.op === '<<' || expr.op === '>>' || expr.op === '>>>') {
          if (!isIntSorted(l) || !isIntSorted(r)) return null
          try {
            const bvA = ctx.Int2BV(a, 32)
            const bvB = ctx.Int2BV(b, 32)
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            const count = (bvB as any).and(31)
            /* eslint-disable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment */
            let bvR
            switch (expr.op) {
              case '|': bvR = (bvA as any).or(bvB); break
              case '&': bvR = (bvA as any).and(bvB); break
              case '^': bvR = (bvA as any).xor(bvB); break
              case '<<': bvR = (bvA as any).shl(count); break
              case '>>': bvR = (bvA as any).ashr(count); break
              default: bvR = (bvA as any).lshr(count); break
            }
            return ctx.BV2Int(bvR, expr.op !== '>>>') as unknown as AnyExpr<'main'>
            /* eslint-enable @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment */
          } catch { return null }
        }
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
            case '==>': return ctx.Implies(l as Bool<'main'>, r as Bool<'main'>)
            default: return null
          }
        } catch { return null /* sort mismatch (Int ref vs Real) */ }
      }
      case 'ternary': {
        const c = translate(expr.condition, env, oldEnv)
        const tRaw = translate(expr.then, env, oldEnv)
        const eRaw = translate(expr.else, env, oldEnv)
        if (c === null || tRaw === null || eRaw === null) return null
        const [t, e] = coerce2(tRaw, eRaw)
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
            const key = `${expr.callee}#${specSignature(expr.callee, env)}(${argSorts.map((s: unknown) => String(s)).join(',')})`
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
        // output(): the returned value — bound by the trailing return step
        if (expr.callee === 'output' && expr.args.length === 0) {
          return env.locals.get('__result') ?? env.nums.get('__result') ?? null
        }
        // Math.floor over Int state: floor(a / b) with Int operands is Z3's
        // integer division; floor of an Int term is the term itself. The
        // general Real case is deliberately unsupported — to_int mixing is
        // where this solver build diverges.
        if (expr.callee === 'Math.floor' && expr.args.length === 1) {
          const argE = expr.args[0]!
          if (argE.kind === 'binary' && argE.op === '/') {
            const n = translate(argE.left, env, oldEnv)
            const d = translate(argE.right, env, oldEnv)
            if (n !== null && d !== null && isIntSorted(n) && isIntSorted(d)) {
              try { return (n as Arith<'main'>).div(d as Arith<'main'>) } catch { return null }
            }
          }
          const x = translate(argE, env, oldEnv)
          return x !== null && isIntSorted(x) ? x : null
        }
        const arg0 = expr.args[0] !== undefined ? translate(expr.args[0]!, env, oldEnv) : null
        if (expr.callee === 'Number.isInteger' && arg0 !== null) {
          if (isIntSorted(arg0)) return ctx.Bool.val(true)  // Int-sorted IS integral
          const x = arg0 as Arith<'main'>
          try { return x.eq(ctx.ToInt(x) as Arith<'main'>) } catch { return null }
        }
        if (expr.callee === 'positive' && arg0 !== null) return (arg0 as Arith<'main'>).gt(isIntSorted(arg0) ? (ctx.Int.val(0) as unknown as Arith<'main'>) : ctx.Real.val(0))
        if (expr.callee === 'nonNegative' && arg0 !== null) return (arg0 as Arith<'main'>).ge(isIntSorted(arg0) ? (ctx.Int.val(0) as unknown as Arith<'main'>) : ctx.Real.val(0))
        if (expr.callee === 'negative' && arg0 !== null) return (arg0 as Arith<'main'>).lt(isIntSorted(arg0) ? (ctx.Int.val(0) as unknown as Arith<'main'>) : ctx.Real.val(0))
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

  const oldEnv: Env = { heap: initialHeap, locals: new Map(), nums: new Map(), arrays: new Map(initialArrays), tag: 'pre' }

  /** Instantiates the definitional-axiom pool at the given heap state. */
  const pushSpecAxioms = (
    atEnv: Env,
    into: Bool<'main'>[],
    intoLabels: string[],
    stateLabel: string,
  ): void => {
    for (const ax of specAxioms) {
      const z3 = translate(ax, atEnv, oldEnv)
      if (z3 !== null) {
        into.push(z3 as Bool<'main'>)
        intoLabels.push(`def@${stateLabel}: ${prettyExpr(ax).slice(0, 50)}`)
      }
    }
  }

  /** Collects root-argument spec applications (bridgeable) from an expr. */
  const collectRootApps = (e: Expr, out: Array<{ callee: string; args: Expr[] }>): void => {
    if (e.kind === 'call' && (e.callee.startsWith('__ufb_') || e.callee.startsWith('__ufr_'))) {
      if (e.args.every(a => a.kind === 'ident')) out.push({ callee: e.callee, args: e.args })
    }
    if (e.kind === 'call') for (const a of e.args) collectRootApps(a, out)
    else if (e.kind === 'binary') { collectRootApps(e.left, out); collectRootApps(e.right, out) }
    else if (e.kind === 'unary') collectRootApps(e.operand, out)
    else if (e.kind === 'ternary') { collectRootApps(e.condition, out); collectRootApps(e.then, out); collectRootApps(e.else, out) }
  }

  /**
   * F5 ownership bridges between two heap states: for X paired with inX via
   * footprint(), if every written root is outside X's structure, X cannot
   * have changed between the states.
   */
  const emitOwnershipBridges = (
    apps: Array<{ callee: string; args: Expr[] }>,
    written: Set<string>,
    fromEnv: Env,
    toEnv: Env,
    into: Bool<'main'>[],
    intoLabels: string[],
  ): void => {
    if (ir.footprints === undefined || written.size === 0) return
    for (const app of apps) {
      const specName = app.callee.replace(/^__uf[br]_/, '')
      const memberName = ir.footprints.get(specName)
      if (memberName === undefined) continue
      if (specSignature(app.callee, toEnv) === specSignature(app.callee, fromEnv)) continue

      const memberDef = ir.specDefs?.get(memberName)
      const memberPrefix = memberDef !== undefined && !memberDef.isBool ? '__ufr_' : '__ufb_'

      const conditions: Bool<'main'>[] = []
      let ok = true
      for (const w of written) {
        const memberApp: Expr = {
          kind: 'call',
          callee: `${memberPrefix}${memberName}`,
          args: [...app.args, { kind: 'ident', name: w }],
        }
        const cond = translate(memberApp, fromEnv, oldEnv)
        if (cond === null) { ok = false; break }
        conditions.push(ctx.Not(cond as Bool<'main'>))
      }
      if (!ok || conditions.length === 0) continue

      const toApp = translate({ kind: 'call', callee: app.callee, args: app.args }, toEnv, oldEnv)
      const fromApp = translate({ kind: 'call', callee: app.callee, args: app.args }, fromEnv, oldEnv)
      if (toApp === null || fromApp === null) continue
      try {
        const antecedent = conditions.length === 1 ? conditions[0]! : ctx.And(...conditions)
        // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
        const consequent = (toApp as any).eq(fromApp) as Bool<'main'>
        into.push(ctx.Implies(antecedent, consequent))
        intoLabels.push(`frame bridge: ${specName} unchanged (writes outside ${memberName})`)
      } catch { /* sort mismatch */ }
    }
  }


  // ── Requires: hold in the initial state; named roots are non-null ────────
  const assumptions: Bool<'main'>[] = []
  const assumptionLabels: string[] = []
  for (const [name, ref] of refs) {
    assumptions.push(ref.gt(NULL_REF))
    assumptionLabels.push(`${name} is a live reference`)
  }
  for (const [name, av] of arrayVars) {
    assumptions.push(av.len.ge(0) as Bool<'main'>)
    assumptionLabels.push(`${name}.length >= 0`)
  }
  for (const c of ir.contracts) {
    if (c.kind !== 'requires' || typeof c.predicate === 'string') continue
    const z3 = translate(c.predicate, oldEnv, oldEnv)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`requires: ${prettyExpr(c.predicate)}`)
    }
  }
  pushSpecAxioms(oldEnv, assumptions, assumptionLabels, 'pre')

  // ── Execute steps over the heap ──────────────────────────────────────────
  //
  // Branches use the guarded-command encoding: every write becomes a
  // conditional store `heap' = ITE(pathCond ∧ alive, Store(...), heap)`.
  // Sequential processing composes correctly — a then-branch mutation read
  // from the else-branch resolves to the original value because its ITE
  // guard is false there. Early returns clear `alive` for their paths.
  const env: Env = { heap: new Map(initialHeap), locals: new Map(), nums: new Map(), arrays: new Map(initialArrays), tag: 'post' }
  const modifiesContract = ir.contracts.find(c => c.kind === 'modifies')
  const allowedWrites = modifiesContract !== undefined
    ? new Set((modifiesContract as { refs: string[] }).refs.map(r => resolveAlias(r, aliasOf)))
    : null

  let alive: Bool<'main'> = ctx.Bool.val(true)
  let loopCounter = 0
  let sortCounter = 0

  const taskVariables = (): Map<string, AnyExpr<'main'>> => {
    const m = new Map<string, AnyExpr<'main'>>()
    for (const [name, ref] of refs) m.set(name, ref as unknown as AnyExpr<'main'>)
    for (const [name, v] of numericVars) m.set(name, v)
    for (const [name, av] of arrayVars) {
      m.set(name, av.arr as AnyExpr<'main'>)
      m.set(`${name}.length`, av.len as unknown as AnyExpr<'main'>)
    }
    return m
  }

  /** Executes one loop-body iteration against the given (havoced) env. */
  const runLoopBody = (list: typeof steps, bodyEnv: Env, pc: Bool<'main'> | null): void => {
    for (const s of list) {
      if (s.kind === 'local') {
        const v = translate(s.value, bodyEnv, oldEnv)
        if (v !== null) bodyEnv.locals.set(s.name, v)
        continue
      }
      if (s.kind === 'num-assign') {
        const v = translate(s.value, bodyEnv, oldEnv)
        if (v !== null) {
          const prev = bodyEnv.nums.get(s.name) ?? numericVars.get(s.name)
          if (pc === null || prev === undefined) {
            bodyEnv.nums.set(s.name, v)
          } else {
            const [cv, cp] = coerce2(v, prev)
            bodyEnv.nums.set(s.name, ctx.If(pc, cv, cp))
          }
        }
        continue
      }
      if (s.kind === 'branch') {
        const condZ3 = translate(s.condition, bodyEnv, oldEnv)
        const cond = condZ3 !== null ? condZ3 as Bool<'main'> : ctx.Bool.const(`__lcond_${loopCounter}_${list.indexOf(s)}`)
        runLoopBody(s.then, bodyEnv, pc === null ? cond : ctx.And(pc, cond))
        runLoopBody(s.else, bodyEnv, pc === null ? ctx.Not(cond) : ctx.And(pc, ctx.Not(cond)))
        continue
      }
      if (s.kind === 'field-write') {
        const target = translate(s.object, bodyEnv, oldEnv)
        const heap = bodyEnv.heap.get(s.field)
        const value = translate(s.value, bodyEnv, oldEnv)
        if (target === null || heap === undefined || value === null) continue
        // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
        const stored = heap.store(target, value)
        // eslint-disable-next-line @typescript-eslint/no-unsafe-argument
        bodyEnv.heap.set(s.field, pc === null ? stored : ctx.If(pc, stored, heap))
        continue
      }
    }
  }

  const processSteps = (list: import('../parser/ir.js').HeapStep[], pc: Bool<'main'> | null): void => {
    for (const step of list) {
      if (step.kind === 'alias') {
        // Numeric aliases (`let remaining = txCount`) seed mutable state;
        // object-root aliases are resolved statically through aliasOf.
        const src = resolveAlias(step.of, aliasOf)
        if (!rootNames.has(src)) {
          const v = env.nums.get(step.of) ?? numericVars.get(step.of) ?? numericVars.get(src)
          if (v !== undefined) env.nums.set(step.name, v)
        }
        continue
      }

      if (step.kind === 'local') {
        const v = translate(step.value, env, oldEnv)
        if (v !== null) env.locals.set(step.name, v)
        continue
      }

      if (step.kind === 'exit') {
        alive = pc === null ? ctx.Bool.val(false) : ctx.And(alive, ctx.Not(pc))
        continue
      }

      if (step.kind === 'num-assign') {
        const v = translate(step.value, env, oldEnv)
        if (v !== null) {
          const prev = env.nums.get(step.name) ?? numericVars.get(step.name)
          const guard = pc === null ? alive : ctx.And(alive, pc)
          if (prev === undefined) {
            env.nums.set(step.name, v)
          } else {
            const [cv, cp] = coerce2(v, prev)
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            env.nums.set(step.name, ctx.If(guard, cv as any, cp as any))
          }
        } else {
          // Untranslatable RHS: the variable DID change to something we can't
          // model — havoc it. Keeping the stale value would prove facts about
          // a world where the assignment never happened.
          env.nums.set(step.name, intVars.has(step.name)
            ? (ctx.Int.const(`${step.name}__havoc${sortCounter++}`) as unknown as AnyExpr<'main'>)
            : ctx.Real.const(`${step.name}__havoc${sortCounter++}`))
        }
        continue
      }

      if (step.kind === 'array-sort') {
        const av = arrayVars.get(step.name)
        if (av === undefined) continue
        // Havoc: element positions changed — every prior content fact dies.
        // Length is a separate constant and is preserved.
        const fresh = ctx.Array.const(
          `${step.name}__sorted${sortCounter++}`,
          ctx.Int.sort(),
          av.ref ? ctx.Int.sort() : ctx.Real.sort(),
        )
        env.arrays.set(step.name, fresh)
        // The trusted contract of Array.prototype.sort — granted ONLY for
        // the numeric ascending comparator, and only for number[] content.
        if (step.sorted && !av.ref) {
          try {
            const qi = ctx.Int.const(`__qs${sortCounter}a`)
            const qj = ctx.Int.const(`__qs${sortCounter}b`)
            assumptions.push(ctx.ForAll([qi, qj], ctx.Implies(
              ctx.And(qi.ge(0), qi.le(qj), qj.lt(av.len)),
              // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-argument
              (fresh.select(qi) as Arith<'main'>).le(fresh.select(qj) as Arith<'main'>),
            )))
            assumptionLabels.push(`sort: ${step.name} sorted ascending (numeric comparator)`)
          } catch { /* never block on the assumption */ }
        }
        continue
      }

      if (step.kind === 'loop') {
        // ── F6: havoc + invariant ────────────────────────────────────────
        // 1. ENTRY: invariants must hold on the state reaching the loop
        for (const inv of step.invariants) {
          const invZ3 = translate(inv, env, oldEnv)
          if (invZ3 === null) continue
          tasks.push({
            functionName: ir.name,
            contractText: `loop invariant (entry): ${prettyExpr(inv)}`,
            variables: taskVariables(),
            assumptions: [...assumptions],
            assumptionLabels: [...assumptionLabels],
            goal: ctx.Not(invZ3 as Bool<'main'>),
            domainConstraints: [],
          })
        }

        // State the loop may modify: fields written + numerics assigned
        const loopFields = new Set<string>()
        const loopNums = new Set<string>()
        const scanBody = (list: typeof steps): void => {
          for (const s of list) {
            if (s.kind === 'field-write') loopFields.add(s.field)
            else if (s.kind === 'num-assign') loopNums.add(s.name)
            else if (s.kind === 'branch') { scanBody(s.then); scanBody(s.else) }
          }
        }
        scanBody(step.body)

        // 2. PRESERVATION: fresh (havoced) state, assume invariants +
        //    condition, run the body, prove invariants again
        const freshEnv: Env = {
          heap: new Map(env.heap), locals: new Map(env.locals),
          nums: new Map(env.nums), arrays: new Map(env.arrays), tag: env.tag,
        }
        for (const f of loopFields) {
          const range = refFields.has(f) ? ctx.Int.sort() : ctx.Real.sort()
          freshEnv.heap.set(f, ctx.Array.const(`__heap_${f}_iter${loopCounter}`, ctx.Int.sort(), range))
        }
        for (const n of loopNums) {
          freshEnv.nums.set(n, intVars.has(n)
            ? (ctx.Int.const(`${n}_iter${loopCounter}`) as unknown as AnyExpr<'main'>)
            : ctx.Real.const(`${n}_iter${loopCounter}`))
        }

        const iterAssumptions: Bool<'main'>[] = [...assumptions]
        const iterLabels: string[] = [...assumptionLabels]
        for (const inv of step.invariants) {
          const invZ3 = translate(inv, freshEnv, oldEnv)
          if (invZ3 !== null) {
            iterAssumptions.push(invZ3 as Bool<'main'>)
            iterLabels.push(`loop invariant: ${prettyExpr(inv)}`)
          }
        }
        const condFresh = translate(step.condition, freshEnv, oldEnv)
        if (condFresh !== null) {
          iterAssumptions.push(condFresh as Bool<'main'>)
          iterLabels.push(`loop condition: ${prettyExpr(step.condition)}`)
        }
        // Spec-definition axioms at the havoced iteration state
        pushSpecAxioms(freshEnv, iterAssumptions, iterLabels, `iter${loopCounter}`)

        const measureBefore = step.decreases !== undefined ? translate(step.decreases, freshEnv, oldEnv) : null

        // Execute one iteration of the body against the fresh state
        const bodyEnv: Env = {
          heap: new Map(freshEnv.heap), locals: new Map(freshEnv.locals),
          nums: new Map(freshEnv.nums), arrays: new Map(freshEnv.arrays), tag: freshEnv.tag,
        }
        runLoopBody(step.body, bodyEnv, null)

        // Axioms at the state AFTER one iteration, plus ownership bridges
        // across the iteration (writes outside the footprint preserve specs)
        pushSpecAxioms(bodyEnv, iterAssumptions, iterLabels, `iterEnd${loopCounter}`)
        {
          const bodyRoots = new Set<string>()
          let bodyDirect = true
          const scanBodyWrites = (list: typeof steps): void => {
            for (const s of list) {
              if (s.kind === 'field-write') {
                if (s.object.kind === 'ident') bodyRoots.add(resolveAlias(s.object.name, aliasOf))
                else bodyDirect = false
              } else if (s.kind === 'branch') { scanBodyWrites(s.then); scanBodyWrites(s.else) }
            }
          }
          scanBodyWrites(step.body)
          if (bodyDirect && bodyRoots.size > 0) {
            const apps: Array<{ callee: string; args: Expr[] }> = []
            for (const inv of step.invariants) collectRootApps(inv, apps)
            emitOwnershipBridges(apps, bodyRoots, freshEnv, bodyEnv, iterAssumptions, iterLabels)
          }
        }

        for (const inv of step.invariants) {
          const invZ3 = translate(inv, bodyEnv, oldEnv)
          if (invZ3 === null) continue
          tasks.push({
            functionName: ir.name,
            contractText: `loop invariant (preserved): ${prettyExpr(inv)}`,
            variables: taskVariables(),
            assumptions: iterAssumptions,
            assumptionLabels: iterLabels,
            goal: ctx.Not(invZ3 as Bool<'main'>),
            domainConstraints: [],
          })
        }

        // Termination: measure bounded below and strictly decreasing
        if (step.decreases !== undefined && measureBefore !== null) {
          tasks.push({
            functionName: ir.name,
            contractText: `loop bound: ${prettyExpr(step.decreases)} >= 0`,
            variables: taskVariables(),
            assumptions: iterAssumptions,
            assumptionLabels: iterLabels,
            goal: ctx.Not((measureBefore as Arith<'main'>).ge(isIntSorted(measureBefore) ? (ctx.Int.val(0) as unknown as Arith<'main'>) : ctx.Real.val(0))),
            domainConstraints: [],
          })
          const measureAfter = translate(step.decreases, bodyEnv, oldEnv)
          if (measureAfter !== null) {
            tasks.push({
              functionName: ir.name,
              contractText: `loop decrease: ${prettyExpr(step.decreases)} strictly decreases`,
              variables: taskVariables(),
              assumptions: iterAssumptions,
              assumptionLabels: iterLabels,
              goal: ctx.Not((measureAfter as Arith<'main'>).lt(measureBefore as Arith<'main'>)),
              domainConstraints: [],
            })
          }
        }

        // 3. POST-LOOP: continue with fresh state where invariants hold and
        //    the condition is false
        for (const f of loopFields) {
          const range = refFields.has(f) ? ctx.Int.sort() : ctx.Real.sort()
          env.heap.set(f, ctx.Array.const(`__heap_${f}_post${loopCounter}`, ctx.Int.sort(), range))
        }
        for (const n of loopNums) {
          env.nums.set(n, intVars.has(n)
            ? (ctx.Int.const(`${n}_post${loopCounter}`) as unknown as AnyExpr<'main'>)
            : ctx.Real.const(`${n}_post${loopCounter}`))
        }
        for (const inv of step.invariants) {
          const invZ3 = translate(inv, env, oldEnv)
          if (invZ3 !== null) {
            assumptions.push(invZ3 as Bool<'main'>)
            assumptionLabels.push(`post-loop invariant: ${prettyExpr(inv)}`)
          }
        }
        const condPost = translate(step.condition, env, oldEnv)
        if (condPost !== null) {
          assumptions.push(ctx.Not(condPost as Bool<'main'>))
          assumptionLabels.push(`post-loop: !(${prettyExpr(step.condition)})`)
        }
        // Axioms at the post-loop state
        pushSpecAxioms(env, assumptions, assumptionLabels, `postLoop${loopCounter}`)
        loopCounter++
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

  // Definitional axioms instantiated at the FINAL state — select-over-store
  // connects them to the initial-state facts through the written window
  pushSpecAxioms(env, assumptions, assumptionLabels, 'final')

  // F5 — ownership frame bridges between the initial and final states,
  // via the footprint(spec, membership) pairing (see emitOwnershipBridges)
  if (ir.footprints !== undefined && ir.footprints.size > 0) {
    const writtenRoots = new Set<string>()
    let allWritesDirect = true
    const scanWrites = (list: typeof steps): void => {
      for (const s of list) {
        if (s.kind === 'field-write') {
          if (s.object.kind === 'ident') writtenRoots.add(resolveAlias(s.object.name, aliasOf))
          else allWritesDirect = false
        } else if (s.kind === 'branch') { scanWrites(s.then); scanWrites(s.else) }
        else if (s.kind === 'loop') scanWrites(s.body)
      }
    }
    scanWrites(steps)
    if (allWritesDirect) {
      const apps: Array<{ callee: string; args: Expr[] }> = []
      for (const c of ir.contracts) {
        if (c.kind === 'ensures' && typeof c.predicate === 'object' && c.predicate !== null) {
          collectRootApps(c.predicate as Expr, apps)
        }
      }
      emitOwnershipBridges(apps, writtenRoots, oldEnv, env, assumptions, assumptionLabels)
    }
  }

  // ── Ensures: hold in the final state ─────────────────────────────────────
  const variables = new Map<string, AnyExpr<'main'>>()
  for (const [name, ref] of refs) variables.set(name, ref as unknown as AnyExpr<'main'>)
  for (const [name, v] of numericVars) variables.set(name, v)
  for (const [name, av] of arrayVars) {
    variables.set(name, av.arr as AnyExpr<'main'>)
    variables.set(`${name}.length`, av.len as unknown as AnyExpr<'main'>)
  }

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
      } else if (step.kind === 'loop') {
        walk(step.condition)
        for (const inv of step.invariants) walk(inv)
        walkSteps(step.body)
      } else if (step.kind === 'num-assign') {
        walk(step.value)
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
      if (expr.property !== 'length') fields.add(expr.property)
      collectFields(expr.object, fields)
      break
    case 'element-access':
      collectFields(expr.object, fields); collectFields(expr.index, fields); break
    case 'quantifier':
      collectFields(expr.body, fields); break
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