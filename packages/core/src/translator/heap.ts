import type { AnyExpr, Arith, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, FunctionIR } from '../parser/ir.js'
import type { VerificationTask } from './index.js'
import { prettyExpr } from '../parser/pretty.js'

/**
 * Heap-as-map encoding — mutation levels 2 and 3.
 *
 * When a function mutates fields of object parameters, flat per-path
 * variables are UNSOUND under aliasing (`f(a, b)` with `a === b`). Here the
 * heap is encoded per field as a Z3 array Int → Real:
 *
 *   read  a.x      →  Select(heap_x, refA)
 *   write a.x = v  →  heap_x' = Store(heap_x, refA, v)
 *
 * Object roots become Int constants ("references"): aliasing is simply
 * refA === refB, which the solver explores like any other equality. Requires
 * are evaluated against the initial heap, ensures against the final one, and
 * old(a.x) reads the initial heap — the classic two-state encoding.
 *
 * Level 3: a `modifies(a, b)` contract restricts which roots may be written;
 * an undeclared write is reported as a violation.
 */
export function translateHeapMode(ir: FunctionIR, ctx: Z3Context): VerificationTask[] {
  const steps = ir.heapSteps ?? []
  const declaredRoots = new Set(ir.heapRoots ?? [])
  const tasks: VerificationTask[] = []

  // ── References: one Int constant per object root; aliases share ──────────
  const refs = new Map<string, Arith<'main'>>()
  const aliasOf = new Map<string, string>()
  for (const step of steps) {
    if (step.kind === 'alias') aliasOf.set(step.name, resolveAlias(step.of, aliasOf))
  }
  const rootNames = new Set<string>(declaredRoots)
  for (const step of steps) if (step.kind === 'field-write') rootNames.add(resolveAlias(step.root, aliasOf))
  for (const name of rootNames) refs.set(name, ctx.Int.const(name))

  // ── Fields: collect every field mentioned in steps and contracts ─────────
  const fields = new Set<string>()
  for (const step of steps) {
    if (step.kind === 'field-write') fields.add(step.field)
    if (step.kind !== 'alias') collectFields(step.value, fields, refs, aliasOf)
  }
  for (const c of ir.contracts) {
    if ('predicate' in c && typeof c.predicate === 'object') collectFields(c.predicate as Expr, fields, refs, aliasOf)
  }

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const initialHeap = new Map<string, any>()
  for (const f of fields) {
    initialHeap.set(f, ctx.Array.const(`__heap_${f}`, ctx.Int.sort(), ctx.Real.sort()))
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
  }

  const translate = (expr: Expr, env: Env, oldEnv: Env): AnyExpr<'main'> | null => {
    switch (expr.kind) {
      case 'literal':
        if (typeof expr.value === 'number') return ctx.Real.val(expr.value)
        if (typeof expr.value === 'boolean') return ctx.Bool.val(expr.value)
        return null
      case 'ident': {
        const resolved = resolveAlias(expr.name, aliasOf)
        return env.locals.get(expr.name) ?? refs.get(resolved) ?? numericVars.get(expr.name) ?? null
      }
      case 'member': {
        if (expr.object.kind === 'ident') {
          const root = resolveAlias(expr.object.name, aliasOf)
          const ref = refs.get(root)
          const heap = env.heap.get(expr.property)
          if (ref !== undefined && heap !== undefined) {
            // eslint-disable-next-line @typescript-eslint/no-unsafe-return, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
            return heap.select(ref)
          }
        }
        return null
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
      }
      case 'ternary': {
        const c = translate(expr.condition, env, oldEnv)
        const t = translate(expr.then, env, oldEnv)
        const e = translate(expr.else, env, oldEnv)
        if (c === null || t === null || e === null) return null
        return ctx.If(c as Bool<'main'>, t, e)
      }
      case 'call': {
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

  const oldEnv: Env = { heap: initialHeap, locals: new Map() }

  // ── Requires: hold in the initial state ──────────────────────────────────
  const assumptions: Bool<'main'>[] = []
  const assumptionLabels: string[] = []
  for (const c of ir.contracts) {
    if (c.kind !== 'requires' || typeof c.predicate === 'string') continue
    const z3 = translate(c.predicate, oldEnv, oldEnv)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`requires: ${prettyExpr(c.predicate)}`)
    }
  }

  // ── Execute steps over the heap ──────────────────────────────────────────
  const env: Env = { heap: new Map(initialHeap), locals: new Map() }
  const modifiesContract = ir.contracts.find(c => c.kind === 'modifies')
  const allowedWrites = modifiesContract !== undefined
    ? new Set((modifiesContract as { refs: string[] }).refs.map(r => resolveAlias(r, aliasOf)))
    : null

  for (const step of steps) {
    if (step.kind === 'alias') continue
    if (step.kind === 'local') {
      const v = translate(step.value, env, oldEnv)
      if (v !== null) env.locals.set(step.name, v)
      continue
    }
    // field-write
    const root = resolveAlias(step.root, aliasOf)
    const ref = refs.get(root)
    const heap = env.heap.get(step.field)
    const value = translate(step.value, env, oldEnv)
    if (ref === undefined || heap === undefined || value === null) continue

    // Level 3: framing — undeclared writes are contract violations
    if (allowedWrites !== null && !allowedWrites.has(root)) {
      tasks.push({
        functionName: ir.name,
        contractText: `modifies violation: writes ${step.root}.${step.field}, not declared in modifies(${[...allowedWrites].join(', ')})`,
        variables: new Map(refs as unknown as Map<string, AnyExpr<'main'>>),
        assumptions: [],
        assumptionLabels: [],
        goal: ctx.Bool.val(true),  // unconditionally violated
        domainConstraints: [],
      })
    }

    // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-assignment
    env.heap.set(step.field, heap.store(ref, value))
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

function collectFields(expr: Expr, fields: Set<string>, refs: Map<string, unknown>, aliasOf: Map<string, string>): void {
  switch (expr.kind) {
    case 'member':
      if (expr.object.kind === 'ident') fields.add(expr.property)
      else collectFields(expr.object, fields, refs, aliasOf)
      break
    case 'binary':
      collectFields(expr.left, fields, refs, aliasOf); collectFields(expr.right, fields, refs, aliasOf); break
    case 'unary':
      collectFields(expr.operand, fields, refs, aliasOf); break
    case 'ternary':
      collectFields(expr.condition, fields, refs, aliasOf); collectFields(expr.then, fields, refs, aliasOf); collectFields(expr.else, fields, refs, aliasOf); break
    case 'call':
      for (const a of expr.args) collectFields(a, fields, refs, aliasOf); break
    default:
      break
  }
}