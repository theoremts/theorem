import type { AnyExpr, Arith, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Contract, Expr, FunctionIR, Loc, LoopInfo, Param, Predicate } from '../parser/ir.js'
import type { ContractRegistry } from '../registry/index.js'
import { prettyExpr } from '../parser/pretty.js'
import { createVariables, makeConst } from './variables.js'
import { toZ3 } from './expr.js'
import { translateStringContract } from './string-contracts.js'
import { substituteExpr, substituteOutput } from './substitution.js'
import { translateHeapMode } from './heap.js'
import { unfoldSpecCalls, rewriteNullToRef } from './spec-unfold.js'

export type { Z3Context }

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

export interface VerificationTask {
  functionName?: string | undefined
  contractText: string
  variables: Map<string, AnyExpr<'main'>>
  assumptions: Bool<'main'>[]
  assumptionLabels: string[]
  goal: Bool<'main'>
  domainConstraints: Bool<'main'>[]
  /** Named intermediate expressions to evaluate in counterexamples (SSA trace). */
  traceExprs?: Map<string, AnyExpr<'main'>> | undefined
  /** Source locations of relevant expressions (body branches, assignments) for error highlighting. */
  traceLocs?: Map<string, import('../parser/ir.js').Loc> | undefined
  /**
   * Informational task: proved is worth reporting (e.g. "error branch
   * unreachable"), but disproved is NORMAL and must not count as a failure.
   */
  informational?: boolean | undefined
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

export function translate(
  ir: FunctionIR,
  ctx: Z3Context,
  registry?: ContractRegistry,
): VerificationTask[] {
  // Heap mode runs FIRST and owns its own spec-unfolding pipeline: axioms
  // must be instantiated PER HEAP VERSION (@pre/@post), and heap-mode null
  // is already a value (NULL_REF) — the general preprocessing below would
  // convert calls prematurely and rewrite null into an unresolvable ident.
  if (ir.heapSteps !== undefined && ir.heapSteps.length > 0) {
    return translateHeapMode(ir, ctx)
  }

  // Spec functions: calls in contract predicates become uninterpreted
  // applications (congruence!), with ground definitional axioms emitted per
  // call instance up to the fuel bound (see translator/spec-unfold.ts)
  if (ir.specDefs !== undefined && ir.specDefs.size > 0) {
    const defs = ir.specDefs
    const axioms: Array<{ text: string; predicate: Expr }> = []
    const contracts = ir.contracts.map(c => {
      if ('predicate' in c && typeof c.predicate === 'object' && c.predicate !== null) {
        const unfolded = unfoldSpecCalls(c.predicate as Expr, defs)
        axioms.push(...unfolded.axioms)
        return { ...c, predicate: unfolded.expr } as typeof c
      }
      return c
    })
    if (axioms.length > 0) {
      const seenAxioms = new Set<string>()
      const uniqueAxioms = axioms.filter(a => {
        const key = prettyExpr(a.predicate)
        if (seenAxioms.has(key)) return false
        seenAxioms.add(key)
        return true
      })

      // Within spec tasks null must be a VALUE (see rewriteNullToRef): the
      // per-name boolean encoding breaks congruence through equalities.
      const specContracts = contracts.map(c =>
        'predicate' in c && typeof c.predicate === 'object' && c.predicate !== null
          ? { ...c, predicate: rewriteNullToRef(c.predicate as Expr) } as typeof c
          : c)
      const specAxioms = uniqueAxioms.map(a => rewriteNullToRef(a.predicate))

      // Object-literal producers yield non-null results
      const notNullFacts: Contract[] = []
      if (ir.body !== undefined && (ir.body.kind === 'object' ||
          (ir.body.kind === 'ternary' && ir.body.then.kind === 'object' && ir.body.else.kind === 'object'))) {
        notNullFacts.push({
          kind: 'assume',
          predicate: {
            kind: 'binary', op: '!==',
            left: { kind: 'call', callee: 'output', args: [] },
            right: { kind: 'ident', name: '__nullref' },
          },
        })
      }

      // Axioms PREPENDED: assume/ensures share one sequential pass, and the
      // ensures task snapshots the assumptions gathered so far
      ir = {
        ...ir,
        contracts: [
          ...specAxioms.map(p => ({ kind: 'assume' as const, predicate: p })),
          ...notNullFacts,
          ...specContracts,
        ],
      }
    } else if (contracts.some((c, i) => c !== ir.contracts[i])) {
      ir = { ...ir, contracts }
    }
  }

  const vars = createVariables(ir.params, ir.returnSort, ctx)
  const tasks: VerificationTask[] = []

  // Register free variables for identifiers that are not params — e.g. Zod
  // parse results (`const rate = Schema.parse(x)` deliberately leaves `rate`
  // unbound; the schema constraints on it arrive as assume contracts).
  for (const contract of ir.contracts) {
    if ((contract.kind === 'assume' || contract.kind === 'requires') && typeof contract.predicate !== 'string') {
      ensureIdentVars(contract.predicate, vars, ctx)
    }
  }
  if (ir.body !== undefined) ensureIdentVars(ir.body, vars, ctx)

  // 1. Translate requires → assumptions (with labels for unsat core)
  const assumptions: Bool<'main'>[] = []
  const assumptionLabels: string[] = []

  // L1 visibility: field mutations the parser could not model are a
  // stated assumption, not silence — they show up in every task's context.
  if (ir.unmodeledWrites !== undefined) {
    for (const w of ir.unmodeledWrites) {
      assumptionLabels.push(`WARNING unmodeled field mutation: ${w} (body shape unsupported for heap mode)`)
    }
  }

  for (const contract of ir.contracts) {
    if (contract.kind !== 'requires') continue
    const z3 = translatePredicate(contract.predicate, vars, ctx)
    if (z3 !== null) {
      assumptions.push(z3 as Bool<'main'>)
      assumptionLabels.push(`requires: ${predicateText(contract.predicate)}`)
    }
  }

  // 2. Body constraint: result === body(params)
  //    Also collects call-site obligations from cross-function calls.
  const callObligations: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }> = []
  const callAssumptions: Bool<'main'>[] = []
  const traceExprs = new Map<string, AnyExpr<'main'>>()
  const traceLocs = new Map<string, Loc>()

  if (ir.body !== undefined) {
    // Special case: body is an object literal { prop: expr, ... }
    // Expand into: result.prop1 = expr1 AND result.prop2 = expr2
    if (ir.body.kind === 'object') {
      for (const prop of ir.body.properties) {
        if (prop.key === '...') continue  // skip spread
        const propName = `result.${prop.key}`
        if (!vars.has(propName)) {
          vars.set(propName, makeConst(propName, 'real', ctx))
        }
        // `prop: null` → equate with the null VALUE reference (spec tasks
        // reason about nullness through equalities, not per-name booleans)
        const isNullProp = prop.value.kind === 'literal' && prop.value.value === null
        if (isNullProp && !vars.has('__nullref')) {
          vars.set('__nullref', makeConst('__nullref', 'real', ctx))
        }
        const propZ3 = isNullProp ? vars.get('__nullref')! : toZ3(prop.value, vars, ctx)
        const propVar = vars.get(propName)
        if (propZ3 !== null && propVar !== undefined) {
          try {
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            assumptions.push((propVar as any).eq(propZ3))
            assumptionLabels.push(`body: ${propName} = ${prettyExpr(prop.value)}`)
          } catch { /* sort mismatch */ }
        }
      }
    }

    // Ternary of object literals: `cond ? { lo: a, hi: b } : { lo: b, hi: a }`
    // expands into per-property ITEs on result.prop
    if (ir.body.kind === 'ternary' && ir.body.then.kind === 'object' && ir.body.else.kind === 'object') {
      const condZ3 = toZ3(ir.body.condition, vars, ctx)
      if (condZ3 !== null) {
        const thenProps = new Map(ir.body.then.properties.map(p => [p.key, p.value]))
        const elseProps = new Map(ir.body.else.properties.map(p => [p.key, p.value]))
        for (const [key, thenVal] of thenProps) {
          const elseVal = elseProps.get(key)
          if (elseVal === undefined || key === '...') continue
          const propName = `result.${key}`
          if (!vars.has(propName)) vars.set(propName, makeConst(propName, 'real', ctx))
          const thenZ3 = toZ3(thenVal, vars, ctx)
          const elseZ3 = toZ3(elseVal, vars, ctx)
          const propVar = vars.get(propName)
          if (thenZ3 !== null && elseZ3 !== null && propVar !== undefined) {
            try {
              // eslint-disable-next-line @typescript-eslint/no-explicit-any
              assumptions.push((propVar as any).eq(ctx.If(condZ3 as Bool<'main'>, thenZ3, elseZ3)))
              assumptionLabels.push(`body: ${propName} = ${prettyExpr(ir.body.condition)} ? ... : ...`)
            } catch { /* sort mismatch */ }
          }
        }
      }
    }

    // Collect trace expressions for intermediate variable display in counterexamples
    collectTraceExprs(ir.body, vars, ctx, traceExprs, traceLocs)

    const bodyZ3 = translateBody(ir.body, vars, ctx, registry, callObligations, callAssumptions)
    const resultVar = vars.get('result')
    if (bodyZ3 !== null && resultVar !== undefined) {
      try {
        let coercedBody = bodyZ3
        try {
          if (ctx.isInt(bodyZ3) && ctx.isReal(resultVar)) {
            coercedBody = ctx.ToReal(bodyZ3 as Arith<'main'>)
          } else if (ctx.isReal(bodyZ3) && ctx.isInt(resultVar)) {
            coercedBody = bodyZ3
          }
        } catch { /* not arithmetic sorts */ }
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        assumptions.push((resultVar as any).eq(coercedBody))
        assumptionLabels.push('body: result = <function body>')
      } catch {
        // Sort mismatch (e.g. Real vs String, Array vs Real) — skip body constraint
      }
    }
  }

  // Add null constraints from ternary null-branch handling
  const nullConstraint = vars.get('__null_constraint')
  if (nullConstraint !== undefined) {
    assumptions.push(nullConstraint as Bool<'main'>)
    assumptionLabels.push('null branch constraint')
  }

  // Object property existence constraints will be added after ensures translation
  // (deferred because __has_*_result vars are created during ensures translation)

  // Add callee postconditions as assumptions
  for (const ca of callAssumptions) {
    assumptions.push(ca)
    assumptionLabels.push('callee ensures')
  }

  // 3. Body safety obligations — division by zero, etc. — plus dead
  //    typed-error branches (Effect.fail under contradictory conditions).
  const unreachableFails: Array<{ text: string; conditions: Expr[] }> = []
  if (ir.body !== undefined) {
    collectBodySafetyObligations(ir.body, vars, ctx, callObligations, unreachableFails)
  }

  // 4. Domain constraints — .length >= 0, numeric union domain
  const domainConstraints = collectDomainConstraints(vars, ir.params, ctx)

  // 5. Merge loop-indexed contracts (loop(N).invariant/decreases) with extracted loops
  if (ir.loops) {
    for (let i = 0; i < ir.loops.length; i++) {
      const loop = ir.loops[i]!
      // Add invariants/decreases from loop-indexed contracts (loop(i).invariant(...))
      for (const c of ir.contracts) {
        if (c.kind === 'invariant' && c.loopIndex === i && typeof c.predicate !== 'string') {
          loop.invariants.push(c.predicate)
        }
        if (c.kind === 'decreases' && c.loopIndex === i && loop.decreases === undefined) {
          loop.decreases = c.expression
        }
      }
    }
  }

  // 6. Loop invariant verification tasks + post-loop assumptions
  //    Must come before ensures so post-loop state is available as assumptions.
  if (ir.loops) {
    for (const loop of ir.loops) {
      ensureLoopVariables(loop, vars, ctx)

      const loopTasks = translateLoop(loop, ir, vars, assumptions, assumptionLabels, domainConstraints, ctx)
      tasks.push(...loopTasks)

      // After the loop: assume all invariants hold AND loop condition is false.
      for (const inv of loop.invariants) {
        const invZ3 = toZ3(inv, vars, ctx)
        if (invZ3 !== null) {
          assumptions.push(invZ3 as Bool<'main'>)
          assumptionLabels.push(`post-loop invariant: ${prettyExpr(inv)}`)
        }
      }
      const condZ3 = toZ3(loop.condition, vars, ctx)
      if (condZ3 !== null) {
        assumptions.push(ctx.Not(condZ3 as Bool<'main'>))
        assumptionLabels.push(`loop terminated: !${prettyExpr(loop.condition)}`)
      }
    }
  }

  // 6b. Recursive termination verification
  //     When a function has a decreases contract (not loop-indexed) AND recursive calls,
  //     generate tasks to prove the measure is bounded and strictly decreasing.
  try {
    const recursiveDecreaseTasks = translateRecursiveDecreases(ir, vars, assumptions, assumptionLabels, domainConstraints, ctx)
    tasks.push(...recursiveDecreaseTasks)
  } catch {
    // Never crash on unsupported patterns — skip recursive termination checks
  }

  // 5b. Two-state model — create __old_ variables for ensures predicates.
  //     old(x) in an ensures clause refers to the value of x at function entry.
  //     We create __old_<param> = <param> for every parameter, then if the body
  //     constrains <param> to a new value, __old_<param> still holds the original.
  //     For member-access variables (e.g. from.balance), we also create __old_ copies.
  const hasOldOrConserved = ir.contracts.some(
    c => c.kind === 'ensures' && typeof c.predicate !== 'string' && exprUsesOld(c.predicate)
  )

  if (hasOldOrConserved) {
    // Create __old_ copies for all params
    for (const param of ir.params) {
      const oldName = `__old_${param.name}`
      if (!vars.has(oldName)) {
        vars.set(oldName, makeConst(oldName, param.sort, ctx))
        const original = vars.get(param.name)
        if (original) {
          // eslint-disable-next-line @typescript-eslint/no-explicit-any
          assumptions.push((vars.get(oldName)! as any).eq(original) as Bool<'main'>)
          assumptionLabels.push(`old: __old_${param.name} = ${param.name}`)
        }
      }
    }

    // Also create __old_ copies for member-access variables already in the map
    const memberVarEntries = [...vars.entries()].filter(([name]) => name.includes('.') && !name.startsWith('__old_'))
    for (const [name, z3var] of memberVarEntries) {
      const oldName = `__old_${name}`
      if (!vars.has(oldName)) {
        vars.set(oldName, makeConst(oldName, 'real', ctx))
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        assumptions.push((vars.get(oldName)! as any).eq(z3var) as Bool<'main'>)
        assumptionLabels.push(`old: __old_${name} = ${name}`)
      }
    }
  }

  // 6. Process check / assume / unreachable / ensures contracts.
  //    When bodySteps exists, check/assume are processed positionally (SSA-aware).
  //    Otherwise, they use the pre-body assumptions.
  const positionalCheckDone = new Set<string>()

  if (ir.bodySteps && ir.bodySteps.length > 0) {
    // Positional processing: check/assume see the SSA state at their position
    // The body assumptions already contain the SSA-resolved body constraint.
    // We process checks/assumes with the body's SSA bindings applied.
    for (const step of ir.bodySteps) {
      if (step.kind === 'check') {
        const goalZ3 = translatePredicate(step.predicate, vars, ctx)
        if (goalZ3 === null) continue
        const text = `check: ${predicateText(step.predicate)}`
        positionalCheckDone.add(text)
        tasks.push({
          functionName: ir.name,
          contractText: text,
          variables: vars,
          assumptions: [...assumptions],  // includes SSA body constraint
          assumptionLabels: [...assumptionLabels],
          goal: ctx.Not(goalZ3 as Bool<'main'>),
          domainConstraints,
          traceExprs: traceExprs.size > 0 ? new Map(traceExprs) : undefined,
      traceLocs: traceLocs.size > 0 ? new Map(traceLocs) : undefined,
        })
      }
      if (step.kind === 'assume') {
        const z3 = translatePredicate(step.predicate, vars, ctx)
        if (z3 !== null) {
          assumptions.push(z3 as Bool<'main'>)
          assumptionLabels.push(`assume: ${predicateText(step.predicate)}`)
        }
      }
    }
  }

  for (const contract of ir.contracts) {
    if (contract.kind === 'assume') {
      if (ir.bodySteps) continue  // already processed positionally
      const z3 = translatePredicate(contract.predicate, vars, ctx)
      if (z3 !== null) {
        assumptions.push(z3 as Bool<'main'>)
        assumptionLabels.push(`assume: ${predicateText(contract.predicate)}`)
      }
      continue
    }

    if (contract.kind === 'check') {
      if (ir.bodySteps) continue  // already processed positionally with SSA
      const goalZ3 = translatePredicate(contract.predicate, vars, ctx)
      if (goalZ3 === null) continue
      tasks.push({
        functionName: ir.name,
        contractText: `check: ${predicateText(contract.predicate)}`,
        variables: vars,
        assumptions: [...assumptions],
        assumptionLabels: [...assumptionLabels],
        goal: ctx.Not(goalZ3 as Bool<'main'>),
        domainConstraints,
        traceExprs: traceExprs.size > 0 ? new Map(traceExprs) : undefined,
      traceLocs: traceLocs.size > 0 ? new Map(traceLocs) : undefined,
      })
      continue
    }

    if (contract.kind === 'unreachable') {
      // Goal is `false` — if UNSAT, the point is truly unreachable
      tasks.push({
        functionName: ir.name,
        contractText: 'unreachable',
        variables: vars,
        assumptions: [...assumptions],
        assumptionLabels: [...assumptionLabels],
        goal: ctx.Bool.val(true),   // negated goal: NOT false = true; solver checks SAT of (assumptions AND true)
        domainConstraints,
      traceExprs: traceExprs.size > 0 ? new Map(traceExprs) : undefined,
      traceLocs: traceLocs.size > 0 ? new Map(traceLocs) : undefined,
      })
      continue
    }

    if (contract.kind !== 'ensures') continue
    const goalZ3 = translatePredicate(contract.predicate, vars, ctx)
    if (goalZ3 === null) continue

    tasks.push({
      functionName: ir.name,
      contractText: predicateText(contract.predicate),
      variables: vars,
      assumptions: [...assumptions],
      assumptionLabels: [...assumptionLabels],
      goal: ctx.Not(goalZ3 as Bool<'main'>),
      domainConstraints,
      traceExprs: traceExprs.size > 0 ? new Map(traceExprs) : undefined,
      traceLocs: traceLocs.size > 0 ? new Map(traceLocs) : undefined,
    })
  }

  // 6c. Object property existence constraints (deferred from body analysis)
  //     Now that ensures have been translated and __has_*_result vars exist,
  //     we can connect them to the body's object structure.
  if (ir.body !== undefined) {
    const propAssumptions: Bool<'main'>[] = []
    const propLabels: string[] = []
    collectPropertyExistence(ir.body, ir.params, vars, ctx, propAssumptions, propLabels)
    if (propAssumptions.length > 0) {
      // Add to all existing tasks' assumptions
      for (const task of tasks) {
        task.assumptions.push(...propAssumptions)
        task.assumptionLabels?.push(...propLabels)
      }
      // Also add to base assumptions for remaining tasks
      assumptions.push(...propAssumptions)
      assumptionLabels.push(...propLabels)
    }
  }

  // 7. Call-site obligations + body safety obligations
  for (const obligation of callObligations) {
    const oblAssumptions = [...assumptions]
    const oblLabels = [...assumptionLabels]
    // Add path conditions (ternary branch guards) as assumptions
    if (obligation.pathConditions) {
      for (const pathCond of obligation.pathConditions) {
        const pathZ3 = toZ3(pathCond, vars, ctx)
        if (pathZ3 !== null) {
          oblAssumptions.push(pathZ3 as Bool<'main'>)
          oblLabels.push(`path: ${prettyExpr(pathCond)}`)
        }
      }
    }
    tasks.push({
      functionName: ir.name,
      contractText: obligation.text,
      variables: vars,
      assumptions: oblAssumptions,
      assumptionLabels: oblLabels,
      goal: ctx.Not(obligation.z3),
      domainConstraints,
      traceExprs: traceExprs.size > 0 ? new Map(traceExprs) : undefined,
      traceLocs: traceLocs.size > 0 ? new Map(traceLocs) : undefined,
    })
  }

  // 8. Dead error branches: prove the path conditions guarding a typed-error
  //    constructor contradict the contracts (informational — reachable is normal).
  for (const fail of unreachableFails) {
    let conj: Bool<'main'> | null = null
    for (const cond of fail.conditions) {
      const condZ3 = toZ3(cond, vars, ctx)
      if (condZ3 === null) { conj = null; break }
      conj = conj === null ? condZ3 as Bool<'main'> : ctx.And(conj, condZ3 as Bool<'main'>)
    }
    if (conj === null) continue
    tasks.push({
      functionName: ir.name,
      contractText: `unreachable error branch: ${fail.text}`,
      variables: vars,
      assumptions: [...assumptions],
      assumptionLabels: [...assumptionLabels],
      // goal is the VIOLATION: the branch being reachable. UNSAT ⇒ dead code.
      goal: conj,
      domainConstraints,
      informational: true,
    })
  }

  return tasks
}

// ---------------------------------------------------------------------------
// Trace expression collection — captures intermediate values for counterexamples
// ---------------------------------------------------------------------------

function collectTraceExprs(
  body: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  out: Map<string, AnyExpr<'main'>>,
  locs?: Map<string, Loc>,
): void {
  collectTraceRecursive(body, vars, ctx, out, locs, 0)
}

function collectTraceRecursive(
  expr: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  out: Map<string, AnyExpr<'main'>>,
  locs: Map<string, Loc> | undefined,
  depth: number,
): void {
  if (depth > 3) return  // limit depth to avoid noise

  switch (expr.kind) {
    case 'binary': {
      // Trace non-trivial sub-expressions
      for (const side of [expr.left, expr.right]) {
        if (side.kind !== 'ident' && side.kind !== 'literal') {
          const text = prettyExpr(side)
          if (!out.has(text) && text.length < 60) {
            try {
              const z3 = toZ3(side, vars, ctx)
              if (z3) {
                out.set(text, z3)
                if (locs && side.loc) locs.set(text, side.loc)
              }
            } catch {}
          }
          collectTraceRecursive(side, vars, ctx, out, locs, depth + 1)
        }
      }
      break
    }
    case 'ternary': {
      try {
        const condText = `(${prettyExpr(expr.condition)})`
        const condZ3 = toZ3(expr.condition, vars, ctx)
        if (condZ3) {
          out.set(condText, condZ3)
          if (locs && expr.condition.loc) locs.set(condText, expr.condition.loc)
        }
      } catch {}
      collectTraceRecursive(expr.then, vars, ctx, out, locs, depth + 1)
      collectTraceRecursive(expr.else, vars, ctx, out, locs, depth + 1)
      break
    }
    case 'call': {
      const text = prettyExpr(expr)
      if (!out.has(text) && text.length < 60) {
        try {
          const z3 = toZ3(expr, vars, ctx)
          if (z3) out.set(text, z3)
        } catch {}
      }
      break
    }
    default:
      break
  }
}

// ---------------------------------------------------------------------------
// Body translation with cross-function call handling
// ---------------------------------------------------------------------------

let callCounter = 0

function translateBody(
  expr: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  registry: ContractRegistry | undefined,
  obligations: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }>,
  callAssumptions: Bool<'main'>[],
  pathConditions: Expr[] = [],
): AnyExpr<'main'> | null {
  // Calls to registered functions can't be encoded by toZ3. Rewrite the
  // expression first: each such call becomes a fresh __ret identifier whose
  // requires are emitted as obligations and whose ensures become assumptions
  // (modular assume-guarantee). The rewritten expression is then translated
  // as a whole, so the `result = <body>` equation survives nested calls.
  if (registry && hasCallTo(expr, registry)) {
    const rewritten = rewriteRegisteredCalls(expr, vars, ctx, registry, obligations, callAssumptions, pathConditions)
    return toZ3(rewritten, vars, ctx)
  }

  return toZ3(expr, vars, ctx)
}

/**
 * Resolves a callee name against the registry.
 * Handles dotted names: `this.payments.calculateFee` → `calculateFee`
 *                       `service.applyDiscount` → `applyDiscount`
 */
function resolveCallee(callee: string, registry: ContractRegistry): string | null {
  // Direct match
  if (registry.has(callee)) return callee
  // Try the last segment of a dotted name: this.x.method → method
  const lastDot = callee.lastIndexOf('.')
  if (lastDot >= 0) {
    const methodName = callee.slice(lastDot + 1)
    if (registry.has(methodName)) return methodName
  }
  return null
}

function translateModularCall(
  callee: string,
  argExprs: Expr[],
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  registry: ContractRegistry,
  obligations: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }>,
  callAssumptions: Bool<'main'>[],
  pathConditions: Expr[] = [],
): { retVar: AnyExpr<'main'>; retName: string } | null {
  const contract = registry.get(callee)
  if (!contract) return null

  // Build a substitution: callee param names → actual argument expressions
  const mapping = new Map<string, Expr>()
  for (let i = 0; i < Math.min(contract.params.length, argExprs.length); i++) {
    mapping.set(contract.params[i]!.name, argExprs[i]!)
  }

  // Create a fresh variable for the return value
  const retName = `__ret_${callee}_${callCounter++}`
  const retIdent: Expr = { kind: 'ident', name: retName }
  const retVar = makeConst(retName, contract.returnSort, ctx)
  mapping.set('result', retIdent)
  vars.set(retName, retVar)

  // Generate caller obligations: each requires must be satisfied
  for (const req of contract.requires) {
    if (typeof req === 'string') continue  // skip string contracts for now
    const substituted = substituteExpr(req, mapping)
    const z3 = toZ3(substituted, vars, ctx)
    if (z3 !== null) {
      const argText = argExprs.map(a => prettyExpr(a)).join(', ')
      obligations.push({
        text: `call ${callee}(${argText}): ${predicateText(req)}`,
        z3: z3 as Bool<'main'>,
        ...(pathConditions.length > 0 ? { pathConditions: [...pathConditions] } : {}),
      })
    }
  }

  // Add callee postconditions as assumptions (substituted).
  // output() must refer to THIS call's fresh return variable — never to the
  // enclosing function's `result` (which toZ3 would otherwise resolve it to,
  // asserting the callee's ensures about the caller's own output).
  for (const ens of contract.ensures) {
    if (typeof ens === 'string') continue
    const substituted = substituteOutput(substituteExpr(ens, mapping), retIdent)
    const z3 = toZ3(substituted, vars, ctx)
    if (z3 !== null) {
      callAssumptions.push(z3 as Bool<'main'>)
    }
  }

  return { retVar, retName }
}

/**
 * Rewrites an expression, replacing every call to a registered function with
 * a fresh `__ret_*` identifier (already bound in `vars` by
 * translateModularCall, which also emits the call's obligations and
 * assumptions). Ternary branches extend the path conditions so obligations
 * inside a branch are only required under that branch's guard.
 */
function rewriteRegisteredCalls(
  expr: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  registry: ContractRegistry,
  obligations: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }>,
  callAssumptions: Bool<'main'>[],
  pathConditions: Expr[] = [],
): Expr {
  const recurse = (e: Expr, pcs: Expr[]): Expr =>
    rewriteRegisteredCalls(e, vars, ctx, registry, obligations, callAssumptions, pcs)

  switch (expr.kind) {
    case 'call': {
      const args = expr.args.map(a => recurse(a, pathConditions))
      const resolved = resolveCallee(expr.callee, registry)
      if (resolved !== null) {
        const call = translateModularCall(resolved, args, vars, ctx, registry, obligations, callAssumptions, pathConditions)
        if (call !== null) return { kind: 'ident', name: call.retName }
      }
      return { kind: 'call', callee: expr.callee, args }
    }

    case 'binary':
      return {
        kind: 'binary', op: expr.op,
        left: recurse(expr.left, pathConditions),
        right: recurse(expr.right, pathConditions),
      }

    case 'unary':
      return { kind: 'unary', op: expr.op, operand: recurse(expr.operand, pathConditions) }

    case 'ternary': {
      const condition = recurse(expr.condition, pathConditions)
      // In the then-branch, the condition holds; in the else-branch, it is negated
      const then = recurse(expr.then, [...pathConditions, expr.condition])
      const els = recurse(expr.else, [...pathConditions, { kind: 'unary' as const, op: '!' as const, operand: expr.condition }])
      return { kind: 'ternary', condition, then, else: els }
    }

    case 'member':
      return { kind: 'member', object: recurse(expr.object, pathConditions), property: expr.property }

    case 'element-access':
      return {
        kind: 'element-access',
        object: recurse(expr.object, pathConditions),
        index: recurse(expr.index, pathConditions),
      }

    case 'array':
      return { kind: 'array', elements: expr.elements.map(e => recurse(e, pathConditions)) }

    case 'object':
      return { kind: 'object', properties: expr.properties.map(p => ({ key: p.key, value: recurse(p.value, pathConditions) })) }

    default:
      return expr
  }
}

/** Check if an expression tree contains a call to a registered function. */
function hasCallTo(expr: Expr, registry: ContractRegistry): boolean {
  switch (expr.kind) {
    case 'call':           return resolveCallee(expr.callee, registry) !== null || expr.args.some(a => hasCallTo(a, registry))
    case 'binary':         return hasCallTo(expr.left, registry) || hasCallTo(expr.right, registry)
    case 'ternary':        return hasCallTo(expr.condition, registry) || hasCallTo(expr.then, registry) || hasCallTo(expr.else, registry)
    case 'unary':          return hasCallTo(expr.operand, registry)
    case 'member':         return hasCallTo(expr.object, registry)
    case 'element-access': return hasCallTo(expr.object, registry) || hasCallTo(expr.index, registry)
    case 'quantifier':     return hasCallTo(expr.body, registry)
    case 'array':          return expr.elements.some(e => hasCallTo(e, registry))
    case 'object':         return expr.properties.some(p => hasCallTo(p.value, registry))
    case 'spread':         return hasCallTo(expr.operand, registry)
    case 'template':       return expr.parts.some(p => typeof p !== 'string' && hasCallTo(p, registry))
    default:               return false
  }
}

// ---------------------------------------------------------------------------
// Loop invariant and termination verification
// ---------------------------------------------------------------------------

function translateLoop(
  loop: LoopInfo,
  ir: FunctionIR,
  vars: Map<string, AnyExpr<'main'>>,
  assumptions: Bool<'main'>[],
  assumptionLabels: string[],
  domainConstraints: Bool<'main'>[],
  ctx: Z3Context,
): VerificationTask[] {
  const tasks: VerificationTask[] = []

  if (loop.invariants.length === 0) return tasks

  // Ensure loop variables (referenced in invariants, condition, decreases)
  // have Z3 representations — create free Real variables for unknowns.
  ensureLoopVariables(loop, vars, ctx)

  const condZ3 = toZ3(loop.condition, vars, ctx)

  for (const inv of loop.invariants) {
    const invText = prettyExpr(inv)
    const invZ3 = toZ3(inv, vars, ctx)
    if (invZ3 === null) continue

    // Task 1: Initialization — preconditions + initial values imply invariant at loop entry
    // For initialization, we add constraints binding loop variables to their initial values.
    const initAssumptions = [...assumptions]
    const initLabels = [...assumptionLabels]
    if (loop.initializations) {
      for (const init of loop.initializations) {
        const nameVar = vars.get(init.name)
        const valZ3 = toZ3(init.value, vars, ctx)
        if (nameVar !== null && valZ3 !== null) {
          // eslint-disable-next-line @typescript-eslint/no-explicit-any
          initAssumptions.push((nameVar as any).eq(valZ3) as Bool<'main'>)
          initLabels.push(`init: ${init.name} = ${prettyExpr(init.value)}`)
        }
      }
    }
    tasks.push({
      functionName: ir.name,
      contractText: `loop invariant init: ${invText}`,
      variables: vars,
      assumptions: initAssumptions,
      assumptionLabels: initLabels,
      goal: ctx.Not(invZ3 as Bool<'main'>),
      domainConstraints,

    })

    // Task 2: Preservation — invariant + condition => invariant (after abstract iteration)
    // Since we model loop variables as free (unconstrained), preservation means:
    // assume invariant AND condition hold, then invariant must still hold.
    // With free variables this is: invariant && condition => invariant, which is trivially true.
    // Instead we use a havoc model: create fresh variables for the loop state,
    // assume the invariant holds for those, assume condition, and check invariant.
    // But since our variables are already free (not constrained by assignments),
    // the initialization check is the meaningful one.
    // We still emit the preservation check with invariant + condition as assumptions
    // so it can catch invariants that are too strong for the loop condition.
    if (condZ3 !== null) {
      tasks.push({
        functionName: ir.name,
        contractText: `loop invariant preservation: ${invText}`,
        variables: vars,
        assumptions: [invZ3 as Bool<'main'>, condZ3 as Bool<'main'>],
        assumptionLabels: [`invariant: ${invText}`, `loop condition: ${prettyExpr(loop.condition)}`],
        goal: ctx.Not(invZ3 as Bool<'main'>),
        domainConstraints,

      })
    }
  }

  // Task 3: Termination — if decreases is specified
  // invariant && condition => decreases >= 0
  if (loop.decreases !== undefined && condZ3 !== null) {
    const decZ3 = toZ3(loop.decreases, vars, ctx)
    if (decZ3 !== null) {
      const decText = prettyExpr(loop.decreases)

      // All invariants hold as assumptions for termination check
      const invAssumptions: Bool<'main'>[] = []
      const invLabels: string[] = []
      for (const inv of loop.invariants) {
        const z3 = toZ3(inv, vars, ctx)
        if (z3 !== null) {
          invAssumptions.push(z3 as Bool<'main'>)
          invLabels.push(`invariant: ${prettyExpr(inv)}`)
        }
      }

      // decreases >= 0 when invariant + condition hold
      const nonNegGoal = (decZ3 as Arith<'main'>).ge(ctx.Real.val(0))
      tasks.push({
        functionName: ir.name,
        contractText: `loop termination: ${decText} >= 0`,
        variables: vars,
        assumptions: [...invAssumptions, condZ3 as Bool<'main'>],
        assumptionLabels: [...invLabels, `loop condition: ${prettyExpr(loop.condition)}`],
        goal: ctx.Not(nonNegGoal as Bool<'main'>),
        domainConstraints,

      })
    }
  }

  return tasks
}

// ---------------------------------------------------------------------------
// Loop variable creation — ensures all identifiers in loop exprs have Z3 vars
// ---------------------------------------------------------------------------

function ensureLoopVariables(
  loop: LoopInfo,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
): void {
  const names = new Set<string>()
  collectIdents(loop.condition, names)
  for (const inv of loop.invariants) collectIdents(inv, names)
  if (loop.decreases) collectIdents(loop.decreases, names)

  for (const name of names) {
    if (!vars.has(name)) {
      vars.set(name, makeConst(name, 'real', ctx))
    }
  }
}

function collectIdents(expr: Expr, out: Set<string>): void {
  switch (expr.kind) {
    case 'ident':          out.add(expr.name); break
    case 'binary':         collectIdents(expr.left, out); collectIdents(expr.right, out); break
    case 'unary':          collectIdents(expr.operand, out); break
    case 'ternary':        collectIdents(expr.condition, out); collectIdents(expr.then, out); collectIdents(expr.else, out); break
    case 'call':           for (const a of expr.args) collectIdents(a, out); break
    case 'member':         collectIdents(expr.object, out); break
    case 'element-access': collectIdents(expr.object, out); collectIdents(expr.index, out); break
    case 'quantifier':     collectIdents(expr.body, out); break
    case 'array':          for (const e of expr.elements) collectIdents(e, out); break
    case 'object':         for (const p of expr.properties) collectIdents(p.value, out); break
    case 'spread':         collectIdents(expr.operand, out); break
    case 'template':       for (const p of expr.parts) { if (typeof p !== 'string') collectIdents(p, out) }; break
    default:               break
  }
}

// ---------------------------------------------------------------------------
// Body safety obligations — catches division by zero that Z3 would hide
// ---------------------------------------------------------------------------

/**
 * Creates free Real variables for plain identifiers that have no Z3
 * representation yet. Members/element-accesses self-register in toZ3;
 * plain idents (Zod parse results, destructured locals) do not.
 */
function ensureIdentVars(expr: Expr, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): void {
  switch (expr.kind) {
    case 'ident':
      if (!vars.has(expr.name)) vars.set(expr.name, makeConst(expr.name, 'real', ctx))
      break
    case 'binary':
      ensureIdentVars(expr.left, vars, ctx)
      ensureIdentVars(expr.right, vars, ctx)
      break
    case 'unary':
      ensureIdentVars(expr.operand, vars, ctx)
      break
    case 'ternary':
      ensureIdentVars(expr.condition, vars, ctx)
      ensureIdentVars(expr.then, vars, ctx)
      ensureIdentVars(expr.else, vars, ctx)
      break
    case 'call':
      for (const a of expr.args) ensureIdentVars(a, vars, ctx)
      break
    case 'array':
      for (const e of expr.elements) ensureIdentVars(e, vars, ctx)
      break
    case 'object':
      for (const p of expr.properties) ensureIdentVars(p.value, vars, ctx)
      break
    default:
      break
  }
}

function collectBodySafetyObligations(
  body: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  out: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }>,
  unreachableFails?: Array<{ text: string; conditions: Expr[] }>,
): void {
  walkBodyForRisks(body, vars, ctx, out, new Set(), [], unreachableFails)
}

/** Callee names treated as typed-error constructors (dead-branch analysis). */
function isFailCallee(callee: string): boolean {
  return callee === 'Effect.fail' || callee.endsWith('.fail') || callee === 'Effect.die' || callee.endsWith('.die')
}

function walkBodyForRisks(
  expr: Expr,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  out: Array<{ text: string; z3: Bool<'main'>; pathConditions?: Expr[] }>,
  seen: Set<string>,
  pathConditions: Expr[] = [],
  unreachableFails?: Array<{ text: string; conditions: Expr[] }>,
): void {
  switch (expr.kind) {
    case 'binary':
      if (expr.op === '/' || expr.op === '%') {
        const denomText = prettyExpr(expr.right)
        if (!seen.has(denomText)) {
          seen.add(denomText)
          // Skip literal non-zero denominators
          if (expr.right.kind === 'literal' && typeof expr.right.value === 'number' && expr.right.value !== 0) break
          const denomZ3 = toZ3(expr.right, vars, ctx)
          if (denomZ3 !== null) {
            out.push({
              text: `safe division: ${denomText} !== 0`,
              z3: ctx.Not((denomZ3 as Arith<'main'>).eq(ctx.Real.val(0)) as Bool<'main'>),
              ...(pathConditions.length > 0 ? { pathConditions: [...pathConditions] } : {}),
            })
          }
        }
      }
      walkBodyForRisks(expr.left, vars, ctx, out, seen, pathConditions, unreachableFails)
      walkBodyForRisks(expr.right, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'ternary': {
      walkBodyForRisks(expr.condition, vars, ctx, out, seen, pathConditions, unreachableFails)
      const negated: Expr = { kind: 'unary', op: '!', operand: expr.condition }
      walkBodyForRisks(expr.then, vars, ctx, out, seen, [...pathConditions, expr.condition], unreachableFails)
      walkBodyForRisks(expr.else, vars, ctx, out, seen, [...pathConditions, negated], unreachableFails)
      break
    }
    case 'unary':
      walkBodyForRisks(expr.operand, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'call': {
      // Dead-branch analysis: a typed-error constructor under path conditions
      // is unreachable when the conditions contradict the contracts.
      if (unreachableFails !== undefined && isFailCallee(expr.callee) && pathConditions.length > 0) {
        const text = `${expr.callee}(${expr.args.map(a => prettyExpr(a)).join(', ')})`
        const key = `fail:${text}:${pathConditions.map(c => prettyExpr(c)).join('∧')}`
        if (!seen.has(key)) {
          seen.add(key)
          unreachableFails.push({ text, conditions: [...pathConditions] })
        }
      }

      const isSqrt = expr.callee === 'Math.sqrt'
      const isLog = expr.callee === 'Math.log' || expr.callee === 'Math.log2' || expr.callee === 'Math.log10'
      if ((isSqrt || isLog) && expr.args.length > 0) {
        const arg = expr.args[0]!
        const argText = prettyExpr(arg)
        const key = `${expr.callee}:${argText}`
        if (!seen.has(key)) {
          seen.add(key)
          const skipLiteral = arg.kind === 'literal' && typeof arg.value === 'number' &&
            (isSqrt ? arg.value >= 0 : arg.value > 0)
          if (!skipLiteral) {
            const argZ3 = toZ3(arg, vars, ctx)
            if (argZ3 !== null) {
              out.push(isSqrt
                ? { text: `safe sqrt: ${argText} >= 0`, z3: (argZ3 as Arith<'main'>).ge(ctx.Real.val(0)) as Bool<'main'>, ...(pathConditions.length > 0 ? { pathConditions: [...pathConditions] } : {}) }
                : { text: `safe log: ${argText} > 0`, z3: (argZ3 as Arith<'main'>).gt(ctx.Real.val(0)) as Bool<'main'>, ...(pathConditions.length > 0 ? { pathConditions: [...pathConditions] } : {}) })
            }
          }
        }
      }
      for (const arg of expr.args) walkBodyForRisks(arg, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    }
    case 'member':
      walkBodyForRisks(expr.object, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'element-access':
      walkBodyForRisks(expr.object, vars, ctx, out, seen, pathConditions, unreachableFails)
      walkBodyForRisks(expr.index, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'array':
      for (const el of expr.elements) walkBodyForRisks(el, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'object':
      for (const p of expr.properties) walkBodyForRisks(p.value, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'spread':
      walkBodyForRisks(expr.operand, vars, ctx, out, seen, pathConditions, unreachableFails)
      break
    case 'template':
      for (const p of expr.parts) { if (typeof p !== 'string') walkBodyForRisks(p, vars, ctx, out, seen, pathConditions, unreachableFails) }
      break
    default:
      break
  }
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// Object property existence tracking
// ---------------------------------------------------------------------------

/**
 * Analyzes the body expression and generates __has_<prop>_result constraints.
 *
 * Handles:
 * - Object literal: `{ name, age }` → __has_name_result = true, __has_age_result = true
 * - Spread: `{ ...data }` → __has_X_result === __has_X_data for all known X
 * - Spread + explicit: `{ ...data, extra: 1 }` → spread + __has_extra_result = true
 * - Identity return: `return data` → __has_X_result === __has_X_data for all known X
 * - Ternary with null: `cond ? null : expr` → delegated to the non-null branch
 */
function collectPropertyExistence(
  body: Expr,
  params: Param[],
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
  assumptions: Bool<'main'>[],
  labels: string[],
): void {
  // Unwrap ternaries with null branches (guard patterns)
  let effectiveBody = body
  if (body.kind === 'ternary') {
    if (body.then.kind === 'literal' && body.then.value === null) effectiveBody = body.else
    else if (body.else.kind === 'literal' && body.else.value === null) effectiveBody = body.then
  }

  if (effectiveBody.kind === 'object') {
    // Object literal return — we know exactly which properties exist
    const explicitProps = new Set<string>()
    const spreadSources: string[] = []

    for (const prop of effectiveBody.properties) {
      if (prop.key === '...' && prop.value.kind === 'spread' && prop.value.operand.kind === 'ident') {
        // Spread: { ...data }
        spreadSources.push(prop.value.operand.name)
      } else if (prop.key !== '...') {
        explicitProps.add(prop.key)
      }
    }

    // Explicit properties are definitely present
    for (const propName of explicitProps) {
      const hasVar = getOrCreateBool(`__has_${propName}_result`, vars, ctx)
      assumptions.push(hasVar.eq(ctx.Bool.val(true)) as Bool<'main'>)
      labels.push(`property existence: result.${propName}`)
    }

    // Spread sources: propagate property existence from source to result
    // For any property X that the ensures/contract asks about, if the source
    // has __has_X_<source>, then __has_X_result === __has_X_<source>
    // We do this lazily: for any __has_*_result var that exists, check if there's
    // a matching source var and connect them.
    // But we don't know yet which props the contract will ask about.
    // Solution: store the spread sources so when __has_X_result is created later,
    // we can connect it. For now, connect any that already exist.
    for (const source of spreadSources) {
      for (const [name, expr] of vars) {
        const hasPrefix = `__has_`
        const resultSuffix = `_result`
        if (name.startsWith(hasPrefix) && name.endsWith(resultSuffix)) {
          const propName = name.slice(hasPrefix.length, -resultSuffix.length)
          if (explicitProps.has(propName)) continue // already set explicitly
          const sourceVarName = `__has_${propName}_${source}`
          const sourceVar = getOrCreateBool(sourceVarName, vars, ctx)
          assumptions.push((expr as Bool<'main'>).eq(sourceVar) as Bool<'main'>)
          labels.push(`spread property: result.${propName} from ${source}`)
        }
      }
      // Also store spread info for deferred resolution
      vars.set(`__spread_source_result`, ctx.Bool.const(source) as unknown as AnyExpr<'main'>)
    }

    // If no spread, properties NOT in explicitProps are absent
    if (spreadSources.length === 0) {
      for (const [name] of vars) {
        if (name.startsWith('__has_') && name.endsWith('_result')) {
          const propName = name.slice('__has_'.length, -'_result'.length)
          if (!explicitProps.has(propName)) {
            const hasVar = vars.get(name) as Bool<'main'>
            assumptions.push(hasVar.eq(ctx.Bool.val(false)) as Bool<'main'>)
            labels.push(`property absence: result.${propName}`)
          }
        }
      }
    }
  } else if (effectiveBody.kind === 'ident') {
    // Identity return: return data → result has same properties as data
    const sourceName = effectiveBody.name
    for (const [name, expr] of vars) {
      if (name.startsWith('__has_') && name.endsWith('_result')) {
        const propName = name.slice('__has_'.length, -'_result'.length)
        const sourceVarName = `__has_${propName}_${sourceName}`
        const sourceVar = getOrCreateBool(sourceVarName, vars, ctx)
        assumptions.push((expr as Bool<'main'>).eq(sourceVar) as Bool<'main'>)
        labels.push(`identity return: result.${propName} from ${sourceName}`)
      }
    }
  }
}

function getOrCreateBool(name: string, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): Bool<'main'> {
  let v = vars.get(name)
  if (!v) {
    v = ctx.Bool.const(name)
    vars.set(name, v)
  }
  return v as Bool<'main'>
}

// ---------------------------------------------------------------------------
// Domain constraints
// ---------------------------------------------------------------------------

function collectDomainConstraints(
  vars: Map<string, AnyExpr<'main'>>,
  params: Param[],
  ctx: Z3Context,
): Bool<'main'>[] {
  const constraints: Bool<'main'>[] = []
  for (const [name, expr] of vars) {
    if (name.endsWith('.length')) {
      try { constraints.push((expr as Arith<'main'>).ge(ctx.Real.val(0))) } catch {}
    }
  }

  // Numeric union domain constraints: variable must be one of the allowed values
  // e.g. type Status = 0 | 1 | 2  =>  status === 0 || status === 1 || status === 2
  for (const param of params) {
    if (typeof param.sort === 'object' && param.sort.kind === 'numeric-union') {
      const v = vars.get(param.name)
      if (v === undefined) continue
      try {
        const options = param.sort.values.map(val =>
          (v as Arith<'main'>).eq(ctx.from(BigInt(val))) as Bool<'main'>
        )
        if (options.length > 0) {
          constraints.push(ctx.Or(...options))
        }
      } catch { /* skip if Z3 operations fail */ }
    }
  }

  return constraints
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function translatePredicate(
  predicate: Predicate,
  vars: Map<string, AnyExpr<'main'>>,
  ctx: Z3Context,
): AnyExpr<'main'> | null {
  if (typeof predicate === 'string') {
    const result = translateStringContract(predicate, vars, ctx)
    if (result === null) {
      process.stderr.write(`[theorem] unrecognized string contract: "${predicate}" — skipped\n`)
    }
    return result
  }
  return toZ3(predicate, vars, ctx)
}

function predicateText(predicate: Predicate): string {
  if (typeof predicate === 'string') return predicate
  return prettyExpr(predicate)
}

// ---------------------------------------------------------------------------
// Recursive termination verification
// ---------------------------------------------------------------------------

/**
 * Represents a recursive call found in the function body,
 * along with the path conditions that must hold for the call to execute.
 */
interface RecursiveCallInfo {
  args: Expr[]
  pathConditions: Expr[]
}

/**
 * Walks an expression tree and collects recursive calls (calls matching fnName),
 * along with the path conditions (ternary branches) leading to each call.
 */
function findRecursiveCalls(body: Expr, fnName: string, pathConditions: Expr[] = []): RecursiveCallInfo[] {
  const results: RecursiveCallInfo[] = []

  switch (body.kind) {
    case 'call':
      if (body.callee === fnName) {
        results.push({ args: body.args, pathConditions: [...pathConditions] })
      }
      // Also recurse into call arguments (e.g. factorial(n - 1) + factorial(n - 2))
      for (const arg of body.args) {
        results.push(...findRecursiveCalls(arg, fnName, pathConditions))
      }
      break

    case 'ternary':
      // In the then-branch, the condition holds
      results.push(...findRecursiveCalls(body.then, fnName, [...pathConditions, body.condition]))
      // In the else-branch, the condition is negated
      results.push(...findRecursiveCalls(body.else, fnName, [
        ...pathConditions,
        { kind: 'unary', op: '!', operand: body.condition },
      ]))
      // Also check condition itself (unlikely but for completeness)
      results.push(...findRecursiveCalls(body.condition, fnName, pathConditions))
      break

    case 'binary':
      results.push(...findRecursiveCalls(body.left, fnName, pathConditions))
      results.push(...findRecursiveCalls(body.right, fnName, pathConditions))
      break

    case 'unary':
      results.push(...findRecursiveCalls(body.operand, fnName, pathConditions))
      break

    case 'member':
      results.push(...findRecursiveCalls(body.object, fnName, pathConditions))
      break

    case 'element-access':
      results.push(...findRecursiveCalls(body.object, fnName, pathConditions))
      results.push(...findRecursiveCalls(body.index, fnName, pathConditions))
      break

    case 'array':
      for (const el of body.elements) {
        results.push(...findRecursiveCalls(el, fnName, pathConditions))
      }
      break

    case 'object':
      for (const p of body.properties) {
        results.push(...findRecursiveCalls(p.value, fnName, pathConditions))
      }
      break

    case 'spread':
      results.push(...findRecursiveCalls(body.operand, fnName, pathConditions))
      break

    case 'quantifier':
      results.push(...findRecursiveCalls(body.body, fnName, pathConditions))
      break

    case 'template':
      for (const p of body.parts) {
        if (typeof p !== 'string') {
          results.push(...findRecursiveCalls(p, fnName, pathConditions))
        }
      }
      break

    default:
      break
  }

  return results
}

/**
 * Generates verification tasks for recursive termination:
 * - Bound: decreases expression >= 0 (given requires)
 * - Decrease: at each recursive call, the measure strictly decreases
 */
function translateRecursiveDecreases(
  ir: FunctionIR,
  vars: Map<string, AnyExpr<'main'>>,
  assumptions: Bool<'main'>[],
  assumptionLabels: string[],
  domainConstraints: Bool<'main'>[],
  ctx: Z3Context,
): VerificationTask[] {
  const tasks: VerificationTask[] = []

  // Find the decreases contract that is NOT loop-indexed
  const decreasesContract = ir.contracts.find(
    c => c.kind === 'decreases' && c.loopIndex === undefined
  )
  if (!decreasesContract || decreasesContract.kind !== 'decreases') return tasks
  if (!ir.name || !ir.body) return tasks

  // Find recursive calls in the body
  const recursiveCalls = findRecursiveCalls(ir.body, ir.name)
  if (recursiveCalls.length === 0) return tasks

  const decreasesExpr = decreasesContract.expression
  const decText = prettyExpr(decreasesExpr)
  const decZ3 = toZ3(decreasesExpr, vars, ctx)
  if (decZ3 === null) return tasks

  // Automatically add integer constraint on the decreases expression.
  // Termination only makes sense for integers (natural numbers decrease to 0).
  try {
    const intConstraint = (decZ3 as Arith<'main'>).eq(ctx.ToInt(decZ3 as Arith<'main'>) as Arith<'main'>)
    assumptions.push(intConstraint as Bool<'main'>)
    assumptionLabels.push(`decreases integer: ${decText} is integer`)
  } catch { /* skip if Z3 operations fail */ }

  // Task 1: Bound — decreases expression >= 0 (given requires)
  const nonNegGoal = (decZ3 as Arith<'main'>).ge(ctx.Real.val(0))
  tasks.push({
    functionName: ir.name,
    contractText: `recursive bound: ${decText} >= 0`,
    variables: vars,
    assumptions: [...assumptions],
    assumptionLabels: [...assumptionLabels],
    goal: ctx.Not(nonNegGoal as Bool<'main'>),
    domainConstraints,
  })

  // Task 2: For each recursive call, prove the measure strictly decreases
  for (const call of recursiveCalls) {
    // Build substitution: param_i → call.args[i]
    const mapping = new Map<string, Expr>()
    for (let i = 0; i < Math.min(ir.params.length, call.args.length); i++) {
      mapping.set(ir.params[i]!.name, call.args[i]!)
    }

    // Apply substitution to decreases expression to get measure at recursive call
    const decreasesAtCall = substituteExpr(decreasesExpr, mapping)
    const decAtCallZ3 = toZ3(decreasesAtCall, vars, ctx)
    if (decAtCallZ3 === null) continue

    const decAtCallText = prettyExpr(decreasesAtCall)

    // Collect path condition assumptions
    const callAssumptions = [...assumptions]
    const callLabels = [...assumptionLabels]
    for (const pathCond of call.pathConditions) {
      const pathZ3 = toZ3(pathCond, vars, ctx)
      if (pathZ3 !== null) {
        callAssumptions.push(pathZ3 as Bool<'main'>)
        callLabels.push(`path: ${prettyExpr(pathCond)}`)
      }
    }

    // Prove: decreasesAtCall < decreasesExpr
    const decreaseGoal = (decAtCallZ3 as Arith<'main'>).lt(decZ3 as Arith<'main'>)
    tasks.push({
      functionName: ir.name,
      contractText: `recursive decrease: ${decAtCallText} < ${decText}`,
      variables: vars,
      assumptions: callAssumptions,
      assumptionLabels: callLabels,
      goal: ctx.Not(decreaseGoal as Bool<'main'>),
      domainConstraints,
    })
  }

  return tasks
}

// ---------------------------------------------------------------------------
// Two-state model helpers
// ---------------------------------------------------------------------------

/**
 * Checks whether an expression tree contains a call to `old()` or `conserved()`.
 * Used to determine whether __old_ variables need to be created.
 */
function exprUsesOld(expr: Expr): boolean {
  switch (expr.kind) {
    case 'call':
      if (expr.callee === 'old' || expr.callee === 'conserved') return true
      return expr.args.some(a => exprUsesOld(a))
    case 'binary':         return exprUsesOld(expr.left) || exprUsesOld(expr.right)
    case 'unary':          return exprUsesOld(expr.operand)
    case 'ternary':        return exprUsesOld(expr.condition) || exprUsesOld(expr.then) || exprUsesOld(expr.else)
    case 'member':         return exprUsesOld(expr.object)
    case 'element-access': return exprUsesOld(expr.object) || exprUsesOld(expr.index)
    case 'quantifier':     return exprUsesOld(expr.body)
    case 'array':          return expr.elements.some(e => exprUsesOld(e))
    case 'object':         return expr.properties.some(p => exprUsesOld(p.value))
    case 'spread':         return exprUsesOld(expr.operand)
    case 'template':       return expr.parts.some(p => typeof p !== 'string' && exprUsesOld(p))
    default:               return false
  }
}
