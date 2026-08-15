import type { Z3Context } from '../solver/context.js'
import type { Expr, FunctionIR } from '../parser/ir.js'
import type { ContractRegistry } from '../registry/index.js'
import type { TranslateOptions, VerificationTask } from '../translator/index.js'
import { translate } from '../translator/index.js'
import { check } from '../solver/index.js'
import { prettyExpr } from '../parser/pretty.js'

/**
 * Houdini-style automatic loop invariants: guess-and-check.
 *
 * Candidates are the requires/ensures conjuncts that mention state the loop
 * writes. Each candidate must PROVE loop entry and preservation; failures
 * are dropped and the check REITERATES (a surviving candidate may have
 * leaned on a dropped one — the classic fixpoint). Survivors are injected
 * as loop invariants, marked `(auto)` in the output.
 *
 * Soundness is free: nothing is assumed that didn't pass both obligations —
 * a debiting loop simply loses its candidate and refutes honestly.
 * Explicit invariant() always composes with (and is never displaced by)
 * the automatic ones.
 */
export async function translateWithAutoInvariants(
  ir: FunctionIR,
  ctx: Z3Context,
  registry?: ContractRegistry,
  opts?: TranslateOptions,
): Promise<VerificationTask[]> {
  const loops = (ir.heapSteps ?? []).filter(s => s.kind === 'loop')
  // v1: single top-level loop — multi-loop candidate attribution is ambiguous
  if (loops.length !== 1) return translate(ir, ctx, registry, opts)
  const loop = loops[0] as Extract<NonNullable<FunctionIR['heapSteps']>[number], { kind: 'loop' }>

  // ── Candidates ───────────────────────────────────────────────────────────
  const writtenNames = new Set<string>()
  const scan = (list: NonNullable<FunctionIR['heapSteps']>): void => {
    for (const s of list) {
      if (s.kind === 'num-assign') writtenNames.add(s.name)
      else if (s.kind === 'field-write') writtenNames.add(s.field)
      else if (s.kind === 'branch') { scan(s.then); scan(s.else) }
      else if (s.kind === 'loop') scan(s.body)
    }
  }
  scan(loop.body)

  const mentionsWritten = (e: Expr): boolean => {
    switch (e.kind) {
      case 'ident': return writtenNames.has(e.name)
      case 'member': return writtenNames.has(e.property) || mentionsWritten(e.object)
      case 'element-access': return mentionsWritten(e.object) || mentionsWritten(e.index)
      case 'binary': return mentionsWritten(e.left) || mentionsWritten(e.right)
      case 'unary': return mentionsWritten(e.operand)
      case 'ternary': return mentionsWritten(e.condition) || mentionsWritten(e.then) || mentionsWritten(e.else)
      case 'call': return e.args.some(mentionsWritten)
      case 'quantifier': return mentionsWritten(e.body)
      default: return false
    }
  }
  const mentionsOutput = (e: Expr): boolean => {
    switch (e.kind) {
      case 'call': return e.callee === 'output' || e.args.some(mentionsOutput)
      case 'binary': return mentionsOutput(e.left) || mentionsOutput(e.right)
      case 'unary': return mentionsOutput(e.operand)
      case 'ternary': return mentionsOutput(e.condition) || mentionsOutput(e.then) || mentionsOutput(e.else)
      case 'member': return mentionsOutput(e.object)
      case 'element-access': return mentionsOutput(e.object) || mentionsOutput(e.index)
      case 'quantifier': return mentionsOutput(e.body)
      default: return false
    }
  }
  const conjuncts = (e: Expr): Expr[] =>
    e.kind === 'binary' && e.op === '&&' ? [...conjuncts(e.left), ...conjuncts(e.right)] : [e]

  const explicitTexts = new Set(loop.invariants.map(prettyExpr))
  const seen = new Set<string>()
  const candidates: Expr[] = []
  for (const c of ir.contracts) {
    if ((c.kind !== 'requires' && c.kind !== 'ensures') || !('predicate' in c)) continue
    if (typeof c.predicate !== 'object' || c.predicate === null) continue
    for (const conj of conjuncts(c.predicate as Expr)) {
      if (mentionsOutput(conj) || !mentionsWritten(conj)) continue
      const text = prettyExpr(conj)
      if (explicitTexts.has(text) || seen.has(text)) continue
      seen.add(text)
      candidates.push(conj)
    }
  }
  if (candidates.length === 0) return translate(ir, ctx, registry, opts)

  // ── Guess-and-check fixpoint ─────────────────────────────────────────────
  const injected = (surviving: Expr[]): FunctionIR => {
    const steps = structuredClone(ir.heapSteps!)
    for (const s of steps) {
      if (s.kind === 'loop') s.invariants = [...s.invariants, ...structuredClone(surviving)]
    }
    return { ...ir, heapSteps: steps }
  }

  let surviving = candidates
  for (let round = 0; round < 5 && surviving.length > 0; round++) {
    const tasks = translate(injected(surviving), ctx, registry, opts)
    const failedTexts = new Set<string>()
    const survivingTexts = new Set(surviving.map(prettyExpr))
    for (const task of tasks) {
      const m = /^loop invariant \((?:entry|preserved)\): (.*)$/.exec(task.contractText)
      if (m === null || !survivingTexts.has(m[1]!)) continue
      try {
        const result = await check({ ...task, timeout: 3000 })
        if (result.status !== 'proved') failedTexts.add(m[1]!)
      } catch {
        failedTexts.add(m[1]!)
      }
    }
    if (failedTexts.size === 0) break
    surviving = surviving.filter(c => !failedTexts.has(prettyExpr(c)))
  }

  if (surviving.length === 0) return translate(ir, ctx, registry, opts)

  // ── Final translation with survivors, marked (auto) ──────────────────────
  const survivingTexts = new Set(surviving.map(prettyExpr))
  const tasks = translate(injected(surviving), ctx, registry, opts)
  for (const task of tasks) {
    const m = /^loop invariant \((?:entry|preserved)\): (.*)$/.exec(task.contractText)
    if (m !== null && survivingTexts.has(m[1]!)) {
      task.contractText = `${task.contractText}  (auto)`
    }
  }
  return tasks
}
