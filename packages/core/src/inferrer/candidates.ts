import type { Bool, AnyExpr } from 'z3-solver'
import type { FunctionIR } from '../parser/ir.js'
import type { Z3Context } from '../solver/context.js'
import type { InferredContract } from './index.js'
import { createVariables } from '../translator/variables.js'
import { toZ3 } from '../translator/expr.js'
import { check } from '../solver/index.js'

type Z3Bool = Bool<'main'>
type Z3Expr = AnyExpr<'main'>

/**
 * Verifies candidate contracts against the function body using Z3.
 * For each candidate, we attempt to prove that the negation of the candidate
 * is unsatisfiable (i.e., the candidate always holds).
 */
export async function verifyCandidates(
  candidates: InferredContract[],
  ir: FunctionIR,
  ctx: Z3Context,
  requires: InferredContract[],
): Promise<InferredContract[]> {
  if (candidates.length === 0) return []

  // Cap candidates at 15 for performance
  const cappedCandidates = candidates.length > 15 ? candidates.slice(0, 15) : candidates

  // 1. Create Z3 variables from function params and return sort
  const vars = createVariables(ir.params, ir.returnSort, ctx)

  // 2. Build assumptions
  const assumptions: Z3Bool[] = []
  const domainConstraints: Z3Bool[] = []

  // Body constraint: result === body(params)
  if (ir.body) {
    try {
      const bodyZ3 = toZ3(ir.body, vars, ctx)
      const result = vars.get('result')
      if (bodyZ3 && result) {
        const eq = (result as any).eq(bodyZ3) as Z3Bool
        assumptions.push(eq)
      }
    } catch {
      // Sort mismatch or translation failure — skip body constraint
    }
  }

  // Requires assumptions
  for (const req of requires) {
    try {
      const reqZ3 = toZ3(req.predicate, vars, ctx)
      if (reqZ3) {
        assumptions.push(reqZ3 as Z3Bool)
      }
    } catch {
      // Skip untranslatable requires
    }
  }

  // Domain constraints: .length >= 0
  for (const [name, expr] of vars) {
    if (name.endsWith('.length')) {
      try {
        domainConstraints.push((expr as any).ge(ctx.Real.val(0)) as Z3Bool)
      } catch {
        // Skip if not numeric
      }
    }
  }

  // 3. Verify each candidate
  const verified: InferredContract[] = []

  for (const candidate of cappedCandidates) {
    try {
      const candidateZ3 = toZ3(candidate.predicate, vars, ctx)
      if (!candidateZ3) continue

      const goal = ctx.Not(candidateZ3 as Z3Bool)

      const result = await check({
        variables: vars,
        assumptions,
        goal,
        domainConstraints,
        timeout: 500,
      })

      if (result.status === 'proved') {
        // UNSAT — the candidate holds for all inputs
        verified.push({ ...candidate, confidence: 'proven' })
      }
      // disproved or unknown — discard the candidate
    } catch {
      // Translation or solver failure — skip this candidate
    }
  }

  // 4. Redundancy filtering: remove weaker bounds when exact equality is proven
  return filterRedundant(verified)
}

/**
 * If an exact equality ensures(output() === expr) is proven, remove weaker
 * relational bounds (>= or <=) that involve the same variables.
 */
function filterRedundant(contracts: InferredContract[]): InferredContract[] {
  const equalities = contracts.filter(
    c => c.kind === 'ensures' && c.text.includes('==='),
  )

  if (equalities.length === 0) return contracts

  return contracts.filter(c => {
    if (c.kind !== 'ensures') return true
    if (c.text.includes('===')) return true

    // Check if this relational bound is implied by any proven equality
    for (const eq of equalities) {
      if (isWeakerBound(c.text, eq.text)) {
        return false // remove the weaker bound
      }
    }
    return true
  })
}

/**
 * Simple heuristic: a bound like `output() >= a` is weaker than
 * `output() === a + b` if the bound's variable appears in the equality
 * and the bound uses >= or <=.
 */
function isWeakerBound(boundText: string, equalityText: string): boolean {
  if (!boundText.includes('>=') && !boundText.includes('<=')) return false

  // Extract the non-output side of the bound
  const boundNormalized = boundText
    .replace(/output\(\)\s*(>=|<=)\s*/, '')
    .replace(/\s*(>=|<=)\s*output\(\)/, '')
    .trim()

  // Check if the equality references the same variables
  if (boundNormalized && equalityText.includes(boundNormalized)) {
    return true
  }

  return false
}
