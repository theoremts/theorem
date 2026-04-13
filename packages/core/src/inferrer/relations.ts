import type { Expr, FunctionIR } from '../parser/ir.js'
import type { Z3Context } from '../solver/context.js'
import type { InferredContract } from './index.js'
import { prettyExpr } from '../parser/pretty.js'

const outputCall: Expr = { kind: 'call', callee: 'output', args: [] }

function mkEnsures(predicate: Expr): InferredContract {
  return {
    kind: 'ensures',
    text: prettyExpr(predicate),
    predicate,
    confidence: 'derived',
    source: 'relational candidate',
  }
}

function exprEqual(a: Expr, b: Expr): boolean {
  return prettyExpr(a) === prettyExpr(b)
}

export async function extractRelations(
  ir: FunctionIR,
  ctx: Z3Context,
  requires: InferredContract[],
): Promise<InferredContract[]> {
  if (!ir.body) return []

  const isNumericReturn = ir.returnSort === 'real' || ir.returnSort === 'int'
  if (!isNumericReturn) return []

  const numericParams = ir.params.filter(
    p => p.sort === 'real' || p.sort === 'int',
  )

  // Cap parameters at 4 — too many params means O(n^2) candidates, too slow
  if (numericParams.length > 4) return []

  const candidates: InferredContract[] = []
  const seen = new Set<string>()
  const MAX_CANDIDATES = 10

  // Build set of existing requires texts for dedup
  const existingTexts = new Set(requires.map(r => r.text))

  function addCandidate(predicate: Expr): boolean {
    if (candidates.length >= MAX_CANDIDATES) return false
    const text = prettyExpr(predicate)
    if (seen.has(text)) return true
    if (existingTexts.has(text)) return true
    // Also check if any existing requires has the same predicate structure
    if (requires.some(r => exprEqual(r.predicate, predicate))) return true
    seen.add(text)
    candidates.push(mkEnsures(predicate))
    return candidates.length < MAX_CANDIDATES
  }

  // For all pairs of numeric params, generate relational candidates
  let capped = false
  for (let i = 0; i < numericParams.length && !capped; i++) {
    for (let j = i + 1; j < numericParams.length && !capped; j++) {
      const a = numericParams[i]!
      const b = numericParams[j]!
      const identA: Expr = { kind: 'ident', name: a.name }
      const identB: Expr = { kind: 'ident', name: b.name }

      // output() >= a
      if (!addCandidate({ kind: 'binary', op: '>=', left: outputCall, right: identA })) { capped = true; break }
      // output() <= a
      if (!addCandidate({ kind: 'binary', op: '<=', left: outputCall, right: identA })) { capped = true; break }
      // output() >= b
      if (!addCandidate({ kind: 'binary', op: '>=', left: outputCall, right: identB })) { capped = true; break }
      // output() <= b
      if (!addCandidate({ kind: 'binary', op: '<=', left: outputCall, right: identB })) { capped = true; break }
    }
  }

  // For single-param case: also generate relational candidates
  if (!capped && numericParams.length === 1) {
    const p = numericParams[0]!
    const ident: Expr = { kind: 'ident', name: p.name }
    addCandidate({ kind: 'binary', op: '>=', left: outputCall, right: ident })
    addCandidate({ kind: 'binary', op: '<=', left: outputCall, right: ident })
  }

  // Non-negativity candidate: always generate output() >= 0
  addCandidate({
    kind: 'binary',
    op: '>=',
    left: outputCall,
    right: { kind: 'literal', value: 0 },
  })

  return candidates
}
