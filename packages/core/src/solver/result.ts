export type ProvedResult = {
  status: 'proved'
  /** Which requires clauses were needed (from unsat core extraction). */
  usedAssumptions?: string[] | undefined
}

export type DisprovedResult = {
  status: 'disproved'
  counterexample: Record<string, unknown>
  /** Additional distinct counterexamples (when multiple are requested). */
  allCounterexamples?: Record<string, unknown>[] | undefined
  /** Intermediate expression values — shows the computation trace. */
  trace?: Record<string, unknown> | undefined
}

export type UnknownResult = {
  status: 'unknown'
  reason: string
}

export type SolverResult = ProvedResult | DisprovedResult | UnknownResult
