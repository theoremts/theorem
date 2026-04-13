import {
  extractFromSource,
  extractDeclareContracts,
  translate,
  getContext,
  check,
  buildRegistry,
  extractCallSiteObligations,
  resolveConfig,
} from '@theoremts/core'
import type {
  FunctionIR,
  ContractRegistry,
  Z3Context,
  ResolvedConfig,
  SolverResult,
} from '@theoremts/core'

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

export interface VerifyFailure {
  functionName: string
  contract: string
  counterexample: Record<string, unknown>
  allCounterexamples?: Record<string, unknown>[] | undefined
  trace?: Record<string, unknown> | undefined
}

export interface VerifyResult {
  proved: boolean
  provedCount: number
  failedCount: number
  failures: VerifyFailure[]
  durationMs: number
}

export interface VerifierOptions {
  /** Z3 solver timeout per obligation in ms (default: 10000) */
  timeout?: number
  /** Max counterexamples per failure (default: 3) */
  maxCounterexamples?: number
  /** Use Z3 Optimize to minimize counterexample values (default: false) */
  minimizeCounterexamples?: boolean
  /** Extra .contracts.ts source strings to load (declare() contracts for libraries) */
  contractSources?: string[]
}

// ---------------------------------------------------------------------------
// createVerifier
// ---------------------------------------------------------------------------

/**
 * Creates a reusable verifier instance.
 *
 * ```typescript
 * import { createVerifier } from 'theoremts-agent'
 *
 * const verifier = createVerifier()
 *
 * const result = await verifier.verify(`
 *   function divide(a: number, b: number) {
 *     requires(b !== 0)
 *     ensures(output() === a / b)
 *     return a / b
 *   }
 * `)
 *
 * if (!result.proved) {
 *   console.log(result.failures)
 *   // [{ functionName: 'divide', contract: '...', counterexample: { b: 0 } }]
 * }
 * ```
 */
export function createVerifier(options: VerifierOptions = {}) {
  const config = resolveConfig(null)

  // Apply user overrides
  if (options.timeout !== undefined) config.solver.timeout = options.timeout
  if (options.maxCounterexamples !== undefined) config.solver.maxCounterexamples = options.maxCounterexamples
  if (options.minimizeCounterexamples !== undefined) config.solver.minimizeCounterexamples = options.minimizeCounterexamples

  // Pre-parse contract sources (for library contracts like @theoremts/contracts-decimal)
  let externalIRs: FunctionIR[] | null = null
  function getExternalIRs(): FunctionIR[] {
    if (externalIRs === null) {
      externalIRs = []
      for (const src of options.contractSources ?? []) {
        externalIRs.push(...extractDeclareContracts(src, 'contracts.ts'))
      }
    }
    return externalIRs
  }

  return { verify, verifyMultiple }

  /**
   * Verify a single source string. All functions with contracts are verified.
   */
  async function verify(source: string, fileName = 'input.ts'): Promise<VerifyResult> {
    return verifyMultiple([{ source, fileName }])
  }

  /**
   * Verify multiple source files together (enables cross-function verification).
   */
  async function verifyMultiple(
    files: Array<{ source: string; fileName?: string }>,
  ): Promise<VerifyResult> {
    const t0 = Date.now()

    // Pass 1: parse all files and build cross-function registry
    const fileIRs: Array<{ fileName: string; irs: FunctionIR[] }> = []
    const allIRs: FunctionIR[] = [...getExternalIRs()]

    for (const { source, fileName = 'input.ts' } of files) {
      const irs = extractFromSource(source, fileName)
      fileIRs.push({ fileName, irs })
      allIRs.push(...irs)
    }

    const registry = buildRegistry(allIRs)
    const ctx = await getContext()

    // Pass 2: verify
    let provedCount = 0
    let failedCount = 0
    const failures: VerifyFailure[] = []

    for (const { fileName, irs } of fileIRs) {
      await verifyIRs(irs, ctx, registry, config, failures, (p, f) => {
        provedCount += p
        failedCount += f
      })

      // Call-site obligations
      const source = files.find(f => (f.fileName ?? 'input.ts') === fileName)!.source
      if (registry.size > 0) {
        const callSiteTasks = extractCallSiteObligations(source, fileName, registry, ctx)
        for (const task of callSiteTasks) {
          const result = await check({ ...task, timeout: config.solver.timeout })
          if (result.status === 'proved') {
            provedCount++
          } else if (result.status === 'disproved') {
            failedCount++
            failures.push({
              functionName: task.functionName ?? '(call-site)',
              contract: task.contractText,
              counterexample: result.counterexample,
              allCounterexamples: result.allCounterexamples,
              trace: result.trace,
            })
          }
        }
      }
    }

    return {
      proved: failedCount === 0 && provedCount > 0,
      provedCount,
      failedCount,
      failures,
      durationMs: Date.now() - t0,
    }
  }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

async function verifyIRs(
  irs: FunctionIR[],
  ctx: Z3Context,
  registry: ContractRegistry,
  config: ResolvedConfig,
  failures: VerifyFailure[],
  count: (proved: number, failed: number) => void,
): Promise<void> {
  for (const ir of irs) {
    const tasks = translate(ir, ctx, registry)

    for (const task of tasks) {
      const result = await check({
        ...task,
        timeout: config.solver.timeout,
        maxCounterexamples: config.solver.maxCounterexamples,
        minimizeCounterexample: config.solver.minimizeCounterexamples,
      })

      if (result.status === 'proved') {
        count(1, 0)
      } else if (result.status === 'disproved') {
        count(0, 1)
        failures.push({
          functionName: task.functionName ?? '(anonymous)',
          contract: task.contractText,
          counterexample: result.counterexample,
          allCounterexamples: result.allCounterexamples,
          trace: result.trace,
        })
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Standalone function (no verifier instance needed)
// ---------------------------------------------------------------------------

/**
 * One-shot verification. Creates a verifier, runs, returns.
 *
 * ```typescript
 * import { verify } from 'theoremts-agent'
 *
 * const result = await verify(`
 *   function abs(x: number) {
 *     ensures(output() >= 0)
 *     return x >= 0 ? x : -x
 *   }
 * `)
 * ```
 */
export async function verify(
  source: string,
  options?: VerifierOptions,
): Promise<VerifyResult> {
  return createVerifier(options).verify(source)
}

/**
 * Format failures as a concise feedback string for AI agents.
 *
 * ```typescript
 * const result = await verify(code)
 * if (!result.proved) {
 *   const feedback = formatFeedback(result)
 *   // "divide: contract `output() === a / b` fails when { b: 0 }"
 * }
 * ```
 */
export function formatFeedback(result: VerifyResult): string {
  if (result.proved) return 'All contracts proved.'

  return result.failures
    .map(f => {
      const ce = Object.entries(f.counterexample)
        .map(([k, v]) => `${k} = ${v}`)
        .join(', ')
      return `${f.functionName}: contract \`${f.contract}\` fails when { ${ce} }`
    })
    .join('\n')
}

// ---------------------------------------------------------------------------
// Audit — zero-annotation analysis for AI-generated code
// ---------------------------------------------------------------------------

export interface AuditRisk {
  kind: string
  level: string
  description: string
  line: number
  counterexample?: Record<string, unknown> | undefined
}

export interface AuditContract {
  kind: 'requires' | 'ensures'
  text: string
  confidence: string
  source: string
}

export interface AuditFunction {
  name: string
  contracts: AuditContract[]
}

export interface AuditResult {
  risks: AuditRisk[]
  inferredContracts: AuditFunction[]
  summary: string
  durationMs: number
}

export async function audit(source: string, options?: { timeout?: number }): Promise<AuditResult> {
  const t0 = Date.now()

  // Import dynamically to avoid circular or missing-subpath issues
  const { inferContracts } = await import('@theoremts/core/inferrer')
  const { scanSource } = await import('@theoremts/core/scanner')

  const ctx = await getContext()

  // Run scan and infer in sequence (both need Z3 context)
  const scanResult = await scanSource(source, 'input.ts', ctx)
  const inferResult = await inferContracts(source, 'input.ts')

  // Map scan risks
  const risks: AuditRisk[] = scanResult.functions.flatMap(f =>
    f.risks.map(r => ({
      kind: r.kind,
      level: r.level,
      description: r.description,
      line: r.line,
      counterexample: r.counterexample,
    }))
  )

  // Map inferred contracts
  const inferredContracts: AuditFunction[] = inferResult.functions.map(f => ({
    name: f.name,
    contracts: f.contracts.map(c => ({
      kind: c.kind,
      text: c.text,
      confidence: c.confidence,
      source: c.source,
    })),
  }))

  // Build summary
  const riskCount = risks.length
  const contractCount = inferredContracts.reduce((sum, f) => sum + f.contracts.length, 0)
  const funcCount = inferResult.functions.length

  const lines: string[] = []
  if (riskCount > 0) {
    lines.push(`${riskCount} risk${riskCount !== 1 ? 's' : ''} found:`)
    for (const r of risks) {
      const ce = r.counterexample ? ` (e.g., ${JSON.stringify(r.counterexample)})` : ''
      lines.push(`  - [${r.level}] ${r.description}${ce}`)
    }
  } else {
    lines.push('No risks found.')
  }

  if (contractCount > 0) {
    lines.push(`${contractCount} contract${contractCount !== 1 ? 's' : ''} inferred for ${funcCount} function${funcCount !== 1 ? 's' : ''}:`)
    for (const f of inferredContracts) {
      for (const c of f.contracts) {
        lines.push(`  - ${f.name}: ${c.kind}(${c.text}) [${c.confidence}]`)
      }
    }
  } else {
    lines.push('No contracts inferred.')
  }

  return {
    risks,
    inferredContracts,
    summary: lines.join('\n'),
    durationMs: Date.now() - t0,
  }
}
