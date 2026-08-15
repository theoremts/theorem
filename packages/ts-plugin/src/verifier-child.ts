// Standalone verification child process.
//
// The Z3 WASM runtime (worker threads, large linear memory) must NEVER run
// inside the tsserver process — it starves the event loop and can crash the
// server. This script runs one verification in an isolated short-lived
// process: it reads { fileName, source, contractsDir } as JSON on stdin,
// writes { failures } as JSON on stdout, and exits.

const DIAG_CODE_DISPROVED = 100_001
const DIAG_CODE_UNKNOWN = 100_002
const DIAG_CODE_CALLSITE = 100_003

interface ChildFailure {
  message: string
  start: number
  length: number
  code: number
  severity: 'error' | 'warning'
}

async function main(): Promise<void> {
  const chunks: Buffer[] = []
  for await (const chunk of process.stdin) chunks.push(chunk as Buffer)
  const input = JSON.parse(Buffer.concat(chunks).toString('utf-8')) as {
    fileName: string
    source: string
    contractsDir?: string
  }
  const { fileName, source, contractsDir } = input

  const core = await import('@theoremts/core')
  const failures: ChildFailure[] = []
  const suppressions: Array<{ line: number; exprText: string }> = []
  const fixes: Array<{ start: number; length: number; title: string; insertPos: number; insertText: string }> = []
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const maybeOfferInvariantFix = (ir: any, span: { start: number; length: number }): Promise<void> =>
    maybeOfferInvariantFixImpl(core, ctx, source, fixes, ir, span)

  let irList: import('@theoremts/core').FunctionIR[]
  try {
    irList = core.extractFromSource(source, fileName)
  } catch {
    emit(failures, suppressions)
    return
  }

  // External contracts (.theorem/contracts/*.contracts.ts)
  const externalIRs: import('@theoremts/core').FunctionIR[] = []
  if (contractsDir) {
    try {
      const { readFileSync, statSync, readdirSync } = await import('fs')
      const { join } = await import('path')
      const walk = (dir: string): void => {
        for (const entry of readdirSync(dir)) {
          const p = join(dir, entry)
          try {
            const stat = statSync(p)
            if (stat.isFile() && p.endsWith('.contracts.ts')) {
              externalIRs.push(...core.extractDeclareContracts(readFileSync(p, 'utf-8'), p))
            } else if (stat.isDirectory()) {
              walk(p)
            }
          } catch { /* skip unreadable entries */ }
        }
      }
      walk(contractsDir)
    } catch { /* no contracts dir */ }

    // Auto-discovery, mirroring the CLI: contract packages in node_modules
    // (@theoremts/contracts-*, @theorem-contracts/*) and local *.contracts.ts
    // under src/ — the editor must see the same registry `theorem verify` does.
    try {
      const { readFileSync, statSync, readdirSync } = await import('fs')
      const { join, dirname } = await import('path')
      const projectRoot = dirname(dirname(contractsDir))  // <root>/.theorem/contracts
      const tryLoad = (p: string): void => {
        try {
          if (statSync(p).isFile()) externalIRs.push(...core.extractDeclareContracts(readFileSync(p, 'utf-8'), p))
        } catch { /* skip */ }
      }
      for (const scope of ['@theoremts', '@theorem-contracts']) {
        const scopeDir = join(projectRoot, 'node_modules', scope)
        try {
          for (const pkg of readdirSync(scopeDir)) {
            if (scope === '@theoremts' && !pkg.startsWith('contracts-')) continue
            tryLoad(join(scopeDir, pkg, 'index.contracts.ts'))
            tryLoad(join(scopeDir, pkg, 'theorem.contracts.ts'))
          }
        } catch { /* scope not installed */ }
      }
      const walkSrc = (dir: string, depth: number): void => {
        if (depth > 6) return
        for (const entry of readdirSync(dir)) {
          if (entry === 'node_modules' || entry.startsWith('.')) continue
          const p = join(dir, entry)
          try {
            const stat = statSync(p)
            if (stat.isFile() && p.endsWith('.contracts.ts')) tryLoad(p)
            else if (stat.isDirectory()) walkSrc(p, depth + 1)
          } catch { /* skip */ }
        }
      }
      try { walkSrc(join(projectRoot, 'src'), 0) } catch { /* no src dir */ }
    } catch { /* discovery is best-effort */ }
  }

  const registry = core.buildRegistry(irList)
  for (const [name, contract] of core.buildRegistry(externalIRs)) {
    if (!registry.has(name)) registry.set(name, contract)
  }

  if (irList.length === 0 && registry.size === 0) {
    emit(failures, suppressions)
    return
  }

  const ctx = await core.getContext()

  for (const ir of irList) {
    let tasks: import('@theoremts/core').VerificationTask[]
    try {
      tasks = await core.translateWithAutoInvariants(ir, ctx, registry, { boundsChecks: true })
    } catch {
      continue
    }

    for (const task of tasks) {
      // Bounds obligations: PROVED licenses suppressing tsc's
      // possibly-undefined at that access; anything else changes nothing
      // (tsc already warns there).
      const bounds = (task as { boundsCheck?: { line: number; exprText: string } }).boundsCheck
      if (bounds !== undefined) {
        try {
          const result = await core.check({ ...task, timeout: 5000 })
          if (result.status === 'proved') {
            suppressions.push({ line: bounds.line, exprText: bounds.exprText })
          }
        } catch { /* skip */ }
        continue
      }
      if (task.informational) continue  // dead-branch hints are CLI-only
      try {
        const result = await core.check({ ...task, timeout: 5000 })
        if (result.status === 'disproved') {
          const ceText = formatCounterexample(result.counterexample)
          const traceText = result.trace ? formatTrace(result.trace) : ''
          const span = findContractPosition(source, ir.name, task.contractText)
          // Spacer-inferred invariants become a one-click editor fix
          await maybeOfferInvariantFix(ir, span)
          // Labeled, multi-line: editors show the first line in the Problems
          // panel and the full text in the hover. The 'theorem' source tag
          // already identifies us — no prefix needed.
          const lines = [`Contract violated: ${task.contractText}`]
          if (ceText) lines.push(`Counterexample: ${ceText}`)
          if (traceText) lines.push(traceText)
          failures.push({
            message: lines.join('\n'),
            start: span.start,
            length: span.length,
            code: DIAG_CODE_DISPROVED,
            severity: 'error',
          })
        } else if (result.status === 'unknown') {
          const span = findContractPosition(source, ir.name, task.contractText)
          failures.push({
            message: `Could not prove: ${task.contractText}\nSolver gave up (${result.reason}) — the contract may still hold`,
            start: span.start,
            length: span.length,
            code: DIAG_CODE_UNKNOWN,
            severity: 'warning',
          })
        }
      } catch { /* skip tasks that error */ }
    }
  }

  // Call-site obligations
  try {
    const callSiteTasks = core.extractCallSiteObligations(source, fileName, registry, ctx)
    for (const task of callSiteTasks) {
      try {
        const result = await core.check({ ...task, timeout: 5000 })
        if (result.status === 'disproved') {
          const ceText = formatCounterexample(result.counterexample)
          const pos = (task as { sourcePos?: { start: number; length: number } }).sourcePos
          const cs = (task as { callSite?: { call: string; predicate: string } }).callSite
          const start = pos?.start ?? findCallSitePosition(source, task.functionName ?? '', task.contractText)
          const lines = cs !== undefined
            ? [`Unmet requires: ${cs.predicate}`, `Call: ${cs.call}`]
            : [`Unmet requires: ${task.contractText}`]
          if (ceText) lines.push(`Counterexample: ${ceText}`)
          failures.push({
            message: lines.join('\n'),
            start,
            length: pos?.length ?? estimateCallSiteSpanLength(source, start),
            code: DIAG_CODE_CALLSITE,
            severity: 'error',
          })
        }
      } catch { /* skip */ }
    }
  } catch { /* skip call-site extraction errors */ }

  emit(failures, suppressions, fixes)
}

function emit(
  failures: ChildFailure[],
  suppressions: Array<{ line: number; exprText: string }> = [],
  fixes: Array<{ start: number; length: number; title: string; insertPos: number; insertText: string }> = [],
): void {
  process.stdout.write(JSON.stringify({ failures, suppressions, fixes }))
}

// ---------------------------------------------------------------------------
// Source position helpers
// ---------------------------------------------------------------------------

/**
 * When a failing function has an uninvarianted loop and Spacer can infer
 * candidates, offer a code fix inserting them in the header position
 * (directly before the while — same semantics as inside the body).
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
async function maybeOfferInvariantFixImpl(
  core: any, ctx: any, source: string,
  fixes: Array<{ start: number; length: number; title: string; insertPos: number; insertText: string }>,
  ir: any, span: { start: number; length: number },
): Promise<void> {
  try {
    // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-call
    const hasBareLoop = ir.heapSteps?.some((st: { kind: string; invariants?: unknown[] }) =>
      st.kind === 'loop' && (st.invariants?.length ?? 0) === 0)
    if (hasBareLoop !== true || typeof ir.name !== 'string') return
    if (fixes.some(f => f.start === span.start)) return
    // eslint-disable-next-line @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
    const inferred = await core.inferLoopInvariants(ir, ctx)
    if (inferred === null || inferred.invariants.length === 0) return
    // Insertion point: the line of the first `while` after the function header
    const fnIdx = source.indexOf(`function ${ir.name}`)
    if (fnIdx === -1) return
    const whileIdx = source.indexOf('while', fnIdx)
    if (whileIdx === -1) return
    const lineStart = source.lastIndexOf('\n', whileIdx) + 1
    const indent = source.slice(lineStart, whileIdx).match(/^\s*/)?.[0] ?? '  '
    // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-unsafe-call
    const lines = (inferred.invariants as string[]).map((i: string) => `${indent}invariant(() => ${i})`)
    fixes.push({
      start: span.start,
      length: span.length,
      title: `Theorem: insert ${lines.length} inferred loop invariant(s)`,
      insertPos: lineStart,
      insertText: lines.join('\n') + '\n',
    })
  } catch { /* fix offers are best-effort */ }
}

function findContractPosition(
  source: string,
  fnName: string | undefined,
  contractText: string,
): { start: number; length: number } {
  const fnStart = findFunctionNamePosition(source, fnName)

  // Safety obligations carry the risky expression in their text — anchor the
  // diagnostic at that expression inside the function, not at the fn name.
  const safety = /^safe (?:division|modulo|sqrt|log): (.+?) (?:!==|>=|>) 0$/.exec(contractText)
  if (safety) {
    const exprText = safety[1]!.trim()
    const idx = source.indexOf(exprText, fnStart >= 0 ? fnStart : 0)
    if (idx >= 0) return { start: idx, length: exprText.length }
  }

  if (fnStart >= 0) return { start: fnStart, length: fnName?.length ?? 20 }
  return { start: 0, length: 20 }
}

function findFunctionNamePosition(source: string, fnName: string | undefined): number {
  if (!fnName) return -1

  const fnPattern = new RegExp(`function\\s+(${escapeRegex(fnName)})\\b`)
  const fnMatch = fnPattern.exec(source)
  if (fnMatch) return fnMatch.index + fnMatch[0].indexOf(fnName)

  const constPattern = new RegExp(`(?:const|let|var)\\s+(${escapeRegex(fnName)})\\b`)
  const constMatch = constPattern.exec(source)
  if (constMatch) return constMatch.index + constMatch[0].indexOf(fnName)

  const methodPattern = new RegExp(`\\b(${escapeRegex(fnName)})\\s*\\(`)
  const methodMatch = methodPattern.exec(source)
  if (methodMatch) return methodMatch.index

  return -1
}

function findCallSitePosition(
  source: string,
  functionName: string,
  contractText: string,
): number {
  const callee = functionName.replace(/^\(call-site\)\s*/, '')
  if (callee) {
    const callMatch = contractText.match(/^([^(]+)\(([^)]*)\)/)
    if (callMatch) {
      const argText = callMatch[2]!.trim()
      const exact = `${callee}(${argText})`
      const idx = source.indexOf(exact)
      if (idx >= 0) return idx
    }
    const pattern = new RegExp(`\\b${escapeRegex(callee)}\\s*\\(`)
    const match = pattern.exec(source)
    if (match) return match.index
  }
  return 0
}

function estimateCallSiteSpanLength(source: string, start: number): number {
  let depth = 0
  let i = start
  while (i < source.length) {
    if (source[i] === '(') depth++
    if (source[i] === ')') {
      depth--
      if (depth === 0) return i - start + 1
    }
    i++
  }
  return Math.min(30, source.length - start)
}

// ---------------------------------------------------------------------------
// Formatting helpers
// ---------------------------------------------------------------------------

function formatCounterexample(ce: Record<string, unknown>): string {
  const entries = Object.entries(ce)
    .filter(([k]) => !k.startsWith('__'))
    .map(([k, v]) => `${k} = ${v}`)
  return entries.length > 0 ? entries.join(', ') : ''
}

function formatTrace(trace: Record<string, unknown>): string {
  const entries = Object.entries(trace)
    .filter(([, v]) => v !== '?')
    .map(([k, v]) => `${k} = ${v}`)
  return entries.length > 0 ? `Initial state: ${entries.join(', ')}` : ''
}

function escapeRegex(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
}

main()
  .then(() => process.exit(0))
  .catch(err => {
    process.stderr.write(String(err))
    process.exit(1)
  })
