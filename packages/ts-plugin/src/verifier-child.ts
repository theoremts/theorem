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
      tasks = core.translate(ir, ctx, registry, { boundsChecks: true })
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

  emit(failures, suppressions)
}

function emit(failures: ChildFailure[], suppressions: Array<{ line: number; exprText: string }> = []): void {
  process.stdout.write(JSON.stringify({ failures, suppressions }))
}

// ---------------------------------------------------------------------------
// Source position helpers
// ---------------------------------------------------------------------------

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
