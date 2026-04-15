import { readFileSync, statSync, readdirSync, watch } from 'node:fs'
import { resolve, join, relative } from 'node:path'
import {
  extractFromSource,
  extractDeclareContracts,
  prettyExpr,
  translate,
  getContext,
  check,
  printFileReport,
  verifyToSarif,
  buildRegistry,
  extractCallSiteObligations,
} from '@theoremts/core'
import type { FunctionReport, TaskResult, FunctionIR, VerificationTask, FileReport, ContractRegistry, ResolvedConfig } from '@theoremts/core'
import { resolveContractFiles } from '../contracts.js'

interface VerifyOptions {
  strict?: boolean
  debug?: boolean
  watch?: boolean
  format?: string
  timeout?: string
}

// ---------------------------------------------------------------------------
// ANSI helpers (duplicated from reporter to keep CLI self-contained)
// ---------------------------------------------------------------------------

const isTTY = process.stdout.isTTY
const dim    = isTTY ? '\x1b[2m'  : ''
const bold   = isTTY ? '\x1b[1m'  : ''
const cyan   = isTTY ? '\x1b[36m' : ''
const yellow = isTTY ? '\x1b[33m' : ''
const green  = isTTY ? '\x1b[32m' : ''
const red    = isTTY ? '\x1b[31m' : ''
const reset  = isTTY ? '\x1b[0m'  : ''

function debugLog(msg: string) {
  process.stdout.write(msg + '\n')
}

// ---------------------------------------------------------------------------
// File resolution
// ---------------------------------------------------------------------------

function resolveFiles(paths: string[], config: ResolvedConfig): string[] {
  const skipDirs = new Set(config.scan.skipDirs)
  const excludePatterns = config.exclude
  const files: string[] = []
  for (const p of paths) {
    collectFiles(resolve(p), files, skipDirs, excludePatterns)
  }
  // Deduplicate preserving order
  return [...new Set(files)]
}

function collectFiles(absPath: string, out: string[], skipDirs: Set<string>, excludePatterns: string[]): void {
  let stat
  try { stat = statSync(absPath) } catch { return }

  if (stat.isFile()) {
    if (isVerifiableFile(absPath, excludePatterns)) out.push(absPath)
    return
  }

  if (stat.isDirectory()) {
    for (const entry of readdirSync(absPath)) {
      if (skipDirs.has(entry)) continue
      collectFiles(join(absPath, entry), out, skipDirs, excludePatterns)
    }
  }
}

/** Accept .ts files, reject .d.ts and excluded patterns */
function isVerifiableFile(p: string, excludePatterns: string[]): boolean {
  if (!p.endsWith('.ts') || p.endsWith('.d.ts')) return false
  for (const pattern of excludePatterns) {
    if (matchesGlob(p, pattern)) return false
  }
  return true
}

/** Simple glob matching for common patterns like **\/*.test.ts */
function matchesGlob(filePath: string, pattern: string): boolean {
  // Handle **/*.ext patterns (most common case)
  if (pattern.startsWith('**/')) {
    const suffix = pattern.slice(3) // e.g. "*.test.ts"
    const fileName = filePath.split('/').pop() ?? filePath
    return matchesSimple(fileName, suffix)
  }
  // Handle *.ext patterns
  if (pattern.startsWith('*')) {
    const fileName = filePath.split('/').pop() ?? filePath
    return matchesSimple(fileName, pattern)
  }
  return filePath.includes(pattern)
}

function matchesSimple(name: string, pattern: string): boolean {
  // *.test.ts => name ends with .test.ts
  if (pattern.startsWith('*')) {
    return name.endsWith(pattern.slice(1))
  }
  return name === pattern
}

// ---------------------------------------------------------------------------
// Debug output per stage
// ---------------------------------------------------------------------------

function debugParser(irs: FunctionIR[]) {
  debugLog(`\n${bold}${cyan}── [parser]${reset}  found ${irs.length} function(s)`)
  for (const ir of irs) {
    const name = ir.name ?? '(anonymous)'
    const params = ir.params.map(p => `${p.name}: ${p.sort}`).join(', ')
    debugLog(`  ${bold}${name}${reset}(${params})`)

    if (ir.body !== undefined) {
      debugLog(`  ${dim}body:   ${prettyExpr(ir.body)}${reset}`)
    }

    for (const c of ir.contracts) {
      if (c.kind === 'requires' || c.kind === 'ensures') {
        const pred = typeof c.predicate === 'string'
          ? `"${c.predicate}"`
          : prettyExpr(c.predicate)
        debugLog(`  ${dim}${c.kind}:  ${pred}${reset}`)
      } else if (c.kind === 'modifies') {
        debugLog(`  ${dim}modifies: [${c.refs.join(', ')}]${reset}`)
      }
    }
  }
}

function debugTranslator(tasks: VerificationTask[]) {
  debugLog(`\n${bold}${cyan}── [translator]${reset}  ${tasks.length} verification task(s)`)
  for (const task of tasks) {
    debugLog(`  ${bold}${task.functionName ?? '?'}${reset}  ensures: ${yellow}${task.contractText}${reset}`)
    debugLog(`  ${dim}assumptions (${task.assumptions.length}):`)
    for (const a of task.assumptions) {
      debugLog(`    ${a.toString()}`)
    }
    debugLog(`  goal (negated ensures):`)
    debugLog(`    ${task.goal.toString()}${reset}`)
  }
}

function debugSolver(task: VerificationTask, result: { status: string; counterexample?: Record<string, unknown> }, ms: number) {
  const icon = result.status === 'proved' ? '✓' : result.status === 'disproved' ? '✗' : '?'
  debugLog(`\n${bold}${cyan}── [solver]${reset}  ${icon} ${result.status}  ${dim}(${ms}ms)${reset}`)
  if (result.status === 'disproved' && result.counterexample) {
    const ce = Object.entries(result.counterexample)
      .map(([k, v]) => `${k} = ${v}`)
      .join(', ')
    debugLog(`  ${dim}counterexample: ${ce}${reset}`)
  }
}

// ---------------------------------------------------------------------------
// Single file processing
// ---------------------------------------------------------------------------

async function verifyFile(
  absPath: string,
  displayPath: string,
  opts: VerifyOptions,
  config: ResolvedConfig,
  registry?: ContractRegistry,
): Promise<{ proved: number; failed: number; unknown: number; report: FileReport } | null> {
  let source: string
  try {
    source = readFileSync(absPath, 'utf-8')
  } catch {
    process.stderr.write(`Error: cannot read file "${displayPath}"\n`)
    return null
  }

  const irs = extractFromSource(source, absPath, registry)

  // Skip files with no contracts AND no registry (nothing to verify)
  if (irs.length === 0 && (!registry || registry.size === 0)) return null

  if (opts.debug && irs.length > 0) debugParser(irs)

  const ctx = await getContext()
  const functionResults: FunctionReport[] = []
  const startAll = Date.now()

  for (const ir of irs) {
    const tasks = translate(ir, ctx, registry)
    if (tasks.length === 0) continue

    if (opts.debug) debugTranslator(tasks)

    const taskResults: TaskResult[] = []

    for (const task of tasks) {
      const t0 = Date.now()
      const timeoutMs = opts.timeout ? Number(opts.timeout) : config.solver.timeout
      const result = await check({
        ...task,
        timeout: timeoutMs,
        maxCounterexamples: config.solver.maxCounterexamples,
        minimizeCounterexample: config.solver.minimizeCounterexamples,
      })
      const ms = Date.now() - t0

      if (opts.debug) debugSolver(task, result, ms)

      taskResults.push({ task, result, durationMs: ms })
    }

    functionResults.push({ name: ir.name, taskResults })
  }

  // Call-site verification: check calls to contracted functions outside proof()
  if (registry && registry.size > 0) {
    try {
      const callSiteTasks = extractCallSiteObligations(source, absPath, registry, ctx)
      if (callSiteTasks.length > 0) {
        const taskResults: TaskResult[] = []
        for (const task of callSiteTasks) {
          try {
            const t0 = Date.now()
            const timeoutMs = opts.timeout ? Number(opts.timeout) : config.solver.timeout
            const result = await check({ ...task, timeout: timeoutMs })
            const ms = Date.now() - t0
            taskResults.push({ task, result, durationMs: ms })
          } catch { /* skip tasks that cause Z3 errors */ }
        }
        if (taskResults.length > 0) {
          functionResults.push({ name: '(call-site checks)', taskResults })
        }
      }
    } catch { /* skip files that cause extraction errors */ }
  }

  if (functionResults.length === 0) return null

  if (opts.debug) {
    debugLog(`\n${bold}${cyan}── [reporter]${reset}`)
  }

  const report: FileReport = {
    filePath: displayPath,
    functionResults,
    totalMs: Date.now() - startAll,
  }

  if (opts.format !== 'sarif') {
    printFileReport(report)
  }

  const all = functionResults.flatMap(f => f.taskResults)
  return {
    proved:  all.filter(r => r.result.status === 'proved').length,
    failed:  all.filter(r => r.result.status === 'disproved').length,
    unknown: all.filter(r => r.result.status === 'unknown').length,
    report,
  }
}

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

async function runVerify(
  files: string[],
  cwd: string,
  opts: VerifyOptions,
  config: ResolvedConfig,
): Promise<{ totalFailed: number }> {
  // Pass 1: collect all IR to build cross-function registry
  const allIRs: FunctionIR[] = []
  for (const absPath of files) {
    try {
      const source = readFileSync(absPath, 'utf-8')
      allIRs.push(...extractFromSource(source, absPath))
    } catch { /* skip unreadable files */ }
  }

  // Load declare() contracts from .contracts.ts files
  const contractFiles = resolveContractFiles(config.contracts, cwd)
  for (const absPath of contractFiles) {
    try {
      const source = readFileSync(absPath, 'utf-8')
      allIRs.push(...extractDeclareContracts(source, absPath))
    } catch { /* skip unreadable contract files */ }
  }

  const registry = buildRegistry(allIRs)

  // Pass 2: verify each file with the registry
  let totalProved = 0
  let totalFailed = 0
  let totalUnknown = 0
  let filesWithContracts = 0
  const allReports: FileReport[] = []

  for (const absPath of files) {
    const displayPath = relative(cwd, absPath)
    const result = await verifyFile(absPath, displayPath, opts, config, registry)
    if (result !== null) {
      filesWithContracts++
      totalProved  += result.proved
      totalFailed  += result.failed
      totalUnknown += result.unknown
      allReports.push(result.report)
    }
  }

  // SARIF output
  if (opts.format === 'sarif') {
    process.stdout.write(verifyToSarif(allReports) + '\n')
    return { totalFailed }
  }

  // CLI output — multi-file grand total
  if (files.length > 1 && filesWithContracts > 0) {
    const parts: string[] = []
    if (totalProved  > 0) parts.push(`${green}${totalProved} proved${reset}`)
    if (totalFailed  > 0) parts.push(`${red}${totalFailed} failed${reset}`)
    if (totalUnknown > 0) parts.push(`${yellow}${totalUnknown} unknown${reset}`)
    process.stdout.write(`${bold}Total${reset}  ${parts.join(`  ${dim}·${reset}  `)}\n\n`)
  }

  if (filesWithContracts === 0) {
    if (registry.size > 0) {
      process.stdout.write(`${dim}No contract violations found in ${files.length === 1 ? files[0]! : `${files.length} files`} (${registry.size} contracts loaded).${reset}\n`)
    } else {
      process.stdout.write(`${dim}No contracts found. Run 'theorem infer' to generate contracts, or add requires()/ensures() to your code.${reset}\n`)
    }
  }

  return { totalFailed }
}

export async function verifyCommand(
  paths: string[],
  opts: VerifyOptions,
  config: ResolvedConfig,
): Promise<void> {
  // CLI --format flag takes precedence over config
  if (!opts.format) opts.format = config.reporter.format
  const cwd = process.cwd()
  const files = resolveFiles(paths, config)

  if (files.length === 0) {
    process.stderr.write(`No .ts files found in: ${paths.join(', ')}\n`)
    process.exit(1)
  }

  const { totalFailed } = await runVerify(files, cwd, opts, config)

  // ── Watch mode ─────────────────────────────────────────────────────────
  if (opts.watch) {
    process.stdout.write(`${dim}Watching for changes… (Ctrl+C to stop)${reset}\n`)

    let debounce: ReturnType<typeof setTimeout> | null = null
    const rerun = () => {
      if (debounce) clearTimeout(debounce)
      debounce = setTimeout(async () => {
        process.stdout.write('\x1Bc')  // clear terminal
        await runVerify(files, cwd, opts, config)
        process.stdout.write(`${dim}Watching for changes… (Ctrl+C to stop)${reset}\n`)
      }, 300)
    }

    for (const p of paths) {
      try {
        watch(resolve(p), { recursive: true }, (_, filename) => {
          if (filename?.endsWith('.ts') && !filename.endsWith('.d.ts')) rerun()
        })
      } catch { /* watch not supported — fall back to single run */ }
    }

    // Keep process alive
    await new Promise<void>(() => {})
  }

  if (opts.strict && totalFailed > 0) process.exit(1)
}
