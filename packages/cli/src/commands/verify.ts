import { readFileSync, statSync, readdirSync, watch, writeFileSync, unlinkSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { spawnSync } from 'node:child_process'
import { resolve, join, relative } from 'node:path'
import {
  extractFromSource,
  resolveImportedFiles,
  extractDeclareContracts,
  prettyExpr,
  translate,
  getContext,
  check,
  printFileReport,
  verifyToSarif,
  buildRegistry,
  extractCallSiteObligations,
  translateWithAutoInvariants,
} from '@theoremts/core'
import type { FunctionReport, TaskResult, FunctionIR, VerificationTask, FileReport, ContractRegistry, ResolvedConfig } from '@theoremts/core'
import { generateRegressionTests, type RegressionEntry } from '../gen-tests.js'
import { resolveContractFiles } from '../contracts.js'

interface VerifyOptions {
  strict?: boolean
  debug?: boolean
  watch?: boolean
  format?: string
  timeout?: string
  genTests?: boolean
  testsDir?: string
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
    // Houdini: uninvarianted loops get requires/ensures conjuncts as
    // guess-and-check invariant candidates — survivors show as (auto)
    // Translation failures are isolated PER FUNCTION: one untranslatable
    // shape must never take down the file (or, sharded, five sibling files).
    let tasks: VerificationTask[]
    try {
      tasks = await translateWithAutoInvariants(ir, ctx, registry)
    } catch (err) {
      process.stderr.write(`${dim}skipped ${ir.name ?? '(anonymous)'} in ${displayPath}: ${err instanceof Error ? err.message : String(err)}${reset}\n`)
      continue
    }
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

      // Informational tasks (e.g. "unreachable error branch"): a reachable
      // error branch is normal — only proved dead branches are worth showing.
      if (task.informational && result.status !== 'proved') continue

      // Counterexample → regression test material. Heap-mode tasks carry the
      // initial field values in the trace — merged in so the object graph is
      // reconstructible (roots sharing a ref = the same object).
      if (opts.genTests && result.status === 'disproved' && ir.name !== undefined) {
        regressionEntries.push({
          sourcePath: absPath,
          functionName: ir.name,
          params: ir.params.map(p => p.name),
          contractText: task.contractText,
          counterexample: { ...(result.trace ?? {}), ...(result.counterexample ?? {}) },
        })
      }

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

// Accumulated across files within one runVerify pass
let regressionEntries: RegressionEntry[] = []

async function runVerify(
  files: string[],
  cwd: string,
  opts: VerifyOptions,
  config: ResolvedConfig,
): Promise<{ totalFailed: number }> {
  regressionEntries = []
  // Pass 1: collect all IR to build cross-function registry
  const allIRs: FunctionIR[] = []
  for (const absPath of files) {
    try {
      const source = readFileSync(absPath, 'utf-8')
      allIRs.push(...extractFromSource(source, absPath))
    } catch { /* skip unreadable files */ }
  }

  // One-hop import expansion for SMALL runs: contracts of directly imported
  // files join the registry (never the verify set), so a single-file verify
  // sees its callees' requires/ensures instead of treating cross-file calls
  // as unknown. Large runs skip this — the sharded path already builds the
  // registry from the whole project.
  if (files.length <= 12) {
    const known = new Set(files)
    for (const absPath of files) {
      try {
        const source = readFileSync(absPath, 'utf-8')
        for (const dep of resolveImportedFiles(source, absPath)) {
          if (known.has(dep)) continue
          known.add(dep)
          try {
            allIRs.push(...extractFromSource(readFileSync(dep, 'utf-8'), dep))
          } catch { /* unreadable import — skip */ }
        }
      } catch { /* skip */ }
    }
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

  // ── Sharding ──────────────────────────────────────────────────────────────
  // The Z3 WASM heap degrades past ~15-20 files in one process. Above the
  // threshold the parent becomes an ORCHESTRATOR: the registry above — built
  // from ALL files, so cross-file call-site checks see the whole project —
  // is serialized and handed to child processes that each verify one chunk.
  const isShardChild = process.env['THEOREM_SHARD_CHILD'] === '1'
  const SHARD_THRESHOLD = 12
  const SHARD_SIZE = 6

  if (isShardChild && process.env['THEOREM_REGISTRY_FILE'] !== undefined) {
    try {
      const entries = JSON.parse(readFileSync(process.env['THEOREM_REGISTRY_FILE'], 'utf-8')) as Array<[string, Parameters<ContractRegistry['set']>[1]]>
      for (const [name, contract] of entries) {
        if (!registry.has(name)) registry.set(name, contract)
      }
    } catch { /* registry handoff is best-effort */ }
  }

  if (!isShardChild && files.length > SHARD_THRESHOLD && opts.format !== 'sarif' && !opts.watch) {
    // Pre-filter: only files that can produce verification tasks reach the
    // solver — ones carrying contracts/schema parses, or mentioning a
    // registered function (call-site obligations). On a 2k-file app this
    // collapses hundreds of Z3 boot-ups into a handful.
    const CONTRACT_RE = /requires\(|ensures\(|invariant\(|declare\(|proof\.|proof\(|\.parse\(|decodeUnknownSync|decodeSync|@invariant/
    const hintNames = [...registry.keys()].filter(k => !k.includes('.prototype.') && !k.startsWith('new '))
    const nameRe = hintNames.length > 0
      ? new RegExp(`\\b(${hintNames.map(n => n.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|')})\\b`)
      : null
    const relevant = files.filter(f => {
      try {
        const src = readFileSync(f, 'utf-8')
        return CONTRACT_RE.test(src) || (nameRe !== null && nameRe.test(src))
      } catch { return false }
    })
    process.stdout.write(`${dim}${files.length} files scanned → ${relevant.length} with contracts or registered calls${reset}\n`)
    if (relevant.length === 0) {
      process.stdout.write(`${dim}No contracts found. Add requires()/ensures(), or run 'theorem infer'.${reset}\n`)
      return { totalFailed: 0 }
    }
    if (relevant.length > SHARD_THRESHOLD) {
      return runSharded(relevant, cwd, opts, registry)
    }
    // Few enough to verify in-process with the global registry
    files = relevant
  }

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

  // Shard children report machine-readable totals and stay quiet otherwise —
  // the orchestrator prints the single grand total for the whole project.
  if (isShardChild) {
    const totalsFile = process.env['THEOREM_TOTALS_FILE']
    if (totalsFile !== undefined) {
      try {
        writeFileSync(totalsFile, JSON.stringify({ proved: totalProved, failed: totalFailed, unknown: totalUnknown, filesWithContracts }))
      } catch { /* parent falls back to zero */ }
    }
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

  // Counterexample → executable regression tests
  if (opts.genTests) {
    const outDir = opts.testsDir ?? '.theorem/regressions'
    const gen = generateRegressionTests(regressionEntries, outDir)
    if (gen.tests > 0) {
      process.stdout.write(`${bold}Generated ${gen.tests} regression test(s)${reset} in ${gen.files.length} file(s):\n`)
      for (const f of gen.files) process.stdout.write(`${dim}  ${f}${reset}\n`)
      process.stdout.write(`${dim}  These tests are RED until the bugs are fixed — run with:\n  node --experimental-strip-types --test <file>${reset}\n\n`)
    }
    if (gen.skipped > 0) {
      process.stdout.write(`${dim}(${gen.skipped} counterexample(s) not test-generable: two-state/quantified contracts or unreconstructible inputs)${reset}\n\n`)
    }
  }

  return { totalFailed }
}

/**
 * Whole-project verification: the global registry (built from every file, so
 * cross-file call-site checks span the project) is serialized to disk and
 * chunks of files are verified in CHILD processes — each gets a fresh Z3 WASM
 * heap, which degrades past ~15-20 files in a single process. Children stream
 * their per-file output directly; the parent prints one grand total.
 */
function runSharded(
  files: string[],
  cwd: string,
  opts: VerifyOptions,
  registry: ContractRegistry,
): { totalFailed: number } {
  const SHARD_SIZE = 6
  const regFile = join(tmpdir(), `theorem-registry-${process.pid}.json`)
  writeFileSync(regFile, JSON.stringify([...registry.entries()]))

  let proved = 0
  let failed = 0
  let unknown = 0
  let filesWithContracts = 0
  const shards = Math.ceil(files.length / SHARD_SIZE)
  process.stdout.write(`${dim}Verifying ${files.length} files in ${shards} shards (registry: ${registry.size} contracts)…${reset}\n\n`)

  for (let i = 0; i < files.length; i += SHARD_SIZE) {
    const chunk = files.slice(i, i + SHARD_SIZE)
    const totalsFile = join(tmpdir(), `theorem-totals-${process.pid}-${i}.json`)
    const args = [process.argv[1]!, 'verify', ...chunk]
    if (opts.debug) args.push('--debug')
    if (opts.timeout !== undefined) args.push('--timeout', opts.timeout)
    if (opts.genTests) args.push('--gen-tests')
    if (opts.testsDir !== undefined) args.push('--tests-dir', opts.testsDir)

    const res = spawnSync(process.execPath, args, {
      cwd,
      stdio: ['ignore', 'inherit', 'inherit'],
      env: {
        ...process.env,
        THEOREM_SHARD_CHILD: '1',
        THEOREM_REGISTRY_FILE: regFile,
        THEOREM_TOTALS_FILE: totalsFile,
      },
    })
    // A healthy child ALWAYS writes its totals file — a missing one means the
    // child died mid-run (uncaught error exits 1, indistinguishable from
    // --strict failures by status alone). Recover by re-running the shard's
    // files ONE BY ONE so a single bad file costs itself, not its siblings.
    let gotTotals = false
    try {
      const t = JSON.parse(readFileSync(totalsFile, 'utf-8')) as { proved: number; failed: number; unknown: number; filesWithContracts: number }
      proved += t.proved
      failed += t.failed
      unknown += t.unknown
      filesWithContracts += t.filesWithContracts
      unlinkSync(totalsFile)
      gotTotals = true
    } catch { /* shard produced no totals */ }

    if (!gotTotals || res.error !== undefined) {
      process.stderr.write(`${red}shard ${i / SHARD_SIZE + 1}/${shards} died${reset} (${res.error?.message ?? `exit ${res.status}`}) — retrying its files individually\n`)
      for (const file of chunk) {
        const soloTotals = join(tmpdir(), `theorem-totals-${process.pid}-${i}-${chunk.indexOf(file)}.json`)
        const soloArgs = [process.argv[1]!, 'verify', file]
        if (opts.debug) soloArgs.push('--debug')
        if (opts.timeout !== undefined) soloArgs.push('--timeout', opts.timeout)
        const solo = spawnSync(process.execPath, soloArgs, {
          cwd,
          stdio: ['ignore', 'inherit', 'inherit'],
          env: { ...process.env, THEOREM_SHARD_CHILD: '1', THEOREM_REGISTRY_FILE: regFile, THEOREM_TOTALS_FILE: soloTotals },
        })
        try {
          const t = JSON.parse(readFileSync(soloTotals, 'utf-8')) as { proved: number; failed: number; unknown: number; filesWithContracts: number }
          proved += t.proved
          failed += t.failed
          unknown += t.unknown
          filesWithContracts += t.filesWithContracts
          unlinkSync(soloTotals)
        } catch {
          process.stderr.write(`${red}  ${relative(cwd, file)} could not be verified${reset} (${solo.error?.message ?? `exit ${solo.status}`})\n`)
        }
      }
    }
  }
  try { unlinkSync(regFile) } catch { /* already gone */ }

  if (filesWithContracts > 0) {
    const parts: string[] = []
    if (proved  > 0) parts.push(`${green}${proved} proved${reset}`)
    if (failed  > 0) parts.push(`${red}${failed} failed${reset}`)
    if (unknown > 0) parts.push(`${yellow}${unknown} unknown${reset}`)
    process.stdout.write(`${bold}Total${reset}  ${parts.join(`  ${dim}·${reset}  `)}  ${dim}(${filesWithContracts} files with contracts of ${files.length} scanned)${reset}\n\n`)
  } else {
    process.stdout.write(`${dim}No contracts found in ${files.length} files. Add requires()/ensures(), or run 'theorem infer'.${reset}\n`)
  }

  return { totalFailed: failed }
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
