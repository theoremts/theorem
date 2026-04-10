import { readFileSync, statSync, readdirSync } from 'node:fs'
import { resolve, join, relative } from 'node:path'
import { getContext, scanToSarif, extractFromSource, extractDeclareContracts, buildRegistry } from '@theorem/core'
import { scanSource } from '@theorem/core/scanner'
import type { ScanFileResult, RiskLevel } from '@theorem/core/scanner'
import type { ResolvedConfig } from '@theorem/core'
import { resolveContractFiles } from '../contracts.js'

interface ScanOptions {
  strict?: boolean
  format?: string
}

// ---------------------------------------------------------------------------
// ANSI
// ---------------------------------------------------------------------------

const isTTY = process.stdout.isTTY
const dim    = isTTY ? '\x1b[2m'  : ''
const bold   = isTTY ? '\x1b[1m'  : ''
const red    = isTTY ? '\x1b[31m' : ''
const yellow = isTTY ? '\x1b[33m' : ''
const reset  = isTTY ? '\x1b[0m'  : ''

const levelColor = (l: RiskLevel) =>
  l === 'critical' ? red : l === 'high' ? yellow : dim

const levelLabel = (l: RiskLevel) =>
  l === 'critical' ? 'CRITICAL' : l === 'high' ? 'HIGH' : 'LOW'

// ---------------------------------------------------------------------------
// File resolution
// ---------------------------------------------------------------------------

function resolveFiles(paths: string[], config: ResolvedConfig): string[] {
  const skipDirs = new Set(config.scan.skipDirs)
  const excludePatterns = config.exclude
  const files: string[] = []
  for (const p of paths) collectFiles(resolve(p), files, skipDirs, excludePatterns)
  return [...new Set(files)]
}

function collectFiles(absPath: string, out: string[], skipDirs: Set<string>, excludePatterns: string[]): void {
  let stat
  try { stat = statSync(absPath) } catch { return }
  if (stat.isFile()) {
    if (isIncludedFile(absPath, excludePatterns)) out.push(absPath)
    return
  }
  if (stat.isDirectory()) {
    for (const entry of readdirSync(absPath)) {
      if (skipDirs.has(entry)) continue
      collectFiles(join(absPath, entry), out, skipDirs, excludePatterns)
    }
  }
}

function isIncludedFile(p: string, excludePatterns: string[]): boolean {
  if (!p.endsWith('.ts') || p.endsWith('.d.ts')) return false
  for (const pattern of excludePatterns) {
    if (matchesGlob(p, pattern)) return false
  }
  return true
}

function matchesGlob(filePath: string, pattern: string): boolean {
  if (pattern.startsWith('**/')) {
    const suffix = pattern.slice(3)
    const fileName = filePath.split('/').pop() ?? filePath
    return matchesSimple(fileName, suffix)
  }
  if (pattern.startsWith('*')) {
    const fileName = filePath.split('/').pop() ?? filePath
    return matchesSimple(fileName, pattern)
  }
  return filePath.includes(pattern)
}

function matchesSimple(name: string, pattern: string): boolean {
  if (pattern.startsWith('*')) {
    return name.endsWith(pattern.slice(1))
  }
  return name === pattern
}

// ---------------------------------------------------------------------------
// Reporter
// ---------------------------------------------------------------------------

function printScanReport(report: ScanFileResult): void {
  const riskyFns = report.functions.filter(f => f.risks.length > 0)
  if (riskyFns.length === 0) return

  process.stdout.write(`\n${bold}${report.filePath}${reset}\n`)

  for (const fn of riskyFns) {
    const name = fn.name ?? '(anonymous)'
    process.stdout.write(`\n  ${bold}${name}${reset}\n`)

    for (const risk of fn.risks) {
      const col = levelColor(risk.level)
      const lbl = levelLabel(risk.level)
      process.stdout.write(`    ${col}${lbl}${reset}  ${risk.description}  ${dim}line ${risk.line}${reset}\n`)

      if (risk.counterexample) {
        const ce = Object.entries(risk.counterexample)
          .filter(([k]) => k !== 'result')
          .map(([k, v]) => `${k} = ${v}`)
          .join(', ')
        if (ce) process.stdout.write(`           ${dim}example: ${ce}${reset}\n`)
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

export async function scanCommand(paths: string[], opts: ScanOptions, config: ResolvedConfig): Promise<void> {
  // CLI --format flag takes precedence over config
  if (!opts.format) opts.format = config.reporter.format
  const cwd = process.cwd()
  const files = resolveFiles(paths, config)

  if (files.length === 0) {
    process.stderr.write(`No .ts files found in: ${paths.join(', ')}\n`)
    process.exit(1)
  }

  // Build registry from all proof() functions for contract violation detection
  const allIRs = []
  for (const f of files) {
    try { allIRs.push(...extractFromSource(readFileSync(f, 'utf-8'), f)) } catch {}
  }

  // Load declare() contracts from .contracts.ts files
  const contractFiles = resolveContractFiles(config.contracts, cwd)
  for (const absPath of contractFiles) {
    try { allIRs.push(...extractDeclareContracts(readFileSync(absPath, 'utf-8'), absPath)) } catch {}
  }

  const registry = buildRegistry(allIRs)

  const ctx = await getContext()

  let totalRisks = 0
  let filesWithRisks = 0
  const allReports: ScanFileResult[] = []

  for (const absPath of files) {
    const displayPath = relative(cwd, absPath)
    let source: string
    try { source = readFileSync(absPath, 'utf-8') } catch { continue }

    const report = await scanSource(source, absPath, ctx, registry)
    const displayReport = { ...report, filePath: displayPath }
    allReports.push(displayReport)

    if (opts.format !== 'sarif') printScanReport(displayReport)

    const risks = report.functions.reduce((n, f) => n + f.risks.length, 0)
    if (risks > 0) {
      filesWithRisks++
      totalRisks += risks
    }
  }

  if (opts.format === 'sarif') {
    process.stdout.write(scanToSarif(allReports) + '\n')
  } else if (totalRisks === 0) {
    process.stdout.write(`\n${dim}No risks found in ${files.length} file${files.length !== 1 ? 's' : ''}.${reset}\n\n`)
  } else {
    const summary = files.length > 1
      ? `  ${red}${totalRisks} risk${totalRisks !== 1 ? 's' : ''}${reset} in ${filesWithRisks} file${filesWithRisks !== 1 ? 's' : ''}\n\n`
      : `\n`
    process.stdout.write(summary)
  }

  if (opts.strict && totalRisks > 0) process.exit(1)
}
