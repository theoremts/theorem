import { readFileSync, writeFileSync, mkdirSync, existsSync, statSync, readdirSync } from 'node:fs'
import { resolve, join, relative, dirname, basename } from 'node:path'
import { inferContracts, generateDeclareFile, generateReport } from '@theoremts/core/inferrer'
import type { InferResult, Confidence } from '@theoremts/core/inferrer'
import { extractDeclareContracts, buildRegistry, type ResolvedConfig } from '@theoremts/core'
import { resolveContractFiles } from '../contracts.js'

interface InferOptions {
  output?: string
  dryRun?: boolean
  confidence?: string
  strict?: boolean
  prove?: boolean
}

// ---------------------------------------------------------------------------
// File resolution (same logic as verify.ts)
// ---------------------------------------------------------------------------

function resolveFiles(paths: string[], config: ResolvedConfig): string[] {
  const skipDirs = new Set(config.scan.skipDirs)
  const excludePatterns = config.exclude
  const files: string[] = []
  for (const p of paths) {
    collectFiles(resolve(p), files, skipDirs, excludePatterns)
  }
  return [...new Set(files)]
}

function collectFiles(absPath: string, out: string[], skipDirs: Set<string>, excludePatterns: string[]): void {
  let stat
  try { stat = statSync(absPath) } catch { return }

  if (stat.isFile()) {
    if (isAnalyzableFile(absPath, excludePatterns)) out.push(absPath)
    return
  }

  if (stat.isDirectory()) {
    for (const entry of readdirSync(absPath)) {
      if (skipDirs.has(entry)) continue
      collectFiles(join(absPath, entry), out, skipDirs, excludePatterns)
    }
  }
}

function isAnalyzableFile(p: string, excludePatterns: string[]): boolean {
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
    if (suffix.startsWith('*')) {
      return fileName.endsWith(suffix.slice(1))
    }
    return fileName === suffix
  }
  return filePath.includes(pattern)
}

// ---------------------------------------------------------------------------
// Confidence parsing
// ---------------------------------------------------------------------------

const VALID_CONFIDENCE: Confidence[] = ['proven', 'guard', 'derived', 'propagated', 'heuristic']

function parseConfidence(s: string): Confidence {
  const lower = s.toLowerCase() as Confidence
  if (VALID_CONFIDENCE.includes(lower)) return lower
  console.error(`Invalid confidence level: ${s}. Valid levels: ${VALID_CONFIDENCE.join(', ')}`)
  process.exit(1)
}

// ---------------------------------------------------------------------------
// ANSI helpers
// ---------------------------------------------------------------------------

const isTTY = process.stdout.isTTY
const green = isTTY ? '\x1b[32m' : ''
const dim   = isTTY ? '\x1b[2m'  : ''
const reset = isTTY ? '\x1b[0m'  : ''

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

export async function inferCommand(paths: string[], opts: InferOptions, config: ResolvedConfig): Promise<void> {
  const files = resolveFiles(paths, config)

  if (files.length === 0) {
    console.log('No TypeScript files found.')
    return
  }

  const minConfidence = opts.confidence ? parseConfidence(opts.confidence) : undefined
  const cwd = process.cwd()

  // Load external contracts from @theoremts/contracts-* packages
  const contractFiles = resolveContractFiles(config.contracts, cwd)
  const contractIRs = contractFiles.flatMap(absPath => {
    try {
      return extractDeclareContracts(readFileSync(absPath, 'utf-8'), absPath)
    } catch { return [] }
  })
  const registry = buildRegistry(contractIRs)

  if (registry.size > 0) {
    console.log(`${dim}Loaded ${registry.size} external contracts${reset}`)
  }

  // Collect results per file (for per-file output) and merged
  const perFile: Array<{ file: string; result: InferResult }> = []

  for (const absPath of files) {
    const source = readFileSync(absPath, 'utf-8')
    const result = await inferContracts(source, absPath, { prove: opts.prove, registry })
    perFile.push({ file: absPath, result })
  }

  // Merge all results
  const merged: InferResult = {
    functions: perFile.flatMap(pf => pf.result.functions),
    durationMs: perFile.reduce((sum, pf) => sum + pf.result.durationMs, 0),
  }

  // Print report
  console.log(generateReport(merged))

  // Write output files
  if (!opts.dryRun) {
    if (opts.output) {
      // Single output file for all results
      const displayPath = relative(process.cwd(), opts.output)
      const content = generateDeclareFile(merged, {
        sourceFile: files.map(f => relative(process.cwd(), f)).join(', '),
        ...(minConfidence ? { minConfidence } : {}),
      })
      writeFileSync(resolve(opts.output), content, 'utf-8')
      console.log(`\n${green}Wrote contracts to${reset} ${displayPath}`)
    } else {
      // Per-file output into .theorem/contracts/
      const projectRoot = process.cwd()
      const contractsDir = join(projectRoot, '.theorem', 'contracts')
      let writtenCount = 0

      for (const { file, result } of perFile) {
        if (result.functions.length === 0) continue
        const relPath = relative(projectRoot, file)
        const base = basename(relPath, '.ts')
        const relDir = dirname(relPath)
        const outDir = join(contractsDir, relDir)
        mkdirSync(outDir, { recursive: true })
        const outPath = join(outDir, `${base}.contracts.ts`)
        const content = generateDeclareFile(result, {
          sourceFile: relPath,
          ...(minConfidence ? { minConfidence } : {}),
        })
        writeFileSync(outPath, content, 'utf-8')
        writtenCount++
      }

      // Ensure .theorem/.gitignore exists
      const gitignorePath = join(projectRoot, '.theorem', '.gitignore')
      if (!existsSync(gitignorePath)) {
        mkdirSync(join(projectRoot, '.theorem'), { recursive: true })
        writeFileSync(gitignorePath, '# Auto-generated by theorem infer\n*\n', 'utf-8')
      }

      if (writtenCount > 0) {
        console.log(`\n${green}Wrote ${writtenCount} contract file${writtenCount === 1 ? '' : 's'} to${reset} .theorem/contracts/`)
      }
    }
  } else {
    console.log(`\n${dim}(dry run — no files written)${reset}`)
  }

  // Strict mode: exit 1 if any function has zero inferred contracts
  if (opts.strict) {
    // Check if any input file had functions but none got contracts
    const functionsWithContracts = new Set(merged.functions.map(f => f.name))
    // We consider it a failure if merged has zero contracts overall
    if (merged.functions.length === 0 && files.length > 0) {
      console.error('\nStrict mode: no contracts were inferred.')
      process.exit(1)
    }
  }
}
