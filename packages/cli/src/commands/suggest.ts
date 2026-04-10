import { readFileSync, statSync, readdirSync } from 'node:fs'
import { resolve, join, relative } from 'node:path'
import { extractFunctionsFromSource, getContext } from '@theoremts/core'
import { suggestContracts } from '@theoremts/core/suggester'
import type { SuggestFunctionResult, ConditionalSuggestion, GuardSuggestion } from '@theoremts/core/suggester'
import type { ResolvedConfig } from '@theoremts/core'

// ---------------------------------------------------------------------------
// ANSI
// ---------------------------------------------------------------------------

const isTTY = process.stdout.isTTY
const dim    = isTTY ? '\x1b[2m'  : ''
const bold   = isTTY ? '\x1b[1m'  : ''
const green  = isTTY ? '\x1b[32m' : ''
const yellow = isTTY ? '\x1b[33m' : ''
const cyan   = isTTY ? '\x1b[36m' : ''
const reset  = isTTY ? '\x1b[0m'  : ''

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

const blue = isTTY ? '\x1b[34m' : ''

function printSuggestions(filePath: string, results: SuggestFunctionResult[]): void {
  const withContent = results.filter(r => r.suggestions.length > 0 || r.conditionals.length > 0 || r.guards.length > 0)
  if (withContent.length === 0) return

  process.stdout.write(`\n${bold}${filePath}${reset}\n`)

  for (const fn of withContent) {
    const name = fn.name ?? '(anonymous)'
    const params = fn.params.join(', ')
    process.stdout.write(`\n  ${bold}${name}${reset}(${dim}${params}${reset})\n`)

    for (const s of fn.suggestions) {
      const icon = s.status === 'provable' ? `${green}✓${reset}` : `${yellow}?${reset}`
      const kindLabel = s.kind === 'requires' ? `${cyan}requires${reset}` : `${cyan}ensures${reset}`

      if (s.status === 'provable') {
        const desc = s.description ? ` — ${s.description}` : ' — always holds'
        process.stdout.write(`    ${icon}  ${kindLabel}(${s.text})  ${dim}${desc}${reset}\n`)
      } else {
        const desc = s.description ? ` — ${s.description}` : ' — recommended'
        process.stdout.write(`    ${icon}  ${kindLabel}(${s.text})  ${dim}${desc}${reset}\n`)
        if (s.counterexample) {
          const ce = Object.entries(s.counterexample)
            .filter(([k]) => k !== 'result')
            .map(([k, v]) => `${k} = ${v}`)
            .join(', ')
          if (ce) {
            process.stdout.write(`       ${dim}without it: ${ce}${reset}\n`)
          }
        }
      }
    }

    // Guard suggestions: existing if/throw patterns
    for (const g of fn.guards) {
      process.stdout.write(`    ${blue}i${reset}  ${dim}existing guard detected:${reset} \`if (${g.condition}) ${g.action}\` ${dim}→ equivalent to${reset} ${cyan}requires${reset}(${g.equivalent})\n`)
    }

    // Conditional suggestions: "if you add X, then Y becomes provable"
    for (const c of fn.conditionals) {
      process.stdout.write(`    ${yellow}→${reset}  ${dim}if you add${reset} ${cyan}requires${reset}(${c.requires})${dim}, then${reset} ${cyan}ensures${reset}(${c.enables}) ${green}becomes provable${reset}\n`)
    }
  }
}

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

export async function suggestCommand(paths: string[], config: ResolvedConfig): Promise<void> {
  const cwd = process.cwd()
  const files = resolveFiles(paths, config)

  if (files.length === 0) {
    process.stderr.write(`No .ts files found in: ${paths.join(', ')}\n`)
    process.exit(1)
  }

  const ctx = await getContext()
  let totalSuggestions = 0

  for (const absPath of files) {
    const displayPath = relative(cwd, absPath)
    let source: string
    try { source = readFileSync(absPath, 'utf-8') } catch { continue }

    const irs = extractFunctionsFromSource(source, absPath)
    if (irs.length === 0) continue

    const results: SuggestFunctionResult[] = []
    for (const ir of irs) {
      const result = await suggestContracts(ir, ctx)
      if (result.suggestions.length > 0 || result.conditionals.length > 0) results.push(result)
    }

    printSuggestions(displayPath, results)
    totalSuggestions += results.reduce((n, r) => n + r.suggestions.length + r.conditionals.length + r.guards.length, 0)
  }

  if (totalSuggestions === 0) {
    process.stdout.write(`\n${dim}No suggestions for ${files.length} file${files.length !== 1 ? 's' : ''}.${reset}\n`)
  }
  process.stdout.write('\n')
}
