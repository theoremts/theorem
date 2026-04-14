import type { SolverResult } from '../solver/result.js'
import type { VerificationTask } from '../translator/index.js'

// ---------------------------------------------------------------------------
// ANSI helpers
// ---------------------------------------------------------------------------

const isTTY = process.stdout.isTTY

const c = {
  reset:  isTTY ? '\x1b[0m'  : '',
  bold:   isTTY ? '\x1b[1m'  : '',
  dim:    isTTY ? '\x1b[2m'  : '',
  green:  isTTY ? '\x1b[32m' : '',
  red:    isTTY ? '\x1b[31m' : '',
  yellow: isTTY ? '\x1b[33m' : '',
  cyan:   isTTY ? '\x1b[36m' : '',
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface TaskResult {
  task: VerificationTask
  result: SolverResult
  durationMs: number
}

export interface FileReport {
  filePath: string
  functionResults: FunctionReport[]
  totalMs: number
}

export interface FunctionReport {
  name?: string | undefined
  taskResults: TaskResult[]
}

// ---------------------------------------------------------------------------
// Formatting
// ---------------------------------------------------------------------------

export function printFileReport(report: FileReport): void {
  const { filePath, functionResults, totalMs } = report

  const allResults = functionResults.flatMap(f => f.taskResults)
  const proved   = allResults.filter(r => r.result.status === 'proved').length
  const failed   = allResults.filter(r => r.result.status === 'disproved').length
  const unknown  = allResults.filter(r => r.result.status === 'unknown').length
  const total    = allResults.length

  if (total === 0) {
    console.log(`${c.dim}No contracts found in ${filePath}${c.reset}`)
    return
  }

  console.log(`\n${c.bold}${filePath}${c.reset}`)

  for (const fn of functionResults) {
    const fnName = fn.name ?? '(anonymous)'
    console.log(`\n  ${c.bold}${fnName}${c.reset}`)

    for (const { task, result, durationMs } of fn.taskResults) {
      const text = task.contractText

      if (result.status === 'proved') {
        console.log(`    ${c.green}✓${c.reset}  ${text}`)
        // Show which assumptions were used (unsat core)
        if (result.usedAssumptions && result.usedAssumptions.length > 0) {
          const used = result.usedAssumptions.filter(a => !a.startsWith('body:'))
          if (used.length > 0) {
            console.log(`       ${c.dim}using: ${used.join(', ')}${c.reset}`)
          }
        }
      } else if (result.status === 'disproved') {
        console.log(`    ${c.red}✗${c.reset}  ${text}`)
        const ce = result.counterexample
        const ceStr = Object.entries(ce)
          .map(([k, v]) => `${k} = ${v}`)
          .join(', ')
        if (ceStr) {
          console.log(`       ${c.dim}counterexample: ${ceStr}${c.reset}`)
        } else {
          console.log(`       ${c.dim}violation confirmed (literal values)${c.reset}`)
        }

        // Show intermediate value trace with source locations if available
        if (result.trace) {
          const traceEntries = Object.entries(result.trace).filter(([, v]) => v !== '?')
          if (traceEntries.length > 0) {
            for (const [name, value] of traceEntries) {
              const loc = result.traceLocs?.[name]
              const locStr = loc ? ` ${c.dim}(line ${loc.line})${c.reset}` : ''
              console.log(`       ${c.dim}  where ${name} = ${value}${locStr}${c.reset}`)
            }
          }
        }

        // Show additional counterexamples if available
        if (result.allCounterexamples && result.allCounterexamples.length > 1) {
          for (let i = 1; i < result.allCounterexamples.length; i++) {
            const extra = result.allCounterexamples[i]!
            const extraStr = Object.entries(extra)
              .map(([k, v]) => `${k} = ${v}`)
              .join(', ')
            console.log(`       ${c.dim}           also: ${extraStr}${c.reset}`)
          }
        }
      } else {
        console.log(`    ${c.yellow}?${c.reset}  ${text}  ${c.dim}(${result.reason})${c.reset}`)
      }

      void durationMs
    }
  }

  const time = `${(totalMs / 1000).toFixed(1)}s`
  const parts: string[] = []
  if (proved  > 0) parts.push(`${c.green}${proved} proved${c.reset}`)
  if (failed  > 0) parts.push(`${c.red}${failed} failed${c.reset}`)
  if (unknown > 0) parts.push(`${c.yellow}${unknown} unknown${c.reset}`)

  console.log(`\n  ${parts.join(`  ${c.dim}·${c.reset}  `)}  ${c.dim}${time}${c.reset}\n`)
}
