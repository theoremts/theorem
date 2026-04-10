import type { TaskResult, FileReport } from './cli.js'
import type { ScanFileResult } from '../scanner/index.js'

// ---------------------------------------------------------------------------
// SARIF types (subset of SARIF 2.1.0 schema)
// ---------------------------------------------------------------------------

interface SarifLog {
  $schema: string
  version: string
  runs: SarifRun[]
}

interface SarifRun {
  tool: { driver: SarifDriver }
  results: SarifResult[]
}

interface SarifDriver {
  name: string
  version: string
  rules: SarifRule[]
}

interface SarifRule {
  id: string
  shortDescription: { text: string }
  defaultConfiguration: { level: 'error' | 'warning' | 'note' }
}

interface SarifResult {
  ruleId: string
  level: 'error' | 'warning' | 'note'
  message: { text: string }
  locations: Array<{
    physicalLocation: {
      artifactLocation: { uri: string }
      region?: { startLine?: number }
    }
  }>
}

// ---------------------------------------------------------------------------
// Rule definitions
// ---------------------------------------------------------------------------

const RULES: SarifRule[] = [
  {
    id: 'theorem/contract-violated',
    shortDescription: { text: 'A contract could not be proved — counterexample found.' },
    defaultConfiguration: { level: 'error' },
  },
  {
    id: 'theorem/contract-proved',
    shortDescription: { text: 'A contract was proved for all inputs.' },
    defaultConfiguration: { level: 'note' },
  },
  {
    id: 'theorem/division-by-zero',
    shortDescription: { text: 'Division by an expression that can be zero.' },
    defaultConfiguration: { level: 'error' },
  },
  {
    id: 'theorem/modulo-by-zero',
    shortDescription: { text: 'Modulo by an expression that can be zero.' },
    defaultConfiguration: { level: 'error' },
  },
  {
    id: 'theorem/negative-sqrt',
    shortDescription: { text: 'Math.sqrt argument can be negative.' },
    defaultConfiguration: { level: 'warning' },
  },
  {
    id: 'theorem/log-of-nonpositive',
    shortDescription: { text: 'Math.log argument can be non-positive.' },
    defaultConfiguration: { level: 'warning' },
  },
  {
    id: 'theorem/contract-violation',
    shortDescription: { text: 'Call to a verified function may violate its requires contract.' },
    defaultConfiguration: { level: 'error' },
  },
  {
    id: 'theorem/array-out-of-bounds',
    shortDescription: { text: 'Array index may be out of bounds (negative index).' },
    defaultConfiguration: { level: 'warning' },
  },
  {
    id: 'theorem/null-access',
    shortDescription: { text: 'Property access on a value that may be null or undefined.' },
    defaultConfiguration: { level: 'error' },
  },
  {
    id: 'theorem/empty-array-reduce',
    shortDescription: { text: 'Array.reduce() called without initial value — throws TypeError on empty array.' },
    defaultConfiguration: { level: 'warning' },
  },
  {
    id: 'theorem/integer-overflow',
    shortDescription: { text: 'Integer operation may overflow Number.MAX_SAFE_INTEGER (2^53 - 1).' },
    defaultConfiguration: { level: 'note' },
  },
]

// ---------------------------------------------------------------------------
// Verify → SARIF
// ---------------------------------------------------------------------------

export function verifyToSarif(reports: FileReport[]): string {
  const results: SarifResult[] = []

  for (const report of reports) {
    for (const fn of report.functionResults) {
      for (const { task, result } of fn.taskResults) {
        const fnName = fn.name ?? '(anonymous)'

        if (result.status === 'disproved') {
          const ce = Object.entries(result.counterexample)
            .map(([k, v]) => `${k} = ${v}`)
            .join(', ')
          results.push({
            ruleId: 'theorem/contract-violated',
            level: 'error',
            message: { text: `${fnName}: ensures(${task.contractText}) — counterexample: ${ce}` },
            locations: [{ physicalLocation: { artifactLocation: { uri: report.filePath } } }],
          })
        } else if (result.status === 'proved') {
          results.push({
            ruleId: 'theorem/contract-proved',
            level: 'note',
            message: { text: `${fnName}: ensures(${task.contractText}) — proved` },
            locations: [{ physicalLocation: { artifactLocation: { uri: report.filePath } } }],
          })
        }
      }
    }
  }

  return JSON.stringify(makeSarifLog(results), null, 2)
}

// ---------------------------------------------------------------------------
// Scan → SARIF
// ---------------------------------------------------------------------------

export function scanToSarif(reports: ScanFileResult[]): string {
  const results: SarifResult[] = []

  for (const report of reports) {
    for (const fn of report.functions) {
      for (const risk of fn.risks) {
        const ruleId = `theorem/${risk.kind}`
        const fnName = fn.name ?? '(anonymous)'
        const ce = risk.counterexample
          ? ` — example: ${Object.entries(risk.counterexample).filter(([k]) => k !== 'result').map(([k, v]) => `${k}=${v}`).join(', ')}`
          : ''

        results.push({
          ruleId,
          level: risk.level === 'critical' ? 'error' : 'warning',
          message: { text: `${fnName}: ${risk.description}${ce}` },
          locations: [{
            physicalLocation: {
              artifactLocation: { uri: report.filePath },
              region: { startLine: risk.line },
            },
          }],
        })
      }
    }
  }

  return JSON.stringify(makeSarifLog(results), null, 2)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeSarifLog(results: SarifResult[]): SarifLog {
  return {
    $schema: 'https://raw.githubusercontent.com/oasis-tcs/sarif-spec/main/sarif-2.1/Schemata/sarif-schema-2.1.0.json',
    version: '2.1.0',
    runs: [{
      tool: {
        driver: {
          name: 'theorem',
          version: '0.1.0',
          rules: RULES,
        },
      },
      results,
    }],
  }
}
