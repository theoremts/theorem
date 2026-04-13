#!/usr/bin/env node
import { Command } from 'commander'
import { loadConfig, resolveConfig } from '@theoremts/core'
import type { ResolvedConfig } from '@theoremts/core'
import { verifyCommand } from './commands/verify.js'
import { scanCommand } from './commands/scan.js'
import { suggestCommand } from './commands/suggest.js'
import { inferCommand } from './commands/infer.js'

// Load config once at startup and make it available to commands
let resolvedConfig: ResolvedConfig

async function getConfig(): Promise<ResolvedConfig> {
  if (!resolvedConfig) {
    const userConfig = await loadConfig(process.cwd())
    resolvedConfig = resolveConfig(userConfig)
  }
  return resolvedConfig
}

const program = new Command()
  .name('theorem')
  .description('Formal verification for TypeScript')
  .version('0.1.0')

program
  .command('verify <paths...>')
  .description('Prove annotated contracts — accepts files, directories, or multiple paths')
  .option('--strict', 'exit 1 if any proof fails (CI mode)')
  .option('--debug', 'show parser → translator → solver internals')
  .option('--watch', 'watch for file changes and re-verify')
  .option('--format <fmt>', 'output format: cli (default) or sarif')
  .option('--timeout <ms>', 'Z3 solver timeout in milliseconds')
  .action(async (paths: string[], opts: Record<string, unknown>) => {
    const config = await getConfig()
    return verifyCommand(paths, opts, config)
  })

program
  .command('scan <paths...>')
  .description('Detect risks without annotations — division by zero, negative sqrt, etc.')
  .option('--strict', 'exit 1 if any risks are found (CI mode)')
  .option('--format <fmt>', 'output format: cli (default) or sarif')
  .action(async (paths: string[], opts: Record<string, unknown>) => {
    const config = await getConfig()
    return scanCommand(paths, opts, config)
  })

program
  .command('suggest <paths...>')
  .description('Auto-generate contract suggestions for unannotated functions')
  .action(async (paths: string[]) => {
    const config = await getConfig()
    return suggestCommand(paths, config)
  })

program
  .command('infer <paths...>')
  .description('Infer contracts from existing code')
  .option('--output <path>', 'write contracts to a specific file')
  .option('--dry-run', 'preview without writing files')
  .option('--confidence <level>', 'minimum confidence: proven, guard, derived, propagated, heuristic')
  .option('--strict', 'exit 1 if any function has no inferred contracts')
  .option('--prove', 'enable Z3 verification of ensures candidates (slower)')
  .action(async (paths: string[], opts: Record<string, unknown>) => {
    const config = await getConfig()
    return inferCommand(paths, opts, config)
  })

program.parseAsync().catch((err: unknown) => {
  console.error(err)
  process.exit(1)
})
