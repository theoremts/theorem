import { existsSync } from 'node:fs'
import { resolve, join } from 'node:path'
import { pathToFileURL } from 'node:url'

// ---------------------------------------------------------------------------
// TheoremConfig type (duplicated from runtime to avoid circular dependency)
// ---------------------------------------------------------------------------

export interface TheoremConfig {
  include?: string[]
  exclude?: string[]
  /** Glob patterns for `.contracts.ts` files that declare contracts for external functions. */
  contracts?: string[]
  solver?: {
    timeout?: number
    maxCounterexamples?: number
    minimizeCounterexamples?: boolean
  }
  scan?: {
    skipDirs?: string[]
    risks?: Record<string, string>
  }
  reporter?: {
    format?: 'cli' | 'sarif'
    showUsedAssumptions?: boolean
  }
}

// ---------------------------------------------------------------------------
// Defaults
// ---------------------------------------------------------------------------

export const DEFAULT_CONFIG: Required<Pick<TheoremConfig, 'include' | 'exclude' | 'contracts'>> & {
  solver: Required<NonNullable<TheoremConfig['solver']>>
  scan: Required<NonNullable<TheoremConfig['scan']>>
  reporter: Required<NonNullable<TheoremConfig['reporter']>>
} = {
  include: ['**/*.ts'],
  exclude: ['**/*.d.ts', '**/*.test.ts', '**/*.spec.ts'],
  contracts: [],
  solver: {
    timeout: 10_000,
    maxCounterexamples: 3,
    minimizeCounterexamples: false,
  },
  scan: {
    skipDirs: ['node_modules', 'dist', '.turbo', '.git', 'coverage', '.next', 'build', 'out'],
    risks: {},
  },
  reporter: {
    format: 'cli',
    showUsedAssumptions: true,
  },
}

// ---------------------------------------------------------------------------
// Resolved config — all fields present
// ---------------------------------------------------------------------------

export interface ResolvedConfig {
  include: string[]
  exclude: string[]
  contracts: string[]
  solver: {
    timeout: number
    maxCounterexamples: number
    minimizeCounterexamples: boolean
  }
  scan: {
    skipDirs: string[]
    risks: Record<string, string>
  }
  reporter: {
    format: 'cli' | 'sarif'
    showUsedAssumptions: boolean
  }
}

// ---------------------------------------------------------------------------
// Config file names (tried in order)
// ---------------------------------------------------------------------------

const CONFIG_FILES = [
  'theorem.config.ts',
  'theorem.config.js',
  'theorem.config.mjs',
]

// ---------------------------------------------------------------------------
// loadConfig — find and import a config file from cwd
// ---------------------------------------------------------------------------

/**
 * Load a `theorem.config.{ts,js,mjs}` file from the given directory.
 * Returns `null` when no config file is found.
 *
 * For `.ts` files, the function looks for the compiled `.js` output in
 * the same directory (assumes the user has compiled it or uses a loader).
 * In practice, CLI commands compile via `tsx` or the user provides `.js`.
 */
export async function loadConfig(cwd: string): Promise<TheoremConfig | null> {
  for (const name of CONFIG_FILES) {
    const filePath = join(cwd, name)
    if (!existsSync(filePath)) continue

    try {
      // For .ts files, try importing directly (works with tsx/ts-node loaders)
      // For .js/.mjs files, import directly
      const url = pathToFileURL(resolve(filePath)).href
      const mod = await import(url) as { default?: TheoremConfig }
      if (mod.default !== undefined) return mod.default
      // Some configs may export without default
      return mod as unknown as TheoremConfig
    } catch {
      // If .ts import fails, try the .js sibling (compiled output)
      if (name.endsWith('.ts')) {
        const jsPath = filePath.replace(/\.ts$/, '.js')
        if (existsSync(jsPath)) {
          try {
            const url = pathToFileURL(resolve(jsPath)).href
            const mod = await import(url) as { default?: TheoremConfig }
            if (mod.default !== undefined) return mod.default
            return mod as unknown as TheoremConfig
          } catch { /* skip */ }
        }
      }
    }
  }

  return null
}

// ---------------------------------------------------------------------------
// resolveConfig — merge user config with defaults
// ---------------------------------------------------------------------------

export function resolveConfig(userConfig: TheoremConfig | null): ResolvedConfig {
  const cfg = userConfig ?? {}
  return {
    include: cfg.include ?? DEFAULT_CONFIG.include,
    exclude: cfg.exclude ?? DEFAULT_CONFIG.exclude,
    contracts: cfg.contracts ?? DEFAULT_CONFIG.contracts,
    solver: {
      timeout: cfg.solver?.timeout ?? DEFAULT_CONFIG.solver.timeout,
      maxCounterexamples: cfg.solver?.maxCounterexamples ?? DEFAULT_CONFIG.solver.maxCounterexamples,
      minimizeCounterexamples: cfg.solver?.minimizeCounterexamples ?? DEFAULT_CONFIG.solver.minimizeCounterexamples,
    },
    scan: {
      skipDirs: cfg.scan?.skipDirs ?? DEFAULT_CONFIG.scan.skipDirs,
      risks: cfg.scan?.risks ?? DEFAULT_CONFIG.scan.risks,
    },
    reporter: {
      format: cfg.reporter?.format ?? DEFAULT_CONFIG.reporter.format,
      showUsedAssumptions: cfg.reporter?.showUsedAssumptions ?? DEFAULT_CONFIG.reporter.showUsedAssumptions,
    },
  }
}
