import { defineConfig } from 'theoremts'

export default defineConfig({
  // Files to include/exclude
  include: ['src/**/*.ts'],
  exclude: ['**/*.test.ts', '**/*.spec.ts'],

  // Z3 solver settings
  solver: {
    timeout: 10000,        // ms per check (default 10000)
    maxCounterexamples: 3, // how many counterexamples to show (default 3)
    minimizeCounterexamples: false, // use Optimize solver (slower)
  },

  // Scan settings
  scan: {
    skipDirs: ['node_modules', 'dist', '.git', 'coverage'],
    risks: {
      'division-by-zero': 'critical',
      'modulo-by-zero': 'critical',
      'negative-sqrt': 'high',
      'log-of-nonpositive': 'high',
      'contract-violation': 'critical',
    },
  },

  // Reporter settings
  reporter: {
    format: 'cli',  // 'cli' | 'sarif'
    showUsedAssumptions: true,
  },
})
