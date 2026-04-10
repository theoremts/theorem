import * as fs from 'node:fs/promises'
import { transformTheoremCode } from './transform.js'

// Minimal structural types — avoids hard dependency on esbuild
interface EsbuildPlugin {
  name: string
  setup(build: EsbuildBuild): void
}

interface EsbuildBuild {
  onLoad(
    options: { filter: RegExp; namespace?: string },
    callback: (args: { path: string }) => Promise<{ contents: string; loader: string } | null | undefined>,
  ): void
}

/**
 * esbuild plugin that strips all `theorem` contracts from the output bundle.
 *
 * @example
 * // esbuild.config.ts
 * import { theoremStrip } from 'theorem/esbuild'
 * await build({ plugins: [theoremStrip()] })
 */
export function theoremStrip(): EsbuildPlugin {
  return {
    name: 'theorem-strip',
    setup(build) {
      build.onLoad({ filter: /\.tsx?$/ }, async (args) => {
        const source = await fs.readFile(args.path, 'utf8')
        if (!source.includes('proof') && !source.includes('theorem') && !source.includes('invariant') && !source.includes('decreases') && !source.includes('modifies')) return null
        const result = transformTheoremCode(source, args.path)
        if (!result) return null
        return { contents: result.code, loader: args.path.endsWith('.tsx') ? 'tsx' : 'ts' }
      })
    },
  }
}
