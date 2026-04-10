import { theoremStrip } from './esbuild.js'

/**
 * tsup plugin that strips all `theorem` contracts from the output bundle.
 * tsup uses esbuild internally, so this wraps the esbuild plugin.
 *
 * @example
 * // tsup.config.ts
 * import { theoremTsup } from 'theorem/tsup'
 * export default defineConfig({ ...theoremTsup() })
 */
export function theoremTsup(): { esbuildPlugins: ReturnType<typeof theoremStrip>[] } {
  return { esbuildPlugins: [theoremStrip()] }
}

// Also re-export the esbuild plugin for backward compatibility
export { theoremStrip } from './esbuild.js'
