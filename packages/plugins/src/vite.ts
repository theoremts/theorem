import { transformTheoremCode } from './transform.js'

// Minimal structural type — avoids hard dependency on vite
interface VitePlugin {
  name: string
  transform?(code: string, id: string): { code: string; map?: undefined } | null
}

/**
 * Vite plugin that strips all `theorem` contracts from the output bundle.
 * Contracts are no-ops at runtime; this removes them for a cleaner build.
 *
 * @example
 * // vite.config.ts
 * import { theoremStrip } from 'theorem/vite'
 * export default { plugins: [theoremStrip()] }
 */
export function theoremStrip(): VitePlugin {
  return {
    name: 'theorem-strip',
    transform(code, id) {
      if (!id.endsWith('.ts') && !id.endsWith('.tsx')) return null
      if (!code.includes('proof') && !code.includes('theorem') && !code.includes('invariant') && !code.includes('decreases') && !code.includes('modifies')) return null
      return transformTheoremCode(code, id)
    },
  }
}
