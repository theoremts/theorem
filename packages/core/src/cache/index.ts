import { createHash } from 'node:crypto'
import type { FunctionReport } from '../reporter/cli.js'

export interface CachedFileResult {
  contentHash: string
  functionResults: FunctionReport[]
  /** Function names with contracts defined in this file. */
  contractNames: string[]
  /** Function names called from this file (for dependency invalidation). */
  calledFunctions: string[]
}

/**
 * In-memory verification cache.
 * Returns cached results for unchanged files; invalidates dependents
 * when a contract-bearing function changes.
 */
export class VerificationCache {
  private entries = new Map<string, CachedFileResult>()

  /** Returns cached result if file contents haven't changed. */
  get(absPath: string, source: string): CachedFileResult | null {
    const entry = this.entries.get(absPath)
    if (entry === undefined) return null
    if (entry.contentHash !== hashContent(source)) return null
    return entry
  }

  set(absPath: string, source: string, result: Omit<CachedFileResult, 'contentHash'>): void {
    this.entries.set(absPath, {
      ...result,
      contentHash: hashContent(source),
    })
  }

  /**
   * Invalidates cache entries that depend on changed contract functions.
   * Returns paths that need re-verification.
   */
  invalidateDependentsOf(changedNames: Set<string>): string[] {
    if (changedNames.size === 0) return []

    const toRevery: string[] = []
    for (const [path, entry] of this.entries) {
      if (entry.calledFunctions.some(name => changedNames.has(name))) {
        this.entries.delete(path)
        toRevery.push(path)
      }
    }
    return toRevery
  }

  clear(): void {
    this.entries.clear()
  }
}

function hashContent(source: string): string {
  return createHash('sha256').update(source).digest('hex')
}
