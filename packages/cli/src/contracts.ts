import { readdirSync, statSync } from 'node:fs'
import { resolve, join } from 'node:path'

/**
 * Resolves contract file globs to absolute paths.
 *
 * Supports simple patterns:
 *   - `contracts/*.contracts.ts` — files matching in the contracts/ directory
 *   - `**\/*.contracts.ts` — recursive search for .contracts.ts files
 *   - Direct file paths: `contracts/math.contracts.ts`
 */
export function resolveContractFiles(patterns: string[], cwd: string): string[] {
  const files: string[] = []

  // Auto-discover: @theorem-contracts/* in node_modules
  autoDiscoverContracts(cwd, files)

  // Auto-discover: theorem.contracts.ts published by libs in node_modules
  autoDiscoverLibContracts(cwd, files)

  for (const pattern of patterns) {
    if (pattern.startsWith('**/')) {
      // Recursive glob: **/*.contracts.ts
      const suffix = pattern.slice(3) // e.g. "*.contracts.ts"
      collectMatchingFiles(cwd, suffix, files, true)
    } else if (pattern.includes('*')) {
      // Directory glob: contracts/*.contracts.ts
      const slashIdx = pattern.lastIndexOf('/')
      const dir = slashIdx >= 0 ? pattern.slice(0, slashIdx) : '.'
      const filePattern = slashIdx >= 0 ? pattern.slice(slashIdx + 1) : pattern
      const absDir = resolve(cwd, dir)
      collectMatchingFiles(absDir, filePattern, files, false)
    } else {
      // Direct file path
      const absPath = resolve(cwd, pattern)
      try {
        if (statSync(absPath).isFile()) files.push(absPath)
      } catch { /* skip missing files */ }
    }
  }

  return [...new Set(files)]
}

function collectMatchingFiles(
  dir: string,
  pattern: string,
  out: string[],
  recursive: boolean,
): void {
  let entries: string[]
  try { entries = readdirSync(dir) } catch { return }

  for (const entry of entries) {
    const absPath = join(dir, entry)
    let stat
    try { stat = statSync(absPath) } catch { continue }

    if (stat.isFile() && matchesPattern(entry, pattern)) {
      out.push(absPath)
    } else if (stat.isDirectory() && recursive) {
      // Skip common non-source dirs
      if (entry === 'node_modules' || entry === 'dist' || entry === '.git') continue
      collectMatchingFiles(absPath, pattern, out, true)
    }
  }
}

function matchesPattern(name: string, pattern: string): boolean {
  if (pattern.startsWith('*')) {
    return name.endsWith(pattern.slice(1))
  }
  return name === pattern
}

/**
 * Auto-discovers @theorem-contracts/* packages in node_modules.
 * Looks for index.contracts.ts or theorem.contracts.ts in each.
 */
function autoDiscoverContracts(cwd: string, out: string[]): void {
  const nmDir = join(cwd, 'node_modules', '@theorem-contracts')
  try {
    const packages = readdirSync(nmDir)
    for (const pkg of packages) {
      const pkgDir = join(nmDir, pkg)
      for (const filename of ['index.contracts.ts', 'theorem.contracts.ts']) {
        const contractFile = join(pkgDir, filename)
        try {
          if (statSync(contractFile).isFile()) {
            out.push(contractFile)
          }
        } catch { /* skip */ }
      }
    }
  } catch { /* @theorem-contracts not installed — skip */ }
}

/**
 * Auto-discovers theorem.contracts.ts published by libraries in node_modules.
 * Scans top-level packages (not deep) for a theorem.contracts.ts file.
 */
function autoDiscoverLibContracts(cwd: string, out: string[]): void {
  const nmDir = join(cwd, 'node_modules')
  try {
    const entries = readdirSync(nmDir)
    for (const entry of entries) {
      if (entry.startsWith('.')) continue

      if (entry.startsWith('@')) {
        // Scoped package: @scope/pkg
        const scopeDir = join(nmDir, entry)
        try {
          const scopedPkgs = readdirSync(scopeDir)
          for (const pkg of scopedPkgs) {
            const contractFile = join(scopeDir, pkg, 'theorem.contracts.ts')
            try {
              if (statSync(contractFile).isFile()) out.push(contractFile)
            } catch { /* skip */ }
          }
        } catch { /* skip */ }
      } else {
        // Regular package
        const contractFile = join(nmDir, entry, 'theorem.contracts.ts')
        try {
          if (statSync(contractFile).isFile()) out.push(contractFile)
        } catch { /* skip */ }
      }
    }
  } catch { /* node_modules not found — skip */ }
}
