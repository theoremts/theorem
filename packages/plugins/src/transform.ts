/**
 * Core AST transform that strips Theorem contracts from source code.
 *
 * Strategy:
 *   1. Remove `import { ... } from 'theorem'` statements
 *   2. Replace `proof(fn, ...contracts)` with `fn`
 *   3. Replace `proof.fn(() => body, ...contracts)` with `(() => body)()`
 *   4. Remove standalone `invariant(...)`, `decreases(...)`, `modifies(...)` calls
 *
 * Uses parenthesis-depth tracking (not regex alone) to handle nested parens
 * and multi-line expressions correctly.
 */

/** Result returned by the transform. `null` means no changes were needed. */
export interface TransformResult {
  code: string
  map?: undefined // source-map support can be added later
}

// All theorem runtime exports that should be stripped from imports
const THEOREM_EXPORTS = new Set([
  'proof', 'of',
  'requires', 'ensures',
  'invariant', 'decreases', 'modifies',
  'old', 'forall', 'exists',
  'positive', 'nonNegative', 'negative', 'finite', 'between',
  'sorted', 'unique', 'conserved',
])

/**
 * Transform source code by stripping all Theorem contracts.
 * Returns `null` if the code does not reference theorem at all.
 */
export function transformTheoremCode(code: string, _id: string): TransformResult | null {
  // Quick check: bail out if no theorem-related identifiers exist
  if (!hasTheoremTokens(code)) return null

  let result = code
  let changed = false

  // Step 1: Remove theorem imports
  const importResult = removeTheoremImports(result)
  if (importResult !== result) {
    result = importResult
    changed = true
  }

  // Step 2: Replace proof.fn(...) calls — do this BEFORE proof() to avoid partial matches
  const proofFnResult = replaceProofFnCalls(result)
  if (proofFnResult !== result) {
    result = proofFnResult
    changed = true
  }

  // Step 3: Replace proof(...) calls
  const proofResult = replaceProofCalls(result)
  if (proofResult !== result) {
    result = proofResult
    changed = true
  }

  // Step 4: Remove standalone invariant/decreases/modifies calls
  const standaloneResult = removeStandaloneCalls(result)
  if (standaloneResult !== result) {
    result = standaloneResult
    changed = true
  }

  return changed ? { code: result } : null
}

// ---------------------------------------------------------------------------
// Step 1: Remove theorem import statements
// ---------------------------------------------------------------------------

function removeTheoremImports(code: string): string {
  // Match: import { ... } from 'theorem'  or  import { ... } from "theorem"
  // Also match: import type { ... } from 'theorem'
  // Also match: import ... from 'theorem/...'  (subpath imports)
  return code.replace(
    /^\s*import\s+(?:type\s+)?(?:\{[^}]*\}|\*\s+as\s+\w+)\s+from\s+['"]theorem(?:\/[^'"]*)?['"]\s*;?\s*$/gm,
    '',
  )
}

// ---------------------------------------------------------------------------
// Step 2: Replace proof.fn(() => body, ...contracts) → (() => body)()
// ---------------------------------------------------------------------------

function replaceProofFnCalls(code: string): string {
  // Find all occurrences of `proof.fn(`
  const marker = 'proof.fn('
  let pos = 0
  let result = ''

  while (pos < code.length) {
    const idx = code.indexOf(marker, pos)
    if (idx === -1) {
      result += code.slice(pos)
      break
    }

    result += code.slice(pos, idx)

    // We're at the start of `proof.fn(`
    const argsStart = idx + marker.length
    const args = extractBalancedArgs(code, argsStart - 1) // pass the opening paren position
    if (args === null) {
      // Can't parse — leave as-is
      result += marker
      pos = argsStart
      continue
    }

    const { firstArg, end } = args
    // proof.fn(thunk, ...contracts) → (thunk)()
    result += `(${firstArg})()`
    pos = end + 1 // skip past the closing paren
  }

  return result
}

// ---------------------------------------------------------------------------
// Step 3: Replace proof(fn, ...contracts) → fn
// ---------------------------------------------------------------------------

function replaceProofCalls(code: string): string {
  // Find all occurrences of `proof(` that are NOT preceded by a dot (to avoid proof.fn)
  const result: string[] = []
  let pos = 0

  while (pos < code.length) {
    const idx = code.indexOf('proof(', pos)
    if (idx === -1) {
      result.push(code.slice(pos))
      break
    }

    // Check it's not proof.fn( or someproof(
    const charBefore = idx > 0 ? code[idx - 1] : ''
    if (charBefore === '.' || isIdentChar(charBefore ?? '')) {
      result.push(code.slice(pos, idx + 6))
      pos = idx + 6
      continue
    }

    result.push(code.slice(pos, idx))

    const argsStart = idx + 6 // length of 'proof('
    const args = extractBalancedArgs(code, argsStart - 1)
    if (args === null) {
      result.push('proof(')
      pos = argsStart
      continue
    }

    const { firstArg, end } = args
    result.push(firstArg)
    pos = end + 1
  }

  return result.join('')
}

// ---------------------------------------------------------------------------
// Step 4: Remove standalone invariant/decreases/modifies calls
// ---------------------------------------------------------------------------

function removeStandaloneCalls(code: string): string {
  // Match standalone calls: `invariant(...)`, `decreases(...)`, `modifies(...)`
  // These appear as statements (possibly indented, ending with optional semicolon)
  const names = ['invariant', 'decreases', 'modifies']

  for (const name of names) {
    let pos = 0
    let result = ''

    while (pos < code.length) {
      const idx = code.indexOf(name + '(', pos)
      if (idx === -1) {
        result += code.slice(pos)
        break
      }

      // Ensure it's not part of a larger identifier
      const charBefore = idx > 0 ? code[idx - 1] : ''
      if (isIdentChar(charBefore ?? '')) {
        result += code.slice(pos, idx + name.length + 1)
        pos = idx + name.length + 1
        continue
      }

      // Find the line start to check if this is a standalone statement
      let lineStart = idx
      while (lineStart > 0 && code[lineStart - 1] !== '\n') {
        lineStart--
      }
      const beforeOnLine = code.slice(lineStart, idx).trim()

      // Only strip if standalone (line is just whitespace before the call)
      // or preceded by `return` (for `return proof.fn(() => { ... invariant(...) })`)
      if (beforeOnLine !== '' && beforeOnLine !== 'return') {
        result += code.slice(pos, idx + name.length + 1)
        pos = idx + name.length + 1
        continue
      }

      const openParen = idx + name.length
      const closePos = findMatchingParen(code, openParen)
      if (closePos === -1) {
        result += code.slice(pos, idx + name.length + 1)
        pos = idx + name.length + 1
        continue
      }

      // Include the trailing semicolon and newline if present
      let endPos = closePos + 1
      while (endPos < code.length && (code[endPos] === ' ' || code[endPos] === '\t')) {
        endPos++
      }
      if (endPos < code.length && code[endPos] === ';') {
        endPos++
      }
      if (endPos < code.length && code[endPos] === '\n') {
        endPos++
      }

      // Also remove leading whitespace on the line
      result += code.slice(pos, lineStart)
      pos = endPos
    }

    code = result
  }

  return code
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const THEOREM_TOKENS = ['proof(', 'proof.fn(', 'invariant(', 'decreases(', 'modifies(', "'theorem", '"theorem']

function hasTheoremTokens(code: string): boolean {
  return THEOREM_TOKENS.some((token) => code.includes(token))
}

function isIdentChar(ch: string): boolean {
  return /[a-zA-Z0-9_$]/.test(ch)
}

/**
 * Given the position of an opening parenthesis, extract the first argument
 * and find the position of the matching closing parenthesis.
 */
function extractBalancedArgs(
  code: string,
  openParenPos: number,
): { firstArg: string; end: number } | null {
  if (code[openParenPos] !== '(') return null

  let depth = 1
  let pos = openParenPos + 1
  let firstArgEnd = -1
  let templateDepth = 0

  // Track when we hit the first comma at depth 1 — that separates fn from contracts
  while (pos < code.length && depth > 0) {
    const ch = code[pos]!

    if (ch === '`') {
      // Skip template literals
      pos++
      while (pos < code.length) {
        if (code[pos] === '\\') {
          pos += 2
          continue
        }
        if (code[pos] === '$' && code[pos + 1] === '{') {
          templateDepth++
          pos += 2
          continue
        }
        if (code[pos] === '}' && templateDepth > 0) {
          templateDepth--
          pos++
          continue
        }
        if (code[pos] === '`' && templateDepth === 0) {
          pos++
          break
        }
        pos++
      }
      continue
    }

    if (ch === "'" || ch === '"') {
      // Skip string literals
      const quote = ch
      pos++
      while (pos < code.length && code[pos] !== quote) {
        if (code[pos] === '\\') pos++
        pos++
      }
      pos++ // skip closing quote
      continue
    }

    if (ch === '/' && code[pos + 1] === '/') {
      // Skip line comments
      while (pos < code.length && code[pos] !== '\n') pos++
      continue
    }

    if (ch === '/' && code[pos + 1] === '*') {
      // Skip block comments
      pos += 2
      while (pos < code.length && !(code[pos - 1] === '*' && code[pos] === '/')) pos++
      pos++
      continue
    }

    if (ch === '(' || ch === '[' || ch === '{') {
      depth++
    } else if (ch === ')' || ch === ']' || ch === '}') {
      depth--
      if (depth === 0) {
        // End of the entire call
        if (firstArgEnd === -1) {
          firstArgEnd = pos // no comma found — single arg
        }
        const firstArg = code.slice(openParenPos + 1, firstArgEnd).trim()
        return { firstArg, end: pos }
      }
    } else if (ch === ',' && depth === 1 && firstArgEnd === -1) {
      firstArgEnd = pos
    }

    pos++
  }

  return null
}

/**
 * Find the position of the closing parenthesis matching the one at `openPos`.
 */
function findMatchingParen(code: string, openPos: number): number {
  const result = extractBalancedArgs(code, openPos)
  return result?.end ?? -1
}
