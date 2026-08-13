import { SyntaxKind, Node, type Block, type SourceFile, type Expression } from 'ts-morph'
import type { InferredContract } from './index.js'
import type { Expr } from '../parser/ir.js'
import {
  resolveSchemaVariable,
  resolveImportedSchema,
  extractArrowPredicates,
  bindRefineInvariant,
  buildFieldExpr,
  buildText,
  findBalancedParen,
  type RefineInvariant,
} from './zod.js'

/**
 * Effect Schema support — full parity with the Zod integration.
 *
 * Recognized patterns:
 *   const x = Schema.decodeUnknownSync(S)(input)   → field constraints assumed
 *   const x = Schema.decodeSync(S)(input)          → same
 *   Schema.Struct({ f: Schema.Number.pipe(Schema.positive()) })
 *   Schema.Struct({...}).pipe(Schema.filter(s => ...))  → cross-field invariant
 *   type T = Schema.Schema.Type<typeof S> / typeof S.Type → producer obligations
 *
 * Works with both `Schema.*` and aliased imports (`import * as S`).
 */

const DECODE_METHODS = new Set(['decodeUnknownSync', 'decodeSync'])

/**
 * Extracts assume-contracts from Effect Schema decode calls in a function body.
 * decodeUnknownSync/decodeSync throw on invalid input, so the schema's
 * constraints hold for the result afterwards — same guard semantics as
 * Zod's parse(). (Effect-returning decode variants are skipped: their failure
 * is a value, not a throw.)
 */
export function extractEffectContracts(body: Block): InferredContract[] {
  const contracts: InferredContract[] = []
  const seen = new Set<string>()

  for (const callNode of body.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    // Curried form: decodeUnknownSync(S)(input) — outer call's expression is
    // itself a call whose callee ends with a decode method name.
    const outerCallee = callNode.getExpression()
    if (!Node.isCallExpression(outerCallee)) continue

    const innerCalleeText = outerCallee.getExpression().getText()
    const lastSegment = innerCalleeText.includes('.')
      ? innerCalleeText.slice(innerCalleeText.lastIndexOf('.') + 1)
      : innerCalleeText
    if (!DECODE_METHODS.has(lastSegment)) continue

    const varDecl = callNode.getFirstAncestorByKind(SyntaxKind.VariableDeclaration)
    if (!varDecl) continue
    const varName = varDecl.getName()
    if (!varName) continue

    const schemaArg = outerCallee.getArguments()[0]
    if (!schemaArg) continue
    let schemaText = schemaArg.getText().trim()
    if (Node.isIdentifier(schemaArg)) {
      const resolved = resolveSchemaVariable(body, schemaArg.getText())
      if (resolved) schemaText = resolved
    }

    const extracted = extractEffectConstraintsFromSchemaText(schemaText, varName)

    // Cross-field invariants from Schema.filter()
    for (const inv of extractEffectFilterInvariants(schemaText)) {
      extracted.push({
        kind: 'requires',
        text: `filter invariant on ${varName}`,
        predicate: bindRefineInvariant(inv, { kind: 'ident', name: varName }),
        confidence: 'guard',
        source: 'from Effect Schema: filter(...)',
      })
    }

    for (const c of extracted) {
      if (!seen.has(c.text)) {
        seen.add(c.text)
        contracts.push(c)
      }
    }
  }

  return contracts
}

/**
 * Cross-field invariants: `Schema.Struct({...}).pipe(Schema.filter(arrow))`.
 * Only filters applied AFTER the Struct's closing paren are struct-level;
 * filters inside field chains are per-field refinements of a single value
 * and are (conservatively) ignored here.
 */
export function extractEffectFilterInvariants(schemaText: string): RefineInvariant[] {
  const structEnd = findStructEnd(schemaText)
  if (structEnd === -1) return []
  return extractArrowPredicates(schemaText.slice(structEnd), 'filter(')
}

/** Position just after the Struct({...}) call's closing paren, or -1. */
function findStructEnd(schemaText: string): number {
  const m = /(?:\w+\.)?Struct\s*\(/.exec(schemaText)
  if (!m) return -1
  const close = findBalancedParen(schemaText, m.index + m[0].length)
  return close === -1 ? -1 : close + 1
}

// ---------------------------------------------------------------------------
// Field-constraint extraction from Struct schema text
// ---------------------------------------------------------------------------

interface EffectFieldConstraint {
  field: string
  op: '>' | '>=' | '<' | '<='
  value: number
  isLength: boolean
  source: string
  /** For Schema.int(): emit Number.isInteger instead of a comparison. */
  isInt?: boolean
}

export function extractEffectConstraintsFromSchemaText(
  schemaText: string,
  varName: string,
): InferredContract[] {
  const constraints: EffectFieldConstraint[] = []

  const structMatch = /(?:\w+\.)?Struct\s*\(\s*\{/.exec(schemaText)
  if (structMatch) {
    const bodyStart = structMatch.index + structMatch[0].length
    const bodyEnd = findBalancedBrace(schemaText, bodyStart)
    if (bodyEnd !== -1) {
      for (const { name, chain } of splitStructFields(schemaText.slice(bodyStart, bodyEnd))) {
        extractEffectChainConstraints(name, chain, constraints)
      }
    }
  } else {
    // Top-level (non-struct) schema: the variable itself is constrained
    extractEffectChainConstraints('', schemaText, constraints)
  }

  return constraints.map(c => {
    if (c.isInt) {
      const fieldExpr = buildFieldExpr(varName, c.field, false)
      return {
        kind: 'requires' as const,
        text: `Number.isInteger(${c.field ? `${varName}.${c.field}` : varName})`,
        predicate: { kind: 'call' as const, callee: 'Number.isInteger', args: [fieldExpr] },
        confidence: 'guard' as const,
        source: `from Effect Schema: ${c.source}`,
      }
    }
    const fieldExpr = buildFieldExpr(varName, c.field, c.isLength)
    return {
      kind: 'requires' as const,
      text: buildText(varName, c.field, c.op, c.value, c.isLength),
      predicate: {
        kind: 'binary' as const,
        op: c.op,
        left: fieldExpr,
        right: { kind: 'literal' as const, value: c.value },
      },
      confidence: 'guard' as const,
      source: `from Effect Schema: ${c.source}`,
    }
  })
}

/** Splits a Struct object-literal body into top-level `name: chain` fields. */
function splitStructFields(body: string): Array<{ name: string; chain: string }> {
  const fields: Array<{ name: string; chain: string }> = []
  let depth = 0
  let start = 0

  const push = (segment: string): void => {
    const m = /^\s*(\w+)\s*:\s*([\s\S]+)$/.exec(segment)
    if (m) fields.push({ name: m[1]!, chain: m[2]!.trim() })
  }

  for (let i = 0; i < body.length; i++) {
    const ch = body[i]
    if (ch === '(' || ch === '{' || ch === '[') depth++
    else if (ch === ')' || ch === '}' || ch === ']') depth--
    else if (ch === ',' && depth === 0) {
      push(body.slice(start, i))
      start = i + 1
    }
  }
  push(body.slice(start))

  return fields
}

const NUM = String.raw`(-?\d+(?:\.\d+)?)`

function extractEffectChainConstraints(
  field: string,
  chain: string,
  out: EffectFieldConstraint[],
): void {
  const baseMatch = /(?:\w+\.)?(Number|String|Array|NonEmptyArray)\b/.exec(chain)
  const base = baseMatch?.[1] ?? 'Number'
  const isLength = base === 'String' || base === 'Array' || base === 'NonEmptyArray'

  if (!isLength) {
    if (/\bpositive\(\)/.test(chain)) out.push({ field, op: '>', value: 0, isLength: false, source: 'positive()' })
    if (/\bnonNegative\(\)/.test(chain)) out.push({ field, op: '>=', value: 0, isLength: false, source: 'nonNegative()' })
    if (/\bnegative\(\)/.test(chain)) out.push({ field, op: '<', value: 0, isLength: false, source: 'negative()' })
    if (/\bnonPositive\(\)/.test(chain)) out.push({ field, op: '<=', value: 0, isLength: false, source: 'nonPositive()' })

    const between = new RegExp(String.raw`\bbetween\(\s*${NUM}\s*,\s*${NUM}\s*\)`).exec(chain)
    if (between) {
      out.push({ field, op: '>=', value: Number(between[1]), isLength: false, source: `between(${between[1]}, ${between[2]})` })
      out.push({ field, op: '<=', value: Number(between[2]), isLength: false, source: `between(${between[1]}, ${between[2]})` })
    }

    const gte = new RegExp(String.raw`\bgreaterThanOrEqualTo\(\s*${NUM}\s*\)`).exec(chain)
    if (gte) out.push({ field, op: '>=', value: Number(gte[1]), isLength: false, source: `greaterThanOrEqualTo(${gte[1]})` })
    const gt = new RegExp(String.raw`\bgreaterThan\(\s*${NUM}\s*\)`).exec(chain)
    if (gt) out.push({ field, op: '>', value: Number(gt[1]), isLength: false, source: `greaterThan(${gt[1]})` })
    const lte = new RegExp(String.raw`\blessThanOrEqualTo\(\s*${NUM}\s*\)`).exec(chain)
    if (lte) out.push({ field, op: '<=', value: Number(lte[1]), isLength: false, source: `lessThanOrEqualTo(${lte[1]})` })
    const lt = new RegExp(String.raw`\blessThan\(\s*${NUM}\s*\)`).exec(chain)
    if (lt) out.push({ field, op: '<', value: Number(lt[1]), isLength: false, source: `lessThan(${lt[1]})` })

    if (/\bint\(\)/.test(chain)) out.push({ field, op: '>=', value: 0, isLength: false, source: 'int()', isInt: true })
  } else {
    if (base === 'NonEmptyArray' || /\bnonEmptyString\(\)/.test(chain) || /\bnonEmptyArray\(\)/.test(chain)) {
      out.push({ field, op: '>', value: 0, isLength: true, source: base === 'NonEmptyArray' ? 'NonEmptyArray' : 'nonEmpty' })
    }
    const minL = new RegExp(String.raw`\bminLength\(\s*(\d+)\s*\)`).exec(chain)
    if (minL) out.push({ field, op: '>=', value: Number(minL[1]), isLength: true, source: `minLength(${minL[1]})` })
    const maxL = new RegExp(String.raw`\bmaxLength\(\s*(\d+)\s*\)`).exec(chain)
    if (maxL) out.push({ field, op: '<=', value: Number(maxL[1]), isLength: true, source: `maxLength(${maxL[1]})` })
    const minI = new RegExp(String.raw`\bminItems\(\s*(\d+)\s*\)`).exec(chain)
    if (minI) out.push({ field, op: '>=', value: Number(minI[1]), isLength: true, source: `minItems(${minI[1]})` })
    const maxI = new RegExp(String.raw`\bmaxItems\(\s*(\d+)\s*\)`).exec(chain)
    if (maxI) out.push({ field, op: '<=', value: Number(maxI[1]), isLength: true, source: `maxItems(${maxI[1]})` })
  }
}

/** Matches a balanced closing brace; `start` is just after the opening `{`. */
function findBalancedBrace(text: string, start: number): number {
  let depth = 1
  for (let i = start; i < text.length; i++) {
    if (text[i] === '{') depth++
    else if (text[i] === '}') {
      depth--
      if (depth === 0) return i
    }
  }
  return -1
}

// ---------------------------------------------------------------------------
// File-level scan — Struct schemas with filter invariants + type aliases
// ---------------------------------------------------------------------------

export interface EffectFileSchemaInvariants {
  schemas: Map<string, RefineInvariant[]>
  aliases: Map<string, string>
}

/**
 * Scans a file for Effect Struct schemas carrying filter() invariants and for
 * type aliases derived from them:
 *   type T = Schema.Schema.Type<typeof S>
 *   type T = typeof S.Type
 */
export function extractEffectSchemaInvariantsFromFile(file: SourceFile): EffectFileSchemaInvariants {
  const schemas = new Map<string, RefineInvariant[]>()
  const aliases = new Map<string, string>()

  for (const decl of file.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
    const init = decl.getInitializer()
    if (!init) continue
    const text = init.getText()
    if (!/(?:\w+\.)?Struct\s*\(/.test(text) || !text.includes('filter(')) continue
    const invs = extractEffectFilterInvariants(text)
    if (invs.length > 0) schemas.set(decl.getName(), invs)
  }

  for (const alias of file.getTypeAliases()) {
    const typeText = alias.getTypeNode()?.getText() ?? ''
    const viaSchemaType = /(?:\w+\.)?Schema\.Type<\s*typeof\s+(\w+)\s*>/.exec(typeText)
    const viaTypeProp = /^typeof\s+(\w+)\.Type$/.exec(typeText.trim())
    const m = viaSchemaType ?? viaTypeProp
    if (m) aliases.set(alias.getName(), m[1]!)
  }

  // Aliases referencing schemas imported from other files
  for (const schemaName of new Set(aliases.values())) {
    if (schemas.has(schemaName)) continue
    const importedText = resolveImportedSchema(file, schemaName)
    if (importedText !== undefined && importedText.includes('filter(')) {
      const invs = extractEffectFilterInvariants(importedText)
      if (invs.length > 0) schemas.set(schemaName, invs)
    }
  }

  return { schemas, aliases }
}

/** True for `<...>.decodeUnknownSync(S)(x)` / `decodeSync(S)(x)` initializers. */
export function isEffectDecodeCall(init: Node): boolean {
  if (!Node.isCallExpression(init)) return false
  const callee = init.getExpression()
  if (!Node.isCallExpression(callee)) return false
  const text = callee.getExpression().getText()
  const last = text.includes('.') ? text.slice(text.lastIndexOf('.') + 1) : text
  return DECODE_METHODS.has(last)
}
