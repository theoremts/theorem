import { SyntaxKind, Node, type Block } from 'ts-morph'
import type { InferredContract } from './index.js'
import type { Expr } from '../parser/ir.js'

/**
 * Extract contracts from Zod schema validation patterns.
 *
 * When code calls `schema.parse(input)`, the parse throws on invalid data,
 * so the remainder of the function can assume the Zod constraints hold.
 * This is equivalent to an if/throw guard, so we emit `requires` contracts.
 *
 * We look for VariableDeclarations of the form:
 *   const data = <schema-expr>.parse(input)
 *
 * Then resolve the schema expression (either inline or by tracing to a
 * VariableDeclaration in the enclosing scope) and use regex to extract
 * constraint methods from the Zod chain.
 */
export function extractZodContracts(body: Block): InferredContract[] {
  const contracts: InferredContract[] = []
  const seen = new Set<string>()

  // Find all call expressions that end in .parse() or .safeParse()
  for (const callNode of body.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const calleeExpr = callNode.getExpression()
    if (!Node.isPropertyAccessExpression(calleeExpr)) continue

    const methodName = calleeExpr.getName()
    if (methodName !== 'parse' && methodName !== 'safeParse') continue

    // For safeParse, the function doesn't throw — skip for now.
    // safeParse returns { success, data, error } and requires the caller
    // to check .success before using .data, so we can't assume the
    // constraints hold unconditionally.
    if (methodName === 'safeParse') continue

    // Find the variable name that stores the parse result.
    // Walk up to find the VariableDeclaration parent.
    const varDecl = callNode.getFirstAncestorByKind(SyntaxKind.VariableDeclaration)
    if (!varDecl) continue
    const varName = varDecl.getName()
    if (!varName) continue

    // Resolve the schema text: either the expression before .parse(),
    // or trace the variable it references.
    const schemaExpr = calleeExpr.getExpression()
    let schemaText = schemaExpr.getText().trim()

    // If the schema expression is a simple identifier, try to find its definition
    if (Node.isIdentifier(schemaExpr)) {
      const schemaName = schemaExpr.getText()
      const resolved = resolveSchemaVariable(body, schemaName)
      if (resolved) {
        schemaText = resolved
      }
    }

    // Extract constraints from the schema text
    const extracted = extractConstraintsFromSchemaText(schemaText, varName)
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
 * Try to find a variable declaration for the schema name in the enclosing
 * scope (the block itself, or any ancestor scope up to the source file).
 */
function resolveSchemaVariable(body: Block, name: string): string | undefined {
  // Search in the body itself
  for (const decl of body.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
    if (decl.getName() === name) {
      const init = decl.getInitializer()
      if (init) return init.getText().trim()
    }
  }

  // Search in sibling/parent scopes (walk up the tree)
  let current: Node | undefined = body.getParent()
  while (current) {
    if (Node.isSourceFile(current) || Node.isBlock(current)) {
      for (const decl of current.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
        if (decl.getName() === name) {
          const init = decl.getInitializer()
          if (init) return init.getText().trim()
        }
      }
    }
    current = current.getParent()
  }

  return undefined
}

// ---------------------------------------------------------------------------
// Regex-based constraint extraction from Zod schema text
// ---------------------------------------------------------------------------

interface FieldConstraint {
  field: string
  op: '>' | '>=' | '<' | '<='
  value: number
  /** Whether this is a .length constraint (for strings/arrays) */
  isLength: boolean
  /** Source description for the contract */
  source: string
}

/**
 * Starting from position `start` (just after an opening paren), find the
 * matching closing paren, handling nested parens.  Returns -1 if not found.
 */
function findBalancedParen(text: string, start: number): number {
  let depth = 1
  for (let i = start; i < text.length; i++) {
    if (text[i] === '(') depth++
    else if (text[i] === ')') {
      depth--
      if (depth === 0) return i
    }
  }
  return -1
}

function extractConstraintsFromSchemaText(schemaText: string, varName: string): InferredContract[] {
  const constraints: FieldConstraint[] = []

  // Match z.object({ field: z.number().<method>(), ... }) patterns
  // We extract field names and their constraint chains.
  // Use a two-step approach: first find "fieldName: z.type(" then balance parens.
  const fieldStartPattern = /(\w+)\s*:\s*z\.(number|string|array)\s*\(/g
  let startMatch: RegExpExecArray | null

  while ((startMatch = fieldStartPattern.exec(schemaText)) !== null) {
    const fieldName = startMatch[1]!
    const baseType = startMatch[2]!
    // Find the balanced closing paren for the base call
    const afterOpen = startMatch.index + startMatch[0].length
    const closeIdx = findBalancedParen(schemaText, afterOpen)
    if (closeIdx === -1) continue

    // Extract the remaining chain after the base call's closing paren
    const rest = schemaText.slice(closeIdx + 1)
    const chainMatch = /^((?:\.\w+\([^)]*\))*)/.exec(rest)
    const chainText = chainMatch?.[1] ?? ''

    extractChainConstraints(fieldName, baseType, chainText, constraints)
  }

  // Also handle top-level (non-object) schemas: z.number().positive().parse(x)
  // In this case the schema itself is the chain with no field name.
  if (constraints.length === 0) {
    const topLevelPattern = /^z\.(number|string|array)\s*\([^)]*\)((?:\.\w+\([^)]*\))*)$/
    const topMatch = topLevelPattern.exec(schemaText)
    if (topMatch) {
      const baseType = topMatch[1]!
      const chainText = topMatch[2] ?? ''
      // For top-level schemas, the varName itself is the constrained value
      extractChainConstraints(null, baseType, chainText, constraints)
    }
  }

  // Convert field constraints to InferredContracts
  return constraints.map(c => {
    const fieldExpr = buildFieldExpr(varName, c.field, c.isLength)
    const text = buildText(varName, c.field, c.op, c.value, c.isLength)

    const predicate: Expr = {
      kind: 'binary',
      op: c.op,
      left: fieldExpr,
      right: { kind: 'literal', value: c.value },
    }

    return {
      kind: 'requires' as const,
      text,
      predicate,
      confidence: 'guard' as const,
      source: `from Zod schema: ${c.source}`,
    }
  })
}

function extractChainConstraints(
  fieldName: string | null,
  baseType: string,
  chainText: string,
  out: FieldConstraint[],
): void {
  const field = fieldName ?? ''

  // Number constraints
  if (baseType === 'number') {
    if (/\.positive\(\)/.test(chainText)) {
      out.push({ field, op: '>', value: 0, isLength: false, source: 'z.number().positive()' })
    }
    if (/\.nonnegative\(\)/.test(chainText)) {
      out.push({ field, op: '>=', value: 0, isLength: false, source: 'z.number().nonnegative()' })
    }
    if (/\.negative\(\)/.test(chainText)) {
      out.push({ field, op: '<', value: 0, isLength: false, source: 'z.number().negative()' })
    }
    const minMatch = /\.min\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (minMatch) {
      out.push({ field, op: '>=', value: Number(minMatch[1]), isLength: false, source: `z.number().min(${minMatch[1]})` })
    }
    const maxMatch = /\.max\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (maxMatch) {
      out.push({ field, op: '<=', value: Number(maxMatch[1]), isLength: false, source: `z.number().max(${maxMatch[1]})` })
    }
    // .gt(N) and .gte(N) / .lt(N) and .lte(N)
    const gtMatch = /\.gt\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (gtMatch) {
      out.push({ field, op: '>', value: Number(gtMatch[1]), isLength: false, source: `z.number().gt(${gtMatch[1]})` })
    }
    const gteMatch = /\.gte\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (gteMatch) {
      out.push({ field, op: '>=', value: Number(gteMatch[1]), isLength: false, source: `z.number().gte(${gteMatch[1]})` })
    }
    const ltMatch = /\.lt\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (ltMatch) {
      out.push({ field, op: '<', value: Number(ltMatch[1]), isLength: false, source: `z.number().lt(${ltMatch[1]})` })
    }
    const lteMatch = /\.lte\(\s*(-?\d+(?:\.\d+)?)\s*\)/.exec(chainText)
    if (lteMatch) {
      out.push({ field, op: '<=', value: Number(lteMatch[1]), isLength: false, source: `z.number().lte(${lteMatch[1]})` })
    }
  }

  // String constraints (on .length)
  if (baseType === 'string') {
    const minMatch = /\.min\(\s*(\d+)\s*\)/.exec(chainText)
    if (minMatch) {
      out.push({ field, op: '>=', value: Number(minMatch[1]), isLength: true, source: `z.string().min(${minMatch[1]})` })
    }
    const maxMatch = /\.max\(\s*(\d+)\s*\)/.exec(chainText)
    if (maxMatch) {
      out.push({ field, op: '<=', value: Number(maxMatch[1]), isLength: true, source: `z.string().max(${maxMatch[1]})` })
    }
    if (/\.nonempty\(\)/.test(chainText)) {
      out.push({ field, op: '>', value: 0, isLength: true, source: 'z.string().nonempty()' })
    }
  }

  // Array constraints (on .length)
  if (baseType === 'array') {
    if (/\.nonempty\(\)/.test(chainText)) {
      out.push({ field, op: '>', value: 0, isLength: true, source: 'z.array().nonempty()' })
    }
    const minMatch = /\.min\(\s*(\d+)\s*\)/.exec(chainText)
    if (minMatch) {
      out.push({ field, op: '>=', value: Number(minMatch[1]), isLength: true, source: `z.array().min(${minMatch[1]})` })
    }
    const maxMatch = /\.max\(\s*(\d+)\s*\)/.exec(chainText)
    if (maxMatch) {
      out.push({ field, op: '<=', value: Number(maxMatch[1]), isLength: true, source: `z.array().max(${maxMatch[1]})` })
    }
  }
}

function buildFieldExpr(varName: string, field: string, isLength: boolean): Expr {
  let base: Expr

  if (field) {
    base = {
      kind: 'member',
      object: { kind: 'ident', name: varName },
      property: field,
    }
  } else {
    base = { kind: 'ident', name: varName }
  }

  if (isLength) {
    return { kind: 'member', object: base, property: 'length' }
  }

  return base
}

function buildText(varName: string, field: string, op: string, value: number, isLength: boolean): string {
  const base = field ? `${varName}.${field}` : varName
  const prop = isLength ? `${base}.length` : base
  return `${prop} ${op} ${value}`
}
