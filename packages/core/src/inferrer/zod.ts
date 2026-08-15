import { SyntaxKind, Node, Project, type Block, type SourceFile, type Expression } from 'ts-morph'
import type { InferredContract } from './index.js'
import type { Expr } from '../parser/ir.js'
import { parseExpr } from '../parser/expr.js'
import { substituteExpr } from '../translator/substitution.js'

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

    // Cross-field invariants from .refine(): bind to the parsed variable
    for (const inv of extractRefinePredicates(schemaText)) {
      const bound = bindRefineInvariant(inv, { kind: 'ident', name: varName })
      extracted.push({
        kind: 'requires',
        text: `refine invariant on ${varName}`,
        predicate: bound,
        confidence: 'guard',
        source: 'from Zod schema: .refine(...)',
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
 * Try to find a variable declaration for the schema name in the enclosing
 * scope (the block itself, or any ancestor scope up to the source file).
 */
export function resolveSchemaVariable(body: Block, name: string): string | undefined {
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
    if (Node.isSourceFile(current)) {
      // Not declared in this file — follow a relative import
      const imported = resolveImportedSchema(current, name)
      if (imported !== undefined) return imported
    }
    current = current.getParent()
  }

  return undefined
}

/**
 * Cross-file resolution: if `name` is imported from a relative module, read
 * that file from disk and extract the schema initializer text.
 * One level deep — schemas composing other imported schemas resolve partially.
 */
export function resolveImportedSchema(file: SourceFile, name: string): string | undefined {
  try {
    for (const imp of file.getImportDeclarations()) {
      const names = imp.getNamedImports().map(n => n.getName())
      if (!names.includes(name)) continue

      const spec = imp.getModuleSpecifierValue()
      if (!spec.startsWith('.')) return undefined  // only relative imports

      // eslint-disable-next-line @typescript-eslint/no-require-imports
      const { readFileSync } = require('fs') as typeof import('fs')
      // eslint-disable-next-line @typescript-eslint/no-require-imports
      const { dirname, resolve } = require('path') as typeof import('path')

      const base = resolve(dirname(file.getFilePath()), spec)
      for (const candidate of [base, `${base}.ts`, `${base}/index.ts`, base.replace(/\.js$/, '.ts')]) {
        let source: string
        try {
          source = readFileSync(candidate, 'utf-8')
        } catch { continue }

        const imported = getRefineProject().createSourceFile('__imported__.ts', source, { overwrite: true })
        for (const decl of imported.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
          if (decl.getName() === name) {
            const init = decl.getInitializer()
            if (init) return init.getText().trim()
          }
        }
        return undefined  // file found but schema not in it
      }
      return undefined
    }
  } catch { /* fs unavailable or unreadable — same-file only */ }
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
  /** For .int(): emit Number.isInteger instead of a comparison. */
  isInt?: boolean
  /** For .regex(/.../flags): emit __reTest instead of a comparison. */
  regex?: { pattern: string; flags: string }
}

/**
 * Starting from position `start` (just after an opening paren), find the
 * matching closing paren, handling nested parens.  Returns -1 if not found.
 */
export function findBalancedParen(text: string, start: number): number {
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

export function extractConstraintsFromSchemaText(schemaText: string, varName: string): InferredContract[] {
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
    const chainMatch = /^((?:\.\w+(?:<[^>]*>)?\([^)]*\))*)/.exec(rest)
    const chainText = chainMatch?.[1] ?? ''

    extractChainConstraints(fieldName, baseType, chainText, constraints)
  }

  // Discriminated unions: z.discriminatedUnion('kind', [z.object({...}), ...])
  // Each variant's field constraints become CONDITIONAL facts:
  //   x.kind === 'pix'  ==>  x.amount > 0
  // plus the domain fact: x.kind is one of the declared literals.
  const duMatch = /z\.discriminatedUnion\(\s*['"](\w+)['"]\s*,\s*\[/.exec(schemaText)
  if (duMatch) {
    const key = duMatch[1]!
    const bodyStart = duMatch.index + duMatch[0].length
    const variants = splitBalancedItems(schemaText.slice(bodyStart))
    const kindValues: string[] = []
    const conditional: Array<{ value: string; cs: FieldConstraint[] }> = []
    for (const variantText of variants) {
      const litMatch = new RegExp(`${key}\\s*:\\s*z\\.literal\\(\\s*['"]([^'"]+)['"]`).exec(variantText)
      if (litMatch === null) continue
      kindValues.push(litMatch[1]!)
      const cs: FieldConstraint[] = []
      const fieldPattern = /(\w+)\s*:\s*z\.(number|string|array)\s*\(/g
      let fm: RegExpExecArray | null
      while ((fm = fieldPattern.exec(variantText)) !== null) {
        const closeIdx2 = findBalancedParen(variantText, fm.index + fm[0].length)
        if (closeIdx2 === -1) continue
        const chain = /^((?:\.\w+(?:<[^>]*>)?\([^)]*\))*)/.exec(variantText.slice(closeIdx2 + 1))?.[1] ?? ''
        extractChainConstraints(fm[1]!, fm[2]!, chain, cs)
      }
      conditional.push({ value: litMatch[1]!, cs })
    }
    if (kindValues.length >= 2) {
      const out: InferredContract[] = []
      const kindExpr: Expr = { kind: 'member', object: { kind: 'ident', name: varName }, property: key }
      // domain: kind ∈ {values}
      const eqs: Expr[] = kindValues.map(v => ({ kind: 'binary', op: '===', left: kindExpr, right: { kind: 'literal', value: v } }))
      out.push({
        kind: 'requires',
        text: `${varName}.${key} in {${kindValues.join(', ')}}`,
        predicate: eqs.reduce((a, b) => ({ kind: 'binary', op: '||', left: a, right: b })),
        confidence: 'guard',
        source: `from Zod schema: z.discriminatedUnion('${key}', ...)`,
      })
      // conditional per-variant field facts
      for (const { value, cs } of conditional) {
        const guard: Expr = { kind: 'binary', op: '===', left: kindExpr, right: { kind: 'literal', value } }
        for (const contract of constraintsToContracts(cs, varName)) {
          if (typeof contract.predicate === 'string') continue
          out.push({
            ...contract,
            text: `${varName}.${key} === '${value}' ==> ${contract.text}`,
            predicate: { kind: 'binary', op: '==>', left: guard, right: contract.predicate },
          })
        }
      }
      return out
    }
  }

  // Also handle top-level (non-object) schemas: z.number().positive().parse(x)
  // In this case the schema itself is the chain with no field name.
  if (constraints.length === 0) {
    const topLevelPattern = /^z\.(number|string|array)\s*\([^)]*\)((?:\.\w+(?:<[^>]*>)?\([^)]*\))*)$/
    const topMatch = topLevelPattern.exec(schemaText)
    if (topMatch) {
      const baseType = topMatch[1]!
      const chainText = topMatch[2] ?? ''
      // For top-level schemas, the varName itself is the constrained value
      extractChainConstraints(null, baseType, chainText, constraints)
    }
  }

  // Convert field constraints to InferredContracts
  return constraintsToContracts(constraints, varName)
}

function constraintsToContracts(constraints: FieldConstraint[], varName: string): InferredContract[] {
  return constraints.map(c => {
    if (c.regex !== undefined) {
      const strExpr = buildFieldExpr(varName, c.field, false)
      const target = c.field ? `${varName}.${c.field}` : varName
      return {
        kind: 'requires' as const,
        text: `/${c.regex.pattern}/${c.regex.flags}.test(${target})`,
        predicate: {
          kind: 'call' as const,
          callee: '__reTest',
          args: [strExpr, { kind: 'literal' as const, value: c.regex.pattern }, { kind: 'literal' as const, value: c.regex.flags }],
        },
        confidence: 'guard' as const,
        source: `from Zod schema: ${c.source}`,
      }
    }
    if (c.isInt) {
      const intExpr = buildFieldExpr(varName, c.field, false)
      return {
        kind: 'requires' as const,
        text: `Number.isInteger(${c.field ? `${varName}.${c.field}` : varName})`,
        predicate: { kind: 'call' as const, callee: 'Number.isInteger', args: [intExpr] },
        confidence: 'guard' as const,
        source: `from Zod schema: ${c.source}`,
      }
    }
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
    if (/\.int\(\)/.test(chainText)) {
      out.push({ field, op: '>=', value: 0, isLength: false, source: 'z.number().int()', isInt: true })
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
    // .email(): SOUND superset of Zod's validation — nonempty local@domain,
    // no spaces/extra @. Every Zod-valid email is in this language.
    if (/\.email\(\)/.test(chainText)) {
      out.push({
        field, op: '>=', value: 0, isLength: false,
        regex: { pattern: '^[^@\\s]+@[^@\\s]+$', flags: '' },
        source: 'z.string().email()',
      })
    }
    // .uuid(): the exact shape (both hex cases allowed)
    if (/\.uuid\(\)/.test(chainText)) {
      out.push({
        field, op: '>=', value: 0, isLength: false,
        regex: { pattern: '^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$', flags: '' },
        source: 'z.string().uuid()',
      })
    }
    // .regex(/pattern/flags) — becomes a Z3 regular-expression membership fact
    const regexMatch = /\.regex\(\s*\/((?:[^/\\\n]|\\.)*)\/([a-z]*)\s*\)/.exec(chainText)
    if (regexMatch) {
      out.push({
        field, op: '>=', value: 0, isLength: false,
        regex: { pattern: regexMatch[1]!, flags: regexMatch[2] ?? '' },
        source: `z.string().regex(/${regexMatch[1]!}/${regexMatch[2] ?? ''})`,
      })
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

export function buildFieldExpr(varName: string, field: string, isLength: boolean): Expr {
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

export function buildText(varName: string, field: string, op: string, value: number, isLength: boolean): string {
  const base = field ? `${varName}.${field}` : varName
  const prop = isLength ? `${base}.length` : base
  return `${prop} ${op} ${value}`
}

// ---------------------------------------------------------------------------
// .refine() invariants — cross-field predicates lifted from schema chains
// ---------------------------------------------------------------------------

/** A cross-field invariant extracted from `.refine(arrow)` on a schema. */
export interface RefineInvariant {
  /** Simple param (`t => t.a === t.b`) or destructured names (`({a, b}) => a === b`). */
  binding: { kind: 'param'; name: string } | { kind: 'destructured'; names: string[] }
  predicate: Expr
  /** Original arrow text, for reporting. */
  text: string
}

let refineProject: Project | null = null

function getRefineProject(): Project {
  if (refineProject === null) {
    refineProject = new Project({
      useInMemoryFileSystem: true,
      skipFileDependencyResolution: true,
      compilerOptions: { strict: false, skipLibCheck: true },
    })
  }
  return refineProject
}

/**
 * Finds every top-level `.refine(...)` in a schema chain and parses the
 * predicate arrow into IR. `superRefine` is skipped (imperative — can't lift).
 */
export function extractRefinePredicates(schemaText: string): RefineInvariant[] {
  return extractArrowPredicates(schemaText, '.refine(')
}

/**
 * Generic arrow-predicate extraction for any `<marker>arrow...)` pattern —
 * `.refine(` for Zod, `filter(` for Effect Schema.
 */
export function extractArrowPredicates(schemaText: string, marker: string): RefineInvariant[] {
  const out: RefineInvariant[] = []
  let idx = 0

  while ((idx = schemaText.indexOf(marker, idx)) !== -1) {
    const argStart = idx + marker.length
    const close = findBalancedParen(schemaText, argStart)
    if (close === -1) break
    const argText = schemaText.slice(argStart, close)
    idx = close

    try {
      const file = getRefineProject().createSourceFile('__refine__.ts', `__r(${argText})`, { overwrite: true })
      const call = file.getFirstDescendantByKind(SyntaxKind.CallExpression)
      const arrow = call?.getArguments()[0]
      if (!arrow || !Node.isArrowFunction(arrow)) continue

      const params = arrow.getParameters()
      if (params.length !== 1) continue
      const paramNode = params[0]!.getNameNode()

      let binding: RefineInvariant['binding'] | null = null
      if (Node.isIdentifier(paramNode)) {
        binding = { kind: 'param', name: paramNode.getText() }
      } else if (Node.isObjectBindingPattern(paramNode)) {
        const names: string[] = []
        for (const el of paramNode.getElements()) {
          names.push(el.getNameNode().getText())
        }
        binding = { kind: 'destructured', names }
      }
      if (binding === null) continue

      const bodyNode = arrow.getBody()
      let exprNode: Expression | null = null
      if (Node.isExpression(bodyNode)) {
        exprNode = bodyNode as Expression
      } else if (Node.isBlock(bodyNode)) {
        const stmts = bodyNode.getStatements()
        if (stmts.length === 1 && Node.isReturnStatement(stmts[0]!)) {
          exprNode = (stmts[0]! as import('ts-morph').ReturnStatement).getExpression() ?? null
        }
      }
      if (exprNode === null) continue

      const predicate = parseExpr(exprNode)
      if (predicate === null) continue

      out.push({ binding, predicate, text: arrow.getText() })
    } catch { /* unparseable refine — skip */ }
  }

  return out
}

/**
 * Binds a refine invariant's predicate to a concrete target expression:
 * the parse-result variable (`order`) or `output()` for producer functions.
 */
export function bindRefineInvariant(inv: RefineInvariant, target: Expr): Expr {
  const mapping = new Map<string, Expr>()
  if (inv.binding.kind === 'param') {
    mapping.set(inv.binding.name, target)
  } else {
    for (const name of inv.binding.names) {
      mapping.set(name, { kind: 'member', object: target, property: name })
    }
  }
  return substituteExpr(inv.predicate, mapping)
}

// ---------------------------------------------------------------------------
// File-level schema scan — schemas with invariants + type aliases
// ---------------------------------------------------------------------------

export interface FileSchemaInvariants {
  /** schema variable name → its refine invariants */
  schemas: Map<string, RefineInvariant[]>
  /** type alias name → schema variable name (via z.output/z.infer<typeof S>) */
  aliases: Map<string, string>
}

/**
 * Scans a file for schema declarations carrying `.refine()` invariants and
 * for type aliases derived from them (`type T = z.output<typeof S>`).
 */
export function extractSchemaInvariantsFromFile(file: SourceFile): FileSchemaInvariants {
  const schemas = new Map<string, RefineInvariant[]>()
  const aliases = new Map<string, string>()

  for (const decl of file.getDescendantsOfKind(SyntaxKind.VariableDeclaration)) {
    const init = decl.getInitializer()
    if (!init) continue
    const text = init.getText()
    if (!text.startsWith('z.') || !text.includes('.refine(')) continue
    const invs = extractRefinePredicates(text)
    if (invs.length > 0) schemas.set(decl.getName(), invs)
  }

  for (const alias of file.getTypeAliases()) {
    const m = /z\.(?:output|infer|input)<\s*typeof\s+(\w+)\s*>/.exec(alias.getTypeNode()?.getText() ?? '')
    if (m) aliases.set(alias.getName(), m[1]!)
  }

  // Aliases referencing schemas imported from other files
  for (const schemaName of new Set(aliases.values())) {
    if (schemas.has(schemaName)) continue
    const importedText = resolveImportedSchema(file, schemaName)
    if (importedText !== undefined && importedText.includes('.refine(')) {
      const invs = extractRefinePredicates(importedText)
      if (invs.length > 0) schemas.set(schemaName, invs)
    }
  }

  return { schemas, aliases }
}

/**
 * Splits the items of an array literal text (starting after '[') at top-level
 * commas, stopping at the matching ']'. Paren/brace/bracket aware.
 */
function splitBalancedItems(s: string): string[] {
  const items: string[] = []
  let depth = 0
  let start = 0
  for (let i = 0; i < s.length; i++) {
    const ch = s[i]
    if (ch === '(' || ch === '{' || ch === '[') depth++
    else if (ch === ')' || ch === '}') depth--
    else if (ch === ']') {
      if (depth === 0) { items.push(s.slice(start, i).trim()); break }
      depth--
    } else if (ch === ',' && depth === 0) {
      items.push(s.slice(start, i).trim())
      start = i + 1
    }
  }
  return items.filter(t => t.length > 0)
}
