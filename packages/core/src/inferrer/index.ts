import { Project, SyntaxKind, Node, type SourceFile, type Block } from 'ts-morph'
import type { Expr, Param, Sort, FunctionIR } from '../parser/ir.js'
import { getContext } from '../solver/context.js'
import type { Z3Context } from '../solver/context.js'
import { extractGuardsFromBlock } from './guards.js'
import { analyzeBodyExpr } from './body.js'
import { extractArithmeticFromBlock } from './arithmetic.js'
import { extractNullSafetyFromNode } from './null-safety.js'
import { extractArraySafetyFromBlock } from './array-safety.js'
import { analyzeReturns } from './returns.js'
import { extractRelations } from './relations.js'
import { verifyCandidates } from './candidates.js'
import { buildCallGraph, propagateContracts } from './propagation.js'
import { extractFunctionsFromSource } from '../parser/extractor.js'
import { parseExpr } from '../parser/expr.js'
import { parseBlockToExpr } from '../parser/expr.js'

// Re-export writer utilities
export { generateDeclareFile, generateReport } from './writer.js'
export type { WriterOptions } from './writer.js'

// Public types
export type Confidence = 'proven' | 'guard' | 'derived' | 'propagated' | 'heuristic'

export interface InferredContract {
  kind: 'requires' | 'ensures'
  text: string
  predicate: Expr
  confidence: Confidence
  source: string
}

export interface InferredFunction {
  name: string
  params: Param[]
  returnSort: Sort
  contracts: InferredContract[]
}

export interface InferResult {
  functions: InferredFunction[]
  durationMs: number
}

export interface InferOptions {
  /** Enable Z3-powered verification of ensures candidates (slower, can crash on complex code). Default: false */
  prove?: boolean | undefined
  /** External contract registry (from @theoremts/contracts-* packages). Used for cross-library propagation. */
  registry?: import('../registry/index.js').ContractRegistry | undefined
}

// ---------------------------------------------------------------------------
// AST function discovery — finds ALL functions at any depth
// ---------------------------------------------------------------------------

interface DiscoveredFunction {
  name: string
  body: Block
  node: Node
  params: Array<{ name: string; sort: Sort; isNullable: boolean }>
  returnSort: Sort
}

function inferSort(typeText: string | undefined): Sort {
  if (!typeText) return 'real' // default — most params are numeric in contracts
  const t = typeText.trim()
  if (t === 'number') return 'real'
  if (t === 'bigint') return 'int'
  if (t === 'boolean') return 'bool'
  if (t === 'string') return 'string'
  return 'unknown'
}

function isNullableType(typeText: string | undefined): boolean {
  if (!typeText) return false
  return typeText.includes('null') || typeText.includes('undefined')
}

function discoverFunctions(sourceFile: SourceFile): DiscoveredFunction[] {
  const results: DiscoveredFunction[] = []

  // Recursively walk ALL nodes
  sourceFile.forEachDescendant(node => {
    let name: string | undefined
    let body: Block | undefined
    let paramNodes: any[] = []
    let returnTypeText: string | undefined

    // Named function declarations: function foo() { ... }
    if (Node.isFunctionDeclaration(node)) {
      name = node.getName()
      const b = node.getBody()
      if (b && Node.isBlock(b)) body = b
      paramNodes = node.getParameters()
      returnTypeText = node.getReturnTypeNode()?.getText()
    }

    // Variable declarations: const foo = (...) => { ... } or const foo = function(...) { ... }
    if (Node.isVariableDeclaration(node)) {
      name = node.getName()
      const init = node.getInitializer()
      if (init && (Node.isArrowFunction(init) || Node.isFunctionExpression(init))) {
        const b = (init as any).getBody()
        if (b && Node.isBlock(b)) {
          body = b
        }
        paramNodes = (init as any).getParameters()
        returnTypeText = (init as any).getReturnTypeNode()?.getText()
      }
    }

    // Method declarations inside classes: class Foo { bar() { ... } }
    if (Node.isMethodDeclaration(node)) {
      name = node.getName()
      const b = node.getBody()
      if (b && Node.isBlock(b)) body = b
      paramNodes = node.getParameters()
      returnTypeText = node.getReturnTypeNode()?.getText()
    }

    if (!name || !body) return

    // Extract param info
    const params = paramNodes.map((p: any) => {
      const paramName = p.getName?.() ?? '_'
      const typeText = p.getTypeNode?.()?.getText()
      const hasQuestion = p.hasQuestionToken?.() ?? false
      return {
        name: paramName,
        sort: inferSort(typeText),
        isNullable: hasQuestion || isNullableType(typeText),
      }
    })

    results.push({
      name,
      body,
      node,
      params,
      returnSort: inferSort(returnTypeText),
    })
  })

  return results
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

export async function inferContracts(source: string, fileName = 'input.ts', options?: InferOptions): Promise<InferResult> {
  const t0 = Date.now()
  const prove = options?.prove ?? false

  // Create ts-morph project
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  const sourceFile = project.createSourceFile(fileName, source, { overwrite: true })

  // Discover ALL functions at any depth
  const discovered = discoverFunctions(sourceFile)

  // Only initialize Z3 if needed
  let ctx: Z3Context | null = null
  if (prove) {
    try { ctx = await getContext() } catch { /* Z3 unavailable */ }
  }

  // Also extract IR for Z3-powered analysis (only when proving)
  let irMap: Map<string, FunctionIR> | null = null
  if (ctx) {
    try {
      const irs = extractFunctionsFromSource(source, fileName)
      irMap = new Map(irs.filter(ir => ir.name).map(ir => [ir.name!, ir]))
    } catch { /* extraction failure — skip Z3 analysis */ }
  }

  const functions: InferredFunction[] = []

  for (const fn of discovered) {
    try {
      const contracts: InferredContract[] = []

      // ── Non-Z3 strategies — work directly on AST ──────────────────

      // Strategy 1: Guard extraction (requires from if/throw)
      contracts.push(...extractGuardsFromBlock(fn.body))

      // Strategy 3: Arithmetic safety (requires from div/mod/sqrt/log)
      const arithmeticContracts = extractArithmeticFromBlock(fn.body)
      const existingTexts = new Set(contracts.map(c => c.text))
      contracts.push(...arithmeticContracts.filter(c => !existingTexts.has(c.text)))

      // Strategy 5: Null safety
      contracts.push(...extractNullSafetyFromNode(fn.params, fn.body))

      // Strategy 6: Array safety
      contracts.push(...extractArraySafetyFromBlock(fn.body))

      // ── Z3-powered strategies (opt-in) ────────────────────────────

      if (ctx && irMap) {
        const ir = irMap.get(fn.name)
        if (ir && ir.returnSort !== 'unknown') {
          const requires = contracts.filter(c => c.kind === 'requires')

          // Strategy 2: Body analysis
          contracts.push(...await analyzeBodyExpr(ir, ctx, requires))

          // Strategy 7: Return type analysis
          const returnCandidates = await analyzeReturns(ir, ctx, requires)

          // Strategy 8: Relational contracts
          const relationCandidates = await extractRelations(ir, ctx, requires)

          // Verify candidates
          const mergedCandidates: InferredContract[] = []
          const seenTexts = new Set(contracts.map(c => c.text))
          for (const c of [...returnCandidates, ...relationCandidates]) {
            if (!seenTexts.has(c.text)) {
              seenTexts.add(c.text)
              mergedCandidates.push(c)
            }
          }
          if (mergedCandidates.length > 0) {
            contracts.push(...await verifyCandidates(mergedCandidates, ir, ctx, requires))
          }
        }
      }

      const irParams: Param[] = fn.params.map(p => ({ name: p.name, sort: p.sort }))

      functions.push({
        name: fn.name,
        params: irParams,
        returnSort: fn.returnSort,
        contracts,
      })
    } catch {
      continue
    }
  }

  // Cross-function propagation (includes external registry from contracts packages)
  try {
    const callGraph = buildCallGraph(functions, source, fileName, options?.registry)
    const propagated = propagateContracts(functions, callGraph, source, fileName, options?.registry)
    functions.length = 0
    functions.push(...propagated)
  } catch { /* keep as-is */ }

  return {
    functions: functions.filter(f => f.contracts.length > 0),
    durationMs: Date.now() - t0,
  }
}
