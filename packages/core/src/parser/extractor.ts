import {
  Node,
  Project,
  SyntaxKind,
  type CallExpression,
  type ArrowFunction,
  type Expression,
  type Statement,
  type VariableDeclaration,
  type FunctionDeclaration,
  type MethodDeclaration,
  type SourceFile,
} from 'ts-morph'
import type { BodyStep, Contract, Expr, FunctionIR, HeapStep, LoopInfo, Param, Predicate, Sort } from './ir.js'
import { parseExpr, parseBlockToExpr, parseBlockWithLoops, parseStmtListDirect, getResolvedPositionalContracts, getFinalSSABindings } from './expr.js'
import { substituteExpr } from '../translator/substitution.js'
import {
  extractZodContracts,
  extractSchemaInvariantsFromFile,
  bindRefineInvariant,
  extractConstraintsFromSchemaText,
  extractRefinePredicates,
  resolveImportedSchema,
} from '../inferrer/zod.js'
import {
  extractEffectContracts,
  extractEffectSchemaInvariantsFromFile,
  extractEffectConstraintsFromSchemaText,
  extractEffectFilterInvariants,
} from '../inferrer/effect-schema.js'

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/**
 * Extracts contract declarations from `declare(target, arrowFn)` calls
 * found in `.contracts.ts` files.
 *
 * Example:
 *   declare(Math.sqrt, (x: number): number => {
 *     requires(x >= 0)
 *     ensures(nonNegative(output()))
 *   })
 *
 * Returns FunctionIR[] with name set to the target text (e.g. "Math.sqrt").
 */
export function extractDeclareContracts(source: string, fileName = 'input.ts'): FunctionIR[] {
  const file = makeFile(source, fileName)
  const results: FunctionIR[] = []

  for (const call of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const callee = call.getExpression().getText()
    if (callee !== 'declare') continue

    const args = call.getArguments()
    if (args.length < 2) continue

    // First argument: the target function (e.g. Math.sqrt, getBalance)
    const targetName = args[0]!.getText()

    // Second argument: the arrow function with contracts
    const contractArg = args[1]!
    if (!Node.isArrowFunction(contractArg)) continue

    const arrow = contractArg as ArrowFunction
    const params = extractParams(arrow)
    const returnSort = inferReturnSort(arrow)

    // Extract contracts from the arrow body
    const contracts: Contract[] = []
    const arrowBody = arrow.getBody()

    if (Node.isBlock(arrowBody)) {
      for (const s of (arrowBody as any).getStatements() as Statement[]) {
        if (Node.isExpressionStatement(s)) {
          const expr = s.getExpression()
          if (Node.isCallExpression(expr)) {
            const contract = tryExtractContract(expr as Expression)
            if (contract !== null) contracts.push(contract)
          }
        }
      }
    }

    if (contracts.length === 0) continue

    results.push({
      name: targetName,
      params,
      returnSort,
      body: undefined,
      contracts,
    })
  }

  return results
}

/**
 * Parses a TypeScript source file and returns one FunctionIR for every
 * `proof(fn, ...contracts)` or `proof.fn(thunk, ...contracts)` call found.
 */
export function extractFromSource(source: string, fileName = 'input.ts', registry?: import('../registry/index.js').ContractRegistry): FunctionIR[] {
  const file = makeFile(source, fileName)
  const results: FunctionIR[] = []

  // 1. Explicit proof() / proof.fn() wrappers
  for (const call of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const ir = tryExtractProof(call) ?? tryExtractProofFn(call)
    if (ir !== null) results.push(ir)
  }

  // 2. Inline contracts: functions with requires()/ensures() in their body
  const proofNames = new Set(results.map(r => r.name).filter(Boolean))
  for (const ir of extractInlineContracts(file, proofNames as Set<string>)) {
    results.push(ir)
  }

  // 3. Decorated class methods: @requires(...) / @ensures(...)
  for (const ir of extractDecoratedMethods(file, proofNames as Set<string>)) {
    results.push(ir)
  }

  // 3b. Schema invariants: a function whose declared return type derives from
  //     a schema with .refine() invariants must PROVE those invariants on its
  //     output — the schema-first equivalent of a class invariant.
  try {
    attachSchemaInvariantObligations(file, source, fileName, results)
  } catch { /* best-effort */ }

  // 3c. tRPC procedures: `t.procedure.input(Schema).mutation(handler)` —
  //     the input schema's constraints hold inside the handler (tRPC
  //     validates before invoking it).
  try {
    for (const ir of extractTrpcProcedures(file)) results.push(ir)
  } catch { /* best-effort */ }

  // 3d. Refinement types: a parameter typed with a schema-derived alias
  //     (`type Rate = z.output<typeof RateSchema>`) carries the schema's
  //     constraints as REQUIRES — assumed inside the function, and proved by
  //     callers through the existing call-site checker.
  try {
    attachParamRefinements(file, source, fileName, results)
  } catch { /* best-effort */ }

  // 3e. Spec-function definitions: every pure same-file function whose body
  //     folds to an expression is available for unfolding inside contract
  //     predicates (translator/spec-unfold.ts). Attached to every IR.
  try {
    const specDefs = collectSpecDefs(source, fileName)
    if (specDefs.size > 0) {
      for (const ir of results) ir.specDefs = specDefs
    }
    const footprints = collectFootprints(file)
    if (footprints.size > 0) {
      for (const ir of results) ir.footprints = footprints
    }
  } catch { /* best-effort */ }

  // 4. Declared contracts: if registry has contracts for functions in this file,
  //    extract the function body and attach the declared contracts.
  //    This allows `declare(fn, ...)` in a .contracts.ts file to be verified
  //    against the actual implementation.
  if (registry && registry.size > 0) {
    const existingNames = new Set(results.map(r => r.name).filter(Boolean))
    const allFunctions = extractFunctionsFromSource(source, fileName)
    for (const fn of allFunctions) {
      if (!fn.name || existingNames.has(fn.name)) continue
      const contract = registry.get(fn.name)
      if (!contract) continue
      // Merge: implementation body + declared contracts
      const contracts: Contract[] = [
        ...contract.requires.map(p => ({ kind: 'requires' as const, predicate: p })),
        ...contract.ensures.map(p => ({ kind: 'ensures' as const, predicate: p })),
      ]
      results.push({
        name: fn.name,
        params: fn.params,
        returnSort: fn.returnSort,
        body: fn.body,
        contracts,
      })
    }
  }

  return results
}

/**
 * Extracts ALL top-level functions from a source file (no proof() wrapper needed).
 * Used by `theorem scan` to analyse unannotated code.
 */
export function extractFunctionsFromSource(source: string, fileName = 'input.ts'): FunctionIR[] {
  const file = makeFile(source, fileName)
  const results: FunctionIR[] = []

  for (const stmt of file.getStatements()) {
    // const foo = (params) => body
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarations()) {
        const init = decl.getInitializer()
        if (!Node.isArrowFunction(init)) continue
        const params = extractParams(init)
        const fnBody = init.getBody()
        const body = Node.isExpression(fnBody)
          ? (parseExpr(fnBody) ?? undefined)
          : Node.isBlock(fnBody)
            ? (parseBlockToExpr(fnBody) ?? undefined)
            : undefined
        results.push({
          name: decl.getName(),
          params,
          returnSort: inferReturnSort(init),
          body,
          contracts: [],
        })
      }
    }

    // function foo(params) { body }
    if (Node.isFunctionDeclaration(stmt)) {
      const fnDecl = stmt as FunctionDeclaration
      const fnBody = fnDecl.getBody()
      const body = fnBody && Node.isBlock(fnBody) ? (parseBlockToExpr(fnBody) ?? undefined) : undefined
      results.push({
        name: fnDecl.getName() ?? undefined,
        params: extractFunctionDeclParams(fnDecl),
        returnSort: inferFunctionDeclReturnSort(fnDecl),
        body,
        contracts: [],
      })
    }
  }

  return results
}

// ---------------------------------------------------------------------------
// proof(arrowFn, ...contracts)
// ---------------------------------------------------------------------------

function tryExtractProof(call: CallExpression): FunctionIR | null {
  const callee = call.getExpression().getText()
  if (callee !== 'proof') return null

  const args = call.getArguments()
  if (args.length < 2) return null

  const firstArg = args[0]

  // Resolve the function — either an inline arrow or a named function reference
  let fnNode: ArrowFunction | FunctionDeclaration | undefined
  let resolvedName: string | undefined

  if (Node.isArrowFunction(firstArg)) {
    fnNode = firstArg
  } else if (Node.isFunctionExpression(firstArg)) {
    // Treat FunctionExpression like ArrowFunction for extraction purposes
    fnNode = firstArg as unknown as ArrowFunction
  } else if (Node.isIdentifier(firstArg)) {
    // proof(namedFn, requires(...)) — resolve identifier to its declaration
    resolvedName = firstArg.getText()
    const sourceFile = call.getSourceFile()

    // Try function declaration: function foo() { ... }
    const fnDecl = sourceFile.getFunction(resolvedName)
    if (fnDecl) {
      fnNode = fnDecl as unknown as ArrowFunction
    }

    // Try variable declaration: const foo = (...) => { ... }
    if (!fnNode) {
      const varDecl = sourceFile.getVariableDeclaration(resolvedName)
      if (varDecl) {
        const init = varDecl.getInitializer()
        if (init && (Node.isArrowFunction(init) || Node.isFunctionExpression(init))) {
          fnNode = init as ArrowFunction
        }
      }
    }
  }

  if (!fnNode) return null

  const isFnDecl = Node.isFunctionDeclaration(fnNode as any)
  const params = isFnDecl
    ? extractFunctionDeclParams(fnNode as unknown as FunctionDeclaration)
    : extractParams(fnNode as ArrowFunction)
  const contracts: Contract[] = []

  for (const arg of args.slice(1)) {
    const contract = tryExtractContract(arg as Expression)
    if (contract !== null) contracts.push(contract)
  }

  const fnBody = (fnNode as any).getBody()
  let body: FunctionIR['body']
  let loops: LoopInfo[] | undefined

  if (fnBody && Node.isExpression(fnBody)) {
    body = parseExpr(fnBody) ?? undefined
  } else if (fnBody && Node.isBlock(fnBody)) {
    const result = parseBlockWithLoops(fnBody)
    body = result.body ?? undefined
    loops = result.loops.length > 0 ? result.loops : undefined
  }

  return {
    name: resolvedName ?? inferName(call),
    params,
    returnSort: isFnDecl
      ? inferFunctionDeclReturnSort(fnNode as unknown as FunctionDeclaration)
      : inferReturnSort(fnNode as ArrowFunction),
    body,
    contracts,
    loops,
  }
}

// ---------------------------------------------------------------------------
// proof.fn(thunk, ...contracts)  — thunk is () => body; params from enclosing fn
// ---------------------------------------------------------------------------

function tryExtractProofFn(call: CallExpression): FunctionIR | null {
  const calleeExpr = call.getExpression()
  if (!Node.isPropertyAccessExpression(calleeExpr)) return null
  if (calleeExpr.getExpression().getText() !== 'proof') return null
  if (calleeExpr.getName() !== 'fn') return null

  const args = call.getArguments()
  if (args.length < 1) return null

  const thunk = args[0]
  if (!Node.isArrowFunction(thunk)) return null

  // Walk up to find the enclosing function / method declaration
  const enclosing = findEnclosingFunctionDecl(call)
  if (enclosing === null) return null

  const params = extractFunctionDeclParams(enclosing)
  const contracts: Contract[] = []

  for (const arg of args.slice(1)) {
    const contract = tryExtractContract(arg as Expression)
    if (contract !== null) contracts.push(contract)
  }

  const thunkBody = (thunk as ArrowFunction).getBody()
  let body: FunctionIR['body']
  let loops: LoopInfo[] | undefined

  if (Node.isExpression(thunkBody)) {
    body = parseExpr(thunkBody) ?? undefined
  } else if (Node.isBlock(thunkBody)) {
    const result = parseBlockWithLoops(thunkBody)
    body = result.body ?? undefined
    loops = result.loops.length > 0 ? result.loops : undefined
  }

  return {
    name: enclosing.getName() ?? undefined,
    params,
    returnSort: inferFunctionDeclReturnSort(enclosing),
    body,
    contracts,
    loops,
  }
}

// ---------------------------------------------------------------------------
// Inline contracts: requires()/ensures() inside function bodies (no proof())
//
//   function safeDivide(a: number, b: number): number {
//     requires(() => b > 0)
//     ensures((result) => result === a / b)
//     return a / b
//   }
// ---------------------------------------------------------------------------
// Decorated class methods: @requires(...) / @ensures(...) on methods
// ---------------------------------------------------------------------------

function extractDecoratedMethods(
  file: ReturnType<typeof makeFile>,
  alreadyExtracted: Set<string>,
): FunctionIR[] {
  const results: FunctionIR[] = []

  for (const cls of file.getClasses()) {
    // Class-level @invariant decorators: predicates over instance fields,
    // normalized to `this.x` identifiers.
    const classInvariants: Expr[] = []
    for (const dec of cls.getDecorators()) {
      if (dec.getName() !== 'invariant') continue
      for (const arg of dec.getArguments()) {
        const pred = extractClassInvariantPredicate(arg as Expression)
        if (pred !== null) classInvariants.push(pred)
      }
    }

    for (const method of cls.getMethods()) {
      const name = method.getName()
      if (alreadyExtracted.has(name)) continue

      const decorators = method.getDecorators()
      if (decorators.length === 0 && classInvariants.length === 0) continue

      const contracts: Contract[] = []
      for (const dec of decorators) {
        const decName = dec.getName()
        const args = dec.getArguments()

        if (decName === 'requires') {
          for (const arg of args) {
            contracts.push({ kind: 'requires', predicate: extractPredicate(arg as Expression) })
          }
        } else if (decName === 'ensures') {
          for (const arg of args) {
            contracts.push({ kind: 'ensures', predicate: extractPredicate(arg as Expression) })
          }
        } else if (decName === 'invariant') {
          for (const arg of args) {
            contracts.push({ kind: 'invariant', predicate: extractPredicate(arg as Expression) })
          }
        }
      }

      const params = extractFunctionDeclParams(method)
      const fnBody = method.getBody()
      let body: FunctionIR['body']
      let loops: LoopInfo[] | undefined
      let finalBindings = new Map<string, Expr>()
      let heapSteps: HeapStep[] | undefined
      let heapRoots: string[] | undefined
      let unmodeledWrites: string[] | undefined

      if (fnBody && Node.isBlock(fnBody)) {
        // Inline contracts in the method body (requires/ensures as statements)
        for (const s of fnBody.getStatements()) {
          if (!Node.isExpressionStatement(s)) continue
          const contract = tryExtractContract(s.getExpression() as Expression)
          if (contract !== null) contracts.push(contract)
        }

        // Methods with loops route through the heap-mode machinery: `this.x`
        // becomes mutable numeric state (num-assign), so loop havoc + real
        // preservation checks apply. The SSA path cannot see through loops —
        // its exit-state invariant obligation would be checked against the
        // ENTRY state, proving trivially even for bodies that break it.
        if (fnBody.getDescendantsOfKind(SyntaxKind.WhileStatement).length > 0) {
          const steps = extractHeapStmtList(fnBody.getStatements(), 'top')
          if (steps !== null && steps.some(st => st.kind === 'loop')) {
            heapSteps = steps
            heapRoots = collectAllHeapRoots(steps, [
              ...contracts,
              ...classInvariants.map(inv => ({ kind: 'requires' as const, predicate: inv })),
            ])
          } else {
            unmodeledWrites = ['loop body could not be modeled — verification incomplete']
          }
        }

        if (heapSteps === undefined) {
          const result = parseBlockWithLoops(fnBody)
          body = result.body ?? undefined
          loops = result.loops.length > 0 ? result.loops : undefined
          finalBindings = getFinalSSABindings()
        }
      }

      if (contracts.length === 0 && classInvariants.length === 0) continue

      // Class invariants: assumed at entry, must hold over the final state
      // of `this.*` fields at exit. In heap mode the predicate is translated
      // against the final environment directly — no substitution needed.
      for (const inv of classInvariants) {
        contracts.push({ kind: 'requires', predicate: inv })
        contracts.push({
          kind: 'ensures',
          predicate: heapSteps === undefined && finalBindings.size > 0
            ? substituteExpr(inv, finalBindings)
            : inv,
        })
      }

      results.push({
        name,
        params,
        returnSort: inferFunctionDeclReturnSort(method),
        body,
        contracts,
        loops,
        heapSteps,
        heapRoots,
        unmodeledWrites,
      })
    }

    // Constructor: must ESTABLISH the invariant (no entry assumption)
    if (classInvariants.length > 0) {
      const ctor = cls.getConstructors()[0]
      if (ctor) {
        const fnBody = ctor.getBody()
        let finalBindings = new Map<string, Expr>()
        let body: FunctionIR['body']
        const contracts: Contract[] = []
        if (fnBody && Node.isBlock(fnBody)) {
          for (const s of fnBody.getStatements()) {
            if (!Node.isExpressionStatement(s)) continue
            const contract = tryExtractContract(s.getExpression() as Expression)
            if (contract !== null) contracts.push(contract)
          }
          body = parseBlockToExpr(fnBody) ?? undefined
          finalBindings = getFinalSSABindings()
        }
        contracts.push(...classInvariants.map(inv => ({
          kind: 'ensures' as const,
          predicate: finalBindings.size > 0 ? substituteExpr(inv, finalBindings) : inv,
        })))
        results.push({
          name: `${cls.getName() ?? 'anonymous'}.constructor`,
          params: ctor.getParameters().map(p => ({
            name: p.getName(),
            sort: 'real' as Sort,
          })),
          returnSort: 'real',
          body,
          contracts,
        })
      }
    }
  }

  return results
}

/**
 * Parses a class @invariant predicate arrow into an Expr over `this.*` fields:
 *   (self) => self.balance >= 0        → this.balance >= 0
 *   ({ balance }) => balance >= 0      → this.balance >= 0
 */
function extractClassInvariantPredicate(arg: Expression): Expr | null {
  if (!Node.isArrowFunction(arg)) return null
  const params = arg.getParameters()
  const bodyNode = arg.getBody()
  if (!Node.isExpression(bodyNode)) return null
  const parsed = parseExpr(bodyNode as Expression)
  if (parsed === null) return null
  if (params.length === 0) return parsed

  const nameNode = params[0]!.getNameNode()
  if (Node.isIdentifier(nameNode)) {
    // (self) => self.balance >= 0 — rebase member accesses on the param to this.*
    return rebaseParamToThis(parsed, nameNode.getText())
  }
  if (Node.isObjectBindingPattern(nameNode)) {
    const mapping = new Map<string, Expr>()
    for (const el of nameNode.getElements()) {
      const n = el.getNameNode().getText()
      mapping.set(n, { kind: 'ident', name: `this.${n}` })
    }
    return substituteExpr(parsed, mapping)
  }
  return parsed
}

/** Rewrites member(ident(param), p) → ident('this.p') recursively. */
function rebaseParamToThis(expr: Expr, param: string): Expr {
  switch (expr.kind) {
    case 'member':
      if (expr.object.kind === 'ident' && expr.object.name === param) {
        return { kind: 'ident', name: `this.${expr.property}` }
      }
      return { kind: 'member', object: rebaseParamToThis(expr.object, param), property: expr.property }
    case 'binary':
      return { kind: 'binary', op: expr.op, left: rebaseParamToThis(expr.left, param), right: rebaseParamToThis(expr.right, param) }
    case 'unary':
      return { kind: 'unary', op: expr.op, operand: rebaseParamToThis(expr.operand, param) }
    case 'ternary':
      return { kind: 'ternary', condition: rebaseParamToThis(expr.condition, param), then: rebaseParamToThis(expr.then, param), else: rebaseParamToThis(expr.else, param) }
    case 'call':
      return { kind: 'call', callee: expr.callee, args: expr.args.map(a => rebaseParamToThis(a, param)) }
    case 'element-access':
      return { kind: 'element-access', object: rebaseParamToThis(expr.object, param), index: rebaseParamToThis(expr.index, param) }
    default:
      return expr
  }
}

// ---------------------------------------------------------------------------

function extractInlineContracts(
  file: ReturnType<typeof makeFile>,
  alreadyExtracted: Set<string>,
): FunctionIR[] {
  const results: FunctionIR[] = []

  for (const stmt of file.getStatements()) {
    // function foo(...) { requires(...); ensures(...); ... }
    if (Node.isFunctionDeclaration(stmt)) {
      const name = stmt.getName()
      if (name && alreadyExtracted.has(name)) continue
      const ir = tryExtractInline(stmt)
      if (ir !== null) results.push(ir)
    }

    // export function foo(...) { ... } — also a FunctionDeclaration
    // const foo = (...) => { requires(...); ... }
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarations()) {
        const name = decl.getName()
        if (alreadyExtracted.has(name)) continue
        const init = decl.getInitializer()
        if (Node.isArrowFunction(init)) {
          const ir = tryExtractInlineArrow(init, name)
          if (ir !== null) results.push(ir)
        }
      }
    }
  }

  return results
}

/**
 * Attaches schema-invariant obligations to functions that produce values of a
 * schema-derived type: `type T = z.output<typeof S>` where S has `.refine()`
 * invariants means every function returning T must prove them on its output.
 * Functions without any other contracts get a fresh IR (they become
 * verifiable purely by returning the type).
 */
function attachSchemaInvariantObligations(
  file: SourceFile,
  source: string,
  fileName: string,
  results: FunctionIR[],
): void {
  const { schemas, aliases } = extractSchemaInvariantsFromFile(file)

  // Merge Effect Schema Struct/filter invariants and aliases
  const effect = extractEffectSchemaInvariantsFromFile(file)
  for (const [name, invs] of effect.schemas) {
    if (!schemas.has(name)) schemas.set(name, invs)
  }
  for (const [alias, schemaName] of effect.aliases) {
    if (!aliases.has(alias)) aliases.set(alias, schemaName)
  }

  if (schemas.size === 0) return

  const outputCall: Expr = { kind: 'call', callee: 'output', args: [] }
  const byName = new Map<string, FunctionIR>()
  for (const r of results) if (r.name) byName.set(r.name, r)

  let plainFunctions: FunctionIR[] | null = null

  for (const fnDecl of file.getFunctions()) {
    const name = fnDecl.getName()
    if (!name) continue
    const retText = fnDecl.getReturnTypeNode()?.getText()
    if (!retText) continue

    let schemaName = aliases.get(retText)
    if (!schemaName) {
      const m = /z\.(?:output|infer)<\s*typeof\s+(\w+)\s*>/.exec(retText)
        ?? /(?:\w+\.)?Schema\.Type<\s*typeof\s+(\w+)\s*>/.exec(retText)
        ?? /^typeof\s+(\w+)\.Type$/.exec(retText.trim())
      if (m) schemaName = m[1]!
    }
    if (!schemaName) continue

    const invs = schemas.get(schemaName)
    if (!invs || invs.length === 0) continue

    const ensures: Contract[] = invs.map(inv => ({
      kind: 'ensures' as const,
      predicate: bindRefineInvariant(inv, outputCall),
    }))

    const existing = byName.get(name)
    if (existing) {
      existing.contracts.push(...ensures)
      continue
    }

    // No inline contracts — the return type alone makes the function verifiable
    if (plainFunctions === null) plainFunctions = extractFunctionsFromSource(source, fileName)
    const plain = plainFunctions.find(f => f.name === name)
    if (plain) {
      results.push({ ...plain, contracts: ensures })
    }
  }
}

/**
 * Refinement types via schema-derived parameter types.
 *
 * `type Rate = z.output<typeof RateSchema>` (or `typeof S.Type` for Effect)
 * turns any parameter annotated `rate: Rate` into a refined value: the
 * schema's field constraints and refine/filter invariants become REQUIRES
 * contracts. Inside the function they are assumptions; at call sites the
 * existing checker obliges callers to PROVE them.
 */
function attachParamRefinements(
  file: SourceFile,
  source: string,
  fileName: string,
  results: FunctionIR[],
): void {
  // alias name → schema name (both Zod and Effect idioms)
  const aliases = new Map<string, string>()
  for (const alias of file.getTypeAliases()) {
    const typeText = alias.getTypeNode()?.getText() ?? ''
    const m = /z\.(?:output|infer)<\s*typeof\s+(\w+)\s*>/.exec(typeText)
      ?? /(?:\w+\.)?Schema\.Type<\s*typeof\s+(\w+)\s*>/.exec(typeText)
      ?? /^typeof\s+(\w+)\.Type$/.exec(typeText.trim())
    if (m) aliases.set(alias.getName(), m[1]!)
  }
  if (aliases.size === 0) return

  const schemaTextOf = (schemaName: string): string | undefined =>
    file.getVariableDeclaration(schemaName)?.getInitializer()?.getText().trim()
      ?? resolveImportedSchema(file, schemaName)

  const byName = new Map<string, FunctionIR>()
  for (const r of results) if (r.name) byName.set(r.name, r)
  let plainFunctions: FunctionIR[] | null = null

  for (const fnDecl of file.getFunctions()) {
    const name = fnDecl.getName()
    if (!name) continue

    const refinements: Contract[] = []
    for (const param of fnDecl.getParameters()) {
      const typeText = param.getTypeNode()?.getText()
      if (!typeText) continue
      const schemaName = aliases.get(typeText)
      if (!schemaName) continue
      const schemaText = schemaTextOf(schemaName)
      if (!schemaText) continue

      const paramName = param.getName()
      // Zod first; Effect only when Zod finds nothing (avoids double-matching
      // shared method names like .positive() on the same chain)
      const zodConstraints = extractConstraintsFromSchemaText(schemaText, paramName)
      const constraints = zodConstraints.length > 0
        ? zodConstraints
        : extractEffectConstraintsFromSchemaText(schemaText, paramName)
      for (const c of constraints) {
        refinements.push({ kind: 'requires', predicate: c.predicate })
      }
      const invariants = [
        ...extractRefinePredicates(schemaText),
        ...extractEffectFilterInvariants(schemaText),
      ]
      for (const inv of invariants) {
        refinements.push({
          kind: 'requires',
          predicate: bindRefineInvariant(inv, { kind: 'ident', name: paramName }),
        })
      }
    }
    if (refinements.length === 0) continue

    const existing = byName.get(name)
    if (existing) {
      existing.contracts.push(...refinements)
      continue
    }

    // No other contracts — the refined parameter type alone makes the
    // function verifiable (and registers it for call-site checking).
    if (plainFunctions === null) plainFunctions = extractFunctionsFromSource(source, fileName)
    const plain = plainFunctions.find(f => f.name === name)
    if (plain) results.push({ ...plain, contracts: refinements })
  }
}

/**
 * Extracts tRPC procedure handlers:
 *   key: t.procedure.input(Schema).mutation(({ input }) => ...)
 *
 * tRPC validates `input` against the schema BEFORE invoking the handler, so
 * the schema's constraints (and refine/filter invariants) hold throughout the
 * handler body. Works for .mutation/.query/.subscription, Zod and Effect
 * Schema inputs, with .output(...) or other links between input and the
 * handler. Handler param must destructure `{ input }` (optionally renamed).
 */
function extractTrpcProcedures(file: SourceFile): FunctionIR[] {
  const results: FunctionIR[] = []

  for (const call of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    const callee = call.getExpression()
    if (!Node.isPropertyAccessExpression(callee)) continue
    const method = callee.getName()
    if (method !== 'mutation' && method !== 'query' && method !== 'subscription') continue

    // Walk down the chain looking for .input(Schema)
    let schemaArg: Expression | undefined
    let chainNode: Node = callee.getExpression()
    while (Node.isCallExpression(chainNode)) {
      const inner = chainNode.getExpression()
      if (!Node.isPropertyAccessExpression(inner)) break
      if (inner.getName() === 'input') {
        schemaArg = chainNode.getArguments()[0] as Expression | undefined
        break
      }
      chainNode = inner.getExpression()
    }
    if (schemaArg === undefined) continue

    // Resolve the schema text (identifier → declaration, possibly imported)
    let schemaText = schemaArg.getText().trim()
    if (Node.isIdentifier(schemaArg)) {
      const name = schemaArg.getText()
      const local = file.getVariableDeclaration(name)?.getInitializer()?.getText().trim()
      schemaText = local ?? resolveImportedSchema(file, name) ?? schemaText
    }

    // Handler arrow with destructured { input } (optionally renamed)
    const handler = call.getArguments()[0]
    if (!handler || !Node.isArrowFunction(handler)) continue
    const inputVar = trpcInputBindingName(handler)
    if (inputVar === null) continue

    // Constraints: try Zod patterns, then Effect Schema patterns
    const contracts: Contract[] = []
    const zodConstraints = extractConstraintsFromSchemaText(schemaText, inputVar)
    const effectConstraints = zodConstraints.length > 0 ? [] : extractEffectConstraintsFromSchemaText(schemaText, inputVar)
    for (const c of [...zodConstraints, ...effectConstraints]) {
      contracts.push({ kind: 'assume', predicate: c.predicate })
    }
    const invariants = [
      ...extractRefinePredicates(schemaText),
      ...extractEffectFilterInvariants(schemaText),
    ]
    for (const inv of invariants) {
      contracts.push({ kind: 'assume', predicate: bindRefineInvariant(inv, { kind: 'ident', name: inputVar }) })
    }
    if (contracts.length === 0) continue

    // Procedure name from the enclosing router key, if any
    const prop = call.getFirstAncestorByKind(SyntaxKind.PropertyAssignment)
    const name = prop?.getName() ?? `(trpc ${method})`

    // Parse the handler body
    const fnBody = handler.getBody()
    let body: FunctionIR['body']
    if (Node.isBlock(fnBody)) {
      body = parseStmtListToExpr(fnBody.getStatements()) ?? undefined
    } else if (Node.isExpression(fnBody)) {
      body = parseExpr(fnBody as Expression) ?? undefined
    }

    results.push({
      name,
      params: [],
      returnSort: 'real',
      body,
      contracts,
    })
  }

  return results
}

/** Name bound to tRPC's input in the handler: `({ input }) =>` or `({ input: order }) =>`. */
function trpcInputBindingName(handler: import('ts-morph').ArrowFunction): string | null {
  const param = handler.getParameters()[0]
  if (!param) return null
  const nameNode = param.getNameNode()
  if (!Node.isObjectBindingPattern(nameNode)) return null
  for (const el of nameNode.getElements()) {
    const propName = el.getPropertyNameNode()?.getText() ?? el.getNameNode().getText()
    if (propName === 'input') return el.getNameNode().getText()
  }
  return null
}

/**
 * Detects and extracts a heap-mode body: a straight-line sequence of locals
 * and field writes over object references (`from.value = from.value + x`).
 * Returns null when there are no non-this field writes; returns
 * { unsupported } when writes exist but the body shape can't be modeled
 * (branches, loops, calls) — the caller surfaces that as a visible warning.
 */
function tryExtractHeapSteps(
  stmts: Statement[],
  contracts: Contract[],
): { steps: HeapStep[]; roots: string[] } | { unsupported: string[] } | null {
  // First: are there field writes ANYWHERE (including nested in loops/ifs)?
  const allWrites: string[] = []
  for (const s of stmts) {
    for (const bin of [s, ...s.getDescendantsOfKind(SyntaxKind.BinaryExpression)]) {
      if (!Node.isBinaryExpression(bin) || bin.getOperatorToken().getText() !== '=') continue
      const left = bin.getLeft()
      if (Node.isPropertyAccessExpression(left)) {
        const base = writeBase(left)
        if (base !== null && base !== 'this') allWrites.push(left.getText())
      }
    }
  }
  if (allWrites.length === 0) {
    // No field writes — but a while loop (honest havoc machinery) or an
    // array sort (havoc + sortedness assumption) still needs heap mode.
    const hasWhile = stmts.some(s => Node.isWhileStatement(s))
    const hasSort = stmts.some(s =>
      Node.isExpressionStatement(s) && matchSortCall(s.getExpression()) !== null)
    if (!hasWhile && !hasSort) return null
    const extracted = extractHeapStmtList(stmts, 'top')
    if (extracted === null) return null
    if (!extracted.some(st => st.kind === 'loop' || st.kind === 'array-sort')) return null
    return { steps: extracted, roots: collectAllHeapRoots(extracted, contracts) }
  }

  const extracted = extractHeapStmtList(stmts, 'top')
  if (extracted === null || !hasFieldWrite(extracted)) return { unsupported: allWrites }
  const steps = extracted

  return { steps, roots: collectAllHeapRoots(steps, contracts) }
}

/** Roots: write bases + member objects + idents ref-compared against them. */
function collectAllHeapRoots(steps: HeapStep[], contracts: Contract[]): string[] {
  const roots = new Set<string>()
  collectHeapRoots(steps, roots)
  const predicates: Expr[] = []
  for (const c of contracts) {
    if (typeof c === 'object' && 'predicate' in c && typeof c.predicate !== 'string') {
      predicates.push(c.predicate)
    }
  }
  for (const p of predicates) collectMemberRoots(p, roots)
  // Second pass: bare idents equality-compared with known roots become roots
  // (e.g. `if (node === head) return` where only head is written)
  for (let pass = 0; pass < 2; pass++) {
    for (const p of predicates) collectRefComparisonRoots(p, roots)
    walkHeapExprs(steps, e => collectRefComparisonRoots(e, roots))
  }
  return [...roots]
}

/** Recursively extracts heap steps from a statement list; null = unsupported. */
function extractHeapStmtList(stmts: Statement[], context: 'top' | 'loop' | 'branch'): HeapStep[] | null {
  const topLevel = context === 'top'
  const steps: HeapStep[] = []

  for (const s of stmts) {
    if (Node.isReturnStatement(s)) {
      const returned = s.getExpression()
      if (returned !== undefined) {
        // A guarded value-return would need a path-conditioned result — bail
        if (!topLevel) return null
        const value = parseExpr(returned as Expression)
        if (value === null) return null
        steps.push({ kind: 'num-assign', name: '__result', value })
      }
      steps.push({ kind: 'exit' })
      break  // statements after return are dead code
    }

    if (Node.isExpressionStatement(s)) {
      const expr = s.getExpression()
      if (Node.isCallExpression(expr)) {
        const sort = matchSortCall(expr)
        if (sort !== null) {
          // Sorting inside a branch/loop would need path-conditioned havoc
          if (!topLevel) return null
          steps.push({ kind: 'array-sort', name: sort.name, sorted: sort.sorted })
        }
        continue  // other calls: check/assume — positional contracts
      }
      if (Node.isBinaryExpression(expr)) {
        const opText = expr.getOperatorToken().getText()
        const compound =
          opText === '+=' ? '+' : opText === '-=' ? '-' :
          opText === '*=' ? '*' : opText === '/=' ? '/' : null
        if (opText === '=' || compound !== null) {
          const left = expr.getLeft()
          const rhs = parseExpr(expr.getRight() as Expression)
          if (rhs === null) return null
          if (Node.isPropertyAccessExpression(left)) {
            const base = writeBase(left)
            if (base !== null && base !== 'this') {
              const objectExpr = parseExpr(left.getExpression() as Expression)
              const current = parseExpr(left as Expression)
              if (objectExpr === null || current === null) return null
              const value: Expr = compound === null
                ? rhs
                : { kind: 'binary', op: compound, left: current, right: rhs }
              steps.push({ kind: 'field-write', root: base, object: objectExpr, field: left.getName(), value })
              continue
            }
            // this.x — normalized to a flat ident, mutable numeric state
            if (base === 'this') {
              const name = left.getText()
              const value: Expr = compound === null
                ? rhs
                : { kind: 'binary', op: compound, left: { kind: 'ident', name }, right: rhs }
              steps.push({ kind: 'num-assign', name, value })
              continue
            }
          }
          // Numeric assignment (loop counters): n = n - 1, n += 1
          if (Node.isIdentifier(left)) {
            const name = left.getText()
            const value: Expr = compound === null
              ? rhs
              : { kind: 'binary', op: compound, left: { kind: 'ident', name }, right: rhs }
            steps.push({ kind: 'num-assign', name, value })
            continue
          }
        }
        return null
      }
      // n++ / n-- / ++n / --n (identifiers and this.x)
      if (Node.isPostfixUnaryExpression(expr) || Node.isPrefixUnaryExpression(expr)) {
        const op = expr.getOperatorToken()
        const delta = op === SyntaxKind.PlusPlusToken ? '+' : op === SyntaxKind.MinusMinusToken ? '-' : null
        if (delta !== null) {
          const operand = expr.getOperand()
          let name: string | null = null
          if (Node.isIdentifier(operand)) name = operand.getText()
          else if (Node.isPropertyAccessExpression(operand) && memberChainBase(operand) === 'this') {
            name = operand.getText()
          }
          if (name !== null) {
            steps.push({
              kind: 'num-assign',
              name,
              value: { kind: 'binary', op: delta, left: { kind: 'ident', name }, right: { kind: 'literal', value: 1 } },
            })
            continue
          }
        }
      }
      return null
    }

    if (Node.isVariableStatement(s)) {
      if (context === 'branch') return null  // branch-local consts: deferred
      const isConst = String(s.getDeclarationKind()) === 'const'
      for (const decl of s.getDeclarations()) {
        const init = decl.getInitializer()
        if (!init) return null
        if (Node.isIdentifier(init)) {
          // Loop-body scope: alias resolution is static and scans only
          // top-level steps — bind as a local value instead
          steps.push(context === 'loop'
            ? { kind: 'local', name: decl.getName(), value: { kind: 'ident', name: init.getText() } }
            : { kind: 'alias', name: decl.getName(), of: init.getText() })
          continue
        }
        const value = parseExpr(init as Expression)
        if (value === null) return null
        // `let` locals may be reassigned (loop accumulators) — model them as
        // mutable numeric state so loop havoc reaches them; `const` locals
        // are immutable bindings.
        steps.push(isConst
          ? { kind: 'local', name: decl.getName(), value }
          : { kind: 'num-assign', name: decl.getName(), value })
      }
      continue
    }

    if (Node.isIfStatement(s)) {
      const condition = parseExpr(s.getExpression() as Expression)
      if (condition === null) return null
      const thenSteps = extractHeapStmtList(blockStatements(s.getThenStatement()), 'branch')
      if (thenSteps === null) return null
      let elseSteps: HeapStep[] = []
      const elseNode = s.getElseStatement()
      if (elseNode !== undefined) {
        const extracted = extractHeapStmtList(
          Node.isIfStatement(elseNode) ? [elseNode] : blockStatements(elseNode),
          'branch',
        )
        if (extracted === null) return null
        elseSteps = extracted
      }
      steps.push({ kind: 'branch', condition, then: thenSteps, else: elseSteps })
      continue
    }

    // While loops (top-level only): invariant()/decreases() statements in the
    // body are the loop's contracts; the rest is the heap-mutating body
    if (Node.isWhileStatement(s) && topLevel) {
      const condition = parseExpr(s.getExpression() as Expression)
      if (condition === null) return null

      const bodyStmts = blockStatements(s.getStatement())
      const invariants: Expr[] = []
      let decreasesExpr: Expr | undefined
      const codeStmts: Statement[] = []
      for (const bs of bodyStmts) {
        if (Node.isExpressionStatement(bs)) {
          const e = bs.getExpression()
          if (Node.isCallExpression(e)) {
            const callee = e.getExpression().getText()
            if (callee === 'invariant' || callee === 'decreases') {
              const arg = e.getArguments()[0]
              let pred: Expr | null = null
              if (arg !== undefined && Node.isArrowFunction(arg)) {
                const body = arg.getBody()
                if (Node.isExpression(body)) pred = parseExpr(body as Expression)
              } else if (arg !== undefined) {
                pred = parseExpr(arg as Expression)
              }
              if (pred !== null) {
                if (callee === 'invariant') invariants.push(pred)
                else decreasesExpr = pred
              }
              continue
            }
          }
        }
        codeStmts.push(bs)
      }

      const body = extractHeapStmtList(codeStmts, 'loop')
      if (body === null) return null
      // Zero invariants is allowed: the havoc machinery then knows nothing
      // after the loop except ¬condition — honest, and it lets Spacer-based
      // invariant INFERENCE see the loop's transition system.
      steps.push({ kind: 'loop', condition, invariants, decreases: decreasesExpr, body })
      continue
    }

    return null
  }

  return steps
}

function blockStatements(node: Node): Statement[] {
  if (Node.isBlock(node)) return node.getStatements()
  return [node as Statement]
}

function hasFieldWrite(steps: HeapStep[]): boolean {
  return steps.some(s =>
    s.kind === 'field-write' ||
    (s.kind === 'branch' && (hasFieldWrite(s.then) || hasFieldWrite(s.else))) ||
    (s.kind === 'loop' && hasFieldWrite(s.body)))
}

function collectHeapRoots(steps: HeapStep[], roots: Set<string>): void {
  for (const s of steps) {
    if (s.kind === 'field-write') {
      roots.add(s.root)
      collectMemberRoots(s.object, roots)
      collectMemberRoots(s.value, roots)
    } else if (s.kind === 'local') {
      collectMemberRoots(s.value, roots)
    } else if (s.kind === 'branch') {
      collectMemberRoots(s.condition, roots)
      collectHeapRoots(s.then, roots)
      collectHeapRoots(s.else, roots)
    } else if (s.kind === 'loop') {
      collectMemberRoots(s.condition, roots)
      for (const inv of s.invariants) collectMemberRoots(inv, roots)
      collectHeapRoots(s.body, roots)
    } else if (s.kind === 'num-assign') {
      collectMemberRoots(s.value, roots)
    }
  }
}

function walkHeapExprs(steps: HeapStep[], visit: (e: Expr) => void): void {
  for (const s of steps) {
    if (s.kind === 'field-write') { visit(s.object); visit(s.value) }
    else if (s.kind === 'local') visit(s.value)
    else if (s.kind === 'branch') {
      visit(s.condition)
      walkHeapExprs(s.then, visit)
      walkHeapExprs(s.else, visit)
    }
    else if (s.kind === 'loop') {
      visit(s.condition)
      for (const inv of s.invariants) visit(inv)
      walkHeapExprs(s.body, visit)
    }
    else if (s.kind === 'num-assign') visit(s.value)
  }
}

/** `x === root` / `x !== root` makes x a reference root too. */
function collectRefComparisonRoots(expr: Expr, roots: Set<string>): void {
  if (expr.kind === 'binary') {
    if (expr.op === '===' || expr.op === '!==') {
      const l = expr.left
      const r = expr.right
      const isRefish = (e: Expr): boolean =>
        (e.kind === 'ident' && roots.has(e.name)) || e.kind === 'member'
      if (l.kind === 'ident' && isRefish(r)) roots.add(l.name)
      if (r.kind === 'ident' && isRefish(l)) roots.add(r.name)
    }
    collectRefComparisonRoots(expr.left, roots)
    collectRefComparisonRoots(expr.right, roots)
  } else if (expr.kind === 'unary') {
    collectRefComparisonRoots(expr.operand, roots)
  } else if (expr.kind === 'ternary') {
    collectRefComparisonRoots(expr.condition, roots)
    collectRefComparisonRoots(expr.then, roots)
    collectRefComparisonRoots(expr.else, roots)
  }
}

/**
 * Collects spec-function definitions: named functions whose bodies fold to a
 * single expression. Recursion is fine — the unfolder bounds it with fuel.
 */
function collectSpecDefs(
  source: string,
  fileName: string,
): Map<string, { params: string[]; body: Expr; isBool: boolean; isSeq: boolean }> {
  const defs = new Map<string, { params: string[]; body: Expr; isBool: boolean; isSeq: boolean }>()
  for (const fn of extractFunctionsFromSource(source, fileName)) {
    if (!fn.name || fn.body === undefined) continue
    defs.set(fn.name, {
      params: fn.params.map(p => p.name),
      body: fn.body,
      isBool: isBooleanBody(fn.body),
      isSeq: isSeqBody(fn.body),
    })
  }
  return defs
}

/** Collects top-level `footprint(spec, membership)` pairings. */
function collectFootprints(file: SourceFile): Map<string, string> {
  const out = new Map<string, string>()
  for (const call of file.getDescendantsOfKind(SyntaxKind.CallExpression)) {
    if (call.getExpression().getText() !== 'footprint') continue
    const args = call.getArguments()
    if (args.length !== 2) continue
    if (Node.isIdentifier(args[0]) && Node.isIdentifier(args[1])) {
      out.set(args[0].getText(), args[1].getText())
    }
  }
  return out
}

function isSeqBody(expr: Expr): boolean {
  switch (expr.kind) {
    case 'array': return true
    case 'ternary': return isSeqBody(expr.then) || isSeqBody(expr.else)
    default: return false
  }
}

function isBooleanBody(expr: Expr): boolean {
  switch (expr.kind) {
    case 'literal': return typeof expr.value === 'boolean'
    case 'binary': return ['===', '!==', '<', '<=', '>', '>=', '&&', '||'].includes(expr.op)
    case 'unary': return expr.op === '!'
    case 'ternary': return isBooleanBody(expr.then) || isBooleanBody(expr.else)
    default: return false
  }
}

/** Base identifier of a member chain (`a.next.prev` → 'a'), or null. */
/**
 * Detects `X.sort()` / `X.sort((a, b) => a - b)` on a bare identifier.
 * `sorted` is true ONLY for the ascending-numeric comparator — JS's bare
 * .sort() is lexicographic ([10, 9].sort() is NOT numerically sorted).
 */
function matchSortCall(expr: Expression): { name: string; sorted: boolean } | null {
  if (!Node.isCallExpression(expr)) return null
  const callee = expr.getExpression()
  if (!Node.isPropertyAccessExpression(callee) || callee.getName() !== 'sort') return null
  let base: Node = callee.getExpression()
  while (Node.isNonNullExpression(base) || Node.isParenthesizedExpression(base) || Node.isAsExpression(base)) {
    base = base.getExpression()
  }
  if (!Node.isIdentifier(base)) return null
  const name = base.getText()
  const args = expr.getArguments()
  if (args.length === 0) return { name, sorted: false }
  const cmp = args[0]
  if (args.length === 1 && Node.isArrowFunction(cmp)) {
    const params = cmp.getParameters()
    const body = cmp.getBody()
    if (params.length === 2 && Node.isExpression(body)) {
      const [a, b] = [params[0]!.getName(), params[1]!.getName()]
      const text = body.getText().replace(/[\s()]/g, '')
      if (text === `${a}-${b}`) return { name, sorted: true }
    }
  }
  return { name, sorted: false }
}

/**
 * Root name of a field-write target: the base identifier of the member
 * chain, `'this'`, or the ARRAY name when the chain starts from an element
 * access (`users[k].balance = v` → 'users').
 */
function writeBase(left: Expression): string | null {
  let current: Node = left
  for (;;) {
    if (Node.isPropertyAccessExpression(current)) { current = current.getExpression(); continue }
    // users[0]!.balance / (users[0] as Account).balance — unwrap wrappers
    if (Node.isNonNullExpression(current) || Node.isParenthesizedExpression(current) || Node.isAsExpression(current)) {
      current = current.getExpression()
      continue
    }
    break
  }
  if (Node.isIdentifier(current)) return current.getText()
  if (current.getKind() === SyntaxKind.ThisKeyword) return 'this'
  if (Node.isElementAccessExpression(current)) {
    let base: Node = current.getExpression()
    while (Node.isNonNullExpression(base) || Node.isParenthesizedExpression(base) || Node.isAsExpression(base)) {
      base = base.getExpression()
    }
    return Node.isIdentifier(base) ? base.getText() : null
  }
  return null
}

function memberChainBase(node: Expression): string | null {
  let current: Node = node
  while (Node.isPropertyAccessExpression(current)) {
    current = current.getExpression()
  }
  if (Node.isIdentifier(current)) return current.getText()
  return current.getKind() === SyntaxKind.ThisKeyword ? 'this' : null
}

function collectMemberRoots(expr: Expr, roots: Set<string>): void {
  switch (expr.kind) {
    case 'member':
      if (expr.object.kind === 'ident' && expr.object.name !== 'this') roots.add(expr.object.name)
      else collectMemberRoots(expr.object, roots)
      break
    case 'binary':
      collectMemberRoots(expr.left, roots); collectMemberRoots(expr.right, roots); break
    case 'unary':
      collectMemberRoots(expr.operand, roots); break
    case 'ternary':
      collectMemberRoots(expr.condition, roots); collectMemberRoots(expr.then, roots); collectMemberRoots(expr.else, roots); break
    case 'call':
      for (const a of expr.args) collectMemberRoots(a, roots); break
    default:
      break
  }
}

function tryExtractInline(fn: FunctionDeclaration): FunctionIR | null {
  const fnBody = fn.getBody()
  if (!fnBody || !Node.isBlock(fnBody)) return null

  const stmts = fnBody.getStatements()
  const contracts: Contract[] = []
  const codeStmts: Statement[] = []
  const bodySteps: BodyStep[] = []
  let hasPositionalContracts = false

  // Process all statements preserving order
  // requires/ensures → top-level contracts (extracted)
  // check/assume → positional: KEPT in codeStmts so parser applies SSA bindings
  // code → codeStmts
  for (const s of stmts) {
    if (Node.isExpressionStatement(s)) {
      const expr = s.getExpression()
      if (Node.isCallExpression(expr)) {
        const contract = tryExtractContract(expr as Expression)
        if (contract !== null) {
          if (contract.kind === 'check' || contract.kind === 'assume') {
            // Positional: keep in code stream so parser applies SSA bindings
            codeStmts.push(s)
            hasPositionalContracts = true
          }
          // requires/ensures/check/assume all go to contracts
          // ensures is ALWAYS global (sees final state, like Dafny/SPARK)
          // check is positional (sees SSA state at that point)
          contracts.push(contract)
          continue
        }
      }
    }
    codeStmts.push(s)
  }

  // Zod schemas are first-class contracts: `const x = Schema.parse(input)`
  // throws on invalid data, so the schema's refinements hold for x afterwards.
  // Inject them as assume contracts — this alone makes the function verifiable
  // (division safety etc.) with zero annotations.
  try {
    // PREPEND: schema facts are entry-level assumptions, and the translator's
    // sequential pass snapshots each ensures' assumptions in contract order —
    // appended assumes would arrive after the ensures already closed over
    // them (the F2 axioms lesson).
    const schemaAssumes: Contract[] = []
    for (const zc of extractZodContracts(fnBody)) {
      schemaAssumes.push({ kind: 'assume', predicate: zc.predicate })
    }
    for (const ec of extractEffectContracts(fnBody)) {
      schemaAssumes.push({ kind: 'assume', predicate: ec.predicate })
    }
    contracts.unshift(...schemaAssumes)
  } catch { /* schema extraction is best-effort */ }

  if (contracts.length === 0) return null

  const body = parseStmtListToExpr(codeStmts)
  const resolvedContracts = getResolvedPositionalContracts()
  const finalBindings = getFinalSSABindings()
  const loops = extractLoopsFromStmts(codeStmts)

  // Replace check/assume predicates with SSA-resolved versions from the parser
  const finalBodySteps: BodyStep[] = []
  if (hasPositionalContracts && resolvedContracts.length > 0) {
    for (const rc of resolvedContracts) {
      finalBodySteps.push({ kind: rc.kind, predicate: rc.predicate })
    }
  }

  // Apply final SSA bindings to ensures predicates
  // ensures always sees the FINAL state (like Dafny/SPARK), not positional
  if (finalBindings.size > 0) {
    for (const c of contracts) {
      if (c.kind === 'ensures' && typeof c.predicate !== 'string') {
        c.predicate = substituteExpr(c.predicate, finalBindings)
      }
    }
  }

  // ── Closure detection (#7): function returning an arrow function ──────────
  // If the only code statement is `return <ArrowFunction>`, merge outer+inner
  try {
    const closureResult = tryExtractClosure(fn, codeStmts, contracts)
    if (closureResult !== null) return closureResult
  } catch {
    // If closure extraction fails, fall through to normal handling
  }

  // Heap mode: field mutations over object parameters
  let heapSteps: HeapStep[] | undefined
  let heapRoots: string[] | undefined
  let unmodeledWrites: string[] | undefined
  const heap = tryExtractHeapSteps(codeStmts, contracts)
  if (heap !== null) {
    if ('unsupported' in heap) {
      unmodeledWrites = heap.unsupported
    } else {
      heapSteps = heap.steps
      heapRoots = heap.roots
    }
  }

  return {
    name: fn.getName() ?? undefined,
    params: extractFunctionDeclParams(fn),
    returnSort: inferFunctionDeclReturnSort(fn),
    body: body ?? undefined,
    contracts,
    loops: loops.length > 0 ? loops : undefined,
    bodySteps: finalBodySteps.length > 0 ? finalBodySteps : undefined,
    heapSteps,
    heapRoots,
    unmodeledWrites,
  }
}

function tryExtractInlineArrow(fn: ArrowFunction, name: string): FunctionIR | null {
  const fnBody = fn.getBody()
  if (!Node.isBlock(fnBody)) return null

  const stmts = (fnBody as any).getStatements() as Statement[]
  const contracts: Contract[] = []
  const codeStmts: Statement[] = []

  for (const s of stmts) {
    if (Node.isExpressionStatement(s)) {
      const expr = s.getExpression()
      if (Node.isCallExpression(expr)) {
        const contract = tryExtractContract(expr as Expression)
        if (contract !== null) {
          contracts.push(contract)
          continue
        }
      }
    }
    codeStmts.push(s)
  }

  // Zod schemas are first-class contracts: `const x = Schema.parse(input)`
  // throws on invalid data, so the schema's refinements hold for x afterwards.
  // Inject them as assume contracts — this alone makes the function verifiable
  // (division safety etc.) with zero annotations.
  try {
    // PREPEND: schema facts are entry-level assumptions, and the translator's
    // sequential pass snapshots each ensures' assumptions in contract order —
    // appended assumes would arrive after the ensures already closed over
    // them (the F2 axioms lesson).
    const schemaAssumes: Contract[] = []
    for (const zc of extractZodContracts(fnBody)) {
      schemaAssumes.push({ kind: 'assume', predicate: zc.predicate })
    }
    for (const ec of extractEffectContracts(fnBody)) {
      schemaAssumes.push({ kind: 'assume', predicate: ec.predicate })
    }
    contracts.unshift(...schemaAssumes)
  } catch { /* schema extraction is best-effort */ }

  if (contracts.length === 0) return null

  const body = parseStmtListToExpr(codeStmts)
  const loops = extractLoopsFromStmts(codeStmts)

  return {
    name,
    params: extractParams(fn),
    returnSort: inferReturnSort(fn),
    body: body ?? undefined,
    contracts,
    loops: loops.length > 0 ? loops : undefined,
  }
}

/**
 * Detects closures: functions whose only code statement is `return <ArrowFunction>`.
 * Merges outer params + contracts with inner params + contracts.
 * Returns null if the function is not a closure pattern.
 */
function tryExtractClosure(
  fn: FunctionDeclaration,
  codeStmts: Statement[],
  outerContracts: Contract[],
): FunctionIR | null {
  // Find the single return statement with an arrow function
  const returnStmts = codeStmts.filter(s => Node.isReturnStatement(s))
  if (returnStmts.length !== 1) return null

  // All code statements should be the return (no other code besides contracts)
  const nonReturnCode = codeStmts.filter(s => !Node.isReturnStatement(s))
  if (nonReturnCode.length > 0) return null

  const returnStmt = returnStmts[0]!
  if (!Node.isReturnStatement(returnStmt)) return null
  const returnExpr = returnStmt.getExpression()
  if (!returnExpr || !Node.isArrowFunction(returnExpr)) return null

  const innerArrow = returnExpr as ArrowFunction
  const innerBody = innerArrow.getBody()

  // Extract inner contracts from the inner arrow's body
  const innerContracts: Contract[] = []
  const innerCodeStmts: Statement[] = []

  if (Node.isBlock(innerBody)) {
    for (const s of (innerBody as any).getStatements() as Statement[]) {
      if (Node.isExpressionStatement(s)) {
        const expr = s.getExpression()
        if (Node.isCallExpression(expr)) {
          const contract = tryExtractContract(expr as Expression)
          if (contract !== null) {
            innerContracts.push(contract)
            continue
          }
        }
      }
      innerCodeStmts.push(s)
    }
  }

  // Merge: outer params + inner params
  const outerParams = extractFunctionDeclParams(fn)
  const innerParams = extractParams(innerArrow)
  const mergedParams = [...outerParams, ...innerParams]

  // Merge: outer contracts + inner contracts
  const mergedContracts = [...outerContracts, ...innerContracts]

  // Parse inner body
  let body: Expr | undefined
  if (Node.isBlock(innerBody)) {
    body = parseStmtListToExpr(innerCodeStmts) ?? undefined
  } else if (Node.isExpression(innerBody)) {
    body = parseExpr(innerBody as Expression) ?? undefined
  }

  return {
    name: fn.getName() ?? undefined,
    params: mergedParams,
    returnSort: inferReturnSort(innerArrow),
    body,
    contracts: mergedContracts,
  }
}

/**
 * Parses a filtered list of code statements (contracts removed) to an expression.
 * Creates a synthetic Block so we can reuse parseBlockToExpr which handles
 * let/if assignment, const inlining, if/return chains, switch/case, etc.
 */
function parseStmtListToExpr(stmts: Statement[]): Expr | null {
  if (stmts.length === 0) return null

  // If there's a parent block, find it and use parseBlockToExpr context
  // Otherwise, delegate to the main parser's statement list handling
  // by wrapping stmts — but parseBlockToExpr expects a Block node.
  // Since we can't create a synthetic Block, we use the exported
  // parseStmtListDirect which handles all patterns.
  return parseStmtListDirect(stmts)
}

/**
 * Extracts loop info from a filtered list of statements.
 * Finds while/for loops and extracts their conditions (invariants come from contracts).
 */
function extractLoopsFromStmts(stmts: Statement[]): LoopInfo[] {
  const loops: LoopInfo[] = []
  // Track variable initializations before loops (let x = value)
  const inits = new Map<string, Expr>()

  for (const s of stmts) {
    // Track: let x = expr
    if (Node.isVariableStatement(s)) {
      for (const decl of s.getDeclarations()) {
        const init = decl.getInitializer()
        if (init) {
          const parsed = parseExpr(init as Expression)
          if (parsed !== null) inits.set(decl.getName(), parsed)
        }
      }
    }

    // while (cond) { body }
    if (Node.isWhileStatement(s)) {
      const cond = parseExpr(s.getExpression() as Expression)
      if (cond !== null) {
        loops.push({
          condition: cond,
          invariants: [],
          initializations: [...inits.entries()].map(([name, value]) => ({ name, value })),
        })
      }
    }

    // for (init; cond; update) { body }
    if (Node.isForStatement(s)) {
      const condNode = s.getCondition()
      if (condNode) {
        const cond = parseExpr(condNode as Expression)
        if (cond !== null) {
          loops.push({
            condition: cond,
            invariants: [],
            initializations: [...inits.entries()].map(([name, value]) => ({ name, value })),
          })
        }
      }
    }
  }

  return loops
}

/** Walk up the AST to the nearest function or method declaration (not arrow). */
function findEnclosingFunctionDecl(
  node: CallExpression,
): FunctionDeclaration | MethodDeclaration | null {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isFunctionDeclaration(current)) return current as FunctionDeclaration
    if (Node.isMethodDeclaration(current)) return current as MethodDeclaration
    current = current.getParent()
  }
  return null
}

// ---------------------------------------------------------------------------
// Params
// ---------------------------------------------------------------------------

function extractParams(fn: ArrowFunction): Param[] {
  return fn.getParameters().map((p) => {
    const name = p.getName()
    const typeNode = p.getTypeNode()
    const sort = typeNode ? tsTypeToSort(typeNode.getText()) : 'real'
    return { name, sort }
  })
}

function extractFunctionDeclParams(fn: FunctionDeclaration | MethodDeclaration): Param[] {
  return fn.getParameters().map((p) => {
    const name = p.getName()
    const typeNode = p.getTypeNode()
    const sort = typeNode ? tsTypeToSort(typeNode.getText()) : 'real'
    const discriminant = sort === 'unknown' ? detectDiscriminatedUnion(p) : undefined
    return { name, sort, discriminant }
  })
}

/**
 * Detects a discriminated union parameter: every union member is an object
 * type sharing one property whose type is a distinct string literal.
 * `type Payment = { kind: 'pix'; ... } | { kind: 'boleto'; ... }` yields
 * { property: 'kind', values: ['pix', 'boleto'] }.
 */
function detectDiscriminatedUnion(param: import('ts-morph').ParameterDeclaration): Param['discriminant'] {
  try {
    const t = param.getType()
    if (!t.isUnion()) return undefined
    const variants = t.getUnionTypes()
    if (variants.length < 2 || !variants.every(v => v.isObject())) return undefined

    const firstProps = variants[0]!.getProperties()
    for (const prop of firstProps) {
      const propName = prop.getName()
      const values: string[] = []
      let ok = true
      for (const v of variants) {
        const sym = v.getProperty(propName)
        if (sym === undefined) { ok = false; break }
        const pt = sym.getTypeAtLocation(param)
        if (!pt.isStringLiteral()) { ok = false; break }
        values.push(String(pt.getLiteralValue()))
      }
      if (ok && new Set(values).size === values.length) {
        return { property: propName, values }
      }
    }
    return undefined
  } catch {
    return undefined
  }
}

function tsTypeToSort(type: string): Sort {
  const trimmed = type.trim()
  switch (trimmed) {
    case 'boolean': return 'bool'
    case 'bigint':  return 'int'
    case 'number':  return 'real'
    case 'string':  return 'string'
    default:        break
  }

  // Promise<T> — unwrap to inner type sort (#2 async unwrapping)
  const promiseMatch = trimmed.match(/^Promise<(.+)>$/)
  if (promiseMatch) {
    return tsTypeToSort(promiseMatch[1]!)
  }

  // Array types: number[], Array<number>, etc.
  if (trimmed === 'number[]' || trimmed === 'Array<number>') return 'array'

  // Arrays of objects: Account[], Array<Node> — arrays of REFERENCES
  const refArr = trimmed.match(/^([A-Za-z_]\w*)\[\]$/) ?? trimmed.match(/^Array<([A-Za-z_]\w*)>$/)
  if (refArr && !['number', 'string', 'boolean', 'unknown', 'any', 'bigint'].includes(refArr[1]!)) {
    return 'ref-array'
  }

  // Set types: Set<number>
  if (trimmed === 'Set<number>') return 'set'

  // Detect numeric literal union types: 0 | 1 | 2, "Pending" | "Active", etc.
  // Only handle numeric literal unions for now (used for enum-like types).
  const parts = trimmed.split('|').map(p => p.trim())
  if (parts.length >= 2 && parts.every(p => /^-?\d+(\.\d+)?$/.test(p))) {
    const values = parts.map(Number)
    return { kind: 'numeric-union', values }
  }

  // Single uppercase letter = generic type parameter (T, U, V, etc.) → treat as real (#6)
  if (/^[A-Z]$/.test(trimmed)) return 'real'

  return 'unknown'
}

// ---------------------------------------------------------------------------
// Contract extraction
// ---------------------------------------------------------------------------

function tryExtractContract(node: Expression): Contract | null {
  if (!Node.isCallExpression(node)) return null

  const callee = node.getExpression().getText()
  const args = node.getArguments()

  switch (callee) {
    case 'requires':
      return { kind: 'requires', predicate: extractPredicate(args[0] as Expression | undefined) }

    case 'ensures':
      return { kind: 'ensures', predicate: extractPredicate(args[0] as Expression | undefined) }

    case 'invariant':
      return { kind: 'invariant', predicate: extractPredicate(args[0] as Expression | undefined) }

    case 'decreases': {
      const decreasesArg = args[0] as Expression | undefined
      if (!decreasesArg) return null
      if (Node.isArrowFunction(decreasesArg)) {
        const body = decreasesArg.getBody()
        if (!Node.isExpression(body)) return null
        const expr = parseExpr(body)
        if (expr === null) return null
        return { kind: 'decreases', expression: expr }
      }
      // Direct expression: decreases(n), decreases(a + b)
      const expr = parseExpr(decreasesArg)
      if (expr === null) return null
      return { kind: 'decreases', expression: expr }
    }

    case 'modifies':
      return {
        kind: 'modifies',
        // Accept both identifiers (modifies(a, b)) and strings (modifies('a'))
        refs: args
          .filter((a) => Node.isStringLiteral(a as Expression) || Node.isIdentifier(a as Expression))
          .map((a) => (a as Expression).getText().replace(/['"]/g, '')),
      }

    case 'check':
      return { kind: 'check', predicate: extractPredicate(args[0] as Expression | undefined) }

    case 'assume':
      return { kind: 'assume', predicate: extractPredicate(args[0] as Expression | undefined) }

    case 'unreachable':
      return { kind: 'unreachable' }

    default:
      break
  }

  // loop(N).invariant(...) / loop(N).decreases(...)
  if (Node.isPropertyAccessExpression(node.getExpression())) {
    const propAccess = node.getExpression()
    if (!Node.isPropertyAccessExpression(propAccess)) return null
    const method = propAccess.getName()
    const loopCall = propAccess.getExpression()

    if (Node.isCallExpression(loopCall) && loopCall.getExpression().getText() === 'loop') {
      const indexArg = loopCall.getArguments()[0]
      if (!indexArg || !Node.isNumericLiteral(indexArg)) return null
      const loopIndex = Number(indexArg.getLiteralValue())

      if (method === 'invariant') {
        return { kind: 'invariant', predicate: extractPredicate(args[0] as Expression | undefined), loopIndex }
      }
      if (method === 'decreases') {
        const decreasesArg = args[0] as Expression | undefined
        if (!decreasesArg) return null
        if (Node.isArrowFunction(decreasesArg)) {
          const body = decreasesArg.getBody()
          if (!Node.isExpression(body)) return null
          const expr = parseExpr(body)
          if (expr === null) return null
          return { kind: 'decreases', expression: expr, loopIndex }
        }
        const expr = parseExpr(decreasesArg)
        if (expr === null) return null
        return { kind: 'decreases', expression: expr, loopIndex }
      }
    }
  }

  return null
}

function extractPredicate(node: Expression | undefined): Predicate {
  if (node === undefined) return { kind: 'literal', value: true }

  // String contract: ensures("money is conserved")
  if (Node.isStringLiteral(node)) {
    return node.getLiteralValue()
  }

  // Arrow function: requires(({ price }) => price > 0)
  if (Node.isArrowFunction(node)) {
    const body = node.getBody()
    if (Node.isExpression(body)) {
      return parseExpr(body) ?? node.getText()
    }
  }

  // Direct expression: requires(positive(amount)), ensures(result > 0)
  const directParsed = parseExpr(node)
  if (directParsed !== null) return directParsed

  return node.getText()  // fallback: keep raw text
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function inferReturnSort(fn: ArrowFunction): Sort {
  const returnTypeNode = fn.getReturnTypeNode()
  if (returnTypeNode) return tsTypeToSort(returnTypeNode.getText())
  return 'real'
}

function inferFunctionDeclReturnSort(fn: FunctionDeclaration | MethodDeclaration): Sort {
  const returnTypeNode = fn.getReturnTypeNode()
  if (returnTypeNode) return tsTypeToSort(returnTypeNode.getText())
  return 'real'
}

function inferName(call: CallExpression): string | undefined {
  const parent = call.getParent()
  if (Node.isVariableDeclaration(parent)) {
    return (parent as VariableDeclaration).getName()
  }
  return undefined
}

function makeFile(source: string, fileName: string) {
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  return project.createSourceFile(fileName, source, { overwrite: true })
}
