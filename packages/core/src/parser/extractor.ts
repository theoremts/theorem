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
} from 'ts-morph'
import type { BodyStep, Contract, Expr, FunctionIR, LoopInfo, Param, Predicate, Sort } from './ir.js'
import { parseExpr, parseBlockToExpr, parseBlockWithLoops, parseStmtListDirect, getResolvedPositionalContracts, getFinalSSABindings } from './expr.js'
import { substituteExpr } from '../translator/substitution.js'

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
export function extractFromSource(source: string, fileName = 'input.ts'): FunctionIR[] {
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
  if (!Node.isArrowFunction(firstArg)) return null

  const params = extractParams(firstArg)
  const contracts: Contract[] = []

  for (const arg of args.slice(1)) {
    const contract = tryExtractContract(arg as Expression)
    if (contract !== null) contracts.push(contract)
  }

  const fnBody = firstArg.getBody()
  let body: FunctionIR['body']
  let loops: LoopInfo[] | undefined

  if (Node.isExpression(fnBody)) {
    body = parseExpr(fnBody) ?? undefined
  } else if (Node.isBlock(fnBody)) {
    const result = parseBlockWithLoops(fnBody)
    body = result.body ?? undefined
    loops = result.loops.length > 0 ? result.loops : undefined
  }

  return {
    name: inferName(call),
    params,
    returnSort: inferReturnSort(firstArg),
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
    for (const method of cls.getMethods()) {
      const name = method.getName()
      if (alreadyExtracted.has(name)) continue

      const decorators = method.getDecorators()
      if (decorators.length === 0) continue

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

      if (contracts.length === 0) continue

      const params = extractFunctionDeclParams(method)
      const fnBody = method.getBody()
      let body: FunctionIR['body']
      let loops: LoopInfo[] | undefined

      if (fnBody && Node.isBlock(fnBody)) {
        const result = parseBlockWithLoops(fnBody)
        body = result.body ?? undefined
        loops = result.loops.length > 0 ? result.loops : undefined
      }

      results.push({
        name,
        params,
        returnSort: inferFunctionDeclReturnSort(method),
        body,
        contracts,
        loops,
      })
    }
  }

  return results
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

  return {
    name: fn.getName() ?? undefined,
    params: extractFunctionDeclParams(fn),
    returnSort: inferFunctionDeclReturnSort(fn),
    body: body ?? undefined,
    contracts,
    loops: loops.length > 0 ? loops : undefined,
    bodySteps: finalBodySteps.length > 0 ? finalBodySteps : undefined,
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
    return { name, sort }
  })
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
        refs: args
          .filter((a) => Node.isStringLiteral(a as Expression))
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
