import {
  Node,
  SyntaxKind,
  type SourceFile,
  type Expression,
} from 'ts-morph'
import type { AnyExpr, Bool } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { Expr, Predicate } from '../parser/ir.js'
import type { ContractRegistry } from '../registry/index.js'
import type { VerificationTask } from '../translator/index.js'
import { inlinePureMethodCalls, buildCallMapping, requiredParamCount, paramPositionCount } from '../translator/index.js'
import { parseExpr, tryDedupIdiom, buildPairwiseDistinctFact } from '../parser/expr.js'
import { collectModuleConstFacts } from '../parser/module-consts.js'
import { prettyExpr } from '../parser/pretty.js'
import { substituteExpr, substituteOutput } from '../translator/substitution.js'
import { makeConst, isArrayExpr } from '../translator/variables.js'
import { toZ3 } from '../translator/expr.js'

/**
 * Finds calls to registered (contracted) functions outside of proof() wrappers
 * and generates verification tasks to check that arguments satisfy the callee's requires.
 *
 * Used by both `verify` and `scan` to catch contract violations at call sites.
 */
export function extractCallSiteObligations(
  source: string,
  fileName: string,
  registry: ContractRegistry,
  ctx: Z3Context,
): VerificationTask[] {
  if (registry.size === 0) return []

  const { Project } = require('ts-morph') as typeof import('ts-morph')
  const project = new Project({
    useInMemoryFileSystem: true,
    skipFileDependencyResolution: true,
    compilerOptions: { strict: false, skipLibCheck: true },
  })
  const file = project.createSourceFile(fileName, source, { overwrite: true })

  // Module constants are facts at call sites too — an argument or guard
  // mentioning MAX_PERCENTAGE means MAX_PERCENTAGE === 100, not a free var.
  let moduleConstFacts = new Map<string, number>()
  try { moduleConstFacts = collectModuleConstFacts(file, fileName) } catch { /* best-effort */ }

  const tasks: VerificationTask[] = []

  // Constructor sites participate too: `new X(...)` matches a contract
  // declared on `X` (declare(FeeCalculator, ...)), same as the translator.
  const callNodes = [
    ...file.getDescendantsOfKind(SyntaxKind.CallExpression),
    ...file.getDescendantsOfKind(SyntaxKind.NewExpression),
  ]
  for (const node of callNodes) {
    const calleeName = node.getExpression().getText()
    const contract = resolveContract(calleeName, registry, node.getArguments().length)
    if (!contract) continue

    // Skip calls inside proof() / proof.fn() / requires() / ensures() — already handled by translator
    if (isInsideContractContext(node)) continue

    const args = node.getArguments()

    // Build substitution: callee param names → argument expressions.
    // Position-aware (destructured params share one slot, object-literal
    // args map per property) and default-aware (setPrecision(x) binds
    // precision := 2, so its requires is checked against the real value).
    const argExprs: Expr[] = []
    for (const a of args) {
      const parsed = parseExpr(a as Expression)
      argExprs.push(parsed ?? { kind: 'ident', name: `__unparsed_arg_${argExprs.length}` })
    }
    const mapping = buildCallMapping(contract.params, argExprs)

    // Collect variable assignments in scope before the call site (constant propagation)
    const { assignments: scopeAssignments, sorts: scopeSorts } = collectScopeAssignments(node)

    // Collect path conditions — if-statement guards enclosing the call site
    // and early-exit guards (`if (x.lte(0)) return ...; f(x)` ⟹ !(x <= 0))
    const pathConditions = collectPathConditions(node)

    // Collect enclosing function's inline requires as assumptions
    const enclosingRequires = collectEnclosingRequires(node)

    // Dedup idioms in the enclosing function grant distinctness facts:
    // `const v = [...new Map(arr.map(x => [x.key, x])).values()]` means
    // uniqueBy(v, key) holds at every later call site in that function.
    for (const fact of collectEnclosingDedupFacts(node)) {
      enclosingRequires.push(fact)
    }

    // Collect enclosing function's decreases() expressions — recursion counters
    // are integers, mirroring the translator's "decreases integer" assumption
    const enclosingDecreases = collectEnclosingDecreases(node)

    // For each requires, generate a verification task
    for (const req of contract.requires) {
      if (typeof req === 'string') continue
      // Method contracts (Decimal.gte etc.) inline to plain comparisons —
      // without this, a requires like rate.greaterThanOrEqualTo(1) fails
      // toZ3 and the obligation is silently dropped.
      const substituted = inlinePureMethodCalls(substituteExpr(req, mapping), registry)

      // Create Z3 variables for all identifiers in the substituted expression.
      // Arg idents are typed by the CALLEE's parameter sorts first — an
      // Account[] argument must be an Int→Int reference array or quantified
      // field facts (forall(users, u => u.balance >= 0)) silently drop.
      const vars = new Map<string, AnyExpr<'main'>>()
      for (const param of contract.params) {
        const argE = mapping.get(param.name)
        if (argE?.kind !== 'ident' || vars.has(argE.name)) continue
        if (param.sort === 'ref-array' || param.sort === 'array' || param.sort === 'string') {
          vars.set(argE.name, makeConst(argE.name, param.sort, ctx))
        }
      }
      collectAndCreateVars(substituted, vars, ctx)

      // Add scope assignments as assumptions (constant propagation)
      const assumptions: Bool<'main'>[] = []
      const assumptionLabels: string[] = []
      for (const [varName, valueExpr] of scopeAssignments) {
        // Array literals can't be one Z3 equality, but they establish
        // structural FACTS: exact length, element values, and — for object
        // literals — pairwise-distinct fresh references. Without these,
        // `users = [{...}, {...}]` right before the call would still be
        // treated as an unknown array (a false positive on length/aliasing
        // requires).
        if (valueExpr.kind === 'array' && !valueExpr.elements.some(e => e.kind === 'spread')) {
          const n = valueExpr.elements.length
          const varIdent: Expr = { kind: 'ident', name: varName }
          const at = (i: number): Expr => ({ kind: 'element-access', object: varIdent, index: { kind: 'literal', value: i } })
          const facts: Expr[] = [{
            kind: 'binary', op: '===',
            left: { kind: 'member', object: varIdent, property: 'length' },
            right: { kind: 'literal', value: n },
          }]

          // Element identity analysis. An element is FRESH when it is an
          // object literal — inline, or an ident whose scope assignment is
          // one (`var a = {...}; [a, {...}]`). A fresh allocation is distinct
          // from every element that isn't the very same one; the SAME ident
          // twice is the same object (an equality fact, not distinctness).
          interface ElemInfo {
            fresh: boolean
            identity: string | null
            props: Array<{ key: string; value: Expr }> | null
          }
          const info: ElemInfo[] = valueExpr.elements.map((el, i) => {
            if (el.kind === 'object') return { fresh: true, identity: `#lit${i}`, props: el.properties }
            if (el.kind === 'ident') {
              const bound = scopeAssignments.get(el.name)
              if (bound !== undefined && bound.kind === 'object') {
                return { fresh: true, identity: `ident:${el.name}`, props: bound.properties }
              }
              return { fresh: false, identity: `ident:${el.name}`, props: null }
            }
            return { fresh: false, identity: null, props: null }
          })

          valueExpr.elements.forEach((el, i) => {
            if (el.kind === 'literal' && typeof el.value === 'number') {
              facts.push({ kind: 'binary', op: '===', left: at(i), right: el })
            }
            const ei = info[i]!
            for (let j = i + 1; j < n; j++) {
              const ej = info[j]!
              if (ei.identity !== null && ei.identity === ej.identity) {
                facts.push({ kind: 'binary', op: '===', left: at(i), right: at(j) })
              } else if (ei.fresh || ej.fresh) {
                facts.push({ kind: 'binary', op: '!==', left: at(i), right: at(j) })
              }
            }
            if (ei.props !== null) {
              for (const prop of ei.props) {
                const propAt: Expr = { kind: 'member', object: at(i), property: prop.key }
                // String literals participate too — `appliesTo: "baseCost"`
                // discharges string-valued quantified requires via __sfield_.
                if (prop.value.kind === 'literal' &&
                    (typeof prop.value.value === 'number' || typeof prop.value.value === 'string')) {
                  facts.push({ kind: 'binary', op: '===', left: propAt, right: prop.value })
                }
                // Truthiness in the Int→Bool field view: `isEnabled: true`
                // discharges `!m.isEnabled ||` guards; a numeric/string/null
                // literal fixes the same view by its JS truthiness.
                if (prop.value.kind === 'literal') {
                  const v = prop.value.value
                  const truthy = typeof v === 'boolean' ? v
                    : v === null ? false
                    : typeof v === 'number' ? v !== 0
                    : v !== ''
                  const negated: Expr = { kind: 'unary', op: '!', operand: propAt }
                  facts.push(truthy ? { kind: 'unary', op: '!', operand: negated } : negated)
                }
              }
              // Pairwise string-prop facts: distinct literal keys make
              // uniqueBy(arr, m => m.key) provable at the call site.
              for (let j = i + 1; j < n; j++) {
                const pj = info[j]!.props
                if (pj === null) continue
                for (const prop of ei.props) {
                  if (prop.value.kind !== 'literal' || typeof prop.value.value !== 'string') continue
                  const other = pj.find(p => p.key === prop.key)
                  if (other === undefined || other.value.kind !== 'literal' || typeof other.value.value !== 'string') continue
                  facts.push({
                    kind: 'binary',
                    op: prop.value.value === other.value.value ? '===' : '!==',
                    left: { kind: 'member', object: at(i), property: prop.key },
                    right: { kind: 'member', object: at(j), property: prop.key },
                  })
                }
              }
            }
          })
          for (const fact of facts) {
            collectAndCreateVars(fact, vars, ctx)
            const factZ3 = toZ3(fact, vars, ctx)
            if (factZ3) {
              try {
                assumptions.push(factZ3 as Bool<'main'>)
                assumptionLabels.push(`scope: ${prettyExpr(fact)}`)
              } catch { /* sort mismatch */ }
            }
          }
          continue
        }

        // Calls to contracted functions can't be encoded in Z3 directly.
        // Replace each one with a fresh variable constrained by the callee's
        // ensures (instantiated with the actual arguments), so that
        // `var a = safeAdd(1, 2) - 10` yields `a = __ret - 10` with
        // `__ret >= 1 ∧ __ret >= 2` instead of dropping the assignment.
        const { expr: encodable, ensures: callEnsures } = instantiateContractCalls(valueExpr, registry)

        for (const { callee, predicate } of callEnsures) {
          collectAndCreateVars(predicate, vars, ctx)
          const ensZ3 = toZ3(predicate, vars, ctx)
          if (ensZ3) {
            try {
              assumptions.push(ensZ3 as Bool<'main'>)
              assumptionLabels.push(`ensures(${callee}): ${prettyExpr(predicate)}`)
            } catch { /* sort mismatch */ }
          }
        }

        collectAndCreateVars(encodable, vars, ctx)
        const varZ3 = vars.get(varName)
        const valZ3 = toZ3(encodable, vars, ctx)
        if (varZ3 && valZ3) {
          try {
            assumptions.push((varZ3 as any).eq(valZ3) as Bool<'main'>)
            assumptionLabels.push(`scope: ${varName} = ${prettyExpr(encodable)}`)
          } catch { /* sort mismatch */ }
        }
      }

      // A preceding numeric sort establishes sortedness of that array —
      // the trusted postcondition of Array.prototype.sort with (a, b) => a - b.
      // Bare .sort() gets NOTHING: JS sorts lexicographically.
      for (const srt of scopeSorts) {
        if (!srt.numeric) continue
        const qi = `__qs_${srt.name}_i`
        const qj = `__qs_${srt.name}_j`
        const arrIdent: Expr = { kind: 'ident', name: srt.name }
        const at = (q: string): Expr => ({ kind: 'element-access', object: arrIdent, index: { kind: 'ident', name: q } })
        const sortedFact: Expr = {
          kind: 'quantifier', quantifier: 'forall', param: qi, sort: 'int',
          body: {
            kind: 'quantifier', quantifier: 'forall', param: qj, sort: 'int',
            body: {
              kind: 'binary', op: '==>',
              left: {
                kind: 'binary', op: '&&',
                left: {
                  kind: 'binary', op: '&&',
                  left: { kind: 'binary', op: '>=', left: { kind: 'ident', name: qi }, right: { kind: 'literal', value: 0 } },
                  right: { kind: 'binary', op: '<=', left: { kind: 'ident', name: qi }, right: { kind: 'ident', name: qj } },
                },
                right: { kind: 'binary', op: '<', left: { kind: 'ident', name: qj }, right: { kind: 'member', object: arrIdent, property: 'length' } },
              },
              right: { kind: 'binary', op: '<=', left: at(qi), right: at(qj) },
            },
          },
        }
        collectAndCreateVars(sortedFact, vars, ctx)
        const sortedZ3 = toZ3(sortedFact, vars, ctx)
        if (sortedZ3) {
          try {
            assumptions.push(sortedZ3 as Bool<'main'>)
            assumptionLabels.push(`sort: ${srt.name} sorted ascending (numeric comparator)`)
          } catch { /* skip */ }
        }
      }

      // Add path conditions as assumptions (if-guards enclosing the call).
      // A truthiness guard (`if (overrides)`) translates as a non-Bool — it
      // would pass construction and explode inside the solver; drop it.
      for (const { expr: rawCondExpr, negated } of pathConditions) {
        // Method-call guards (`x.lte(0)`) inline to plain comparisons —
        // without this, Decimal guards silently drop from path conditions.
        const condExpr = inlinePureMethodCalls(rawCondExpr, registry)
        collectAndCreateVars(condExpr, vars, ctx)
        const condZ3 = toZ3(condExpr, vars, ctx)
        if (condZ3 && isBoolSorted(condZ3)) {
          try {
            const assumption = negated ? ctx.Not(condZ3 as Bool<'main'>) : condZ3 as Bool<'main'>
            assumptions.push(assumption)
            assumptionLabels.push(`path: ${negated ? '!' : ''}${prettyExpr(condExpr)}`)
          } catch { /* skip */ }
        }
      }

      // Add enclosing function's requires as assumptions
      for (const rawReqExpr of enclosingRequires) {
        const reqExpr = inlinePureMethodCalls(rawReqExpr, registry)
        collectAndCreateVars(reqExpr, vars, ctx)
        const reqZ3 = toZ3(reqExpr, vars, ctx)
        if (reqZ3 && isBoolSorted(reqZ3)) {
          try {
            assumptions.push(reqZ3 as Bool<'main'>)
            assumptionLabels.push(`enclosing requires: ${prettyExpr(reqExpr)}`)
          } catch { /* skip */ }
        }
      }

      // decreases(x) implies x is an integer recursion counter
      for (const decExpr of enclosingDecreases) {
        collectAndCreateVars(decExpr, vars, ctx)
        const decZ3 = toZ3(decExpr, vars, ctx)
        if (decZ3) {
          try {
            assumptions.push((ctx.ToInt(decZ3 as any) as any).eq(decZ3) as Bool<'main'>)
            assumptionLabels.push(`decreases integer: ${prettyExpr(decExpr)} is integer`)
          } catch { /* not arithmetic */ }
        }
      }

      // Module constants referenced by this task are pinned to their values.
      // Skipped when a scope assignment shadows the name (local wins).
      for (const [constName, constValue] of moduleConstFacts) {
        const constVar = vars.get(constName)
        if (constVar === undefined || scopeAssignments.has(constName)) continue
        try {
          // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any
          assumptions.push((constVar as any).eq(ctx.Real.val(constValue)) as Bool<'main'>)
          assumptionLabels.push(`module const: ${constName} === ${constValue}`)
        } catch { /* non-numeric sort — skip */ }
      }

      const z3 = toZ3(substituted, vars, ctx)
      if (z3 === null) continue

      // Ensure the goal is a Bool (skip if sort mismatch)
      let goal: Bool<'main'>
      try {
        goal = ctx.Not(z3 as Bool<'main'>)
      } catch { continue }

      const argTexts = args.map(a => a.getText().trim()).join(', ')

      tasks.push({
        functionName: `(call-site) ${calleeName}`,
        contractText: `${calleeName}(${argTexts}): ${prettyExpr(req)}`,
        variables: vars,
        assumptions,
        assumptionLabels,
        goal,
        domainConstraints: [],
        sourcePos: { start: node.getStart(), length: node.getWidth() },
        callSite: { call: `${calleeName}(${argTexts})`, predicate: prettyExpr(req) },
      })
    }
  }

  return tasks
}

/**
 * Resolves a callee name against the registry: tries the full text first,
 * then the last segment of a dotted name (e.g. `utils.safeAdd` → `safeAdd`).
 */
/** True when a Z3 expression is Bool-sorted — the only sort assertable as an assumption. */
function isBoolSorted(e: AnyExpr<'main'>): boolean {
  // eslint-disable-next-line @typescript-eslint/no-unsafe-member-access, @typescript-eslint/no-explicit-any
  try { return String((e as any).sort) === 'Bool' } catch { return false }
}

function resolveContract(calleeName: string, registry: ContractRegistry, argCount?: number) {
  if (registry.has(calleeName)) return registry.get(calleeName)
  if (calleeName.includes('.')) {
    const contract = registry.get(calleeName.slice(calleeName.lastIndexOf('.') + 1))
    // A method-shaped call matching a free function by name only is accepted
    // only when the arity agrees (defaults/optionals relax the lower bound) —
    // `calculator.total()` must not inherit `total(lineItems, taxRate, rules)`.
    if (contract !== undefined && argCount !== undefined &&
        (argCount < requiredParamCount(contract.params) || argCount > paramPositionCount(contract.params))) return undefined
    return contract
  }
  return undefined
}

let freshCallCounter = 0

/**
 * Walks an expression and replaces every call to a contracted function with a
 * fresh identifier. Each replacement contributes the callee's ensures,
 * instantiated with the (recursively transformed) actual arguments and with
 * output()/result mapped to the fresh identifier. Calls to unknown functions
 * are left in place (toZ3 later rejects them, keeping the value unconstrained).
 */
function instantiateContractCalls(
  expr: Expr,
  registry: ContractRegistry,
): { expr: Expr; ensures: Array<{ callee: string; predicate: Expr }> } {
  const collected: Array<{ callee: string; predicate: Expr }> = []

  function walk(e: Expr): Expr {
    switch (e.kind) {
      case 'call': {
        const args = e.args.map(walk)
        const contract = resolveContract(e.callee, registry, e.args.length)
        if (!contract) {
          return args.some((a, i) => a !== e.args[i]) ? { kind: 'call', callee: e.callee, args } : e
        }
        const fresh: Expr = { kind: 'ident', name: `__ret_${contract.name}_${freshCallCounter++}` }
        const mapping = buildCallMapping(contract.params, args)
        mapping.set('result', fresh)
        for (const ens of contract.ensures) {
          if (typeof ens === 'string') continue
          collected.push({ callee: e.callee, predicate: substituteOutput(substituteExpr(ens, mapping), fresh) })
        }
        return fresh
      }
      case 'binary': {
        const left = walk(e.left)
        const right = walk(e.right)
        return left === e.left && right === e.right ? e : { kind: 'binary', op: e.op, left, right }
      }
      case 'unary': {
        const operand = walk(e.operand)
        return operand === e.operand ? e : { kind: 'unary', op: e.op, operand }
      }
      case 'ternary': {
        const condition = walk(e.condition)
        const then = walk(e.then)
        const els = walk(e.else)
        return condition === e.condition && then === e.then && els === e.else
          ? e : { kind: 'ternary', condition, then, else: els }
      }
      case 'member': {
        const object = walk(e.object)
        return object === e.object ? e : { kind: 'member', object, property: e.property }
      }
      case 'element-access': {
        const object = walk(e.object)
        const index = walk(e.index)
        return object === e.object && index === e.index ? e : { kind: 'element-access', object, index }
      }
      default:
        return e
    }
  }

  return { expr: walk(expr), ensures: collected }
}


/**
 * Check if a node is directly inside a proof() wrapper or a contract call.
 * Calls inside regular functions with inline contracts are NOT skipped —
 * those still need call-site verification.
 */
function isInsideContractContext(node: Node): boolean {
  let current = node.getParent()
  while (current !== undefined) {
    if (Node.isCallExpression(current)) {
      const callee = current.getExpression().getText()
      // Skip calls that are arguments to proof(), requires(), ensures(), etc.
      if (callee === 'proof' || callee === 'proof.fn' ||
          callee === 'requires' || callee === 'ensures' ||
          callee === 'check' || callee === 'assume' ||
          callee === 'invariant' || callee === 'decreases') return true
    }
    // Inside a decorated method with @requires/@ensures — handled by translator
    if (Node.isMethodDeclaration(current)) {
      const decorators = current.getDecorators()
      if (decorators.some(d => ['requires', 'ensures'].includes(d.getName()))) return true
    }
    // NOTE: we deliberately do NOT skip calls inside functions with inline
    // requires/ensures. The translator verifies the function's own contracts,
    // but calls to other contracted functions inside the body still need
    // call-site verification.
    current = current.getParent()
  }
  return false
}

/**
 * Collects variable assignments (var/let/const with initializer) that are
 * in scope before the given call-site node. This enables constant propagation
 * so that `var a = 2; nextOdd(a)` knows `a === 2`.
 *
 * Walks backwards through sibling statements and up through parent blocks.
 * Only collects simple literal or expression initializers — no complex patterns.
 */
function collectScopeAssignments(callNode: Node): { assignments: Map<string, Expr>; sorts: Array<{ name: string; numeric: boolean }> } {
  const assignments = new Map<string, Expr>()
  const sorts: Array<{ name: string; numeric: boolean }> = []

  // Walk up to find containing block/source file
  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    // If parent is a Block or SourceFile, walk its statements before `current`
    if (Node.isBlock(parent) || Node.isSourceFile(parent)) {
      const statements = parent.getStatements()
      for (const stmt of statements) {
        // Stop at the statement containing our call
        if (stmt.getPos() >= callNode.getPos()) break

        // Variable declarations: var a = 2, const b = 3
        if (Node.isVariableStatement(stmt)) {
          for (const decl of stmt.getDeclarationList().getDeclarations()) {
            const name = decl.getName()
            const init = decl.getInitializer()
            if (init) {
              const parsed = parseExpr(init as Expression)
              if (parsed) {
                assignments.set(name, parsed)
              }
            }
          }
        }

        // Expression statement assignments: a = 5
        if (Node.isExpressionStatement(stmt)) {
          const expr = stmt.getExpression()
          // X.sort(...): positions changed — prior content facts about X are
          // stale (drop them); a numeric comparator establishes sortedness.
          const sortCall = matchSortStatement(expr)
          if (sortCall !== null) {
            assignments.delete(sortCall.name)
            sorts.push({ name: sortCall.name, numeric: sortCall.numeric })
          }
          if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === '=') {
            const left = expr.getLeft()
            if (Node.isIdentifier(left)) {
              const parsed = parseExpr(expr.getRight() as Expression)
              if (parsed) {
                assignments.set(left.getText(), parsed)
              }
            }
          }
        }
      }
    }

    current = parent
  }

  return { assignments, sorts }
}

/** Detects `X.sort()` / `X.sort((a, b) => a - b)` — see the extractor twin. */
function matchSortStatement(expr: Node): { name: string; numeric: boolean } | null {
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
  if (args.length === 1 && Node.isArrowFunction(args[0])) {
    const params = args[0].getParameters()
    const body = args[0].getBody()
    if (params.length === 2 && Node.isExpression(body)) {
      const text = body.getText().replace(/[\s()]/g, '')
      if (text === `${params[0]!.getName()}-${params[1]!.getName()}`) return { name, numeric: true }
    }
  }
  return { name, numeric: false }
}

/**
 * Collects inline requires() calls from the enclosing function.
 * If the call is inside `function f(x) { requires(x > 0); ... call() }`,
 * then `x > 0` is an assumption for the call.
 */
function collectEnclosingRequires(callNode: Node): Expr[] {
  const requires: Expr[] = []
  // Parameter names rebound by callbacks BETWEEN the call and an outer
  // function. An outer requires is only sound inside the callback if it
  // doesn't mention a rebound name (captured variables are the SAME
  // variables, so everything else carries over lexically).
  const shadowed = new Set<string>()

  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    if (Node.isFunctionDeclaration(parent) || Node.isArrowFunction(parent) ||
        Node.isFunctionExpression(parent) || Node.isMethodDeclaration(parent)) {
      const body = (parent as any).getBody()
      if (body && Node.isBlock(body)) {
        for (const stmt of body.getStatements()) {
          if (!Node.isExpressionStatement(stmt)) continue
          const expr = stmt.getExpression()
          if (!Node.isCallExpression(expr)) continue
          const callee = expr.getExpression().getText()
          // assume() statements are facts in scope, same as requires —
          // dedup-idiom grants and trusted DB facts must discharge
          // obligations at call sites inside the same function.
          if (callee !== 'requires' && callee !== 'assume') continue
          const args = expr.getArguments()
          if (args.length === 0) continue
          const firstArg = args[0]!
          // Handle arrow-wrapped: requires(({x}) => x > 0)
          let parsed: Expr | null = null
          if (Node.isArrowFunction(firstArg)) {
            const argBody = (firstArg as any).getBody()
            if (argBody) parsed = parseExpr(argBody as Expression)
          } else {
            parsed = parseExpr(firstArg as Expression)
          }
          if (parsed && !mentionsAnyIdent(parsed, shadowed)) requires.push(parsed)
        }
      }
      // This function's parameters shadow same-named outer bindings for
      // everything collected above this level — a reduce callback's
      // (amount, lineItem) must not invalidate the outer taxRate requires,
      // but an outer requires about `lineItem` would be about a DIFFERENT
      // variable and is dropped.
      try {
        for (const p of (parent as any).getParameters?.() ?? []) {
          const nameNode = p.getNameNode?.()
          if (nameNode !== undefined && !Node.isIdentifier(nameNode)) {
            // Destructuring pattern: every bound identifier shadows
            for (const id of nameNode.getDescendantsOfKind(SyntaxKind.Identifier)) {
              shadowed.add(id.getText())
            }
          } else {
            shadowed.add(p.getName())
          }
        }
      } catch { /* parameter reflection is best-effort */ }
      // Keep walking: a call inside a callback still sits under the outer
      // function whose requires constrain the captured variables.
    }

    current = parent
  }

  return requires
}

/**
 * Scans the enclosing function's body for dedup-idiom const declarations
 * (`const v = [...new Map(arr.map(x => [x.key, x])).values()]` etc.) and
 * returns the granted distinctness facts over the declared variables.
 */
function collectEnclosingDedupFacts(callNode: Node): Expr[] {
  const facts: Expr[] = []
  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break
    if (Node.isFunctionDeclaration(parent) || Node.isArrowFunction(parent) ||
        Node.isFunctionExpression(parent) || Node.isMethodDeclaration(parent)) {
      // eslint-disable-next-line @typescript-eslint/no-unsafe-assignment, @typescript-eslint/no-explicit-any, @typescript-eslint/no-unsafe-call, @typescript-eslint/no-unsafe-member-access
      const body = (parent as any).getBody()
      if (body && Node.isBlock(body)) {
        // ALL declarations in the function, nested blocks included — the
        // dedup const usually lives inside an if-branch right before the
        // call. Block scoping makes the per-name grant safe: a reference
        // outside the variable's scope would not compile. Declarations in
        // NESTED functions are excluded — their scope doesn't reach here.
        for (const stmt of (body as Node).getDescendantsOfKind(SyntaxKind.VariableStatement)) {
          const owner = stmt.getFirstAncestor(a =>
            Node.isFunctionDeclaration(a) || Node.isArrowFunction(a) ||
            Node.isFunctionExpression(a) || Node.isMethodDeclaration(a))
          if (owner !== parent) continue
          for (const decl of stmt.getDeclarations()) {
            const init = decl.getInitializer()
            if (init === undefined) continue
            const dedup = tryDedupIdiom(init)
            if (dedup === null) continue
            const varIdent: Expr = { kind: 'ident', name: decl.getName() }
            facts.push(buildPairwiseDistinctFact(varIdent, dedup.field, `dedup(${decl.getName()})`))
          }
        }
      }
      break  // immediate enclosing function only — dedup vars are locals
    }
    current = parent
  }
  return facts
}

/** True if the expression mentions any of the given identifier names
 *  (including as the root of a member chain). */
function mentionsAnyIdent(expr: Expr, names: Set<string>): boolean {
  if (names.size === 0) return false
  switch (expr.kind) {
    case 'ident':          return names.has(expr.name) || names.has(expr.name.split('.')[0]!)
    case 'binary':         return mentionsAnyIdent(expr.left, names) || mentionsAnyIdent(expr.right, names)
    case 'unary':          return mentionsAnyIdent(expr.operand, names)
    case 'ternary':        return mentionsAnyIdent(expr.condition, names) || mentionsAnyIdent(expr.then, names) || mentionsAnyIdent(expr.else, names)
    case 'call':           return expr.args.some(a => mentionsAnyIdent(a, names)) || (expr.recv !== undefined && mentionsAnyIdent(expr.recv, names)) || names.has(expr.callee.split('.')[0]!)
    case 'member':         return mentionsAnyIdent(expr.object, names)
    case 'element-access': return mentionsAnyIdent(expr.object, names) || mentionsAnyIdent(expr.index, names)
    case 'quantifier':     return mentionsAnyIdent(expr.body, names)
    case 'array':          return expr.elements.some(e => mentionsAnyIdent(e, names))
    case 'object':         return expr.properties.some(p => mentionsAnyIdent(p.value, names))
    case 'spread':         return mentionsAnyIdent(expr.operand, names)
    default:               return false
  }
}

/**
 * Collects the argument expressions of decreases() calls in the immediate
 * enclosing function (e.g. `decreases(exp)` → the `exp` expression).
 */
function collectEnclosingDecreases(callNode: Node): Expr[] {
  const decreases: Expr[] = []

  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    if (Node.isFunctionDeclaration(parent) || Node.isArrowFunction(parent) || Node.isFunctionExpression(parent)) {
      const body = (parent as any).getBody()
      if (body && Node.isBlock(body)) {
        for (const stmt of body.getStatements()) {
          if (!Node.isExpressionStatement(stmt)) continue
          const expr = stmt.getExpression()
          if (!Node.isCallExpression(expr)) continue
          if (expr.getExpression().getText() !== 'decreases') continue
          const args = expr.getArguments()
          if (args.length === 0) continue
          const parsed = parseExpr(args[0]! as Expression)
          if (parsed) decreases.push(parsed)
        }
      }
      break // only the immediate enclosing function
    }

    current = parent
  }

  return decreases
}

/**
 * Collects if-statement conditions that guard the call site.
 * If the call is inside `if (cond) { call() }`, then `cond` is a path condition.
 * If the call is in the else branch, the condition is negated.
 * Also handles early-exit guards: `if (!cond) return; call()` → cond is assumed.
 */
function collectPathConditions(callNode: Node): Array<{ expr: Expr; negated: boolean }> {
  const conditions: Array<{ expr: Expr; negated: boolean }> = []

  let current: Node | undefined = callNode
  while (current) {
    const parent = current.getParent()
    if (!parent) break

    if (Node.isIfStatement(parent)) {
      const condNode = parent.getExpression()
      const parsed = parseExpr(condNode as Expression)
      if (parsed) {
        const thenStmt = parent.getThenStatement()
        const elseStmt = parent.getElseStatement()

        // Is the call in the then-branch or else-branch?
        if (thenStmt && isDescendantOf(current, thenStmt)) {
          // In then-branch: condition is true
          conditions.push({ expr: parsed, negated: false })
        } else if (elseStmt && isDescendantOf(current, elseStmt)) {
          // In else-branch: condition is false (negated)
          conditions.push({ expr: parsed, negated: true })
        }
      }
    }

    // Early-exit guard: if (!cond) return/throw; ...call()
    // If we're in a block and there's an if/return before us, assume the guard
    if (Node.isBlock(parent)) {
      const statements = parent.getStatements()
      for (const stmt of statements) {
        // Stop at the statement containing our call. Comparing end positions
        // matters: a call INSIDE `if (c) return f(x)` must not assume !c.
        if (stmt.getEnd() > callNode.getPos()) break

        if (Node.isIfStatement(stmt) && !stmt.getElseStatement()) {
          const thenBranch = stmt.getThenStatement()
          if (isUnconditionalExit(thenBranch)) {
            // Guard: if (BAD) return → after this, !BAD holds
            const condNode = stmt.getExpression()
            const parsed = parseExpr(condNode as Expression)
            if (parsed) {
              conditions.push({ expr: parsed, negated: true })
            }
          }
        }
      }
    }

    current = parent
  }

  return conditions
}

function isDescendantOf(node: Node, ancestor: Node): boolean {
  let current: Node | undefined = node
  while (current) {
    if (current === ancestor) return true
    current = current.getParent()
  }
  return false
}

function isUnconditionalExit(node: Node): boolean {
  if (Node.isReturnStatement(node) || Node.isThrowStatement(node)) return true
  if (Node.isBlock(node)) {
    const stmts = node.getStatements()
    if (stmts.length === 0) return false
    const last = stmts[stmts.length - 1]!
    return Node.isReturnStatement(last) || Node.isThrowStatement(last)
  }
  return false
}

/** Recursively collects identifiers from an expression and creates Z3 variables. */
function collectAndCreateVars(expr: Expr, vars: Map<string, AnyExpr<'main'>>, ctx: Z3Context): void {
  switch (expr.kind) {
    case 'ident':
      if (!vars.has(expr.name)) vars.set(expr.name, makeConst(expr.name, 'real', ctx))
      break
    case 'quantifier':
      collectAndCreateVars(expr.body, vars, ctx)
      break
    case 'binary':
      collectAndCreateVars(expr.left, vars, ctx)
      collectAndCreateVars(expr.right, vars, ctx)
      break
    case 'unary':
      collectAndCreateVars(expr.operand, vars, ctx)
      break
    case 'ternary':
      collectAndCreateVars(expr.condition, vars, ctx)
      collectAndCreateVars(expr.then, vars, ctx)
      collectAndCreateVars(expr.else, vars, ctx)
      break
    case 'call':
      for (const a of expr.args) collectAndCreateVars(a, vars, ctx)
      break
    case 'member':
      collectAndCreateVars(expr.object, vars, ctx)
      break
    case 'element-access': {
      // The object of an element access must be a Z3 Array for select —
      // promote it even if an earlier walk (e.g. `x.length`) created it
      // as a scalar; nothing has been translated against vars yet.
      if (expr.object.kind === 'ident') {
        const existing = vars.get(expr.object.name)
        if (existing === undefined || !isArrayExpr(existing, ctx)) {
          vars.set(expr.object.name, makeConst(expr.object.name, 'array', ctx))
        }
      } else {
        collectAndCreateVars(expr.object, vars, ctx)
      }
      collectAndCreateVars(expr.index, vars, ctx)
      break
    }
    default:
      break
  }
}
