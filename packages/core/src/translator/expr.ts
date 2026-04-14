import type { AnyExpr, Bool, Arith, Seq, SMTArray, SMTSet } from 'z3-solver'
import type { Z3Context } from '../solver/context.js'
import type { BinaryOp, Expr } from '../parser/ir.js'
import { makeConst, makeArrayConst, isArrayExpr, isStringExpr, isSetVariable, registerSetVariable } from './variables.js'

type Z3Expr = AnyExpr<'main'>
type Z3Bool = Bool<'main'>
type Z3Arith = Arith<'main'>
type Z3Seq = Seq<'main'>
type Z3Array = SMTArray<'main'>
type Z3Set = SMTSet<'main'>

/**
 * Converts an Expr IR node to a Z3 expression.
 * Returns null when the node cannot be represented (unsupported syntax).
 *
 * The `vars` map is mutated lazily: member-access expressions like
 * `from.balance` introduce a new flat Real variable on first use.
 */
export function toZ3(
  expr: Expr,
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  switch (expr.kind) {
    // ── Literals ──────────────────────────────────────────────────
    case 'literal':
      if (expr.value === null) return null              // null/undefined → no Z3 representation
      if (typeof expr.value === 'boolean') return ctx.Bool.val(expr.value)
      if (typeof expr.value === 'string') {
        try { return ctx.String.val(expr.value) as unknown as Z3Expr } catch { return null }
      }
      return ctx.Real.val(expr.value)

    // ── Identifiers ───────────────────────────────────────────────
    case 'ident': {
      const v = vars.get(expr.name)
      if (v !== undefined) return v
      // `this` — create as a free variable so `this.field` member access works (#3)
      if (expr.name === 'this') {
        const thisVar = makeConst('this', 'real', ctx)
        vars.set('this', thisVar)
        return thisVar
      }
      return null
    }

    // ── Member access: from.balance, s.length, Theorem.Result, output().prop ─
    case 'member': {
      // Theorem.Result → maps to the 'result' Z3 variable
      if (expr.object.kind === 'ident' && expr.object.name === 'Theorem' && expr.property === 'Result') {
        return vars.get('result') ?? null
      }
      // output().prop → result.prop
      if (expr.object.kind === 'call' && expr.object.callee === 'output' && expr.object.args.length === 0) {
        const flatName = `result.${expr.property}`
        if (!vars.has(flatName)) vars.set(flatName, makeConst(flatName, 'real', ctx))
        return vars.get(flatName)!
      }
      // Special case: string.length → Z3 Seq.length() returning Int
      const objZ3 = resolveObject(expr.object, vars, ctx)
      if (objZ3 !== null && expr.property === 'length' && isStringExpr(objZ3, ctx)) {
        try {
          return (objZ3 as unknown as Z3Seq).length() as unknown as Z3Expr
        } catch { /* fall through to flat variable */ }
      }

      // Special case: array.length → free Int variable (Z3 arrays don't have length)
      if (objZ3 !== null && expr.property === 'length' && isArrayExpr(objZ3, ctx)) {
        const flatName = flattenMember(expr)
        if (flatName === null) return null
        if (!vars.has(flatName)) {
          vars.set(flatName, ctx.Int.const(flatName) as unknown as Z3Expr)
        }
        return vars.get(flatName)!
      }

      // Special case: set.size → free Int variable >= 0 (Z3 sets don't have cardinality)
      if (expr.object.kind === 'ident' && expr.property === 'size' && isSetVariable(expr.object.name)) {
        const flatName = `${expr.object.name}.size`
        if (!vars.has(flatName)) {
          vars.set(flatName, ctx.Int.const(flatName) as unknown as Z3Expr)
        }
        return vars.get(flatName)!
      }

      // Flatten nested member access: a.b.c → "a.b.c"
      const flatName = flattenMember(expr)
      if (flatName === null) return null
      if (!vars.has(flatName)) {
        vars.set(flatName, makeConst(flatName, 'real', ctx))
      }
      return vars.get(flatName)!
    }

    // ── Element access: arr[i] ───────────────────────────────────
    case 'element-access': {
      const objName = expr.object.kind === 'ident' ? expr.object.name : null
      if (objName === null) return null

      // Check if the object is a Z3 Array — use select
      const objZ3 = vars.get(objName)
      if (objZ3 !== null && objZ3 !== undefined && isArrayExpr(objZ3, ctx)) {
        const idxZ3 = toZ3(expr.index, vars, ctx)
        if (idxZ3 !== null) {
          try {
            return ctx.Select(objZ3 as Z3Array, idxZ3 as Z3Arith) as unknown as Z3Expr
          } catch { /* fall through to flat variable */ }
        }
        // For literal indices, try explicit Int val
        if (expr.index.kind === 'literal' && typeof expr.index.value === 'number') {
          try {
            return ctx.Select(objZ3 as Z3Array, ctx.Int.val(expr.index.value)) as unknown as Z3Expr
          } catch { /* fall through */ }
        }
      }

      // If the object doesn't exist yet, create it as an Array and use select
      if (objZ3 === undefined) {
        try {
          const arrConst = makeArrayConst(objName, ctx)
          vars.set(objName, arrConst)
          const idxZ3 = toZ3(expr.index, vars, ctx)
          if (idxZ3 !== null) {
            return ctx.Select(arrConst as Z3Array, idxZ3 as Z3Arith) as unknown as Z3Expr
          }
        } catch { /* fall through to flat variable approach */ }
      }

      // Fallback: flatten to "arr[i]" as a free variable (for non-array objects)
      const idxStr = expr.index.kind === 'literal' ? String(expr.index.value) : null
      if (idxStr !== null) {
        const flatName = `${objName}[${idxStr}]`
        if (!vars.has(flatName)) vars.set(flatName, makeConst(flatName, 'real', ctx))
        return vars.get(flatName)!
      }
      // Dynamic index — can't model as a single variable
      return null
    }

    // ── Unary ────────────────────────────────────────────────────
    case 'unary': {
      if (expr.op === 'typeof') return null

      const operand = toZ3(expr.operand, vars, ctx)
      if (operand === null) return null

      if (expr.op === '-') {
        try { return (operand as Z3Arith).neg() } catch { return null }
      }
      // op === '!' — only works on Bool sort, not String/Real
      try { return ctx.Not(operand as Z3Bool) } catch { return null }
    }

    // ── Ternary: condition ? then : else → Z3 ITE ────────────────
    case 'ternary': {
      const cond = toZ3(expr.condition, vars, ctx)
      if (cond === null) return null

      const thenIsNull = expr.then.kind === 'literal' && expr.then.value === null
      const elseIsNull = expr.else.kind === 'literal' && expr.else.value === null

      // Handle ternaries with null branches: cond ? null : expr or cond ? expr : null
      // Constrain __is_null_result = cond (or !cond) so Z3 knows when result is null
      if (thenIsNull || elseIsNull) {
        const nonNullBranch = thenIsNull ? expr.else : expr.then
        const nonNullZ3 = toZ3(nonNullBranch, vars, ctx)

        // Set __is_null_result: true when the null branch is taken
        const nullVarName = '__is_null_result'
        let nullVar = vars.get(nullVarName)
        if (!nullVar) {
          nullVar = ctx.Bool.const(nullVarName)
          vars.set(nullVarName, nullVar)
        }
        // __is_null_result === cond (if then is null) or __is_null_result === !cond (if else is null)
        const nullCondition = thenIsNull ? cond : ctx.Not(cond as Z3Bool)
        // Store as a domain constraint via a helper variable
        const constraintName = '__null_constraint'
        vars.set(constraintName, (nullVar as Z3Bool).eq(nullCondition as Z3Bool) as unknown as Z3Expr)

        if (nonNullZ3 !== null) return nonNullZ3
        return null
      }

      const then = toZ3(expr.then, vars, ctx)
      const els  = toZ3(expr.else, vars, ctx)
      if (then === null || els === null) return null
      try { return ctx.If(cond as Z3Bool, then, els) } catch { return null }
    }

    // ── Binary ────────────────────────────────────────────────────
    case 'binary': {
      if (expr.op === '??') return toZ3(expr.left, vars, ctx)

      // typeof x === 'type' or typeof x !== 'type' — skip (over-approximate as true) (#5)
      // This is safe: we don't add it as a constraint, so the solver considers all paths.
      if ((expr.op === '===' || expr.op === '!==') &&
          ((expr.left.kind === 'unary' && expr.left.op === 'typeof') ||
           (expr.right.kind === 'unary' && expr.right.op === 'typeof'))) {
        return ctx.Bool.val(true)
      }

      // null/undefined comparisons: x === null, output() === null, etc.
      // Model as a boolean variable __is_null_<name> since Z3 has no null value.
      if (expr.op === '===' || expr.op === '!==') {
        const isNullLiteral = (e: Expr) => e.kind === 'literal' && e.value === null
        const getNullSubject = (e: Expr): string | null => {
          if (e.kind === 'ident') return e.name
          if (e.kind === 'call' && e.callee === 'output') return 'result'
          if (e.kind === 'member') {
            const flat = flattenMember(e)
            return flat
          }
          return null
        }

        if (isNullLiteral(expr.left) || isNullLiteral(expr.right)) {
          const subject = isNullLiteral(expr.right)
            ? getNullSubject(expr.left)
            : getNullSubject(expr.right)
          if (subject !== null) {
            const nullVarName = `__is_null_${subject}`
            let nullVar = vars.get(nullVarName)
            if (!nullVar) {
              nullVar = ctx.Bool.const(nullVarName)
              vars.set(nullVarName, nullVar)
            }
            // x === null → __is_null_x, x !== null → NOT __is_null_x
            if (expr.op === '===') {
              return nullVar
            }
            return ctx.Not(nullVar as Z3Bool)
          }
        }
      }

      // String concatenation: s + other where s is a string
      if (expr.op === '+') {
        const left = toZ3(expr.left, vars, ctx)
        const right = toZ3(expr.right, vars, ctx)
        if (left !== null && right !== null) {
          if (isStringExpr(left, ctx) && isStringExpr(right, ctx)) {
            try {
              return (left as unknown as Z3Seq).concat(right as unknown as Z3Seq) as unknown as Z3Expr
            } catch { /* fall through to arithmetic */ }
          }
          // If one side is a string literal and the other is a string var
          if (isStringExpr(left, ctx) || isStringExpr(right, ctx)) {
            try {
              return (left as unknown as Z3Seq).concat(right as unknown as Z3Seq) as unknown as Z3Expr
            } catch { /* fall through to arithmetic */ }
          }
          try { return applyBinaryOp(expr.op, left, right, ctx) } catch { return null }
        }
        return null
      }

      const left  = toZ3(expr.left,  vars, ctx)
      const right = toZ3(expr.right, vars, ctx)
      if (left === null || right === null) return null
      try { return applyBinaryOp(expr.op, left, right, ctx) } catch { return null }
    }

    // ── Function calls ────────────────────────────────────────────
    case 'call':
      try { return translateCall(expr.callee, expr.args, vars, ctx) } catch { return null }

    // ── Quantifiers: forall/exists ─────────────────────────────────
    case 'quantifier': {
      try {
        const boundVar = ctx.Real.const(expr.param)
        const innerVars = new Map(vars)
        innerVars.set(expr.param, boundVar)
        const body = toZ3(expr.body, innerVars, ctx)
        if (body === null) return null
        return expr.quantifier === 'forall'
          ? ctx.ForAll([boundVar], body as Z3Bool)
          : ctx.Exists([boundVar], body as Z3Bool)
      } catch { return null }
    }

    // ── IR kinds that can't be represented in Z3 ──────────────────
    case 'array':
    case 'object':
    case 'spread':
    case 'template':
      return null
  }
}

// ---------------------------------------------------------------------------
// Helper: resolve an expression to its Z3 value (for member-access objects)
// ---------------------------------------------------------------------------

function resolveObject(expr: Expr, vars: Map<string, Z3Expr>, ctx: Z3Context): Z3Expr | null {
  if (expr.kind === 'ident') {
    return vars.get(expr.name) ?? null
  }
  return toZ3(expr, vars, ctx)
}

// ---------------------------------------------------------------------------
// Member access flattening: a.b.c → "a.b.c"
// ---------------------------------------------------------------------------

function flattenMember(expr: Expr): string | null {
  if (expr.kind === 'ident') return expr.name
  if (expr.kind === 'member') {
    // Theorem.Result → result
    if (expr.object.kind === 'ident' && expr.object.name === 'Theorem' && expr.property === 'Result') {
      return 'result'
    }
    // output().prop → result.prop
    if (expr.object.kind === 'call' && expr.object.callee === 'output' && expr.object.args.length === 0) {
      return `result.${expr.property}`
    }
    const obj = flattenMember(expr.object)
    if (obj === null) return null
    return `${obj}.${expr.property}`
  }
  return null
}

// ---------------------------------------------------------------------------
// Sort coercion: Int ↔ Real
// ---------------------------------------------------------------------------

/**
 * When one operand is Int and the other is Real, promote the Int to Real
 * via ctx.ToReal(). This handles the common case of numeric-union (Int)
 * parameters used in arithmetic with Real literals or Real variables.
 */
function coerceArithPair(left: Z3Expr, right: Z3Expr, ctx: Z3Context): [Z3Expr, Z3Expr] {
  try {
    const lIsInt = ctx.isInt(left)
    const rIsInt = ctx.isInt(right)
    const lIsReal = ctx.isReal(left)
    const rIsReal = ctx.isReal(right)

    if (lIsInt && rIsReal) return [ctx.ToReal(left as Z3Arith), right]
    if (lIsReal && rIsInt) return [left, ctx.ToReal(right as Z3Arith)]
  } catch { /* not arithmetic sorts — return as-is */ }
  return [left, right]
}

// ---------------------------------------------------------------------------
// Binary operators
// ---------------------------------------------------------------------------

function applyBinaryOp(
  op: BinaryOp,
  left: Z3Expr,
  right: Z3Expr,
  ctx: Z3Context,
): Z3Expr | null {
  // Coerce Int ↔ Real sort mismatch: promote Int to Real
  const [cl, cr] = coerceArithPair(left, right, ctx)
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const l = cl as any
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const r = cr as any

  switch (op) {
    // Arithmetic
    case '+':   return (l as Z3Arith).add(r)
    case '-':   return (l as Z3Arith).sub(r)
    case '*':   return (l as Z3Arith).mul(r)
    case '/':   return (l as Z3Arith).div(r)
    case '%':   return (l as Z3Arith).mod(r)
    case '**':  return (l as Z3Arith).pow(r)
    // Comparison
    case '<':   return (l as Z3Arith).lt(r)
    case '<=':  return (l as Z3Arith).le(r)
    case '>':   return (l as Z3Arith).gt(r)
    case '>=':  return (l as Z3Arith).ge(r)
    // Equality
    case '===': return l.eq(r)
    case '!==': return ctx.Not(l.eq(r) as Z3Bool)
    // Logical
    case '&&':  return ctx.And(l as Z3Bool, r as Z3Bool)
    case '||':  return ctx.Or(l as Z3Bool, r as Z3Bool)
    // Nullish coalesce handled above in toZ3
    case '??':  return null
    default:    return null
  }
}

// ---------------------------------------------------------------------------
// Built-in helper functions and method calls
// ---------------------------------------------------------------------------

function translateCall(
  callee: string,
  argExprs: Expr[],
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  const args = argExprs.map(a => toZ3(a, vars, ctx))

  // ── String method calls: s.includes(x), s.startsWith(x), etc. ──
  const dotIdx = callee.lastIndexOf('.')
  if (dotIdx > 0) {
    const objName = callee.slice(0, dotIdx)
    const method = callee.slice(dotIdx + 1)
    const objZ3 = vars.get(objName)

    if (objZ3 !== undefined && isStringExpr(objZ3, ctx)) {
      const seq = objZ3 as unknown as Z3Seq
      return translateStringMethod(method, seq, args, argExprs, vars, ctx)
    }

    // ── Set method calls: s.has(x), s.add(x), s.delete(x) ──
    if (objZ3 !== undefined && isSetVariable(objName)) {
      const set = objZ3 as unknown as Z3Set
      return translateSetMethod(method, set, objName, args, vars, ctx)
    }

    // ── Chained Set method calls: s.add(x).has(y), s.delete(x).has(y) ──
    // Pattern: "varName.method(args).outerMethod" where the inner part is a set call
    const chainedResult = tryTranslateChainedSetCall(callee, method, args, vars, ctx)
    if (chainedResult !== null) return chainedResult
  }

  switch (callee) {
    case 'integer': {
      const [x] = args
      if (!x) return null
      return (x as Z3Arith).eq(ctx.ToInt(x as Z3Arith) as Z3Arith)
    }

    case 'positive': {
      const [x] = args
      if (!x) return null
      return (x as Z3Arith).gt(ctx.Real.val(0))
    }

    case 'nonNegative': {
      const [x] = args
      if (!x) return null
      return (x as Z3Arith).ge(ctx.Real.val(0))
    }

    case 'negative': {
      const [x] = args
      if (!x) return null
      return (x as Z3Arith).lt(ctx.Real.val(0))
    }

    case 'finite':
      return ctx.Bool.val(true)

    case 'between': {
      const [x, min, max] = args
      if (!x || !min || !max) return null
      return ctx.And(
        (x as Z3Arith).ge(min as Z3Arith) as Z3Bool,
        (x as Z3Arith).le(max as Z3Arith) as Z3Bool,
      )
    }

    case 'Math.abs': {
      const [x] = args
      if (!x) return null
      return ctx.If((x as Z3Arith).ge(ctx.Real.val(0)), x, (x as Z3Arith).neg())
    }

    case 'Math.max': {
      if (args.length < 2 || args.some(a => a === null)) return null
      return args.reduce((acc, a) =>
        ctx.If((acc as Z3Arith).ge(a as Z3Arith), acc!, a!) as Z3Expr
      )
    }

    case 'Math.min': {
      if (args.length < 2 || args.some(a => a === null)) return null
      return args.reduce((acc, a) =>
        ctx.If((acc as Z3Arith).le(a as Z3Arith), acc!, a!) as Z3Expr
      )
    }

    case 'Math.floor': {
      const [x] = args
      if (!x) return null
      return ctx.ToInt(x as Z3Arith)
    }

    case 'Math.ceil': {
      const [x] = args
      if (!x) return null
      // ceil(x) = -floor(-x)
      return (ctx.ToInt((x as Z3Arith).neg()) as Z3Arith).neg()
    }

    case 'Math.sign': {
      const [x] = args
      if (!x) return null
      const a = x as Z3Arith
      return ctx.If(a.gt(ctx.Real.val(0)), ctx.Real.val(1),
        ctx.If(a.lt(ctx.Real.val(0)), ctx.Real.val(-1), ctx.Real.val(0)))
    }

    case 'Math.pow': {
      const [base, exp] = args
      if (!base || !exp) return null
      return (base as Z3Arith).pow(exp as Z3Arith)
    }

    case 'output':
      // output() → the 'result' Z3 variable
      return vars.get('result') ?? null

    case 'old': {
      // old(x) references the value of x at function entry.
      const inner = argExprs[0]
      if (!inner) return null
      const oldName = oldVarName(inner)
      if (oldName !== null && vars.has(oldName)) {
        return vars.get(oldName)!
      }
      // Fallback: pure function, old(x) === x
      return args[0] ?? null
    }

    case 'conserved': {
      // conserved(a, b, c) means sum(old(a), old(b), old(c)) === sum(a, b, c)
      if (argExprs.length === 0) return ctx.Bool.val(true)

      let oldSum: Z3Arith | null = null
      let curSum: Z3Arith | null = null

      for (const argExpr of argExprs) {
        const cur = toZ3(argExpr, vars, ctx)
        if (cur === null) return null

        const oName = oldVarName(argExpr)
        const oldVal = (oName !== null && vars.has(oName))
          ? vars.get(oName)!
          : cur

        oldSum = oldSum === null
          ? oldVal as Z3Arith
          : oldSum.add(oldVal as Z3Arith)
        curSum = curSum === null
          ? cur as Z3Arith
          : curSum.add(cur as Z3Arith)
      }

      if (oldSum === null || curSum === null) return ctx.Bool.val(true)
      return oldSum.eq(curSum)
    }

    case 'Number.isFinite':
      return ctx.Bool.val(true)  // Z3 Reals are always finite

    case 'Number.isNaN':
      return ctx.Bool.val(false) // Z3 Reals never NaN

    case 'Number.isInteger': {
      const [x] = args
      if (!x) return null
      return (x as Z3Arith).eq(ctx.ToInt(x as Z3Arith) as Z3Arith)
    }

    default:
      return null
  }
}

// ---------------------------------------------------------------------------
// String method translation
// ---------------------------------------------------------------------------

function translateStringMethod(
  method: string,
  seq: Z3Seq,
  args: Array<Z3Expr | null>,
  _argExprs: Expr[],
  _vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  switch (method) {
    case 'includes':
    case 'contains': {
      // s.includes(sub) → seq.contains(sub)
      const [sub] = args
      if (!sub) return null
      try {
        return seq.contains(sub as unknown as Z3Seq | string) as unknown as Z3Expr
      } catch { return null }
    }

    case 'startsWith': {
      // s.startsWith(prefix) → prefix.prefixOf(s)
      // Z3 API: prefix.prefixOf(s) returns Bool — "is prefix a prefix of s?"
      const [prefix] = args
      if (!prefix) return null
      try {
        return (prefix as unknown as Z3Seq).prefixOf(seq) as unknown as Z3Expr
      } catch { return null }
    }

    case 'endsWith': {
      // s.endsWith(suffix) → suffix.suffixOf(s)
      const [suffix] = args
      if (!suffix) return null
      try {
        return (suffix as unknown as Z3Seq).suffixOf(seq) as unknown as Z3Expr
      } catch { return null }
    }

    case 'indexOf': {
      // s.indexOf(sub) → seq.indexOf(sub, 0)
      const [sub] = args
      if (!sub) return null
      try {
        return seq.indexOf(sub as unknown as Z3Seq | string, 0) as unknown as Z3Expr
      } catch { return null }
    }

    case 'concat': {
      // s.concat(other) → seq.concat(other)
      const [other] = args
      if (!other) return null
      try {
        return seq.concat(other as unknown as Z3Seq | string) as unknown as Z3Expr
      } catch { return null }
    }

    case 'charAt':
    case 'at': {
      // s.charAt(i) or s.at(i) → seq.at(i)
      const [idx] = args
      if (!idx) return null
      try {
        return seq.at(idx as unknown as Z3Arith) as unknown as Z3Expr
      } catch { return null }
    }

    case 'substring':
    case 'slice': {
      // s.substring(start, end) → seq.extract(start, end - start)
      const [start, end] = args
      if (!start) return null
      try {
        if (end) {
          const len = (end as Z3Arith).sub(start as Z3Arith)
          return seq.extract(start as unknown as Z3Arith, len) as unknown as Z3Expr
        }
        // s.substring(start) → seq.extract(start, seq.length() - start)
        const totalLen = seq.length()
        const remaining = (totalLen as Z3Arith).sub(start as Z3Arith)
        return seq.extract(start as unknown as Z3Arith, remaining) as unknown as Z3Expr
      } catch { return null }
    }

    default:
      return null
  }
}

// ---------------------------------------------------------------------------
// Chained Set method translation — handles s.add(x).has(y), etc.
// ---------------------------------------------------------------------------

/**
 * Parses chained set call patterns from the callee string.
 * E.g., "s.add(x).has" where s is a set variable, "add" is the inner method,
 * "(x)" are the inner args parsed from the text, and "has" is the outer method.
 */
function tryTranslateChainedSetCall(
  callee: string,
  outerMethod: string,
  outerArgs: Array<Z3Expr | null>,
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  try {
    // Match pattern: varName.innerMethod(innerArgs).outerMethod
    // The callee without the outer method is: varName.innerMethod(innerArgs)
    const withoutOuter = callee.slice(0, callee.lastIndexOf('.'))
    // Match: identifierName.methodName(args)
    const chainMatch = withoutOuter.match(/^(\w+)\.(\w+)\((.+)\)$/)
    if (!chainMatch) return null

    const [, varName, innerMethod, innerArgText] = chainMatch as unknown as [string, string, string, string]
    if (!isSetVariable(varName)) return null
    const setZ3 = vars.get(varName)
    if (!setZ3) return null

    // Resolve inner argument(s) — for simple cases like a single identifier or literal
    const innerArgName = innerArgText.trim()
    let innerArgZ3: Z3Expr | null = null
    if (vars.has(innerArgName)) {
      innerArgZ3 = vars.get(innerArgName)!
    } else {
      // Try parsing as a numeric literal
      const num = Number(innerArgName)
      if (!isNaN(num)) {
        innerArgZ3 = ctx.Real.val(num) as unknown as Z3Expr
      }
    }
    if (innerArgZ3 === null) return null

    // Execute the inner method to get the intermediate set
    const innerResult = translateSetMethod(
      innerMethod,
      setZ3 as unknown as Z3Set,
      varName,
      [innerArgZ3],
      vars,
      ctx,
    )
    if (innerResult === null) return null

    // Now apply the outer method on the intermediate result
    // The intermediate result is a set if inner method was add/del/union/etc.
    const intermediateSetName = `${varName}__${innerMethod}`
    registerSetVariable(intermediateSetName)
    return translateSetMethod(
      outerMethod,
      innerResult as unknown as Z3Set,
      intermediateSetName,
      outerArgs,
      vars,
      ctx,
    )
  } catch {
    return null
  }
}

// ---------------------------------------------------------------------------
// Set method translation
// ---------------------------------------------------------------------------

function translateSetMethod(
  method: string,
  set: Z3Set,
  setName: string,
  args: Array<Z3Expr | null>,
  vars: Map<string, Z3Expr>,
  ctx: Z3Context,
): Z3Expr | null {
  switch (method) {
    case 'has': {
      // s.has(x) → set.contains(x) — returns Bool
      const [elem] = args
      if (!elem) return null
      try {
        return set.contains(elem as any) as unknown as Z3Expr
      } catch { return null }
    }

    case 'add': {
      // s.add(x) → set.add(x) — returns a new Set
      const [elem] = args
      if (!elem) return null
      try {
        const result = set.add(elem as any) as unknown as Z3Expr
        // Register the result as a set variable (for chaining)
        const resultName = `${setName}__add`
        vars.set(resultName, result)
        registerSetVariable(resultName)
        return result
      } catch { return null }
    }

    case 'delete': {
      // s.delete(x) → set.del(x) — returns a new Set
      const [elem] = args
      if (!elem) return null
      try {
        const result = set.del(elem as any) as unknown as Z3Expr
        const resultName = `${setName}__del`
        vars.set(resultName, result)
        registerSetVariable(resultName)
        return result
      } catch { return null }
    }

    case 'union': {
      // s.union(other) — returns a new Set
      const [other] = args
      if (!other) return null
      try {
        return set.union(other as unknown as Z3Set) as unknown as Z3Expr
      } catch { return null }
    }

    case 'intersect': {
      // s.intersect(other) — returns a new Set
      const [other] = args
      if (!other) return null
      try {
        return set.intersect(other as unknown as Z3Set) as unknown as Z3Expr
      } catch { return null }
    }

    case 'diff': {
      // s.diff(other) — returns a new Set
      const [other] = args
      if (!other) return null
      try {
        return set.diff(other as unknown as Z3Set) as unknown as Z3Expr
      } catch { return null }
    }

    case 'subsetOf': {
      // s.subsetOf(other) → Bool
      const [other] = args
      if (!other) return null
      try {
        return set.subsetOf(other as unknown as Z3Set) as unknown as Z3Expr
      } catch { return null }
    }

    default:
      return null
  }
}

// ---------------------------------------------------------------------------
// old() variable name resolution
// ---------------------------------------------------------------------------

/**
 * Given the inner expression of an `old(expr)` call, returns the __old_ prefixed
 * variable name.  Supports identifiers (`old(x)` → `__old_x`) and member access
 * (`old(a.b)` → `__old_a.b`).  Returns null for unsupported expression kinds.
 */
function oldVarName(expr: Expr): string | null {
  if (expr.kind === 'ident') return `__old_${expr.name}`
  if (expr.kind === 'member') {
    const flat = flattenMember(expr)
    if (flat === null) return null
    return `__old_${flat}`
  }
  return null
}
