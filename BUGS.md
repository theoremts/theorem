# Known Bugs

## const + if/return literal replacement

**Status:** Fixed

When a `const` variable is used in an `if` guard and the then-branch returns a literal, the literal gets incorrectly replaced with the const's expression:

```typescript
function test(a: number): number {
  const x = a * 2
  if (x <= 0) return 0   // should be: then-branch = 0
  return x
}
// Expected body: a * 2 <= 0 ? 0 : a * 2
// Actual body:   a * 2 <= 0 ? a * 2 : a * 2  ← 0 replaced with a * 2
```

**Impact:** Functions with `const` intermediate variables + `if/return` guards may not verify correctly. The workaround is to use the variable directly without `const`:

```typescript
// Workaround: use param directly
function test(a: number): number {
  if (a * 2 <= 0) return 0
  return a * 2
}
// Body: a * 2 <= 0 ? 0 : a * 2 ✓
```

**Affected examples:** `kellyPositionSize`, `marginCallAmount` in `trading-engine.ts`

**Root cause:** The SSA `substituteExpr` in `parseWithBindings` is replacing literals in if/return then-branches. The substitution function itself works correctly (verified standalone), but something in the `parseWithBindings` orchestration applies the binding to the literal return value.
