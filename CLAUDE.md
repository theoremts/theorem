# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Status

The core pipeline is fully implemented and production-ready. 124 tests passing. All three operating modes (scan, suggest, verify) are working.

## What This Is

Theorem is a formal verification tool for TypeScript that uses the Z3 SMT solver to mathematically prove code correctness for all possible inputs — not by sampling test cases, but by disproving the existence of any violating input.

## Commands

```bash
# Verify annotated contracts
theorem verify src/              # files or directories
theorem verify --strict src/     # exit 1 if any proof fails (CI mode)
theorem verify --watch src/      # re-verify on file change
theorem verify --debug file.ts   # show parser → translator → solver internals
theorem verify --format sarif .  # SARIF JSON output (GitHub/VS Code)

# Detect risks without annotations
theorem scan src/                # division by zero, modulo, sqrt, log + contract violations
theorem scan --strict src/       # CI mode
theorem scan --format sarif .    # SARIF output

# Auto-generate contract suggestions
theorem suggest src/

# Build
npm run build                    # turbo build all packages
npm run test                     # node:test runner
npm run typecheck
```

## Architecture

**Pipeline**: Parser (ts-morph) → IR → Translator (Z3) → Solver → Reporter

```
TypeScript source (.ts / .proof.ts)
       ↓
  PARSER (ts-morph)       — extracts proof()/proof.fn() calls, contracts, function IR
       ↓
  TRANSLATOR              — converts TS operations and contracts → Z3 assertions
       ↓                    cross-function: ContractRegistry + call-site obligations
       ↓
  SOLVER (Z3 WASM)        — UNSAT = proved, SAT = counterexample found
       ↓                    features: unsat cores, Optimize, blocking evaluations
       ↓
  REPORTER                — CLI (ANSI) / SARIF output with counterexample values
```

### Package structure

- `packages/core/` — parser, translator, solver, scanner, suggester, reporter, registry, cache
- `packages/runtime/` — published as `theorem`; all exports are **no-ops at runtime**
- `packages/cli/` — published as `theorem-cli`; commands: scan, suggest, verify
- `packages/plugins/` — placeholder (vite/esbuild/tsup stubs)

### Key modules in core

- `parser/ir.ts` — the Expr union type (13 kinds) and FunctionIR
- `parser/expr.ts` — ts-morph AST → IR (handles all TS constructs)
- `parser/extractor.ts` — finds proof()/proof.fn() calls + extractFunctionsFromSource for scan
- `translator/expr.ts` — IR → Z3 expressions (arithmetic, comparisons, ITE, quantifiers, Math.*)
- `translator/index.ts` — produces VerificationTasks with cross-function obligations + safety obligations
- `translator/substitution.ts` — Expr-level substitution for modular verification
- `scanner/index.ts` — AST-level risk detection with path-sensitive analysis
- `solver/index.ts` — Z3 check with unsat cores, Optimize minimization, blocking evaluations
- `registry/index.ts` — ContractRegistry mapping function names to requires/ensures
- `suggester/index.ts` — candidate generation + "what-if" reasoning

### Three operating modes

1. **Scan** — zero effort; detects division-by-zero, modulo-by-zero, negative sqrt, log of non-positive, AND contract violations at call sites outside proof()
2. **Suggest** — auto-generates requires/ensures candidates; shows "if you add requires(X), then ensures(Y) becomes provable"
3. **Verify** — full contracts; cross-function modular verification; division safety obligations; unsat core reporting

### IR coverage

Literals (number, boolean, null, string), identifiers, member access (nested a.b.c), element access (arr[i]), unary (! - typeof), binary (+ - * / % ** < <= > >= === !== && || ??), ternary, if/else chains, switch/case → ITE, calls (Math.abs/max/min/floor/ceil/sign/pow, Number.isFinite/isNaN/isInteger), quantifiers (forall/exists), type assertions (as), non-null assertions (x!), await (unwrap), array/object/spread/template literals.

### Key design invariants

- All runtime exports are **no-ops** — they exist for static analysis only
- Z3 treats division by zero as a total function (returns arbitrary value). Theorem auto-generates `denominator !== 0` safety obligations to catch this.
- Cross-function verification: when A calls B (with contracts), Theorem checks A's arguments satisfy B's requires, and assumes B's ensures for A's postconditions.
- Path-sensitive scan: `if (x > 0) { ... / x }` — the guard is encoded as a Z3 assumption, eliminating false positives.
- `.length >= 0` domain constraints are auto-asserted for any member access ending in `.length`.
