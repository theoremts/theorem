# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Status

Production-ready. 264 tests passing. Four operating modes: verify, scan, suggest, infer.

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

# Infer contracts from existing code (zero annotations needed)
theorem infer src/               # extracts guards, null checks, arithmetic safety
theorem infer --dry-run src/     # preview without writing files
theorem infer --prove src/       # enable Z3 verification of ensures (slower)
theorem infer --confidence heuristic src/  # show all including heuristics (default: guard)
# Output goes to .theorem/contracts/ (gitignored)

# Detect risks without annotations
theorem scan src/                # division by zero, modulo, sqrt, log + contract violations
theorem scan --strict src/       # CI mode

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

- `packages/core/` — parser, translator, solver, scanner, suggester, inferrer, reporter, registry
- `packages/runtime/` — published as `theoremts`; all exports are **no-ops at runtime**
- `packages/cli/` — published as `theoremts-cli`; commands: verify, scan, suggest, infer
- `packages/agent/` — published as `theoremts-agent`; programmatic API for AI agents (verify, audit)
- `packages/plugins/` — bundler plugins (vite/esbuild/tsup stubs)
- `packages/ts-plugin/` — TypeScript Language Service Plugin for inline verification

### Key modules in core

- `parser/ir.ts` — the Expr union type (13 kinds) and FunctionIR
- `parser/expr.ts` — ts-morph AST → IR (handles all TS constructs)
- `parser/extractor.ts` — finds proof()/inline contracts + extractFunctionsFromSource + declare() verification against implementations
- `translator/expr.ts` — IR → Z3 expressions (arithmetic, comparisons, ITE, quantifiers, Math.*)
- `translator/index.ts` — produces VerificationTasks with cross-function obligations + safety obligations
- `translator/substitution.ts` — Expr-level substitution for modular verification
- `scanner/index.ts` — AST-level risk detection with path-sensitive analysis
- `solver/index.ts` — Z3 check with unsat cores, Optimize minimization, blocking evaluations
- `registry/index.ts` — ContractRegistry mapping function names to requires/ensures
- `suggester/index.ts` — candidate generation + "what-if" reasoning
- `inferrer/index.ts` — automatic contract inference from unannotated code
- `inferrer/guards.ts` — if/throw and sentinel-return guard extraction
- `inferrer/arithmetic.ts` — division/sqrt/log safety requirements
- `inferrer/null-safety.ts` — nullable parameter detection
- `inferrer/array-safety.ts` — array bounds and reduce safety
- `inferrer/zod.ts` — Zod schema validation pattern recognition
- `inferrer/propagation.ts` — cross-function contract propagation via call graph
- `inferrer/candidates.ts` — Z3-powered candidate verification
- `inferrer/writer.ts` — .contracts.ts generator and CLI report

### Four operating modes

1. **Verify** — full contracts; cross-function modular verification; declare() verified against implementations; division safety obligations; unsat core reporting
2. **Infer** — zero annotations; extracts guards (if/throw, sentinel returns), arithmetic safety, null safety, array safety, Zod schemas; cross-function propagation; optional Z3 verification with --prove; outputs to .theorem/contracts/
3. **Scan** — zero effort; detects division-by-zero, modulo-by-zero, negative sqrt, log of non-positive, AND contract violations at call sites
4. **Suggest** — auto-generates requires/ensures candidates; shows "if you add requires(X), then ensures(Y) becomes provable"

### Inferrer strategies (9 total)

1. Guard extraction — if/throw → requires (+ sentinel returns like `return null`, `return redirect(...)`)
2. Body analysis — return expression → ensures (with --prove)
3. Arithmetic safety — division, modulo, sqrt, log → requires
4. Cross-function propagation — callee requires → caller requires (includes external registry from @theoremts/contracts-*)
5. Null safety — nullable params without guards → requires
6. Array safety — reduce without initial, numeric array indexing → requires
7. Return analysis — Math.abs/max/min, squared, clamp → ensures (with --prove)
8. Relational contracts — cross-parameter relationships (with --prove)
9. Zod schemas — z.number().positive(), .min(N), .max(N) etc. → requires

### Key design invariants

- All runtime exports are **no-ops** — they exist for static analysis only
- Z3 treats division by zero as a total function (returns arbitrary value). Theorem auto-generates `denominator !== 0` safety obligations to catch this.
- Cross-function verification: when A calls B (with contracts), Theorem checks A's arguments satisfy B's requires, and assumes B's ensures for A's postconditions.
- declare() contracts are verified against implementations when both exist in the codebase.
- Path-sensitive scan: `if (x > 0) { ... / x }` — the guard is encoded as a Z3 assumption, eliminating false positives.
- `.length >= 0` domain constraints are auto-asserted for any member access ending in `.length`.
- Infer without --prove never touches Z3 (safe on any codebase, no WASM crash risk).
- External contract packages (@theoremts/contracts-*) are auto-discovered from node_modules and used in both verify and infer propagation.
