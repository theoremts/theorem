# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Status

Production-ready. 360+ core tests passing (500+ workspace-wide). Since 0.9.2: body equations survive method-call initializers and modular calls in returned object literals — pure method contracts inline into SSA bindings (`const d = a.sub(b)` translates), and object-literal prop equations route through the modular rewriter (memoized __rets: two props built from identical call trees stay EQUAL even when arguments are untranslatable) — kills the free-vars-refute-a-tautology false positive (`const second = first; return { first, second }` failing `second.equals(first)`). Since 0.9.1: module-const facts reach CALL-SITE obligations (an argument or guard mentioning a const pins its value — no more free MAX_PERCENTAGE in counterexamples), and path-condition guards inline pure method contracts (`if (x.lte(0)) return` discharges a callee requires — the early-return Decimal-guard false-positive class is dead). Since 0.9.0: module constants resolved automatically — trusted initializers (numeric literal, `new Decimal(lit)`, folded arithmetic) become assumed facts in every referencing function, same-file AND imported (relative + tsconfig `paths` aliases, one hop) — no more `assume(ZERO.equals(0))` hand-holding. Parameter defaults apply at call sites (`setPrecision(x)` checks `precision := 2`). Destructured object params expand into typed params (`function f({ a, b }: Input)` verifies like `f(a, b)`; sorts from same-file interfaces/type literals; call sites map object-literal args per property, plain idents as member accesses; arity guards count source positions, not expanded bindings). Typed field views: string/bool contexts route element fields through Int→String (`__sfield_`) / Int→Bool (`__bfield_`) heap views — `m.appliesTo === "baseCost"` inside a forall translates, `!m.isEnabled ||` guards work, field-vs-field string equality (`d.key === m.appliesTo`) follows once either side is string-typed by a literal comparison, truthiness operands of `!`/`&&`/`||` go bool-first for ident/member operands. Call-site array-literal facts extended: string prop equalities, truthiness facts for ALL literal props (`isEnabled: true` discharges `!m.isEnabled ||`), pairwise string-prop (in)equalities (uniqueBy over string keys proves for literal arrays). The FeeCalculator-style referential-integrity guard (`forall m: !m.isEnabled || m.appliesTo === "baseCost" || exists d: d.key === m.appliesTo && d.isEnabled`) is now provable/refutable at call sites. Zod dedup TRANSFORMS as uniqueness guarantees: `.transform(a => [...new Map(a.map(x => [x.key, x])).values()])` grants `uniqueBy` on the parsed value, `.transform(a => [...new Set(a)])` grants `unique` (stronger than the Set-size refine — the parse guarantees it). Fixed a silent drop: schema-injected assume contracts vanished in functions WITH positional check/assume steps (bodySteps skip) — schema facts now lead the steps. Nullable-object truthiness desugar: `value ? value : ZERO` where value's declared type is a nullable object/array union becomes `value !== null` (objects are always truthy) — the valueOrDefault pattern proves end-to-end. Since 0.8.7: dedup idioms as TRUSTED contracts (like sort) — `[...new Map(arr.map(x => [x.key, x])).values()]` grants `uniqueBy(v, key)` + `v.length <= arr.length` (content havoc'd); `[...new Set(arr)]` / `Array.from(new Set(arr))` grants `unique(v)`; recognized in the SSA path (synthesized positional assumes) AND the call-site checker (collectEnclosingDedupFacts). `assume()` statements count as facts in scope at call sites (same as requires). tRPC `.input(Schema.standardSchemaV1(X))` unwrapped (Effect Standard Schema bridge). Fixed two silent drops: synthesized positional contracts were gated on literal check/assume statements existing in the source, and the sort pre-create pass skipped bodySteps predicates (a quantified uniqueBy over a local died in toZ3 — both the assume and any obligation over the variable vanished). Since 0.8.5: havoc'd ternary guards — an untranslatable condition (optional chains, string methods, unknown calls) becomes a FREE boolean instead of dropping the whole body, so branch-structure properties prove (a comparator's `output() === -1 || 0 || 1` proves without the solver understanding `a?.lastName?.toLowerCase()`); sound overapproximation — refutations under a havoc guard may pick an infeasible branch (strictly better than a free result). Whole-project verify pre-filters: only files carrying contracts/schema parses or mentioning registered functions reach the solver (2k-file app: 7m37s → 3m32s). Counterexample display suppresses ref-array aliasing notes (`same object as`) and raw ref maps when the query has no field heaps — slot identities are arbitrary model choices there. Since 0.8.4: whole-project verification — bare `theorem verify` (or `theorem verify src`) sweeps everything from the cwd honoring theorem.config.ts; above ~12 files the CLI self-shards: the registry is built from ALL files first (cross-file call-site checks span the project), serialized, and chunks of 6 verify in CHILD processes (fresh Z3 WASM heap each — the heap degrades past ~15-20 files in one process); children stream per-file output and report machine-readable totals, the parent prints one grand total; a crashed shard is reported and skipped. `Math.round(x)` modeled exactly as `to_int(x + 0.5)` (JS half-up semantics incl. negative halves). Since 0.8.3: nullable/Decimal-tolerant comparison vocabulary — `gt/gte/lt/lte/eq/neq(a, b)` desugar to plain binary comparisons; runtime typing accepts `number | { toNumber() } | null | undefined` (structural Decimal, no dependency), semantics "present AND in the domain" (nullish fails at runtime, solver translates the numeric comparison). `positive/nonNegative/negative/finite/between` rebuilt on top (so they accept nullable and Decimal now). `defined(x)` is a real TS type guard (`requires(defined(x) && x.f >= 0)` narrows x in the rest of the predicate) desugaring to `x !== null`. `neq(b, 0)` discharges division-safety obligations. This kills the `x == null || x >= 0` dance on optional params — `requires(nonNegative(x))` / `requires(gte(rate, 0))` covers number and Decimal alike. Since 0.8.2: numeric accumulation folds — `arr.reduce((acc, x) => acc + x.f, 0)` (and Decimal `acc.add(x.f || 0)`, block bodies with a single return) plus for-of accumulation loops (`let acc = 0; for (const x of arr) acc += x.f`, multiple accumulators, leading `if (cond) continue;` guards) desugar to `__sumBy` fold constants with boundary axioms: `len === 0 ⟹ sum === 0` and bounds from quantified element facts (`forall x.f >= c ⟹ sum >= c·len`). Soundness modes on the fold's 4th arg: continue-guards make the loop a SUBSET (bounds clamp through zero), conditional facts (`!x.f || x.f >= c`) only apply to zero-guarded projections (`|| 0` / `?? 0` — an unguarded nullish field is NaN poison), unknown fallbacks (`?? SOME_CONST`) get no bounds. The CLI reads its version from package.json (a hardcoded string shipped 0.8.1 binaries reporting 0.8.0). Since 0.8.1: method contracts live end-to-end (`declare(Type.prototype.m)` matched at `x.m(y)` call sites — @theoremts/contracts-decimal works; receiver as first param, pure-contract inlining, per-path memoization, native-namespace denylist), contract packages auto-discovered from both `@theorem-contracts/*` and `@theoremts/contracts-*` in CLI AND ts-plugin (plus `src/**/*.contracts.ts`), enclosing requires reach call sites inside callbacks (shadowing-aware), last-segment callee matching gated by arity, method calls inlined inside quantifier bodies (pure-only — no `__ret` under a binder). Five CLI commands: verify, scan, suggest, infer, prisma. Zod AND Effect Schema work as out-of-the-box contracts in verify/scan/ts-plugin, including cross-field invariants (`.refine()` / `Schema.filter()`), `.brand()`/`.int()`, cross-file schema resolution, tRPC `.input()` boundaries, and dead-error-branch analysis (`Effect.fail` proved unreachable under contracts). Class `@invariant` decorators implement Design-by-Contract object invariants. `theorem prisma` generates schemas from schema.prisma (Int → integer facts). Since 0.7.0: quantified array contracts (forall/exists/sorted/unique over Int indices — quarantined e-matching fragment), arrays of objects (ref-arrays composing with field heaps; in-array aliasing is a solver case), Array.prototype.sort as trusted contract (havoc + sortedness for numeric comparator only), regex contracts (/re/.test + z.string().regex → str.in_re), bitwise via BV32, discriminated unions (exhaustiveness provable), Spacer/CHC loop-invariant inference (suggest + editor quick-fix), Houdini automatic invariants (requires/ensures conjuncts guess-and-checked, shown as `(auto)`), collection vocabulary (uniqueBy/sortedBy/sumBy/countBy — folds via heap-versioned delta axioms gated on unique()), zod+effect array element facts, bounds obligations suppressing tsc possibly-undefined in the editor, labeled multi-line plugin diagnostics with path traces.

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
theorem verify --gen-tests src/  # counterexamples → executable regression tests
                                 # (.theorem/regressions/, RED until the bug is fixed)

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

# Generate Theorem-consumable schemas from a Prisma schema
theorem prisma prisma/schema.prisma          # → theorem-schemas.ts next to it
theorem prisma schema.prisma --dry-run       # print without writing

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
- Zod schemas are first-class contracts: `const x = Schema.parse(input)` injects the schema's refinements as assume contracts (extractor) — a function with only a Zod parse becomes verifiable with zero annotations, in verify, scan, and the ts-plugin. Parse results stay free Z3 variables (parser skips SSA-binding `.parse()` initializers); `safeParse` is deliberately ignored (doesn't throw).
- Schema invariants: `.refine(arrow)` cross-field predicates are model invariants — assumed at parse sites AND proved for every function whose return type derives from the schema (`type T = z.output<typeof S>`). Schemas imported via relative paths are resolved cross-file (`inferrer/zod.ts`: `resolveImportedSchema`).
- Effect Schema (`inferrer/effect-schema.ts`) has full parity with Zod: `Schema.decodeUnknownSync(S)(x)` / `decodeSync` are the parse sites (Effect-returning decode variants skipped — failures are values, not throws); Struct field refinements (positive/nonNegative/between/greaterThan[OrEqualTo]/lessThan[OrEqualTo]/int/minLength/maxLength/minItems/maxItems) become assumptions — `Schema.int()` emits a Number.isInteger constraint Z3 uses; `Schema.filter(arrow)` after the Struct is the cross-field invariant; `typeof S.Type` / `Schema.Schema.Type<typeof S>` aliases put producers under proof obligation. Works with `Schema.*` or aliased `import * as S`.
- Class invariants: `@invariant((self) => ...)` on a class is assumed at each method entry and proved at each exit; the constructor must establish it. `this.x` is normalized to a flat `this.x` identifier in the parser, so field mutations flow through the same SSA machinery as local variables (including if-guarded clamps). Inline requires/ensures statements in method bodies are honored alongside decorators.
- Modular calls in bodies: `rewriteRegisteredCalls` replaces registered calls with fresh `__ret_*` idents so the `result = <body>` equation survives nested calls; callee ensures instantiate `output()` to the call's `__ret`, never the caller's `result`.
- Call-site checker propagates callee ensures through variable assignments (`var a = f(1) - 10` → `a = __ret - 10` with f's ensures on `__ret`), and assumes enclosing requires + decreases-integer constraints.
- Body safety obligations are path-sensitive: ternary/early-return guards become path-condition assumptions (`if (b === 0) return 0; return a / b` proves).
- Dead error branches: `Effect.fail`/`Effect.die` under path conditions produce informational tasks (goal = branch reachable; UNSAT ⇒ dead code, reported as ✓; reachable is normal and hidden). CLI drops informational non-proved results; ts-plugin skips them.
- tRPC: `t.procedure.input(Schema).mutation/query/subscription(handler)` — the handler (named after its router key) assumes the input schema's constraints and invariants; `{ input }` destructuring with renames supported; Zod or Effect Schema.
- `theorem prisma` (`prisma/index.ts`): parses schema.prisma → Zod-style row schemas; Int/BigInt → `.int()` (integer facts), optional → `.nullable()`, relations/lists skipped, enums documented.
- Refinement types: a parameter typed with a schema-derived alias (`rate: Rate` where `type Rate = z.output<typeof RateSchema>`) carries the schema constraints as requires — assumed inside the function, PROVED at call sites (`as`-casts satisfy tsc, not Z3).
- Heap mode (`translator/heap.ts`): functions mutating fields of object params are encoded with the heap as Z3 arrays (select/store), object roots as Int references — aliasing (`from === to`) is explored by the solver, not assumed away. `old(x.f)` reads the initial heap. `modifies(a, b)` restricts writable roots (undeclared write = violation). Unsupported body shapes (loops/branches over mutations) fall back with a visible "unmodeled field mutation" warning label. Straight-line bodies only for now.
- Scanner suppresses access-then-check patterns (`const x = arr[i]; if (!x) return`) and `as keyof typeof` record lookups — idiomatic safe JS, not risks.
- Method contracts: `declare(Type.prototype.method, ...)` matches `x.method(y)` call sites — the parser stores the receiver as `recv` on call Exprs; `resolveCallee` falls back to a unique `*.prototype.<method>` suffix match (receiver types are unresolvable in the in-memory parse project; ambiguity = no match; `Math`/`Number`/other native namespaces are never hijacked); the receiver becomes the first contract parameter, `new X(...)` matches `declare(X, ...)`. Pure contracts (`ensures(output() === E)` only) are inlined; impure ones go through the `__ret` modular machinery. Contract predicates themselves route through the rewriter (`translateContractPredicate`). Rewrites are memoized per (callee, args, path) — fresh `__ret`s per occurrence would break congruence across result properties. Walkers that rebuild call nodes MUST spread `...expr` to preserve `recv`/`loc` (spec-unfold dropped them — recurring bug class). CLI auto-discovery loads `@theoremts/contracts-*` packages (`index.contracts.ts`).
