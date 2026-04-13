# theorem infer — Implementation Tasks

> **Instructions for AI agents:**
> - Use **multiple agents in parallel** whenever tasks are independent of each other. Tasks within the same phase that don't share files can be built concurrently.
> - Mark each task as done `[x]` immediately after completing it. Do not batch completions.
> - Each task includes the exact files to create/modify, what to implement, and how to test it.
> - Phases are sequential (Phase 2 depends on Phase 1, etc.), but tasks within a phase are parallelizable unless noted.
> - Always run `npm run build && npm run test` after completing a task to ensure nothing is broken.
> - Reference `docs/theorem-infer-plan.md` for full design context, patterns, and examples.

---

## Phase 1: Foundation — Types, Guard Extraction, and Scaffolding

These tasks set up the inferrer module and implement the highest-value inference: extracting `requires` from guards.

### 1.1 Scaffolding

- [x] **Create the inferrer module structure and public types.**
- [x] **Create empty strategy module stubs.**

### 1.2 Guard Extraction (Strategy 1)

- [x] **Implement guard extraction from if/throw patterns.**
- [x] **Implement condition negation utility.**

### 1.3 Guard Extraction Tests

- [x] **Write comprehensive tests for guard extraction.**

---

## Phase 2: Body Analysis and Arithmetic Safety

- [x] **2.1 — Implement direct body-to-ensures analysis.**
- [x] **2.2 — Implement arithmetic safety extraction.**
- [x] **2.3 — Implement null-safety extraction.**

---

## Phase 3: Advanced Ensures and Candidate Verification

- [x] **3.1 — Implement return type analysis.**
- [x] **3.2 — Implement candidate verification with Z3.**
- [x] **3.3 — Implement array safety extraction.**
- [x] **3.4 — Implement relational contract extraction.**

---

## Phase 4: Cross-Function Propagation

- [x] **4.1 — Implement call graph extraction.**
- [x] **4.2 — Implement requires propagation.**

---

## Phase 5: Contract Writer

- [x] **5.1 — Implement .contracts.ts file generator.**
- [x] **5.2 — Implement human-readable report generator.**

---

## Phase 6: CLI Integration

- [x] **6.1 — Create the `theorem infer` CLI command.**
- [x] **6.2 — Register the infer command in the CLI entry point.**
- [ ] **6.3 — Write CLI integration tests.**

---

## Phase 7: Agent Integration

- [x] **7.1 — Add `audit()` function to theoremts-agent.**
- [x] **7.2 — Write tests for audit().**

---

## Phase 8: End-to-End Validation

- [x] **8.1 — Create example files for theorem infer.**
- [x] **8.2 — Run theorem infer on examples and validate output.**
- [ ] **8.3 — Run theorem scan with inferred contracts and validate it catches bugs.**

---

## Phase 9: Revert Unrelated Changes

- [x] **9.1 — Revert the packages/agent unused imports.**

---

## Post-Implementation Fixes

- [x] **Deduplicate arithmetic requires against guards** — `b !== 0` no longer appears twice (guard + arithmetic).
- [x] **Only treat throw-guards as requires** — early-return guards (clamp pattern) no longer generate false preconditions.
- [x] **Skip guard-ternary bodies in body analysis** — `if (b === 0) throw; return a / b` no longer generates confusing ensures.
- [x] **Deduplicate candidates before verification** — `output() >= 0` from returns + relations no longer duplicates.
