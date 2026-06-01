# Symex (#100) build plan

> The full design and phase plan for the symbolic execution capability tracked
> in [proptest #100](https://github.com/coreyleavitt/proptest/issues/100).
> Updated as decisions land.

## Status

| | |
|---|---|
| **Plan** | live |
| **Build status** | Phase 0 complete (2026-05-31); Phase 1 next |
| **Trigger condition** | **none** — build proceeding without a champion consumer; first usable capability lands at Phase 1 |
| **SMT substrate** | [nim-z3](https://github.com/coreyleavitt/nim-z3) v1.0.0 (SemVer-stable, audit-cycle-closed 2026-05-31) |
| **Estimated total** | 14–22 weeks (3.5–5.5 months) for one full-time builder |

## Scope

This document covers the build sequence for **symbolic execution for
branch-targeted coverage proof** — the Shape B framing of issue #100. It does
**not** cover constraint-guided generation (Shape A, tracked separately at
[#124](https://github.com/coreyleavitt/proptest/issues/124) with sub-features
[#125–#132](https://github.com/coreyleavitt/proptest/issues/124)), though the
two shapes share some infrastructure noted under § Shared infrastructure.

The plan is structured as a sequence of phases. Each phase ships
standalone-useful capability. Phases 1–6 produce `symexFind` over a growing
fragment of Nim; Phase 7 integrates with proptest's engine pipeline; Phase 9
opens the door for additional consumers and eventual extraction. (Phase 8 —
the original nkdl-v2 champion-consumer phase — was dropped; see § Trigger
history.)

The plan is reversible at each phase boundary. None of the phases assumes the
later phases will be built.

## Cross-references

- [#100](https://github.com/coreyleavitt/proptest/issues/100) — tracking issue (this plan supersedes the inline body)
- [#124](https://github.com/coreyleavitt/proptest/issues/124) — sibling umbrella for constraint-guided generation (Shape A)
- [#107](https://github.com/coreyleavitt/proptest/issues/107) — coverage-guided fuzz (integration point in Phase 7)
- [#111](https://github.com/coreyleavitt/proptest/issues/111) — refinement-type derivation (consumed by ADR-0001)
- [#119](https://github.com/coreyleavitt/proptest/issues/119) — engine pipeline (integration point in Phase 7)
- nim-z3 v1.0.0 release notes: [CHANGELOG.md](https://github.com/coreyleavitt/nim-z3/blob/main/CHANGELOG.md)

## Substrate prerequisites

The five-round nim-z3 v1.0-readiness audit shipped exactly the surfaces symex
needs:

- **`Z3Solver.checkWith(assumptions)`** — probe path conditions under
  successive structural assumptions without rebuilding solver state. The hot
  loop of the symex walker.
- **`Z3Solver.translate(targetCtx)`** — corpus migration across worker
  contexts when symex runs in parallel.
- **`Z3Context.interrupt`** — cross-thread cancellation makes the per-query
  SMT timeout work cleanly even when the property runner needs to cancel
  mid-solve.
- **`lambda[K, V](bound, body)`** — higher-order encoding for path conditions
  that reason about callbacks.
- **`astHash`** — memoize the Z3 encoding of identical AST subtrees across
  path forks.
- **Generic `simplify[T: Z3Term]`** — fold path conditions before each SAT
  call; reduces solver time by 5–30 % in practice.
- **SemVer-stable surface** — symex pins `requires "z3 >= 1.0.0, < 2.0.0"`
  and relies on the API not shifting underneath it.

## Trigger history

The original #100 framing identified **nkdl-v2 post-rewrite, optimization
phase** as the champion consumer that would trigger the build. That trigger
was retired 2026-05-31:

> [Nkdl is getting a custom oracle, distinct from symex; symex was briefly
> considered for that role but rejected: an oracle bound to the SUT's own
> implementation paths is just an expensive identity function — it can only
> catch deviations from itself, not deviations from the spec.]

The trigger is currently **consumer TBD**. Candidate consumers that would
naturally reactivate it:

- **intonaco walker** — when capability-discharge correctness over auxiliary
  subsystems needs branch-coverage proof.
- **fresco's terminal escape-sequence parser** — same optimization-correctness
  pattern as the original nkdl trigger.
- Any future performance-sensitive Nim project with a continuous
  fast-path-addition workflow.

This plan exists so that when a real consumer surfaces, the build can begin
without re-deriving the architecture.

## Architectural Decision Records

### ADR-0001 — Integer semantics

**Decision**: BV[W] as the soundness floor with selective abstraction to
`Z3Int` proved sound by static range analysis. Default setting:
`isOptimised`.

**Background**. Nim's default integer ops are silently modular at runtime
(`x + y` wraps; no overflow check unless `-d:nimDangerous` or per-pragma
opt-in). Three options were considered:

| | Description | Soundness |
|---|---|---|
| Option A | Always unbounded `Z3Int` | **Unsound for symex's purpose** — admits witnesses that overflow at runtime and so don't actually reach the target. False positives. |
| Option B | Always `Z3BitVec[W]` | Sound but 10–100× slower per query on 64-bit arithmetic. |
| Option C | Hybrid (Int by default, BV[W] when triggered) | The naive trigger ("switch on width-specific ops") is unsound because all fixed-width arithmetic is silently modular. Once the trigger set widens to "all integer arithmetic on fixed-width types", the hybrid collapses to Option B. |

**Resolution**. The right design is *Option B as the soundness floor with
selective abstraction*. Walker default: every fixed-width Nim integer maps to
`Z3BitVec[sizeof(T) * 8]`. Every operation is BV. Sound by construction.

When the walker can statically prove a variable's value range fits in a
non-overflowing window, abstract that variable to `Z3Int` for as long as the
proof holds. Z3's Int solver runs faster; the abstraction is sound because
we've proved the BV semantics and Int semantics agree over the relevant range.

Proof techniques for v1:

- **Range-type info from the type system**: `range[0..100]`, `Natural`,
  `Positive` (already inferred by proptest's #111 refinement-type derivation)
  carry exact range info that the walker propagates.
- **Refinement constraints from the DSL**: `arbitrary[where(x: int, x in 0..100)]`
  adds `0 ≤ x ≤ 100` to the symbolic env's range table (shared with #124).
- **Trivial interval arithmetic**: `x ∈ [0..100], y ∈ [0..100] ⊢ x + y ∈ [0..200]`.
  Sums, products, mods composed similarly.

When abstraction fails (range can't be bounded, or composition crosses the
W-bit boundary), the variable stays BV. The walker bridges Int↔BV via
`Z3_mk_int2bv` / `Z3_mk_bv2int` when explicit casts demand it (both already
in nim-z3).

User-facing setting:

```nim
type IntegerSemantics* = enum
  isExact      ## BV[W] always. Sound, slowest, simplest. Use when the
               ## abstraction layer's static analysis is itself in doubt.
  isOptimised  ## BV[W] + selective Int abstraction proved sound. Default.
  isLoose      ## Int everywhere, no soundness proof. Fast, may produce
               ## false-positive witnesses. Research / educational mode only;
               ## prints a per-run banner reminding the user.
```

Default `isOptimised`. The per-variable abstraction decisions are recorded
in the path state for audit (`Path.abstractions: Table[Symbol, AbstractionProof]`),
so a user investigating an unexpected witness can verify which variables got
abstracted and why.

**Out-of-scope for v1** (deferred):

- Loop-invariant inference (Phase 6 treats loops as non-promotable; abstraction
  proofs don't survive into k-unwound copies).
- Assertion-based range refinement (`assert x > 0`).
- Refinement carried through user-defined function calls.

These would each enable additional abstraction opportunities but aren't
needed for the v1 capability set.

### ADR-0002 — Predicate-DSL factoring

**Decision**: three-layer split under `proptest/smt/` — pure translator,
type-environment bridge, ergonomic consumer adapters. Consumer adapters live
next to their consumers.

**Background**. A predicate DSL (e.g., `where(x: int, x mod 3 == 0)`) is a
macro that takes a Nim predicate-as-source-tree and translates it to a Z3
constraint. Two consumers exist:

- Symex (#100) — `constraint: proc(input: T): bool = …` parameter on
  `symexFind`.
- Shape A (#125) — `arbitrary[where(x: int, x mod 3 == 0)]` strategy
  constructor.

Both are syntactically identical and use the same translation pipeline.

The question was where to put the code. Two options were considered:

| | Description | Cost |
|---|---|---|
| Option A | Build the DSL inside the symex codebase; Shape A imports it when it ships | Re-architecture cost when Shape A's trigger fires; weird that the DSL "lives" in symex despite Shape A being its larger consumer. |
| Option B | Factor to `proptest/smt/dsl.nim` from day one; both consumers depend on a shared module | One extra module in v1; saves the re-architecture cost. |

**Resolution**. Option B refined into three layers:

```
proptest/smt/
  dsl_parser.nim         # Layer 1: pure Nim-AST → Z3-expression
                         # Stateless. Testable in isolation.
                         # Handles: nnkIntLit, nnkInfix, nnkCall (limited),
                         # nnkIfStmt (as `ite`), nnkBracketExpr, etc.
  dsl_typebridge.nim     # Layer 3: typedesc → Z3 family resolution
                         # Wraps nim-z3's sortOfType machinery
  dsl.nim                # Re-exports + ergonomic constructors
                         # The "DSL" import-surface
proptest/symex.nim       # ← consumes dsl.constraint
proptest/smt/strategy.nim  # ← consumes dsl.where (when Shape A builds)
```

**Why this is best-in-class**:

- **Layer 1 is testable in isolation**: write tests for `parse("x mod 3 == 0", x: Z3Int) → expected Z3 AST` without touching either consumer. The hardest, most algorithmically subtle part of the DSL gets its own test surface.
- **Layer 3 is separately maintained**: typedesc → Z3Family resolution is essentially a `derive` operation; it already exists in nim-z3's `sortOfType` machinery. Wrap once here, both consumers use it.
- **Consumer adapters stay thin**: each ergonomic surface lives next to its primary consumer; they don't infect each other's APIs.
- **Shape A's eventual build becomes mechanical**: when #125 fires, the consumer adapter is one new file (`proptest/smt/strategy.nim`). The hard work is already done and tested.

This also means the **DSL is the first shared module** between symex and the
future Shape A umbrella, establishing the `proptest/smt/` namespace as the
home for Z3-touching code generally.

## Shared infrastructure with #124 Shape A

The following components are designed in this plan but consumed by both #100
(Shape B) and #124 (Shape A):

| Module | Owner | Purpose | Consumers |
|---|---|---|---|
| `proptest/smt/dsl_parser.nim` | this plan (Phase 0–1) | Nim-AST → Z3 translator | symex (`constraint`), Shape A (`where`) |
| `proptest/smt/dsl_typebridge.nim` | this plan (Phase 0–1) | typedesc → Z3 family | both |
| `proptest/smt/dsl.nim` | this plan (Phase 0–1) | ergonomic re-exports | both |
| nim-z3 v1.0.0 dependency pin | this plan (Phase 0) | substrate | both |
| Z3-version determinism story | this plan (Phase 7) | regression-seed Z3-version tagging | both |

When Shape A's first sub-feature (#125) becomes a real build, it consumes the
DSL machinery this plan ships in Phase 1.

## Phased build plan

### Phase 0 — Architecture decisions resolved (1–2 weeks)

**Goal**. Land the two ADRs above as committed design records. Open
follow-up sub-issues for the bounded next-cycle work each ADR defers
(loop-invariant inference, assertion-based refinement, refinement
through-calls).

**Deliverables**:

- `docs/symex/ADR-0001-integer-semantics.md` — committed ADR
- `docs/symex/ADR-0002-dsl-factoring.md` — committed ADR
- `docs/symex/README.md` — index of ADRs and pointers to this plan
- Three issues filed for deferred work: [#133](https://github.com/coreyleavitt/proptest/issues/133) (loop-invariant inference), [#134](https://github.com/coreyleavitt/proptest/issues/134) (assertion-based refinement), [#135](https://github.com/coreyleavitt/proptest/issues/135) (refinement through-call)

**Status (2026-05-31)**: complete. ADRs accepted; deferred-work issues filed.

**Success criteria**: the ADRs are reviewable design artifacts; a future
contributor reading them can reproduce the reasoning without external context.

**Dependencies**: none. Concurrent with Phase 1 acceptable.

### Phase 1 — Minimal viable walker (2–3 weeks)

**Goal**. `symexFind` works for a hand-picked target proc whose body is a
small Nim subset. The tracer bullet.

**Supported fragment for Phase 1**:

- Parameters: `int`, `bool`
- Locals: `int`, `bool`, declared via `let` or `var`
- Operators: arithmetic (`+ - * div mod`), comparison (`== != < <= > >=`),
  boolean (`and or xor not`)
- Control flow: `nnkIfStmt` (if / elif / else)
- Termination: `nnkReturnStmt`
- No function calls beyond compiler intrinsics
- No loops, no `case`, no types beyond `int`/`bool`
- BV[W] encoding always (Phase 2 adds the abstraction layer)

**Modules**:

- `proptest/smt/types.nim` — `Path`, `SymexResult`, `SymexTarget`, `SymexSettings` core types
- `proptest/smt/dsl_parser.nim` — initial parser, just enough for boolean + arithmetic predicates
- `proptest/smt/dsl_typebridge.nim` — Int / Bool only
- `proptest/smt/dsl.nim` — re-exports
- `proptest/smt/walker.nim` — macro: consume typed-proc symbol, produce walker; handles the supported AST kinds above
- `proptest/smt/runtime.nim` — path frontier management, dispatches `checkWith`, materializes results
- `proptest/symex.nim` — public-API entry point `symexFind`

**Tests**:

- `tests/tsymex_phase1_arith.nim` — `proc f(x: int): int = (if x > 5: x else: 0)`, target = "the `x > 5` branch", `symexFind` returns `SymexResult[(int,)](witness: (6,))`
- `tests/tsymex_phase1_bool.nim` — multi-variable predicate over bools and ints
- `tests/tsymex_phase1_unsat.nim` — provably unreachable branch returns `srUnsat` not `srUnknown`
- `tests/tsymex_phase1_dsl.nim` — `dsl_parser` Layer 1 round-trip tests, independent of the walker

**Success criteria**: `symexFind(f, target = "...")` returns `SymexResult` carrying a satisfying input for a 10-line target proc on the supported fragment. Test coverage on the walker's per-AST-kind dispatch ≥ 90 %.

**Dependencies**: Phase 0 ADRs ratified.

### Phase 2 — Width-specific integer modeling + ADR-0001 verification (1–2 weeks)

**Goal**. The BV[W] floor with selective Int abstraction from ADR-0001
actually works in practice.

**Deliverables**:

- `proptest/smt/abstraction.nim` — range tracker (per-variable `[lo, hi]`
  interval) + interval arithmetic
- Walker integration: every fixed-width Nim integer starts in BV[W]; the
  abstraction module promotes to Int when proof succeeds
- `SymexSettings.integerSemantics` honored
- `dsl_parser` extended to recognize `range[lo..hi]` / `Natural` / `Positive`
  type info and seed the range table
- Bit-twiddling operator support: `shl`, `shr`, `and`, `or`, `xor`, `not` on
  integer types — these always force BV (no abstraction even when ranges
  would otherwise permit)
- Audit log: `Path.abstractions` records the per-variable proof obligations

**Tests**:

- `tests/tsymex_phase2_bv_arith.nim` — byte parser style: `proc f(b: uint16): uint8 = uint8(b shr 8)`, target = "high byte is 0xFF", confirms BV encoding finds `b = 0xFF00`
- `tests/tsymex_phase2_abstraction.nim` — `proc f(x: range[0..100], y: range[0..100]): int = x + y` triggers the optimistic Int abstraction; audit log confirms it
- `tests/tsymex_phase2_fallback.nim` — `proc f(x: int, y: int): int = x + y` (no range info) stays in BV; audit log shows no abstraction attempted
- `tests/tsymex_phase2_overflow.nim` — *witness soundness regression test*: a proc with `x + y` where the only path-reaching `x = int.high, y = 1` would overflow. Confirms `isExact` and `isOptimised` both refuse the witness; `isLoose` accepts it (with the documented per-run banner).

**Success criteria**: ADR-0001's `isOptimised` default is faster than `isExact`
by a measurable margin on the range-rich test cases, and is correct (no
false-positive witnesses) on the overflow regression test.

**Dependencies**: Phase 1 walker.

### Phase 3 — User-defined function calls (2–3 weeks)

**Goal**. Inline-via-`getImpl` with k-bounded recursion. The walker can
follow calls into user code.

**Deliverables**:

- Macro-time `getImpl` + recursive walk; bind args to params in the callee's `env`
- Recursion bound: `SymexSettings.maxCallDepth` (default 3); overflow flags
  the path as `ePathUnknown`
- Per-call summarization cache (`Table[(procSym, argShapeHash), SymexSummary]`)
  so the same proc-with-same-arg-shape isn't re-walked; uses `astHash` from
  nim-z3
- Mutual recursion handled (the cache breaks the cycle when re-entering with
  the same args)
- Stdlib model registry stub: `proptest/smt/stdlib_models.nim` exists but is
  empty; framework for Phase 5+ additions

**Tests**:

- `tests/tsymex_phase3_inline.nim` — caller→helper→target, symex finds inputs
  for branches in the helper via the caller
- `tests/tsymex_phase3_recursion.nim` — recursive proc, depth-3 unwound,
  confirms `ePathUnknown` at depth 4
- `tests/tsymex_phase3_summarization.nim` — same proc called twice from
  different callers with the same arg shape produces a cache hit (test via
  internal instrumentation)
- `tests/tsymex_phase3_mutual.nim` — mutual recursion between two procs
  terminates at the cache cycle break

**Success criteria**: a 100-LOC small program with 3 user-defined procs,
each branching, reaches every named target from `symexFind`. Recursion at
depth-3 honored; depth-4 properly flags UNKNOWN.

**Dependencies**: Phase 2 abstraction layer (recursion through procs may
need the abstraction to survive across calls — at minimum, BV witnesses must
flow correctly).

### Phase 4 — Composite types: object, tuple, static array (2–3 weeks)

**Goal**. Cover the object/tuple/static-array surface — the data shapes most
user procs operate on.

**Deliverables**:

- `nnkObjConstr` → tuple-of-Z3-values encoding (one Z3 family per field)
- `nnkDotExpr` (field access) → tuple-index
- `nnkBracketExpr` on `array[N, T]` → `Z3Array[Z3Int, sortOf(T)]` `select`
- Static-array initialization (`[a, b, c]`) → batch `store` chain
- Out-of-bounds branch generation: `select(arr, i)` forks the path; the OOB
  path adds `i < 0 ∨ i ≥ N` to its condition and terminates with an
  IndexError tag (callers can ask symex for "find an OOB input" via target)
- `proptest/smt/dsl_typebridge` extended to recognize tuples, objects, static
  arrays
- Nested type support: `tuple[a: tuple[x: int, y: int], b: int]` etc.

**Tests**:

- `tests/tsymex_phase4_object.nim` — target proc on a `tuple[a, b: int]`,
  symex finds witnesses for branches over `t.a > t.b`
- `tests/tsymex_phase4_nested.nim` — nested tuple, one-level-deep field access
- `tests/tsymex_phase4_array.nim` — static array, find an index where `arr[i] == 42`
- `tests/tsymex_phase4_oob.nim` — `arr[i]` where `i` is symbolic, target =
  "the OOB branch", symex finds `i = N` (or `i = -1`)

**Success criteria**: object-heavy SUT (1–2 nested object levels) is
supported. Refs / pointers still rejected with a clear macro-time diagnostic.

**Dependencies**: Phase 3 (objects often appear as proc params or local
state across calls).

### Phase 5 — Dynamic sequences + Table + HashSet (2–3 weeks)

**Goal**. `seq[T]`, `Table[K, V]`, `HashSet[T]` via Z3's array theory. The
biggest surface jump.

**Deliverables**:

- `seq[T]` → `(len: Z3Int, data: Z3Array[Z3Int, sortOf(T)])` pair
- `seq.add` → `len += 1` + `store(data, len-1, v)`
- `seq[i]` → bounds-check fork + `select(data, i)`
- `Table[K, V]` → `Z3Array[sortOf(K), sortOf(V)]` + presence map
  `Z3Array[sortOf(K), Z3Bool]`
- `HashSet[T]` → `Z3Array[sortOf(T), Z3Bool]`
- Stdlib model registry entries for the canonical accessors:
  `[]`, `[]=`, `contains`, `len`, `add`, `del`, `pop`, `pairs` (limited to
  finite small-sized iteration via Phase 6's k-unwinding)
- DSL extension: `dsl_parser` recognizes `in` / `notin` on `Table`/`HashSet`

**Tests**:

- `tests/tsymex_phase5_seq.nim` — target proc takes `seq[int]` and branches
  on length + element values
- `tests/tsymex_phase5_table.nim` — target proc reads `t["foo"]` and branches
  on the value
- `tests/tsymex_phase5_hashset.nim` — target proc tests `x in s` membership
- `tests/tsymex_phase5_models.nim` — stdlib-model audit: each accessor's Z3
  encoding tested in isolation

**Success criteria**: most realistic SUT bodies are walkable. `ref` / `ptr`
/ closures still rejected.

**Dependencies**: Phase 4 (composite types underpin the seq element type).

### Phase 6 — Bounded loops + `case` (2–3 weeks)

**Goal**. Control-flow constructs deferred from Phase 1.

**Deliverables**:

- `nnkWhileStmt` k-unwinding per `SymexSettings.unwindDepth` (default 5);
  unwind exhaustion flags `ePathUnknown`
- `nnkForStmt` over `seq[T]` / `array[N, T]` / `0..N` — desugared via standard
  Nim iterator macros, walked as k-unwound loop
- `nnkCaseStmt` multi-way fork
- `nnkBreakStmt` / `nnkContinueStmt` within unwound loops
- Per-loop unwound-copy isolation: each unwound iteration is a separate path
  state; the loop body's local variables are scoped per iteration to avoid
  cross-iteration aliasing
- Loop-invariant abstraction is NOT done in v1; loops are k-unwound and the
  abstraction layer's range info doesn't carry across iterations (the path
  state re-derives ranges per iteration)

**Tests**:

- `tests/tsymex_phase6_while.nim` — target proc that loops over a small
  `seq[int]` searching for an element; symex finds witnesses for "found" and
  "not found" branches at depth 5
- `tests/tsymex_phase6_for.nim` — for-loop variant of the same
- `tests/tsymex_phase6_case.nim` — multi-way `case` over an enum; one path
  per branch
- `tests/tsymex_phase6_break.nim` — early-exit semantics correct

**Success criteria**: imperative Nim with bounded loops + multi-way `case`
works. Unbounded loops still flag as unknown (this is fine; documented).

**Dependencies**: Phase 5 (loops over seq[T] need Phase 5's seq encoding).

### Phase 7 — proptest engine integration + `assertCoveredBy` (2 weeks)

**Goal**. Symex output integrates with proptest's existing test pipeline.

**Deliverables**:

- `assertCoveredBy(fn, target, testFn)` — if symex finds a witness that
  `testFn` doesn't reach, raise. The CI primitive from #100.
- `Report.symexFindings: seq[SymexFinding]` — when a property uses symex
  internally, the report carries the found witnesses + UNKNOWN counts
- Symex-witness ↔ choice-IR bridge: symex witnesses serialise to the same
  regression-seed format the corpus already understands; bumping Z3 version
  invalidates persisted seeds (Z3-version tag stamped in the seed metadata)
- New engine phase variant `symexProve` in `proptest/engine/phases.nim`
  (#119): runs after `random` but before `shrink` for properties that opted in
- Integration with `forAllUsing(db, …)`: the example database stores symex
  witnesses alongside random ones, tagged by Z3 version
- Cross-Z3-version determinism docs: a section in this plan documenting the
  pin requirement + the seed-invalidation story

**Tests**:

- `tests/tsymex_integration_assertcovered.nim` — end-to-end `assertCoveredBy`
  that fails on a wrongly-unreached branch and passes after a corresponding
  test is added
- `tests/tsymex_integration_phase.nim` — `symexProve` phase runs inside the
  engine pipeline; report carries the findings
- `tests/tsymex_integration_database.nim` — symex witness round-trips
  through the example database; Z3-version mismatch correctly invalidates

**Success criteria**: `assertCoveredBy` is a usable CI primitive. A
hypothetical consumer could add `assertCoveredBy` calls to their PR-diff
gate and get meaningful pass/fail signal.

**Dependencies**: Phases 1–6 (the walker fragment is the substrate);
proptest's #119 engine pipeline; #107 coverage runtime (for the
witness-vs-reached comparison).

### ~~Phase 8 — nkdl-v2 integration~~ (dropped)

The original plan named nkdl-v2 as the champion-consumer phase. That trigger
was retired (see § Trigger history). The next consumer will validate the
plan; the plan does not bind to a specific consumer.

### Phase 9 — Public docs, examples, extraction prep (1–2 weeks)

**Goal**. The door is open for the next consumer and for eventual extraction.

**Deliverables**:

- `docs/symex/README.md` — capability overview, supported fragment, settings reference
- `docs/symex/tutorial.md` — beginner walkthrough using a small toy SUT
- `docs/symex/extending-stdlib.md` — how to add a stdlib model
- `docs/symex/abstraction-internals.md` — the integer-abstraction proof obligations explained for users debugging unexpected results
- `examples/symex_simple.nim`, `examples/symex_oob.nim`,
  `examples/symex_assert_covered.nim`, `examples/symex_table.nim` —
  3–5 worked examples
- Module-boundary review: confirm `proptest/symex/` is self-contained enough
  to extract as `nim-symex` standalone library when a second non-PBT consumer
  surfaces; document the extraction checklist

**Success criteria**: external user can adopt symex from docs alone. Walking
the tutorial start-to-finish produces a working `assertCoveredBy` integration
in under 30 minutes.

**Dependencies**: Phase 7.

## Out of scope for v1

Recorded here so the boundary is explicit:

- **`ref T` / `ptr T` / closures with captures** — needs aliasing/identity
  tracking via Z3 array theory + occurs-check. Phase 4 rejects these with a
  clear macro-time diagnostic.
- **Unbounded loops with invariants** — needs user-supplied loop invariants
  or invariant inference. Phase 6 k-unwinds and tags UNKNOWN beyond depth.
- **Effect tracking** — symex over procs with I/O effects requires per-effect
  models. Phase 5's stdlib registry handles pure stdlib procs; effectful
  procs (`echo`, file ops, network) get the FFI treatment: fresh symbolic of
  return type + `ePathUnknown`.
- **Cross-module visibility** — when target procs depend on private helpers
  in other modules whose AST isn't reachable via `getImpl`. Phase 3 inlining
  works for public/exported callees; private cross-module is rejected.
- **Concurrency** — symex over `Thread`-spawning procs, GC roots, channels.
  Out of scope.
- **Loop-invariant inference, assertion-based range refinement,
  refinement through user-defined function calls** — three deferrals from
  ADR-0001's abstraction layer. Each gets its own follow-up issue from
  Phase 0.
- **Extraction to standalone `nim-symex`** — fires when a second non-PBT
  consumer materializes. Extraction is mechanical given the Phase 9 prep.

## Open questions

Items the plan flags but doesn't resolve. Each is a real design call that
the build will surface:

1. **Path-merging vs. path-forking trade-off**. The plan defaults to path
   forking (one path per branch). For SUTs with high branch counts and
   convergent control flow, path merging can reduce the state explosion.
   Decision deferred to Phase 7's engine integration when real perf data is
   available.
2. **Per-target vs. per-coverage-bitmap symex invocation**. Phase 7's
   `assertCoveredBy` takes a single target; the coverage-bitmap-driven
   variant (#107 integration: "find inputs for every unhit edge") is the
   natural follow-on but not in v1 scope.
3. **The Phase 6 unwind-depth setting's default of 5** is a guess based on
   bounded-model-checking conventions. Phase 8 (now dropped) was supposed to
   tune this against a real consumer. When a new consumer surfaces, the
   default should be validated against their workload.
4. **The `isLoose` setting in ADR-0001** is research-grade. We may discover
   that no real user wants it; if so, drop in Phase 9 cleanup.
5. **Witness serialization format compatibility across nim-z3 minor versions**.
   The Z3-version tag handles major-version invalidation, but nim-z3 minor
   versions may also subtly change `Z3.simplify` output, affecting how
   witnesses get folded before serialization. Worth a regression test.

## Estimated total

| Phase | Weeks (low–high) |
|---|---|
| Phase 0 — ADRs | 1–2 |
| Phase 1 — minimal walker | 2–3 |
| Phase 2 — BV[W] + abstraction | 1–2 |
| Phase 3 — function calls | 2–3 |
| Phase 4 — composite types | 2–3 |
| Phase 5 — dynamic seq/Table/HashSet | 2–3 |
| Phase 6 — loops + case | 2–3 |
| Phase 7 — proptest integration | 2 |
| Phase 9 — docs + examples + extraction prep | 1–2 |
| **Total** | **15–23 weeks (3.75–5.75 months)** for one full-time builder |

Comparable to the M16 engine refactor's scope (which took ~5 months). Not
multi-year.

The first **usable** capability ships at the end of Phase 1 (~3–5 weeks
in): `symexFind` over a small Nim subset. Each subsequent phase widens the
supported fragment, so a consumer with constrained-shape SUTs can start
integrating early and grow with the plan.

## Versioning

The plan ships as a series of patch releases against proptest's post-1.0
SemVer:

- Phase 1 first release → first minor bump that introduces `proptest/symex` (e.g., proptest 1.x.0)
- Phases 2–6 → further minor bumps as the supported fragment grows
- Phase 7 → minor bump that adds `assertCoveredBy` + report integration
- Phase 9 → patch release (docs)

Each phase release is additive — no breaking changes to proptest's
pre-symex surface.

