# Symex (#100) build plan

> The full design and phase plan for the symbolic execution capability tracked
> in [proptest #100](https://github.com/coreyleavitt/proptest/issues/100).
> Updated as decisions land.

## Status

| | |
|---|---|
| **Plan** | live |
| **Build status** | Phases 0-7 + 9 + 10 + 11 + 12 shipped on `main`; symex package feature-complete for v1 minus #138 |
| **Trigger condition** | **none** — build proceeded without a champion consumer per user direction |
| **SMT substrate** | [nim-z3](https://github.com/coreyleavitt/nim-z3) v1.0.0 (SemVer-stable, audit-cycle-closed 2026-05-31) |
| **Test count** | 58 symex test files across all phases, ~222 tests, 0 failures |
| **Walker version** | `"3"` — last bumped at Phase 11 deferral #5 close-out (plain-fields shared). Phase 12 left it untouched and added a separate `renderAsChoicesVersion` constant for serialisation-encoding bumps. |
| **Rendering version** | `"2"` — bumped at Phase 12 cycle 6 (continue-boolean encoding for seq / HashSet / Table witnesses, replacing the latently-broken length-prefix encoding). |
| **Deferrals** | All Shape-B follow-ups (#133-#145) closed except #138; Phase 11 deferrals: 6 of 12 closed, 6 open await consumer demand; Phase 12 deferrals: 15 entries logged in [`docs/symex/PHASE12_PLAN.md`](symex/PHASE12_PLAN.md) (toolchain bugs + intentional v1 scope cuts + cross-cycle corrections). |

### Phase-by-phase

| Phase | Status | Commit |
|---|---|---|
| 0 — ADRs | shipped | `0c7b574` |
| 1 — minimal walker | shipped | `6b73793` |
| 2 — BV[W] + abstraction | shipped | `39ecfa9` |
| 3 — function calls | shipped | `bcb9e8a` |
| 4 — composite types | shipped | `b6fa0a8` |
| 5 — dynamic containers (read) | shipped | `6050e94`, `b52955f` |
| 5 — dynamic containers (mutate) | shipped via rectify | `6922f76` |
| 6 — bounded loops + case | shipped | `d7b5be4` |
| Rectifications round 1 (#137/#140/#142/#143/#144/#145) | shipped | `6922f76` |
| Rectifications round 2 (#133/#134/#135/#136/#139/#141) | shipped | `4381404` |
| 7 — `assertCoveredBy` + Report.symexFindings + DB tag | shipped | `ad9936e` |
| 9 — docs / examples / extraction prep | shipped | `f7c95f9` |
| 10 — content-addressed cache key (SHA-1 over canonical IR + target + settings + Z3/Nim/walker versions) | shipped | `d6f8105` |
| 11 — variant soundness (`itVariant` first-class, walker forks at field access, `tFieldDefect`, case-dispatch witness, plain-fields shared, walker version `"3"`) | shipped | `14cf500` |
| 12 — input-source seeding (three-layered `symexFindAllWitnesses` / `forAllWithSymexSeeds` / `symexForAll` API; `symexSeedPhase` between explicit and random; auto-discovery via IR-scan; `renderingVersion` split from walker version; renderAsChoices continue-boolean fix for collections) | shipped | `ed66c5b` |
| 13 — UNSAT/UNKNOWN verdict caching (three sibling slots `:sat`/`:unsat`/`:unk` under content-addressed key; `queryTimeoutMs → queryRLimit` rename + Z3 `rlimit` wired in `trySolve` for deterministic UNKNOWN; `SymexFinding.fromCache` provenance; DB save/load errors route to `errors` accumulator per the documented `db.nim` contract) | shipped | (pending commit at cycle-12 time) |

### Phase 7 design decision (recorded)

The original spec called for a unified `symexProvePhase` inside the engine
pipeline. During the build we surfaced that this conflated **two distinct
roles** of symex in a PBT loop — *output verifier* ("did the random run
reach this branch?") and *input source* ("seed the random run with corner
cases symex finds"). State-of-the-art hybrid systems (CrossHair,
Driller/QSYM, Korat) keep these separate. The shipped Phase 7 reflects that
decomposition:

| Role | Surface | Status |
|---|---|---|
| Output verifier | `assertCoveredBy(fn, target, testFn = fn, settings)` macro — standalone, single- and openArray-multi-target forms | shipped |
| Reporting sink | `Report[T].symexFindings: seq[SymexFinding]` populated via thread-local `consumeSymexFindings()` | shipped |
| Witness ↔ choice-IR | `renderAsChoices[T](w: T): seq[ChoiceNode]` generic, length-prefixed | shipped |
| Persistence with version tag | `saveSymexWitness` / `loadSymexWitnesses` bucketed under `<testId>#symex#<z3Version>` | shipped |
| Determinism contract | `docs/symex/determinism.md` | shipped |
| Input-source strategy combinator (`withSymexSeeds`) | — | deferred; design fully composable on top of `loadSymexWitnesses` |
| Pipeline phase (`symexProvePhase`) | — | dropped as wrong abstraction; decomposed surfaces above replace it |

19 tests in `tests/tsymex_phase7_assertcovered.nim`, 0 failures.

### Phase 10 design decision (recorded)

The pre-Phase-10 DB key was `<testId>#symex#<z3Version>`. Two problems:

1. **testId is metadata, not identity.** Two tests over the same SUT
   shouldn't have separate buckets.
2. **No invalidation on SUT refactor.** Change the proc body, leave
   testId — the load returns a stale witness.

Phase 10 replaced the key with a SHA-1 content hash over every input
that determines a witness's validity: canonical SUT IR, target,
witness-relevant settings, Z3 version, Nim version, walker version.
Documented in `docs/symex/determinism.md`. The pure key derivation
is `symexCacheKey(prog, target, settings, z3v, nimv, walkerv)` —
testable without macros.

### Phase 11 design decision (recorded)

The pre-Phase-11 variant lowering was a deliberate Phase-4 compromise:
variants flat-tuple'd, witness stubbed as `default(Object)`. Sound
for SUT control flow that gates field access on `kind`, but the
witness was meaningless and the walker's IR was dishonest about
Nim's sum-type semantics.

Phase 11 made variants first-class. Decomposed across 13 cycles plus
a deferral close-out pass:

| Role | Surface |
|---|---|
| IR | new `itVariant` kind with `vArms` + plain-fields prefix; new `isVariantField` and `isVariantReassign` statements |
| Walker | new `svVariant` SymVal; `allocateSym` allocates per-arm + shared plain fields; `walk(isVariantField)` forks (in-arm vs. out-of-arm); `walk(isVariantReassign)` updates disc + zero-inits new arm's primitives |
| New target | `tFieldDefect()` — analogous to `tIndexError()`; satisfied by out-of-arm field accesses |
| Witness construction | case-dispatch in `emitTyAndReader` (drops `default(Object)` stub); plain fields read at shared paths |
| `renderAsChoices` | covers variants via Nim's `fields()` iterator (positional, active-arm only) + new enum branch |
| Abstraction | discriminator's convex-hull interval `[min, max]` logged in `r.abstractions` under `isOptimised` |
| canonicalize | records plain fields separately from arms; walker version `"2"` → `"3"` |

Plain-fields-shared (#5) was identified as a real bug, not just a
soundness lie at the IR level: `obj.kind = X` was zero-initing the
plain prefix because every arm prefixed plain fields. Fixed by
splitting plain from arm-specific in the IR; walker version bumped
to `"3"` to invalidate the old (incorrect) witnesses.

45+ Phase-11-specific tests across:
`tsymex_canonicalize.nim` (variant kind),
`tsymex_typebridge_variants.nim`,
`tsymex_phase11_walker.nim`,
`tsymex_phase11_fielddefect.nim`,
`tsymex_rectify_variants.nim` (migrated).

Full deferrals table in `docs/symex/PHASE11_PLAN.md`. Six of twelve
deferrals closed; the rest await consumer demand (Nim-syntax-rare
patterns + Z3Int promotion of disc).

### Phase 12 design decision (recorded)

Phase 7's split surfaced two roles; Phase 7 shipped the *output
verifier* (`assertCoveredBy`) and deferred the *input source*
("seed the random run with corner cases symex finds"). Phase 12
closes the deferral.

**Three-layered API**, each layer earning its public exposure by
hiding a distinct internal complexity:

| Layer | Surface | What it hides |
|---|---|---|
| 1 | `symexFindAllWitnesses(fn, db, settings, excludeTargets): seq[SymexFinding]` | IR scan + transitive callee traversal + per-target Z3 run + content-addressed cache load/save + sink deposition |
| 2 | `forAllWithSymexSeeds(seeds, s, prop, settings): Report[T]` | Custom pipeline assembly with `symexSeedPhase` slotted between `explicit` and `random`, delegated to the cycle-13 helper `runForAllPipelineWithPhases` |
| 3 | `symexForAll(s, fn, db, ...): Report[T]` | Combines layers 1 and 2; single-arg passes `fn` directly as the property; multi-arg emits a tuple-splatting wrapper from `getTypeInst(s)[1]`. Drains the sink into `report.symexFindings` so the caller has the audit trail without a second call. |

**`symexSeedPhase` placement decision.** The plan considered three
options for where symex witnesses enter the engine:

1. **Replay through `explicit` phase.** Rejected: the explicit
   phase's contract is "no shrinking on user-pinned values" — but
   symex returns *some* satisfying assignment, not a minimal one.
   Z3-produced witnesses are exactly the inputs the shrinker
   *should* minimise.
2. **Strategy combinator.** Rejected: strategies must stay pure
   (random draw), and a seeded strategy would need to commit to
   choice replay vs. fresh generation at construction time.
3. **New pipeline phase between `explicit` and `random`.** Chosen.
   Self-gating on `state.output.rawFalsification.isSome` matches
   every other source phase; the falsification carries forward
   through `shrinkPhase` like any random falsification would.

The closure-capturing seed list required flipping `Phase[T].run`
from `{.nimcall.}` to `{.closure.}` (cycle 2 prerequisite). Top-
level non-capturing phase procs coerce safely; no caller-side
change.

**`renderAsChoicesVersion` ↔ `symexWalkerVersion` separation.**
The walker version covers walker semantics — how the walker
reasons about the SUT. The rendering version covers how a SAT
witness is serialised into the choice IR. Phase 12 cycle 6 fixed
the `seq` / `HashSet` / `Table` encoding (from latently-broken
length-prefix to working continue-boolean); that change rotates
collection witnesses but should NOT touch int / bool / string /
tuple / object / variant witnesses' validity. Splitting into two
constants both in the cache key gives orthogonal invalidation,
with the regression-guarded by tests in
`tsymex_canonicalize.nim` and `tsymex_phase12_renderchoices.nim`.

Phase 12 also surfaced two **spec corrections** during the build
(both recorded in `PHASE12_PLAN.md`'s deferrals table):

- The plan claimed walker-side `RawWitness` readers
  (`readSeqInt`/`readTableStrInt`/`readSetInt`) participated in
  the renderAsChoices round-trip. They don't — they're on the
  in-process `symexFind` codegen path via `emitTyAndReader`,
  independent of choice-IR replay. Cycle 6 dropped the reader
  changes.
- The plan specified `excludeTargets: static openArray[SymexTarget] =
  []`. Nim 2.2 nil-crashes on iterating a default-empty
  `static openArray`; every viable `static seq[T]` default also
  rejects. Cycle 11 dropped `static`, kept the constructor-form
  call ergonomics (`excludeTargets = @[tIndexError()]`), and
  inspects the call-site NimNode AST directly in the macro.

50 cumulative symex test files / ~210 tests / 0 failures after
Phase 12.

### Phase 13 design decision (recorded)

Phase 12 closed deferral #9: UNSAT findings re-derived on every
call. Phase 13 fixes it by extending the content-addressed
cache to non-SAT verdicts AND closing a latent foundational
issue surfaced during the architect review — `queryTimeoutMs`
was never wired to Z3, so any "UNKNOWN via timeout" story was
built on a phantom mechanism.

**Three sibling keys** under the existing `"sx:" & H` namespace
(`:sat` / `:unsat` / `:unk`). UNSAT and UNKNOWN store the
sentinel empty seq `@[]`; `verdictCacheMaxEntries = 1` keeps the
slot's positional invariant unbreakable. `loadSymexVerdictImpl`
checks `:unsat` first — **UNSAT-first load-order tie-break**;
the stronger verdict wins regardless of save order.

**`queryTimeoutMs → queryRLimit` rename + Z3 wiring.** The
pre-Phase-13 field's name suggested wall-clock milliseconds; it
participated in the cache key but was never applied to the
solver. Phase 13 renames it `queryRLimit` (uint, Z3 logical
step count) and wires it via `solver.setParams(p)` with
`p["rlimit"] = settings.queryRLimit; p["random_seed"] = 0'u`.
`rlimit` is deterministic across machines for a fixed Z3 build
(unlike wall-clock `timeout`), making UNKNOWN verdicts
reproducibly cacheable. Default `queryRLimit = 0` keeps
existing callers unbounded — no behavior regression. The
canonicalize tag prefix changes `";to="` → `";rl="` to read
honestly in debug output.

**`SymexFinding.fromCache: bool`.** New field flagging the
load-vs-derive provenance. Closes Phase 12 future-work #6
(cache-hit visibility). Layer 1 sets it true on SAT-cache-hit
and verdict-cache-hit paths; cold paths leave it false.

**DbError contract fix.** The pre-RFC inconsistency: `db.nim`'s
module promise said errors flow to `Report.dbErrors`, but
`saveSymexWitnessImpl` was propagating exceptions and aborting
the analysis with partial findings. Phase 13 wraps the
DB-touching calls and routes failures into an
`errors: var seq[string]` accumulator passed by reference. The
verdict primitives, the witness primitives, and the Layer 1
macro emission all use the same contract.

**Architect review trail.** Two parallel rounds, 4 frames each.
Round 1: 28 findings (5 CRITICAL — including the `queryTimeoutMs`
phantom). Round 2: 15 findings (2 CRITICAL — including a missing
canonicalize test-title rename and a wrong line-number citation).
All baked into the RFC v3 before any TDD slice ran. Zero true
opinion forks escalated; PhD-CS bar resolved every other
question.

**Phase 13 testing**: 7 new test files (`tsymex_phase13_*`)
covering rlimit wiring, suffix migration, verdict primitives,
UNSAT/UNKNOWN round-trips, `acceptUnknownAsCovered` integration
guard, Layer 1 wire (cold/warm UNSAT + cold/warm UNKNOWN), and
verdict macro forms.

58 cumulative symex test files / ~222 tests / 0 failures after
Phase 13.

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

### ADR-0018 — Closure ground-axiom soundness (SND-1b)

**Decision**: reuse the existing `closureForcedUnknown` whole-run degrade
(fed today by `ceClosureUnknownCallee`/`ceInlineBudgetExceeded`) rather than
invent a new precedence mechanism. `applyClosureGround` now skips folding a
closure-body returned sub-path into the ground `currentClosureCallAxioms`
sink whenever that sub-path's `cp.uncertain` is true, and instead pushes a
new `ceClosureBodyUncertain` error kind so `closureForcedUnknown` fires.

**Background** (RFC-chapulin-hardening, Cluster 1, round-2 finding). SND-1
taints every path `uncertain = true` when it crosses an `isUnsupported`
statement or a `maxCallDepth` bail, and the `Path.uncertain` chokepoints
(`isTargetLabel`, `routeRaise`) demote a downstream sxSat/sxRaised reached on
that SAME path. But `applyClosureGround` descends a closure body ONCE via a
second, unregistered raw `Path(...)` construction and folds the body's
returned sub-paths into GROUND Z3 implications pushed into the **global**
`currentClosureCallAxioms` threadvar — drained into *every* subsequent
`trySolve` for the rest of the run. `assertArm` (the axiom emitter) never
consulted `cp.uncertain`, unlike the call-cache, which already refuses to
cache a summary when `frame.returnedPaths[0].uncertain`. A closure body that
silently dropped a mutation (or bailed on `maxCallDepth`) therefore had its
possibly-wrong return value asserted as an unconditional, PERMANENT fact —
SND-1's own repro shape placed inside a closure body still produced a false
sxSat with no recorded error.

**Resolution**. There is no live `Path` at the closure-call `lower()` site to
taint per-occurrence (the same reason SND-1 uses global chokepoints instead
of threading a `Path` through `RawResult`/`w.found`), so the fix is
necessarily coarse: whole-run, not per-occurrence. This matches the
precedent CR-2b already accepts for its own whole-run degrade. Concretely: in
`applyClosureGround`, each of the two return-channel loops (explicit
`return EXPR` sub-paths, and the implicit-`result` fall-through sub-paths)
now checks `cp.uncertain` before calling `assertArm`; an uncertain sub-path
is dropped from axiomatization, and if any sub-path was dropped, a single
`SymexErrorInfo(kind: ceClosureBodyUncertain, severity: sevError)` is pushed
into both `currentClosureCallErrors` (threadvar fallback) and
`w.closureCallErrors` (live `WalkCtx` store), mirroring the existing
`ceInlineBudgetExceeded` push pattern. A clean (fully-modeled) closure
application — no uncertain sub-path — is unaffected: it still axiomatizes
every arm and still yields a valid sxSat.

### ADR-0019 — `isAssume` distinct IR kind (SND-2)

**Decision**: `symexAssume(cond)` gets its own `isAssume` IR kind — NOT a
boolean flag on `isAssert` — so Nim's `case`-exhaustiveness compiler-forces
every switch site touching statement kinds to make an explicit decision for
it. `mkAssume(cond)` mirrors `mkAssert(cond)` structurally (same `acond`
field, added via `of isAssert, isAssume: acond*: IRExpr` in the `IRStmt`
variant). `dsl_parser.nim`'s `symexAssume(...)` marker now lowers to
`mkAssume(...)` (was `mkAssert(...)`, byte-identical to `symexAssert`).

**Background** (RFC-chapulin-hardening, Cluster 1, SND-2, CRIT). `symex.nim`
documents `symexAssume` as filter/prune: conjoin `cond` into the path
condition. But because the parser lowered it to the exact same IR as
`symexAssert`, the `isAssert` walker arm unconditionally forked an
`AssertionDefect` for it too. A genuinely-unreachable target proved `sxUnsat`
cleanly; prepending a violatable `symexAssume` flipped the verdict to a false
`sxRaised(AssertionDefect)` — a false defect masking a correct proof.

**Resolution**. An exhaustive 12-switch-site inventory was walked (every
`case s.kind`/variant-case switch touching `isAssert`):
`abstraction.nim` (`collectAssertRanges`, `collectBan`), `canonicalize.nim`
(cache-key render), `types.nim` (variant decl, `render`), `dsl_parser.nim`
(`emitStmt`), `runtime.nim` (`collectSetLitMembers`, `collectTableLitKeys`,
walker dispatch), `scan.nim` (three auto-discovery switches). Ten of the
twelve are UNIFORM — `isAssume` behaves exactly like `isAssert` there (both
contribute their `cond` to whatever the switch collects) — handled via `of
isAssert, isAssume:` OR-arms. Two are deliberately NON-uniform:

- **Walker dispatch (the one semantic divergence).** The `isAssert` arm does
  four things: (1) `lowerBoolInExpr` + `drainScalarRaiseForks`, (2)
  `drainConvFloatToIntRaises`, (3) `forkDefect(p, not cond,
  "AssertionDefect", …)`, (4) `forkPath(p, p.pc & [cond], …)`. The new
  `isAssume` arm shares (1), (2), (4) VERBATIM and omits ONLY (3). Steps
  (1)/(2) are not assert-specific — they surface raises that arise from
  EVALUATING the condition itself (e.g. `symexAssume(1 div x == 0)` with
  symbolic `x` able to be `0` must still surface `DivByZeroDefect`); only
  the assert-specific defect fork is assume-inapplicable.
- **`canonicalize.nim` cache-key render — MUST diverge.** `isAssert` renders
  `"St<At:...>"`. Sharing that tag would let `symexAssert(c)` and
  `symexAssume(c)` on identical `c` collapse to the SAME cache key despite
  different verdict semantics (a silent-wrong-answer risk), so `isAssume`
  gets a distinct `"St<Am:...>"` tag, mirroring the existing `VR:`/`VRS:` and
  `Nw:`/`Dr:` distinct-tag discipline. This changes cache keys for any SUT
  using `symexAssume`, so `symexWalkerVersion` rotates 39→40.

One further round-2 fix rode along in the same switch inventory:
`abstraction.nim`'s `collectAssertRanges` had an `else: discard` (unlike its
exhaustive sibling `collectBan`) that silently dropped `isAssume`, losing
assume-derived range facts for abstraction seeding — a completeness
regression distinct from the CRIT soundness bug above. Fixed by adding
`isAssume` to the `of isAssert, ...:` arm.

`scan.nim`'s auto-discovery trap was verified rather than changed: the
switch that flags `found[0] = true` (driving `tAssertionViolation`
auto-discovery) intentionally does NOT gain an `isAssume` arm — an
assume-only SUT must not auto-discover an assert-violation search, since
`symexAssume` cannot itself be "violated" in that sense. It falls through
the existing `else: discard` safe default.

### ADR-0020 — Last-resort walker catch → distinct internal-fault kind (CR-1c)

**Decision**: add a single final `except CatchableError as e:` catch-all arm
to the **already-existing** `try/except` in `runSymex` (`runtime.nim`), after
the 18 specific `Symex*Error` arms, the `SymexClassifiedDegradeError` arm, and
the `Z3Error` arm. An unanticipated native exception that escapes the walker
from any dispatch depth matches none of the specific arms and lands in this
catch-all, which classifies it with a new `weInternalWalkerFault` error kind →
`sxUnknown`. Anticipated carriers (the 18 `Symex*Error`, `Z3Error` and its 12
subclasses, `SymexClassifiedDegradeError`) are consumed by their specific arms
*before* the catch-all and behave exactly as before — never conflated with the
internal fault. The slice also introduces a single new generic
`SymexClassifiedDegradeError* = object of CatchableError {kind*: SymexErrorKind}`
carrier + its one dedicated `except` arm, for DELIBERATE pre-classified degrades
(CR-2b reuses it) — distinct from the native-fault safety net above.

**Why the catch is at the `runSymex` boundary, NOT per-`walk`-frame (the
delicate part).** The first implementation wrapped `walk`'s recursive
`case stmt.kind` in its own `try/except` that re-raised anticipated carriers
and converted the rest. On Nim's **C backend** (ORC + goto exceptions) this
crashed with a SIGSEGV (nil read) whenever an anticipated carrier
(e.g. `SymexNotInHandlerError` from `getCurrentExceptionMsg()` outside a
handler) was raised from a statement that was **not** the first in its block:
`walkBlock`'s `result = walk(s, result, w)` loop had already reassigned its
live `seq[Path]` result (whose `Path` elements hold refcounted Z3 ASTs with
custom destructors) on an earlier iteration, and the repeated per-frame
catch-and-re-raise interacting with the ORC destructor unwind of that live seq
corrupted memory. It reproduced on C (both `tsymex_phase15_E8_getcurrentexn`
and `tsymex_phase15_S11_mutation`), was **invisible on C++**, and vanished
under instrumentation (a heisenbug) — the same backend-divergence class as the
`b7258f7` `try/finally` precedent. Moving the single catch onto the outermost,
pre-existing `runSymex` try eliminates it: an unanticipated native now unwinds
**straight through** the whole walk exactly as it did pre-CR-1c (which was
sound — the walker never wrapped its own dispatch), and is caught **once** at
the boundary. No per-frame catch, no re-raise, no new nested `try` (the
`runSymexImpl` comment from `b7258f7`/CR-13 explicitly warns that *any* nested
`try` there swallows re-raises on C). The safety guarantee is identical:
nothing else catches an unanticipated native, so it always reaches the
catch-all regardless of depth.

**Background** (RFC-chapulin-hardening, Cluster 2 — Crash-totality, CR-1c).
The §0 thesis requires the walker to never native-crash on an unmodeled
construct — but exhaustively auditing every reachable `doAssert`/`raise` for
totality does not scale, and each individual fix (CR-1a, CR-1b) only closes
the ONE construct it targets. This ADR makes totality hold **by construction**
for the residual, unforeseen case: whatever the walker's author did not
anticipate anywhere under the walk now degrades to a sound, classified
`sxUnknown` instead of crashing the process.

**Why a DISTINCT kind, not just routing into an existing `se*`/`fe*` kind.**
An ordinary construct-gap kind (e.g. `seUnsupportedStringOp`) means "this SUT
uses a construct the walker doesn't model yet" — an expected, trackable
capability gap. `weInternalWalkerFault` means "the walker itself hit a bug
reaching this statement" — a correctness defect in proptest, not a gap in SUT
coverage. Conflating the two would make a walker bug indistinguishable from
routine unmodeled-construct `sxUnknown` noise, silently closing the very
invariant this ADR exists to keep open. Keeping them distinct lets CI/
telemetry track "how often the safety net fires" as a live walker-bug
backlog — the crash-doctrine's goal (surface walker bugs) is preserved
through classification and audit rather than through an uncaught crash. This
is also why CR-1c does **not** touch the ~63 `doAssert`/~90 `raise
newException` internal-invariant guards elsewhere in `runtime.nim`: those are
`Defect` (`doAssert`) or ordinary `CatchableError` raises the RFC deliberately
leaves alone; the single boundary-level catch-all is the entire mechanism, not
a license to rewrite 150+ existing call sites.

**Why `try/except`, never `try/finally` (hard rule).** Commit `b7258f7` is a
live precedent: an earlier walker-level `try/finally` with no `except` hit
Nim's C-backend goto-based exception model and SILENTLY SWALLOWED a re-raise,
producing a wrong `sxUnsat` instead of `sxUnknown` — a failure mode that was
**C-backend-only and invisible on C++**. CR-1c reuses the existing `runSymex`
`try/except` (no new `try`, no `finally` anywhere), and its regression test
(`tests/tsymex_phase16_CR1c_internal_fault.nim`, run on both `c` and `cpp` via
the standard sweep) asserts the exact verdict (`== sxUnknown`, the
`weInternalWalkerFault` kind present) AND explicitly asserts `!= sxUnsat` /
`!= sxSat`, so a reintroduced swallow-shaped bug on either backend fails that
backend's sweep entry loudly rather than merely "not matching by omission."
The test is fed by a synthetic fault-injection hook
(`when defined(symexTestInjectWalkerFault)` in the `isTargetLabel` arm, wired
only through the test's companion `.nim.cfg`, compiled out of every normal
build) that raises a plain `ValueError` — the same type as an ordinary
internal-invariant guard — so the safety net can distinguish it by nothing
other than "matched no specific arm." The cross-backend requirement is not
cosmetic here: the per-frame first attempt passed on C++ and crashed on C, and
only the both-backend sweep surfaced it.

**Why one generic carrier, not a 19th near-identical type.**
`runtime.nim:47-192` already declares 18 near-identical `object of
CatchableError` carriers, each with its own parallel `except` arm at the
`runSymex` boundary. Minting a 19th for the *deliberate pre-classified degrade*
case would continue that growth indefinitely as future slices add their own
degrade signals. Instead, CR-1c introduces one generic
`SymexClassifiedDegradeError` that carries a `kind*: SymexErrorKind` field and
whose single `except` arm re-emits `SymexErrorInfo(kind: e.kind, …)` verbatim;
CR-2b (and any later slice) raises it with its own kind rather than declaring a
fresh type. (CR-1c's own *unanticipated-native* safety net does not raise this
carrier — it produces the `weInternalWalkerFault` verdict directly in the
`except CatchableError` catch-all, because deliberately raising-then-recatching
inside the walk is exactly the per-frame pattern that crashed on C.) The
existing 18 carriers are named-but-deferred debt this makes trivial to retire
incrementally (each site becomes `raise (ref SymexClassifiedDegradeError)(kind:
seXxx, msg: …)`) — not required by this slice, but the count stops climbing
here.

### ADR-0021 — Ref-object construction as an expression = harden the existing value-tuple arm, NOT a heap allocation (P2b)

**Decision**: `ref object` construction used as an EXPRESSION (`let p =
Node(val: x, next: nil)`, `Node = ref object`) is modeled by EXTENDING the
existing `nnkObjConstr` value-tuple arm (P2a) to soundly handle ref/ptr-typed
FIELDS — NOT by synthesising a new `isNew`-allocation + `mkFieldDerefWrite`
preamble (the RFC's original sketch). There is deliberately no ref-vs-value
branch in the arm: `classifyType` already unwraps a NAMED `ref object` alias
to the identical `tTuple(fields, fieldNames, objectName)` shape a plain value
object produces (`dsl_typebridge.nim`'s "#136: unwrap ref T / ptr T",
~195-205), so P2a's arm was *already*, silently, reached for ref-object
constructors — every ref/ptr-typed field simply degraded to `sxUnknown`
because (a) a bare `nnkNilLit` field value has no general `parseExpr` arm
outside the `==`/`!=` nil-comparison special case, and (b) an omitted
ref-typed field has no `zeroValueForType` encoding (its `else: nil`
catch-all does not cover `itRef`/`itPtr`). P2b closes exactly that gap:

- `next: nil` → `mkNil(fieldTy)` directly, using the FIELD's own declared
  type (the field-position value never reaches the general `parseExpr`
  recursion for this shape).
- An OMITTED ref-typed field → `mkNil(fieldTy)`. This is Nim's REAL zero for
  a ref/ptr (sound, not a degrade — the same "genuine zero-init" argument
  P2a already established for scalar fields via `zeroValueForType`).
- A PRESENT ref-typed field whose value expression does NOT resolve to a
  genuine ref/ptr address (`refExprClassify`, below) degrades THAT FIELD ONLY
  (`feUnsupportedExprKind` + `mkUnsupported`, SND-1 taints the whole run to
  `sxUnknown`) and fills the slot with a type-COMPATIBLE `mkNil` — never a
  shape-mismatched value.
- A VARIANT object constructor (`itVariant`/`itMultiVariant`) reaching this
  arm is GUARDED: register the classified error and return a reference to a
  FRESH, deliberately UNBOUND synthetic var name (never `mkLet`/`mkAssign`-
  bound) rather than a type-mismatched scalar dummy — see the crash-avoidance
  rationale below. This retroactively hardens a **P2a gap**: a variant
  constructor (ref OR value) reaching the ORIGINAL P2a arm hard-crashes macro
  expansion today (`objTy.fieldNames`/`.fields` do not exist on an
  `itVariant`/`itMultiVariant`-kinded `IRType` — empirically confirmed:
  `VNode(kind: true, a: x)` for a `case`-fielded `VNode` fails to compile the
  SUT at all, pre-P2b). Variant object construction stays explicitly
  EXCLUDED (round-2 decision) — the field-split heap already declines
  variant READS (`heRefVariantUnsupported`); construction needs its own ADR
  revisiting that read gap.

**Background**. The RFC's sketch for P2b was: mint a fresh ref via `mkNewT`
(an `isNew` allocation), write each present field via `mkFieldDerefWrite`
into the field-split heap (the SAME machinery R6/R9 already use for
`p.field = v` on a genuine heap ref), and return a read of the fresh ref —
mirroring how `let p = new(Node); p.val = x` already works at the
LET-STATEMENT level (R1a/R2). This was investigated and EMPIRICALLY
REJECTED, not merely deemed inconvenient:

**The empirical finding.** `let q = new(Node)` for a NAMED `ref object`
alias — the RFC's own canonical linked-list example, and the ONLY shape that
needs a *named* self-referential type — CRASHES today, before any P2b code
existed: `field 'refPointeeTy' is not accessible for type 'IRType' using
'kind = itTuple' [FieldDefect]`. Root cause: the existing R2 let-section
`isNewCall` arm computes the bound name's type via
`classifyType(id[j])` and hands it straight to `mkNewT` (which unconditionally
expects an `itRef`/`itPtr`-kinded `IRType`) — but `classifyType` UNWRAPS a
named `ref object` alias to `itTuple`, ALWAYS, for ANY symbol (`nnkSym`)
whose static type resolves to that alias, regardless of whether the symbol is
a formal parameter or a `let`-bound local (Phase 16 D1a's deliberate
value-modelling of bare ref-object-alias symbols does not distinguish origin
— it is purely a function of the symbol's own static Nim type). This is a
PRE-EXISTING gap in R2, orthogonal to P2b, that this investigation surfaced
as a side effect (out of scope to fix here — R2's `new(Point)`-style INLINE
`ref T` case, the only shape R6/R9's existing tests exercise, is unaffected
and untouched).

Even setting that crash aside, the sketch has a deeper architectural
incompatibility with this parser's ALREADY-LOCKED design (Phase 16 D1a): ANY
`svRef` a heap-based P2b construction minted for `p` would be **invisible**
to every OTHER read of `p.field` in the same SUT. Each such read
independently re-derives `p`'s classification from the AST at its OWN call
site (`classifyType(p)`), and for a bare symbol of a NAMED ref-object-alias
type that ALWAYS unwraps to `itTuple` (value semantics) — the read routing
decision does not, and structurally CANNOT, consult how `p` was constructed.
So even a successful heap allocation would bind `p` under a DECLARED type
(`itTuple`, from the let-section's own independent `classifyType(id[j])`
call) inconsistent with its bound VALUE's kind (`svRef`), and the very next
`p.val` in the SUT body would take the ordinary VALUE-tuple field-access path
(`mkField` expecting `svTuple`), not the field-split-heap path — a
`SymVal`-kind mismatch at `env["p"]` lookup, not a sound read of the
allocated heap cell.

**Why this is sound, not merely convenient.** Reusing the value-tuple model
means a `ref object` constructed as an expression is treated exactly like the
existing `n: Node` bare-PARAMETER precedent (R9's `walk4` test, `tests/
tsymex_phase15_r9_recursive.nim`: "`n: Node` is VALUE-MODELLED (svTuple, not
svRef)") — a deliberate, ALREADY-SHIPPED design point, not a new
approximation invented for P2b. A field ONE LEVEL DEEPER than a bare
value-modelled node (`p.next`, itself carrying a genuine `svRef` value
because the FIELD's own type is heap-ref-classified via `classifyFieldType`)
still correctly routes through the field-split heap for further access
(`p.next.next`) — this hybrid (bare symbol = value snapshot; a value's OWN
ref-typed field = a real heap address once dereferenced one level) is exactly
R9's existing, tested behavior, unmodified by P2b.

**Why the variant-guard's degrade returns an unbound `mkVar`, not a
type-mismatched `mkIntLit(0)` (the crash-avoidance detail).** `env` is a
plain `OrderedTable[string, SymVal]`; reading a name that was never
`mkLet`/`mkAssign`-bound raises `KeyError`, a `CatchableError` — caught by
ADR-0020's `runSymex` boundary safety net (`weInternalWalkerFault` →
`sxUnknown`). Binding the SAME name to a WRONGLY-KINDED-BUT-PRESENT `SymVal`
instead (e.g. a scalar `0` under a name whose DECLARED type is `itVariant`)
is unsafe: a later variant-field access on it reaches `isVariantField`'s `of
… else: doAssert false, "isVariantField on non-variant SymVal kind=…"` — an
`AssertionDefect`, which is a `Defect`, NOT a `CatchableError`, and therefore
is **not** caught by the ADR-0020 safety net — a genuine, uncatchable process
crash. The missing-key path fails BEFORE the mismatched-kind dispatch is ever
reached (the `KeyError` fires while resolving the receiver, one step earlier
than the `case recv.kind` that would otherwise crash), which is why it is the
correct degrade shape here, not merely an equally-valid alternative.

**Scope note.** Recursive construction FROM an existing allocated ref (e.g.
`next: (some `ref int`/`ref Point`-INLINE-typed expression)`) is NOT excluded
by this ADR — `refExprClassify`'s two-level check (mirroring the existing
nil-comparison and R9 recursive-field-read classifiers) accepts any value
expression that genuinely resolves to `itRef`/`itPtr`, which includes a
one-level-deep field read off ANOTHER node (`otherNode.next`) or an inline
`ref T` parameter. Only a BARE symbol of a NAMED ref-object-alias type
(value-modelled, no address) is degraded.

### ADR-0022 — Named ref-object HEAP IDENTITY (Cluster H; SUPERSEDES ADR-0021's value-model for P2b)

**Status**: PROPOSED (design doc; awaiting implementation). Reopens P2b per Corey
(2026-07-23) to model `ref object` construction — and named-ref-alias symbols
generally — with true heap identity, so aliasing and reference identity yield REAL
verdicts instead of the `sxUnknown` degrades ADR-0021 produced.

**Context — this is completing a deferred follow-up, NOT overturning a locked decision.**
The value-model of a bare symbol whose static type is a NAMED `ref object` alias
(`type Node = ref object` → `classifyType` unwraps to `itTuple`) is *pre-existing
Phase-14 `classifyType` behavior* (`dsl_typebridge.nim:195-213`, the "#136 unwrap
ref T / ptr T" path), written BEFORE the heap model existed, whose own comment reads
"Aliasing tracking is a follow-up" (`dsl_typebridge.nim:196`). It was never revisited
for the named case after Phase-15 Cluster R landed the field-split heap. ADR-0021's
"Phase 16 D1a" attribution is retroactive — **no ADR ever weighed heap-identity for
named ref aliases and rejected it.** ADR-0021 rejected heap-alloc for the P2b
construction case *specifically*, on two grounds that this ADR resolves at the root:
(a) `mkNewT` crashed because `classifyType` handed it an `itTuple` `nRefTy`; (b) a
constructed `svRef` would be invisible to later `p.field` reads that independently
re-classify `p` as `itTuple`. **Both vanish once `classifyType` classifies the symbol
class as `itRef`** — construction and every read then agree on the heap representation.

**The machinery already exists and is tested — for INLINE `ref T` only.** Cluster R
(R6/R7/R9, ADR-0009/0010/0013) fully implements heap identity: `svRef` carries identity
as a shared Z3 term (`let q = p` aliases for free; a `store` through one alias is
visible to a `select` through the other — `tsymex_phase15_r7_alias_chain.nim`); `p == q`
is real address-equality (`refEq`, `runtime.nim:2339`); freshness is asserted for `new`
(`runtime_heap.nim:64-133`); and alias-group WITNESS rendering already works
(`heapSnapshot` with `pointsTo`/`aliasRef`, `runtime.nim:3780`, ADR-0010 H7/H21). The
sole gap: named aliases never route here because `classifyType` unwraps them first.

**Decision.** Generalize Cluster R's heap identity from inline `ref T` to NAMED
ref-object aliases via a classification-policy change, then let the existing heap paths
engage. Supersede ADR-0021's value-modeled construction with the RFC's original
`mkNewT` + `mkFieldDerefWrite` shape (now well-formed).

**Root change.** `classifyType` (`dsl_typebridge.nim:195-213`): a bare symbol whose
static type is a named `ref object` alias classifies as `itRef(pointeeObjectType)`,
NOT `itTuple`. The pointee object is built via the existing plain-record path but must
NOT infinitely recurse on self-referential types (`Node.next: Node`) — reuse
`classifyFieldType`'s `namedRefPlaceholder` idiom (`dsl_typebridge.nim:468-483`) so a
bare symbol and its own ref-typed field agree on representation. **Reconciling
`classifyType` (bare) with `classifyFieldType` (field) on the SAME named type is the
highest-risk part of the change** and gets its own slice (H1).

**Site-by-site routing plan** — each gate below currently gates on
`classifyType(...).ty.kind in {itRef,itPtr}` and DELIBERATELY excludes named aliases
(matching today's value-model). Each flips from excluding to routing through the
already-built heap path:

| Site | File:line | Flip |
|---|---|---|
| param/let binding | `runtime.nim:1614` (itTuple) → `:1449` (itRef arm) | mint a FREE `Ref_T` const (param semantics — NOT `freshRef`/`assertFreshness`, which are `new`-only) |
| `let p = new Node` | `dsl_parser.nim:3010`, walker `runtime_heap.nim:669` | crash site resolves — `nRefTy` now `itRef` |
| `var p; p = new Node` | `dsl_parser.nim:2508`, `2603` | `isNewCall` gate now passes |
| field READ `p.f` | `dsl_parser.nim:1306-1352` (bare-sym exclusion at 1326) | remove exclusion → `mkFieldDeref` |
| field WRITE `p.f = v` | `dsl_parser.nim:2556-2572` | gate passes → `mkFieldDerefWrite` |
| `p == q` / `p != q` | `runtime.nim:2339` `refEq` vs `symEq` raise at `2142` | route ref operands to `refEq` |
| `p == nil` | `dsl_parser.nim:1104-1146` bare-sym special-case | becomes dead — Level-1 classify suffices |
| R9 hybrid boundary | `dsl_parser.nim:1315-1330` | becomes redundant; verify no double-dispatch |
| construction (P2b) | the `nnkObjConstr` arm | `mkNewT(tmp,refTy)` + per-field `mkFieldDerefWrite` + return `mkVar(tmp)` |
| `refExprClassify` | `dsl_parser.nim:2421-2439` | bare node now resolves `itRef` → `sutRecursiveFromBareNode` flips degrade→real |

**Construction (P2b proper).** When the constructor's classified type is
`itRef(pointeeObject)`: `preamble.add mkNewT(tmp, refTy)`; for each present field
`preamble.add mkFieldDerefWrite(mkVar(tmp), val, fieldTy, pointee, name, isPtr=false)`;
return `mkVar(tmp)`. **Omitted-field zero-init (re-opened in the heap model):** a
field-split heap array is a FREE Z3 const, so `select(freshRef)` on an unwritten field
is NOT automatically a sound zero — so omitted fields need EXPLICIT zero-writes
(`mkFieldDerefWrite` with `zeroValueForType`/`mkNil` for the field's type). Determine
empirically in H4 and encode.

**Sub-decisions (resolved).**
1. **Variant ref objects** (`type N = ref object` with `case` fields): stay EXCLUDED /
   degrading. The field-split heap already declines variant reads
   (`heRefVariantUnsupported`, ADR-0013); variant heap identity needs its own ADR that
   revisits that read gap. The ADR-0021 variant-guard (crash-avoidance) is PRESERVED.
2. **`renderAsChoicesVersion` bumps 5→6** (unlike value-modeled P2b, which correctly did
   not). Named-alias PARAMS becoming `svRef` makes them eligible for
   `heapSnapshot`/alias-group witness rendering — a new witness shape for a parameter
   class. `symexWalkerVersion` also bumps (broad verdict-surface change).

**Test impact.** Cases that ADR-0021 left at `sxUnknown` FLIP to real verdicts and their
tests update accordingly: `tsymex_p2b_refobjconstr_expr.nim` (`sutRecursiveFromBareNode`
degrade→real; add aliasing + identity SAT/UNSAT tests), and the R9 value-model
expectations (`tsymex_phase15_r9_recursive.nim:36-38` "`n: Node` is VALUE-MODELLED"
comment + guards flip to heap-modeled — `n != nil`, `n == n2` now supported). Every
existing Cluster-R heap test (R6/R7/R9/R12) MUST stay green. `42eafde` is SUPERSEDED
(construction arm replaced), not `git revert`ed; its variant-guard fix survives.

**Slicing (H-cluster).**
- **H1** — `classifyType` named-alias → `itRef`; reconcile with `classifyFieldType`
  (recursion/placeholder); param alloc → free `svRef`. DoD: `n: Node` param is `svRef`;
  `n == n2` real verdict; R9 tests updated; heap tests green.
- **H2** — enable bare-symbol field read/write routing. DoD: aliasing
  (`q=p; q.val=99; p.val==99` → real `sxSat`); non-alias independence preserved.
- **H3** — `let p = new Node` + var-rebind (resolve the crash site).
- **H4** — construction (P2b proper): real heap alloc + field-writes + omitted-field
  zero-writes; supersede `42eafde`'s value arm.
- **H5** — nil-compare + `==`/`!=` routing; delete dead value-model workarounds.
- **H6** — witness rendering: named-alias params via `heapSnapshot`/alias-group; RC bump
  5→6; witness replay tests.
- **H7** — variant guard preserved; SW/RC pins; full sweep both backends.

**Risks.** (1) The H1 classifyType/classifyFieldType reconciliation on self-referential
types. (2) Blast radius — every routing gate re-audited; a missed one silently reverts a
case to value-model (unsound if it now claims a verdict). (3) The R9 value-model tests
are load-bearing and must be re-reasoned, not just flipped to pass.

---

### ADR-0022 Round-1 architect review (2026-07-23) — findings applied

A 4-lens review team (depth/breadth/design/feasibility) found the ORIGINAL H1 above was
**self-contradictory** and revised the design as follows. The four lenses converged on one
root cause; the resolution below supersedes the "reuse the empty placeholder for the bare
symbol" instruction in **Root change** above.

**Root contradiction.** The empty `namedRefPlaceholder` (`dsl_typebridge.nim:468-483`) is
load-bearing for BOTH (a) Z3-sort identity — `refPointeeTypeId` = sanitized `$pointeeTy`
(`runtime_heap.nim:25-33`), and `$` for `itTuple` is STRUCTURAL over the field list
(`types.nim:1662-1668`), so a bare `n: Node` and a field `x.next: Node` share the
`Ref_Node` sort ONLY if their pointees render identically → forces the empty placeholder
everywhere; and (b) recursion termination. BUT three consumers need the FULL field list /
a real value off that SAME pointee: construction (`objTy.fieldNames`,
`dsl_parser.nim:2089-2096`), the witness reader (`emitTyAndReader`'s itRef arm stubs an
empty-fielded named placeholder to `nil` regardless of the model, `symex.nim:983-988`; same
in `isRenderableWitnessTy`, `types.nim:1535-1544`), and `new(Node)` field zero-init. No
single pointee representation satisfies both — as literally written, if placeholder-consistency
wins, every named-alias constructor mis-degrades and every param witness renders `nil`; if
full-fielded wins, cross-site sort identity breaks (`Z3SortMismatchError`).

**Resolution — decouple sort-identity from field-presence.** Key Z3-sort identity on a
**canonical NOMINAL type id** (the object's symbol-unique name PLUS its generic
instantiation args), NOT the structural `$fields` string. Change `refPointeeTypeId`/`$` for
named-object pointees accordingly. Then:
- Bare named-ref symbol → `itRef(FULL pointee)` (real fields; recursive ref-typed fields
  stay `itRef(placeholder)` via `classifyFieldType`, so classification still terminates).
- The recursive field's placeholder and the bare symbol's full pointee **share the same
  `Ref_Node` sort** via the nominal id — sort identity holds regardless of field-presence.
- Construction reads real fields off the full pointee ✓. Witness reader reads real fields ✓
  (the `nil`-stub now fires ONLY for genuinely recursion-truncated nested fields — the
  existing, sound R9/R11b approximation — never for a top-level param).
- **Generic disambiguation falls out for free**: the nominal id includes the instantiation,
  so `Box[int]` and `Box[string]` get distinct `Ref_Box_int` / `Ref_Box_string` sorts (this
  also fixes a latent monomorphization-collision of the same class as Cluster G; key on
  symbol identity / mangled args, NOT bare `strVal`).

**Additional required fixes (were missing):**
1. **Universal zero-write on `isNew`** — the `isNew` walker arm (`runtime_heap.nim:651-688`)
   must zero-write EVERY field of an object pointee (via `mkFieldDerefWrite` with
   `mkNil`/`zeroValueForType`), not just omitted `nnkObjConstr` fields. A fresh Z3 heap array
   is a FREE const (`mkHeapArrayVar`), so an unwritten field `select` is unconstrained →
   `p.next != nil` after a bare `new(Node)` would be falsely SAT (Invariant-3 violation).
   This is unconditional for `new`, independent of the construction arm.
2. **Preserve variant detection** — `namedRefPlaceholder` is variant-blind (no `hasRecCase`
   check). Detect variant-ness on the FULL pointee (via the existing plain-record
   `hasRecCase` path) BEFORE routing, so a `ref object` with `case` fields still hits the
   H7 exclusion / `heRefVariantUnsupported` guard and never falls through as a zero-field
   heap construction (which would lose ADR-0013's arm-aware FieldDefect discipline).

**Slicing revised.** Because every downstream routing site already gates on
`classifyType(...).ty.kind in {itRef,itPtr}` (parser) or runtime `SymVal.kind in
{svRef,svPtr}`, flipping `classifyType` **automatically** activates field read/write,
`new`/var-rebind, `refExprClassify`, and `==`/`!=`→`refEq` with ZERO new code at those
sites. Therefore:
- **H1 is the atomic root commit** and MUST fold in: the classifyType flip;
  the nominal sort-id change; `H1a` extract a construction-only `classifyObjectRecordFields`
  (full fields, bypassing the ref-wrap); `H1b` widen the construction guard
  (`dsl_parser.nim:2078`) to accept `itRef`/`itPtr` (route via the helper, still
  value-constructing pending H4); `H1c` teach `emitTyAndReader`/`isRenderableWitnessTy` to
  read real fields for a top-level param (nil only for recursion-truncated); the universal
  `isNew` zero-write; the variant-detection preservation; **and the SW + RC 5→6 bumps**
  (buildHeapSnapshot starts populating for named-ref params the instant H1 lands — gated on
  runtime `svRef` kind, `runtime.nim:3776` — so RC MUST bump here, not at a later H6).
  H1 has genuine RED→GREEN behavioral tests: `n == n2` and `n != nil` on bare `Node` params
  flip from unsupported to real verdicts.
- **H2/H3/H5 → verification checkpoints** (add aliasing/identity/nil tests; confirm the
  auto-activated routing behaves), NOT separate production changes.
- **H4** = real heap construction (replace `42eafde`'s value-tuple fill with `mkNewT` +
  per-field `mkFieldDerefWrite`; keep the field-loop skeleton + widened variant guard;
  omitted-field zero-writes with a RED test PER field-type — a missed zero-write = a free
  unconstrained heap cell = silent soundness bug). SW bump.
- **H_containers** (NEW) — `seq[Node]`, `Table[K,Node]`, `array[N,Node]`, `tuple[a:Node]`
  classify elements via plain `classifyType` (`dsl_typebridge.nim:78,143,391,396,402`), so
  they auto-flip to `itRef` under H1; add construction/access/witness tests. (Scope: see
  fork below.)
- **Refactor (fold into H1)** — extract `isHeapRef(n: NimNode): bool` for the repeated
  `classifyType(x).ty.kind in {itRef,itPtr}` idiom and grep-replace all ~10 sites, so the
  audit surface is one identifier; and DELETE (not flip) the 3 explicit bare-symbol
  carve-outs that actively suppress `itRef` (`dsl_parser.nim:1327-1331`, `refExprClassify`
  at `:2436`, and its user at `:2106`).

**Expanded test-impact (re-reason, do NOT relabel).** Beyond `tsymex_p2b_refobjconstr_expr`
and `r9_recursive`: `r9_recursive` heap-depth counting now starts ONE LEVEL EARLIER
(`n.next` becomes a real deref) — re-derive the `maxHeapDepth=3/8` arithmetic;
`tsymex_phase15_r10_budget.nim`, `tsymex_phase15_r11b_smoke.nim`,
`tsymex_rectify_refs.nim` rely on the value-model exemption from the unconditional nil-fork
and will shift — re-reason their expected verdicts. R6/R7/R12 use only inline refs — unaffected.

**Scope decisions (Corey-resolved 2026-07-23).**
1. **Containers IN Cluster H.** `seq[Node]`/`Table[K,Node]`/`array[N,Node]`/`tuple[a:Node]`
   auto-flip to `itRef` under H1, so they get their own slice (**H_containers**) with
   construction/access/witness tests — no untested surface ships.
2. **Generics — minimal disambiguation now.** The canonical nominal sort-id includes the
   generic instantiation args (symbol-unique, mangled), so `Box[int]`/`Box[string]` get
   distinct sorts — closing the collision as a SOUNDNESS fix in H1. Full generic-ref FEATURE
   work (beyond not-colliding) defers to Cluster G (the monomorphization-collision locus).
3. **Unify all refs on one nominal sort-id scheme.** Inline `ref T` (R6/R7) and named-ref
   pointees both move to the nominal id — a single sort-naming code path, not two. R6/R7
   stay green by construction (inline-ref pointees are also nominally identifiable); their
   existing tests cover the change.

### ADR-0022 Round-2 architect review (2026-07-23) — findings applied

Round 2 (4-lens team on the revised design) confirmed the plan is **buildable** — the
canonical nominal-id primitive was empirically verified against the dev Nim toolchain — and
supplied concrete refinements + two honest scope corrections. Applied:

**Nominal-id primitive — CONCRETE (was an under-specified IOU).** The canonical id is a
recursive `nominalId(n: NimNode): string` computed from Nim's `signatureHash`, carried as a
first-class `nominalId: string` field on `IRType` (NOT a re-derived string, NOT bare
`strVal` — bare `strVal` would merge same-named types from different modules). Verified
behavior: `nnkSym → signatureHash` is STABLE across independent classify call sites (so a
bare symbol's full pointee and a recursive field's placeholder for the same type get the
same id); a generic instantiation's `getTypeInst` is `nnkBracketExpr` and `signatureHash`
on it is a hard compile error, so the helper MUST dispatch on `.kind`:
`nnkSym → signatureHash`; `nnkBracketExpr → head.signatureHash & concatMap(args, nominalId)`
(distinguishes `Box[int]`/`Box[string]` via the args — the head hash is
instantiation-independent); fallback `→ .repr` for `static[int]`-style args. **ONE shared
helper** is used by both `classifyType`'s full-pointee arm AND `namedRefPlaceholder`
(`dsl_typebridge.nim:468-483`) — else a generic self-referential type's bare pointee and
its own `next` field placeholder compute different ids → `Z3SortMismatchError`. Change
**`refPointeeTypeId` ONLY** (`runtime_heap.nim:25-33`, prefer `nominalId`, fall back to
`$pointeeTy` for anonymous tuples) — do NOT touch the general `$` (it feeds ~9 diagnostics
no test protects). `IRType.==` stays STRUCTURAL (a full pointee and a placeholder are
`==`-unequal but share a sort) — `refPointeeTypeId`/`nominalId` is the ONLY nominal-equality
channel; a one-line note steers future code away from "fixing" `==` to be nominal.

**H1 must fold in H4's core (CRITICAL — no interim regression).** H1b's original "still
value-constructing pending H4" is REMOVED: because the field-read routing is a parse-time
decision with no runtime fallback (`dsl_parser.nim:1304-1353` → walker raises
`SymexRefUnresolvedError` → `sxUnknown` on an `svTuple` where it now expects `svRef`),
leaving construction on `mkTupleLit` would regress ALL of `tsymex_p2b_refobjconstr_expr.nim`
(P2b-1..8) to `sxUnknown` between H1 and H4. So H1 emits **real** `mkNewT` +
per-present-field `mkFieldDerefWrite`. The universal `isNew` zero-write then handles omitted
fields, so H4 collapses into H1 (H4 as a separate slice is eliminated).

**Sym-indirection form (CRITICAL).** H1 must ALSO patch `classifyType`'s
`inner.kind == nnkSym` branch (`dsl_typebridge.nim:204-205`) — `type NodeRef = ref Obj`
currently collapses to `classifyType(Obj) = itTuple` with no ref-wrap, so a bare
`p: NodeRef` would stay value-modeled while its fields go heap-modeled (a divergence, and
`p == nil` falls through to a nonexistent `nnkNilLit` arm). Route it to `itRef(full pointee
of Obj)` keyed on **Obj's** nominal id. RED test: `p: NodeRef; p == nil` + field-write.

**Witness top-level-vs-truncated needs a provenance flag (HIGH).** The existing
`fields.len == 0` heuristic (`symex.nim:983-988`, `types.nim:1535-1544`) that renders a
recursion-truncated placeholder as `nil` is AMBIGUOUS for a legitimately **zero-field**
named ref type (`type Token = ref object` — no fields): its top-level full pointee is also
`fields.len == 0`, so a proven-non-nil `p: Token` would mis-render as `nil` (unsound
witness). Thread an explicit provenance/recursion flag rather than overloading the
field-count. Also extract `isRecursionPlaceholder(ty)` (the sniff is already duplicated at
two sites) alongside `isHeapRef(n)`.

**Universal `isNew` zero-write refinements.** H4's separate omitted-field zero-write is
DROPPED (redundant): the construction arm writes only PRESENT fields; `isNew` zero-writes
the rest. `zeroValueForType` (`dsl_parser.nim:2406-2419`) covers only primitives+string —
extend it to recurse into `itTuple` (bounded: Nim forbids cyclic VALUE nesting) for a
by-value nested-object field, OR scope the `isNew` zero-write to primitive+ref fields and
degrade (SND-1 taint) on a by-value nested-object field, documented. Cost is linear in field
count (no cap needed; confirmed). Recursive ref-field zero = `mkNil(fieldTy)` — sound, the
nil-const self-heals (`iekNil` calls `allocRefSort` first, `runtime.nim:3155-3169`).
(Deeper alternative noted for a future pass: default-initialize `mkHeapArrayVar` via
`Z3_mk_const_array` seeded with the field zero — confines the invariant to one proc,
touch-order-independent — but the per-field-store version is the shippable H1 form.)

**Container coverage CORRECTED (scope decision 1 refined).** Only `seq[Node]`,
`array[N,Node]`, and `tuple[a:Node]` become newly-real under H1. **`Table[K,Node]` /
`HashSet[Node]` stay degraded regardless** — `allocateSym` hard-restricts table keys to
string / values to int (`runtime.nim:1640-1665`) and set elems to int64 (`:1666-1678`),
orthogonal to Node's ref-ness. `H_containers` also needs an `itRef` arm added to
`storeSeqElem` (`runtime.nim:6783-6817`, currently raises on object elems) for `seq[Node]`
LITERAL construction, and its own SW bump. Per-element `seq[Node]` witness fidelity is
length-only (the `extractSeqElements` itRef arm is a deferred R11b/R12 stub) — a documented
ceiling, not full coverage.

**Landing order (de-risked, replaces the flat H1→H7).**
- **Step A** — pure plumbing: add `IRType.nominalId` + the `nominalId(NimNode)` helper,
  populate at all `tTuple` sites incl. `namedRefPlaceholder`. Zero runtime change;
  macro-time unit-testable (`nominalId(Node)==nominalId(Node)`, `Box[int]!=Box[string]`);
  independently bisectable, no Z3/sweep.
- **Step B** — flip `refPointeeTypeId` to prefer `nominalId` (fallback `$`). Verify against
  the INLINE-ref surface only (R6/R7/R9/R12) — named aliases don't reach `itRef` yet — so the
  sort-naming mechanism is proven green before the risky commit.
- **Step C = the atomic H1**: `classifyType` flip (BOTH `nnkObjectTy` and `nnkSym` branches)
  + `classifyObjectRecordFields` shared core (owns the `hasRecCase` variant gate) + real
  `mkNewT`+`mkFieldDerefWrite` construction + universal `isNew` zero-write + witness
  provenance flag + `isHeapRef`/`isRecursionPlaceholder` extraction + delete the 3
  bare-symbol carve-outs + **SW 54→55 + RC 5→6**.
- Then **H_containers** (storeSeqElem arm + seq/array/tuple tests; own SW bump) →
  **verification** slices (aliasing/identity/nil RED tests) → **H_final** (variant-arm test,
  full sweep, pins).

**Confirmed sound (no change):** cyclic construction; nil-const self-healing; zero-write cost
bound; test-impact list is COMPLETE (5 tests — `p2b`, `r9`, `r10`, `r11b`, `rectify_refs` —
breadth verified no untracked regressions).

**Two scope items returned to Corey (see handoff Open forks):** (1) generics — round 2 found
NO live `Box[int]`/`Box[string]` collision (generic ref-objects are `itUninterp`→`sxUnknown`
today), so the sound-minimal is keep-`sxUnknown`+guard+test and defer generic-object support
to Cluster G — revises the premise of the round-1 "minimal disambiguation now" answer;
(2) witness-rendering scope — accept LIMITED (direct param↔param aliasing renders; one-hop /
container-element / param↔constructed-node aliasing + per-element seq fidelity are known
future gaps; VERDICTS stay fully sound) vs. pull recursive-`pointsTo` witness work into
Cluster H.

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

