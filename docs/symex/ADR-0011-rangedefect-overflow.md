# ADR-0011 — Defect-flow architecture (unified raise model) + arithmetic-defect modeling

> **STATUS: DRAFT STUB — PROPOSED, not accepted.** Captured 2026-06-27 from the
> Phase-15 review session, then hardened in the round-1 `/architect` review.
> Governs **Cluster D** (defect-flow unification — the cross-cutting decision) and
> **Cluster R16** (arithmetic defects) of
> [RFC-phase16](RFC-phase16-language-fragments.md). It records the design space,
> the open forks (with leans), and a proposed cycle breakdown — enough that the
> work can be scheduled without re-deriving the mechanics. Citations are
> point-in-time (post-Phase-15, walker `v17`); re-verify at `/tdd` time.

## Context (current state — from the mechanics fact-sheet)

The engine has **two unrelated mechanisms** for "something bad happens", and this
is the crux of the design:

1. **Target-based defects** — `IndexDefect` (array/seq OOB), `FieldDefect`
   (variant wrong-arm access), `AssertionDefect` (`doAssert`). When the active
   *target* is the matching `stk*` kind, the walker forks the error condition,
   `trySolve`s it, and emits a direct **`sxSat`** finding ("here's an input that
   makes `arr[i]` go OOB"). It does **NOT** model a raised exception type and is
   **NOT** catchable by `try/except`.
   - IndexDefect: runtime.nim:4632-4643 (seq), 4738-4747 (array)
   - FieldDefect: runtime.nim:5065-5074
   - AssertionDefect: runtime.nim:5389-5398

2. **Exception-flow** — `raise` statements and `parseInt`'s ValueError route
   through `routeRaise` (runtime.nim:5541-5657) → propagate through the handler
   stack → produce **`sxRaised`**, gated by `defectExclusions` (the membership
   test at runtime.nim:5629; `typeIdToDefectKind` at runtime.nim:4110-4124). This
   IS catchable by `try/except`.

**The latent inconsistency:** because the target defects don't route through
`routeRaise`, a SUT like `try: arr[i] except IndexDefect: …` is **not modeled
correctly today** — the OOB is a target `sxSat`, never a catchable raise.

**What is unmodeled for arithmetic/conversion:**
- Integer `+`/`-`/`*` overflow → silent BV modular wraparound (`binBV`
  runtime.nim:1963; `arithInt` 2189; dispatch `lowerArith` 2333-2349). No check.
- Division/modulo by zero → no zero-check (`divBV`/`modBV` runtime.nim:1995-2017).
- Float→int out-of-range → **CR-3 interim**: domain *narrowed* to the target's
  representable range + `feConvDomainExcluded` sevHint (runtime_floats.nim:159-245;
  drained as a pc-narrowing, not a fork, runtime.nim:4181-4211). The comment at
  runtime_floats.nim:172 explicitly says raise-modeling is Phase-16.
- Int-width narrowing (`int8(300)`, subrange assignment) → **not even in the IR**
  (parser models fixed-width ops, not explicit width conversions; fact-sheet §6).
- `integerSemantics` (`isExact`/`isOptimised`(default)/`isLoose`, types.nim:1483)
  controls Z3 **encoding** (BV vs Z3Int), **NOT** whether overflow is checked.
- `DefectKind` (types.nim:793-806) has `dkRangeDefect` but **no `dkOverflowDefect`
  or `dkDivByZeroDefect`**. `dkRangeDefect` is declared but never emitted.

## Decision (TBD — capturing leans; confirm when scheduling)

Model arithmetic/conversion defects as **first-class catchable raises**, unifying
the two mechanisms. Proposed shape:

- A defect (Range/Overflow/DivByZero) **forks** the offending operation into a
  normal path (constraint: no defect) and a defect path (constraint: the defect
  condition). The defect path routes through **`routeRaise("RangeDefect", …)`** so
  it propagates through handlers and is catchable — AND surfaces as a finding when
  it reaches a `stkRaisedExn`/defect target. This *unifies* with exception-flow and
  fixes the latent `try/except IndexDefect` gap (retrofit the existing target
  defects in a later cycle).

## Open forks (resolve at scheduling; leads given)

- **F1 — mechanism.** Target-only `sxSat` (mirror IndexDefect, simplest) vs
  exception-flow `routeRaise` (catchable, faithful) vs **unified** (both).
  _Lean: **unified**_ — it's the correct architecture, fixes the existing
  inconsistency, and the new code is greenfield so we don't pay a migration cost
  for RangeDefect itself; retrofitting Index/Field/Assertion is a separable cycle (RD6).
- **F2 — overflow-checks policy.** `integerSemantics` is encoding-only, so we need
  a new dimension mapping to Nim's `--overflowChecks`/`--rangeChecks`. _Lean: a
  `set[ArithCheck]` setting (like `defectExclusions`), members
  `{acOverflow, acDivByZero, acRange}`, **default all-on** (debug-like → finds
  bugs); empty set = release-like wrap/unchecked._ Put it in the cache key.
- **F3 — enum additions.** Add `dkOverflowDefect`, `dkDivByZeroDefect`. _Lean:
  add both_ (Nim distinguishes OverflowDefect ≠ RangeDefect ≠ DivByZeroDefect).
  **⚠ ordinal-stability gotcha:** `defectExclusions` is a `set[DefectKind]`
  rendered into the cache key as an ordinal bitmask (canonicalize.nim:728; the
  CR-16 lesson). **Append new enum values at the END** so existing ordinals don't
  shift (else every cached `;de=` digest silently changes meaning). Bump
  `symexWalkerVersion` regardless (verdicts change).
- **F4 — slice scope/order.** _Lean:_ the unification (old RD6, now **D1**) lands
  **first** — before any new defect type — so the foundation is uniform and the
  version bump happens once; pairing with RD2 avoids a user-visible window where
  `try/except RangeDefect` works but `try/except IndexDefect` doesn't. Then RD2
  float→int (replaces CR-3) → RD3 div/mod-by-zero → RD4 overflow → RD5 int-width
  (deferred; needs new parser IR).
- **F5 — nim-z3 dependency. RESOLVED (present).** `addNoOverflow`/`subNoUnderflow`/
  `mulNoOverflow`/`negNoOverflow`/`sdivNoOverflow` are exported from
  `_deps/z3/src/z3/bitvec.nim:617-663` (always-on `z3/bitvec` import; test
  `_deps/z3/tests/tbitvec_overflow.nim`). RD4 is **Track-A, not library-gated** — its
  only gate is the BV/Int mixing rule (F6/§Global-concern 6).

## Proposed cycles (stub DoDs)

Cluster **D** (foundation) lands before Cluster **R16** (new defects). The old "RD6"
is promoted to **D1** and moved to the front (see F4).

| cycle | goal | key sites | DoD (stub) | tests perturbed |
|-------|------|-----------|------------|-----------------|
| D0-ADR | accept this ADR; resolve F1–F4 (F5 resolved) + F6 svInt rule | — | forks decided; ordinal-append + version-bump plan confirmed | — |
| **D1** | **unify existing target defects** (F1) — front-loaded | IndexDefect/FieldDefect/AssertionDefect sites (runtime.nim:4632/5065/5389) | route through `routeRaise` (catchable) while preserving target findings; `try: arr[i] except IndexDefect` modeled; lands before new defect types | `phase11_fielddefect`, IndexDefect/Assertion target tests |
| R16-1 | enum + policy foundation (was RD1) | types.nim:793-806 (**append** dk*), :4110 `typeIdToDefectKind`, new `ArithCheck` setting + `ResourceBudget`/merge/validate/cache key | enum appended (ordinals stable); setting threads full settings surface; `validateSymexSettings` **warns when arithChecks ∩ unexcluded DefectKinds = ∅**; no behavior change; suite green | CR2_cachekey (version) |
| R16-2 | float→int **RangeDefect** (replace CR-3); **pairs with D1** | runtime_floats.nim:159-245; drain 4181-4211 | domain-narrowing becomes a **fork**: in-range proceeds, out-of-range → routeRaise("RangeDefect"); `int(hugeFloat)` *finds* the defect; `try/except RangeDefect` catches; `feConvDomainExcluded` retired; **path-multiplicative — run bounded**; F5-hang canary clean | `CR3_CR4_CR6_float`, `F5hang_derefwrite`, `rereview_drains` (retire the hint asserts) |
| R16-3 | div/mod-by-zero **DivByZeroDefect** | `divBV`/`modBV` runtime.nim:1995-2017 | divisor==0 forks → routeRaise; symbolic `b` finds the zero case; respects `acDivByZero`; path-multiplicative — bounded; both backends | new |
| R16-4 | integer **OverflowDefect** (F5 resolved — predicates present) | `binBV` 1963; `lowerArith` 2333-2349 | with `acOverflow` on, `+`/`-`/`*` fork via `addNoOverflow`/`mulNoOverflow`/`subNoUnderflow` → routeRaise; off = current wrap; **must SKIP `svInt` operands** (unbounded Z3Int — overflow meaningless; never emit a BV predicate on an Int term → avoids the BV/Int hang); both backends | new |
| R16-5 | int-width narrowing / subrange (deferred) | **new `iekConvIntWidth` parser IR node** — `dsl_parser.nim` currently unwraps `nnkConv`/`nnkHiddenStdConv` silently (the primary scope driver, not the walker fork) | `int8(x)` / `range[0..10]` assignment range-checks → RangeDefect; deferred within R16 | new |

## Consequences
- **Soundness/completeness win:** overflow, div-by-zero, and range-conversion bugs
  become *findings* and the defects become *catchable* — closing real coverage gaps.
- **Default behavior changes:** with checks-on default, SUTs that previously
  symexed to `sxSat`/`sxUnsat` may now surface an arithmetic-defect `sxRaised`
  finding. This is desirable (it's a real bug) but is a verdict change → version bump
  + cache invalidation; communicate in the changelog.
- **Respects `defectExclusions`:** a user can suppress any family via the existing
  set (and the new `ArithCheck` policy gates whether the fork is even emitted).

## Open questions (for RD0-ADR)
- Should `acRange` and `defectExclusions{dkRangeDefect}` be *both* honored, and in
  which order (policy gates emission; exclusions gate surfacing)? — propose:
  policy first (no fork if unchecked), then exclusions (fork but suppress finding).
- Does `integerSemantics == isOptimised` (Z3Int promotion) interfere with BV
  no-overflow predicates in RD4? (Promoted vars are unbounded Z3Int — overflow is
  meaningless there.) Likely: overflow checks only apply to genuinely BV-encoded
  fixed-width vars; promoted-to-Z3Int vars are provably in-range so no fork. Verify.
- Retire vs keep `feConvDomainExcluded`: once RD2 forks, the hint is obsolete for
  the modeled case — keep only if some pointee/width stays unmodeled.
