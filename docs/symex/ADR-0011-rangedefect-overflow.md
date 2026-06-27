# ADR-0011 — RangeDefect / arithmetic-defect raise modeling

> **STATUS: DRAFT STUB — PROPOSED, not accepted.** Captured 2026-06-27 from the
> Phase-15 review session. This is the detailed stub for slice **A1** of
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
- **F4 — slice scope/order.** _Lean:_ RD2 float→int range (replaces CR-3, cheapest
  + highest-value) → RD3 div/mod-by-zero → RD4 integer overflow → RD5 int-width
  narrowing (deferred; needs new parser IR) → RD6 unify existing target defects.
- **F5 — nim-z3 dependency (verify early).** Integer overflow detection (RD4)
  wants Z3 `bvadd_no_overflow`/`bvmul_no_overflow`/`bvsub_no_underflow` predicates
  — **confirm these are exposed in the pinned nim-z3 v2.0.0 FFI** before committing
  RD4; if absent, RD4 becomes Track-B-style (library work first) while RD2/RD3
  (which only need ordinary comparisons / `== 0`) proceed.

## Proposed cycles (stub DoDs)

| cycle | goal | key sites | DoD (stub) |
|-------|------|-----------|------------|
| RD0-ADR | accept this ADR; resolve F1–F5 | — | forks decided; ordinal-append + version-bump plan confirmed |
| RD1 | enum + policy foundation | types.nim:793-806 (append dk*), :4110 `typeIdToDefectKind`, new `ArithCheck` setting + cache key (canonicalize.nim) | enum appended (ordinals stable); setting merges/validates/canonicalizes; no behavior change; suite green |
| RD2 | float→int **RangeDefect** (replace CR-3) | runtime_floats.nim:159-245; drain 4181-4211 | the domain-narrowing becomes a **fork**: in-range proceeds, out-of-range → routeRaise("RangeDefect"); `int(hugeFloat)` now *finds* the defect; `try/except RangeDefect` catches; CR-3 `feConvDomainExcluded` retired or downgraded; both backends; F5-hang canary clean |
| RD3 | div/mod-by-zero **DivByZeroDefect** | `divBV`/`modBV` runtime.nim:1995-2017 | divisor==0 forks → routeRaise; `a div b` with symbolic `b` finds the zero case; respects `acDivByZero` policy; both backends |
| RD4 | integer **OverflowDefect** (gated F2/F5) | `binBV` 1963; `lowerArith` 2333-2349 | with `acOverflow` on, `+`/`-`/`*` fork the overflow path via Z3 no-overflow predicates → routeRaise; off = current wrap; **no Z3 hang** (watch mixed BV/Int — keep ground); both backends |
| RD5 | int-width narrowing / subrange (deferred) | parser IR (none today, fact-sheet §6) | needs new conv IR node; `int8(x)` / `range[0..10]` assignment range-checks → RangeDefect; scope TBD |
| RD6 | unify existing target defects (F1) | IndexDefect/FieldDefect/AssertionDefect sites above | they route through `routeRaise` (catchable) while preserving target findings; `try: arr[i] except IndexDefect` modeled; possibly its own ADR |

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
