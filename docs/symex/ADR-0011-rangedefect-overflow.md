# ADR-0011 — Defect-flow architecture (unified raise model) + arithmetic-defect modeling

> **STATUS: ACCEPTED — cycle D0-ADR, 2026-06-27.** Captured from the Phase-15
> review session, hardened across rounds 1–2 of the `/architect` review, and
> accepted at D0-ADR (forks F1–F4 + F6 resolved; F5 was already resolved). Governs
> **Cluster D** (defect-flow unification — the cross-cutting decision) and
> **Cluster R16** (arithmetic defects) of
> [RFC-phase16](RFC-phase16-language-fragments.md). Citations are point-in-time
> (post-Phase-15, walker `v18` after A5); re-verify at each `/tdd` cycle.
>
> **One product decision worth a veto-window (F2):** arithmetic checks default
> **all-on** — every `+`/`-`/`*`, `div`/`mod`, and `int(float)` forks a defect
> check by default, so SUTs that previously verdicted `sxSat`/`sxUnsat` may now
> surface an arithmetic-defect `sxRaised`. This matches the tool's purpose (find
> bugs) and Nim's own debug-build defaults, but it is a real default-behavior
> change. Empty `arithChecks` = release-like (wrap/unchecked) opt-out.

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

## Decision (ACCEPTED at D0-ADR — forks below resolved)

Model arithmetic/conversion defects as **first-class catchable raises**, unifying
the two mechanisms. Proposed shape:

- A defect (Range/Overflow/DivByZero) **forks** the offending operation into a
  normal path (constraint: no defect) and a defect path (constraint: the defect
  condition). The defect path routes through **`routeRaise("RangeDefect", …)`** so
  it propagates through handlers and is catchable — AND surfaces as a finding when
  it reaches a `stkRaisedExn`/defect target. This *unifies* with exception-flow and
  fixes the latent `try/except IndexDefect` gap (retrofit the existing target
  defects in a later cycle).

## Forks — RESOLVED at D0-ADR

- **F1 — mechanism. DECIDED: unified** (target `sxSat` *and* exception-flow
  `routeRaise`). It's the correct architecture, fixes the existing inconsistency,
  and the new code is greenfield so we don't pay a migration cost for RangeDefect
  itself; retrofitting Index/Field/Assertion is the (front-loaded) D1a cycle.
  Rejected: target-only (leaves `try/except` unmodeled) and routeRaise-only (loses
  the direct target finding).
- **F2 — overflow-checks policy. DECIDED: a `set[ArithCheck]` setting**
  (like `defectExclusions`), members `{acOverflow, acDivByZero, acRange}`,
  **default all-on** (debug-like → finds bugs; matches Nim's debug defaults);
  empty set = release-like wrap/unchecked. In the cache key. `integerSemantics`
  stays encoding-only (orthogonal axis). *This is the one default-behavior change —
  see the STATUS veto-window note.*
- **F3 — enum additions. DECIDED: add both** `dkOverflowDefect`,
  `dkDivByZeroDefect` (Nim distinguishes OverflowDefect ≠ RangeDefect ≠
  DivByZeroDefect). **⚠ ordinal-stability gotcha (binding):** `defectExclusions`
  is a `set[DefectKind]` rendered into the cache key as an ordinal bitmask
  (canonicalize.nim:728; the CR-16 lesson). **Append the new enum values at the
  END** so existing ordinals don't shift (else every cached `;de=` digest silently
  changes meaning). Bump `symexWalkerVersion` when verdicts change (R16-1 onward).
- **F4 — slice scope/order. DECIDED:** the unification (now **D1a/D1b**) lands
  **first** — before any new defect type — so the foundation is uniform and the
  version bump happens once; pairing with R16-2 avoids a user-visible window where
  `try/except RangeDefect` works but `try/except IndexDefect` doesn't. Then R16-2
  float→int (replaces CR-3) → R16-3 div/mod-by-zero → R16-4 overflow → R16-5
  int-width (deferred; needs new parser IR).
- **F5 — nim-z3 dependency. RESOLVED (present).** `addNoOverflow`/`subNoUnderflow`/
  `mulNoOverflow`/`negNoOverflow`/`sdivNoOverflow` are exported from
  `_deps/z3/src/z3/bitvec.nim:617-663` (always-on `z3/bitvec` import; test
  `_deps/z3/tests/tbitvec_overflow.nim`). RD4 is **Track-A, not library-gated** — its
  only gate is the BV/Int mixing rule (F6 below).
- **F6 — svInt short-circuit (`isOptimised` × overflow fork).** Under
  `integerSemantics == isOptimised`, range-typed vars promote to unbounded `Z3Int`
  (`svInt`), where overflow is mathematically impossible; emitting a BV no-overflow
  predicate on an `svInt` operand is a type mismatch and risks the BV/Int hang.
  Options: (A) assert the operand is `svBV*` before forking; (B) skip the overflow
  fork whenever any operand is `svInt`. **DECIDED: (B) skip** — promoted vars are
  provably in-range, so the fork is trivially UNSAT and only adds path pressure;
  skipping also guarantees we never emit a BV no-overflow predicate on a Z3Int
  term (the BV/Int mixed-theory hang). Supersedes the old Open-question item.

## Proposed cycles (stub DoDs)

Cluster **D** (foundation) lands before Cluster **R16** (new defects). The old "RD6"
is promoted to **D1** and moved to the front (see F4). **D1 is split into D1a (engine
+ verdict change) and D1b (`assertCoveredBy` replay companion)** — the round-2
feasibility review found D1 is not a single clean slice: it changes the public verdict
of four target kinds, removes a fork-gate, touches five code sites, and requires a
macro code change. R16-1 remains a hard prerequisite for R16-2 (R16-2 forks gate on
`acRange`, which R16-1 introduces).

| cycle | goal | key sites | DoD (stub) | tests perturbed |
|-------|------|-----------|------------|-----------------|
| D0-ADR | accept this ADR; resolve F1–F4 + F6 (F5 resolved) | — | forks decided; ordinal-append + version-bump plan confirmed; **update this ADR STATUS → ACCEPTED (cycle D0-ADR + date)** | — |
| **D1a** | **unify existing target defects** (F1) — front-loaded; engine + verdict change | IndexDefect/FieldDefect/AssertionDefect sites (runtime.nim:4632/4738/5065/5354) **+ NilAccessDefect site (runtime_heap.nim:327-340)** | **(1)** Remove the `if w.target.kind == stkXxx:` fork-gate at all four sites — the fork is now **unconditional** (gating on the *target* rather than the *defect* is exactly what leaves `try/except IndexDefect` unmodeled). **(2)** Route the defect sub-path through `routeRaise("IndexDefect"/…, …)` instead of `trySolve→sxSat`. **(3)** Delete the four `of sxRaised: discard ## E2a` arms (they live inside the deleted trySolve blocks; the invariant still holds at routeRaise:5656). **API BREAK (E6 wins — desirable, not a regression):** `symexFind(fn, tFieldDefect()/tIndexError()/tAssertionViolation()/tNilAccess())` now returns `sxRaised{isDefect:true}` — witness moves `r.witness`→`r.raisedWitness`, `r.raisedTypeId` set. "Preserving findings" = *not dropped*, NOT *same status*. Behavior change: a defect fully caught by a handler now yields `sxUnsat` for that target (pre-D1 it spuriously returned `sxSat`). Introduce a `forkDefect(p, defectCond, typeId, msg, w)` helper to unify the four (five with R16) sites. | `phase11_fielddefect`, `phase11_walker`, `phase4_oob`, `phase1_assert` (status `sxSat`→`sxRaised`, witness→raisedWitness); `phase12_witnesses` (sfRaised must carry a **distinct** `targetDesc`, e.g. `"raised(IndexDefect)"`, so the `sfSat` filter loop at 127/139/151 doesn't double-match) |
| **D1b** | **`assertCoveredBy` raisedWitness replay** (companion — code change, NOT just tests) | symex.nim:1179-1188 (`of sxRaised:` arm) | The arm hardcodes `covered:false` and skips replay; its "E2b not shipped yet" comment is **stale** (`raisedWitness` IS populated — toPublic:4134). Post-D1a this silently drops coverage-checking for the defect targets. Fix: for `stkAssertionViolation`/`stkIndexError`/`stkFieldDefect`/`stkNilAccess` with `r.status==sxRaised`, splat `r.raisedWitness` through `testFn`, run the same try/except coverage check as the `of sxSat:` arm, raise on `not covered`. | `phase7_assertcovered` (lines 66-103), `phase11_fielddefect` (line 83) |
| R16-1 | enum + policy foundation (was RD1) | types.nim:793-806 (**append** dk*), :4110 `typeIdToDefectKind`, new `ArithCheck` setting + `ResourceBudget`/merge/validate/cache key | enum appended (ordinals stable); setting threads full settings surface; `validateSymexSettings` **warns bidirectionally**: (a) when `arithChecks ∩ unexcluded DefectKinds = ∅` (no checks visible), AND (b) when a check is *enabled* in `arithChecks` but its `DefectKind` is in `defectExclusions` (fork cost paid, finding suppressed — pure waste). `acRange` scope = **float→int domain checks (RD2) only**; int-width narrowing (RD5) will also gate on `acRange` when it lands. No behavior change; suite green | CR2_cachekey (version) |
| R16-2 | float→int **RangeDefect** (replace CR-3); **pairs with D1a** | runtime_floats.nim:159-245; normal-path drain 4181-4211 (UNCHANGED) + **new** walk-arm raise-drain | **Dual-drain, NOT a substitution.** (a) The in-range bounding via `drainConvFloatToIntBounds`→`p.pc` STAYS — it keeps the `toSbv` BV truncation sound on the normal path. (b) ADD a new `drainConvFloatToIntRaises(p, w): seq[Path]` (parallel to `drainParseIntRaises`; returns `seq[Path]`, so it can NOT live inside the single-Path `drainPendingLowerEffects` — call it at the walk-arm level wherever `drainParseIntRaises` is called) that forks `not(domainCond)`→`routeRaise("RangeDefect")`. `int(hugeFloat)` *finds* the defect; `try/except RangeDefect` catches. **Hint teardown** (5 sites, 3 files): remove `domHint32`/`domHint64` emission + `syncConvFloatToIntDomainHint` + the `convFloatToIntDomainHints` threadvar/WalkCtx field/reset/drain. `feConvDomainExcluded` is a closed-enum member (types.nim:711) → **freeze-annotate `## retired R16-2 — do not reuse ordinal`, do NOT delete** (CR-16 ordinal-stability). Path cost is **O(N) in the common case** (raise paths are terminal — routeRaise returns `@[]`); 2^N only under pathological nested try/except — bounded runner still mandatory (F5 discipline); F5-hang canary clean | `CR3_CR4_CR6_float`, `F5hang_derefwrite`, `rereview_drains`, **`cr9_lowerInExpr`** (retire the hint asserts — **6 asserts across all 4 files**) |
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
- **D1a is a public API break (one-time reconciliation).** The four defect targets
  (`tIndexError`/`tFieldDefect`/`tAssertionViolation`/`tNilAccess`) flip from `sxSat`
  (witness in `r.witness`) to `sxRaised{isDefect:true}` (witness in `r.raisedWitness`,
  `r.raisedTypeId` set). Name this in the changelog. The `set[ArithCheck]` and
  `set[DefectKind]` are the correct **two-axis** model: `arithChecks` gates *fork
  emission* (the only lever against 2^N path cost); `defectExclusions` gates *finding
  surfacing* after the fork. They are not collapsible.
- **`stkAssertionViolation`'s second role survives D1a.** Beyond triggering the
  `AssertionDefect` fork (which E6 now subsumes), `stkAssertionViolation` also makes
  ANY reachable `CatchableError` raise surface as a finding (routeRaise:5637). Do NOT
  remove that branch when retiring the AssertionDefect-specific fork site.

## Open questions — RESOLVED at D0-ADR
- **Two-axis ordering — RESOLVED:** both `acRange` (policy) and
  `defectExclusions{dkRangeDefect}` (surfacing) are honored, **policy first**: no
  fork if the check is unchecked in `arithChecks`; if checked, the fork emits but
  the finding is suppressed when the kind is in `defectExclusions`. `arithChecks`
  is the only lever against 2^N path cost; `defectExclusions` only filters output.
  `validateSymexSettings` warns on the wasteful combination (checked + excluded).
- **`isOptimised`/Z3Int interference — RESOLVED by F6(B):** overflow checks apply
  only to genuinely BV-encoded fixed-width vars; a promoted-to-Z3Int (`svInt`)
  operand skips the fork entirely (provably in-range; never emit a BV predicate on
  an Int term).
- **Retire vs keep `feConvDomainExcluded` — RESOLVED (R16-2):** retire emission;
  **freeze the enum ordinal** (do not delete — CR-16 ordinal-stability). All six
  asserts across the four perturbed test files are updated to expect the
  RangeDefect fork outcome rather than the hint.
