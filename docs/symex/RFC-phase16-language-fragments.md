# RFC — Phase 16 (language fragments, part 2 + frontier)

> **STATUS: DRAFT STUB — round-1 reviewed (2026-06-27), not scheduled, not
> reconciled.** Captured from the Phase-15 code-review session synthesis, then
> hardened by a 4-lens `/architect` review (depth, breadth, design, feasibility).
> Each slice is a *stub* to be fleshed out (and reconciled against code, per the
> [reconciliation pattern](RFC-phase15-reconciliation.md)) before `/tdd`. Line
> citations are point-in-time (post-Phase-15, walker `v17`); re-verify at schedule time.

## Context

Phase 15 shipped the 9 language-fragment clusters (Z, L, F, S, H, E, G, C, R) and a
full code-review remediation (CR-1…CR-22; CR-7 god-module split; CR-9 `WalkCtx`
migration + `ResourceBudget` + integer-rep boundary helpers). The engine is
architecturally clean. Almost everything below is honestly classified `sxUnknown`
today (Invariant 3) — so Phase 16 is mostly *coverage expansion*, not bug-fixing —
**with two exceptions found in review** that are real defects: the defect-mechanism
inconsistency (catchable `RangeDefect` but un-catchable `IndexDefect`, see Cluster D)
and named-`break`-label being silently dropped (see §Unattended). The
`*Unsupported`/`*NotImplemented`/`*Skipped` classification kinds in `types.nim`
enumerate most of the frontier.

## Tracking (how this RFC stays honest over time)

- Cycle-level tracking lives in **`SYMEX_PLAN_16.md`** (new section or file, per the
  `SYMEX_PLAN.md` pattern); when a slice is promoted stub→scheduled it gets a
  cluster ID + a cycle table here, copied into the plan tracker.
- **Slice IDs below are stable references** (D, R16, A2, A3, A5, A6, A0, B1…B6).
- A **`RFC-phase16-reconciliation.md`** is authored before the first `/tdd` cycle.
- The `status` column in the inventory is the source of truth; "shipped" rows are
  not deleted, they flip status (rot-resistant).

## Global concerns (cross-cutting — apply to every slice)

Carried-over Phase-15 invariants **3** (`sxUnknown` ⇔ a classified `sevError`), **6**
(version constants single-sourced in `canonicalize.nim`), **7** (sevHint never flips
a verdict) all still hold — **except** Invariant 3's meaning shifts for retrofitted
defects under Cluster D (a defect becomes a catchable `sxRaised`, not only a target
`sxSat`).

1. **Walker-version discipline.** Every slice that changes a verdict/witness bumps
   `symexWalkerVersion` (currently `"17"`) by one (and `renderAsChoicesVersion` if
   witness rendering changes). A1/R16, A2, A3, A5, A6 all change verdicts.
2. **Enum ordinal stability (CR-16 lesson).** New `DefectKind`/`SymexErrorKind`
   values **must be appended at the END** of their enum — `defectExclusions` is a
   `set[DefectKind]` rendered into the cache key as an ordinal bitmask
   (`canonicalize.nim`), so mid-enum insertion silently corrupts every cached digest.
3. **Settings surface (CR-2/CR-9b pattern).** Each new setting (R16's `ArithCheck`,
   A3's iterator-unroll budget, …) must thread through `ResourceBudget` →
   `SymexSettings.+` merge → `validateSymexSettings` → `canonicalize(SymexSettings)`,
   matching the audited inclusion/exclusion comment block.
4. **Path-explosion + hang discipline.** Defect *forks* (R16) multiply paths
   (2^N for N arithmetic ops) and may pressure `maxFrontierSize` (ADR-0004); keep
   encodings ground; **always** run via `scripts/dt-bounded.sh`/`parity-check.sh`
   (137 = hang = engine defect, the F5 lesson). Flag per-slice hang risk below.
5. **Determinism.** New witness forms (R16 `sxRaised`, A2 ref-variant heap) must be
   deterministic and checked against `renderAsChoicesVersion` (see `determinism.md`,
   ADR-0007 D4 `cacheKeyRaised`).
6. **Abstraction × overflow.** `integerSemantics == isOptimised` promotes range-typed
   vars to unbounded `Z3Int` where overflow is meaningless — overflow forks (R16/RD4)
   **must skip `svInt` operands** (see ADR-0011 + ADR-0001).

## Slice inventory

Value/effort are rough; "Blocker" = nim-z3/Z3 capability gap (else engine-side).

| ID | Slice | Value | Deps | Blocker | Status | ADR |
|----|-------|-------|------|---------|--------|-----|
| A0 | CR-9 trailing threadvars → WalkCtx (3 sinks) | low | — | — | stub | — |
| D  | **Defect-flow unification** (catchable defects) | high | — | — | stub | 0011 |
| R16| Arithmetic defects (Range/Overflow/DivByZero) | high | D | — | stub | 0011 |
| A5 | float `classify()` + remaining math ops | med | — | — | stub | 0005 |
| A2 | ref-of-variant / complex pointee deref | med | design-ADR | — | stub | new |
| A3 | closure iterators (`{.closure.}`) | med | — | — | stub | 0009 |
| A6 | symbolic-length `filter`/`map` (was B4) | med | — | — (engine) | stub | 0009 |
| INV| wire never-emitted `se*`/add `geVtableDispatch` (Invariant-3 consistency) | med | — | — | stub | — |
| A7 | Unicode rune witnesses (UTF-8 encode/decode layer) | high | — | **engine-side** (Z3 is full-Unicode) | stub | 0006 |
| A8 | radix conversions (fixed-width BV bit-slice) | med | — | **engine-side** | stub | — |
| A9 | ASCII/Latin-1 case-fold + `reverse` + bounded `sort` | low-med | — | **engine-side** | stub | — |
| B1 | regex `find` over patterns | med | Z3 lacks `seq.indexof_re` | engine-side (cumbersome) **or** wrap upstream | queued | 0006 |
| — | full-Unicode case-fold; symbolic-length `sort` | — | — | **genuine-cannot** (see Indefinite) | — | — |

---

## D — Defect-flow unification  ⟶ **prerequisite; [ADR-0011](ADR-0011-rangedefect-overflow.md)**

The engine has **two unrelated "bad thing" mechanisms** (fact-sheet in ADR-0011):
*target-based* defects (`IndexDefect`/`FieldDefect`/`AssertionDefect` fork→solve→emit
**`sxSat`**, **not catchable**) vs *exception-flow* (`routeRaise`→**`sxRaised`**, gated
by `defectExclusions`, catchable). **Latent bug:** `try: arr[i] except IndexDefect`
is *not* modeled today. This is cross-cutting (it changes already-shipped constructs),
so it is elevated above R16 and lands first:
- **D0-ADR:** accept ADR-0011 at architectural scope; resolve forks F1 (mechanism —
  _lean: unify_), F2 (overflow-checks policy), F3 (enum additions + append rule),
  F6 (svInt short-circuit). Lock the version-bump plan.
- **D1 (was ADR-0011 RD6):** retrofit IndexDefect/FieldDefect/AssertionDefect through
  `routeRaise` so they are catchable while preserving target findings. Highest
  breaking-change risk → lands before new defect types. **Perturbs:**
  `tsymex_phase11_fielddefect.nim` + IndexDefect/Assertion target tests.

## R16 — Arithmetic defects (on the unified D foundation)  ⟶ **[ADR-0011](ADR-0011-rangedefect-overflow.md)**

Adds **RangeDefect** (float→int out-of-range — *replaces* the CR-3 domain-narrowing
interim, runtime_floats.nim), **OverflowDefect** (int `+`/`-`/`*` — uses nim-z3's
`addNoOverflow`/`mulNoOverflow`/`subNoUnderflow`, **confirmed present**,
`_deps/z3/src/z3/bitvec.nim:617-663`), and **DivByZeroDefect** (`div`/`mod` by zero).
Adds enum values `dkOverflowDefect`, `dkDivByZeroDefect` (append-only). Cycles
RD0–RD4 in ADR-0011; **RD2 (float→int) pairs with D1**; **RD5 (int-width narrowing
`int8(x)`/subrange) is deferred within R16** — it needs a new `iekConvIntWidth`
parser IR node (`dsl_parser.nim` currently unwraps `nnkConv`/`nnkHiddenStdConv`
silently). **Hang risk:** path-multiplicative forks (RD2/RD3) + BV/Int mixing (RD4 —
skip `svInt`). **Perturbs:** `CR3_CR4_CR6_float`, `F5hang_derefwrite`,
`rereview_drains` (all assert the `feConvDomainExcluded` hint RD2 retires).

## A5 — float `classify()` + remaining `std/math`  *(candidate opener — lowest risk)*
- **Missing:** `classify(f)`→`FloatClass`, `copySign`, `nextafter` → `feUnsupportedOp`
  (runtime_floats.nim `lowerMathCall`; ADR-0005).
- **Approach:** pure `lowerMathCall` extension mapping `"classify"` to a `case` over
  `FloatClass` using already-shipped FP predicates (`isNaN`/`isInf`/`isZero`/
  `isNormal`/`isSubnormal`/…). **No new IR, no settings, no cache-key change, no
  existing-test breakage** — the cleanest "Phase 16 is open" commit.

## A2 — ref-of-variant / complex pointee deref  *(needs a design ADR first)*
- **Missing:** `ref T where T is variant` → `heRefVariantUnsupported`
  (runtime.nim:~6332); ref-of-complex (`ref seq[T]`) still `sxUnknown` via
  `liftHeapValue`. CR-19 aligned only *primitive* pointee sorts.
- **Hard part (feasibility):** a variant has **no single Z3 sort** (`allocateSym(itVariant)`
  yields a discriminator + per-arm field arrays, not one sort). `heapValueSort`
  reads the Z3 sort of an `allocateSym` result — undefined for variants. Needs a
  design ADR choosing field-split-per-arm heaps vs a Z3 datatype encoding. **Harder
  than A5** → schedule after A5.

## A3 — closure iterators (`iterator foo(): T {.closure.}`)
- **Missing:** **no IR node** — the parser has no `iekIterator`; iterator calls
  likely route as unknown `isCall` shapes → `sxUnknown`. (The `ceNotImplemented` at
  runtime.nim:~6294-6301 is for `iekLambda`/`iekClosureCall`, *not* iterators;
  verify the exact parse-time fallback first.)
- **Approach:** model the resumable closure-iterator protocol (env + resume point)
  over ADR-0009's closure encoding; likely bounded unrolling like `for`/`while`.

## A6 — symbolic-length `filter`/`map`  *(engine-side; was mis-filed as Track B)*
- **Correction (depth lens):** **not nim-z3-blocked.** nim-z3 v2.0.0 already exposes
  `seqMap`/`seqFoldl`/`seqMapi`/`seqFoldli` (`_deps/z3/src/z3/funcdecl.nim:584-661`);
  Z3 simply never had a native `seq.filter`. `filter` is encodable engine-side as a
  `seqFoldl` over the predicate. Today: concrete-length inline works (select-mask
  fold, runtime.nim:~6111-6128); `map` has a *partial* axiom path (capture-free
  `int→int` via `Z3_mk_map`); **`filter` is the only fully-deferred HOF**, and `map`
  over non-`int→int` symbolic shapes is also open.
- **Approach:** `seqFoldl`-based `filter`; generalize the `map` axiom path. **Hang
  risk:** Z3's solver is incomplete for symbolic-length seq HOFs — a concrete-length-
  branched encoding may be needed (F5-hang discipline mandatory).

## INV — Invariant-3 consistency cleanup
- **Missing (breadth lens):** `seNestedSeqUnsupported`, `seUnsupportedTableValType`,
  `seUnsupportedSetCharInterop`, `seByteIndexUnsupported`, `seByteIterUnsupported`
  are **defined in `types.nim` but never emitted** — the corresponding constructs
  fall to an unstructured `isUnsupported` reason-string instead of the structured
  kind (still `sxUnknown`, so Invariant 3 is *nominally* held, but tooling matching
  `errors[0].kind` can't). And `geVtableDispatch` (Phase-15 deferred subtype/vtable
  dispatch) **is not in the enum at all**.
- **Approach:** wire each defined-but-unemitted kind to its emission site (or
  document `reserved/unused` like `ceUnsupportedCapture`); add `geVtableDispatch`.

## A0 — CR-9 trailing threadvars (infra carryover)
- Phase-15 CR-9 Stage 5 deferred 3 sinks (`parseIntGateConstraints`,
  `currentClosureCallAxioms`/`…Strs`) — read mid-walk in `trySolve` (no `WalkCtx`
  param). No verdict impact; pure tidiness. Migrate or leave noted.

---

## Library/Z3-capability tail (post-investigation — 2026-06-27)

A per-item Z3/nim-z3 capability investigation (evidence in commit log) **collapsed
the former "Track B" almost entirely into engine-side work** — confirming the bar's
verdict that these belong in scope. The honest residue:

- **A7 — Unicode runes (was B2): ENGINE-SIDE.** Z3's string sort already ranges over
  Unicode codepoints 0..0x2FFFF (`z3_api.h` `Z3_mk_u32string`); the byte-faithful
  ≤0xFF model (ADR-0006, locked) was our deliberate soundness choice, not a Z3 limit.
  The work is a UTF-8 encode/decode + witness-rendering layer at the boundary
  (optionally wrap `Z3_mk_u32string` in nim-z3 for convenience).
- **A8 — radix (was B5): ENGINE-SIDE.** Z3 int↔str is decimal only, but fixed-width
  `toHex`/`toBin` = BV nibble-extract + a digit-table ITE (quantifier-free, sound).
  `Z3Int` (unbounded) radix is harder (`seqFoldl`, incomplete for symbolic length).
- **A9 — case-fold ASCII/Latin-1 + reverse + bounded sort: ENGINE-SIDE.** Finite char
  domain ⇒ case-fold is an ITE/`seqMap` mapping (sound for ASCII/Latin-1). `reverse`
  is an index permutation at any length. `sort` for **concrete/bounded** length is a
  fixed comparator network (quantifier-free).
- **B1 — regex `find` over patterns: the one genuine upstream gap.** Z3 lacks
  `Z3_mk_seq_indexof_re` (it has `seq.in_re` membership + `seq.index` for fixed
  needles). Encodable engine-side via membership + a bounded existential over split
  points (cumbersome); a nim-z3/Z3 `indexof_re` wrapper would shortcut it. `replaceRe`
  is already wrapped (`-d:z3WithSeqReplaceRe`); `replaceAll` is a Z3 ≥4.15.5 version
  upgrade (pinned 4.15.0), not a missing API.

## Unattended categories (no slice yet — explicit so nothing is silently lost)

Each is currently `sxUnknown`/unclassified unless noted; promote to a slice on demand.
- **Latent BUG — named `block`/`break <label>`:** `nnkBreakStmt` with a label is
  parsed to a label-less `mkBreak()` (`dsl_parser.nim:~1636`) → a cross-loop
  `break outer` is silently modeled as breaking the *innermost* loop. **Real
  soundness bug**, deserves a fix slice (labeled break/continue).
- `openArray`/`varargs` params — no `itOpenArray` IR; ubiquitous in stdlib; a sound
  model treats them as `seq` with a pinned length.
- `seq[T]` mutation (`add`/`del`/`setLen`) — seqs modeled immutable/fixed-length.
- `seq[seq[T]]` nested (`seNestedSeqUnsupported`); `set[T]` ops beyond `in`
  (union/intersect/diff); `s[i] in set[char]` (`seUnsupportedSetCharInterop`).
- `case s: string` (string-discriminated case — encodable as per-arm str-eq).
- String mutation `s[i]=c`/`s.add` — Phase-15 proposed a sound `bytes(s)` BV8
  functional-update encoding (don't discard it as "indefinite" — it's a tracked design).
- Symbolic `for c in s` over a *free* string (unbounded iteration); object `method`
  dispatch on non-ref objects; `defer` (reconcile — may already route via try/finally);
  signed `shr` arithmetic-vs-logical semantics (ADR-0001 nit); enum-with-holes
  discriminator ordinals (audit `discTags`); `{.raises.}` effect-tracking;
  `{.nimcall.}` vs `{.closure.}` surfaces; `var T` (mutable non-ref) capture
  snapshot-vs-observe; ADR-0001 abstraction deferrals (loop-invariant promotion,
  assert-range refinement, refinement through inlined calls — intersects R16/RD4).

## Indefinite / out of scope (not Phase 16)
`float80` / extended precision; signaling-vs-quiet NaN; NaN-payload witnesses for
`cast`-SUTs; `cstring` FFI.

**Genuine-cannot (Z3 cannot express soundly + terminating — documented bounds, with
doable subsets covered above):**
- **Full-Unicode case-fold** — context-dependent equivalences (Turkish ı/I, Greek
  σ/ς) need a locale oracle Z3 lacks. ASCII/Latin-1 fold is covered by A9.
- **Symbolic-length `sort`** — the permutation constraint (`∀v. count(v,in)=count(v,out)`)
  requires a universal quantifier → incomplete/​hang (G4 class). Concrete/bounded-length
  `sort` and `reverse` (any length) are covered by A9.

## Already handled (do NOT re-list as deferred)
`maxSplitParts` wiring (CR-11/CR-18, b7258f7) · RFC-completeness robustness (frontier
pruning, Z3-error policy, constraintDigest — shipped via Phases 11-14; audit residuals
only) · `s.high` + `for c in s` over **concrete** strings (byte-faithful, ADR-0006) ·
`$float`/`parseFloat` (S10b) · `string <` lexicographic.

---

## ADRs introduced by this RFC

| ADR | Title | Governs | Authoring cycle | Status |
|-----|-------|---------|-----------------|--------|
| 0011 | Defect-flow architecture + arithmetic-defect modeling | D, R16 | D0-ADR | DRAFT |
| (new) | ref-variant/complex pointee heap encoding | A2 | A2-ADR | not started |

## Sequencing, entry point & Phase-DoD

**Entry point for a new implementer:** the cheapest validation of cadence is **A5**
(pure `lowerMathCall` extension, zero plumbing, zero test breakage). Then the
foundation: **D0-ADR** (lock the defect forks) → **D1** (retrofit the three target
defects — catchable) → **R16/RD2** (float→int RangeDefect) → RD3 (div-by-zero) →
RD4 (overflow) → A2 (after its design-ADR) → A3 → A6.

Dependency edges: D0-ADR ≺ D1 ≺ R16 (R16 builds on unified defects); RD2 pairs with
D1; A2 ≺ nothing but needs its own ADR (harder than A5); A6/A2/A3/A5/A7/A8/A9
mutually independent. A7/A8/A9/B1 are ordinary engine-side slices (the former
"Track B," reclassified by the capability investigation); none is gated on an
external decision.

**Phase 16 complete when:** A0, D, R16, A5, A2, A3, A6, A7, A8, A9, INV each ship
with a regression smoke green on both backends; every `*Unsupported`/`*NotImplemented`
kind in `types.nim` is either emitted or documented reserved. The only items outside
this phase's coverage are B1 (schedulable as engine work, or via an upstream
`indexof_re` wrapper) and the two documented genuine-cannot bounds (full-Unicode
case-fold, symbolic-length `sort`).

## Open design gates

1. **Defect-mechanism (D, ADR-0011 F1)** — unify (catchable) vs target-only.
   _Lean: unify._ Recorded; locked at D0-ADR — not blocking now.
2. **Overflow-checks policy (R16, ADR-0011 F2)** — new `set[ArithCheck]` distinct
   from `integerSemantics`. _Lean: default all-on (finds bugs)._ Locked at D0-ADR.
3. **First slice** — A5 warm-up vs jumping straight to D. _Lean: A5 first to validate
   cadence, then D._ Not blocking.
4. **Track B — CLOSED, no fork remains.** The bar resolved the direction and the
   capability investigation resolved the facts: the former Track B was mostly
   mis-filed engine work (now A7/A8/A9), B1 is engine-side-or-upstream-wrapper, and
   the only genuine-cannot is full-Unicode case-fold + symbolic-length `sort` (both
   with doable subsets shipped in A9, documented bounds in §Indefinite). There is no
   "appetite" decision to make. The remaining input is pure ordering — recommendation
   stands: A5 opener → Cluster D → R16, with A7/A8/A9/B1 as ordinary Track-A slices.
