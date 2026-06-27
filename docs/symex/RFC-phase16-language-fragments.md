# RFC — Phase 16 (language fragments, part 2 + frontier)

> **STATUS: DRAFT STUB — rounds 1–2 reviewed (2026-06-27), not scheduled, not
> reconciled.** Captured from the Phase-15 code-review session synthesis, then
> hardened by two 4-lens `/architect` rounds (depth, breadth, design, feasibility).
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

- **Authority chain:** ADR-0011 is the *design* authority for the D/R16 cycle DoDs;
  this RFC is the *scheduling* authority (the inventory `status` column); a future
  **`SYMEX_PLAN_16.md`** is the *execution* tracker (cycle SHAs). DoD rows are copied
  from the ADR verbatim; the ADR is not edited after a slice is promoted.
- `SYMEX_PLAN_16.md` **does not exist yet** — it is created at the first D0-ADR cycle
  (its absence is not an error).
- **Slice IDs below are stable references** (A0, D, R16, A2, A3, A5, A6, A7, A8, A9,
  INV, B1). The old `B2…B6` IDs were dissolved into engine-side slices (see §former-
  Track-B); do not reuse them.
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
   witness rendering changes). D, R16, A2, A3, A5, A6, A7, A8, A9 all change verdicts
   (INV changes `errors[0].kind`, not the verdict — bump only if a test matches the kind).
   **Expected progression: v17 → ~v27** (≈10 verdict-changing slices: D1a, R16-1…R16-4,
   A5, A7, A8, A9, INV — each +1). **CI verdict caches run cold throughout Phase 16;
   this is expected, not a regression.** Per-slice bump is the accepted cost (it keeps
   `digest→verdict` auditability honest); the only batching lever is co-committing the
   genuinely verdict-neutral tidies (A0, and INV *if* no `errors[0].kind` test depends
   on it) under an adjacent slice's bump.
2. **Enum ordinal stability (CR-16 lesson) — two distinct rationales.** New enum
   values **must be appended at the END**, but for different reasons:
   - `DefectKind` (R16's `dkOverflowDefect`/`dkDivByZeroDefect`): `defectExclusions` is
     a `set[DefectKind]` rendered into the cache key as an ordinal bitmask
     (`canonicalize.nim`), so mid-insertion silently corrupts every cached `;de=` digest.
   - `SymexErrorKind` (INV's `geVtableDispatch`): **not** in the cache key — append-only
     is for *external-consumer ordinal stability* (tooling matching `errors[0].kind`),
     not cache correctness.
3. **Settings surface (CR-2/CR-9b pattern).** Each new setting (R16's `ArithCheck`,
   A3's iterator-unroll budget, …) must thread through `ResourceBudget` →
   `SymexSettings.+` merge → `validateSymexSettings` → `canonicalize(SymexSettings)`,
   matching the audited inclusion/exclusion comment block. New here: `validateSymexSettings`
   gains a **cross-setting** check (R16) — warn when an enabled `ArithCheck` has its
   corresponding `DefectKind` in `defectExclusions` (active check, finding always suppressed).
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

Value/Effort are rough (S/M/L). All slices are engine-side; the lone upstream item is
B1. Genuine-cannot items are **not** rows here — they live in §Indefinite.

| ID | Slice | Value | Effort | Deps | Status | ADR |
|----|-------|-------|--------|------|--------|-----|
| A0 | CR-9 trailing threadvars → WalkCtx (3 sinks) | low | S | — | stub | — |
| D  | **Defect-flow unification** (D1a/D1b retrofit) | high | L | — | stub | 0011 |
| R16| Arithmetic defects (Range/Overflow/DivByZero) | high | L | D | stub | 0011 |
| A5 | float `classify()` + remaining math ops | med | S | — | stub | 0005 |
| A2 | ref-of-variant / complex pointee deref | med | L | A2-ADR | stub | new |
| A3 | closure iterators (`{.closure.}`) | med | M | — | stub | 0009 |
| A6 | symbolic-length `filter`/`map` (was B4) | med | M | — | stub | 0009 |
| INV| wire never-emitted `se*`/add `geVtableDispatch` | med | S–M | — | stub | — |
| A7 | Unicode rune witnesses (parallel `Rune` path — **Path B only**) | high | M | nim-z3 wrapper | stub | 0006 |
| A8 | radix conversions (fixed-width BV bit-slice) | med | S–M | — | stub | — |
| A9 | ASCII/Latin-1 case-fold + `reverse` + bounded `sort` | low-med | M | — | stub | — |
| B1 | regex `find` over patterns (engine-side or upstream wrapper) | med | M | — | **post-16** | 0006 |

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
- **D1 (was ADR-0011 RD6) — split into D1a + D1b (round-2 feasibility):** retrofit
  IndexDefect/FieldDefect/AssertionDefect **+ NilAccessDefect** (a fourth identical
  site, runtime_heap.nim:327-340) through `routeRaise` so they are catchable. This is
  **not a clean single slice** — highest breaking-change risk → lands before new
  defect types. Three things the implementer must know (full detail in ADR-0011 D1a/D1b):
  1. **Public API break, not just an internal route swap.** E6 makes any non-excluded
     defect surface as `sxRaised{isDefect:true}` unconditionally, so `symexFind(fn,
     tFieldDefect()/tIndexError()/tAssertionViolation()/tNilAccess())` flips from
     `sxSat` to `sxRaised` — witness moves `r.witness`→`r.raisedWitness`. "Preserving
     target findings" means the finding is *not dropped*, NOT that the status is
     unchanged. Callers asserting `r.status == sxSat` must be updated.
  2. **The `if w.target.kind == stkXxx:` fork-gate must be *removed*, not just have its
     body swapped.** Gating the fork on the search *target* (rather than on the defect)
     is precisely what leaves `try: arr[i] except IndexDefect` unmodeled under a
     non-IndexError search. Removing the gate is the load-bearing fix. Behavior change:
     a defect fully caught by a handler now yields `sxUnsat` for that target (pre-D1 it
     spuriously returned `sxSat`).
  3. **D1b is a code change to `assertCoveredBy`, not a test edit.** Its `of sxRaised:`
     arm (symex.nim:1179-1188) hardcodes `covered:false` and never replays — its
     "E2b not shipped" comment is stale (`raisedWitness` is populated). Without a
     replay-from-`raisedWitness` branch, coverage-checking silently degrades to a no-op
     for the defect targets.
  **Perturbs:** `tsymex_phase11_fielddefect.nim`, `tsymex_phase11_walker.nim`,
  `tsymex_phase4_oob.nim`, `tsymex_phase1_assert.nim`, `tsymex_phase7_assertcovered.nim`,
  `tsymex_phase12_witnesses.nim` (sfRaised entries need a distinct `targetDesc`).

## R16 — Arithmetic defects (on the unified D foundation)  ⟶ **[ADR-0011](ADR-0011-rangedefect-overflow.md)**

Adds **RangeDefect** (float→int out-of-range — *replaces* the CR-3 domain-narrowing
interim, runtime_floats.nim), **OverflowDefect** (int `+`/`-`/`*` — uses nim-z3's
`addNoOverflow`/`mulNoOverflow`/`subNoUnderflow`, **confirmed present**,
`_deps/z3/src/z3/bitvec.nim:617-663`), and **DivByZeroDefect** (`div`/`mod` by zero).
Adds enum values `dkOverflowDefect`, `dkDivByZeroDefect` (append-only). Cycles
RD0–RD4 in ADR-0011; **RD2 (float→int) pairs with D1a; R16-1 ≺ R16-2 (acRange gate)**; **RD5 (int-width narrowing
`int8(x)`/subrange) is deferred within R16** — it needs a new `iekConvIntWidth`
parser IR node (`dsl_parser.nim` currently unwraps `nnkConv`/`nnkHiddenStdConv`
silently). **Hang risk:** path-multiplicative forks (RD2/RD3) + BV/Int mixing (RD4 —
skip `svInt`). **Perturbs:** `CR3_CR4_CR6_float`, `F5hang_derefwrite`,
`rereview_drains`, **`cr9_lowerInExpr`** (all four files — 6 asserts total — assert
the `feConvDomainExcluded` hint RD2 retires). **RD2 is a dual-drain, not a
substitution:** the in-range `p.pc` bounding stays (it keeps `toSbv` sound on the
normal path); a *new* `drainConvFloatToIntRaises` walk-arm drain forks the
out-of-range case to `routeRaise`. The retired enum ordinal is frozen, not deleted.

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
  reads the Z3 sort of an `allocateSym` result — undefined for variants. **Also in
  scope:** the identical `isDerefWrite`-side gap (runtime_heap.nim:524-527).
- **A2-ADR scope (round-2 design lens — the two options are NOT equal-cost):**
  - **Z3-datatype encoding requires raw FFI.** nim-z3's typed `declareDatatype[T]`
    surface (`_deps/z3/src/z3/datatypes.nim`) needs a *static Nim marker type* `T` at
    compile time. SUT variant types are *runtime-described* (`IRType`/`itVariant`), so
    the typed surface is inapplicable — using Z3 datatypes means dropping to
    `Z3_mk_constructor`/`Z3_mk_datatype`/`Z3_query_constructor` raw FFI and re-introducing
    the refcount/lifecycle hazards the binding exists to hide. High burden.
  - **Field-split-per-arm extends existing infra and should be the recommended primary.**
    Per-arm heap keys (`typeId & "__" & arm & "__" & field`) + a discriminator heap
    (`typeId & "__disc"` → `Z3Array[Ref_T, Z3Int]`); arm access asserts `disc == tag`
    before read/write — exactly the inline `isVariantField` pattern (runtime.nim:5061-5083),
    lifted to the heap. `heapValueSort` is never called for the whole variant (each
    field/disc has a primitive sort), so the "undefined sort" problem evaporates.
  The A2-ADR should recommend field-split-per-arm; defer Z3-datatypes as a possible
  future optimization. **Harder than A5** → schedule after A5.

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
  document `reserved/unused` like `ceUnsupportedCapture`); add `geVtableDispatch`
  (new-enum append only — ordinal stability per Global Concern 2).
- **Perturbs:** zero known tests (grep of `tests/` for these five kinds is empty —
  the constructs are untested today). Confirm-zero at schedule time by searching for
  SUTs using `seq[seq[T]]` / `Table[K, complexV]` / `set[char]` membership / symbolic
  byte iteration that assert a specific `errors[0].kind`; any such test flips when the
  structured kind replaces the reason-string. Since these are still `sxUnknown` either
  way, INV is verdict-stable for any test that only checks `r.status` — but it is **not
  a no-bump slice**: tooling/tests that match `errors[0].kind` see a new value.

## A0 — CR-9 trailing threadvars (infra carryover)
- Phase-15 CR-9 Stage 5 deferred 3 sinks (`parseIntGateConstraints`,
  `currentClosureCallAxioms`/`…Strs`) — read mid-walk in `trySolve` (no `WalkCtx`
  param). No verdict impact; pure tidiness. Migrate or leave noted.

---

## A7 / A8 / A9 / B1 — former Track B (now engine-side; B1 upstream)  {#former-track-b}

A per-item Z3/nim-z3 capability investigation (evidence in commit log) **collapsed
the former "Track B" almost entirely into engine-side work** — confirming the bar's
verdict that these belong in scope. (Each gets a full `##` section with DoD when
promoted from stub to scheduled; the per-slice content below is the stub.) The residue:

- **A7 — Unicode runes (was B2): ENGINE-SIDE — but MUST NOT reopen ADR-0006.** Z3's
  string sort already ranges over Unicode codepoints 0..0x2FFFF (`z3_api.h`
  `Z3_mk_u32string`); the byte-faithful ≤0xFF model (ADR-0006, **Corey-locked**) was
  our deliberate soundness choice, not a Z3 limit.
  - **⚠ Model-compatibility gate (round-2 breadth lens).** There are two ways to build
    A7, and they are NOT interchangeable. **Path A** — lift the ≤0xFF free-`string`
    constraint (runtime.nim:1390-1402) so Z3 may pick full codepoints — **reopens the
    locked ADR-0006 Decision §1 and breaks all 14 S-cluster test files** (byte-faithful
    round-trip via `evalStr` no longer holds). This is a **spec-assumption escalation**:
    do NOT take Path A without an explicit ADR-0006 lock-unlock + Corey sign-off.
    **Path B (mandated)** — keep the `string` model byte-faithful and untouched; add a
    *parallel* `Rune`/`runes(s)` codepoint path. Note `Z3_mk_u32string` is **absent from
    the current nim-z3 FFI** (ADR-0006 §Reality-note confirms only `Z3_mk_lstring`), so
    Path B requires a nim-z3 wrapper addition first — confirm before scheduling.
  - **Perturbs:** none under Path B (new tests only); all 14 S-cluster files unaffected.
- **A8 — radix (was B5): ENGINE-SIDE.** Z3 int↔str is decimal only, but fixed-width
  `toHex`/`toBin` = BV nibble-extract + a digit-table ITE (quantifier-free, sound).
  `Z3Int` (unbounded) radix is harder (`seqFoldl`, incomplete for symbolic length).
  **Perturbs:** zero known tests (grep of `tests/` for `toHex`/`toBin`/`toOct` is empty;
  these currently fall to `feUnsupportedOp`). New tests only; confirm-zero at schedule.
- **A9 — case-fold ASCII/Latin-1 + reverse + bounded sort: ENGINE-SIDE.** Finite char
  domain ⇒ case-fold is an ITE/`seqMap` mapping (sound for ASCII/Latin-1). `reverse`
  is an index permutation at any length. `sort` for **concrete/bounded** length is a
  fixed comparator network (quantifier-free).
  - **Perturbs (round-2 breadth lens):** `tsymex_phase15_S9_caseconv.nim` — **all 4
    tests** (`toLower`/`toLowerAscii`/`toUpper`/`toUpperAscii`) currently assert
    `sxUnknown` + `errors[0].kind == seUnsupportedStringOp`; after A9 they become `sxSat`
    with case-fold witnesses (update status + error asserts + the file-header deferral
    note). Also update **ADR-0006** §Consequences "Accepted as cost" (drop toLower/toUpper
    from the unmodeled list for ASCII/Latin-1) and the Z3-API-table rows for those ops.
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
- `seq[T]` mutation (`add`/`del`/`setLen`) — seqs modeled immutable/fixed-length —
  and **`seq` slice assignment `s[a..b] = v`** (both hit unstructured `mkUnsupported`).
- **`array[SomeEnum, T]` indexing → compile-time macro `error()`** (`classifyType`,
  dsl_typebridge.nim:~125 accepts only integer-literal index ranges) — this *crashes
  macro expansion* rather than returning `sxUnknown`, strictly worse than an
  Invariant-3 nuance. Fix: derive size from `enum.len` or intercept as a structured kind.
- **`countup`/`countdown(a, b, step)`** loops — unstructured `mkUnsupported` (for-loop
  else-arm); desugar to `while iv <= hi: …; iv += step`, mirroring the `a..b` desugar.
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
`$float`/`parseFloat` (S10b) · `string <` lexicographic · `for i in a..<b`
(exclusive-upper range, dsl_parser.nim) — listed so it isn't re-filed as a gap.

---

## ADRs introduced by this RFC

| ADR | Title | Governs | Authoring cycle | Status |
|-----|-------|---------|-----------------|--------|
| 0011 | Defect-flow architecture + arithmetic-defect modeling | D, R16 | D0-ADR | DRAFT |
| (new) | ref-variant/complex pointee heap encoding | A2 | A2-ADR | not started — scope sketched in §A2 (recommend field-split-per-arm; Z3-datatypes need raw FFI) |

## Sequencing, entry point & Phase-DoD

**Entry point for a new implementer:** the cheapest validation of cadence is **A5**
(pure `lowerMathCall` extension, zero plumbing, zero test breakage). Then the
foundation: **D0-ADR** (lock the defect forks) → **D1a** (retrofit the four target
defects through `routeRaise` — catchable; API break) → **D1b** (`assertCoveredBy`
raisedWitness replay) → **R16-1** (enum + `ArithCheck` policy) → **R16-2** (float→int
RangeDefect) → R16-3 (div-by-zero) → R16-4 (overflow) → A2 (after its design-ADR) →
A3 → A6.

Dependency edges: D0-ADR ≺ D1a ≺ D1b ≺ R16 (R16 builds on unified defects);
**R16-1 ≺ R16-2** (R16-2's out-of-range fork gates on `acRange`, which R16-1
introduces — this is a hard edge, not just table order); RD2 pairs with D1a; A2 ≺
nothing but needs its own ADR (harder than A5); A6/A2/A3/A5/A7/A8/A9 mutually
independent. A7/A8/A9/B1 are ordinary engine-side slices (the former "Track B,"
reclassified by the capability investigation); none is gated on an external
decision **except A7, which must take Path B (no ADR-0006 unlock) — see A7 above.**

**Smallest first defect-cluster commit that compiles + passes:** D1a alone is the
minimal green foundation — it is self-contained (engine route swap + gate removal +
the verdict-API test updates) and does NOT require R16-1/R16-2 to exist. D1b follows
immediately (without it, `assertCoveredBy` coverage-checks silently degrade, so they
ship as a pair even though D1a compiles green on its own).

**Phase 16 complete when:** A0, D, R16, A5, A2, A3, A6, A7, A8, A9, INV each ship
with a regression smoke green on both backends; every `*Unsupported`/`*NotImplemented`
kind in `types.nim` is either emitted or documented reserved. The only items outside
this phase's coverage are B1 (`post-16` in the inventory) and the two documented
genuine-cannot bounds (full-Unicode case-fold, symbolic-length `sort`).

**Scope boundary (Invariant 3):** after Phase 16, Invariant 3 holds for every
construct with a defined `SymexErrorKind` (INV closes the never-emitted ones). The
§Unattended constructs (openArray, countup, `array[enum,T]`, …) still hit unstructured
`mkUnsupported` (or, for `array[enum,T]`, a macro `error()`) — that is the accepted
Phase-16 boundary, not a DoD violation; each is promoted to a slice on demand.

**Default-behavior change (migration):** D1/D1a and R16 flip verdicts for SUTs hitting
defect/arithmetic sites (e.g. `try/except IndexDefect`, overflow under default checks).
Each such slice needs a changelog entry + a `defectExclusions`/`arithChecks` migration
note — tracked here, not just in the ADR §Consequences.

## Pre-scheduling decisions (leans recorded; formalized at D0-ADR)

1. **Defect-mechanism (D, ADR-0011 F1)** — unify (catchable) vs target-only.
   _Lean: unify._ Recorded; locked at D0-ADR — not blocking now.
2. **Overflow-checks policy (R16, ADR-0011 F2)** — new `set[ArithCheck]` distinct
   from `integerSemantics`. _Lean: default all-on (finds bugs)._ Locked at D0-ADR.
3. **First slice** — A5 warm-up vs jumping straight to D. _Lean: A5 first to validate
   cadence, then D._ Not blocking.

(Track B is closed — see §former-Track-B and §Context; no fork remains there.)
