# RFC — Phase 16 (language fragments, part 2 + frontier)

> **STATUS: DRAFT STUB — not scheduled, not reconciled.** Captured 2026-06-27 from
> the Phase-15 code-review session roadmap synthesis (the Explore inventory + the
> RangeDefect mechanics fact-sheet). This doc exists so the deferral frontier is
> not lost; each slice is a *stub* to be fleshed out (and reconciled against code,
> per the [reconciliation pattern](RFC-phase15-reconciliation.md)) before `/tdd`.
> Line citations are point-in-time (post-Phase-15, walker `v17`) — re-verify.

## Context

Phase 15 shipped the 9 language-fragment clusters (Z, L, F, S, H, E, G, C, R) and a
full code-review remediation (CR-1…CR-22; CR-7 god-module split; CR-9 `WalkCtx`
migration + `ResourceBudget` + integer-rep boundary helpers). The engine is
architecturally clean and **every construct below is honestly classified
`sxUnknown` today** (Invariant 3 holds) — so Phase 16 is pure *coverage expansion*,
not bug-fixing. The classification kinds in `types.nim` (`*Unsupported`,
`*NotImplemented`, `*Skipped`, …) literally enumerate the frontier.

Two tracks, split by unblock path:

- **Track A — engine-side** (no library blocker): pure walker/IR/parser work.
- **Track B — nim-z3-blocked**: needs an upstream Z3/nim-z3 primitive first; the
  engine cannot proceed until the library gains the capability (or a workaround
  is designed). Track B is effectively a *separate library project*.

---

## Track A — engine-side slices

### A1 — RangeDefect / overflow raise modeling  ⟶ **highest value; see [ADR-0011](ADR-0011-rangedefect-overflow.md)**
- **Missing:** integer arithmetic overflow is silent BV wraparound (`binBV`,
  runtime.nim:1963); float→int out-of-range is *domain-narrowed* (CR-3 interim,
  `feConvDomainExcluded` sevHint, runtime_floats.nim:159-245) rather than modeled
  as the `RangeDefect`/`OverflowDefect` the program would raise; `dkRangeDefect`
  (types.nim:798) is declared but **never raised**.
- **Why first:** finding overflow/range bugs is exactly what a counterexample
  engine is for; it joins the existing `sxRaised` machinery (`routeRaise`,
  runtime.nim:5541-5657) with the integer abstraction; unblocks nothing else so it
  can land independently.
- **Open design gates (captured in ADR-0011):** target-vs-exception-flow mechanism
  (and whether to *unify* the existing target-only IndexDefect/FieldDefect/
  AssertionDefect so they become catchable); a new overflow-checks policy setting
  (distinct from `integerSemantics`, which is encoding-only); adding
  `dkOverflowDefect` to the enum.
- **DoD (stub):** float→int range fork replaces CR-3; `try/except RangeDefect`
  modeled; respects `defectExclusions`; both backends; ADR-0011 accepted.

### A2 — `ref`-of-variant + ref-of-complex pointee deref  (CR-19 follow-on)
- **Missing:** `ref T where T is a variant object` → `heRefVariantUnsupported`
  (sevError, runtime.nim:6332); ref-of-complex pointees (e.g. `ref seq[T]`) still
  `sxUnknown` via `liftHeapValue`. CR-19 (this review) aligned only *primitive*
  pointee sorts (`dsl_typebridge` `classifyFieldType`).
- **Approach (stub):** extend the field-sort alignment + heap value-sort machinery
  (`runtime_heap.nim` `heapValueSort`/`liftHeapValue`) to variant and composite
  pointees; model variant identity + aliasing interaction.
- **DoD (stub):** `h.v[]` for a `ref`-to-variant field resolves; both backends.

### A3 — Closure iterators (`iterator foo(): T {.closure.}`)
- **Missing:** `ceNotImplemented` (runtime.nim:3287 / ADR-0009:381). No iterator-
  protocol semantics.
- **Approach (stub):** model the resumable-state closure-iterator protocol (env +
  resume point) over the existing closure encoding (ADR-0009); likely bounded
  unrolling like `for`/`while`.
- **DoD (stub):** a `{.closure.}` iterator consumed in a `for` symexes; both backends.

### A4 — `func` effect-tracking / `proc` distinction
- **Missing:** Phase 15 treats `func` identically to `proc` (ADR-0009:383). No
  purity/effect modeling.
- **Approach (stub):** decide whether effect-tracking buys soundness/precision
  here at all (Nim's effect system is semchecker-verified pre-parse). Likely a
  *documentation/trust* slice rather than encoding work — confirm before scheduling.
- **DoD (stub):** explicit decision recorded; tests if any behavior changes.

### A5 — Float `classify()` + remaining `std/math` ops
- **Missing:** `classify(f)` → `FloatClass` enum branching, `copySign`, `nextafter`,
  etc. → `feUnsupportedOp` (sevError, runtime.nim:6237 / ADR-0005).
- **Approach (stub):** map FP classification to the `FloatClass` enum via the
  existing FP predicate machinery (`isNaN`/`isInf`/… already shipped); add the
  remaining ground FP ops.
- **DoD (stub):** `case classify(x)` symexes; both backends.

---

## Track B — nim-z3-blocked slices (upstream first)

> Each needs a Z3/nim-z3 primitive that does not exist in the pinned `nim-z3
> v2.0.0` FFI today. Sequencing: **extend nim-z3 → then the engine slice.** Until
> then these stay honest `sxUnknown`.

### B1 — Regex `find`/`replace` over patterns  (`s.find(re"…")`)
- **Blocker:** no `Z3_mk_seq_indexof_re` (Z3 `indexOf` is fixed-string-needle only).
- **Current:** `seUnsupportedRegex` (sevError, runtime.nim:6253); parser already
  emits the `iekStrFindRe` IR node routed to the classified error.
- **Note:** `iekStrReplaceRe` is gated behind `-d:z3WithSeqReplaceRe`
  (`seZ3VersionMissing` sevWarning, runtime.nim:6260) — partially available on newer Z3.

### B2 — Unicode / multi-byte rune witnesses
- **Blocker:** no `Z3_mk_u32string` scalar-value constructor in the FFI; the
  byte-faithful ≤0xFF Latin-1 model (ADR-0006, Corey-locked) is the *soundness*
  mechanism. Real runes need a U32 string sort + a UTF-8 encode/decode layer so
  witnesses round-trip.
- **Current:** multi-byte runes cannot be synthesized (ADR-0006:273-277).

### B3 — `toLower` / `toUpper` case-folding
- **Blocker:** no Z3 case-fold op. Possible workaround: regex-range case
  approximation (design required, may be unsound for full Unicode).
- **Current:** `seUnsupportedStringOp` (sevError, ADR-0006:243,279).

### B4 — Symbolic-length `filter` over `seq[T]` (axiomatize path)
- **Blocker:** no Z3 `seqFilter` HOF primitive.
- **Current:** `ceUnsupportedHof` (sevError, runtime.nim:6146 / ADR-0009:384). The
  concrete-length inline path (≤ `seqInlineThreshold`) already works; only the
  symbolic-length axiomatize path is blocked.

---

## Out of scope / indefinite (not Phase 16)
- `float80` / extended precision (not a Nim ABI concern; ADR-0005:244).
- Signaling-vs-quiet NaN distinction (ADR-0005:239-240).
- NaN-payload witnesses for `cast`-using SUTs (proptest DSL limitation, not engine).
- `cstring` FFI interop (ADR-0006:282-283).
- String mutation `s[i]=c` / `s.add` (Z3 strings immutable; would need functional-
  update encoding — revisit only if demand appears; ADR-0006:280).

## Already handled (do NOT re-list as deferred)
- `maxSplitParts` wiring — **done** this review (CR-11/CR-18, commit b7258f7).
- RFC-completeness robustness (frontier pruning C3, Z3-internal-error policy C4,
  constraintDigest) — **largely shipped via Phases 11–14** (`phase14_frontier_pruning`,
  `phase14_c4_z3error` tests exist); audit for residuals only.

---

## Sequencing & process
- Same cadence as Phase 15: **cluster-by-cluster `/tdd`** slices, cheapest-infra →
  deepest; one ADR per cluster; a reconciliation pass before each cluster
  ([RFC-phase15-reconciliation.md](RFC-phase15-reconciliation.md) pattern).
- **Always** bound test runs via `scripts/dt-bounded.sh` + `scripts/parity-check.sh`
  (both C and C++ backends); 137 = Z3-hang regression. Non-termination is a real
  failure mode (the F5 lesson).
- Recommended order: **A1 (RangeDefect) → A2 (ref-variant) → A5 (float classify)
  → A3 (iterators) → A4 (func)**; Track B only after a nim-z3 capability decision.

## Open design gates (forks — resolve when scheduling, not now)
1. **Defect mechanism unification** (A1 / ADR-0011): route defects through
   `routeRaise` (catchable) vs target-only `sxSat`. Affects existing
   IndexDefect/FieldDefect/AssertionDefect too. _Lean: unify, see ADR-0011._
2. **Overflow-checks policy** (A1 / ADR-0011): new setting distinct from
   `integerSemantics`; default checked vs unchecked. _Lean: a `checkedArith`
   setting, default on (finds bugs)._
3. **Track B commitment:** is extending nim-z3 in scope, or is string/regex/HOF
   depth parked indefinitely? _Genuine fork — needs your call on appetite._
