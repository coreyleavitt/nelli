# RFC — Phase 15: language-fragment completeness

> ⚠️ **RECONCILIATION REQUIRED — read `RFC-phase15-reconciliation.md` first.**
> This RFC was authored against an idealized file layout. The file paths in
> the cycle GREEN-lists (`strategies/*.nim`, `smt/db.nim`, `smt/walker.nim`)
> and a few "currently…" premises are wrong. `RFC-phase15-reconciliation.md`
> is the authoritative override layer (path map, premise corrections, the
> item-1 named-tuple design, and the net-new-symbol registry). The *design*
> below stands; consult the reconciliation doc for *where* each change lands.
> Notably: Z0's `:unk` skip-load guard is **struck** — `:unk` is the live
> suffix and a guard would break current caching (see reconciliation §C.3).

> Closes the language-coverage gaps surfaced by the round-of-rounds
> reviewer quote at the end of Phase 14:
>
> > Not covered — and this is the bug-rich territory: generics,
> > closures/procs-as-values, ref/pointer aliasing, exceptions,
> > templates/macros, float, full strings.
>
> Phase 15 brings the symex engine from "covers the data-shape
> majority of Nim" to "covers the language fragments a real PBT
> consumer actually writes." It is the largest Phase to date in
> cycle count (~45-65 slices across 8 clusters) and the deepest in
> design surface — three of the clusters (G, C, R) are first-of-kind
> for proptest.
>
> The standing directive **`complete-lib-not-consumer`** governs:
> every reviewer-flagged gap is in scope by default. No deferrals
> on "wait for concrete demand" — a gap shipped is a future "not
> implemented" wall.
>
> **Revision history**
> - **v1** — initial draft. 8 clusters (Z, L, F, S, E, G, C, R),
>   ordered cheapest infra → deepest, so type-bridge work compounds.
>   Heap model (Cluster R) decided up front: **logical heap via Z3
>   array theory + symbolic ref addresses + counter-based freshness**
>   (KLEE/Pex/angr/CBMC standard). Static-analysis paradigms
>   (region-based, Andersen, Steensgaard) rejected as wrong-tool
>   for a symex engine that already owns path-sat. nim-z3 v2.0.0
>   pin bump folded in as Cluster Z preamble. ~55 cycles total.
> - **v2 (current)** — round 1 architect review (4 lenses, 62
>   findings deduped) baked in. Full findings preserved in
>   `RFC-phase15-language-fragments.round1-findings.md`. Material
>   changes:
>   - **EffectCtx record** extracted from `WalkCtx` bundling
>     handler stack, in-flight exception, closure symbol table,
>     ref sorts, allocation counters; per-walker concerns only.
>     Per-path concerns (`heaps`, `heapDepth`, `allocCounters`
>     snapshot) live on `Path` and are deep-copied at every fork
>     site. Addresses the Phase 14 shared-WalkCtx bug class.
>   - **Walker version bumped per cluster, not once at R12**:
>     `"4"→"5"` at F8, `"5"→"6"` at S11, `"6"→"7"` at E7,
>     `"7"→"8"` at G10, `"8"→"9"` at C6, `"9"→"10"` at R12.
>     Eliminates mid-/loop stale-cache risk. Invariant 1
>     rewritten accordingly.
>   - **Preparatory cycles added**:
>     - **Z0** — close Phase 14 carryover (B4 named-field tuple
>       strategies; populate empty `constraintDigest` on `floats`,
>       `strings`, `lists`, `tables`, `sets` strategies).
>     - **R0** — refactor `Path` to carry `heaps`, `heapDepth`,
>       `allocCounters`; audit every fork site in the existing
>       walker for deep-copy correctness. Lands before R1.
>     - **R1b** — inter-procedural heap threading: every
>       `isCall`/`isGenericCall`/`iekClosureCall` descent passes
>       caller `path.heaps` in and merges callee's exit `heaps`
>       out. Addresses Depth-CRIT-2.
>   - **Cycle splits**:
>     - **E2 → E2a (structural `sxRaised` cascade through
>       `symex.nim`/`runtime.nim`/`types.nim`/cache-key table
>       with stub `sfRaised` arm) + E2b (real `walk(isRaise)`
>       semantics)**.
>     - **G1 → G1a (IR + canonicalize) + G1b (parser) + G1c
>       (walker dispatch + cache + cap)**. G2 and G9 folded
>       into G1c. Cluster G stays at 10 cycles net.
>     - **C2 → C2a (closure construction) + C2b (closure call
>       dispatch)**.
>     - **R12 → R11b (cross-cluster regression sweep, no
>       format/version changes) + R12 (final walker bump,
>       rendering bump, heap-snapshot witness format)**.
>     - **S7 → S7a (UTF-8 BMP encoding) + S7b (regression
>       smoke + determinism doc update)**.
>   - **New cycles added**:
>     - **S8** — `&` string concatenation (`Z3_mk_seq_concat`).
>     - **S9** — `toLower`/`toUpper`: emit
>       `seUnsupportedStringOp` classified error (Z3 String
>       theory has no native case conversion; regex-range
>       approximation deferred to backlog).
>     - **S10** — `$int`/`parseInt` via nim-z3's
>       `Z3Int.toStr`/`Z3String.toInt`; `$float`/`parseFloat`
>       emit `seUnsupportedStringOp` classified error.
>     - **S11** — string mutation (`s[i] = c`, `s.add(c)`)
>       classified as `seUnsupportedStringOp`; documented in
>       `determinism.md`.
>     - **E4a** — dynamic user-exception hierarchy: parser
>       walks `nnkTypeDef` ancestors of any `except` clause
>       type symbol via `getImpl`; populates
>       `userExnHierarchy: Table[string, string]`. Closes
>       soundness gap for user-defined exceptions.
>     - **E8** — `getCurrentException()` /
>       `getCurrentExceptionMsg()`: msg from in-flight
>       `raiseMsg` IRExpr (evaluated in E2 — see below);
>       exception object is `svUninterpRef` keyed by typeId.
>     - **F9** — `array[N, float32]`/`array[N, float64]`
>       element-type-bridge audit (the existing array walker
>       must accept `svFloat32`/`svFloat64` element kinds).
>     - **R13** — closures capturing `ref T` locals
>       (composition with C5; lifts the `ceUnsupportedCapture`
>       classification once R-cluster machinery exists).
>   - **ADR externalization**: ADRs 0005–0010 authored as
>     **standalone files** (`docs/symex/ADR-000N-*.md`)
>     matching ADR-0001..0004 depth, **before** their
>     respective cluster's TDD begins. RFC retains one-paragraph
>     pointers in the "ADRs introduced" section.
>   - **`sxRaised` cache key** changed from `:raised` to
>     `:raised:<typeId>`. Cache key suffixes standardized on
>     full English words: `:sat`, `:unsat`, `:unknown`,
>     `:raised:<typeId>`. The legacy `:unk` suffix is migrated
>     in Z0.
>   - **`WalkCtx.found`** changed from `Option[RawResult]` to
>     `seq[RawResult]` so `sxRaised` accumulates alongside
>     `sxSat` for multi-finding mode.
>   - **`WalkResult` private union** introduced for internal
>     handler-stack propagation. Only the top-level `runSymex`
>     maps `WalkRaised → sxRaised`. Prevents internal
>     intermediate states from leaking to the public verdict.
>   - **Error-kind prefix scheme** standardized:
>     `he`=heap (R), `fe`=float (F), `se`=string (S),
>     `ge`=generics (G), `ce`=closures (C), `ee`=exceptions (E).
>     `heInstantiationCapped`→`geInstantiationCapped`,
>     `heConceptViolation`→`geConceptViolation`,
>     `heUnresolvedGeneric`→`geUnresolvedGeneric`,
>     `seNotImplemented`(closure)→`ceNotImplemented`,
>     `seUnsupportedCapture`→`ceUnsupportedCapture`.
>     `SymexErrorKind` enum added before E1; `kind: string`
>     becomes `kind: SymexErrorKind`.
>   - **Closure encoding**: phantom-typed `Z3FuncDecl[ArgsTup, Ret]`
>     cannot be instantiated at walk time. C2b spec'd to use raw
>     `Z3_mk_app` via `ffi.nim` for closure application.
>     `closureSyms` keyed by `(site, envSortId, paramsSortTupleId)`
>     to disambiguate generic closure instantiations. Closure
>     equality semantics resolved (Open Question 6 closed):
>     **nominal-for-site + structural-for-env** — matches Nim
>     runtime proc-value semantics. Closure `funcSym` axiom
>     asserted as `implies(path.pc, funcSym(env,args) == ret)`
>     not unconditionally (prevents cross-path over-constraint).
>     `maxClosureInlineCount` setting added (default 64).
>   - **`mkString` codepoint/byte clarification**: ADR-0006
>     amended — `mkString(nimStr)` produces a Z3 String whose
>     Z3-side `len` equals `nimStr.runeLen` (codepoints), NOT
>     `nimStr.len` (bytes). S2 RED test explicitly covers a
>     multi-byte literal and asserts the codepoint length.
>     Divergence from Nim's byte-indexed `s.len` documented in
>     `determinism.md`.
>   - **`finally`/`inFlightExn` lifecycle** specified explicitly
>     in E5 GREEN: set on handler entry, cleared on handler exit
>     normal completion, bare `raise` inside `finally` on
>     normal path produces `sxRaised` from finally itself
>     (not `raiseOutsideHandler`).
>   - **F5 helper corrected**: `symValToBV64` was undefined.
>     F5 GREEN now spec's `intToBv[64](sv.zi, Z3BitVec[64])`
>     then `toFpFromSigned(rmRNE(), bv, Z3Float64)`. Width
>     dispatch handles `svBV32`/`svBV64` directly.
>   - **`iuFpNeg` dropped**: F3 reuses `uNeg` with
>     runtime-dispatch on `sv.kind` (consistent with FP binops
>     reusing `ibAdd` etc.).
>   - **`split` soundness**: bounded to `maxSplitParts` (new
>     setting, default 8). Adds `forall i < seqLen(parts). not
>     contains(parts[i], sep)` constraint; overflow yields
>     `seZ3StringIncomplete`.
>   - **`bytes(s)` symbolic-length**: emits
>     `seBytesSymbolicLength` classified error when `s.len` is
>     symbolic at walk time.
>   - **`distinct T` bijection**: G4 adds ejection function
>     alongside injection, with bijectivity axioms.
>   - **`signatureHash` defined**: `symBodyHash(calleeSym)` or
>     equivalent body-content hash; not the bare-name
>     `strVal`. G2 cache key schema: `name#typeargs` for
>     generics, `name` for non-generics.
>   - **Uninterpreted sort path corrected**: G4/R1 use
>     `Z3_mk_uninterpreted_sort` via `ffi.nim` returning
>     `RawZ3Sort` (the phantom-typed `Z3UninterpretedVal[T]`
>     API requires compile-time `T`).
>   - **`for c in s` byte iteration** and **`s.high`**: classified
>     `seByteIterUnsupported`/`seByteIndexUnsupported`; routed
>     through `bytes(s)` deferred to Phase 16.
>   - **`int(f)` overflow**: F5 emits `sxRaised(RangeDefect)`
>     on out-of-range conversion paths.
>   - **`inc(p)`/`dec(p)` pointer arithmetic**: R8 classifies
>     as `hePtrArith`.
>   - **`raiseMsg` evaluated**: E2 evaluates `stmt.raiseMsg`
>     via `walkExpr`; result stored in `RawResult.raisedMsg:
>     Option[string]`.
>   - **`IRRegex` simplified**: stored as `rePatternStr:
>     string` at IR layer; parsed to Z3 Regex at walk time.
>     No recursive-type boxing needed.
>   - **Open Question 4 closed**: Defects modeled as
>     `sxRaised(typeId, isDefect=true)`. The silent-pass risk
>     under `sxUnreached` is unambiguous; per
>     `complete-lib-not-consumer`, this is not a fork.
>   - **Open Question 5 closed**: `maxInstantiationsPerProc =
>     64` (consistent with `maxFrontierSize`/`maxInlineSeqLen`
>     family defaults).
>   - **Open Question 6 closed**: see closure semantics above.
>   - **Open Question 7 closed**: `cast[ptr T]` →
>     `sxUnknown(heUnsafeCast)`. Safe-cast modeling deferred
>     to Phase 16 backlog.
>   - **Cycle count**: ~70 (was ~55).
>   - **LOW-tier fixes** (dead-text removal at R5, F4 NaN
>     bit-pattern DoD moved to F7, S1 `string.len` routing
>     guard, G8 Cluster S dependency note, `:unknown`
>     standardization, `sfUnknown`/`sxUnknown` typo sweep,
>     `InlinePolicy` enum replacing `maxInlineSeqLen=0`
>     sentinel, per-cluster cycle tables with key-dependency
>     column, F1 precondition documented, S6 regex
>     parser scope, `maxInlineSeqLen=maxInt` warning) applied
>     in the per-cluster bake-in.
> - **v3 (current)** — round 2 architect review (4 lenses, 85
>   raw findings deduped to ~67) baked in. Full findings preserved
>   in `RFC-phase15-language-fragments.round2-findings.md`. Zero
>   open forks survived the fork-filter; every change below is a
>   PhD-CS clear-best fix. Material changes:
>   - **Cluster Z expanded to 5 cycles**: Z0 (Phase 14 carryover),
>     Z1 (pin bump), Z2 (regression smoke), **Z3** (cross-cutting
>     infra: `SYMEX_PLAN.md` authored with the 70-row cycle table;
>     `SymexErrorKind` enum replaces `SymexErrorInfo.kind: string`
>     with all Phase-14 + Phase-15 kinds populated; `classifyType`
>     accepts `char` (`uint8`) and strips `nnkSinkTy`/`nnkLentTy`
>     wrappers; `SymexErrorInfo.severity` field added with
>     `sevHint`/`sevWarning`/`sevError`), **Z4** (`WalkCtx.found:
>     Option[RawResult] → seq[RawResult]` field-type change with
>     `shouldStop` semantics rewrite — extracted out of E2a per
>     Feas-H9 so E2a only adds the structural `sxRaised` cascade).
>     Cluster Z does not bump walker version (still verification/
>     infrastructure).
>   - **New Cluster H — heap preparation** (single cycle, between
>     S and E). H1 promotes the former R0 (`Path` refactor for
>     `heaps`/`heapDepth`/`allocCounters`, fork-site audit) ahead
>     of Cluster E so E3/E5/E7's heap-state threading compiles.
>     Cluster R loses R0; H1 is its preparatory equivalent.
>     Cluster R is now 15 cycles (R1 → R13).
>   - **`EffectCtx` split into `WalkerStatics` + `CallFrameCtx`**
>     (closes Des-CRIT-D1). `WalkerStatics` (immutable post-parse):
>     `refSorts`, `nilConsts`, `closureSyms`, `userExnHierarchy`,
>     `distinctSorts`, `exnTable`. `CallFrameCtx` (pushed/popped
>     on call descent): `handlerStack`, `inFlightExn`,
>     `closureInlineCount`. `WalkCtx.statics` + `WalkCtx.frame`
>     replace `WalkCtx.effects`. Call-frame push/pop spec'd in E1
>     and C2a.
>   - **`WalkerStatics.distinctSorts`** caches `Z3Sort[stUninterpreted]`
>     per distinct type name across all call frames (closes
>     Depth-MED-4); bijectivity axioms asserted at most once per
>     `(typeId, runSymex)` pair (Des-MED-5, Feas-MED-2). For base
>     types in FP/String fragments, axioms are **skipped** and
>     `geDistinctBijectivitySkipped` classified hint is added
>     (Depth-HIGH-6).
>   - **Walker/rendering version constants** live in
>     `canonicalize.nim` (correcting per-cluster GREEN file
>     references that wrongly cited `runtime.nim`/`walker.nim`).
>     `canonicalize.walkerVersion` is the single source of truth;
>     no string-literal duplication. New cross-cluster invariant 6.
>   - **`SymexErrorInfo.severity`** field added in Z3; values
>     `sevHint`/`sevWarning`/`sevError`. Invariant: `sxUnknown`
>     ⇒ ≥1 `sevError` entry. Halting kinds (`heDepthExhausted`,
>     `heUnsafeCast`, `hePtrArith`, `feUnsupportedOp`, etc.) =
>     `sevError`; informational kinds (`hePtrFamily`,
>     `geDistinctBijectivitySkipped`, classifier hints) =
>     `sevHint` (Des-HIGH-D2). New cross-cluster invariant 7.
>   - **`withSymexSettings`** builder added to public API in Z3:
>     `withSymexSettings(base = defaultSettings()) do (s: var
>     SymexSettings): s.maxHeapDepth = 2`. Composition primitive
>     for the now-9-knob settings family (Des-HIGH-D1). Documented
>     in cross-cluster section.
>   - **`InlinePolicy` enum** moved from C4 to Z3 (cross-cluster
>     types section), alongside other `SymexSettings` field types
>     (Des-HIGH-D4). Marked exported.
>   - **`DefectKind` enum** replaces `defectExclusions: set[string]`
>     with `set[DefectKind]` (`dkAssertionDefect`, `dkIndexDefect`,
>     `dkFieldDefect`, `dkRangeDefect`, `dkOutOfMemoryDefect`,
>     `dkStackOverflowDefect`, `dkOther`); landed in Z3 (Des-MED-D1).
>   - **`svUninterpRef`** added to `SVKind` in Z3 with exhaustive
>     dispatch stubs (`walk`, `extractFromSymVal`, `allocateSym`,
>     `typeOf`, `symValHash`, `iteSymVal`, `svEq`) so E8's
>     `getCurrentException()` use-site compiles. Closes
>     Breadth-CRIT-2 / Des-MED-D7.
>   - **`WalkResult`/`RawResult` unification**: `WalkResult`
>     renamed to `InternalVerdict`, kept private to symex.nim;
>     `RawResult` becomes the public type; sole conversion via
>     `toPublic(iv: InternalVerdict): RawResult` at `runSymex`
>     boundary (Des-HIGH-D3). Closes the duplicate-union problem.
>   - **Multi-`sxRaised` cache serialization**: serializer iterates
>     `found: seq[RawResult]` and writes every `sxRaised` finding
>     under its own `":raised:" & typeId` key; deserializer reads
>     all matching keys for the SUT prefix and reconstructs the
>     seq (Depth-CRIT-1). `loadAll(sutKeyPrefix): seq[RawResult]`
>     helper replaces single-probe load. E2a DoD test:
>     two-raise-path SUT round-trips both findings.
>   - **`cacheKeyRaised(typeId): string` proc** replaces the bare
>     `cacheKeyRaisedSuffix*` constant (Des-MED-D4); no caller-side
>     string concat.
>   - **`allocCounters` write-back uses `max`**, not replacement
>     (Depth-CRIT-3). R1b spec amended; freshness guarantee
>     preserved across nested calls.
>   - **Closure axiom under multi-return-path** (Depth-CRIT-2):
>     C2b collects `seq[InternalVerdict]` from body descent; for
>     each sub-path `(pc_i, v_i)` assert `implies(path.pc and
>     pc_i, funcSym(env, args) == v_i)`. Main axiom uses Z3
>     `ite`-merge of sub-path results.
>   - **`lambdaSite` key** changes from `"file:line:col"` (
>     formatting-sensitive) to `(symBodyHash(lambdaBody),
>     declOrderIndex)` matching G's `symBodyHash` convention
>     (Des-HIGH-D6). ADR-0009 amended.
>   - **`itLambda` → `iekLambda`** rename (value-producing
>     expression kind; Des-MED-D2). Prefix-convention comment
>     added to `types.nim`.
>   - **Closure `params` carry post-monomorphization types**
>     (Depth-HIGH-D4). C1 GREEN specifies `iekLambda` emitted
>     after monomorphization pass; RED test exercises same lambda
>     site at two type instantiations, asserts distinct cache
>     keys.
>   - **`split(s, "")` empty-separator case** handled (Depth-HIGH-D2):
>     when `sep` is the empty literal, skip the
>     `contains(parts[i], sep)` constraint and assert `forall i.
>     len(parts[i]) == 1 and seqLen(parts) == len(s)` instead.
>     Concrete-string special-case in S5 uses inline enumeration
>     (no quantifier) for `s` literal + single-char sep
>     (Feas-MED-1).
>   - **`parseInt` raises-path** added (Depth-HIGH-D3): S10
>     forks digits-path (`Z3String.toInt(s) ≥ 0`) and raises-path
>     (`< 0` ⇒ `sxRaised("ValueError")`). S10 **reordered to
>     after E1 lands** within Cluster S — split into S10a (digits
>     model only, before E) and S10b (raises-path, after E1).
>     Negative-string preprocessing via `"-"` prefix detect +
>     `toInt(substr)` + negation (Depth-MED-D1). Also covers
>     `parseInt("-42")`.
>   - **`finally` multi-path threading** specified (Depth-HIGH-D5):
>     E5 enumerates all `tryBody` exit continuations (normal,
>     raised, plus per-branch from internal forks); walks
>     `tryFinally` per continuation; cross-products outcomes.
>     E7 DoD test adds conditional-write try + finally read.
>   - **Inter-procedural `WalkRaised` propagation** specified
>     (Depth-HIGH-D7): `isCall`'s walker arm propagates callee
>     `WalkRaised` into caller's handler stack; heap state at
>     raise point merged. E7 DoD: SUT calls helper that raises,
>     outer try catches.
>   - **`E5` finally-raised heap state** (Depth-MED-D7): the
>     `WalkRaised` from the finally body carries heap as of the
>     raise point inside finally (includes pre-raise finally
>     writes). DoD asserts this explicitly.
>   - **`E3` exact-match transitional flag** (Depth-MED-D2): E3
>     GREEN explicitly notes that string-equality match is
>     transitional, superseded by E4's `isSubtypeOf`; negative
>     test confirms base-type handler does NOT catch derived
>     until E4 lands.
>   - **`ref object` inheritance** (Depth-HIGH-D8): R6 detects
>     inherited fields via `defining type ≠ deref'd type`,
>     resolves to flat layout (base fields first). DoD covers
>     both inherited and own fields.
>   - **`ref object` with variant fields** (Feas-MED-4) emits
>     `heRefVariantUnsupported` classified error instead of
>     reaching a `Defect` on `svTuple` dispatch.
>   - **Freshness assertion cap** (Feas-MED-3): R2 adds
>     `maxFreshnessAssertions: int = 256` (0 = unlimited); cap
>     overflow ⇒ `heFreshnessCapExceeded` hint. R5 nil-fork
>     short-circuits when `p != nil` already in path condition
>     (Depth-LOW-4).
>   - **`maxHeapDepth = 0` semantics** (Depth-MED-D3): falls
>     back to `maxCallDepth`, then hard cap 256 if both 0.
>     R9 GREEN guard `if settings.maxHeapDepth > 0 and …`
>     explicitly written (Des-LOW-D1).
>   - **R1 cycle split** R1 → R1a (IR + `SVKind` variants +
>     exhaustive dispatch stubs) + R1 (heap-feature: `refSorts`,
>     `nilConsts`, `allocRefSort`, `isDeref` select). Mirrors
>     G1a/G1c split rationale (Feas-HIGH-3).
>   - **C1 PoC for raw `Z3_mk_app`** (Feas-HIGH-2): C1 DoD adds
>     a fixture that constructs a `RawZ3FuncDecl` with
>     runtime-known sorts, calls `Z3_mk_app`, and verifies Z3
>     accepts. `sortOfTuple(svTuple): RawZ3Sort` helper added.
>   - **`symBodyHash` collision fallback** (Feas-HIGH-5):
>     G1a fallback key is `getImpl.lineInfo.filename & ":" &
>     strVal`, NOT `repr.hash`. DoD covers same-name procs in
>     two modules.
>   - **`G4` axioms only for decidable base sorts** (Depth-HIGH-D6):
>     base ∈ {int, BV, bool}: assert injectivity + ejectivity.
>     base ∈ {FP, String}: skip + emit
>     `geDistinctBijectivitySkipped`. Documented in ADR-0008.
>   - **`distinct T` nested chain** (Breadth-HIGH-H6): G4 DoD
>     adds recursive ejection + per-level bijectivity test for
>     `type KiloMeters = distinct Meters`.
>   - **`sink`/`lent` strip in `classifyType`** (Z3 includes
>     this; Breadth-HIGH-H5).
>   - **`E4` ExnTypeTable source-of-truth** documented
>     (Feas-LOW-1) — the manual coverage list is the authoritative
>     spec, with a DoD assertion that user-defined Defect
>     subtypes route to `dkOther`.
>   - **`F6` adds Z3 FP-native predicates** (Breadth-MED-M2):
>     `isNaN`, `isInf`, `isFinite`, `isNormal`. `classify(f)`
>     emits `feUnsupportedOp` (deferred).
>   - **F9 expanded** to also audit `seq[float32/64]` SUT
>     parameter types (Breadth-HIGH-H2 fold), `array[N, float]`
>     NaN extraction via `model.eval(…, model_completion=true)`
>     (Depth-HIGH-D1), and `object variant` arm-field bridge
>     (Breadth-HIGH-H3). Now spans F9a (array elem), F9b
>     (seq[float] param), F9c (variant arm-field).
>   - **S6 split**: S6a (`regex_parser.nim` standalone parser
>     + unit tests covering `\d`, `\w`, `\s`, `[^…]`, `(?:…)`
>     in addition to the v2 set) + S6b (walker integration).
>     Closes Des-HIGH-D5, Depth-MED-D5, Feas-LOW-3.
>   - **Z3 codepoint↔BV8 interop classified** (Breadth-MED-M9):
>     `s[i] in set[char]` ⇒ `seUnsupportedSetCharInterop`.
>   - **`Table[string, V]` for non-`int` V classified**
>     (Breadth-HIGH-H1): parse-time `seUnsupportedTableValType`
>     emitted from Z3 sweep. Subsumes Breadth-MED-M3.
>   - **`seq[ref T]` in scope** (Breadth-MED-M4): R3 DoD adds
>     array element of `svRef` test. `seq[seq[T]]` classified
>     `seNestedSeqUnsupported` (Phase 16 backlog).
>   - **`var ref T` rebinding** (Breadth-HIGH-H4): R8b cycle
>     covers heap write-back + caller-side ref rebinding;
>     fallback `heUnsupportedVarRef` if implementation slips.
>   - **`owned T` / `WeakRef` / `Atomic[T]`** (Breadth-LOW-L4):
>     classified `heUnsupportedOwnership` in `classifyType`.
>   - **`E7` composition test rewrite** (Feas-HIGH-4): uses
>     integer locals not `ptr int` deref. The `ptr T`+finally
>     composition moves to R13 (renamed to include this scope).
>   - **ADR index table** added to ADRs section (Des-MED-D6);
>     ADR-0009 + `closures.md` co-authored in C1 (Breadth-LOW-L6).
>   - **`witness-format-v3.md` authored in R11b's DoD**
>     (Feas-MED-7). R12 sub-test independence preserved
>     (Feas-MED-6).
>   - **ADR-authoring cycles** named explicitly: F0-ADR, S0-ADR,
>     G0-ADR, C0-ADR each precedes its cluster's first feature
>     cycle (Feas-HIGH-6). E0-ADR folds into Z4 (the E-prep
>     `WalkCtx.found` field-change cycle). R0-ADR folds into H1.
>   - **`maxFreshnessAssertions`, `maxBytesEncodingLen`,
>     `maxSplitParts`, `maxClosureInlineCount`,
>     `maxInstantiationsPerProc`, `maxHeapDepth`,
>     `defectExclusions`** — all wired through `withSymexSettings`
>     and the canonicalize cache-key suffix.
>   - **`E8`** lifts to `svUninterpRef`-returning extractor (now
>     a defined SymVal variant via Z3). `getCurrentExceptionMsg()`
>     uses `inFlightExn.msg.get("")` correctly.
>   - **Cluster preambles** gain "Out of scope for this cluster"
>     tables (Breadth-LOW-L1) listing classified-error ops for
>     auditability.
>   - **Cluster G cycle table** documents folded G2, G9 with
>     explanatory rows (Breadth-LOW-L3).
>   - **G8 multi-param key** spec'd: name→type via
>     `gatherTypeSubst` table, then sorted-by-name (Depth-LOW-D3).
>   - **Walker version invariant 1** documents the general rule
>     "+1 per walker-semantic cluster"; explicit for Phase 16
>     (Des-LOW-D4).
>   - **Cycle count**: ~78 (was ~70 after round 1). Increase
>     reflects Z3/Z4 cross-cutting cycles, H1 promotion, R1
>     split, S6 split, S10 split, F9 expansion to a/b/c, and
>     ADR-authoring cycles.

## Scope and non-scope

**In scope (this RFC):**

1. **Cluster Z** — bump `nim-z3` pin to v2.0.0. The v2.0.0
   migration doc's "Proptest sync note" already confirmed that
   none of the eight symbol-level renames appear in proptest's
   source tree (proptest's only nim-z3 import is the umbrella
   `import z3` in `smt/runtime.nim`), so this cluster is build-
   system + lockfile + regression smoke — no source rewrites
   expected. The cluster still exists so the regression smoke
   under v2.0.0 lands on the record before F/S exercise the
   stabilized FP and String surfaces.
2. **Cluster L** — templates and macros. Verification-heavy; the
   Nim semchecker expands templates and macros before our walker
   sees the tree, so most of L is auditing the boundary and
   adding regression coverage.
3. **Cluster F** — `float`, `float32`, `float64`. Z3 FP bridge,
   literal lifts, NaN/Inf semantics, eval-side extraction,
   real↔float conversions.
4. **Cluster S** — full `string` surface. Today's symex strings
   are bounded ASCII via byte-sequences; full strings means Z3
   String + Regex theories: `find`/`contains`/`startsWith`/
   `endsWith`/`replace`/`replaceAll`/codepoint indexing/regex
   matching/`split`/`join`/`toLower`/`toUpper`.
5. **Cluster E** — exceptions. `raise` / `try` / `except` /
   `finally` modeled as path semantics: a `raise` on a feasible
   path either matches a dynamic `except` handler (path continues
   in handler) or escapes (path terminates with a typed-exception
   verdict that propagates through the call stack).
6. **Cluster G** — generics. Walker support for generic procs at
   their **instantiation sites**: each instantiation is symex'd
   as a distinct typed body. `distinct T` becomes a fresh
   uninterpreted Z3 sort with an injection to `T`. Concept
   constraints honored via type-class membership at instantiation
   time.
7. **Cluster C** — closures and procs-as-values. First-class
   procs modeled as uninterpreted Z3 function symbols (one symbol
   per syntactic lambda site); closure environments captured as
   a Z3 record of captured locals. Higher-order DSL targets
   (`filter`, `map`, `fold`) get explicit walker treatment.
8. **Cluster R** — `ref T` and `ptr T` with aliasing.
   Logical-heap model: one `Z3Array[Ref, T]` per pointee-type;
   `Ref` is a Z3 uninterpreted sort; `new T` produces a fresh
   symbolic ref via counter-based freshness; `p[]` is
   `heap[p]`; `p[] = v` rebinds the heap array; aliasing is a
   Z3 equality query the existing path-sat layer answers for
   free. Bounded heap depth via a per-walker recursion-budget
   on cyclic structures.

**Explicitly NOT in scope (deferred to Phase 16+):**

- **GC type erasure** (`RootRef`/`RootObj`-rooted dynamic
  dispatch on inheritance hierarchies). Cluster G covers
  parametric polymorphism; subtype polymorphism is a separate
  modelling problem (vtable encoding) and is deferred.
- **Channels, locks, threads.** Concurrency semantics require a
  separate path model.
- **FFI / `importc` / `emit`.** Out of symex scope by definition —
  external code is opaque.
- **`{.async.}` / CPS-style transforms.** Macro-expanded; if a
  user `async` proc compiles to a closure iterator, Cluster C
  may incidentally cover it, but the surface is not in scope.
- **Style insensitivity / Unicode identifiers.** Lexical, not
  semantic.

## Ordering and rationale

| Order | Cluster | Why this position |
|-------|---------|-------------------|
| 1 | Z | Blocking — F/S clusters use nim-z3 v2.0.0 surfaces (renamed `strings`/`chars`/`arrays` modules; new FP eval extractors). Z also lands the cross-cutting infra (Z3: `SymexErrorKind` enum, `severity` field, `InlinePolicy`, `DefectKind`, `svUninterpRef`, `withSymexSettings`, `char` classification, sink/lent strip; Z4: `WalkCtx.found` field-type change) every subsequent cluster depends on. |
| 2 | L | Verification-shaped; uncovers boundaries that inform F/S design. |
| 3 | F | Smallest type-bridge addition; flips on a Z3 family that's already tested in nim-z3. Cheap precision win. |
| 4 | S | Builds on F's lift-extraction pattern; pulls in regex/sequence theories. |
| 5 | H | **Heap preparation** — promoted from former R0. `Path` extension (`heaps`/`heapDepth`/`allocCounters`) + fork-site audit. Lands before E so E3/E5/E7's heap-state threading compiles. Pure infra; no walker-semantic change; does not bump walker version. |
| 6 | E | Walker control-flow change. Lands before G/C/R add their own control-flow surfaces (proc-call semantics, deref-may-fail). Depends on H (heap-state fields on `Path`). |
| 7 | G | Walker grows an instantiation cache + a type-substitution path. Lands before C so closures can be generic. |
| 8 | C | Uses G's instantiation machinery for generic higher-order procs. |
| 9 | R | Deepest. Lands last so every other cluster's tests serve as regression coverage for the heap-threading change. R cluster starts at R1 (R0 promoted to H1). |

## Cross-cluster invariants

These must hold at the end of every cluster's last cycle:

1. **Walker version bumps per cluster, not mid-cluster.**
   Walker version goes `"4"`→`"5"` atomically at the last
   cycle of Cluster F (F8), `"5"`→`"6"` at S11, `"6"`→`"7"`
   at E7, `"7"`→`"8"` at G10, `"8"`→`"9"` at C6,
   `"9"`→`"10"` at R12. Each cluster ends in a single atomic
   version bump; no mid-cluster bumps. Per-cluster bumps
   eliminate stale-cache risk during the multi-cluster /loop
   session (a Phase 14 cache entry for, e.g., a `float`-typed
   SUT would have been cached as `sxUnknown`/parser-rejected;
   after F1's type-bridge lands the same SUT computes a real
   verdict but the cache key under unchanged walker version
   would silently serve the stale entry). Z, L, H don't bump
   (no walker-semantic change — Z is pin-bump + cross-cutting
   infra; L is verification-only; H is pure `Path`-extension
   prep). **General rule (for Phase 16+):** walker version
   increments by 1 for each cluster that adds new walker arms
   or changes existing walker semantics. Verification-only and
   infra-only clusters don't bump. Phase 16 continues from
   `"10"`.
2. **Rendering version bumps once** — `"2"`→`"3"` atomically
   at R12 when heap-snapshot witness fields land. No other
   cluster touches the on-disk witness format. The witness
   format spec lives in `docs/symex/witness-format-v3.md`,
   authored as part of R11b's DoD (not deferred until R12).
3. **No silent fallback paths.** Every new IR kind (`itRaise`,
   `itDeref`, `itNew`, `iekLambda`, `itClosureCall`, etc.) must
   raise a deterministic, classified `SymexErrorInfo` with
   `severity: sevError` in the walker if its semantic path is
   incomplete — never `sxUnknown` with no `SymexErrorInfo`.
   (Reinforces the standing `inspect-before-pessimizing` rule
   on the reporting side.) **Severity contract (new):**
   `sxUnknown` ⇒ ≥1 `SymexErrorInfo` with
   `severity == sevError` in the finding's `errors` field.
   `sxSat`/`sxUnsat` with non-empty `errors` ⇒ all entries are
   `sevHint` or `sevWarning` (informational annotations on a
   successful verdict — e.g. `hePtrFamily`,
   `geDistinctBijectivitySkipped`).
4. **Per-cluster regression smoke.** Every cluster ends with a
   "regression smoke" cycle that re-runs the prior cluster's
   tests under the new walker state to catch state-threading
   bugs. (Phase 14 lesson: the most expensive bugs were
   shared-module edits that broke earlier-cluster cycles.)
5. **`complete-lib-not-consumer` enforcement.** No cycle is
   allowed to ship with a `# TODO: defer until consumer demand`
   comment. Phase-15 standing-rule check.
6. **Single-source-of-truth version constants.**
   `canonicalize.walkerVersion` and `canonicalize.renderingVersion`
   (formerly `renderAsChoicesVersion`) are defined ONCE in
   `src/proptest/smt/canonicalize.nim`. Every consumer
   (`runtime.nim`, `db.nim`, the witness serializer) imports
   them; no duplicate string literal. Every per-cluster
   closing-cycle DoD edits `canonicalize.nim` (NOT
   `runtime.nim`, NOT `walker.nim`). Corrects the v2 GREEN
   file references.
7. **Per-walker vs per-call-frame state, lifetime-tagged.**
   `WalkerStatics` (immutable post-parse) holds: `refSorts`,
   `nilConsts`, `closureSyms`, `distinctSorts`,
   `userExnHierarchy`, `exnTable`. `CallFrameCtx` (push/pop
   on call descent) holds: `handlerStack`, `inFlightExn`,
   `closureInlineCount`. `WalkCtx` is `{statics: WalkerStatics,
   frame: CallFrameCtx, settings: SymexSettings, errors:
   seq[SymexErrorInfo], found: seq[RawResult]}`. Per-path
   state (`heaps`, `heapDepth`, `allocCounters`) stays on
   `Path` (deep-copied at every fork). No mutable per-walker
   state may sit on `WalkCtx` outside `statics`/`frame`/`errors`/
   `found`. (Replaces the round-1 `EffectCtx` extraction with
   a lifetime-tagged split.)
8. **`withSymexSettings` composition.** The 9-knob
   `SymexSettings` family (`maxFrontierSize`, `maxCallDepth`,
   `maxInstantiationsPerProc`, `maxClosureInlineCount`,
   `maxHeapDepth`, `maxSplitParts`, `maxBytesEncodingLen`,
   `maxFreshnessAssertions`, `inlinePolicy` +
   `seqInlineThreshold` + `defectExclusions`) is exposed via
   `proc withSymexSettings(base = defaultSettings(), f: proc
   (s: var SymexSettings)): SymexSettings` defined in Z3.
   Every cluster's new setting field must be exercised via
   `withSymexSettings` in at least one cycle's RED test to
   confirm override composition works.
9. **Internal-vs-public verdict types.** `InternalVerdict`
   (formerly `WalkResult`) is private to symex internals and
   carries the in-flight handler-stack states (`vrSat`,
   `vrUnsat`, `vrUnknown`, `vrRaised`). `RawResult` is the
   public type returned through `runSymex`. The only allowed
   conversion is `toPublic(iv: InternalVerdict): RawResult`
   called exactly once per finding at the `runSymex`
   boundary. No call site outside `runSymex` constructs a
   `RawResult` from an `InternalVerdict`.

## ADRs introduced by this RFC

Authored as **standalone files** in `docs/symex/` matching ADR-0001..0004
depth (decision, alternatives considered with rejection reasons,
consequences, implementation notes). Each cluster gains an explicit
**ADR-authoring cycle** (F0-ADR, S0-ADR, G0-ADR, C0-ADR; E0-ADR
folds into Z4 since Z4 is the E-prep field-change cycle; R0-ADR
folds into H1 since H1 is the heap-prep cycle) before its first
feature cycle. The cycle's DoD is a checklist (ADR exists at the
canonical path, contains the required sections, summary length
matches ADR-0001..0004). The summaries below are pointers, not
the ADR itself.

### ADR index

| ADR | Title | Governs | Depends on | Authoring cycle | Status |
|-----|-------|---------|------------|-----------------|--------|
| 0005 | Float NaN/Inf semantics | F1–F9 (a/b/c) | — | F0-ADR | pending |
| 0006 | String codepoint vs byte indexing | S1–S11 | — | S0-ADR | pending |
| 0007 | Exception flow model | E1–E8 | ADR-0010 (heap-state visible in finally) | Z4 (folds E0-ADR) | pending |
| 0008 | Generic instantiation policy | G1a–G10 | — | G0-ADR | pending |
| 0009 | Closure environment encoding | C1–C6 | ADR-0008 (signatureHash/symBodyHash convention) | C0-ADR (also authors `closures.md` stub) | pending |
| 0010 | Logical heap model | H1, R1–R13 | — | H1 (folds R0-ADR) | pending |
| `witness-format-v3.md` | Heap-snapshot witness format | R12 | ADR-0010 | R11b DoD | pending |


- **ADR-0005** — float NaN/Inf semantics (Cluster F).
  Decision: `NaN != NaN` honored exactly (Z3 FP theory default);
  `Inf` is a normal value in arithmetic; `nan-payload` not
  modeled (single canonical NaN). Rationale: matches Nim's
  observable float semantics under `-d:release`; payload-distinct
  NaNs would require Z3 FP `to_ieee_bv` round-trips that the user
  cannot observe through any Nim API.
- **ADR-0006** — string codepoint vs byte indexing (Cluster S).
  Decision: codepoint-indexed (Z3 String theory native); byte
  indexing exposed via an explicit `bytes(s)` lift that returns
  a `seq[byte]`. Rationale: Z3 String is codepoint-native;
  matching Nim's UTF-8-as-bytes default invites off-by-Unicode
  bugs the symex would miss. **Lift-layer clarification**:
  `mkString(nimStr)` passes UTF-8 bytes to Z3 via
  `Z3_mk_lstring`; Z3 then interprets the buffer as a codepoint
  sequence, so `mkString("é").len` is `1` (Z3 codepoints), NOT
  `2` (Nim bytes). This is documented divergence from Nim's
  byte-length `s.len`; S2's RED test asserts it explicitly.
  `s.high` and `for c in s` (Nim's byte-iterator default) are
  classified as `seByteIndexUnsupported`/`seByteIterUnsupported`
  — routing them through `bytes(s)` is Phase 16 backlog.
- **ADR-0007** — exception flow model (Cluster E).
  Decision: stack-of-handlers walker state on `EffectCtx`;
  `raise` emits a private `WalkRaised(typeId, msg, witness)`
  intermediate result that propagates up through `Try` frames.
  Only `WalkRaised` that reaches `runSymex`'s top level
  materializes as the public `sxRaised(typeId, msg, witness)`
  verdict — internal walker intermediate states never leak.
  `finally` runs on both normal and raised paths with the same
  heap state visible at finally entry; `inFlightExn` is set on
  handler entry, cleared on handler normal exit, and a bare
  `raise` inside `finally` on a normal (non-raised) path
  produces a fresh `WalkRaised` from the finally body, not a
  classified error. Catches matched against the **dynamic
  exception hierarchy table** (stdlib types from a compile-time
  constant + user-defined types from parse-time `getImpl` walk
  of every `nnkExceptBranch` type sym). Cache key suffix is
  `:raised:<typeId>` (not bare `:raised`). `WalkCtx.found` is
  `seq[RawResult]` so `sxRaised` and `sxSat` accumulate side by
  side. `Defect` modeled as `sxRaised(typeId, isDefect=true)` —
  silent-pass via `sxUnreached` would be unsound for a
  correctness oracle.
- **ADR-0008** — generic instantiation policy (Cluster G).
  Decision: per-call-site monomorphization with a global
  instantiation cache keyed by `(symBodyHash(procSym),
  instTypeTuple)` (body-content hash, not bare name — same-name
  procs across modules don't collide). `ctx.procs` key schema:
  `name#typeargs` for generics, `name` for non-generics.
  `distinct T` becomes a fresh uninterpreted Z3 sort
  (allocated via `Z3_mk_uninterpreted_sort` through `ffi.nim`
  returning `RawZ3Sort`) with both an **injection**
  `inject_T: Base→Distinct` AND **ejection** `eject_T:
  Distinct→Base` function, axiomatized as a bijection.
  Concept conformance for **stdlib type classes**
  (`SomeNumber`, etc.) validated against a compile-time table;
  **user-defined concepts** trust the Nim semchecker (which
  already enforced them at the call site) — no re-validation.
  `maxInstantiationsPerProc = 64` (default; matches
  `maxFrontierSize`/`maxInlineSeqLen` family). Alternatives:
  symbolic generic walking requires a type-variable Z3 theory
  that doesn't exist.
- **ADR-0009** — closure environment encoding (Cluster C).
  Decision: closures encoded as `(funcSym, envRecord)` where
  `funcSym` is a per-(site, envSortId, paramsSortTupleId)
  uninterpreted Z3 function declaration (the sort-tuple
  disambiguates generic-closure instantiations at the same
  syntactic site) and `envRecord` is a Z3 tuple of captured
  locals at closure construction time. Phantom-typed
  `Z3FuncDecl[ArgsTup, Ret]` cannot be instantiated at walk
  time (ArgsTup is compile-time); closure application goes
  through raw `Z3_mk_app` via `ffi.nim`, producing a
  `Z3AnyAst` cast to the typed result via `wrap[T]`.
  Closure equality is **nominal-for-site + structural-for-env**:
  two closures from different sites are unequal regardless of
  environment (matches Nim runtime pointer semantics); two
  closures from the same site are equal iff their `envRecord`s
  are Z3-equal. Closure body `funcSym(env, args) == ret`
  axioms are asserted under path condition
  (`implies(path.pc, funcSym(env,args) == ret)`), not
  unconditionally (prevents cross-path over-constraint).
  `maxClosureInlineCount = 64` setting bounds per-walk closure
  body descents.
- **ADR-0010** — logical heap model (Cluster R).
  Decision: one `Z3Array[Ref_T, T]` per concrete pointee type
  `T`. `Ref_T` is a **per-pointee-type uninterpreted Z3 sort**
  (allocated once per type via `Z3_mk_uninterpreted_sort`
  through `ffi.nim` returning `RawZ3Sort` — not the same sort
  across types; cross-type ref comparisons become Z3 sort
  errors, preventing whole class of false-alias bugs).
  **Heap state is per-`Path`, not per-`WalkCtx`**: `Path`
  carries `heaps: Table[string, Z3AnyAst]`, `heapDepth: int`,
  and `allocCounters: Table[string, int]`. Every fork site in
  the walker must deep-copy these; **R0** (preparatory cycle)
  refactors `Path` to grow these fields and audits all
  existing fork sites for correctness before R1's
  heap-feature work begins. **Inter-procedural threading**:
  every `isCall`/`isGenericCall`/`iekClosureCall` descent
  passes caller `path.heaps` in and merges callee's exit
  `heaps` out — addressed by **R1b**. `new T` returns the
  next address from the per-path monotone counter
  `path.allocCounters[T]`; counter increments are path-local,
  so disjoint paths don't leak freshness assertions into each
  other. `nil` is a sort-level distinguished constant per
  `Ref_T`. Cycles handled via per-path `maxHeapDepth`
  budget; exceeding budget yields `sxUnknown(heDepthExhausted)`.
  `inc(p)`/`dec(p)` pointer arithmetic and `cast[ptr T]`
  → `sxUnknown(hePtrArith)` / `sxUnknown(heUnsafeCast)`.
  Witness rendering version bumps `"2"`→`"3"` to carry
  heap-snapshot serialization; format spec in
  `docs/symex/witness-format-v3.md` (covers aliased refs,
  nil refs, ref groups). Static-analysis points-to
  (Andersen/Steensgaard/region-based) rejected — path-sat
  already answers may-alias precisely.

## Cluster index (v3)

| Cluster | Topic | Cycles | First | Last | Version bump |
|---------|-------|--------|-------|------|--------------|
| Z | nim-z3 v2.0.0 pin + Phase-14 carryover + cross-cutting infra | 5 | Z0 | Z4 | — |
| L | templates / macros | 3 | L1 | L3 | — |
| F | float | 10 | F0-ADR | F8, +F9a/b/c | walker `"4"`→`"5"` at F8 |
| S | full strings | 14 | S0-ADR | S11 (S6a/b split, S7a/b split, S10a/b split) | walker `"5"`→`"6"` at S11 |
| H | heap preparation (`Path` refactor + R0-ADR/ADR-0010) | 1 | H1 | H1 | — |
| E | exceptions | 10 | E1 | E7 (incl. E2a/E2b, E4a, E8; E0-ADR folded into Z4) | walker `"6"`→`"7"` at E7 |
| G | generics | 11 | G0-ADR | G10 (incl. G1a/b/c split; G2/G9 folded into G1c) | walker `"7"`→`"8"` at G10 |
| C | closures + procs-as-values | 8 | C0-ADR | C6 (incl. C2a/C2b split) | walker `"8"`→`"9"` at C6 |
| R | ref/ptr aliasing | 16 | R1a | R13 (R1 split into R1a/R1, R8b var-ref, R11b/R12 split, R13 closure-capturing-ref) | walker `"9"`→`"10"` AND rendering `"2"`→`"3"` at R12 |
| | **Total** | **~78** | | | |

(Cluster ordering is fixed by the rationale table above; cycle
ordering within a cluster is fixed by each cluster's own section.
Cycle counts after v3 bake-in include the structural splits, new
ADR-authoring cycles, the H cluster promotion, R1 split, S6/S10
splits, F9 expansion, and other additions enumerated in the v3
revision-history entry.)

---

<!-- CLUSTER SECTIONS BELOW — populated by per-cluster drafting passes. -->

<!-- CLUSTER_Z -->
## Cluster Z — nim-z3 v2.0.0 preamble

> **Purpose:** bump the nim-z3 pin from v1.0.x to v2.0.0, verify
> proptest is unaffected by the 8 breaking renames, and lay the
> cross-cutting infrastructure (type-system scaffolding, structured
> error types, and field-layout changes) that all language-fragment
> clusters depend on. This cluster lands before any language-fragment
> work (Clusters L–R) because those clusters may surface new nim-z3
> v2 APIs; the pin must be stable first, and the shared types must
> be in place before any cluster authors RED tests.
>
> **Standing rules:**
> - PhD-CS bar; no external consumers; interface breaks are free.
> - Every cycle is independently testable.
> - No silent fallback paths (RFC-phase15 invariant 3).
> - Per-cluster regression smoke is mandatory (RFC-phase15 invariant 4)
>   — Z2 fulfils this for Cluster Z.
>
> **Walker version:** Cluster Z does **not** bump the walker version.
> Walker version stays at `"4"` (set in Phase 14) throughout Z0–Z4.
> The next version bump belongs to whichever language-fragment cluster
> first adds new walker arms. Z3 and Z4 are infrastructure — they add
> types, field layouts, and plan documents, none of which alters what
> the walker computes from a given IR.
>
> **Verification policy (v2 grep):** Z1's DoD requires an automated grep
> asserting zero matches for each of the 8 v1 symbol names in both
> `src/` and `tests/`. The 8 names are: `toInt\b`, `strToInt`,
> `intToStr`, `mkNaN\b`, `mkInf\b`, `mkZero\b`, `toFp(`, `mkRegexAll\b`.
> The commit message must include a line of the form
> `grep-verified: 0 matches for all 8 v1 names in src/ and tests/`.
>
> **Out of scope for this cluster:**
> - Walker-semantic changes (new IR nodes, new `SVKind` variants with
>   substantive logic). Z3 adds `svUninterpRef` stubs only; no walker
>   behaviour changes.
> - Any language-fragment test (float, string, exception, generic,
>   closure, ref/ptr). Cluster Z owns infra only.
> - Walker version bumps (see note above).

| Cycle | Topic | Key dependency |
|-------|-------|----------------|
| Z0 | Phase 14 carryover close-out | — (this is the prerequisite) |
| Z1 | nim-z3 v2.0.0 pin bump + grep verification | Z0 |
| Z2 | regression smoke | Z1 |
| Z3 | cross-cutting infrastructure (enums, types, plan doc) | Z2 |
| Z4 | `WalkCtx.found` field-type change + ADR-0007 | Z3 |

---

### Z0 — Phase 14 carryover close-out

**What it does:** Closes two Phase 14 loose ends that must land before
any language-fragment cluster can safely use multi-type strategies or
rely on cache-key correctness:

1. **B4 (named-field tuple strategies):** The `tupleOf` macro currently
   errors at compile time when the tuple has named fields (e.g.,
   `tupleOf(x: int, y: string)`). This blocks C4 and G8, which compose
   multi-type strategies over named-field tuples. Fix: extend the macro's
   field-extraction branch to handle `nnkIdentDefs` nodes with explicit
   field names, generating the correct `map(sa, sb, ...)` call.

2. **`constraintDigest` population:** Five existing strategies ship with
   `constraintDigest = ""`: `floats`, `strings`, `lists`, `tables`,
   `sets`. A blank digest means every variant of these strategies
   (e.g., `floats(-1.0, 1.0)` vs `floats(0.0, 100.0)`) produces the
   same cache key, causing cross-variant cache collisions in the F and S
   clusters. Fix: each strategy must compute its digest from its
   bounding/configuration parameters at construction time, following the
   same pattern already used by `ints` and `booleans`.

3. **`:unk` suffix migration acknowledgement:** Any cached verdict entries
   written with the legacy `:unk` suffix (pre-Phase 13 naming) must be
   marked for skip-load. The full suffix standardisation
   (`":unk"` → `":unknown"`) happens at the same time as the next
   walker version bump; Z0 only documents the migration and adds a
   skip-load guard so stale `:unk` entries do not pollute Phase 15 runs.

**RED test:** `tests/tsymex_phase15_z0_carryover.nim`, two named tests:
- `"z0 B4: named-field tupleOf compiles and generates correct strategy"` —
  calls `tupleOf(x: int, y: string)` and asserts the resulting strategy
  produces `(int, string)` pairs without a compile-time error.
- `"z0 constraintDigest: floats/strings/lists/tables/sets have non-empty digest"` —
  constructs one variant of each strategy and asserts
  `s.constraintDigest != ""`.

**GREEN:**

- `src/proptest/strategies/tuples.nim` — extend the macro to handle
  named-field `nnkIdentDefs` nodes.
- `src/proptest/strategies/floats.nim`, `strings.nim`, `lists.nim`,
  `tables.nim`, `sets.nim` — populate `constraintDigest` from
  constructor parameters.
- `src/proptest/smt/db.nim` — add skip-load guard: entries whose cache
  key ends with `:unk` are silently ignored on load (not an error; they
  are stale pre-Phase-13 writes). Document the guard in a
  `## :unk migration` comment.
- `tests/tsymex_phase15_z0_carryover.nim` — new test file (the RED file,
  now made GREEN).

**DoD:**
- [ ] Both RED tests pass `nim c -r` and `nim cpp -r`
- [ ] `tupleOf(x: int, y: string)` compiles without error in a fresh
  `nim c --path:src` invocation
- [ ] All five strategies have `constraintDigest != ""` for at least two
  distinct parameterisations each (verified by the test)
- [ ] `:unk` skip-load guard present and covered by a test assertion that
  a DB loaded with a `:unk` entry does not surface it as a verdict hit
- [ ] `docs/symex/SYMEX_PLAN.md` Z0 row marked SHIPPED with commit SHA

---

### Z1 — pin bump + import-rename sweep

**What it does:** Updates the nim-z3 version pin from `1.0.0` to `2.0.0`
in `milpa.kdl` and `milpa.lock`, then does a full-source grep confirming
none of the 8 v2 breaking renames (`toInt` → `toInt64`; `strToInt` →
`Z3String.toInt`; `intToStr` → `Z3Int.toStr`; `mkNaN` → `mkFpNaN`;
`mkInf` → `mkFpInf`; `mkZero` → `mkFpZero`; `toFp(bv,_)` →
`bvToFpBits`; `mkRegexAll` → `mkRegexAllChar`) appear in proptest source.
Per the nim-z3 MIGRATION-1.x-to-2.0.md "Proptest sync note", the Lens 4
grep at the 2.0.0 tag confirmed none of the renamed symbols exist in
proptest's tree — so the full migration delta is a single pin-bump with no
source edits.

**RED test:** `tests/tsymex_phase15_z1_canary.nim`, test name
`"z3 v2 canary: Z3StringSort construction compiles and round-trips"`.
Specifies: imports `z3` (the bumped dependency), constructs a
`Z3StringSort` via `sortOf[Z3String]()`, and asserts that
`$sort == "String"` — a smoke value confirming the new shared library
loaded correctly and the sort-printer is intact under the new pin.
The test must not import any of the 8 renamed symbols (the OLD names);
it must compile cleanly, proving that none of the renames are lurking
as stale references in proptest's transitive build.

**GREEN:**

- `milpa.kdl` — update `"z3"` dep entry: change `local=…` to a version
  pin `git=(url)"…" ref="v2.0.0"`, or if kept as a local path, update
  the nim-z3 checkout to the `v2.0.0` tag. The lock file (`milpa.lock`)
  is regenerated by `milpa lock` after the edit; the `dep "z3"` stanza
  gains `version "2.0.0"` and an updated `identity` hash.

- No source files under `src/proptest/smt/` require edits. The only
  nim-z3 import in the smt layer is `import z3` in
  `src/proptest/smt/runtime.nim` (umbrella import — unaffected by the
  submodule renames because proptest never imported `z3/string`,
  `z3/char`, or `z3/array` directly).

- `tests/tsymex_phase15_z1_canary.nim` — new test file (the RED file,
  now made GREEN).

**DoD:**
- [ ] `tests/tsymex_phase15_z1_canary.nim` passes `nim c -r` and
  `nim cpp -r` (both backends, `--hints:off --path:src`)
- [ ] `nim c` of `src/proptest/smt/runtime.nim` succeeds against the
  new pin with no `undeclared identifier` errors
- [ ] `milpa.lock` `dep "z3"` stanza shows `version "2.0.0"`
- [ ] Automated grep confirms zero matches for all 8 v1 symbol names
  (`toInt\b`, `strToInt`, `intToStr`, `mkNaN\b`, `mkInf\b`, `mkZero\b`,
  `toFp(`, `mkRegexAll\b`) in both `src/` and `tests/`; the commit
  message includes the line
  `grep-verified: 0 matches for all 8 v1 names in src/ and tests/`
- [ ] `docs/symex/SYMEX_PLAN.md` Z1 row marked SHIPPED with commit SHA

---

### Z2 — regression smoke under new pin

**What it does:** Re-runs a curated subset of existing symex tests
against the v2.0.0 pin to confirm no behaviour drift from the 8 renames
or from the ancillary v2 changes (model enumeration surface,
`Z3Error`-subclass hierarchy, `Z3Int.toInt64` return-type change). If all
selected tests pass without source changes, this cycle closes with a
green checkmark and no code delta — it is a verification-only cycle, not
a TDD slice.

**RED test:** `tests/tsymex_phase15_z2_regression.nim`, test name
`"z2 regression driver: curated symex subset passes under nim-z3 v2.0.0"`.
Specifies: the test file is a thin Nim runner that `exec`s (at compile
time via `gorge`) or delegates to `testament` the following curated subset
and asserts the exit code is 0 for each:

```
tsymex_phase1_arith          # Z3Int / Z3Bool fundamentals
tsymex_phase1_bool
tsymex_phase2_bv_arith       # Z3BitVec — affected by toInt64 rename if used
tsymex_phase2_overflow
tsymex_phase5_seq            # Z3Seq / Z3String baseline
tsymex_phase14_c4_z3error    # Z3Error catch hierarchy — v2 adds Z3MemoryError
tsymex_phase14_multivariant_walker  # deepest walker path; exercises solve
tsymex_phase13_acceptunknown_guard  # rlimit + verdict caching
```

The selection covers: integer arithmetic (toInt64 rename zone), BV
arithmetic, string/seq (strToInt / intToStr rename zone), the Z3Error
catch hierarchy (v2 adds `Z3MemoryError` / `Z3InternalError` as named
subclasses), the deepest walker path, and verdict-cache behaviour.

**GREEN:** No source changes expected. If a test fails, the failing test
identifies which v2 API surface caused drift and the fix lands in Z2 (not
a new cycle). Document any fix in a `## Z2 drift log` section appended to
this file.

**DoD:**
- [ ] All 8 curated tests pass `nim c -r --hints:off --path:src` under
  the v2.0.0 pin
- [ ] All 8 curated tests also pass `nim cpp -r` (cpp backend parity)
- [ ] `tests/tsymex_phase15_z2_regression.nim` is committed and listed in
  `proptest.nimble`'s test task
- [ ] Zero unresolved `undeclared identifier` or type-mismatch errors
  attributable to the pin bump (any residual errors are pre-existing and
  documented)
- [ ] `docs/symex/SYMEX_PLAN.md` Z2 row marked SHIPPED with commit SHA;
  Cluster Z summary line reads "pin bump complete, 0 drift findings" (or
  lists findings if any were found and fixed)
- [ ] **Z2 regression smoke (enum + severity):** after Z3 lands, re-run
  the 8 curated tests to confirm `SymexErrorKind` enum migration and the
  new `severity` field do not regress Phase-14 cached verdicts — all
  8 tests must still produce identical `fromCache: true` hits as before
  the enum introduction; no verdict key collision or deserialization
  failure introduced by the new field.

---

### Z3 — cross-cutting infrastructure

**What it does:** Introduces the shared type scaffolding that all Phase-15
language-fragment clusters depend on. Every RED test in Clusters F–R
references enum variants, severity values, or settings builders that must
exist before those clusters compile. Z3 is a pure infrastructure slice:
no walker behaviour changes; no new language fragment coverage; no walker
version bump.

Eight changes land together because they are mutually referential (e.g.,
`SymexErrorInfo.kind` cannot become `SymexErrorKind` until the enum exists,
and `DefectKind` fields reference `SymexSettings` which references
`SymexErrorKind` in its diagnostic surface):

1. **`SymexErrorKind` enum** — replaces `SymexErrorInfo.kind: string`.
2. **`SymexErrorInfo.severity` field** — typed `SymexErrorSeverity`.
3. **`DefectKind` enum + `SymexSettings.defectExclusions`** field.
4. **`InlinePolicy` enum** moved here from C4; exported.
5. **`svUninterpRef` SVKind variant** — dispatch stubs in every `case sv.kind`.
6. **`classifyType` additions** — `char` branch and `sink T`/`lent T` strip.
7. **`withSymexSettings` builder + `+` merge combinator** on public API.
8. **`cacheKeyRaised(typeId)` proc** + version constants documented.

Additionally, **`docs/symex/SYMEX_PLAN.md`** is authored in this cycle.

#### `SymexErrorKind` enum

The current `SymexErrorInfo.kind: string` field holds free-form strings
(Phase 14's only site is `kind: $e.name` for caught `Z3Error` subclasses).
The enum replaces this with a closed set of declared variants, making
error-kind exhaustive matching available at compile time and enabling
`nim doc` discoverability.

**Phase-14 kinds** (pulled from existing `Z3Error`-subclass naming
convention in `runtime.nim`; the strings were `$e.name` — class names):

```
ekZ3Error            ## bare Z3Error (no named subclass)
ekZ3MemoryError      ## Z3MemoryError subclass (nim-z3 v2+)
ekZ3InternalError    ## Z3InternalError subclass (nim-z3 v2+)
ekZ3SolverError      ## Z3SolverError subclass
```

**Phase-15 front-end / classification kinds** (`fe` prefix = front-end
parser / classify phase; `se` = string/seq encoding; `ee` = exception
engine; `ge` = generics engine; `ce` = closure engine; `he` = heap /
ref engine):

```
feUnsupportedOp              ## unclassified / catch-all for unsupported AST ops
seUnsupportedStringOp        ## string op not in the supported fragment
seUnsupportedRegex           ## regex construct not translatable to Z3
seZ3StringIncomplete         ## Z3 string theory incomplete for this query
seBytesSymbolicLength        ## bytes(s) called with symbolic s length
seBytesLengthTooLarge        ## bytes(s) length > maxBytesEncodingLen
seByteIndexUnsupported       ## byte index out of supported Z3 model
seByteIterUnsupported        ## byte iteration not supported
seUnsupportedTableValType    ## Table[K,V] where V not in {int,bool,string}
seUnsupportedSetCharInterop  ## s[i] in set[char] codepoint/BV8 mismatch
seNestedSeqUnsupported       ## seq[seq[T]] — nested seq not yet modeled
eeUninterpRefExtraction      ## getCurrentException() fields not modeled symbolically
geInstantiationCapped        ## generic instantiation depth cap hit
geConceptViolation           ## concept constraint check failed during symex
geUnresolvedGeneric          ## unresolved type variable at walk time
geDistinctBijectivitySkipped ## bijectivity axiom skipped for FP/String base type
ceNotImplemented             ## closure feature not yet implemented
ceUnsupportedCapture         ## capture variable type not supported
ceUnsupportedHof             ## higher-order function (filter/map/fold) deferred
heDepthExhausted             ## maxCallDepth / maxHeapDepth exceeded
heUnsafeCast                 ## unsafe cast expression encountered
hePtrArith                   ## pointer arithmetic not modeled
hePtrFamily                  ## ptr T / UncheckedArray — pointer family, not heap
heFreshnessCapExceeded       ## maxFreshnessAssertions cap hit
heUnsupportedVarRef          ## var ref T rebinding not modeled
heRefVariantUnsupported      ## ref object with inheritance variant — unmodeled
heUnsupportedOwnership       ## owned T / WeakRef / Atomic[T]
```

Declaration in `types.nim` immediately before `SymexErrorInfo`:

```nim
type
  SymexErrorSeverity* = enum
    sevHint     ## classified hint — informational; does NOT force sxUnknown
    sevWarning  ## non-fatal issue; walker continues; verdict may be valid
    sevError    ## halting error — causes sxUnknown result

  SymexErrorKind* = enum
    ekZ3Error, ekZ3MemoryError, ekZ3InternalError, ekZ3SolverError,
    feUnsupportedOp,
    seUnsupportedStringOp, seUnsupportedRegex, seZ3StringIncomplete,
    seBytesSymbolicLength, seBytesLengthTooLarge,
    seByteIndexUnsupported, seByteIterUnsupported,
    seUnsupportedTableValType, seUnsupportedSetCharInterop,
    seNestedSeqUnsupported,
    eeUninterpRefExtraction,
    geInstantiationCapped, geConceptViolation, geUnresolvedGeneric,
    geDistinctBijectivitySkipped,
    ceNotImplemented, ceUnsupportedCapture, ceUnsupportedHof,
    heDepthExhausted, heUnsafeCast, hePtrArith, hePtrFamily,
    heFreshnessCapExceeded, heUnsupportedVarRef, heRefVariantUnsupported,
    heUnsupportedOwnership

  SymexErrorInfo* = object
    kind*:     SymexErrorKind
    severity*: SymexErrorSeverity
    msg*:      string
```

**Default severity assignments:**
- All new Phase-15 sites: `sevError` unless listed below.
- `hePtrFamily`: `sevHint` (pointer-family observation; walker continues
  on non-heap-path code).
- `geDistinctBijectivitySkipped`: `sevHint` (axiom elided, not an error;
  walker continues).
- `eeUninterpRefExtraction`: `sevHint` (exception-object fields unmodeled
  symbolically; classified, not a halt — see `svUninterpRef` below).

**Invariant 7 contract** (cross-cluster, registered in the invariants
section):
> A `RawResult` with `status = sxUnknown` must carry at least one
> `SymexErrorInfo` entry with `severity = sevError`. Conversely, a result
> whose `errors` seq contains only `sevHint` / `sevWarning` entries must
> not be `sxUnknown` — it must resolve to `sxSat` or `sxUnsat`.

#### `DefectKind` enum + `SymexSettings.defectExclusions`

```nim
type
  DefectKind* = enum
    dkAssertionDefect    ## assert / doAssert / raiseAssert
    dkIndexDefect        ## array/seq out-of-bounds
    dkFieldDefect        ## object field access on wrong variant
    dkRangeDefect        ## range constraint violation
    dkOutOfMemoryDefect  ## allocation failure
    dkStackOverflowDefect
    dkOther              ## user-defined defect types
```

Added to `SymexSettings`:

```nim
defectExclusions*: set[DefectKind]
  ## Defect types that the walker should NOT model as raise-paths.
  ## Default excludes dkOutOfMemoryDefect + dkStackOverflowDefect
  ## (modelling alloc failure and stack overflow produces spurious
  ## sxRaised results for virtually all real SUTs). Set to {} to
  ## model all defects; add dkAssertionDefect to skip assert
  ## instrumentation.
```

`defaultSymexSettings()` initialises:
```nim
defectExclusions: {dkOutOfMemoryDefect, dkStackOverflowDefect}
```

#### `InlinePolicy` enum (moved from C4)

```nim
type
  InlinePolicy* = enum
    ipAlwaysInline      ## walk body for every call site (no axiom)
    ipAlwaysAxiomatize  ## emit summary axiom; never walk body
    ipHybrid            ## walk up to seqInlineThreshold times, then axiomatize
```

Moved here so `SymexSettings.inlinePolicy: InlinePolicy` is resolvable
at Z3 time, before Cluster C is open. `seqInlineThreshold` is documented
as only meaningful under `ipHybrid`. Cluster C4 still owns the axiom
construction logic; the type definition moves to `types.nim` alongside
`SymexSettings`.

#### `svUninterpRef(sortName, typeTag)` SVKind variant

Added to the `SVKind` enum in `types.nim`:

```nim
svUninterpRef  ## uninterpreted reference sort; fields not modeled symbolically
```

The variant carries `sortName: string` (the Z3 uninterpreted-sort name,
e.g. `"ExnRef_ValueError"`) and `typeTag: string` (Nim type name for
diagnostic messages).

**Stub arms required in every `case sv.kind` dispatch:**

| Proc | Stub behaviour |
|------|----------------|
| `walk` | emit `isUnsupported("svUninterpRef: fields not walked")` |
| `extractFromSymVal` | emit `SymexErrorInfo{kind: eeUninterpRefExtraction, severity: sevHint, msg: "exception object fields not modeled symbolically"}`; return `none(T)` |
| `allocateSym` | call `ctx.mkFreshConst(sortName)` using the uninterpreted sort; return the resulting `SymVal` |
| `typeOf` | return `tUninterp(sortName)` (new `IRType` variant; see below) |
| `symValHash` | `hash(sv.sortName) !& hash(sv.typeTag)` |
| `iteSymVal` | delegate to `Z3_mk_ite` on the underlying Z3 `AST` — uninterpreted sort supports `ite` |
| `svEq` | `mkEq(a.uninterpAst, b.uninterpAst)` |

`tUninterp(name: string): IRType` is also new; add to `IRType` enum with
no additional walker dispatch changes needed at this cycle.

Note: `extractFromSymVal(svUninterpRef)` is the mechanism by which E8's
`getCurrentExceptionMsg()` will return an empty string model rather than
crashing. The `sevHint` severity means the result is `sxSat` (with the
stub witness), not `sxUnknown`.

#### `classifyType` additions

Two additions to `dsl_typebridge.nim`'s `classifyType` proc:

1. **`char` branch:**
   ```nim
   of "char": unranged(tInt(8, signed = false))
   ```
   `char` in Nim is an 8-bit unsigned integer (`uint8`). Symex models it
   identically to `uint8`. This closes `Breadth-MED-M24` and unblocks
   string-related SUTs that use `char` locals.

2. **`sink T` / `lent T` strip:**
   ```nim
   if impl.kind in {nnkSinkTy, nnkLentTy}:
     return classifyType(impl[0], ctx)
   ```
   Applied at the top of `classifyType`, before the `typeKind` switch.
   `sink T` and `lent T` are ownership annotations; symex is by-value, so
   both are transparently treated as `T`. Closes `Breadth-HIGH-H26`.

Both additions are documented in a `## determinism.md ref: classifyType
extensions (Phase 15 Z3)` comment block.

#### `withSymexSettings` builder + `+` merge combinator

Added to the public API surface (`src/proptest/smt/runtime.nim` or a new
`src/proptest/smt/settings.nim` — whichever the GREEN plan specifies):

```nim
proc withSymexSettings*(base = defaultSymexSettings(),
                        f: proc(s: var SymexSettings) {.closure.}
                       ): SymexSettings =
  result = base
  f(result)

proc `+`*(a, b: SymexSettings): SymexSettings =
  ## Merge: b's non-default fields override a's. Fields that equal
  ## defaultSymexSettings() in b are taken from a.
  ## Useful for composing per-cluster overrides.
  result = a
  let d = defaultSymexSettings()
  if b.integerSemantics != d.integerSemantics: result.integerSemantics = b.integerSemantics
  if b.queryRLimit != d.queryRLimit: result.queryRLimit = b.queryRLimit
  if b.maxFrontierSize != d.maxFrontierSize: result.maxFrontierSize = b.maxFrontierSize
  if b.maxCallDepth != d.maxCallDepth: result.maxCallDepth = b.maxCallDepth
  if b.maxLoopUnwind != d.maxLoopUnwind: result.maxLoopUnwind = b.maxLoopUnwind
  if b.acceptUnknownAsCovered != d.acceptUnknownAsCovered:
    result.acceptUnknownAsCovered = b.acceptUnknownAsCovered
  if b.defectExclusions != d.defectExclusions: result.defectExclusions = b.defectExclusions
  if b.inlinePolicy != d.inlinePolicy: result.inlinePolicy = b.inlinePolicy
```

Usage pattern (documented in cross-cluster section, used in Z4 DoD test):
```nim
let s = withSymexSettings() do (s: var SymexSettings):
  s.maxFrontierSize = 1
  s.defectExclusions = {}
```

#### `cacheKeyRaised` proc + version constant documentation

In `canonicalize.nim`, replace the bare `cacheKeyRaisedSuffix` constant
(if it exists) with a proc:

```nim
proc cacheKeyRaised*(typeId: string): string =
  ## Cache key for a sxRaised finding with the given exception type ID.
  ## Example: cacheKeyRaised("ValueError") == ":raised:ValueError"
  ":raised:" & typeId
```

The three atomic suffix constants remain:
```nim
const
  cacheKeySat*     = ":sat"
  cacheKeyUnsat*   = ":unsat"
  cacheKeyUnknown* = ":unknown"
```

Note: the current code uses `cacheKeySatSuffix`, `cacheKeyUnsatSuffix`,
`cacheKeyUnkSuffix`. The `:unk` to `:unknown` rename aligns with Phase 13's
`sfUnknown`/`sxUnknown` standardization; the old `cacheKeyUnkSuffix`
constant is removed, replaced by `cacheKeyUnknown`. Callers are updated
in this cycle.

**Walker/rendering version constants — single source of truth:**
`canonicalize.nim` already holds `symexWalkerVersion* = "4"` and
`renderAsChoicesVersion* = "2"`. This cycle adds an inline documentation
block:
```nim
## Walker-version invariant (cross-cluster invariant 6):
## canonicalize.nim is the single source of truth for both version
## constants. runtime.nim and db.nim import them — they do NOT
## declare their own string literals. Any cluster that bumps walker
## semantics edits symexWalkerVersion here. The witness serializer
## imports renderAsChoicesVersion from this module.
```
Any per-cluster GREEN file reference to `runtime.nim` or `walker.nim`
as the home of these constants must be corrected to `canonicalize.nim`
(closes `Breadth-MED-M12` / `Feas-LOW-4`).

#### `SYMEX_PLAN.md` authoring

`docs/symex/SYMEX_PLAN.md` is created in this cycle with the 78-row
cycle table (one row per Phase-15 cycle across all clusters). Schema:

```
| cluster | cycle | status  | commit |
|---------|-------|---------|--------|
| Z       | Z0    | pending |        |
| Z       | Z1    | pending |        |
...
```

All rows pre-filled `pending` with empty commit. Z0 row becomes the
first candidate to flip to `SHIPPED` once Z0 lands (Z0 DoD already
requires this). The 78-row count covers Z0-Z4 (5), L1-L3 (3), F1-F9c
(~12), S1-S11 (11), H1 (1), E1-E8 (8), G1-G8 (8+), C1-C5 (5+), R1-R13
(13+), plus ADR doc cycles — total approximately 78. A `## Documentation
index` section is appended at the bottom (closes `Des-LOW-L2`).

---

**RED test:** `tests/tsymex_phase15_z3_infra.nim`, three named tests:

1. `"z3 infra: SymexErrorInfo.kind is SymexErrorKind (compile-time type
   check)"` — calls `discard SymexErrorInfo(kind: feUnsupportedOp,
   severity: sevError, msg: "test")` and asserts the field types match
   the enum declarations. Uses `static: doAssert typeof(SymexErrorInfo.kind)
   is SymexErrorKind`.

2. `"z3 infra: severity sevError invariant — sxUnknown implies sevError"` —
   constructs a `RawResult` with `status = sxUnknown` and `errors = @[
   SymexErrorInfo(kind: feUnsupportedOp, severity: sevHint)]` and asserts
   a helper proc `checkInvariant7(r)` returns `false` (invariant 7
   violation is detectable). Then constructs one with `severity = sevError`
   and asserts `checkInvariant7` returns `true`.

3. `"z3 infra: enum-vs-string round-trip — SymexErrorKind has stable ordinals"` —
   asserts `ord(feUnsupportedOp) > ord(ekZ3SolverError)` (Phase-15 kinds
   follow Phase-14 kinds), and `$heDepthExhausted == "heDepthExhausted"`
   (Nim's default `$enum` uses the variant name).

**GREEN:**

- `src/proptest/smt/types.nim` — add `SymexErrorSeverity`, `SymexErrorKind`,
  `DefectKind` enums; migrate `SymexErrorInfo.kind: string` to `SymexErrorKind`;
  add `severity: SymexErrorSeverity` field; add `defectExclusions:
  set[DefectKind]` to `SymexSettings`; move `InlinePolicy` definition
  here; add `svUninterpRef` to `SVKind`; add `tUninterp` to `IRType`;
  update `defaultSymexSettings()` to initialise `defectExclusions`.
- `src/proptest/smt/dsl_typebridge.nim` — add `char` branch and
  `nnkSinkTy`/`nnkLentTy` strip to `classifyType`.
- `src/proptest/smt/runtime.nim` — add `svUninterpRef` arms to every
  `case sv.kind` dispatch (`walk`, `extractFromSymVal`, `allocateSym`,
  `typeOf`, `symValHash`, `iteSymVal`, `svEq`); migrate existing
  `SymexErrorInfo(kind: $e.name, ...)` site to use the enum
  (`ekZ3MemoryError` etc.); add `withSymexSettings` builder and `+`
  combinator.
- `src/proptest/smt/canonicalize.nim` — add `cacheKeyRaised` proc;
  rename `cacheKeyUnkSuffix` to `cacheKeyUnknown`; rename
  `cacheKeySatSuffix` to `cacheKeySat`, `cacheKeyUnsatSuffix` to
  `cacheKeyUnsat`; add walker/rendering version documentation comment.
- `src/proptest/smt/db.nim` — update callers of renamed suffix constants.
- `docs/symex/SYMEX_PLAN.md` — new file; 78-row cycle table; all rows
  `pending`.
- `tests/tsymex_phase15_z3_infra.nim` — new test file (the RED file,
  now made GREEN).

**DoD:**
- [ ] All three RED tests pass `nim c -r` and `nim cpp -r`
- [ ] `typeof(SymexErrorInfo.kind) is SymexErrorKind` holds at compile time
- [ ] `typeof(SymexErrorInfo.severity) is SymexErrorSeverity` holds at
  compile time
- [ ] All 32 `SymexErrorKind` variants declared and visible via `nim doc`
  (4 Phase-14 kinds + 28 Phase-15 kinds)
- [ ] `SymexSettings.defectExclusions` defaults to
  `{dkOutOfMemoryDefect, dkStackOverflowDefect}` (verified by test)
- [ ] `InlinePolicy` exported from `types.nim`; `import proptest/smt/types`
  resolves `ipHybrid` without further qualification
- [ ] `svUninterpRef` arm present in every `case sv.kind` dispatch (grep
  confirms: `grep -c 'svUninterpRef' src/proptest/smt/runtime.nim` >= 7)
- [ ] `classifyType` handles `"char"` and strips `nnkSinkTy`/`nnkLentTy`
  (verified by a test or `nim c --eval` exercising `charType`)
- [ ] `cacheKeyRaised("ValueError") == ":raised:ValueError"` (test assertion)
- [ ] `cacheKeySat == ":sat"`, `cacheKeyUnsat == ":unsat"`,
  `cacheKeyUnknown == ":unknown"` (old `cacheKeyUnkSuffix` constant removed)
- [ ] `canonicalize.nim` carries the walker/rendering version documentation
  comment; no other file declares these as string literals
- [ ] `withSymexSettings` compiles and produces correct field override
  (exercised by Z4's DoD test; Z3 can stub the call with a trivial assertion)
- [ ] `docs/symex/SYMEX_PLAN.md` exists with >= 78 rows; Z3 row marked
  SHIPPED with commit SHA after this cycle closes
- [ ] Full `nimble test` green (enum migration is backward-compatible at
  value level — existing string-based comparisons replaced by enum comparisons)
- [ ] **Z2 regression smoke passes post-migration**: the 8 curated Z2 tests
  still produce identical verdicts with `fromCache: true` where applicable;
  no verdict key collision introduced by the `cacheKeyUnknown` rename

---

### Z4 — `WalkCtx.found` field-type change + ADR-0007

**What it does:** Extracts the `WalkCtx.found: Option[RawResult]` to
`seq[RawResult]` field-type change out of E2a (per Feas-H9 in the round-2
findings). E2a was burdened with simultaneously changing the field type,
updating all `w.found` sites, rewriting `shouldStop` semantics, AND adding
the structural `sxRaised` cascade. That is too many concerns in one TDD
slice. Z4 lands only the structural change so E2a can focus purely on the
exception cascade.

Additionally, Z4 lands the `EffectCtx` to `WalkerStatics + CallFrameCtx`
field rename on `WalkCtx` (structural split — initial empty records suffice
here; the fields are populated in their respective clusters E1, C2a, R1).
This rename is a CRIT finding (Des-CRIT-D1 / round-2 C6): the split is
the structural change, not the population of fields.

Finally, Z4 authors **ADR-0007 (exception flow model)** — folded from the
E0-ADR doc-authoring cycle (H14) so it co-locates with the `sxRaised`
infrastructure that motivates it.

#### `WalkCtx.found` field-type change

Current type: `found: Option[RawResult]`
New type: `found: seq[RawResult]`

**`shouldStop` semantics rewrite:**

Old (single-result): `w.found.isSome`
New (multi-result):
```nim
proc shouldStop(w: WalkCtx): bool =
  w.found.len > 0 and w.found.anyIt(it.status in {sxSat, sxRaised})
```
This preserves the first-finding short-circuit: once a satisfying or
exception-raising path is found, the walker stops exploring further.
An `sxUnknown` finding alone does not stop the walk (the walker may
find a SAT path on a different branch). An `sxUnsat` finding alone
also does not stop the walk.

**All `w.found` sites rewritten:**

| Old pattern | New pattern |
|-------------|-------------|
| `w.found.isSome` | `w.found.len > 0` |
| `w.found.get` | `w.found[0]` (primary result) or iterate `w.found` |
| `w.found = some(r)` | `w.found.add(r)` |

Note: after Z4, `w.found` may contain multiple entries only if multiple
`sxUnknown` results accumulate before a `sxSat` or `sxRaised` is found.
E2a will build on this by producing one `sxRaised` entry per distinct
exception type path.

#### `EffectCtx` split to `WalkerStatics + CallFrameCtx`

`WalkCtx` gains two fields; `effects` is removed:

```nim
WalkCtx* = object
  # ... existing fields ...
  statics*: WalkerStatics    ## per-walker, immutable post-parse
  frame*:   CallFrameCtx     ## pushed/popped per call descent
  # effects field removed
```

Initial (Z4) definitions — empty records sufficient for compilation:

```nim
WalkerStatics* = object
  ## Populated by E1 (userExnHierarchy), C2a (closureSyms),
  ## R1 (refSorts, nilConsts, distinctSorts).
  ## Immutable after the first call to runSymex.

CallFrameCtx* = object
  ## Populated by E1 (handlerStack, inFlightExn),
  ## C2a (closureInlineCount).
  ## Push/pop protocol spec'd in E1 and C2a.
```

The full field populations land in Clusters E, C, and R respectively.
Z4 only introduces the types and the `WalkCtx` field rename so that
E1's GREEN file list can reference `WalkCtx.statics.userExnHierarchy`
without a forward-reference problem.

All `w.effects` sites in `runtime.nim` are rewritten to `w.statics` or
`w.frame` as appropriate:
- `refSorts`, `closureSyms`, `userExnHierarchy`, `distinctSorts`,
  `exnTable` become `w.statics.*`
- `handlerStack`, `inFlightExn`, `closureInlineCount` become `w.frame.*`

#### ADR-0007 (exception flow model)

Path: `docs/symex/ADR-0007-exception-flow.md`

Must match ADR-0001..0004 depth. Required sections:

- **Context:** why exception flow modeling in a symbolic executor is
  non-trivial; the `WalkRaised` internal result type; the multi-path
  problem (a SUT may raise from multiple callsites under different path
  conditions); Phase 14's single-finding limitation.
- **Decision:** `WalkCtx.found` holds `seq[RawResult]`; `shouldStop`
  halts on first `sxSat`/`sxRaised`; each distinct `(exnType, pathCond)`
  pair is a separate `sxRaised` entry; cache serialization writes one
  entry per `":raised:" & typeId` key.
- **Alternatives considered:**
  - Keep `Option[RawResult]` and extend to `(sat: Option, raised: seq)` —
    rejected: two parallel sequences with different stop semantics increase
    `shouldStop` complexity and diverge from the unified `seq[RawResult]`
    shape E2a needs.
  - Model exception flow purely axiomatically (never walk exception paths) —
    rejected: soundness gap; user SUTs that propagate `raise` through
    intermediate procs would silently become `sxUnsat`.
  - Use a separate `raisedFindings: seq[RawResult]` field in `WalkCtx` in
    addition to `found` — rejected: same issue as first alternative;
    `shouldStop` must reason about both.
- **Consequences:**
  - E2a becomes a pure cascade addition (no field-type change needed).
  - `shouldStop` has two conditions: `sxSat` halts (witness found);
    `sxRaised` halts (defect/exception found); `sxUnknown` alone does not.
  - Multi-raise SUTs produce multiple cache entries; deserialization reads
    all matching `":raised:"` prefixed keys.
- **Implementation notes:** `cacheKeyRaised(typeId)` proc (Z3) produces the
  per-type key; `loadAll(sutPrefix)` in `db.nim` scans all keys matching
  the SUT prefix and reconstructs the `seq[RawResult]`.

---

**RED test:** `tests/tsymex_phase15_z4_walkctx.nim`, two named tests:

1. `"z4 found: WalkCtx.found is seq[RawResult]"` — compile-time type
   assertion: `static: doAssert typeof(WalkCtx.found) is seq[RawResult]`.

2. `"z4 settings composition: withSymexSettings maxFrontierSize=1 wires
   through"` — calls `withSymexSettings() do (s: var SymexSettings):
   s.maxFrontierSize = 1` and asserts the returned settings have
   `maxFrontierSize == 1` and all other fields equal `defaultSymexSettings()`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — change `WalkCtx.found` field type
  from `Option[RawResult]` to `seq[RawResult]`; rewrite all `isSome`/
  `get`/`= some(...)` sites; rewrite `shouldStop`; add `WalkerStatics`
  and `CallFrameCtx` type definitions (empty records); rename
  `WalkCtx.effects` to `WalkCtx.statics` + `WalkCtx.frame`; rewrite all
  `w.effects.*` sites to `w.statics.*` or `w.frame.*`.
- `docs/symex/ADR-0007-exception-flow.md` — new file.
- `tests/tsymex_phase15_z4_walkctx.nim` — new test file (the RED file,
  now made GREEN).

**DoD:**
- [ ] Both RED tests pass `nim c -r` and `nim cpp -r`
- [ ] `typeof(WalkCtx.found) is seq[RawResult]` at compile time
- [ ] `shouldStop` halts on first `sxSat` or `sxRaised` entry; does NOT
  halt on `sxUnknown`-only `found` (verified by constructing a `WalkCtx`
  with one `sxUnknown` entry and asserting `shouldStop == false`)
- [ ] Zero `w.found.isSome` / `w.found.get` / `w.found = some(` patterns
  remaining in `runtime.nim` (grep confirms)
- [ ] `WalkCtx.effects` field removed; `WalkCtx.statics: WalkerStatics`
  and `WalkCtx.frame: CallFrameCtx` present (grep confirms)
- [ ] Zero `w.effects` references remaining in `runtime.nim` (grep confirms)
- [ ] `ADR-0007-exception-flow.md` on disk with all required sections
  (context, decision, alternatives, consequences, implementation notes)
- [ ] `withSymexSettings(base, f)` composition wires through correctly
  (test 2 above)
- [ ] Full `nimble test` green; field-rename compiles on both backends
- [ ] `docs/symex/SYMEX_PLAN.md` Z4 row marked SHIPPED with commit SHA

<!-- CLUSTER_L -->
## Cluster L — templates and macros

### Preamble

**Verified hypothesis.** Nim's semchecker expands all templates and
macros before the typed AST reaches the proptest symex pipeline.
Every entry point into the parser — `symexFind`, `symexForAll`,
and `assertCoveredBy` — obtains the SUT body via `fn.getImpl`, which
always yields `nnkProcDef`. `parseProc` opens with
`procDef.expectKind nnkProcDef`; if the macro or semchecker ever
handed back anything else the assertion would fire at compile time.
No `nnkTemplateDef`, `nnkMacroDef`, or unresolved `nnkCall`-to-macro
node can reach `parseStmt` or `parseExpr`. This is not a design
choice we made — it is a consequence of how Nim's macro system works:
by the time any `macro` body runs, the typed elaboration pass has
already reduced every template expansion and applied every macro
transformation reachable from the call graph.

**Open question 1 — CLOSED (architect bake-in, v2).** Decision:
**trust the semchecker, regression-test the trust boundary.**
The semchecker is Nim's contract-keeper for the typed AST;
second-guessing it inside the symex walker would require
reimplementing a subset of the Nim elaboration rules, which is
both fragile and incorrect in the presence of language evolution.
Cluster L encodes the trust boundary as an explicit, executable
regression surface: if a future Nim version changes elaboration
order or introduces a new node kind that leaks through `getImpl`,
the L1 structural assertion test will turn RED, making the
breakage visible before it silently corrupts the analysis.
The `{.dirty.}` template variant (which injects identifiers into
the caller's scope and can produce different AST residuals than
vanilla templates) is explicitly included as a third test case in
L1's RED test specification; any new node kind it surfaces falls
under L2's classified-error handling.

**Cluster shape.** Because the primary hypothesis is confirmed,
Cluster L is a **verification + boundary-audit cluster**, not a
feature cluster. Its three cycles are:

| Cycle | Topic | Key dependency |
|-------|-------|----------------|
| L1 | Boundary audit — structural assertion on expanded AST; source-location behaviour documented; `{.dirty.}` template variant | Cluster Z green (Z0/Z1/Z2) |
| L2 | `untyped` template parameters — verify shaped typed body; classified error if residual node escapes | L1 confirmed trust boundary |
| L3 | `getAst` / `quote do` macros — round-trip verification; stdlib-op call identity; Cluster Z regression smoke | L2 classified-error machinery |

No walker version bump, no new IR kinds, no new `SymVal` variants
land in Cluster L. If any cycle discovers a residual node that the
walker cannot handle, it either extends `parseStmt`/`parseExpr`
narrowly (preferred) or emits a classified `isUnsupported` with
a `SymexErrorInfo` (invariant 3) — never `sxUnknown` with no info.

**Out of scope for this cluster.**
- `quote`-block AST mutators whose identifiers the semchecker leaves
  unresolved (e.g. spliced type-class constraints that are not
  concretised at the `getImpl` site): classified as
  `seUnsupportedOp` if encountered at walk time; no attempt is made
  to resolve them inside the walker.
- `{.experimental: "..."}` pragma surfaces (e.g.
  `{.experimental: "strictFuncs"}`, `{.experimental: "views"}`):
  these may alter the typed AST in ways not covered by the
  semchecker guarantee above; any node kind they surface is
  classified as `seUnsupportedOp` at parse time and does not
  constitute a Cluster L regression.

---

### L1 — boundary audit

**What it does:** Writes a structural assertion test confirming that
a SUT defined inside a template and a SUT emitted by a macro both
reach `parseProc` as a plain `nnkProcDef` with a fully expanded
body. Documents source-location behaviour (call-site vs expansion
internals) as an explicit, stable contract.

**RED test:** `tests/tsymex_phase15_l1_boundary.nim`, test name
`"template-defined SUT reaches parser as nnkProcDef with expanded body"`.
Specifies: (a) a `template withLogging(name, body)` that wraps a
`proc` definition is used to define a SUT; (b) a macro
`emitSut(name)` that calls `quote do: proc <name>(x: int): bool = ...`
emits a SUT proc; (c) a `{.dirty.}` template variant —
`template withCounter(body: untyped) {.dirty.}` that injects a
fresh `counter` identifier into the caller's scope — is used to
define a third SUT; the `{.dirty.}` case is audited for the same
invariants as cases (a) and (b): `parseProc(fn.getImpl)` must return
a plain `nnkProcDef` with no `nnkTemplateDef`, `nnkMacroDef`, or
unresolved `nnkCall`-to-macro node anywhere in the IR tree; if a
new node kind surfaces (e.g. an injected-identifier residual not
seen in vanilla template expansion) it is recorded and L2's
classified-error handling applies; (d) an inner `debugHook` proc
(callable from a test-only macro) calls `parseProc(fn.getImpl)` on
all three SUTs and asserts the result's kind is `nnkProcDef`, the
body's root is `isBlock`, and neither `nnkTemplateDef` nor
`nnkMacroDef` appears anywhere in the parse result's IR; (e)
source-location nodes in the raw `nnkProcDef` are recorded and
asserted to not reference the template-definition file line — they
must reference the call-site line or the macro emission site;
(f) `symexFind` on each SUT produces a sound `SymexResult` with no
`sxUnknown`.

**GREEN:** No parser changes. Changes land in:
- `tests/tsymex_phase15_l1_boundary.nim` — new test file. The
  structural assertion is implemented as a compile-time `macro
  auditGetImpl(fn: typed)` that calls `parseProc(fn.getImpl)` and
  iterates the returned `ParseResult.body` IR tree via a small
  recursive scanner asserting no IR kind is an unknown-reason
  `isUnsupported` node. The scanner is test-local, not shipped to
  the library.
- `docs/symex/templates-macros.md` — new document recording the
  confirmed behaviour: (a) semchecker expands before `getImpl`;
  (b) source-location points to the expanded-proc declaration site
  (which, for a template-defined proc, is the template instantiation
  site — verifiable); (c) the trust boundary and its regression-
  test harness; (d) the confirmed non-scope: proptest cannot symex
  a SUT whose *name* is computed dynamically by a macro at a call
  site proptest's own macro never sees (the `fn` parameter must
  be a resolvable symbol at the `symexFind` call site).

**DoD:**
- [ ] `"template-defined SUT reaches parser as nnkProcDef with expanded body"` passes under both `--backend:c` and `--backend:js` (or documented js-skip with rationale)
- [ ] `"macro-emitted SUT reaches parser as nnkProcDef with expanded body"` passes
- [ ] `"{.dirty.} template SUT reaches parser as nnkProcDef with expanded body"` passes; any new node kinds surfaced are recorded in `docs/symex/templates-macros.md` and classified (not silently ignored)
- [ ] `"source location in expanded proc does not reference template internals"` assertion passes or is documented as Nim-version-specific with a version guard
- [ ] `symexFind` on the template-defined SUT produces `sxSat` with a correct witness
- [ ] `symexFind` on the macro-emitted SUT produces `sxSat` with a correct witness
- [ ] `symexFind` on the `{.dirty.}` template SUT produces `sxSat` with a correct witness (or `sxUnknown` with non-empty `SymexErrorInfo` if a residual node kind is found)
- [ ] `docs/symex/templates-macros.md` committed with the trust-boundary contract
- [ ] `classifyType` recognises `char` as BV8 (`unranged(tInt(8, signed=false))`): a SUT `proc f(c: char): bool = c == 'A'` produces a real `sxSat` verdict (not `sxUnknown`) — wired through Z3's BV8 sort
- [ ] `sink T` / `lent T` annotations on template-expanded code paths are stripped before `classifyType` is called; regression test: a SUT parameter typed `sink int` in a template-expanded proc produces the same verdict as `int` (no `seUnsupportedOp`)
- [ ] Regression: existing phase-14 tests pass unchanged

---

### L2 — `untyped` template parameters

**What it does:** Verifies that a SUT using a template with `untyped`
parameters — which defer typechecking until expansion and can produce
surprising intermediate AST shapes — still delivers a
walker-acceptable typed `nnkProcDef` body to `parseProc`. If any
residual node kind survives that the parser cannot handle, the cycle
either (a) adds a narrow `parseStmt`/`parseExpr` case for the node
kind, or (b) emits a deterministic classified `isUnsupported` with
a `SymexErrorInfo` that names the residual kind — never silent.

**RED test:** `tests/tsymex_phase15_l2_untyped_template.nim`, test
name `"untyped-template SUT body parses without unknown residuals"`.
Specifies: (a) `template assertPositive(x: untyped) = if x <= 0: discard`
is used inside a SUT `proc f(n: int): bool = assertPositive(n); n > 0;
symexTarget("positive")` — the `untyped` template is expanded by the
semchecker before `getImpl` is called; (b) `parseProc(f.getImpl)`
produces a `ParseResult` whose IR tree contains no `isUnsupported`
node with `reason` beginning with `"statement kind nnk"` and a kind
that is not already in the supported fragment; (c) `symexFind(f,
tLabel("positive"))` produces `sxSat` with a witness `n > 0`.
A second sub-test `"untyped-template with branch produces classified
error not sxUnknown"` uses a template that expands to a node kind
known to be outside the supported fragment and asserts the result
is `isUnsupported` with non-empty `reason` and that `symexFind`
returns `sxUnknown` with a non-empty `SymexErrorInfo` on the finding
(invariant 3: classified, never silent).

**GREEN:** Files touched depend on what residual nodes are found during
the RED investigation:

- **If all `untyped` template expansions land in already-supported
  node kinds** (the expected outcome based on the semchecker
  guarantee): no parser changes; test is GREEN purely from the
  structural assertion confirming no residuals escape.
- **If a residual node kind is found** (e.g. a `nnkStaticExpr` or
  `nnkMixin` surviving into the typed body): `dsl_parser.nim`
  `parseStmtInner` gains a narrow `of nnk<Kind>:` case. The case
  either lowers the node to an existing IR form (preferred) or
  falls through to `mkUnsupported(reason)` where `reason` names the
  node kind explicitly. The `mkUnsupported` path satisfies invariant
  3 because `isUnsupported` with a named reason is classified; the
  walker emits `sxUnknown` with `SymexErrorInfo{source: "parser:unsupported",
  message: reason}` via the existing B67 / C4 machinery, not a
  silent `sxUnknown` with empty errors.
- `tests/tsymex_phase15_l2_untyped_template.nim` — new test file.
- `docs/symex/templates-macros.md` updated with `untyped` template
  findings section.

**DoD:**
- [ ] `"untyped-template SUT body parses without unknown residuals"` passes; `symexFind` produces `sxSat`
- [ ] `"untyped-template with branch produces classified error not sxUnknown"` passes; finding has non-empty `errors` field
- [ ] No `isUnsupported` node with `reason = ""` anywhere in the parse result of the first sub-test (invariant 3 self-check)
- [ ] If any new `parseStmt` case was added: it has its own focused unit test in the same file
- [ ] `docs/symex/templates-macros.md` `untyped` section committed
- [ ] Regression: L1 tests and all phase-14 tests pass unchanged

---

### L3 — `getAst` / `quote do` macros

**What it does:** Verifies that macros using `getAst` or `quote do`
to construct and emit proc bodies round-trip correctly through the
symex parser. Specifically: (a) a macro that emits a call to a
symex-known stdlib op (e.g. `len`) inside the SUT body produces a
walker-accepted IR identical to a hand-written call to the same op;
(b) a macro that emits nested generic calls or type-class-constrained
calls produces either a sound witness or a classified error — not
silent fallback.

**RED test:** `tests/tsymex_phase15_l3_quote_do.nim`, test name
`"quote-do macro emitting len call is walker-identical to hand-written"`.
Specifies: (a) `macro withLenCheck(name, body): untyped` uses
`quote do: proc `name`(s: seq[int]): bool = if s.len > 3: `body``
to emit a SUT; (b) a hand-written SUT `proc handWritten(s: seq[int]):
bool = if s.len > 3: symexTarget("long")` is defined beside it;
(c) `symexFind(quoteSut, tLabel("long"))` and `symexFind(handWritten,
tLabel("long"))` produce witnesses that are observably equal
(same constraint on `s.len`); (d) a second sub-test
`"quote-do macro emitting constrained-generic call produces classified error not silent"`:
a macro emits a call to a user-defined generic proc `proc clamp[T: Ordinal](v, lo, hi: T): T`
inside the SUT body; `symexFind` must return either `sxSat` (if the
instantiation is monomorphisable at the call site — which is the
case if the concrete type is determined by the SUT's parameter) or
`sxUnknown` with non-empty `SymexErrorInfo` (if the generic cannot
be resolved) — never `sxUnknown` with empty errors.

**GREEN:** No walker changes expected. Files touched:
- `tests/tsymex_phase15_l3_quote_do.nim` — new test file.
- If the `getAst` / `quote do` round-trip surfaces a node-kind gap
  not caught in L2 (e.g. `nnkAccQuoted` surviving into the typed
  body for backtick-quoted identifiers): `dsl_parser.nim`
  `parseExpr` or `parseStmtInner` gains a narrow case following the
  same pattern as L2's GREEN: lower if possible, else
  `mkUnsupported(reason)` with an explicit reason string.
- `docs/symex/templates-macros.md` updated with `quote do` and
  `getAst` findings section and the stdlib-op identity confirmation.
- **Invariant 4 — regression smoke:** This cycle includes an
  explicit re-run of Cluster Z's full test suite under the walker
  state as of L3. The re-run is recorded in the cycle's commit
  as a CI check, not a new test file. Purpose: catch any
  state-threading bug introduced by the L1/L2/L3 parser additions
  (if any were made) against the earliest cluster's baseline.

**DoD:**
- [ ] `"quote-do macro emitting len call is walker-identical to hand-written"` passes; both witnesses satisfy `s.len > 3`
- [ ] `"quote-do macro emitting constrained-generic call produces classified error not silent"` passes; if `sxUnknown`, `finding.errors` is non-empty
- [ ] Cluster Z regression smoke passes (all Z1/Z2 tests green under L3 walker state)
- [ ] No `isUnsupported` node with empty `reason` in any parse result from these tests (invariant 3 self-check)
- [ ] `docs/symex/templates-macros.md` complete: trust boundary, `untyped` findings, `quote do`/`getAst` findings, confirmed non-scope (dynamic-name SUTs), source-location contract
- [ ] All L1/L2 tests still pass (regression within cluster)
- [ ] All phase-14 tests pass (cross-cluster regression)

<!-- CLUSTER_F -->
## Cluster F — float

Cluster F adds IEEE 754 floating-point support to the symex engine:
`float`, `float32`, and `float64` as SUT parameter types, literal
lifts, arithmetic and comparison ops, int↔float conversions,
math-module functions, eval-side extraction, and a round-trip
regression smoke. It lands after Cluster L and before Cluster S.

| Cycle | Topic | Key dependency |
|-------|-------|----------------|
| F0-ADR | Author `docs/symex/ADR-0005-float-nan-inf.md` (NaN/Inf semantics, IEEE comparison rules, single-canonical-NaN, Z3 FP theory choices, rejected alternatives) | Cluster L green |
| F1 | Type-bridge: `float`/`float32`/`float64` IR kinds, `svFloat32`/`svFloat64` | F0-ADR |
| F2 | Float literal lifts (`Inf`, `NaN`, `-0.0`, finite) | F1 |
| F3 | Arithmetic ops (`+`, `-`, `*`, `/`, unary `-` via `uNeg` runtime dispatch) | F2 |
| F4 | Comparison ops (`<`, `<=`, `==`, `!=`, `>`, `>=`) | F3 |
| F5 | int↔float conversions (`float(x)`, `int(f)`) with range overflow handling | F4 |
| F6 | math-module ops (`abs`, `sqrt`, `min`, `max`, `floor`, `ceil`, `round`, `trunc`); `signbit`; FP predicates `isNaN`, `isInf`, `isFinite`, `isNormal`; `copySign`/`nextafter` deferred as `feUnsupportedOp`; `classify(f)` deferred as `feUnsupportedOp` (`severity: sevError`) | F5 |
| F7 | Eval-side extraction: bit-exact float witness round-trip; `model.eval(expr, model_completion=true)` before `fpBitsToUint64` | F6 |
| F8 | Regression smoke + arbitrary float64 SUT round-trip property; walker version `"4"→"5"`; `withSymexSettings` wiring confirmed | F7 |
| F9a | Array element type-bridge audit (`array[N, float32]`/`array[N, float64]`); NaN extraction test via `model_completion` | F8 |
| F9b | `seq[float32/64]` SUT parameter type: allocate → extract → `emitTyAndReader` | F9a |
| F9c | `object variant` arm fields of type `float32/64`: both-arm witness round-trip | F9b |

### Preamble

**ADR-0005: NaN/Inf semantics.** The engine honors IEEE 754 NaN
semantics exactly as Z3's FP theory delivers them. Specifically:
`NaN != NaN` is `true` (IEEE equality via `Z3_mk_fpa_eq` returns
`false` for NaN/NaN); `+0 == -0` is `true`. A single canonical
NaN is modeled — NaN payload bits are not reachable through any
Nim API under `-d:release`, so payload-distinct NaNs would add
solver complexity with no observable user benefit. `Inf` is a
normal Z3 FP value: arithmetic on `Inf` follows IEEE 754 (e.g.
`Inf + 1.0 == Inf`). These choices match Nim's observable float
semantics at the language boundary. Any SUT that relies on NaN
inequality will be naturally handled: the witness finder will
satisfy `x != NaN` when a path constraint requires it, or will
find `NaN` as the witness when a path becomes satisfiable only
via NaN (e.g. `isNaN(f)` guard). The `NaN != NaN` rule means
`==` on a float SUT parameter never equates two NaN witnesses —
the engine will not produce a spurious UNSAT on a path that
requires two distinct NaN values.

**Open Question 2 — closed.** Rounding modes confirmed:
**`rmRNE` for int→float**, **`rmRTZ` for float→int** (truncation
toward zero, matching C semantics and Nim's observable behavior
under `-d:release` on all common targets). Both directions are
encoded explicitly in F5. No Nim integer type introduces a
rounding quirk beyond what `toFpFromSigned`/`toSbv` with the
stated modes already model. Decision is final.

**Why F is a cheap precision win.** nim-z3 v2.0.0 ships a
complete, stable, tested FP surface in `z3/fp.nim`: typed
`Z3Fp[E, S]` with phantom widths, the full five-rounding-mode
family, IEEE arithmetic operators (`fpAdd`, `fpSub`, `fpMul`,
`fpDiv`) with operator overloads (`+`, `-`, `*`, `/` default to
`rmRNE`), comparisons (`<`, `<=`, `>`, `>=`, `==`, `!=`),
special-value constructors (`mkFpNaN`, `mkFpInf`, `mkFpZero`),
and bit-exact model extractors (`evalFloat64Opt`, `evalFloat32Opt`
via `toFloat64`/`toFloat32` which route through
`Z3_mk_fpa_to_ieee_bv` + `Z3_get_numeral_uint64`). The
extraction pattern — `m.evalFloat64Opt(sv.fp64)` returning
`Option[float64]` — is already fully unit-tested in
`tests/tfp_eval.nim`. The type-bridge addition (F1) and the
`RawWitness` extension (F7) are the only structural lifts; the
remaining cycles are plumbing the existing nim-z3 surface into
proptest's IR/walker/extractor pipeline.

**Path-sat impact: none.** Float introduces no new control-flow
surfaces. Branching on a float value (e.g. `if f > 0.0`) already
parses as an `nnkIfStmt` with a float comparison in the condition;
the walker forks on the `Z3Bool` produced by the comparison
operator, exactly as it does for integer branches. The float data
domain is a pure extension to the set of `SymVal` variants —
it does not widen the path frontier. F3/F4 arithmetic and
comparison ops add new `SVKind` entries and new `IRBinop`/`IRUnop`
entries, but the path-forking machinery is unchanged.

**`SymexErrorKind` enum.** F1 assumes (or introduces via a
pre-F1 ADR pass) a `SymexErrorKind` enum replacing the free-form
`kind: string` field of `SymexErrorInfo`. All F-cluster classified
errors use the `fe` prefix: `feUnsupportedOp`, `feExtractionFailed`,
etc. These become enum variants (e.g. `feUnsupportedOp`,
`feExtractionFailed`). The enum is defined in `types.nim` before F1
bakes in; every existing string-based error kind in the codebase is
either migrated in a pre-F1 sweep or aliased until the full enum
migration lands.

**Standing rules for this cluster:**

- PhD-CS bar, no consumers yet. Every gap in the float fragment
  is a future "not implemented" wall.
- **Invariant 3 (no silent fallbacks):** any unsupported FP
  operation encountered in the walker emits a classified
  `SymexErrorInfo{kind: feUnsupportedOp, op: "<name>"}` — never
  `sxUnknown` with an empty `errors` field. This applies equally
  to math-module ops that fall through the `stdlib_models` table
  (F6) and to unrecognized FP call nodes at parse time.
- **Invariant 4:** F8 is the regression smoke for the cluster.
  All prior-cluster tests must pass under the F8 cycle's walker
  state before F8's own round-trip property test is added.

**Out of scope for Cluster F** (all emit `feUnsupportedOp`, `severity: sevError`; Phase 16 backlog):

| Operation | Reason deferred |
|-----------|----------------|
| `copySign(x, y)` | Encodeable via `fpIsNegative`/`fpAbs` composition but cost/benefit deferred |
| `nextafter(x, y)` | No native Z3 FP equivalent |
| `log(x)`, `exp(x)`, `pow(x, y)` | No Z3 FP native; would require axiomatization with unknown completeness impact |
| `sin(x)`, `cos(x)`, `tan(x)`, `atan2(y, x)` | Transcendental; no Z3 FP decision procedure |
| `log2(x)`, `log10(x)` | Same as `log` |
| `classify(f)` as enum result | `FloatClass` enum encoding deferred; `isNaN`/`isInf`/`isFinite`/`isNormal` predicates cover the practical test-predicate cases |
| Payload-distinct NaNs | Not observable through any Nim language operation in scope; see ADR-0005 |

---

### F0-ADR — NaN/Inf semantics decision record

**What it does:** Authors `docs/symex/ADR-0005-float-nan-inf.md` before
any float feature code lands. The ADR records the four design decisions
that the rest of Cluster F depends on: (1) single-canonical NaN with no
payload bits, (2) IEEE comparison operators throughout via Z3 FP theory
(`Z3_mk_fpa_eq` etc.), (3) ±Inf via `mkFpInf` constructors, (4)
signed-zero preservation with `mkFpZero`. It documents rejected
alternatives (payload-distinct NaN family, structural Z3 equality for
`==`) and the reasoning for each rejection. No source code is edited;
this is a checklist-DoD documentation cycle.

**RED test:** None (documentation cycle).

**GREEN:** File created:

- `docs/symex/ADR-0005-float-nan-inf.md` — NaN/Inf semantics decision
  record matching ADR-0001..0004 depth. Sections: Context, Options
  considered (NaN encoding, IEEE comparison, Inf, signed zero), Decision
  (six numbered decisions), Z3 FP-theory API mapping table, Consequences
  (intended / accepted cost / deferred), Validation (links to F2/F4/F6/F7
  DoD items that verify the decisions).

**DoD:**
- [ ] `docs/symex/ADR-0005-float-nan-inf.md` exists on disk and covers:
  NaN/Inf semantics, IEEE comparison rules, single-canonical-NaN decision
  (no payload), Z3 FP-theory choices, rejected alternatives.
- [ ] ADR sections: Context, Options considered, Decision, Consequences,
  Validation — matching the structure of ADR-0001..0004.
- [ ] Z3 FP API mapping table present (at minimum: `mkFpNaN`, `mkFpInf`,
  `mkFpZero`, `Z3_mk_fpa_eq`, `fpIsNaN`, `fpIsInfinite`, `fpIsNormal`,
  `evalFloat64Opt`).
- [ ] F1 cycle references the ADR as its design authority (preamble
  updated if needed).

---

### F1 — type-bridge: `float`, `float32`, `float64`

**What it does:** Adds `itFloat32` and `itFloat64` IR type kinds
(Nim's `float` aliases to `float64` on all current targets) and
wires them through every dispatch site that currently has a case
for `itBool`/`itInt`. The walker gets a new `svFloat32` and
`svFloat64` `SVKind` variant; `allocateSym` allocates the matching
`Z3Float32`/`Z3Float64` free variable. A SUT with one `float`
parameter reaches `trySolve`, Z3 returns a model, and the walker
extracts a concrete `float64` witness.

**RED test:** `tests/tsymex_phase15_F1_typebridge.nim`, test name
`"float64 SUT: symexFind returns a float witness"`. Specifies:
given a SUT `proc f(x: float): bool = x > 0.0`, `symexFind`
returns `sxSat` with a witness satisfying `x > 0.0`.

**GREEN:** Files touched:

- `src/proptest/smt/types.nim` — add `itFloat32`, `itFloat64` to
  `IRTypeKind` enum; add matching `of itFloat32`, `of itFloat64`
  branches to `IRType` (no payload fields needed — the sort is
  fully determined by the kind); add `tFloat32()` and `tFloat64()`
  constructors; extend `==` and `$` on `IRType`.

- `src/proptest/smt/dsl_typebridge.nim` — extend `classifyType`'s
  text-match block with:
  ```
  of "float":   unranged(tFloat64())
  of "float32": unranged(tFloat32())
  of "float64": unranged(tFloat64())
  ```
  No range support for floats (range[float] is not legal Nim);
  `hasRange` stays `false`.

- `src/proptest/smt/dsl_parser.nim` — extend `emitIRType` with
  `of itFloat32: newCall(bindSym"tFloat32")` and
  `of itFloat64: newCall(bindSym"tFloat64")`; extend
  `emitExpr`'s `iekFloatLit` stub (added in F2 — F1 adds a
  compile-time stub that calls `error("float literal: implement in F2")`).

- `src/proptest/smt/runtime.nim` — add `svFloat32` and `svFloat64`
  to `SVKind`; extend `SymVal` with `fp32: Z3Float32` and
  `fp64: Z3Float64` fields; extend `allocateSym`:
  ```
  of itFloat32: SymVal(kind: svFloat32, fp32: mkFloat32Var(baseName))
  of itFloat64: SymVal(kind: svFloat64, fp64: mkFloat64Var(baseName))
  ```
  Extend `typeOf(sv: SymVal)` with `of svFloat32: tFloat32()` and
  `of svFloat64: tFloat64()`; extend `extractLeaf` stub (real
  extraction lands in F7 — stub raises `ValueError("float
  extraction: implement in F7")`). Extend every other `case sv.kind`
  dispatch with `of svFloat32, svFloat64: raise ...` stubs so
  compilation is exhaustive.

- `src/proptest/symex.nim` — extend `primTyAndReader` with
  `of itFloat32: ("float32", "readFloat32")` and
  `of itFloat64: ("float", "readFloat")` (stubs; real readers
  land in F7); extend `emitTyAndReader`'s `of itBool, itInt:`
  branch to include `itFloat32, itFloat64`.

- `src/proptest/smt/canonicalize.nim` — extend the type-encoding
  with `of itFloat32: result &= "F32"` and
  `of itFloat64: result &= "F64"`.

nim-z3 APIs: `mkFloat32Var`, `mkFloat64Var` (both in `z3/fp.nim`).

**DoD:**
- [ ] **Precondition:** no `:unknown` cache entries exist for
      `float`/`float32`/`float64`-typed SUTs before F1. Confirmed
      by `grep -r 'itFloat' .cache/` (or equivalent DB scan) — the
      parser rejected all float SUTs at parse time before F1, so
      no stale cache entries can exist. Documented and asserted at
      the start of F1's TDD session.
- [ ] `"float64 SUT: symexFind returns a float witness"` passes
      (witness extraction not yet bit-correct — stub reader returns
      `default(float)`, test asserts only `sxSat` status and that
      the witness field type is `float`).
- [ ] All ~76 prior-cycle test files compile and pass (exhaustive
      `case` dispatch guaranteed by compiler; existing float-free
      SUTs are unaffected).
- [ ] `CLAUDE.md` / inline comments note F7 stub sites.

---

### F2 — float literal lifts

**What it does:** Constant-folds float literals in the DSL into
`Z3Float32`/`Z3Float64` AST nodes. Covers: normal finite values
(`3.14`, `1e10`, `-1.5`), `0.0`, `-0.0`, `Inf`, `-Inf`, `NaN`.
The parser recognizes `nnkFloat64Lit`, `nnkFloat32Lit`, and the
`math.Inf`/`math.NaN`/`math.classify` call patterns.

**RED test:** `tests/tsymex_phase15_F2_float_literals.nim`, test
name `"float literal lifts: Inf, NaN, -0.0, finite values all
produce Z3 FP numerals"`. Specifies: SUTs that check
`f == Inf`, `f == NaN`, `f == -0.0`, `f == 3.14`, `f == 0.0`
each produce `sxSat` (except `f == NaN` which is `sxUnsat` by
ADR-0005 — NaN != NaN under IEEE equality means the constraint
`f == NaN` is unsatisfiable in the Z3 FP theory).

**GREEN:** Files touched:

- `src/proptest/smt/types.nim` — add `iekFloatLit` to `IRExprKind`;
  add `fval: float64` and `fwidth: int` (32 or 64) payload to the
  matching `IRExpr` branch. Add `mkFloatLit(v: float64, width =
  64): IRExpr` and `mkFloat32Lit(v: float32): IRExpr` constructors.

- `src/proptest/smt/dsl_parser.nim` — in `parseExpr`, recognize:
  - `nnkFloat64Lit` nodes → `mkFloatLit(node.floatVal, 64)`
  - `nnkFloat32Lit` nodes → `mkFloat32Lit(float32(node.floatVal))`
  - `nnkPrefix` with op `"-"` on a float literal → negate the
    `fval` at parse time (covers `-0.0` and `-Inf`).
  - Qualified identifiers `Inf`, `NegInf`, `NaN` from `std/math`
    → `mkFloatLit(Inf, 64)`, `mkFloatLit(-Inf, 64)`,
    `mkFloatLit(NaN, 64)` using Nim's compile-time `Inf`/`NaN`
    constants (both are `float` in `std/math`).
  Extend `emitExpr` with `of iekFloatLit: newCall(bindSym"mkFloatLit", newLit(e.fval), newLit(e.fwidth))`.

- `src/proptest/smt/runtime.nim` — add `walk` case for
  `iekFloatLit`: dispatch on `e.fwidth`:
  ```
  if e.fwidth == 32: SymVal(kind: svFloat32, fp32: mkFloat32(float32(e.fval)))
  else:              SymVal(kind: svFloat64, fp64: mkFloat64(e.fval))
  ```
  `mkFloat32`/`mkFloat64` are the nim-z3 literal constructors
  (`Z3_mk_fpa_numeral_float`/`Z3_mk_fpa_numeral_double`). Special
  values: `mkFpNaN[8,24]()` / `mkFpNaN[11,53]()`,
  `mkFpInf[8,24](negative=...)` / `mkFpInf[11,53](negative=...)`,
  `mkFpZero[8,24](negative=true)` / `mkFpZero[11,53](negative=true)`
  — all in `z3/fp.nim`. Detection at walk time via Nim's
  `classify(e.fval)` from `std/math` (`fcNaN`, `fcInf`, `fcNegInf`,
  `fcNegZero`).

nim-z3 APIs: `mkFloat32`, `mkFloat64`, `mkFpNaN`, `mkFpInf`,
`mkFpZero`.

**DoD:**
- [ ] `"float literal lifts: Inf, NaN, -0.0, finite values all
      produce Z3 FP numerals"` passes — in particular the `NaN`
      case asserting `sxUnsat` (since Z3 cannot satisfy `x == NaN`
      under IEEE equality).
- [ ] `-0.0` lift produces the correct `mkFpZero[11,53](negative=true)`;
      the test asserts `sxSat` for a SUT `proc f(x: float): bool =
      x == -0.0` and verifies the witness is `+0.0` or `-0.0`
      (both satisfy IEEE `+0 == -0`).
- [ ] All prior tests pass.

---

### F3 — arithmetic ops (`+`, `-`, `*`, `/`, unary `-`)

**What it does:** Wires the four binary IEEE 754 arithmetic
operators and unary negation for `float`/`float32`/`float64` SUT
expressions through the parser's existing `nnkInfix`/`nnkPrefix`
path and the walker's `iekBinop`/`iekUnop` dispatch. All binary
ops use `rmRNE` (round-nearest-ties-to-even) — the Z3 FP default
and Nim's IEEE 754 default — matching the infix `+`/`-`/`*`/`/`
operator overloads in `z3/fp.nim` which default to `rmRNE(a.ctx)`.
Users needing explicit rounding modes cannot express them in a
proptest SUT (no `rmRTZ(...)` syntax in Nim property bodies);
explicit RM is not in scope for this cluster.

**RED test:** `tests/tsymex_phase15_F3_float_arith.nim`, test name
`"float arithmetic: symexFind finds witness for x * x > 100.0"`.
Specifies: given `proc f(x: float): bool = x * x > 100.0`,
`symexFind` returns `sxSat` with a witness `x` such that
`x * x > 100.0` holds at runtime.

**GREEN:** Files touched:

- `src/proptest/smt/types.nim` — No new `IRBinop` or `IRUnop`
  entries needed. The existing `ibAdd`, `ibSub`, `ibMul`, `ibDiv`
  cover binary ops. Unary FP negation reuses the existing `uNeg`
  `IRUnop` entry — **no `iuFpNeg` is introduced**. (The earlier
  v1 draft introduced `iuFpNeg`; it was dropped in v2 because it
  breaks type-erasure consistency with FP binops, which already
  reuse `ibAdd`/`ibSub` etc. for float dispatch.)

- `src/proptest/smt/runtime.nim` — In the walker's `iekBinop`
  dispatch, after resolving both operand `SymVal`s, add a float
  branch:
  ```nim
  if lv.kind == svFloat64:
    case e.bop
    of ibAdd: SymVal(kind: svFloat64, fp64: fpAdd(lv.fp64, rv.fp64))
    of ibSub: SymVal(kind: svFloat64, fp64: fpSub(lv.fp64, rv.fp64))
    of ibMul: SymVal(kind: svFloat64, fp64: fpMul(lv.fp64, rv.fp64))
    of ibDiv: SymVal(kind: svFloat64, fp64: fpDiv(lv.fp64, rv.fp64))
    else: raiseUnsupportedOp($e.bop & " on float64")
  elif lv.kind == svFloat32:
    # symmetric, fp32 variants
  ```
  `fpAdd`/`fpSub`/`fpMul`/`fpDiv` with no explicit RM argument use
  the `rmRNE`-defaulting overloads from `z3/fp.nim`.

  Unary FP negation is handled by extending the walker's **existing
  `uNeg` arm** with `sv.kind` runtime dispatch — **not** a new
  `IRUnop` variant:
  ```nim
  of iuNeg:
    let sv = walkExpr(e.unaryOperand, env, pcOut)
    case sv.kind
    of svInt:     SymVal(kind: svInt, zi: -sv.zi)
    of svFloat64: SymVal(kind: svFloat64, fp64: -sv.fp64)
    of svFloat32: SymVal(kind: svFloat32, fp32: -sv.fp32)
    else: raiseUnsupportedOp("uNeg on " & $sv.kind)
  ```
  The `-` unary overloads for `Z3Float32`/`Z3Float64` in `z3/fp.nim`
  wrap `Z3_mk_fpa_neg`.

  Unsupported ops raise `SymexErrorInfo{kind: feUnsupportedOp,
  op: "<name>"}` (Invariant 3).

- `src/proptest/smt/dsl_parser.nim` — No parser changes needed;
  the existing `nnkInfix`/`nnkPrefix` → `iekBinop`/`iekUnop`
  paths already emit the right IR nodes. The `"-"` prefix on a
  float expression emits the existing `iuNeg`; the walker's
  runtime dispatch handles the float case.

nim-z3 APIs: `fpAdd`, `fpSub`, `fpMul`, `fpDiv`, `proc \`-\`[E,S]`.

**DoD:**
- [ ] `"float arithmetic: symexFind finds witness for x * x >
      100.0"` passes with a numerically correct witness.
- [ ] Additional targeted tests: `x + y == 5.0`, `x / y > 2.0`
      (requires `y != 0.0` constraint or `y` is non-zero witness),
      `-x < 0.0` for `x > 0.0`.
- [ ] Unsupported op (e.g. `x ** y` FP exponentiation) produces
      `SymexErrorInfo{kind: feUnsupportedOp}` (not `sxUnknown`
      with empty errors).
- [ ] All prior tests pass.

---

### F4 — comparison ops (`<`, `<=`, `==`, `!=`, `>`, `>=`)

**What it does:** Wires IEEE 754 FP comparisons into the walker's
`iekBinop` boolean-producing path, honoring NaN-unordered
semantics per ADR-0005. `==` and `!=` use `Z3_mk_fpa_eq` (IEEE
equality: `NaN != NaN`, `+0 == -0`). `<`, `<=`, `>`, `>=` use
`Z3_mk_fpa_lt`/`Z3_mk_fpa_leq`/`Z3_mk_fpa_gt`/`Z3_mk_fpa_geq`,
which are all false when either operand is NaN (IEEE
"unordered-silent" semantics). The path condition from a float
comparison is always a `Z3Bool`, so the existing path-forking
machinery is unchanged.

**RED test:** `tests/tsymex_phase15_F4_float_cmp.nim`, test name
`"float comparisons: NaN unordered semantics preserved"`.
Specifies: (a) `symexFind` on `proc f(x: float): bool = x > 0.0`
returns `sxSat` with positive witness; (b) `symexFind` on
`proc f(x: float): bool = x == x` returns `sxUnknown` or `sxSat`
(NaN satisfies `not (x == x)`, so the positive branch may be SAT
or the SUT may be UNSAT; the test verifies that both paths are
explored and a NaN witness is reachable for the negated form
`not (x == x)`).

**GREEN:** Files touched:

- `src/proptest/smt/runtime.nim` — In `walk(iekBinop)`, extend the
  float branch to cover comparison operators that produce `svBool`:
  ```nim
  of ibEq:  SymVal(kind: svBool, bo: lv.fp64 == rv.fp64)
  of ibNeq: SymVal(kind: svBool, bo: lv.fp64 != rv.fp64)
  of ibLt:  SymVal(kind: svBool, bo: lv.fp64 <  rv.fp64)
  of ibLe:  SymVal(kind: svBool, bo: lv.fp64 <= rv.fp64)
  of ibGt:  SymVal(kind: svBool, bo: lv.fp64 >  rv.fp64)
  of ibGe:  SymVal(kind: svBool, bo: lv.fp64 >= rv.fp64)
  ```
  All six operators are the `Z3Fp[E,S]` overloads from `z3/fp.nim`:
  `==`/`!=` via `Z3_mk_fpa_eq`/`Z3_mk_not(Z3_mk_fpa_eq(...))`;
  `<`/`<=`/`>`/`>=` via `Z3_mk_fpa_lt`/`_leq`/`_gt`/`_geq`.
  Symmetric for `svFloat32`.

  The resulting `svBool` participates in the path condition fork
  exactly as integer-comparison `svBool` results do — no walker
  changes needed.

- No parser or type changes needed beyond F3's additions.

nim-z3 APIs: `proc \`==\`[E,S]`, `proc \`!=\`[E,S]`,
`proc \`<\`[E,S]`, `proc \`<=\`[E,S]`,
`proc \`>\`[E,S]`, `proc \`>=\`[E,S]` (all in `z3/fp.nim`).

**DoD:**
- [ ] `"float comparisons: NaN unordered semantics preserved"` —
      the negated-equality SUT `not (x == x)` returns `sxSat`
      (the NaN path is reachable). Witness bit-pattern check
      (confirming the extracted witness is NaN via
      `classify(w) == fcNaN`) is **deferred to F7 DoD** — F4
      lands before F7's bit-exact extraction is in place, so the
      bit-pattern check is not feasible at F4 time. F4 DoD
      asserts `sxSat` status only.
- [ ] `"float comparisons: < / <= / > / >= correct on normals"` —
      basic ordering tests.
- [ ] `+0 == -0` test: SUT `proc f(x: float): bool = x == 0.0`
      produces SAT with either `+0.0` or `-0.0` as witness
      (both satisfy IEEE equality).
- [ ] All prior tests pass.

---

### F5 — int↔float conversions

**What it does:** Models Nim's `float(x)` for integer `x`
(int→float64, round-nearest-even) and `int(f)` for float `f`
(float64→int64, round-toward-zero, matching C truncation semantics).
Also handles `float32(x)` and `int32(f)`. Per Open Question 2,
the rounding modes are explicit: `toFpFromSigned(rmRNE(), bv64,
Z3Float64)` for int→float and `toSbv[11,53,64](rmRTZ(), fp64)`
for float→int.

**RED test:** `tests/tsymex_phase15_F5_float_conv.nim`, test name
`"int-to-float conversion: symexFind witnesses conversion constraint"`.
Specifies: given `proc f(x: int): bool = float(x) > 1.5`, `symexFind`
returns `sxSat` with a witness `x >= 2`; and given
`proc f(x: float): bool = int(x) == 3`, `symexFind` returns `sxSat`
with a witness in the interval `[3.0, 4.0)`.

**GREEN:** Files touched:

- `src/proptest/smt/types.nim` — Add `iekConvIntToFloat` and
  `iekConvFloatToInt` to `IRExprKind`. Each carries a child
  expression plus a target width. Add constructors
  `mkConvIntToFloat(e: IRExpr, targetWidth = 64): IRExpr` and
  `mkConvFloatToInt(e: IRExpr, targetWidth = 64): IRExpr`.

- `src/proptest/smt/dsl_parser.nim` — Recognize `nnkConv` and
  `nnkHiddenStdConv` nodes where the source type is int and the
  target is float (or vice versa). The parser already handles
  `nnkHiddenStdConv` for int widening (pass-through); extend it
  to emit `iekConvIntToFloat` when the target typedesc is `float`/
  `float32`/`float64` and the source is any int family, and
  `iekConvFloatToInt` in the reverse direction. `float(x)` in typed
  Nim AST appears as `nnkConv(float, x)` after semcheck.

- `src/proptest/smt/runtime.nim` — Walk cases for the two new
  expression kinds:

  **F5a — int→float (`iekConvIntToFloat`):**

  The `toFpFromSigned` nim-z3 API requires a `Z3BitVec[W]` operand;
  `SymVal` for an `int` carries a `Z3Int` (`svInt`), not a bitvector.
  The correct chain is:

  ```nim
  of iekConvIntToFloat:
    let sv = walkExpr(e.convOperand, env, pcOut)
    let bv64: Z3BitVec[64] =
      case sv.kind
      of svInt:   intToBv[64](sv.zi, Z3BitVec[64])
                  # bitvec.nim:746 — Z3_mk_int2bv; width from typedesc
      of svBV32:  sv.bv32.signExtend[64]()   # sign-extend to 64 bits
      of svBV64:  sv.bv64                    # use directly
      else: raiseUnsupportedOp("int→float conv from " & $sv.kind)
    SymVal(kind: svFloat64,
           fp64: toFpFromSigned(rmRNE(), bv64, Z3Float64))
  ```
  `float32` conversions use `intToBv[32]` and `toFpFromSigned(rmRNE(), bv32, Z3Float32)`.

  **F5b — float→int (`iekConvFloatToInt`):**

  Out-of-range `int(f)` is implementation-defined in Nim (C truncation
  semantics with UB for out-of-range values). The walker models both
  the in-range and out-of-range paths:

  ```nim
  of iekConvFloatToInt:
    let sv = walkExpr(e.convOperand, env, pcOut)
    # In-range constraint: INT64_MIN_AS_FLOAT <= f <= INT64_MAX_AS_FLOAT
    let inRange = sv.fp64 >= mkFloat64(-9.223372036854776e18) and
                  sv.fp64 <= mkFloat64( 9.223372036854776e18)
    # Out-of-range fork: emit sxRaised(RangeDefect)
    forkPath(not inRange):
      emitRaisedResult(path, "RangeDefect", isDefect = true)
    # Main path (in-range):
    let bv64 = toSbv[11, 53, 64](rmRTZ(), sv.fp64)
    liftBV(bv64, signed = true)
  ```
  The out-of-range fork follows the same `sxRaised(RangeDefect)`
  pattern used for out-of-bounds index access. `INT64_MIN_AS_FLOAT`
  and `INT64_MAX_AS_FLOAT` are Nim compile-time `float64` constants
  derived from `low(int64)` and `high(int64)`.

  `float32` conversions use `[8,24]` and the `int32` range bounds.
  `rmRNE()` and `rmRTZ()` are the zero-argument context-inferring
  forms from `z3/fp.nim`.

nim-z3 APIs: `intToBv` (`z3/bitvec.nim:746` — `Z3_mk_int2bv`),
`toFpFromSigned` (`Z3_mk_fpa_to_fp_signed`),
`toSbv` (`Z3_mk_fpa_to_sbv`), `rmRNE`, `rmRTZ`.

**DoD:**
- [ ] Both conversion direction tests pass with numerically correct
      witnesses.
- [ ] `float32(x: int32)` conversion test: `proc f(x: int32): bool =
      float32(x) > 1.5'f32` → SAT witness `x >= 2`.
- [ ] Edge-case test: `int(float(n)) == n` for `n` in a range
      where the round-trip is exact (small integers) → SAT.
- [ ] Out-of-range `int(f)` test: SUT `proc f(x: float): bool = int(x) == 0`
      with a path constraint that forces `x` to a value exceeding
      `INT64_MAX_AS_FLOAT` produces `sxRaised(RangeDefect)` on the
      out-of-range fork and `sxSat` on the in-range fork.
- [ ] `intToBv[64]` path confirmed: walker compiles and links
      (no "symValToBV64 undefined" error); the `svInt` → `Z3BitVec[64]`
      chain used in `iekConvIntToFloat` is unit-tested directly.
- [ ] All prior tests pass.

---

### F6 — math-module ops (`abs`, `sqrt`, `min`, `max`, `floor`, `ceil`, `round`); `signbit`; FP predicates; deferred ops

**What it does:** Adds symex models for the `std/math` functions
most commonly used in float-bearing SUTs. Z3 FP theory has native
support for `abs` (`Z3_mk_fpa_abs`), `sqrt`
(`Z3_mk_fpa_sqrt`, `rmRNE`), `min` (`Z3_mk_fpa_min`), and `max`
(`Z3_mk_fpa_max`). `floor`, `ceil`, and `round` are modeled via
`roundToIntegral` with the appropriate rounding mode: `rmRTN`
(toward negative infinity) for `floor`, `rmRTP` (toward positive
infinity) for `ceil`, `rmRNE` for `round`. Nim's `trunc` is
`roundToIntegral(rmRTZ(), a)`.

This cycle also adds four Z3 FP-native float-classification predicates
(Breadth-M2): `isNaN(f)` → `fpIsNaN` (`Z3_mk_fpa_is_nan`),
`isInf(f)` → `fpIsInfinite` (`Z3_mk_fpa_is_infinite`),
`isFinite(f)` → `not(fpIsNaN(f)) and not(fpIsInfinite(f))` (combination),
`isNormal(f)` → `fpIsNormal` (`Z3_mk_fpa_is_normal`). All four return
`Z3Bool`-backed `svBool` and participate in path conditions.

Additionally, this cycle covers `system.signbit(x)` → `fpIsNegative(sv.fp64)`.

`copySign` and `nextafter` emit `SymexErrorInfo{kind: feUnsupportedOp,
severity: sevError}` classified errors (Phase 16 backlog; see out-of-scope
table in preamble). `classify(f)` — Nim's `std/math.classify` returning
a `FloatClass` enum value — emits `feUnsupportedOp` (`severity: sevError`)
classified error; enum-classification modeling is deferred to Phase 16.
Both must emit a classified error per Invariant 3 — never silent UNSAT.

Any other `std/math` call encountered in a SUT that reaches the
walker emits `SymexErrorInfo{kind: feUnsupportedOp, op: "math.<name>",
severity: sevError}` per Invariant 3.

**RED test:** `tests/tsymex_phase15_F6_float_math.nim`, test names:
- `"math ops: symexFind witnesses sqrt and floor constraints"` —
  `proc f(x: float): bool = sqrt(x) > 2.0` → SAT with witness `x > 4.0`;
  `proc f(x: float): bool = floor(x) == 3.0` → SAT with witness in `[3.0, 4.0)`.
- `"isNaN predicate: proc f(x: float): bool = not isNaN(x) and x == x"` —
  produces `sxSat` with a finite witness (Breadth-M2 RED).
- `"classify(f) emits feUnsupportedOp"` — SUT `proc f(x: float): bool = classify(x) == fcNaN`
  produces `sxUnknown` with `errors[0].kind == feUnsupportedOp`.

**GREEN:** Files touched:

- `src/proptest/smt/stdlib_models.nim` — Add a `mathFpModels`
  table (or extend the existing call-dispatch table) mapping
  qualified call names to their walker implementations. Supported:
  `"abs"`, `"sqrt"`, `"min"`, `"max"`, `"floor"`, `"ceil"`,
  `"round"`, `"trunc"`, `"signbit"`, `"isNaN"`, `"isInf"`,
  `"isFinite"`, `"isNormal"`. Registered as unsupported (emit
  `feUnsupportedOp`): `"copySign"`, `"nextafter"`, `"classify"`.

  | Op | Z3 API | nim-z3 wrapper | Returns |
  |----|--------|----------------|---------|
  | `abs(x)` | `Z3_mk_fpa_abs` | `abs[E,S]` | `svFloat64` |
  | `sqrt(x)` | `Z3_mk_fpa_sqrt` | `sqrt[E,S]` (rmRNE) | `svFloat64` |
  | `min(x,y)` | `Z3_mk_fpa_min` | `min[E,S]` | `svFloat64` |
  | `max(x,y)` | `Z3_mk_fpa_max` | `max[E,S]` | `svFloat64` |
  | `floor(x)` | `Z3_mk_fpa_round_to_integral` | `roundToIntegral(rmRTN(), x)` | `svFloat64` |
  | `ceil(x)` | `Z3_mk_fpa_round_to_integral` | `roundToIntegral(rmRTP(), x)` | `svFloat64` |
  | `round(x)` | `Z3_mk_fpa_round_to_integral` | `roundToIntegral(rmRNE(), x)` | `svFloat64` |
  | `trunc(x)` | `Z3_mk_fpa_round_to_integral` | `roundToIntegral(rmRTZ(), x)` | `svFloat64` |
  | `signbit(x)` | `Z3_mk_fpa_is_negative` | `fpIsNegative[E,S]` | `svBool` |
  | `isNaN(x)` | `Z3_mk_fpa_is_nan` | `fpIsNaN[E,S]` | `svBool` |
  | `isInf(x)` | `Z3_mk_fpa_is_infinite` | `fpIsInfinite[E,S]` | `svBool` |
  | `isFinite(x)` | combination | `not fpIsNaN(x) and not fpIsInfinite(x)` | `svBool` |
  | `isNormal(x)` | `Z3_mk_fpa_is_normal` | `fpIsNormal[E,S]` | `svBool` |
  | `copySign(x,y)` | — | `feUnsupportedOp` (sevError) | — |
  | `nextafter(x,y)` | — | `feUnsupportedOp` (sevError) | — |
  | `classify(x)` | — | `feUnsupportedOp` (sevError) | — |

- `src/proptest/smt/runtime.nim` — In the call-dispatch path for
  math calls with a float receiver, look up the call name in
  `mathFpModels` before falling through to the `feUnsupportedOp`
  error. The lookup path mirrors the existing stdlib-modeled proc
  pattern. Symmetric for `svFloat32` using the `[8,24]` forms.

nim-z3 APIs: `abs[E,S]` (`Z3_mk_fpa_abs`), `sqrt[E,S]`
(`Z3_mk_fpa_sqrt`), `min[E,S]` (`Z3_mk_fpa_min`),
`max[E,S]` (`Z3_mk_fpa_max`), `roundToIntegral[E,S]`
(`Z3_mk_fpa_round_to_integral`), `fpIsNegative[E,S]`
(`Z3_mk_fpa_is_negative`), `fpIsNaN[E,S]` (`Z3_mk_fpa_is_nan`),
`fpIsInfinite[E,S]` (`Z3_mk_fpa_is_infinite`), `fpIsNormal[E,S]`
(`Z3_mk_fpa_is_normal`), `rmRTN`, `rmRTP`, `rmRTZ`.

**DoD:**
- [ ] `sqrt` and `floor` tests pass with correct witness bounds.
- [ ] `"math ops: unsupported math.log raises feUnsupportedOp"` —
      a SUT that calls `math.log(x)` produces `sxUnknown` with
      `errors` containing `{kind: feUnsupportedOp, op: "math.log"}`.
- [ ] `abs`, `min`, `max`, `ceil`, `round`, `trunc` each have at
      least one targeted test.
- [ ] `"signbit: proc f(x: float): bool = signbit(x)"` — SUT with
      `signbit` returns `sxSat` with a negative witness; `not signbit(x)`
      returns `sxSat` with a non-negative witness.
- [ ] `"isNaN predicate: proc f(x: float): bool = not isNaN(x) and x == x"` —
      produces `sxSat` with a finite (non-NaN) witness; `fpIsNaN`
      dispatch confirmed via `errors` being empty on success path.
- [ ] `"isInf predicate: proc f(x: float): bool = isInf(x)"` —
      produces `sxSat` with an infinite witness.
- [ ] `"isFinite combination: proc f(x: float): bool = isFinite(x) and x > 1.0"` —
      produces `sxSat` with a finite witness > 1.0.
- [ ] `"isNormal predicate: proc f(x: float): bool = isNormal(x)"` —
      produces `sxSat` with a normal (non-zero, non-subnormal, non-NaN,
      non-Inf) witness.
- [ ] `"classify(f) emits feUnsupportedOp"` — SUT calling `classify(x)`
      yields `sxUnknown` with `errors[0].kind == feUnsupportedOp` and
      `errors[0].severity == sevError`.
- [ ] `"copySign emits feUnsupportedOp"` — SUT calling `copySign(x, y)`
      yields `sxUnknown` with `errors[0].kind == feUnsupportedOp`.
- [ ] `"nextafter emits feUnsupportedOp"` — same pattern.
- [ ] All prior tests pass.

---

### F7 — eval-side extraction: float witness round-trip

**What it does:** Replaces the F1 stub in `extractLeaf` with the
real bit-exact extraction path. When Z3 returns a model, the
walker evaluates each `svFloat32`/`svFloat64` SymVal through
`m.evalFloat64Opt`/`m.evalFloat32Opt` (nim-z3's
`fpBitsToUint64`-backed extractors) and stores the result in new
`float32Vals`/`float64Vals` tables on `RawWitness`. The witness
emitter (`symex.nim`) reads from these tables via `readFloat` and
`readFloat32` helper procs. Special values (NaN, ±Inf, ±0) are
preserved exactly — the `toFloat64`/`toFloat32` path uses
`Z3_mk_fpa_to_ieee_bv` + `Z3_get_numeral_uint64` + `cast`, which
is lossless for all IEEE 754 bit patterns including NaN payloads
(though proptest models only a single canonical NaN per
ADR-0005).

**Depth-H1 — NaN extraction via model_completion.** For float
expressions derived from array element access (`Z3_mk_select`-derived
ASTs) the model may return an unevaluated `select` expression rather
than a concrete FP numeral. To guarantee NaN round-trips correctly
through any `Z3_mk_select`-derived float AST, the extraction path
explicitly calls `model.eval(expr, model_completion=true)` before
`fpBitsToUint64` — not just for direct FP variables but for all float
ASTs passed to `evalFloat64Opt`/`evalFloat32Opt`. nim-z3's
`evalFloat64Opt` already accepts the `modelCompletion` flag; F7
ensures it is **always set to `true`** in `extractLeaf`, eliminating
the unevaluated-select hazard for array-derived floats.

**RED test:** `tests/tsymex_phase15_F7_float_extract.nim`, test
name `"float extraction: witness bit-pattern round-trip for float64"`.
Specifies: for a SUT `proc f(x: float): bool = x == 3.14`,
`symexFind` returns `sxSat` and the extracted witness satisfies
`w == 3.14` (exact float64 equality, not approximate).

**GREEN:** Files touched:

- `src/proptest/smt/runtime.nim` — Extend `RawWitness` with two
  new tables:
  ```nim
  float32Vals: Table[string, float32]
  float64Vals: Table[string, float64]
  ```
  Replace the F1 stub in `extractLeaf` with:
  ```nim
  of svFloat64:
    let evaled = m.eval(sv.fp64.raw, modelCompletion = true)
    let opt = m.evalFloat64Opt(Z3Float64(raw: evaled))
    w.float64Vals[path] = opt.get(float64(0.0))
  of svFloat32:
    let evaled = m.eval(sv.fp32.raw, modelCompletion = true)
    let opt = m.evalFloat32Opt(Z3Float32(raw: evaled))
    w.float32Vals[path] = opt.get(float32(0.0))
  ```
  The explicit `model.eval(..., modelCompletion=true)` step forces
  Z3 to resolve any `Z3_mk_select`-derived float ASTs to concrete
  FP numerals before `fpBitsToUint64` is called. Without this,
  array-extracted NaN elements may fail to round-trip. If `opt` is
  `none` after the forced eval (should not happen on a SAT model
  with `modelCompletion=true`), log a `SymexErrorInfo{kind:
  feExtractionFailed, severity: sevError}` and store `0.0` as the
  fallback.

- `src/proptest/symex.nim` — Remove F1 stubs; implement
  `readFloat(w: RawWitness, path: string): float` and
  `readFloat32(w: RawWitness, path: string): float32` as helper
  procs that index into `w.float64Vals`/`w.float32Vals`; extend
  `primTyAndReader` to emit these names:
  ```nim
  of itFloat32: ("float32", "readFloat32")
  of itFloat64: ("float",   "readFloat")
  ```

- `src/proptest/smt/canonicalize.nim` — Extend the rendering of
  `RawWitness` for choice-sequence generation (seed replay) to
  include float values. Float witness rendering uses Nim's `$`
  on the `float`/`float32` with enough precision to round-trip:
  `formatFloat(v, ffDefault, 17)` for `float64` and
  `formatFloat(float64(v), ffDefault, 9)` for `float32`.

nim-z3 APIs: `evalFloat64Opt` (wraps `fpBitsToUint64` →
`Z3_mk_fpa_to_ieee_bv` + `Z3_simplify` + `Z3_get_numeral_uint64`
+ `cast[float64]`; `modelCompletion` parameter controls
`Z3_model_eval` forcing), `evalFloat32Opt` (same, via `uint32` cast),
`m.eval(ast, modelCompletion: bool)` (nim-z3 `model.nim`).

**DoD:**
- [ ] `"float extraction: witness bit-pattern round-trip for
      float64"` passes with exact equality.
- [ ] `"float extraction: NaN witness extracted and round-tripped"` —
      SUT `proc f(x: float): bool = not (x == x)` (satisfied only
      by NaN); the extracted witness is NaN (verified via
      `classify(w) == fcNaN`). **This is the bit-pattern check
      deferred from F4 DoD.** The combined assertion: F4 confirms
      `sxSat`; F7 confirms the extracted witness bit-pattern is NaN.
- [ ] `"float extraction: ±Inf witnesses extracted correctly"`.
- [ ] `float32` parallel tests at reduced precision.
- [ ] `model.eval(expr, modelCompletion=true)` is confirmed to be
      called for every float extraction in `extractLeaf` (code-review
      assertion; no conditional fallback without `modelCompletion`).
- [ ] All prior tests pass.

---

### F8 — regression smoke + arbitrary float64 SUT round-trip property

**What it does:** Re-runs the full prior-cluster test suite
(Cluster L + all earlier Phase-15 clusters) under the post-F7
walker to catch state-threading bugs from the multi-file edits in
F1–F7. Adds a property-test that generates arbitrary `float64`
SUTs (with varied arithmetic, comparison, and conversion
constraints) and verifies that the symex engine round-trips each
one: witnesses produced by `symexFind` satisfy the SUT's body
when plugged back in, and witnesses produced under the negated
body satisfy the negation.

**RED test:** `tests/tsymex_phase15_F8_smoke.nim`, test name
`"F-cluster smoke: all L-cluster and prior phase-15 tests still
pass under float-extended walker"`. And: `"float64 round-trip
property: symexFind witness satisfies SUT at runtime"`. The
round-trip property is checked for at least 20 SUT shapes
(pure arithmetic threshold, comparison, conversion, math-op) via
a hand-enumerated suite (not a PBT-of-PBT loop, to keep the test
hermetic).

**GREEN:** No new source files expected. Possible fixes to
`src/proptest/smt/canonicalize.nim`, `dsl_parser.nim`, or
`symex.nim` if the smoke uncovers regressions (the cycle budget
is reserved for fix work). The round-trip property test file is
the only addition.

**DoD:**
- [ ] All ~76 pre-F-cluster test files pass unchanged (no new
      failures introduced by float plumbing in shared dispatch
      tables).
- [ ] The 20-shape round-trip property suite passes: each
      `symexFind` SAT witness satisfies the SUT body at Nim
      runtime; each UNSAT verdict is confirmed by checking that
      no witness in a bounded search space satisfies the SUT.
- [ ] `SymexErrorInfo{kind: feUnsupportedOp}` is confirmed to be
      the only non-zero error kind for the intentionally-broken
      SUT shape (unsupported math function) — no silent fallback
      to empty-errors `sxUnknown`.
- [ ] **Walker version bumped `"4"→"5"` atomically as the last
      step of F8.** The bump is committed in a single edit to the
      `walkerVersion` constant in `src/proptest/smt/canonicalize.nim`
      (single source of truth; M12/Breadth-LOW-L5) after the full
      regression smoke is green. **`canonicalize.walkerVersion == "5"`**
      is asserted in the smoke test. Per v2 Invariant 1, every cluster
      ends with its own version bump to eliminate stale-cache risk
      during the multi-cluster /loop session. No further float-cluster
      cycle may land after the bump without first confirming the new
      version is in effect.
- [ ] `determinism.md` updated: float section added covering the
      `float`/`float32`/`float64` type-bridge, ADR-0005 NaN/Inf
      summary, the rounding-mode choices from F3/F5, and the
      `float64Vals`/`float32Vals` witness table additions.
- [ ] **`withSymexSettings` wiring confirmed.** F8 smoke includes
      a test: `withSymexSettings(defaultSettings()) do (s: var SymexSettings):
      s.inlinePolicy = ipAlwaysAxiomatize` applied to a float SUT
      produces `sxSat` (the settings builder compiles and threads
      through `runSymex` correctly). This confirms the public
      `withSymexSettings` API wires through before Cluster C
      depends on it (H15).
- [ ] `docs/symex/ADR-0005-float-nan-inf.md` confirmed on disk
      (closing check for F0-ADR).

---

### F9a — array element type-bridge audit + NaN extraction

**What it does:** Verifies that `classifyType` correctly handles
`array[N, float32]` and `array[N, float64]` element types, and
that the existing array walker (Phase 4) accepts `svFloat32`/`svFloat64`
element kinds without sort-mismatch errors. F9a is a completeness
check — no new walker machinery is expected, only confirmation that
the F1 additions slot cleanly into the array walker's existing
element-dispatch path.

Additionally (Depth-H1 array-NaN), F9a adds the NaN extraction test
for array-derived floats: a SUT whose array element is NaN must
produce a witness where the extracted element classifies as `fcNaN`
via the `model_completion=true` extraction path confirmed in F7.

Specifically: (1) `classifyType` on `array[4, float64]` produces an
`itArray(itFloat64, 4)` IR type; (2) the walker's element-access path
(`iekArrayGet`) for `svFloat64`-typed elements returns a `svFloat64`
SymVal without a sort-mismatch assertion failure; (3) a SUT that
reads a float64 from an array position and constrains it participates
in a satisfiable Z3 query with a witness; (4) an array-element NaN
witness round-trips correctly via `model_completion=true`.

**RED test:** `tests/tsymex_phase15_F9a_array_float.nim`, test names:
- `"array[4, float64] SUT: element access returns svFloat64 witness"` —
  `proc f(xs: array[4, float64]): bool = xs[2] > 0.0` → `sxSat`.
- `"array[4, float64] SUT: NaN element extraction via model_completion"` —
  `proc f(xs: array[4, float64]): bool = not (xs[0] == xs[0])` (NaN path)
  → `sxSat` with extracted `xs[0]` classifying as `fcNaN`.

**GREEN:** No new source files expected. If gaps exist:

- `src/proptest/smt/dsl_typebridge.nim` — extend `classifyType`'s
  array element dispatch to correctly route `float`, `float32`,
  `float64` element types to `itFloat64`/`itFloat32` (not an
  `itUnknown` fallthrough).

- `src/proptest/smt/runtime.nim` — Confirm the `iekArrayGet` path's
  element-extraction branch handles `of svFloat32, svFloat64:` without
  an `unreachable` or `raise` stub. If a stub exists from F1's
  exhaustive-dispatch sweep, remove it and add the real dispatch.

- `src/proptest/smt/canonicalize.nim` — Confirm that the array
  witness canonicalization path visits `float32Vals`/`float64Vals`
  alongside `intVals`/`boolVals`. Fix if needed.

nim-z3 APIs: no new APIs. Float sort identity (`Z3Float32`/`Z3Float64`)
is already established in F1; the array sort `Z3_mk_array_sort(domain, range)`
uses the element sort directly.

**DoD:**
- [ ] `"array[4, float64] SUT: element access returns svFloat64 witness"` passes;
      the witness array has a positive `float64` at index 2.
- [ ] `array[4, float32]` parallel test passes.
- [ ] `"array[4, float64] SUT: NaN element extraction via model_completion"` —
      array-extracted NaN element classifies as `fcNaN` at Nim runtime
      (confirms `model_completion=true` path in F7 works for `Z3_mk_select`-
      derived float ASTs).
- [ ] Sort-mismatch assertion error does not occur when a float array
      element is accessed via `iekArrayGet` (regression guard).
- [ ] `classifyType("array[4, float64]")` produces `itArray(itFloat64, 4)`
      in a unit test (confirms the type-bridge path is complete).
- [ ] All prior F-cluster tests pass (regression within cluster).

---

### F9b — `seq[float32/64]` SUT parameter type

**What it does:** Extends the symex engine to accept `seq[float32]`
and `seq[float64]` as SUT parameter types. This requires: (1)
`allocateSym(itSeq{itFloat64})` dispatches to a float-element seq
allocation (analogous to `itSeq{itInt}` for integer seqs); (2)
`extractLeaf` for seq-of-float elements populates `float64Vals`/
`float32Vals` tables (analogous to `intVals` for integer seq elements);
(3) `emitTyAndReader(itSeq{itFloat64})` produces correct Nim
reconstruction code using `readFloat`/`readFloat32`.

**RED test:** `tests/tsymex_phase15_F9b_seq_float.nim`, test names:
- `"seq[float64] SUT: NaN element witness"` — RED: SUT
  `proc f(xs: seq[float64]): bool = xs[0] != xs[0]` (satisfied only
  when `xs[0]` is NaN) → `sxSat` with a NaN witness in `xs[0]`
  (Breadth-H2 RED). Fails before GREEN.
- `"seq[float32] SUT: basic constraint"` — `proc f(xs: seq[float32]):
  bool = xs[0] > 1.0'f32` → `sxSat`.

**GREEN:** Files touched:

- `src/proptest/smt/runtime.nim` — Extend `allocateSym` dispatch:
  ```nim
  of itSeq:
    case e.elemKind
    of itFloat64: allocateSeqSymFloat64(baseName, path)
    of itFloat32: allocateSeqSymFloat32(baseName, path)
    # ... existing int/bool cases
  ```
  Extend `extractLeaf` to populate `w.float64Vals`/`w.float32Vals`
  for seq-of-float element paths, using the `model_completion=true`
  extraction established in F7.

- `src/proptest/symex.nim` — Extend `emitTyAndReader` with:
  ```nim
  of itSeq:
    case e.elemKind
    of itFloat64: ("seq[float]",   "readSeqFloat64")
    of itFloat32: ("seq[float32]", "readSeqFloat32")
  ```
  Implement `readSeqFloat64`/`readSeqFloat32` helper procs that
  reconstruct a seq from the `float64Vals`/`float32Vals` subtables
  for the seq's path prefix (analogous to `readSeqInt`).

nim-z3 APIs: no new APIs. Seq elements use the same float sort and
extraction path as scalar float parameters.

**DoD:**
- [ ] `"seq[float64] SUT: NaN element witness"` — RED→GREEN confirmed;
      `xs[0] != xs[0]` produces `sxSat` with extracted `xs[0]`
      classifying as `fcNaN`.
- [ ] `"seq[float32] SUT: basic constraint"` passes.
- [ ] `"seq[float64] SUT: multi-element constraint"` — `proc f(xs:
      seq[float64]): bool = xs[0] < xs[1]` → `sxSat` with witnesses
      satisfying the ordering.
- [ ] `emitTyAndReader(itSeq{itFloat64})` produces correct
      reconstruction code (unit test on the macro output or compile
      check).
- [ ] `float32` and `float64` both work end-to-end.
- [ ] All prior F-cluster tests pass.

---

### F9c — `object variant` arm fields of type `float32/64`

**What it does:** Audits and extends the `object variant` walker
(existing Phase support) to correctly handle variant arms where a
field has type `float32` or `float64`. The discriminant is an
existing type (`bool` or `enum`); the arm fields are the new territory.
This covers: (1) `allocateSym` for variant types with float arm
fields correctly initializes `svFloat32`/`svFloat64` SymVals in the
arm's field table; (2) extraction populates `float64Vals`/`float32Vals`
for the active arm's fields; (3) the witness round-trips both arms
correctly (one arm with float field, one without).

**RED test:** `tests/tsymex_phase15_F9c_variant_float.nim`, test names:
- `"variant with float arm: sxSat witnesses both arms"` — SUT:
  ```nim
  type V = object
    case k: bool
    of true:  x: float64
    of false: y: int
  proc f(v: V): bool = (if v.k: v.x > 0.0 else: v.y < 0)
  ```
  `symexFind` returns `sxSat` twice (once for each arm); the
  `true`-arm witness has `v.x > 0.0`; the `false`-arm witness
  has `v.y < 0`. Breadth-H3.

**GREEN:** Files touched (if gaps exist):

- `src/proptest/smt/runtime.nim` — Extend the variant arm
  field-allocation dispatch to handle `itFloat32`/`itFloat64` field
  types alongside the existing `itInt`/`itBool` cases. Extend
  `extractLeaf` variant path to populate float tables for active arm.

- `src/proptest/smt/dsl_typebridge.nim` — Confirm `classifyType`
  on a variant type with float arm fields produces the correct
  `itVariant` with `itFloat64`/`itFloat32` arm field types. Fix if
  it falls through to `itUnknown`.

nim-z3 APIs: no new APIs.

**DoD:**
- [ ] `"variant with float arm: sxSat witnesses both arms"` passes;
      both the `true`-arm (float64 field) and `false`-arm (int field)
      witnesses are correct and distinct.
- [ ] `float32` variant arm test passes in parallel.
- [ ] Extraction populates `float64Vals` for active arm fields (confirmed
      by witness containing non-default float values for the arm field).
- [ ] `classifyType` on the variant type produces `itVariant` with
      correct arm field types (unit test).
- [ ] All prior F-cluster tests pass.

<!-- CLUSTER_S -->
## Cluster S — full strings

Cluster S promotes the symex engine's `string` support from the bounded,
operationally narrow Phase 5 state — where `string` is a Z3 free variable
that participates in equality and table-key indexing but nothing more — to the
full Z3 String + Regex theory surface. Fifteen cycles carry the type-bridge
migration, literal lifts, every Nim `string` stdlib op with a Z3 equivalent,
byte-level escape via `bytes(s)`, concatenation, case-conversion
classification, int/string conversion, and string mutation classification.
(S0-ADR + S1–S9 + S10a + S10b + S11, with S6 split into S6a/S6b and S10 split
into S10a/S10b.)

**ADR-0006 in cluster context (amended).** Z3's String sort is
codepoint-native: `len` counts Unicode scalar values, `at(s, i)` returns a
single-codepoint string, and `substr` offsets are codepoint positions. Cluster
S adopts this model unchanged. **ADR-0006 amendment**: `mkString(nimStr)`
produces a Z3 String whose Z3-side `len` equals `nimStr.runeLen` (Unicode
codepoint count), **not** `nimStr.len` (byte count). For multi-byte literals
such as `"é"` (2 bytes, 1 codepoint), `mkString("é").len` is 1 in Z3 and 2
at Nim runtime. This divergence is intentional and documented; the symbolic
model uses codepoint semantics uniformly. Nim's native `string` is UTF-8
bytes, meaning a Nim programmer who writes `s[2]` gets the byte at offset 2,
not the third codepoint. The engine's symbolic model must pick one of these
semantics; ADR-0006 picks codepoint-indexed as the canonical model for two
reasons: (1) Z3 provides it natively with no encoding overhead, and (2)
byte-indexed witnesses would require Z3 to reason about multi-byte codepoint
boundaries, producing a class of off-by-one bugs that the engine would fail to
detect. Users who need byte-level access have an explicit opt-in: the
`bytes(s)` DSL lift (cycle S7a) returns a `seq[byte]` SymVal that models the
raw UTF-8 encoding. The codepoint/byte distinction is surfaced in witness
output and in `determinism.md` so property-test authors are never silently
surprised.

**Open question 3 (cstring interop) — closed: deferred to Phase 16.** `cstring`
is FFI surface; FFI is excluded from Phase 15 by the scope section. Any Nim
SUT that takes a `cstring` parameter receives a parse-time `error()` with a
clear diagnostic pointing at the Phase 16 backlog. No silent fallbacks.

**Z3 4.15.0 version-gating policy.** The dev toolchain ships Z3 4.15.0
(Tumbleweed `z3-4.15.0-1.3`). `Z3_mk_seq_replace_all` and
`Z3_mk_seq_re_replace_all` are absent from this version; they landed upstream
in commit `fc7660d0` (Z3 4.15.5, 2025-11-04). Both are already gated in
nim-z3 under `when defined(z3WithSeqReplaceAll)` / `when
defined(z3WithSeqReplaceRe)`. Cluster S maps this build-time gate to a
runtime version probe: at walker startup, if `replaceAll` or regex-replace
path is needed and the probe fails, the walker emits `SymexErrorInfo{kind:
seZ3VersionMissing, msg: "replaceAll requires Z3 >= 4.15.5; current build
lacks Z3_mk_seq_replace_all"}` and the path yields `sxUnknown` (cached under
`:unknown`). This is Invariant 3 (no silent fallbacks) applied to the version
boundary: the error is classified, structured, and routed through the standard
`errors: seq[SymexErrorInfo]` accumulator. Consumers can treat
`seZ3VersionMissing` as fatal at their report-policy layer.

**Migration risk and S7b regression smoke.** Phase 5 shipped `itString` /
`svString` backed by `mkStringVar` / `mkString` / `evalStr` — the same Z3
String APIs Cluster S builds on. The type-bridge (S1) does not replace that
foundation; it extends the walker to handle the full string op surface.
Existing tests that use `string`-typed SUTs exercise the `svString` allocation
and extraction paths; S7b's regression smoke re-runs them under the full
Cluster S walker (through S7a) to confirm the S1–S7a additions leave those
paths intact. S7b also performs a Cluster F cross-cluster smoke to catch
state-threading bugs introduced by the shared `runtime.nim` edits.

**Out of scope for this cluster.** The following operations have no sound Z3
String theory encoding at Phase 15 depth. Each is classified at parse time and
produces a structured error; none is silently ignored.

| Operation | Classified error kind | Notes |
|-----------|----------------------|-------|
| `toLower`, `toUpper` | `seUnsupportedStringOp` | No Z3 native; regex-range approximation backlog Phase 16 |
| `s.high` | `seByteIndexUnsupported` | Nim byte-index semantics; codepoint model incompatible |
| `for c in s` | `seByteIterUnsupported` | Nim byte iterator; codepoint model incompatible |
| `s[i] = c` | `seUnsupportedStringOp` | Byte-index mutation; sound model via `bytes(s)` deferred Phase 16 |
| `s.add(c)` | `seUnsupportedStringOp` | Byte append; may produce partial UTF-8 codepoint |
| byte-indexing ops | `seByteIndexUnsupported` | Any Nim byte-offset API on `string` |
| `Table[string, V]` where V ∉ {int} | `seUnsupportedTableValType` | Emitted at parse time via `dsl_typebridge.nim`; V=int is the only supported value type |
| `s[i] in mySet` where `mySet: set[char]` | `seUnsupportedSetCharInterop` | Codepoint (Z3Int) / BV8 (`svBV8`) mismatch; set-of-char interop deferred Phase 16 |
| `seq[seq[T]]` | `seNestedSeqUnsupported` | Nested sequence types unsupported at all walker levels |

**New classified error kinds introduced in this cluster preamble (emitted at parse time):**

- `seUnsupportedTableValType` — `Table[string, V]` where V ∉ {int}; emitted by `dsl_typebridge.nim` during type-bridge sweep. Invariant: any `Table[string, V]` SUT param with V not an integral type is rejected before any Z3 query is issued.
- `seUnsupportedSetCharInterop` — `s[i] in mySet` where `mySet: set[char]`; codepoint vs BV8 mismatch; classified at parse time.
- `seNestedSeqUnsupported` — `seq[seq[T]]` for any T; nested sequence types unsupported at all walker levels; classified at parse time.

### Cluster S — cycle table

| Cycle | Topic | Key files | Key dependency |
|-------|-------|-----------|----------------|
| S0-ADR | Author `docs/symex/ADR-0006-string-codepoint-indexing.md`; no RED test (doc-authoring cycle) | `docs/symex/ADR-0006-string-codepoint-indexing.md` | Preamble text present |
| S1 | Type-bridge migration: `string` param → full Z3 String walker; `iekStr*` IR stubs; `iekSeqLen`→`iekStrLen` routing guard | `types.nim`, `stdlib_models.nim`, `dsl_parser.nim` | Phase 5 `itString`/`svString` baseline |
| S2 | String literal lifts: `""`, `"hello"`, embedded escapes; multi-byte codepoint/byte divergence documented | `dsl_parser.nim`, `runtime.nim` | S1 IR stubs present |
| S3 | `s.len`, `s[i]`, `s[a..b]`; `s.high` → `seByteIndexUnsupported`; `for c in s` → `seByteIterUnsupported` | `stdlib_models.nim`, `dsl_parser.nim`, `runtime.nim` | S1 guard; ADR-0006 codepoint model |
| S4 | `find`, `contains`, `startsWith`, `endsWith` | `stdlib_models.nim`, `dsl_parser.nim`, `runtime.nim` | S3 (`iekStrLen` guard landed) |
| S5 | `replace`, `replaceAll`, `split`, `join`; `maxSplitParts` setting; sep-non-substring ∀-constraint; empty-sep special case; concrete-string+single-char-sep inline enumeration | `symex_settings.nim`, `stdlib_models.nim`, `runtime.nim`, `dsl_parser.nim` | S4; `SymexSettings` |
| S6a | `regex_parser.nim` standalone: literal, `.`, `[a-z]`, `*`, `+`, `?`, `\|`, `()`, `{n,m}`, `\d`, `\w`, `\s`, `[^...]`, `(?:...)`; rejects backrefs/lookahead/named-groups | `regex_parser.nim`, `tests/smt/tregex_parser.nim` | S5; `z3/regex` |
| S6b | Walker integration: `iekStrMatch`/`iekStrFindRe` dispatch in `runtime.nim`; `parseNimRegexToZ3Regex` from S6a | `types.nim`, `dsl_parser.nim`, `runtime.nim` | S6a |
| S7a | `bytes(s)` UTF-8 BMP encoding: Z3 `ite`-branched BV arithmetic; `maxBytesEncodingLen` cap → `seBytesLengthTooLarge`; symbolic-length guard → `seBytesSymbolicLength` | `types.nim`, `dsl_parser.nim`, `runtime.nim` | S6b; `z3/strings.toCode` |
| S7b | Z3-string-theory regression smoke (L + F + S1–S7a); `determinism.md` update | `tests/symex/tphase15_S7b_smoke.nim`, `docs/symex/determinism.md` | S7a complete |
| S8 | `&` string concatenation → `Z3_mk_seq_concat` | `types.nim`, `dsl_parser.nim`, `runtime.nim` | S7b green |
| S9 | `toLower`/`toUpper` → `seUnsupportedStringOp` classified error | `dsl_parser.nim`, `runtime.nim` | S8 |
| S10a | `$int`/`parseInt` digits-path; negative-string `"-"` prefix ITE; `seParseIntPreE` hint; explicit unsoundness window | `dsl_parser.nim`, `runtime.nim` | S9; `z3/strings` int-interop |
| S10b | `parseInt` raises-path fork: `sxRaised(ValueError)` for non-digit; `$float`/`parseFloat` → `seUnsupportedStringOp`; **depends on E1** | `runtime.nim` | S10a; E1 landed |
| S11 | String mutation (`s[i]=c`, `s.add(c)`) → `seUnsupportedStringOp`; `determinism.md`; walker version bump `"5"`→`"6"` | `dsl_parser.nim`, `runtime.nim`, `canonicalize.nim`, `docs/symex/determinism.md` | S10b |

---

### S0-ADR — `ADR-0006-string-codepoint-indexing.md`

**What it does:** Authors the formal architecture decision record for Cluster
S's foundational design choice: codepoint-indexed Z3 String semantics over
byte-indexed Nim string semantics. This is a doc-authoring cycle; there is no
RED test and no GREEN production-code edit. The ADR is the definitive reference
document for all string-model questions across S1–S11.

**ADR structure** (matching ADR-0001..ADR-0004 depth):

- **Status:** Accepted
- **Date:** (cycle authoring date)
- **Context:** Nim's native `string` type is a mutable, UTF-8-encoded byte
  sequence. Z3's `String` sort is a sequence of Unicode scalar values
  (codepoints). The two models diverge on: `s.len` (byte count vs codepoint
  count); `s[i]` (byte at offset vs codepoint-string at codepoint position);
  iteration (`for c in s` yields `char`/byte vs codepoint-string per Z3 `at`);
  multi-byte literals (`"é"` has `len == 2` in Nim, `len == 1` in Z3).
- **Decision:** Cluster S adopts Z3 codepoint semantics unchanged. `mkString(nimStr)`
  calls `Z3_mk_lstring(ctx, nimStr.len, nimStr.cstring)`, which Z3 interprets
  as codepoints; for ASCII-only strings the two models agree. For multi-byte
  codepoints the Z3-side `len` equals `nimStr.runeLen`, not `nimStr.len`. This
  is intentional and documented at every use site.
- **`mkString(nimStr)` codepoint clarification:** `mkString("é")` produces a
  Z3 String of codepoint-length 1 (U+00E9). Any constraint asserting
  `len(mkString("é")) == 2` is UNSAT. Property-test authors writing string
  witnesses with multi-byte codepoints must use codepoint counts in all `len`
  constraints.
- **`s.high` and `for c in s` deferral:** Both are byte-offset operations in
  Nim. Sound symbolic modeling of byte offsets requires the `bytes(s)` lifting
  (S7a), which is a codepoint→bytes translation. Using `s.high` or `for c in s`
  directly in a SUT produces `seByteIndexUnsupported` / `seByteIterUnsupported`
  classified errors. Full byte-iterator support deferred to Phase 16.
- **Rejected alternatives:**
  - *BV8-sequence model:* Represent `string` as `Z3Seq[Z3BV8]` mirroring Nim
    bytes. Rejected because Z3's String theory quantifier support, regex
    membership, and `toInt`/`toStr` conversions are defined on the String sort
    only; a BV8-sequence model loses all these operations and requires manual
    re-encoding.
  - *Hybrid model (detect byte vs codepoint context at parse time):* Rejected
    because it produces two incompatible constraint sets for the same `string`
    variable depending on which operation is observed first; unsound and
    complex.
  - *Warn-and-continue with byte semantics:* Rejected per Invariant 3; silent
    model divergence is never acceptable.
- **Consequences:**
  - All Z3-side `len` results are codepoint counts. Witnesses for `string`
    params report codepoint-indexed positions.
  - `bytes(s)` (S7a) is the explicit byte-level escape hatch; it lowers to a
    `seq[byte]` SymVal with UTF-8 BMP constraints.
  - `determinism.md` documents the codepoint/byte split for property-test
    authors.

**DoD:**
- [ ] `docs/symex/ADR-0006-string-codepoint-indexing.md` authored and matches the structure above.
- [ ] ADR references all four rejected alternatives with reasoning.
- [ ] ADR is indexed in the ADR index table (if present in the top matter or cross-cluster section).
- [ ] No production-code changes in this cycle.

---

### S1 — type-bridge migration: `string` param → full Z3 String walker

**What it does:** Audits and documents the delta between the Phase 5 bounded
`string` handling and the full Z3 String model; confirms that `allocateSym`
for `itString` already emits `mkStringVar`, that `extractLeaf` already calls
`evalStr`, and establishes the baseline walker path. Any gap between the Phase
5 stub and the full model is made explicit: stubs in `stdlib_models.nim` for
the new string operation kinds (`smkStrLen`, `smkStrIndex`, `smkStrFind`,
`smkStrContains`, `smkStrStartsWith`, `smkStrEndsWith`, `smkStrReplace`,
`smkStrReplaceAll`, `smkStrSplit`, `smkStrJoin`, `smkStrAt`, `smkStrSubstr`,
`smkStrMatch`, `smkStrBytes`) are stubbed as `smkUnregistered` and new
`iekStr*` IR expression kinds are defined in `types.nim` for the ops S2–S11
will fill in one cycle at a time.

**RED test:** `tests/symex/tphase15_S1_typebridge.nim`, test name
`"string SUT param: walker accepts, Z3 returns model, evalStr extracts Nim string"`.
Specifies: a one-param SUT `proc f(s: string)` with a `symexTarget` gated on
`s == "hello"` is handed to `symexFind`; the result is `sxSat` with witness
string equal to `"hello"`. A second test verifies a SUT gated on `s.len > 3`
fails parse with `isUnsupported` and not a crash — establishing the clean
parser boundary before S3 lands.

**GREEN:**
- `src/proptest/smt/types.nim` — new `IEKind` variants:
  `iekStrLen`, `iekStrAt`, `iekStrSubstr`, `iekStrFind`, `iekStrContains`,
  `iekStrStartsWith`, `iekStrEndsWith`, `iekStrReplace`, `iekStrReplaceAll`,
  `iekStrSplit`, `iekStrJoin`, `iekStrMatch`, `iekStrBytes`, `iekStrConcat`,
  `iekStrUnsupported`, `iekIntToStr`, `iekStrToInt`. Matching `of iekStr*:`
  stubs in `render`, `canonicalize`, and `IRExpr.==`.
- `src/proptest/smt/stdlib_models.nim` — new `StdlibModelKind` variants
  for each string op; `getStdlibModelFor` extended with `of itString:` dispatch
  branch (all variants return `smkUnregistered` until S2–S10 flesh them out).
- `src/proptest/smt/dsl_parser.nim` — audit: `getStdlibModelFor` called for
  `itString` receiver; parser emits `isUnsupported` with a clear diagnostic
  for unrecognised string calls. No semantic change for the `==` / literal path.
  **`string.len` routing guard**: audit `parseExpr` for `nnkDotExpr` where the
  receiver type is `itString` and the method name is `"len"`. If the current
  code routes to `iekSeqLen`, add an explicit guard that routes to `iekStrLen`
  instead (stubbed to `isUnsupported` until S3 fleshes it out). This prevents a
  Z3 sort mismatch crash when `iekSeqLen` is lowered with a `Z3String` operand.
- nim-z3 APIs used: `mkStringVar`, `mkString`, `evalStr` (already present;
  confirmed via `strings.nim` read).

**DoD:**
- [ ] `tphase15_S1_typebridge.nim` passes in the proptest dev container (`nimlang/nim:2.2.0` + Z3 4.15.0).
- [ ] `s.len > 3` on an `itString` receiver emits `isUnsupported` (not a sort-mismatch crash).
- [ ] All existing `tphase5_*.nim` and `tphase14_*.nim` tests remain green (no type regression from stub additions).
- [ ] `types.nim` compiles cleanly with every new `iek*` stub having an `of` branch in every `case e.kind` dispatch.

---

### S2 — string literal lifts: `""`, `"hello"`, embedded escapes

**What it does:** Extends the parser to recognise string-literal expressions
in SUT bodies and lower them through the already-present `iekStrLit` →
`mkString(e.sval)` path. Validates round-trip: Z3 solves a constraint of the
form `s == "hello"`, `evalStr` extracts `"hello"`, and the witness renders
correctly. Also covers the empty string and strings with Nim escape sequences
(`"\n"`, `"\t"`, `"\x61"`), which `Z3_mk_lstring` handles natively (NUL-safe
length-prefixed encoding). The ADR-0006 codepoint/byte divergence is
explicitly exercised and documented here.

**RED test:** `tests/symex/tphase15_S2_strlit.nim`, test name
`"string literal: \"hello\" round-trips through Z3 model"`. Additional tests:
`"empty string literal is SAT"`, `"embedded newline escape preserved in witness"`.
Specifies: `s == "hello"` is SAT; `s == ""` is SAT with empty witness string;
`s == "\n"` is SAT with witness `"\n"`. A negative test: a SUT asserting
`s == "hello"` and `s == "world"` simultaneously is UNSAT.
**Multi-byte literal test (ADR-0006 amendment)**: `s == "é"` (1 codepoint, 2
bytes) with `s.len == 1` produces `sxSat` — confirming Z3 codepoint length is
1, not 2. This test must be included in the RED suite.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim` — confirm `nnkStrLit` → `mkStrLit(e.strVal)`.
  Embedded escapes: Nim semchecker has already evaluated escape sequences;
  `strVal` is the decoded string, so no additional handling needed.
  Parser validates: `nnkTripleStrLit` also produces a clean `iekStrLit`.
- `src/proptest/smt/runtime.nim` — the existing `of iekStrLit: SymVal(kind: svString, str: mkString(e.sval))` branch is confirmed correct; no change needed.
  **Codepoint/byte divergence**: `mkString(nimStr)` passes the raw UTF-8 bytes
  via `Z3_mk_lstring(ctx, len(nimStr), nimStr.cstring)` — Z3 interprets
  the byte sequence as codepoints per SMT-LIB `(str.len s)` semantics, so
  `len` returns `nimStr.runeLen`. This is the correct behavior; no workaround
  needed, but it must be documented.
- nim-z3 APIs used: `mkString` (via `Z3_mk_lstring`), `evalStr`
  (via `Z3_get_lstring`).

**DoD:**
- [ ] All three RED tests pass (SAT, empty, newline).
- [ ] Multi-byte literal test passes: `s == "é"` and `s.len == 1` is `sxSat`.
- [ ] UNSAT test passes (contradictory literals are UNSAT, not crash).
- [ ] `nnkTripleStrLit` test passes.
- [ ] No regression on `tphase5_*` string tests.
- [ ] Documented divergence added to `determinism.md`: "`s.len` in symex equals codepoint count (`runeLen`); in Nim runtime equals byte count. This affects multi-byte Unicode literals."

---

### S3 — length, indexing, slicing: `s.len`, `s[i]`, `s[a..b]`

**What it does:** Adds `len`, codepoint-index (`at`), and substring-slice
(`substr`) to the string walker. Per ADR-0006, all offsets are codepoint
positions. `s.len` returns a Z3Int via `len` (from `z3/sequence`) on the
`svString`. `s[i]` — where `i` is a `Z3Int`-typed IR expression — lowers to
`at(sv, i)`, returning a single-codepoint `Z3String`. `s[a..b]` lowers to
`substr(sv, a, b - a + 1)` (length argument, matching Z3's `Z3_mk_seq_extract`
convention). Out-of-bounds access in the concrete model (e.g. `s[i]` with
`i >= s.len`) yields the empty string per Z3 spec — this is the Z3-native
behaviour, not a Cluster S choice, and it is documented in `determinism.md`.

**RED test:** `tests/symex/tphase15_S3_strindex.nim`, test name
`"string len: s.len == 5 is SAT"`. Additional tests:
`"string at: s[1] == at(s, mkInt(1))"`, `"string substr: s[1..3] == \"bcd\" for s == \"abcde\""`.
Specifies: `s.len == 5` with no other constraints is SAT (Z3 picks any
5-codepoint string); `s == "hello"` and `s[1..3] == "ell"` is SAT.

**GREEN:**
- `src/proptest/smt/stdlib_models.nim` — `smkStrLen`, `smkStrAt`,
  `smkStrSubstr` registered in `getStdlibModelFor(itString)`.
- `src/proptest/smt/dsl_parser.nim` — `s.len` call on an `itString` receiver
  emits `iekStrLen` (explicit routing; the S1 guard ensures this does not fall
  through to `iekSeqLen`). `s[i]` on `itString` emits `iekStrAt`. `s[a..b]`
  range-index emits `iekStrSubstr`.
  **`s.high` and `for c in s` classified**: `s.high` (Nim's byte-index-based
  `s.len - 1`) emits `SymexErrorInfo{kind: seByteIndexUnsupported}` classified
  error. `for c in s` (Nim's byte iterator yielding `char` per byte) emits
  `SymexErrorInfo{kind: seByteIterUnsupported}`. Both have routing through
  `bytes(s)` deferred to Phase 16.
- `src/proptest/smt/runtime.nim` — `of iekStrLen:` branch: `SymVal(kind: svInt, zi: len(sv.str))`.
  `of iekStrAt:` branch: `SymVal(kind: svString, str: at(sv.str, idx.zi))`.
  `of iekStrSubstr:` branch: `SymVal(kind: svString, str: substr(sv.str, lo.zi, hi.zi - lo.zi + mkInt(1)))`.
- nim-z3 APIs used: `len` (from `z3/sequence` via `z3/strings` re-export),
  `at` (from `z3/sequence`), `substr` (from `z3/sequence` as
  `Z3_mk_seq_extract`).

**DoD:**
- [ ] `s.len == 5` SAT test passes.
- [ ] `s[1..3] == "ell"` for `s == "abcde"` SAT test passes.
- [ ] Out-of-bounds `s[i]` with `i >= s.len` does not crash; witness shows empty string per Z3 spec.
- [ ] `s.high` call on `itString` receiver produces `sxUnknown` with `errors[0].kind == seByteIndexUnsupported` (not a crash).
- [ ] `for c in s` on `itString` receiver produces `sxUnknown` with `errors[0].kind == seByteIterUnsupported` (not a crash).
- [ ] No regression on S2 tests.

---

### S4 — `find`, `contains`, `startsWith`, `endsWith`

**What it does:** Wires the four substring-predicate and substring-search
operations directly to their Z3 String theory equivalents. `contains(s, sub)`,
`startsWith(s, prefix)`, and `endsWith(s, suffix)` each return a `Z3Bool`
SymVal; `find(s, sub)` (Nim's `strutils.find`) returns a Z3Int giving the
codepoint offset of the first occurrence, or `mkInt(-1)` when absent (matching
Z3's `Z3_mk_seq_index` semantics). The parser intercepts these calls by name
against an `itString` receiver and emits the corresponding `iekStr*` IR node;
the runtime lowers each to its nim-z3 API call without a stdlib model lookup
(all are direct single-dispatch).

**RED test:** `tests/symex/tphase15_S4_strpred.nim`, test name
`"contains: s contains \"ell\" is SAT only for strings with ell"`. Additional
tests: `"startsWith: s starts with \"he\" implies s[0..1] == \"he\""`,
`"endsWith: s ends with \"lo\" implies last two codepoints match"`,
`"find: s.find(\"bc\") == 1 for s == \"abc\""`,
`"find returns -1 when pattern absent"`.
Specifies: each predicate correctly constrains Z3 to produce a satisfying
witness or proves UNSAT on the contradictory constraint.

**GREEN:**
- `src/proptest/smt/stdlib_models.nim` — `smkStrContains`, `smkStrStartsWith`,
  `smkStrEndsWith`, `smkStrFind` registered.
- `src/proptest/smt/dsl_parser.nim` — call interception for `contains`,
  `startsWith`, `endsWith` (with `itString` receiver) and `find` (ditto).
  `x in s` for `itString` receiver emits `iekStrContains` (not `iekContains`,
  which is the seq/table/set path).
- `src/proptest/smt/runtime.nim` — lowers:
  `iekStrContains` → `SymVal(kind: svBool, bo: contains(sv.str, sub.str))`,
  `iekStrStartsWith` → `startsWith(sv.str, prefix.str)`,
  `iekStrEndsWith` → `endsWith(sv.str, suffix.str)`,
  `iekStrFind` → `SymVal(kind: svInt, zi: indexOf(sv.str, sub.str))`.
- nim-z3 APIs used: `contains`, `startsWith`, `endsWith` (from
  `z3/sequence`); `indexOf` (from `z3/sequence` as `Z3_mk_seq_index`).

**DoD:**
- [ ] All five RED tests pass.
- [ ] `x in s` syntax for `itString` receiver lowers to `iekStrContains` (not the seq/table path).
- [ ] `find` returns `mkInt(-1)` when pattern absent (SMT-valid, no crash).
- [ ] No regression on S2–S3 tests.

---

### S5 — `replace`, `replaceAll`, `split`, `join`

**What it does:** Adds the string replacement and sequence-decomposition
operations. `replace(s, old, new)` (first-occurrence replacement) maps to
Z3's `Z3_mk_seq_replace`. `replaceAll(s, old, new)` (global replacement) maps
to `Z3_mk_seq_replace_all` — **version-gated**: if the build lacks
`z3WithSeqReplaceAll`, the walker emits `SymexErrorInfo{kind: seZ3VersionMissing,
msg: "replaceAll requires Z3 >= 4.15.5 (Z3_mk_seq_replace_all absent)"}` and
the path yields `sxUnknown` cached under `:unknown`.

`split(s, sep)` is modeled as a symbolic `seq[string]` with three constraints:
(1) `join(parts, sep) == s`; (2) `forall i < seqLen(parts). not contains(parts[i], sep)`
(Z3 universal quantifier, ensures the decomposition is the unique `sep`-delimited
one); (3) `seqLen(parts) <= maxSplitParts`. The `maxSplitParts` bound is a new
`SymexSettings` field (default `8`, matching `maxInlineSeqLen`). When the
symbolic string length cannot be bounded within `maxSplitParts`, the walker
emits `seZ3StringIncomplete` and the path yields `sxUnknown`. For
symbolic-string inputs that can't be decided within `rlimit`, the result is
also `sxUnknown` with `seZ3StringIncomplete`. `join(parts, sep)` is modeled
symmetrically as the concatenation of `parts` with `sep` interleaved.

**RED test:** `tests/symex/tphase15_S5_strops.nim`, test name
`"replace: replace(\"foofoo\", \"foo\", \"bar\") == \"barfoo\""`. Additional
tests:
`"replaceAll: emits seZ3VersionMissing on Z3 4.15.0 build"`,
`"replaceAll: replaces all occurrences when gate passes"` (skipped if gate
absent),
`"split: split(\"a,b,c\", \",\") yields three-element seq"`,
`"join: join([\"a\",\"b\",\"c\"], \",\") == \"a,b,c\""`.
Specifies: `replace` first-occurrence is SAT; `replaceAll` on 4.15.0 emits
structured error (not crash, not silent UNSAT); `split` and `join` produce
SAT witnesses consistent with the constraint.

**Additional RED tests for S5 amendments (H2 / Feas-M1):**
- `"split: split(\"abc\", \"\") yields single-codepoint parts (empty-sep special case)"` — verifies `sxSat` with `@["a","b","c"]`; no `seZ3StringIncomplete`.
- `"split: split(\"a,b,c\", \",\") is sxSat via concrete-inline path"` — verifies no Z3 quantifier emitted.

**GREEN:**
- `src/proptest/smt/symex_settings.nim` (or equivalent settings record) —
  add `maxSplitParts: int = 8`.
- `src/proptest/smt/stdlib_models.nim` — `smkStrReplace`, `smkStrReplaceAll`,
  `smkStrSplit`, `smkStrJoin` registered.
- `src/proptest/smt/runtime.nim` — lowers:
  `iekStrReplace` → `replace(sv.str, old.str, neu.str)` via
  `Z3_mk_seq_replace`.
  `iekStrReplaceAll` → version probe: `when defined(z3WithSeqReplaceAll):`
  use `replaceAll(sv.str, old.str, neu.str)`; `else:` push
  `SymexErrorInfo{kind: seZ3VersionMissing, ...}` to the walk's error
  accumulator and return a fresh `mkStringVar` (symbolic placeholder so
  the path continues, classified UNKNOWN by the error presence).
  `iekStrSplit` → dispatch:
    (a) **empty-sep path** (H2 fix): detect `len(sv_sep)` is numeral zero;
        skip `contains` constraint; assert `forall i. len(parts[i]) == 1 and
        seqLen(parts) == len(sv_s)`.
    (b) **concrete-inline path** (M14 fix): detect `isStringValue(sv_s.str)`
        and `len(sv_sep) == 1`; emit concrete `svSeq` of literal parts; no
        quantifier asserted.
    (c) **general path**: symbolic `seq[string]` with constraints
        (1) `join(parts, sep) == s`, (2) universal `not contains(parts[i], sep)`,
        (3) `seqLen(parts) <= settings.maxSplitParts`; overflow or rlimit
        exhaustion pushes `SymexErrorInfo{kind: seZ3StringIncomplete}` and
        yields `sxUnknown`.
  `iekStrJoin` → lowers to `concat`-with-interleaved-sep chain over the `svSeq`
  elements.
- `src/proptest/smt/dsl_parser.nim` — intercepts `replace`, `replaceAll`,
  `split`, `join` on `itString` receivers; `join` also handles `seq[string]`
  receiver.
- nim-z3 APIs used: `replace` (from `z3/sequence` as `Z3_mk_seq_replace`);
  `replaceAll` (from `z3/sequence`, gated `when defined(z3WithSeqReplaceAll)`);
  `concat` (from `z3/sequence` via `z3/strings` re-export);
  `isStringValue` (from `z3/strings` or `z3/ast`; tests whether a `Z3String` AST is a concrete string constant).

**DoD:**
- [ ] `replace` first-occurrence test passes.
- [ ] `replaceAll` on 4.15.0 produces `sxUnknown` with `errors[0].kind == seZ3VersionMissing` (not a crash).
- [ ] `split` and `join` SAT tests pass.
- [ ] `split("abc", "")` ⇒ `sxSat` witness `@["a","b","c"]` (empty-sep special case; `seZ3StringIncomplete` must not appear).
- [ ] `split("a,b,c", ",")` ⇒ `sxSat` via concrete-inline path (no Z3 quantifier emitted).
- [ ] `split` with `maxSplitParts` overflow produces `sxUnknown` with `errors[0].kind == seZ3StringIncomplete`.
- [ ] `SymexErrorInfo` routing reaches `SymexFinding.errors` in the standard accumulator.
- [ ] No regression on S2–S4 tests.

---

### S6a — `regex_parser.nim` standalone

**What it does:** Creates `src/proptest/smt/regex_parser.nim` as a standalone
module with no walker dependency. Implements
`parseNimRegexToZ3Regex(pattern: string): Result[Z3Regex[Z3String], string]`
translating Nim regex pattern strings to Z3 Regex AST combinator trees. This
cycle covers only the parser and its direct unit tests; walker integration is
S6b.

**Supported constructs:** literal strings/single chars → `mkRegex(str)`;
`.` → `mkRegexAllChar`; `[a-z]` → `range`; `*` → `star`; `+` → `plus`;
`?` → `option`; `|` → `union`; `()` capturing group (transparent);
`{n,m}` → `loop`; `\d` → `range("0","9")`; `\w` → word union;
`\s` → whitespace union; `[^...]` → `complement`; `(?:...)` non-capturing
group (transparent).

**Rejected constructs** (return `Err` string / `seUnsupportedRegex`):
backreferences `\N`; lookahead `(?=...)`/`(?!...)`; named groups `(?P<name>...)`.

**RED test:** `tests/smt/tregex_parser.nim` — direct parser unit tests (no
`symexFind` involved). At least 8 supported + 3 unsupported constructs tested.
Test names include:
`"parser: literal string"`, `"parser: dot → allChar"`, `"parser: [a-z] → range"`,
`"parser: star"`, `"parser: plus"`, `"parser: question"`,
`"parser: alternation → union"`, `"parser: {2,5} → loop"`,
`"parser: \\d → digit range"`, `"parser: \\w → word union"`,
`"parser: \\s → whitespace union"`, `"parser: [^abc] → complement"`,
`"parser: (?:...) transparent"`,
`"parser: backreference → Err seUnsupportedRegex"`,
`"parser: lookahead → Err seUnsupportedRegex"`,
`"parser: named group → Err seUnsupportedRegex"`.

**GREEN:**
- `src/proptest/smt/regex_parser.nim` (new file) — implements
  `parseNimRegexToZ3Regex`. No import of `runtime.nim` or `walker.nim`;
  imports only `z3/regex` and `results`.
- `tests/smt/tregex_parser.nim` (new test file) — direct parser unit tests
  as above. Checks `isOk` + Z3 AST for supported; `isErr` + message for
  unsupported.
- nim-z3 APIs used: `mkRegex`, `star`, `plus`, `option`, `complement`,
  `concat`, `union`, `range`, `loop`, `mkRegexAllChar` (from `z3/regex`).

**DoD:**
- [ ] All ≥16 RED tests pass (≥8 supported constructs + ≥3 unsupported).
- [ ] `regex_parser.nim` compiles with no `runtime.nim`/`walker.nim` import.
- [ ] Backreference, lookahead, named-group all return `isErr` with descriptive message.
- [ ] `\d`, `\w`, `\s`, `[^...]`, `(?:...)` all return `isOk`.
- [ ] No regression on S1–S5 tests.

---

### S6b — walker integration: `iekStrMatch`/`iekStrFindRe`

**What it does:** Wires `regex_parser.nim` (from S6a) into the walker. Adds
`iekStrMatch` and `iekStrFindRe` IR dispatch to `runtime.nim`, parser
interception in `dsl_parser.nim`, and `re_replace_all` version-gating. Nim's
`re`/`nre` packages provide `match(s, pattern)` and `find(s, pattern)` with
compiled `Regex` objects; the symex model intercepts these at the call site,
invokes `parseNimRegexToZ3Regex` from S6a, and asserts the appropriate Z3
Regex membership constraint (`matches(sv, re)` for `match`; `indexOf`-on-regex
for `find`).

**IR (M4 fix):** `iekStrMatch` and `iekStrFindRe` carry a `rePatternStr: string`
field — the raw pattern string extracted at parse time from Nim's `re"..."`
macro form. No recursive `IRRegex` sum type; no boxing. At walk time,
`parseNimRegexToZ3Regex` (from S6a) translates the pattern. On `Err(msg)` the
walker emits `SymexErrorInfo{kind: seUnsupportedRegex, msg: msg}` — not silent
UNSAT. `re_replace_all` (regex global replacement) is gated behind
`when defined(z3WithSeqReplaceRe)` identically to S5's `replaceAll` gate;
absence emits `seZ3VersionMissing`.

**RED test:** `tests/symex/tphase15_S6b_regex.nim`, test name
`"regex match: s matching [a-z]+ is SAT with lowercase witness"`. Additional
tests:
`"regex match: s matching digit+ is SAT with numeric witness"`,
`"regex match: UNSAT for contradictory regex (empty) + non-empty s"`,
`"regex: backreference emits seUnsupportedRegex classified error"`,
`"regex re_replace_all: emits seZ3VersionMissing on 4.15.0 build"`.
Specifies: `matches(sv, range("a","z").plus)` produces a SAT witness of
lowercase letters; backreference causes a structured error, not a crash.

**GREEN:**
- `src/proptest/smt/types.nim` — `iekStrMatch` and `iekStrFindRe` carry
  `rePatternStr: string` field (raw pattern from `re"..."` macro). No recursive
  `IRRegex` type.
- `src/proptest/smt/dsl_parser.nim` — intercepts `match(s, re"pattern")` and
  `find(s, re"pattern")` on `itString` receivers; extracts literal pattern
  string; emits `iekStrMatch` or `iekStrFindRe` with `rePatternStr` populated.
- `src/proptest/smt/runtime.nim` — `of iekStrMatch:`/`of iekStrFindRe:`:
  calls `parseNimRegexToZ3Regex(e.rePatternStr)` from S6a; on `Ok(re)`: lowers
  to `matches(sv.str, re)` / `indexOf(sv.str, re)`; on `Err(msg)`: pushes
  `SymexErrorInfo{kind: seUnsupportedRegex, msg: msg}` and returns an
  unconstrained fresh SymVal (path yields `sxUnknown` via the error).
  `iekStrReplaceRe` version-gates identically to S5's `replaceAll`.
- nim-z3 APIs used: `matches` (from `z3/regex` via `z3` umbrella);
  all regex combinators delegated to `regex_parser.nim`.

**DoD:**
- [ ] `[a-z]+` SAT test passes; witness is all-lowercase.
- [ ] `\d+` SAT test passes; witness is numeric string.
- [ ] Contradictory regex + `s.len > 0` is UNSAT.
- [ ] Backreference path produces `sxUnknown` with `errors[0].kind == seUnsupportedRegex`.
- [ ] `replaceRe` on 4.15.0 produces `sxUnknown` with `errors[0].kind == seZ3VersionMissing`.
- [ ] No regression on S2–S5 tests.

---

### S7a — `bytes(s)` UTF-8 BMP encoding

**What it does:** Implements the `bytes(s)` DSL lift that ADR-0006 designates
as the explicit byte-access escape hatch. `bytes(s)` lowers to a `seq[byte]`
SymVal (`svSeq` of `svBV8`) constrained such that the byte sequence is the
UTF-8 encoding of `s`.

**Z3 encoding (explicit):** For each codepoint index `i < len(sv)`, let
`cp = toCode(at(sv, i))` (a `Z3Int`). The byte group at UTF-8 offset
corresponding to `i` is constrained via a nested `ite`:

```
ite(cp < mkInt(128),
  seqLen[i] == 1 AND bytes[offset] == bvFromInt[8](cp),
  ite(cp < mkInt(0x800),
    seqLen[i] == 2
    AND bytes[offset]   == (0xC0 OR (cp >> 6))
    AND bytes[offset+1] == (0x80 OR (cp AND 0x3F)),
    ite(cp < mkInt(0x10000),
      seqLen[i] == 3
      AND bytes[offset]   == (0xE0 OR (cp >> 12))
      AND bytes[offset+1] == (0x80 OR ((cp >> 6) AND 0x3F))
      AND bytes[offset+2] == (0x80 OR (cp AND 0x3F)),
      ERROR: seBytesBeyondBMP)))
```

The implementation is bounded to the BMP (codepoints < 0x10000, at most 3
UTF-8 bytes). Codepoints at or above U+10000 push
`SymexErrorInfo{kind: seBytesBeyondBMP}` and return an unconstrained fresh
`svSeq` (classified UNKNOWN via the error, per Invariant 3).

**Symbolic length restriction:** If `s.len` is symbolic at walk time (the Z3
AST for `len(sv)` is not a numeral literal), the walker emits
`SymexErrorInfo{kind: seBytesSymbolicLength}` and returns an unconstrained
fresh `svSeq`. The caller must constrain `s.len` concretely (e.g., `s.len == 3`)
for `bytes(s)` to produce a fully constrained encoding.

**Encoding length cap (L8 / Depth-LOW-D5 fix).** A new `SymexSettings` field
`maxBytesEncodingLen: int = 32` caps the maximum number of bytes the walker
will emit for a single `bytes(s)` call. If the concrete codepoint count would
produce more than `maxBytesEncodingLen` bytes (i.e., the string has more
codepoints than `maxBytesEncodingLen / 3`), the walker emits
`SymexErrorInfo{kind: seBytesLengthTooLarge, msg: "bytes(s): encoding would
exceed maxBytesEncodingLen=N"}` and returns an unconstrained fresh `svSeq`
(classified UNKNOWN via the error, per Invariant 3). The default of 32 covers
all common short string use-cases while bounding the constraint explosion from
the BMP ite-chain.

Single-codepoint ASCII characters (codepoint 0–127) collapse to direct
equality (1 byte = the codepoint value).

**RED test:** `tests/symex/tphase15_S7a_bytes.nim`, test name
`"bytes(s): ASCII string maps to identical byte values"`. Additional tests:
`"bytes(s): two-byte UTF-8 codepoint produces correct byte pair"`,
`"bytes(s): len(bytes(s)) >= len(s) always (multi-byte constraint)"`,
`"bytes(s): symbolic s.len emits seBytesSymbolicLength"`,
`"bytes(s): codepoint > 0xFFFF emits seBytesBeyondBMP"`.
Specifies: for `s == "A"`, `bytes(s)` is a length-1 `seq[byte]` with
`bytes[0] == 65`; for `s` constrained to contain a two-byte codepoint,
`bytes(s)` has the correct two-byte encoding.

**GREEN:**
- `src/proptest/smt/types.nim` — `iekStrBytes` IR expression kind (stubbed in S1);
  emitted as `iekStrBytes(recv: IRExpr)`.
- `src/proptest/smt/dsl_parser.nim` — intercepts `bytes(s)` call on `itString`
  receiver; emits `iekStrBytes`.
- `src/proptest/smt/symex_settings.nim` — add `maxBytesEncodingLen: int = 32`.
- `src/proptest/smt/runtime.nim` — `of iekStrBytes:` branch: checks whether
  `len(sv.str)` is a Z3 numeral literal; if not, pushes `seBytesSymbolicLength`
  and returns an unconstrained `svSeq`. If concrete length exceeds the
  `maxBytesEncodingLen` cap (codepoint count > `settings.maxBytesEncodingLen / 3`),
  pushes `SymexErrorInfo{kind: seBytesLengthTooLarge}` and returns unconstrained.
  Otherwise: constructs a `svSeq` of `svBV8` elements with `ite`-branched BMP
  UTF-8 constraints per codepoint.
  Codepoints above 0xFFFF push `seBytesBeyondBMP` and return unconstrained.
- nim-z3 APIs used: `toCode` (from `z3/strings` as `Z3_mk_string_to_code`),
  `at` (from `z3/sequence`), `len` (from `z3/sequence`), `ite` (from
  `z3/builder`), `mkBitVec` (from `z3/bitvec`).

**DoD:**
- [ ] ASCII byte-access test passes: `bytes("A")[0] == 65`.
- [ ] Two-byte UTF-8 test passes.
- [ ] `len(bytes(s)) >= len(s)` constraint holds in the model for a concrete-length `s`.
- [ ] Symbolic `s.len` produces `sxUnknown` with `errors[0].kind == seBytesSymbolicLength`.
- [ ] Codepoints > 0xFFFF produce `sxUnknown` with `errors[0].kind == seBytesBeyondBMP`.
- [ ] `bytes(s)` with concrete `s.len` exceeding `maxBytesEncodingLen` cap produces `sxUnknown` with `errors[0].kind == seBytesLengthTooLarge`.
- [ ] No regression on S2–S6 tests.

---

### S7b — Z3-string-theory regression smoke

**What it does:** Performs the full Cluster S regression smoke through S7a —
re-runs every test in `tphase5_*` (bounded string handling), `tphase14_*`
(runtime.nim broadly), Cluster L, and Cluster F tests from Phase 15 under the
post-S7a walker, confirming that none of the S1–S7a additions introduced
state-threading bugs. Updates `determinism.md`. No walker version bump (that
lands at S11).

**RED test:** `tests/symex/tphase15_S7b_smoke.nim`, test names:
`"regression smoke: all tphase5_* pass under Cluster S walker"`,
`"regression smoke: all tphase14_* pass under Cluster S walker"`,
`"regression smoke: Cluster F tests pass under Cluster S walker"`,
`"regression smoke: Cluster L tests pass under Cluster S walker"`.

**GREEN:**
- `tests/symex/tphase15_S7b_smoke.nim` — programmatically invokes the full
  test suites for `tphase5_*`, `tphase14_*`, Cluster L, and Cluster F tests.
- `docs/symex/determinism.md` — updated with:
  codepoint/byte distinction (ADR-0006 amendment reference),
  `seZ3VersionMissing` and `seBytesBeyondBMP` error kinds,
  `seBytesSymbolicLength` error kind,
  Z3 string theory completeness caveat for `split`/`join`/regex queries,
  `seByteIndexUnsupported`/`seByteIterUnsupported` for `s.high`/`for c in s`.

**DoD:**
- [ ] All `tphase5_*` tests green under Cluster S walker.
- [ ] All `tphase14_*` tests green under Cluster S walker.
- [ ] Cluster L regression tests green under Cluster S walker.
- [ ] Cluster F regression tests green under Cluster S walker.
- [ ] `determinism.md` updated as above.
- [ ] No walker version bump in this cycle.

---

### S8 — `&` string concatenation

**What it does:** Wires Nim's `&` operator on `string` operands to Z3's
`Z3_mk_seq_concat` (exposed as `concat` / `&` in nim-z3's `z3/sequence`).
`s & t` lowers to `SymVal(kind: svString, str: sv1.str & sv2.str)` where `&`
is the `Z3String` operator from `z3/strings`. This covers both `string &
string` and `string & literal` (the latter is lifted by nim-z3's
`liftBinString` template on `z3/strings`).

**RED test:** `tests/symex/tphase15_S8_concat.nim`, test name
`"string concat: s & \"!\" contains s and ends with \"!\""`. Additional test:
`"string concat: \"hello\" & s & \"world\" has len >= 10"`.
Specifies: `s & "!"` produces a string that both `contains(s)` and
`endsWith("!")` — SAT with a non-trivial witness; contradictory constraint
(concat result shorter than either operand) is UNSAT.

**GREEN:**
- `src/proptest/smt/types.nim` — `iekStrConcat` IR expression kind (stubbed in S1).
- `src/proptest/smt/dsl_parser.nim` — intercepts `nnkInfix` with `&` operator
  where both operands are `itString`; emits `iekStrConcat(lhs, rhs)`.
- `src/proptest/smt/runtime.nim` — `of iekStrConcat:` branch:
  `SymVal(kind: svString, str: sv1.str & sv2.str)` using `z3/strings` `&`.
- nim-z3 APIs used: `&` on `Z3String` (from `z3/strings` `liftBinString`
  template; wraps `Z3_mk_seq_concat`).

**DoD:**
- [ ] RED test passes: `s & "!"` is SAT with witness containing `s` and ending `"!"`.
- [ ] Chain concat `"hello" & s & "world"` SAT test passes.
- [ ] No regression on S2–S7b tests.

---

### S9 — `toLower`/`toUpper` classification

**What it does:** Z3 String theory has no native case-conversion operations.
Any SUT call to `s.toLower` or `s.toUpper` (from Nim's `strutils`) is
classified as an unsupported string operation: the walker emits
`SymexErrorInfo{kind: seUnsupportedStringOp, msg: "toLower: no Z3 String
theory equivalent; regex-range approximation deferred to Phase 16 backlog"}`
(or `toUpper` respectively) and the path yields `sxUnknown`.

**RED test:** `tests/symex/tphase15_S9_caseconv.nim`, test name
`"toLower: SUT calling s.toLower produces seUnsupportedStringOp classified error"`.
Additional test: `"toUpper: classified error with op name in msg"`.
Specifies: `sxUnknown` result with `errors[0].kind == seUnsupportedStringOp`
and `errors[0].msg` containing `"toLower"` (or `"toUpper"`).

**GREEN:**
- `src/proptest/smt/dsl_parser.nim` — intercepts `toLower(s)` and `toUpper(s)`
  (and dot forms `s.toLower`, `s.toUpper`) on `itString` receivers; emits
  `iekStrUnsupported` node carrying the op name.
- `src/proptest/smt/runtime.nim` — `of iekStrUnsupported:` branch: pushes
  `SymexErrorInfo{kind: seUnsupportedStringOp, msg: e.opName & ": ..."}` and
  returns a fresh unconstrained `mkStringVar` (path classified `sxUnknown`
  via the error).

**DoD:**
- [ ] `s.toLower` produces `sxUnknown` with `errors[0].kind == seUnsupportedStringOp` and `"toLower"` in msg.
- [ ] `s.toUpper` produces `sxUnknown` with `errors[0].kind == seUnsupportedStringOp` and `"toUpper"` in msg.
- [ ] No crash; no silent UNSAT.
- [ ] No regression on S2–S8 tests.

---

### S10a — `$int`/`parseInt` digits-path (pre-E1)

**What it does:** Wires the integer-string conversion operations that Z3
String theory supports directly, covering only the digits-path (no
raises-path). The raises-path requires E1 (exception walker infrastructure)
and is split into S10b.

- `$n` for `n: int` (Nim's `system.$`) lowers to `Z3Int.toStr(sv.zi)` — the
  nim-z3 `toStr` proc on `Z3Int` (wraps `Z3_mk_int_to_str`). Result is a `svString`.
- `parseInt(s)` **digits-path only:** lowers to `Z3String.toInt(sv.str)` with
  an additional assertion `toInt(sv.str) >= 0`. Z3's `Z3_mk_str_to_int` returns
  a non-negative integer for digit strings and is undefined (returns an
  unconstrained symbolic integer) for non-digit strings. The `>= 0` assertion
  is the soundness gate for the digits-path.
- **Negative-string preprocessing:** detect a leading `"-"` prefix at walk time
  (check `prefixOf(mkString("-"), sv.str)` as a Z3 Bool). Fork: (1) digits
  branch: `not prefixOf("-", s) and toInt(s) >= 0`; (2) negative branch:
  `prefixOf("-", s) and toInt(substr(s, 1, len(s)-1)) >= 0`; result is
  `-toInt(substr(s, 1, len(s)-1))`.

**Explicit unsoundness window.** Until S10b lands, `parseInt(s)` for a
non-digit, non-negative-prefixed string produces a false `sxSat` with an
unconstrained witness (Z3 picks an arbitrary non-negative integer). This is a
documented, classified temporary gap. The walker emits a classified hint
`SymexErrorInfo{kind: seParseIntPreE, severity: sevHint,
msg: "parseInt: non-digit input branch returns unconstrained model until S10b
raises-path lands; witness may not match Nim runtime behavior"}` on any path
where the non-digit branch is taken. `seParseIntPreE` is a `sevHint` (not
`sevError`); the result remains `sxSat` but with the hint in `errors`. Property
authors are warned via the hint and via `determinism.md`.

**RED test:** `tests/symex/tphase15_S10a_strconv.nim`, test name
`"$int: $n for n: int produces decimal string representation"`. Additional
tests:
`"parseInt: parseInt(s) == 42 is SAT with witness s == \"42\""`,
`"parseInt: parseInt(\"-42\") produces sxSat with witness -42"`,
`"parseInt: non-digit string emits seParseIntPreE hint"`.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim` — intercepts `$(n)` where `n` is `itInt`;
  intercepts `parseInt(s)` where `s` is `itString`.
- `src/proptest/smt/runtime.nim` — `of iekIntToStr:` →
  `SymVal(kind: svString, str: toStr(sv.zi))`.
  `of iekStrToInt:` → digits-path: assert `toInt(sv.str) >= 0`; negative
  preprocessing via `prefixOf` fork; non-digit path emits `seParseIntPreE`
  hint and returns `toInt(sv.str)` unconstrained (until S10b).
- nim-z3 APIs used: `toStr` on `Z3Int` (from `z3/strings`),
  `toInt` on `Z3String` (from `z3/strings`),
  `prefixOf` (from `z3/sequence`).

**DoD:**
- [ ] `$n` for symbolic `n: int` produces a `svString` SAT witness of the decimal form.
- [ ] `parseInt(s) == 42` is SAT with witness `s == "42"`.
- [ ] `parseInt("-42")` produces `sxSat` with witness `-42`.
- [ ] Non-digit `parseInt` input emits `seParseIntPreE` hint in `errors`; result is still `sxSat` (pre-E1 unsoundness window documented).
- [ ] `determinism.md` updated: "parseInt non-digit input returns unconstrained model until S10b lands."
- [ ] No regression on S2–S9 tests.

---

### S10b — `parseInt` raises-path (post-E1)

**Preamble — dependency on E1.** S10b is the only post-E cycle in Cluster S.
It must run after E1 (exception walker infrastructure: `sxRaised`, `WalkRaised`,
`handlerStack`) has landed. Cluster ordering is preserved by treating S10b as a
deferred slice: it is listed in the Cluster S cycle table for completeness and
for namespace continuity, but its commit must follow E1's GREEN commit. Do not
start S10b until E1's DoD is fully green.

**What it does:** Extends `parseInt` (from S10a) with the raises-path fork.
Forks the `parseInt(s)` model into two branches based on the Z3 constraint:

- **Digits-path** (extended from S10a): `toInt(sv.str) >= 0` (for non-negative)
  or `prefixOf("-", s) and toInt(substr(s, 1)) >= 0` (for negative) → returns
  the integer result as in S10a.
- **Raises-path**: input is non-digit and non-negative-prefixed →
  `not (toInt(sv.str) >= 0) and not prefixOf("-", sv.str)` → asserts
  `sxRaised("ValueError")` on this path.

Additionally:
- `$f` for `f: float`/`float64` and `parseFloat(s)` emit `seUnsupportedStringOp`
  (Z3 String theory has no float-string conversion). These are moved from S10a
  (where they were omitted from the unsoundness window) to S10b to avoid
  confusion.

**Removes the `seParseIntPreE` hint** from paths where the raises-path is now
correctly modeled. The hint is suppressed once S10b GREEN is committed.

**RED test:** `tests/symex/tphase15_S10b_strconv.nim`, test name
`"parseInt: parseInt(\"abc\") produces sxRaised(ValueError)"`. Additional
tests:
`"parseInt: parseInt(\"-42\") produces sxSat with -42 (raises-path fork present)"`,
`"$float: classified seUnsupportedStringOp"`,
`"parseFloat: classified seUnsupportedStringOp"`.
Specifies: `parseInt("abc")` ⇒ `sxRaised("ValueError")`; `parseInt("-42")` ⇒
`sxSat` with witness `-42`.

**GREEN:**
- `src/proptest/smt/runtime.nim` — `of iekStrToInt:` extended with raises-path
  fork: when `not (toInt(sv.str) >= 0) and not prefixOf("-", sv.str)`, emit
  `WalkRaised{exnType: "ValueError"}` to the caller's handler stack. Remove
  `seParseIntPreE` hint emission.
  Float forms added: `iekStrUnsupported` (per S9) with `opName = "$float"` /
  `"parseFloat"`.
- `src/proptest/smt/dsl_parser.nim` — add interception of `$(f)` / `parseFloat(s)`.

**DoD:**
- [ ] `parseInt("abc")` ⇒ `sxRaised("ValueError")` (raises-path).
- [ ] `parseInt("-42")` ⇒ `sxSat` with witness `-42` (digits-path fork).
- [ ] `$f` and `parseFloat` produce `sxUnknown` with `errors[0].kind == seUnsupportedStringOp`.
- [ ] `seParseIntPreE` hint no longer emitted for any `parseInt` call.
- [ ] No regression on S2–S10a tests.

---

### S11 — string mutation classification + walker version bump

**What it does:** Classifies Nim string mutation operations — `s[i] = c`
(byte-index assign) and `s.add(c: char)` (append a byte) — as unsupported,
emitting a structured `seUnsupportedStringOp` error. Neither operation is
sound in the codepoint-indexed symbolic model: `s[i] = c` targets a byte
offset, not a codepoint offset, and would require round-tripping through
`bytes(s)` to model correctly (deferred to Phase 16). `s.add(c: char)`
appends a single byte which may be a partial UTF-8 sequence. Both are detected
at parse time and cause the affected path to yield `sxUnknown`.

This cycle also performs the walker version bump: `"5"` -> `"6"`.

**RED test:** `tests/symex/tphase15_S11_strmut.nim`, test name
`"string byte-assign: s[i] = c emits seUnsupportedStringOp with reason 'string mutation'"`.
Additional test: `"string add: s.add(c) emits seUnsupportedStringOp with reason 'string add'"`.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim` — intercepts `nnkAsgn` where the LHS is
  `s[i]` with `itString` receiver; emits `iekStrUnsupported` with
  `opName = "string mutation"`. Intercepts `s.add(c)` where `s` is `itString`
  and `c` is `char`/`itByte`; emits `iekStrUnsupported` with
  `opName = "string add"`.
- `src/proptest/smt/runtime.nim` — existing `of iekStrUnsupported:` branch
  handles both (per S9 infrastructure).
- `src/proptest/smt/canonicalize.nim` — walker version constant updated: `"5"` → `"6"`.
  The single source-of-truth for the walker version lives in `canonicalize.nim`
  (not `runtime.nim` or `walker.nim`) per M12; do not edit `walker.nim` for this
  purpose. DoD verifies `canonicalize.walkerVersion == "6"`.
- `docs/symex/determinism.md` — updated: `s[i] = c` and `s.add(c)` produce
  `seUnsupportedStringOp` with reason "string mutation" / "string add"; both
  deferred to Phase 16.

**DoD:**
- [ ] `s[i] = c` produces `sxUnknown` with `errors[0].kind == seUnsupportedStringOp` and `"string mutation"` in msg.
- [ ] `s.add(c)` produces `sxUnknown` with `errors[0].kind == seUnsupportedStringOp` and `"string add"` in msg.
- [ ] `canonicalize.walkerVersion == "6"` after this cycle (edited in `canonicalize.nim`, not `walker.nim`).
- [ ] All existing Phase-15 tests that check walker version pass.
- [ ] `determinism.md` updated as above.
- [ ] No regression on S2–S10b tests.

---

<!-- CLUSTER_H -->
## Cluster H — heap preparation

Cluster H is pure infrastructure: it promotes the former R0 preparatory
cycle forward between Cluster S and Cluster E. The motivation is a hard
compile-time dependency: round-2 architect review (finding Feas-CRIT-1)
found that E3, E5, and E7 each reference `path.heaps`, `path.heapDepth`,
and `path.allocCounters` to thread heap state through try/finally and
inter-procedural exception propagation. With R0 living inside Cluster R —
three clusters later — the E-cluster RED tests cannot even compile. H
pulls the `Path` field extension forward so E1–E7 compile against a
`Path` type that already carries the three heap-state fields. No
heap-feature semantics land in H; those belong to Cluster R. H
introduces no walker-semantic change and therefore carries **no walker
version bump** and no rendering version bump.

**Dependencies:** Z3 and Z4 (cross-cutting infra live; `WalkCtx` has the
`statics`/`frame` split in place). H has no dependency on L, F, or S
beyond the baseline `Path` type being stable.

**Out of scope for this cluster:** any heap-feature semantics — symbolic
allocation, dereference, ref-equality, nil-fork, alias propagation, or
witness serialisation. All of those land in Cluster R.

### Cluster H — cycle table

| Cycle | Topic | Walker bump |
|-------|-------|-------------|
| H1 | `Path` refactor + ADR-0010 (heap model authored) | — |

---

### H1 — `Path` refactor for heap state (formerly R0; folds R0-ADR)

**RED test:** `tests/symex/tphase15_H1_path_heap_fields.nim`.

Two assertions:

1. **Type-level field existence** — the test file opens with three
   `compiles` checks that must be true at compile time:
   ```nim
   var p: Path
   doAssert compiles(p.heaps)
   doAssert compiles(p.heapDepth)
   doAssert compiles(p.allocCounters)
   ```
   These fail to compile before H1's GREEN lands (the fields do not yet
   exist), which is the RED signal.

2. **Fork isolation deep-copy invariant** — a synthetic fixture that
   exercises the `walk(isIf)` fork path in isolation: create a parent
   `Path`, pre-populate `path.heaps["x"] = someAst`, call the fork
   helper, mutate the child's `heaps["x"]` to a different AST, then
   assert the parent's `heaps["x"]` is unchanged. Test name:
   `"H1: fork-site deep-copy: mutating child heaps does not mutate parent"`.

**GREEN:**

- **`src/proptest/smt/runtime.nim`** — extend the `Path` type with three
  new fields, defaulting to empty:
  ```nim
  heaps: Table[string, Z3AnyAst]       # per-path symbolic heap (Cluster R fills)
  heapDepth: int                        # current heap-descent depth
  allocCounters: Table[string, int]     # per-type fresh-ref counter
  ```
  Enumerate every constructor / fork site via:
  ```
  grep -n "Path(" src/proptest/smt/runtime.nim
  ```
  The post-Phase-14 count (before E/G/C land) is the target: expect
  roughly 15–20 sites (finding Feas-LOW-2 / L10 notes the post-E/G
  total will reach 25–30; H1 audits only the sites present now).
  At every site that constructs a child `Path` from a parent (i.e.
  every fork site — `isIf`, `isCase`, `isWhile` loop-entry, call-descent
  clones), update the construction to deep-copy the three tables using
  the new helper below. Sites that construct a fresh root `Path` (no
  parent) are correct by default (empty tables).

- **`proc deepCopyHeapState`** helper in `runtime.nim` (used at fork
  sites for readability):
  ```nim
  proc deepCopyHeapState(src: Path):
      tuple[heaps: Table[string, Z3AnyAst],
            allocCounters: Table[string, int]] =
    result.heaps = src.heaps          # Table copy = value copy in Nim
    result.allocCounters = src.allocCounters
  ```
  (`heapDepth` is an `int` and copies by value automatically; no helper
  needed for it.)

- **Fork-site comment block** — immediately above the first fork site in
  `runtime.nim`, add a code-comment block that lists every fork site with
  its line number (updated to actual line numbers after the edit):
  ```nim
  # Fork-site registry (H1 deep-copy contract)
  # Every site that creates a child Path from a parent MUST deep-copy
  # heaps and allocCounters via deepCopyHeapState. heapDepth copies by
  # value automatically.
  #
  # Sites (line numbers reflect post-H1 state):
  #   <line>  walk(isIf)        — true-branch fork
  #   <line>  walk(isIf)        — false-branch fork
  #   <line>  walk(isCase)      — per-arm fork
  #   <line>  walk(isWhile)     — loop-entry clone
  #   <line>  descend (isCall)  — callee-frame clone
  #   ... (all remaining sites)
  ```
  This comment block is the canonical registry for the fork-site audit;
  it is updated whenever a new fork site is introduced (E, G, C, R each
  add sites; the R-cluster walker comment block supersedes this one).

- **`docs/symex/ADR-0010-logical-heap.md`** — authored at this path,
  matching the structure and depth of ADR-0001 through ADR-0004.
  Required sections:

  *Decision.* The symex engine models the heap as a family of Z3 arrays,
  one per pointee type: `Z3Array[Ref_T, T]` where `Ref_T` is an
  uninterpreted sort representing abstract addresses for objects of type
  `T`. Freshness (the property that `new(T)` returns an address not
  previously observed on any path) is maintained by a per-type counter
  stored in `path.allocCounters[typeId]`; each `new` increments the
  counter and asserts the resulting address is distinct from all prior
  addresses for that type. `nil` is modelled as the sort-level constant
  `Z3_mk_const(ctx, nilSym_T, Ref_T)` for each sort — a dedicated,
  globally-named constant that is never returned by the freshness
  mechanism. Heap state is snapshotted on `Path` (`path.heaps`,
  `path.heapDepth`, `path.allocCounters`) and deep-copied at every
  fork site so paths never share mutable heap state.

  *Alternatives considered and rejected.*
  - **Region-based analysis (Hind, Reps):** tracks which heap regions
    a pointer may alias rather than tracking individual allocations.
    Rejected: region-based techniques produce may-alias sets, not
    definite value models. A symex engine that already owns path-sat
    can produce precise, path-sensitive heap models; degrading to
    region summaries would lose the very precision that makes symex
    useful for PBT witnesses.
  - **Andersen-style points-to analysis:** whole-program flow-insensitive
    over-approximation. Rejected: same precision argument; additionally,
    Andersen requires a whole-program view the proptest engine does not
    have (it walks one SUT at a time).
  - **Steensgaard-style unification:** linear-time but merges all
    aliasing pointers into one equivalence class. Rejected: merging
    alias classes prevents the engine from distinguishing `p` and `q`
    when both can point to the same object — exactly the distinction
    needed for ref-aliasing PBT witnesses.

  *Consequences.*
  - Cross-type `ref` comparisons become Z3 sort errors at construction
    time, preventing false alias between `ref Foo` and `ref Bar`.
  - Bounded allocation cycles: `maxHeapDepth` caps the recursion depth
    of `ref object` field expansion in witness serialisation (R9/R12).
  - `path.heaps` deep-copied at every fork site (see H1 fork-site
    registry in `runtime.nim`); callee heap state merged back into
    caller at call-exit (R1b threading protocol).

  *Implementation notes.*
  - `Path` field schema: `heaps: Table[string, Z3AnyAst]` keyed by
    sort name; `heapDepth: int`; `allocCounters: Table[string, int]`
    keyed by type ID string.
  - Fork deep-copy contract: see `runtime.nim` fork-site registry
    comment block (introduced H1, maintained through R).
  - R1b preview: inter-procedural heap threading passes caller
    `path.heaps` into callee descent and merges callee exit heaps
    back out; `allocCounters` merge uses `max(caller, callee)` per
    finding C5 / R1b spec.

**Heap witness invariants** (Des-H7 / finding H21) — the following
non-negotiable invariants govern the `heapSnapshot` section of the
witness format authored in R11b (`witness-format-v3.md`). They are
recorded here so R11b's author has a concrete contract to satisfy and
so E-cluster reviewers can cross-reference:

1. `heapSnapshot` is emitted in a witness only when the witness
   includes at least one `svRef` or `svPtr` parameter.
2. Alias groups are deduplicated: the lexicographically-first
   parameter name among an alias group holds the `pointsTo` field;
   all other members of the group carry `aliasRef: <primary_name>`
   and no `pointsTo`.
3. `nil` refs are rendered as `{value: "nil", pointsTo: null}` with
   no `aliasGroup` entry.
4. `pointsTo` for a `ref object` value is recursively expanded using
   the same field-path format as non-ref tuple witnesses, bounded by
   `maxHeapDepth` (Cluster R setting). When `maxHeapDepth` is reached,
   the field is rendered as `{truncated: true}`.

These invariants are cross-referenced by R11b (witness authoring) and
R12 (final serialisation DoD).

**DoD:**

- [ ] `tphase15_H1_path_heap_fields.nim` passes in the proptest dev
  container (`nimlang/nim:2.2.0` + Z3 4.15.0 + libz3-dev).
- [ ] `Path` type in `runtime.nim` carries all three new fields;
  `nimble build` is clean.
- [ ] Fork-site audit complete: every fork site in `runtime.nim` that
  constructs a child `Path` from a parent calls `deepCopyHeapState`;
  the fork-site registry comment block is present with accurate line
  numbers.
- [ ] Fork isolation test green: mutating `child.heaps` after fork does
  not mutate `parent.heaps`.
- [ ] `ADR-0010-logical-heap.md` on disk at `docs/symex/ADR-0010-logical-heap.md`.
- [ ] Heap witness invariants subsection present above (cross-referenced
  by R11b and R12 DoDs).
- [ ] Full `nimble test` green — no behaviour change for Phase-14 SUTs
  (the new fields are inert until Cluster R activates them).
- [ ] No walker version bump; no rendering version bump.

---

## Standing rules

- **PhD-CS bar. No consumers yet.** Every cycle's design is evaluated against
  the correctness of the symbolic model, not against the convenience of any
  particular user scenario. Correctness is defined by SMT-LIB string theory
  semantics, Nim's observable string behaviour, and ADR-0006.

- **Invariant 3 (no silent fallbacks).** Every unsupported or
  version-gated operation emits a classified `SymexErrorInfo` via the standard
  accumulator and causes the affected path to yield `sxUnknown` cached under
  `:unknown`. The following sources all trigger classified errors, never silent
  UNSAT:
  - `replaceAll` / `re_replace_all` on a Z3 build lacking
    `Z3_mk_seq_replace_all` / `Z3_mk_seq_replace_re`: `kind = seZ3VersionMissing`.
  - Nim RE constructs with no Z3 Regex equivalent (backreferences, lookahead,
    named groups): `kind = seUnsupportedRegex`.
  - Codepoints above U+FFFF in `bytes(s)` constraints: `kind = seBytesBeyondBMP`.
  - `bytes(s)` with symbolic `s.len` at walk time: `kind = seBytesSymbolicLength`.
  - `s.high`, `for c in s`: `kind = seByteIndexUnsupported` / `seByteIterUnsupported`.
  - `toLower`, `toUpper`, `$float`, `parseFloat`, `s[i] = c`, `s.add(c)`:
    `kind = seUnsupportedStringOp`.
  - `split` overflow beyond `maxSplitParts` or rlimit exhaustion:
    `kind = seZ3StringIncomplete`.
  - Any other string op that falls through the walker without a matching IR
    branch raises an `AssertionDefect` (real walker bug, not classified error;
    must surface during development).

- **Invariant 4 (S7b is the Z3-string-theory regression smoke).** S7b
  re-runs `tphase5_*`, `tphase14_*`, Cluster L, and Cluster F tests under the
  Cluster S walker through S7a. S8-S11 land after S7b. The final walker
  version bump for this cluster is at S11. No Cluster S commit is considered
  complete until S11's DoD is fully green.

<!-- CLUSTER_E -->
## Cluster E — exceptions

### Cycle table

| Cycle | Title | Key dependency |
|-------|-------|----------------|
| E1 | IR extension + walker handler-stack plumbing | — |
| E2a | Structural `sxRaised` cascade (stub arms, cache key, `sfRaised`; `WalkCtx.found: seq[RawResult]`) | E1, `SymexErrorKind` enum (Z3) |
| E2b | Real `walk(isRaise)` semantics + `InternalVerdict` private union | E2a |
| E3 | `try`/`except` matching by type (first-match, catch-all) + inter-procedural propagation stub | E2b |
| E4 | Exception type hierarchy (subtype catch, static `ExnTypeTable`) | E3 |
| E4a | Dynamic user-exception hierarchy table (`getImpl` walk, `userExnHierarchy`) | E4 |
| E5 | `finally` semantics (all-exit-continuation cross-product; finally-raises-replaces; heap state at raise point) | E4a |
| E6 | `Defect` modeling (`sxRaised` with `isDefect = true`; `defectExclusions: set[DefectKind]`; OQ 4 closed) | E5 |
| E7 | Regression smoke (inter-proc raise + finally heap-threading; multi-frame re-raise; cache round-trip; walker version `"6"→"7"` in `canonicalize.nim`) | E6 |
| E8 | `getCurrentException()` / `getCurrentExceptionMsg()` (uses `svUninterpRef` from Z3) | E5 |

**ADR-0007** — exception flow model — was authored as part of Cluster Z4 (already documented in v3 top matter). No E0-ADR cycle is added here.

### Preamble

**Cluster E depends on:**
- **Cluster H** — `Path` carries `heaps`, `heapDepth`, and `allocCounters` (R0 pulled forward to H; E3/E5/E7's heap-state threading compiles against these fields).
- **Z3 / Z4** — `WalkCtx.statics` (`WalkerStatics`) and `WalkCtx.frame` (`CallFrameCtx`) split (C6); `SymexErrorKind` enum with all `ee*` variants (C2); `severity` field on `SymexErrorInfo` (H16); `svUninterpRef` in `SVKind` (C8, used by E8).

**Cross-cluster invariants that apply here:**
- **Invariant 6** (single-source-of-truth): `symexWalkerVersion` constant lives in `canonicalize.nim` only (not `runtime.nim`); all version references import from there.
- **Invariant 7** (severity contract): every `SymexErrorInfo` emitted by E-cluster code carries `severity: sevHint | sevWarning | sevError`; halting error kinds (`eeRaiseUnimplemented`, `eeTryUnimplemented`, `eeRaiseOutsideHandler`, `eeNotInHandler`) use `sevError`; hint-class diagnostics use `sevHint`. An `sxUnknown` verdict implies ≥1 `sevError` in `w.errors`.
- **Invariant 9** (`InternalVerdict` / public `RawResult`): internal handler-stack propagation uses `InternalVerdict` (renamed from `WalkResult` per Des-H3; variants `ivSat | ivUnsat | ivUnknown | ivRaised`). The conversion `toPublic(iv: InternalVerdict): RawResult` is called exactly once per finding at the `runSymex` boundary. No `sxRaised` escapes internal handler-stack code.

**`EffectCtx` field migration.** Round-2 CRIT finding C6 splits `EffectCtx` into two distinct lifetime scopes:
- `WalkerStatics` (per-walker, immutable post-parse): holds `userExnHierarchy`, `exnTable`.
- `CallFrameCtx` (push/pop per call descent): holds `handlerStack`, `inFlightExn`.

Throughout this cluster, references to `w.effects.userExnHierarchy` and `w.effects.exnTable` become `w.statics.userExnHierarchy` and `w.statics.exnTable`. References to `w.effects.handlerStack` and `w.effects.inFlightExn` become `w.frame.handlerStack` and `w.frame.inFlightExn`. Every `isCall`/`isGenericCall`/`iekClosureCall` descent pushes a fresh `CallFrameCtx`; returns pop. Handler-stack threading is per-frame. Affected cycles: E1, E3, E5, E6, E7.

**`InternalVerdict` replaces `WalkResult`.** All internal uses of `WalkResult` / `WalkRaised` etc. are renamed `InternalVerdict` / `ivRaised` etc. per Des-H3. The E2b introduction section is updated accordingly; `WalkResult` does not appear as a new type name from E2b onward.

**Out of scope for this cluster:**
- Continuation-based exceptions: no `try`/`except`/`finally` nesting beyond what Nim's semchecker emits in the typed AST.
- Exception filters: Nim has none.
- `{.raises: [Exception].}` pragma effect-tracking: Phase 16.

**ADR-0007 summary.** Exception control flow is modeled via a stack of
handler frames threaded through `WalkCtx`. A `raise` on a feasible path
emits a new `RawResult` variant `sxRaised(typeId, witness)` rather than
continuing the path. Propagation is explicit: if the walker's handler
stack is non-empty, it pops the top frame and pattern-matches the raised
type against the frame's except-clauses (first-match wins; bare `except:`
matches everything). If a match is found, control transfers into the
matched handler body and the `sxRaised` result is consumed — the path
continues. If no match is found, the result propagates up through the
call stack until either a matching handler is found or the SUT boundary
is reached, at which point the top-level verdict becomes `sxRaised`.
`finally` blocks run unconditionally on both normal and raised exit from
their try body; if a `finally` block itself raises, that new exception
replaces the in-flight one (Nim runtime semantics, faithfully modeled by
checking whether the finally body produces `ivRaised` before restoring
the prior exception).

**Why this model is sound.** The walker is already a path-explicit
interpreter: every branch produces a concrete `Path` value annotated
with a path condition. Modeling exceptions as an explicit `ivRaised`
result threaded through return continuations is therefore a conservative
extension of the existing structure — no CPS transform, no implicit
control-flow edges, no changes to the path-sat layer. Every `raise`
carries the path condition under which it fires, so the emitted Z3 query
that produces the witness is just the accumulated `pc` at the point of
the raise. Type-hierarchy matching (E4) consults a static lookup table
built from the Nim type-class hierarchy at parse time; it is not a Z3
query. The result is that every raised verdict has explicit path
provenance, the same guarantee the existing `sxSat` verdict family
already provides.

**Open question 4 — CLOSED.** ADR-0007's default — modeling `Defect`
raises as `sxRaised` with `isDefect: true` rather than as `sxUnreached`
— is correct. A `Defect` indicates a precondition violation; silently
short-circuiting it to `sxUnreached` would cause property tests to pass
on inputs that trigger contract violations inside the SUT. The
`sxUnreached` alternative is not a performance tradeoff but a soundness
policy: it silences observable failures. For Defects that are genuinely
unreachable through normal symex paths (`OutOfMemoryDefect`,
`StackOverflowDefect`), the correct mechanism is a per-type exclusion
filter (`defectExclusions: set[DefectKind]` in `SymexSettings`) rather than
a blanket `sxUnreached`. This is implemented in E6. (See round-1
findings M3 and Depth-MED-3; round-2 MED finding M1.)

**Top-level verdict shape.** `sxRaised` is a new variant of
`SymexStatusKind`, alongside the existing `sxSat`, `sxUnsat`, and
`sxUnknown`. Its payload is `(typeId: string, isDefect: bool,
raisedMsg: Option[string], witness: RawWitness)`. `RawResult` grows a
corresponding branch. Consumers of `symexFindAllWitnesses`, `symexFind`,
and `assertCoveredBy` surface raised verdicts as failing properties: a
raised verdict on a property that was only searching for `tLabel` or
`tAssertionViolation` targets is itself a finding (the SUT raised instead
of returning normally), reported as `SymexFindingStatus.sfRaised`.
Consumers that explicitly search for `stkRaisedExn` targets (introduced
in E2a as a new `SymexTargetKind`) can treat a matching `sxRaised` as
`sfSat`. The verdict is cached under a `:raised:<typeId>` key suffix,
distinct from `:sat`/`:unsat`/`:unknown`, so re-runs serve from cache
without re-invoking Z3. Cross-cluster invariant 3 applies: `itRaise` and
`itTry` nodes that reach the walker before their semantic paths are
complete raise a deterministic `SymexErrorInfo`-tagged error
(`kind: eeRaiseUnimplemented` / `eeTryUnimplemented`), never silent
fallback to `sxUnknown`.

**`InternalVerdict` private union.** Internal handler-stack propagation uses
a private `InternalVerdict` discriminated union (`ivSat | ivUnsat |
ivUnknown | ivRaised`). The `ivRaised` variant carries
`(typeId, msg, witness)` and is the only internal representation of an
in-flight exception. Only the top-level `runSymex` calls
`toPublic(iv: InternalVerdict): RawResult`, mapping `ivRaised →
RawResult{status: sxRaised}`. This conversion happens exactly once per
finding at the `runSymex` boundary. (Addresses round-1 HIGH finding H2;
naming aligned with round-2 Des-H3.)

**Error-kind prefix.** All E-cluster errors use the `ee` prefix:
`eeRaiseOutsideHandler`, `eeNotInHandler`, `eeRaiseUnimplemented`,
`eeTryUnimplemented`, `eeFinallyRaisedUnimplemented`. The `SymexErrorKind`
enum (introduced in Z3 per v3 top matter) carries these variants.
`eeUninterpRefExtraction` is a `sevHint`-severity kind added in E8.

---

### E1 — IR extension + walker handler-stack plumbing

**What it does:** Introduces the two new IR statement kinds `isRaise`
and `isTry` into `types.nim` and `dsl_parser.nim`, and adds
`CallFrameCtx` with `handlerStack: seq[HandlerFrame]` and
`inFlightExn: Option[ExnRecord]` to `WalkCtx.frame` in `runtime.nim`.
`WalkerStatics` gains `exnTable` (the static `ExnTypeTable`) and
`userExnHierarchy` (populated in E4a; nil/empty until then).
This is purely structural: the parser recognizes
`nnkRaiseStmt`, `nnkTryStmt`, `nnkExceptBranch`, and `nnkFinally` and
emits the new IR kinds; the walker stubs raise a deterministic
`SymexErrorInfo`-tagged error on both new kinds (Invariant 3). No
semantic behavior yet.

Every `isCall`/`isGenericCall`/`iekClosureCall` descent must push a fresh
`CallFrameCtx` onto an implicit frame stack before descending into the
callee body, and pop it on return. Handler-stack threading is therefore
per-frame: a handler pushed inside `f` is not visible to a caller `g` after
`f` returns. This push/pop protocol is specified here and implemented in
the call-descent arms; E3 and E5 rely on it being correct.

`svUninterpRef` is already added to `SVKind` in Z3; E8 consumes it. E1
need not extend `SVKind`.

**Consumer note.** Cluster S cycle S10b (the `parseInt` raises-path) depends
on E1 being shipped; S10b is sequenced in Cluster S after E1 lands.

**RED test:** `tests/symex/tsymex_phase15_E1_ir.nim`, test name
`"E1: parser emits isRaise for nnkRaiseStmt"`. Specifies: a SUT
containing `raise newException(ValueError, "x")` is passed through the
parser; the resulting `IRStmt` tree contains a node with `kind ==
isRaise`; `render(stmt)` produces the canonical string
`"raise(ValueError,\"x\")"`. A second case in the same test file
asserts `render` of a minimal `isTry` IR (hand-constructed) matches
`"try{...}except[ValueError=>...][finally=>...]"`. A third case
confirms the walker stubs on both new kinds produce a classified
`SymexErrorInfo` rather than propagating to `sxUnknown` silently.

**GREEN:**

- `src/proptest/smt/types.nim` — extend `IRStmtKind` with `isRaise`
  and `isTry`. Add fields to `IRStmt`:
  ```
  of isRaise:
    raiseTypeId*: string   ## qualified Nim type name, e.g. "ValueError"
    raiseMsg*: IRExpr      ## nil for bare `raise` (re-raise)
    raiseIsReraise*: bool  ## true for no-argument `raise`
  of isTry:
    tryBody*:     IRStmt
    tryHandlers*: seq[ExceptHandler]
    tryFinally*:  IRStmt   ## nil if no `finally`
  ```
  Add `ExceptHandler` type:
  ```nim
  ExceptHandler* = object
    typeIds*: seq[string]  ## empty = bare `except:` (catch-all)
    body*:    IRStmt
  ```
  Add constructors `mkRaise`, `mkReraise`, `mkTry`. Add `render`
  branches for both new kinds.

- `src/proptest/smt/dsl_parser.nim` — add cases for `nnkRaiseStmt`,
  `nnkTryStmt`, `nnkExceptBranch`, `nnkFinally` in the statement
  parser. `nnkRaiseStmt` with a child emits `mkRaise(typeId, msgExpr)`;
  with no child (bare `raise`) emits `mkReraise()`. `nnkTryStmt`
  collects `nnkExceptBranch` children into `ExceptHandler` values and
  the `nnkFinally` child into `tryFinally`.

- `src/proptest/smt/runtime.nim` — add `HandlerFrame` and `ExnRecord`
  types; add `CallFrameCtx`:
  ```nim
  HandlerFrame = object
    handlers*:    seq[ExceptHandler]
    finallyBlock*: IRStmt   ## nil if no finally
  ExnRecord = object
    typeId*: string
    msg*:    Option[string]
  CallFrameCtx = object
    handlerStack*: seq[HandlerFrame]
    inFlightExn*:  Option[ExnRecord]
  ```
  Add `frame: CallFrameCtx` to `WalkCtx`. Add `exnTable` and
  (nil/empty) `userExnHierarchy` to `WalkerStatics`. Add push/pop
  helpers `pushFrame(w)` / `popFrame(w)` used by call-descent arms.
  Add stub branches in `walk(stmt: IRStmt, ...)` for `isRaise` and
  `isTry` that call `raiseClassifiedError(w, eeRaiseUnimplemented,
  sevError)` / `eeTryUnimplemented` (same pattern as existing
  unimplemented IR kinds). Add `emitExpr` and `emitStmt` branches in
  `dsl_parser.nim` for the new IR nodes.

**DoD:**
- [ ] `"E1: parser emits isRaise for nnkRaiseStmt"` passes both `isExact` and `isOptimised` backends
- [ ] Walker stubs produce `SymexErrorInfo{kind: eeRaiseUnimplemented, severity: sevError}` / `eeTryUnimplemented` — never silent `sxUnknown`
- [ ] `render(isRaise)` / `render(isTry)` round-trips through `render` without panic
- [ ] `CallFrameCtx` push/pop wired in every `isCall`/`isGenericCall`/`iekClosureCall` descent arm
- [ ] All 76 prior test files green (no `types.nim` regression)

---

### E2a — Structural `sxRaised` cascade

**What it does:** Purely mechanical cascade: adds `sxRaised` to
`SymexStatusKind` and the `RawResult` variant object, stubs all three
exhaustive `case raw.status` dispatch sites in `symex.nim` (at the
`toFindingStatus` call, `saveSymexVerdictImpl`, and
`loadSymexVerdictImpl`), adds `cacheKeyRaised(typeId): string` proc to
`canonicalize.nim` (Invariant 6: single source of truth — no
caller-side concat), adds `sfRaised` to `SymexFindingStatus` in
`engine/types.nim`, extends `SymexTargetKind` with `stkRaisedExn`.

The `WalkCtx.found: Option[RawResult] → seq[RawResult]` field-type
change is part of this cycle (round-2 Feas-H9 / Z4 prep; all
`shouldStop` and `w.found` sites updated simultaneously here).
`sxRaised` results accumulate alongside `sxSat` in multi-finding mode.

No Z3 reasoning, no `walk(isRaise)` implementation. The `sxRaised` arm
in the walker is a stub that emits `eeRaiseUnimplemented` (same as E1).
The purpose of this cycle is to make the codebase **compile with
`sxRaised` fully wired** before any semantics are added, ensuring every
exhaustiveness-checked `case` is satisfied.

**Multi-`sxRaised` cache serialization.** `saveSymexVerdictImpl` iterates
`found: seq[RawResult]` and writes every `sxRaised` finding under
`cacheKeyRaised(raw.raisedTypeId)`. `loadSymexVerdictImpl` uses
`loadAll(sutKeyPrefix): seq[RawResult]` to read all `:raised:*` key
matches and reconstructs the full seq. This ensures a SUT with two
distinct raise paths (`ValueError` on `x < 0`, `IOError` on `x == 0`)
round-trips both findings through DB save/load.

All `SymexErrorKind` enum variants are used throughout E2a GREEN (no
bare-string error-kind literals).

**RED test:** `tests/symex/tsymex_phase15_E2a_cascade.nim`. Two test
cases:

1. `"E2a: SUT with raise compiles; sfRaised surfaces as stub verdict"` —
   SUT `proc f(x: int) = raise newException(ValueError, "x")` is
   passed to `symexFind(f, tAssertionViolation())`; the result
   compiles (no exhaustiveness panic) and the returned finding has
   `status == sfRaised` (stub arm fires; no witness yet). Verifies
   that the cascade is structurally complete without requiring real
   walker semantics.

2. `"E2a: multi-sxRaised DB round-trip"` — SUT:
   ```nim
   proc f(x: int) =
     if x < 0: raise newException(ValueError, "neg")
     elif x == 0: raise newException(IOError, "zero")
   ```
   After `symexFindAllWitnesses(f)` populates the DB, a second call
   with an empty in-memory cache loads both `sxRaised` findings
   (one for `ValueError`, one for `IOError`) from the DB without
   invoking Z3. Asserts `found.len == 2` and both `raisedTypeId`
   values are present.

**GREEN:**

- `src/proptest/smt/runtime.nim` — add `sxRaised` to `SymexStatusKind`.
  Add branch to `RawResult`:
  ```nim
  of sxRaised:
    raisedTypeId*: string
    isDefect*:     bool           ## populated in E6; false until then
    raisedMsg*:    Option[string] ## populated in E2b; none until then
    witness*:      RawWitness
  ```
  Change `WalkCtx.found` from `Option[RawResult]` to `seq[RawResult]`.
  Update all `case raw.status` dispatch sites and `shouldStop` semantics.
  Add stub `of sxRaised:` arm in the walker's `walk(isRaise)` that still
  emits `eeRaiseUnimplemented` (this arm will be replaced in E2b).

- `src/proptest/smt/canonicalize.nim` — add:
  ```nim
  proc cacheKeyRaised*(typeId: string): string =
    ":raised:" & typeId
  ```
  No bare-suffix constant; callers use the proc exclusively.

- `src/proptest/engine/types.nim` — add `sfRaised` to
  `SymexFindingStatus`. Extend `SymexTargetKind` with `stkRaisedExn`.
  Add `ExnTypeFilter` field: `stkRaisedExn{typeFilter: string}`
  (empty = any raised exception).

- `src/proptest/symex.nim` — add `of sxRaised:` arms to:
  - `toFindingStatus`: maps `sxRaised → sfRaised`.
  - `saveSymexVerdictImpl`: iterates `found`, writes each `sxRaised`
    under `cacheKeyRaised(raw.raisedTypeId)`.
  - `loadSymexVerdictImpl`: calls `loadAll(sutKeyPrefix)` to retrieve
    all `:raised:*` entries and reconstructs `seq[RawResult]`.
  Extend `assertCoveredBy` to treat `sfRaised` on a non-`stkRaisedExn`
  target as a test failure with a diagnostic naming the raised type.

**DoD:**
- [ ] E2a test case 1 compiles and passes under `isExact` and `isOptimised`
- [ ] E2a test case 2 (multi-`sxRaised` DB round-trip) passes: both `ValueError` and `IOError` findings reloaded without Z3 re-invocation
- [ ] All three `case raw.status` sites compile without exhaustiveness error
- [ ] `toFindingStatus(sxRaised) == sfRaised`
- [ ] `saveSymexVerdictImpl` iterates `found: seq[RawResult]`; `loadSymexVerdictImpl` uses `loadAll`
- [ ] `cacheKeyRaised(typeId)` proc exported from `canonicalize.nim` (no bare suffix constant)
- [ ] `WalkCtx.found: seq[RawResult]` — all `shouldStop` and call sites updated
- [ ] No bare-string `SymexErrorKind` literals in new E2a GREEN code
- [ ] All prior E1 + Cluster S tests green

---

### E2b — Real `walk(isRaise)` semantics

**What it does:** Implements the actual walker semantics for `isRaise`:
evaluates `stmt.raiseMsg` via `walkExpr` and stores the result as
`RawResult.raisedMsg`; returns an `ivRaised(typeId, msg, witness)`
private intermediate result. Top-level `runSymex` calls
`toPublic(iv: InternalVerdict): RawResult` to map `ivRaised` at the SUT
boundary to `RawResult{status: sxRaised, ...}`.
Introduces the `InternalVerdict` private discriminated union
(`ivSat | ivUnsat | ivUnknown | ivRaised`). Internal
handler-stack propagation never produces a public `sxRaised` — only
`runSymex` calls `toPublic` at the boundary.

**RED test:** `tests/symex/tsymex_phase15_E2b_raise.nim`. Two test
cases:

1. `"E2b: unconditional raise yields sxRaised verdict"` — SUT `proc
   f(x: int) = raise newException(ValueError, "always")` passed to
   `symexFind(f, tAssertionViolation())` returns a result with
   `status == sxRaised` and `raisedTypeId == "ValueError"`.

2. `"E2b: conditional raise yields sxRaised under path constraint"` —
   SUT `proc f(x: int) = if x > 0: raise newException(ValueError, "pos")`;
   `symexFind(f, tLabel("unreachable"))` on the non-raise branch returns
   `sxUnsat`; `symexFind(f, stkRaisedExn{typeId: "ValueError"})` returns
   `sxRaised` with a witness satisfying `x > 0`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — introduce `InternalVerdict` private union:
  ```nim
  type InternalVerdictKind = enum ivSat, ivUnsat, ivUnknown, ivRaised
  InternalVerdict = object
    case kind: InternalVerdictKind
    of ivSat:    witness: RawWitness
    of ivUnsat, ivUnknown: discard
    of ivRaised:
      raisedTypeId: string
      raisedMsg:    Option[string]
      witness:      RawWitness
  ```
  Add `toPublic(iv: InternalVerdict): RawResult` proc called exactly once
  per finding at the `runSymex` boundary.
  Replace the E2a stub `of sxRaised:` arm in `walk(isRaise)` with the
  real implementation: evaluate `stmt.raiseMsg` via `walkExpr`
  (nil/absent → `none(string)`); extract witness from current path's
  env (same as `ivSat` path); return
  `InternalVerdict(kind: ivRaised, raisedTypeId: stmt.raiseTypeId,
  raisedMsg: msg, witness: rw)`. Bare `raise` (`raiseIsReraise = true`)
  with an empty handler stack and no in-flight exception emits
  `eeRaiseOutsideHandler` (classified error, `sevError` — Invariant 3).
  Bare `raise` with an in-flight exception re-raises it.

  Top-level `runSymex`: call `toPublic(iv)` on each `ivRaised` verdict
  at the SUT boundary and append to `w.found`.

  `w.frame.inFlightExn: Option[ExnRecord]` is set on
  `ExceptHandler` body entry (from E1's `CallFrameCtx`).

**DoD:**
- [ ] Both E2b test cases pass under `isExact` and `isOptimised`
- [ ] `sxRaised` verdict cached under `cacheKeyRaised(typeId)` key; second run is a cache hit
- [ ] `sfRaised` finding emitted in `Report.symexFindings`
- [ ] `raisedMsg` populated from `stmt.raiseMsg` when present
- [ ] `InternalVerdict` private union introduced; `toPublic` called exactly once per finding at `runSymex` boundary; no `sxRaised` escapes internal handler-stack code
- [ ] All prior E1 + E2a + Cluster S tests green

---

### E3 — `try` / `except` matching by type (first-match, catch-all)

**What it does:** Implements the `isTry` walker path for the normal
exception-matching case: the try body is walked; if it produces
`ivRaised`, the handler stack is consulted and the first matching
`ExceptHandler` wins. Multi-clause `except` branches (e.g. `except
ValueError, IOError:`) are modeled as a type-set membership test.
A bare `except:` clause catches everything. If no handler matches,
the `ivRaised` propagates up.

**Inter-procedural `ivRaised` propagation.** The `isCall`/`isGenericCall`/
`iekClosureCall` walker arms must propagate a callee `InternalVerdict(ivRaised)`
into the caller's handler-stack search. After descending into the callee
body (on the current `CallFrameCtx`), if the callee returns `ivRaised`,
that result is merged back into the caller's handler stack using the
heap state at the raise point per R1b (merging `path.heaps` and
`path.allocCounters`). This is the inter-procedural raise propagation
path; without it, a raise inside a helper proc escapes the caller's
`try/except` invisibly.

**Transitional handler matching.** E3's `stmt.raiseTypeId in handler.typeIds`
check is exact-string membership — a transitional simplification. It is
**superseded by E4's `isSubtypeOf`** check. At the E3 stage a
`CatchableError` handler does NOT catch a `ValueError` raise (this will
be fixed in E4). A negative DoD test documents and enforces this
transitional behavior.

**RED test:** `tests/symex/tsymex_phase15_E3_try.nim`. Five test
cases:

1. `"E3: raise inside try caught by matching except"` — SUT:
   ```nim
   proc f(x: int): int =
     try:
       if x < 0: raise newException(ValueError, "neg")
       result = x
     except ValueError:
       result = -1
   ```
   `symexFind(f, tLabel("done"))` on the normal path returns a
   witness with `x >= 0`; a separate `symexFind` for the
   except-handler body (a `symexTarget("caught")` marker inside the
   handler) returns `x < 0`.

2. `"E3: unmatched exception type propagates past try"` — SUT has
   `except IOError:` but raises `ValueError`; `symexFind` returns
   `sxRaised{typeId: "ValueError"}` at the SUT boundary.

3. `"E3: bare except catches all"` — SUT raises any exception;
   `except:` handler runs; `symexFind` finds the handler body.

4. `"E3: inter-proc raise propagates into caller handler"` — SUT:
   ```nim
   proc helper(x: int) =
     if x < 0: raise newException(ValueError, "neg")
   proc f(x: int): int =
     try:
       helper(x)
       result = x
     except ValueError:
       result = -1
   ```
   `symexFind(f, tLabel("caught"))` returns `sxSat` with witness
   `x < 0`. Verifies that `helper`'s `ivRaised` propagated into `f`'s
   handler stack and the `except ValueError:` matched.

5. `"E3: CatchableError handler does NOT catch ValueError at E3 stage"` —
   (negative transitional test) SUT raises `ValueError`; handler is
   `except CatchableError:`; exception propagates to boundary as
   `sxRaised{typeId: "ValueError"}`. This transitional behavior is
   correct at E3 and will be superseded in E4.

**GREEN:**

- `src/proptest/smt/runtime.nim` — implement `walk(isTry)`:
  1. Push a `HandlerFrame{handlers: stmt.tryHandlers, finallyBlock:
     stmt.tryFinally}` onto `w.frame.handlerStack`.
  2. Walk `stmt.tryBody`.
  3. Pop the handler frame.
  4. If the body result is `ivRaised`: iterate `frame.handlers` in
     order; for each handler, check `stmt.raiseTypeId in
     handler.typeIds` (or `handler.typeIds.len == 0` for bare
     `except:`). On first match, walk the handler body on the raised
     path (using the raised path's `pc` and `env`). The handler body
     is walked with the raise-site's `path.heaps`, `path.heapDepth`,
     and `path.allocCounters` — heap mutations performed in the try
     body before the raise are visible to the handler body. (Heap
     fields are on `Path` via Cluster H/R0.) If no match, let the
     `ivRaised` propagate.
  5. `finally` handling deferred to E5; stub: if `tryFinally != nil`,
     walk it on the normal path only (raised-path finally is E5's
     work — stub raises `SymexErrorInfo{kind: eeFinallyRaisedUnimplemented,
     severity: sevError}`).
  - In `isCall`/`isGenericCall`/`iekClosureCall` arms: after descending
    into callee body, if callee returns `ivRaised`, propagate it into
    `w.frame.handlerStack` search (same matching logic as inline `isTry`).
    Merge `path.heaps` / `path.allocCounters` per R1b at the raise point.

**DoD:**
- [ ] Test cases 1–4 pass under both backends
- [ ] Negative transitional test (case 5): `CatchableError` handler does NOT catch `ValueError` at E3 stage
- [ ] Unmatched-type propagation reaches SUT boundary as `sxRaised`
- [ ] Handler-stack depth tracked; exceeding `maxCallDepth` produces `sxUnknown` with `SymexErrorInfo` (not silent)
- [ ] Inter-proc raise propagation: callee `ivRaised` merges into caller's handler stack
- [ ] E1 + E2a + E2b tests still green

---

### E4 — Exception type hierarchy (subtype catch)

**What it does:** Extends the type-matching in E3's handler search to
honor Nim's exception hierarchy. An `except CatchableError:` clause must
catch a raised `ValueError` because `ValueError` is-a `CatchableError`
is-a `Exception`. The walker performs a subtype check via a static
`ExnTypeTable` built at parse time from the Nim type-class hierarchy;
this is a pure lookup, not a Z3 query.

The `ExnTypeTable` is the authoritative coverage list for standard
Nim exception types. User-defined `Defect` subtypes that are not in the
static table map to `dkOther` (see E6 and Feas-LOW-1). The inclusion
check ("`is this type a Defect?`") continues to work for unknown subtypes
via the `dkOther` fallback.

**RED test:** `tests/symex/tsymex_phase15_E4_hierarchy.nim`. Three test
cases:

1. `"E4: base-type except catches derived raise"` — SUT raises
   `ValueError`; handler has `except CatchableError:` with a
   `symexTarget("caught_by_base")` marker; `symexFind` for that
   label finds a witness.

2. `"E4: sibling type does not match"` — SUT raises `ValueError`;
   handler has `except IOError:`; exception propagates to boundary
   as `sxRaised{typeId: "ValueError"}`.

3. `"E4: user-defined Defect subtype routes to dkOther; inclusion check works"` —
   SUT: `type MyDefect = object of Defect`. SUT raises `MyDefect`;
   `w.statics.exnTable.isDefect("MyDefect")` returns `true` (via `dkOther`
   fallback); the finding has `isDefect = true`.

**GREEN:**

- `src/proptest/smt/dsl_typebridge.nim` (or a new
  `src/proptest/smt/exn_hierarchy.nim`) — define `ExnTypeTable`:
  a `Table[string, seq[string]]` mapping each exception type name to
  its ancestors in the Nim standard hierarchy. Populate the full
  standard-library hierarchy at minimum:
  `Exception → CatchableError → {ValueError, IOError, OSError,
  KeyError, IndexDefect, FieldDefect, AssertionDefect, …}` plus
  `Defect → {IndexDefect, FieldDefect, AssertionDefect,
  OutOfMemoryDefect, …}`. The table is a compile-time constant.
  Add `isDefect(typeId: string): bool` that checks the hierarchy
  and returns `true` for any known `Defect` subtype or for
  unknown types whose direct parent (in `userExnHierarchy`) traces
  to `Defect` (via `dkOther` fallback).

- `src/proptest/smt/runtime.nim` — replace the exact `typeId ∈
  handler.typeIds` check in `walk(isTry)` with
  `isSubtypeOf(raised, handlerType, w.statics.exnTable,
  w.statics.userExnHierarchy)` where `isSubtypeOf` walks the ancestor
  chain. Unknown exception types (not in the table and not in
  `userExnHierarchy`) emit `SymexErrorInfo{kind: eeUnknownExnType,
  severity: sevWarning, msg: typeId}` and conservatively match
  `except:` only (no silent false-negative — Invariant 3).

**DoD:**
- [ ] Test cases 1–3 pass under both backends
- [ ] Unknown exception type produces classified `SymexErrorInfo{severity: sevWarning}`, not a silent miss
- [ ] `ExnTypeTable` covers at minimum: `Exception`, `CatchableError`, `Defect`, `ValueError`, `IOError`, `OSError`, `KeyError`, `IndexDefect`, `FieldDefect`, `AssertionDefect`, `OutOfMemoryDefect`, `StackOverflowDefect`
- [ ] User-defined `Defect` subtype routes to `dkOther`; `isDefect` returns `true` for it
- [ ] E1–E3 tests still green

---

### E4a — Dynamic user-exception hierarchy table

**What it does:** Closes the soundness gap for user-defined exception
types (round-1 CRIT finding C7). The static `ExnTypeTable` built in E4
only covers the Nim standard library hierarchy; a SUT that defines
`type MyError = object of ValueError` will silently fail to match an
`except ValueError:` handler without E4a.

E4a adds a parser pass that walks `nnkTypeDef` ancestors of every type
symbol appearing in `nnkExceptBranch` via `getImpl`, collects the
inheritance chain up to a known exception base (`Exception` or `Defect`),
and populates `userExnHierarchy: Table[string, string]` (child → direct
parent). At walk time, `isSubtypeOf` consults both the static
`ExnTypeTable` AND `w.statics.userExnHierarchy`.

**RED test:** `tests/symex/tsymex_phase15_E4a_userexn.nim`. Two test
cases:

1. `"E4a: user-defined exception subtype matched by base handler"` —
   SUT:
   ```nim
   type MyError = object of ValueError
   proc f(x: int) =
     try:
       raise newException(MyError, "custom")
     except ValueError:
       symexTarget("caught_by_base")
   ```
   `symexFind(f, tLabel("caught_by_base"))` returns `sxSat` (witness
   exists). Without E4a, this case would silently produce `sxRaised`
   at the SUT boundary (soundness failure).

2. `"E4a: unrelated user type not matched by unrelated handler"` — SUT
   defines `type SomeError = object of IOError`; handler is
   `except ValueError:`; exception propagates to boundary as
   `sxRaised{typeId: "SomeError"}`.

**GREEN:**

- `src/proptest/smt/dsl_parser.nim` — after collecting `nnkExceptBranch`
  type symbols, call a new `collectUserExnAncestors(typeSym)` helper
  that calls `typeSym.getImpl` and walks `nnkObjectTy`'s inherit field
  to retrieve the parent type symbol. Recurse until reaching a type in
  `ExnTypeTable` or the end of the chain. Populate
  `parserCtx.userExnHierarchy: Table[string, string]` (child name →
  parent name). The table is thread-local to the parse phase; it is
  passed to `WalkerStatics` at parse completion.

- `src/proptest/smt/runtime.nim` — extend `isSubtypeOf` to consult
  `w.statics.userExnHierarchy` as a fallback when the type is not in
  the static `ExnTypeTable`. `WalkerStatics` already has
  `userExnHierarchy: Table[string, string]` from E1 (populated here).

**DoD:**
- [ ] Both E4a test cases pass under both backends
- [ ] User-defined exception subtype correctly matched by ancestor handler
- [ ] Unknown hierarchy types still produce classified `SymexErrorInfo` (not silent miss)
- [ ] E1–E4 tests still green

---

### E5 — `finally` semantics (both paths; finally-raises-replaces)

**What it does:** Completes the `isTry` walker: the `finally` block runs
on both the normal exit path and the raised exit path. If the `finally`
block itself produces `ivRaised`, that new exception replaces the
in-flight one (Nim's documented semantics). The stub installed in E3 is
replaced with the full implementation. Specifies the `inFlightExn`
lifecycle on `CallFrameCtx` and heap-state threading through `finally`.

**Multi-path finally threading.** After walking `tryBody`, all exit
continuations are collected: normal-exit continuations, raised-exit
continuations, and any per-fork sub-paths produced by conditional
branches inside the try body. For each continuation, `tryFinally` is
walked starting from that continuation's path state (its `path.heaps`,
`path.heapDepth`, `path.allocCounters`, and `path.pc`). The finally
walk produces its own exit continuations; these are combined according
to the rules:
- normal-exit + finally-normal = normal (original try-body result)
- raised-exit + finally-normal = re-raised (original exception preserved)
- any + finally-raised = finally-raised wins (new exception replaces original)

**Finally-raised heap state.** The `InternalVerdict(ivRaised)` produced
by the finally body carries `path.heaps` as of the raise point inside
the finally body — which includes all pre-raise writes made by the
finally body itself (and by the try body before the raise). Both sets
of writes are visible in the resulting witness.

**RED test:** `tests/symex/tsymex_phase15_E5_finally.nim`. Three test
cases:

1. `"E5: finally runs on normal exit"` — SUT:
   ```nim
   proc f(x: int): int =
     try:
       result = x * 2
     finally:
       symexTarget("finally_normal")
   ```
   `symexFind(f, tLabel("finally_normal"))` returns `sxSat` with any
   witness (the `finally` marker is always reachable on the normal
   path).

2. `"E5: finally raises replaces in-flight exception"` — SUT:
   ```nim
   proc f(x: int): int =
     try:
       raise newException(ValueError, "original")
     finally:
       if x > 100: raise newException(IOError, "overrides")
   ```
   `symexFind(f, stkRaisedExn{typeFilter: "IOError"})` returns
   `sxRaised{typeId: "IOError"}` with witness `x > 100`.
   `symexFind(f, stkRaisedExn{typeFilter: "ValueError"})` returns
   `sxRaised{typeId: "ValueError"}` with witness `x <= 100`.

3. `"E5: finally heap state includes pre-raise finally writes"` — SUT:
   ```nim
   proc f(p: ptr int, q: ptr int) =
     try:
       p[] = 7
     finally:
       q[] = 99
       raise newException(ValueError, "finally-raised")
   ```
   `symexFind(f, stkRaisedExn{typeFilter: "ValueError"})` returns a
   witness where both `p[] == 7` (from try body) and `q[] == 99`
   (from finally before raise) are visible.

**GREEN:**

- `src/proptest/smt/runtime.nim` — replace the E3 finally stub with
  full implementation in `walk(isTry)`. Specify the `inFlightExn`
  lifecycle on `w.frame`:

  - `w.frame.inFlightExn: Option[ExnRecord]` (from E1's `CallFrameCtx`).
  - **Set** when entering a matching `ExceptHandler` body (set to the
    caught exception's `ExnRecord`).
  - **Cleared** when the handler body exits normally.
  - In `finally`: walked on all exit continuations (normal and raised).
  - A bare `raise` inside `finally` on a **normal** path (no current
    in-flight exception) produces a fresh `ivRaised` from the finally
    body itself — NOT a `eeRaiseOutsideHandler` classified error.
  - In `finally`: if the in-flight exception is replaced by a new raise
    from finally, the new one wins (matches Nim runtime semantics).

  Implementation steps:
  1. After walking the try body, enumerate all exit continuations
     (one per path fork in the try body). Record each as normal or
     `ivRaised` with its `path.heaps`/`heapDepth`/`allocCounters`.
  2. For each continuation, walk `tryFinally` starting from that
     continuation's path state.
  3. Combine each (try-exit, finally-exit) pair per the cross-product
     rules above.
  4. Collect the combined results as the `isTry` statement's output
     continuations.

**DoD:**
- [ ] All three E5 test cases pass under both backends
- [ ] Finally-raised-replacement produces correctly typed `sxRaised` verdict
- [ ] Finally on normal path does not alter the normal result
- [ ] `w.frame.inFlightExn` set on handler entry, cleared on normal handler exit
- [ ] Bare `raise` in `finally` on normal path produces `ivRaised`, not `eeRaiseOutsideHandler`
- [ ] `path.heaps`/`heapDepth`/`allocCounters` from each exit continuation propagated into finally walk
- [ ] Finally-raised heap state includes both try-body and pre-raise finally-body writes (test case 3)
- [ ] E1–E4a tests still green

---

### E6 — `Defect` modeling (default: `sxRaised` with `isDefect = true`)

**What it does:** Implements ADR-0007's closed default policy (Open
question 4 resolved in v2 preamble) for Nim `Defect` subtypes:
`assert false` (which raises `AssertionDefect`), OOB index when modeled
as a raise rather than via `stkIndexError`, and other `Defect` raises
all produce `sxRaised{typeId: ..., isDefect: true}` rather than
`sxUnreached`. The `isDefect` flag allows consumers to distinguish
contract violations from ordinary exception witnesses. `SymexFinding.sfRaised`
gains a `defectTypeId: string` field for display. Note: the existing
`stkIndexError` and `stkFieldDefect` targets (Phases 4 and 11) are NOT
changed — they already produce `sxSat` witnesses under their own target
semantics. E6 only affects the `sxRaised` propagation path when a Defect
is raised via `raise` syntax or via the implicit Defect raise that the
runtime emits for `assert`.

`OutOfMemoryDefect` and `StackOverflowDefect` are excluded by default
via `defectExclusions: set[DefectKind]` in `SymexSettings`
(round-2 MED finding M1). `DefectKind` is an enum whose variants cover
the standard-library Defect hierarchy; `dkOther` covers all
user-defined `Defect` subtypes. Because user-defined defects map to
`dkOther`, they cannot be individually excluded — either all user
defects are excluded (by including `dkOther` in `defectExclusions`) or
none are. This limitation is documented in the `SymexSettings` API
comment.

**RED test:** `tests/symex/tsymex_phase15_E6_defect.nim`. Two test
cases:

1. `"E6: assert false produces sxRaised with isDefect"` — SUT:
   ```nim
   proc f(x: int) =
     assert x > 0, "must be positive"
   ```
   `symexFind(f, stkRaisedExn{typeFilter: "AssertionDefect"})` returns
   `sxRaised{typeId: "AssertionDefect", isDefect: true}` with witness
   `x <= 0`.

2. `"E6: Defect does not silently pass as sxUnreached"` — same SUT;
   `symexFind(f, tLabel("never_reached"))` returns a result where
   `Report.symexFindings` includes an `sfRaised` entry for
   `AssertionDefect`, not `sxUnsat` on the defect path. A property
   test that calls `f` with a negative input would fail at runtime —
   the symex must surface, not suppress, this.

**GREEN:**

- `src/proptest/engine/types.nim` — add `DefectKind` enum:
  `dkAssertionDefect | dkIndexDefect | dkFieldDefect |
  dkOutOfMemoryDefect | dkStackOverflowDefect | dkOther`.
  Replace `defectExclusions: set[string]` in `SymexSettings` with
  `defectExclusions: set[DefectKind]`. Default:
  `{dkOutOfMemoryDefect, dkStackOverflowDefect}`. Add API comment
  documenting that `dkOther` covers all user-defined Defect subtypes.

- `src/proptest/smt/types.nim` — `sxRaised` branch of `RawResult`
  already has `isDefect: bool` from E2a (initialized to `false`).
  Populate it `true` in E6 by consulting `w.statics.exnTable.isDefect(typeId)`.

- `src/proptest/smt/runtime.nim` — in `walk(isRaise)`, after
  constructing the `InternalVerdict`, set `iv.raisedIsDefect =
  w.statics.exnTable.isDefect(stmt.raiseTypeId)`. For `assert false`
  (which the parser already lowers to `symexAssert(false)` in the
  `tAssertionViolation` flow), add a parallel path: when a SUT
  `assert cond` is parsed outside a `tAssertionViolation` target
  context, the parser also emits an `isRaise` for the implicit
  `AssertionDefect` on the false branch. The `isRaise` carries
  `raiseTypeId = "AssertionDefect"`.

- `src/proptest/symex.nim` — `sfRaised` finding rendering: include
  `isDefect` flag in the `SymexFinding` record and surface it in the
  report rendering.

**DoD:**
- [ ] Both E6 test cases pass under both backends
- [ ] `isDefect = true` on all `Defect`-hierarchy raises; `false` on `CatchableError` raises
- [ ] `DefectKind` enum in `engine/types.nim`; `defectExclusions: set[DefectKind]` in `SymexSettings`
- [ ] `dkOther` covers user-defined `Defect` subtypes; API comment documents individual-exclusion limitation
- [ ] Existing `stkIndexError` and `stkFieldDefect` paths unchanged (no regression)
- [ ] `OutOfMemoryDefect` and `StackOverflowDefect` excluded by default; overridable via `SymexSettings`
- [ ] E1–E5 tests still green

---

### E7 — regression smoke against Cluster S + multi-frame re-raise test

**What it does:** Runs the full Cluster S test suite under the Cluster E
walker state (which now has `w.frame.handlerStack`, `w.frame.inFlightExn`,
and the `sxRaised` verdict path active) to catch state-threading bugs
introduced by Cluster E's changes to `WalkCtx`. Additionally implements
and tests the multi-frame scenario: a `try`-in-`try` nesting where the
inner handler re-raises with a bare `raise`, which must pop to the outer
handler frame and match there. Includes an E+heap-threading composition
test using integer-local variables (safe for Phase-14-era machinery).
Includes a multi-finding cache round-trip test (complementary to E2a's
DoD). Bumps the walker version `"6"→"7"` in `canonicalize.nim`
(Invariant 6 — the single source of truth; `canonicalize.walkerVersion`
constant, not anything in `runtime.nim`).

**E+R composition scope.** The `ptr T` + finally composition test that
appeared in v2 is moved to Cluster R (R13 scope) because `isDeref` does
not exist until R1. E7's composition test uses integer-local heap-state
threading instead (round-2 Feas-H12).

**RED test:** `tests/symex/tsymex_phase15_E7_regression.nim`. Five
test cases:

1. `"E7: Cluster S full-string SUTs unaffected by handlerStack"` —
   runs a representative sample of five Cluster S SUTs (chosen to
   exercise `svString`, `svSeq`, and `svTable` paths) through
   `symexFind` and asserts their verdicts are unchanged from the
   Cluster S reference run. This is a regression-smoke canary: if
   `WalkCtx` state threading is broken, these will diverge.

2. `"E7: E+heap composition — heap-state threading through finally (integer locals)"` — SUT:
   ```nim
   proc f(x: int): bool =
     var n = x
     try:
       n += 1
     finally:
       if n > x: raise newException(ValueError, "incremented")
   ```
   `symexFind(f, stkRaisedExn{typeFilter: "ValueError"})` returns
   `sxRaised{typeId: "ValueError"}` with a witness satisfying
   `n == x + 1` (i.e. `n > x` after the try body's increment).
   Verifies heap-state-style threading through finally using
   Phase-14-era machinery (no `ptr T` deref required).

3. `"E7: nested try with re-raise pops to outer handler"` — SUT:
   ```nim
   proc f(x: int): int =
     try:
       try:
         if x < 0: raise newException(ValueError, "inner")
         result = x
       except IOError:
         result = -99   ## does not match; bare raise propagates
         raise
     except ValueError:
       symexTarget("outer_caught")
       result = -1
   ```
   `symexFind(f, tLabel("outer_caught"))` returns `sxSat` with
   witness `x < 0`. Verifies: inner `except IOError:` did not match;
   bare `raise` in an except handler re-raised to the outer try;
   outer `except ValueError:` matched.

4. `"E7: re-raise outside any handler produces classified error"` —
   SUT containing a bare `raise` at the top level (not inside any
   `except` branch) produces `SymexErrorInfo{kind: eeRaiseOutsideHandler,
   severity: sevError}`, not a panic or silent `sxUnknown`.

5. `"E7: multi-finding cache round-trip (E7 complement)"` — same
   two-raise-path SUT as E2a test case 2 (`ValueError` on `x < 0`,
   `IOError` on `x == 0`). After a full `symexFindAllWitnesses` run,
   reload from DB with empty in-memory state and assert both findings
   are present (`found.len == 2`, correct `raisedTypeId` values). This
   complements E2a's structural round-trip with a semantically-complete
   run.

**GREEN:**

- No new production-code changes except: verify and (if needed)
  fix that `WalkCtx` initialization at `runSymex` zeroes
  `w.frame` (`handlerStack`, `inFlightExn`) to their correct defaults.
  Any Cluster S state-threading bug surfaces here and is fixed before
  marking E7 green.

- `src/proptest/smt/runtime.nim` — `walk(isRaise)` re-raise branch
  (`raiseIsReraise = true`): check `w.frame.inFlightExn.isSome`; if
  not, emit `eeRaiseOutsideHandler` error (`sevError`); if yes, re-raise
  `w.frame.inFlightExn.get` as the active `ivRaised`. Set
  `w.frame.inFlightExn = some(ExnRecord{typeId: stmt.raiseTypeId})`
  when entering an `ExceptHandler` body so that bare `raise` inside a
  handler re-raises the caught exception.

- `src/proptest/smt/canonicalize.nim` — bump `walkerVersion` from
  `"6"` to `"7"` (Invariant 6: this file is the single source of truth).

**DoD:**
- [ ] All five E7 test cases pass under both backends
- [ ] Cluster S representative sample produces identical verdicts (zero divergence)
- [ ] `re-raise outside handler` produces `SymexErrorInfo{kind: eeRaiseOutsideHandler, severity: sevError}`, not panic
- [ ] E+heap composition test (integer-local) verifies heap-state threading through finally
- [ ] Multi-finding cache round-trip (test case 5) passes: both findings reloaded from DB
- [ ] All 76 prior-cluster test files green (full regression sweep, not just sample)
- [ ] `determinism.md` gains an "Exceptions" subsection documenting `sxRaised` cache key proc `cacheKeyRaised(typeId)`, `isDefect` semantics, and the handler-stack depth bound
- [ ] Walker version bumped `"6"→"7"` in `canonicalize.walkerVersion` constant in `canonicalize.nim`
- [ ] `SYMEX_PLAN.md` Cluster E row marked SHIPPED with test count updated

---

### E8 — `getCurrentException()` / `getCurrentExceptionMsg()`

**What it does:** Implements the two Nim standard library intrinsics for
querying the in-flight exception from inside an `except` handler body.
Both are only valid inside an `except` handler body (when
`w.frame.inFlightExn.isSome`); out-of-handler calls emit a classified
error.

- `getCurrentException()` returns `svUninterpRef(sortName: "Exn_" & typeId,
  typeTag: typeId)` with a fresh constant. `svUninterpRef` is already
  present in `SVKind` (added in Z3); E8 consumes it. The returned ref
  is an opaque handle; field access on it produces classified errors
  (exception fields are not modeled symbolically).
- `getCurrentExceptionMsg()` returns
  `svString(w.frame.inFlightExn.get.msg.get(""))`. If `msg` is `none`
  (zero-arg `raise newException(T)` with no message), the empty string
  is returned — matching Nim runtime behaviour.
- Out-of-handler calls emit `SymexErrorInfo{kind: eeNotInHandler,
  severity: sevError}`.
- `extractFromSymVal(svUninterpRef)` emits
  `SymexErrorInfo{kind: eeUninterpRefExtraction, severity: sevHint}`
  as an informational hint (not a halting error).

**RED test:** `tests/symex/tsymex_phase15_E8_getcurrentexn.nim`. Four
test cases:

1. `"E8: getCurrentExceptionMsg returns in-flight msg"` — SUT:
   ```nim
   proc f(x: int): string =
     try:
       raise newException(ValueError, "hello")
     except ValueError:
       result = getCurrentExceptionMsg()
   ```
   `symexFind(f, tLabel("done"))` returns `sxSat` with the result
   string constrained to `"hello"`.

2. `"E8: getCurrentException returns svUninterpRef tagged with typeId"` —
   SUT inside an `except ValueError:` handler calls
   `getCurrentException()`; the returned `SymVal` has kind `svUninterpRef`
   and its `sortName` matches `"Exn_ValueError"` and `typeTag` matches
   `"ValueError"`.

3. `"E8: getCurrentExceptionMsg outside handler produces classified error"` —
   SUT calls `getCurrentExceptionMsg()` outside any `except` body;
   result is `SymexErrorInfo{kind: eeNotInHandler, severity: sevError}`,
   not a panic.

4. `"E8: getCurrentExceptionMsg with no-msg raise returns empty string"` —
   SUT: `raise newException(ValueError)` (no message argument); handler
   reads `getCurrentExceptionMsg()`; result string equals `""`. Verifies
   the `msg.get("")` fallback for zero-arg `raise`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — add walker cases for the magic calls
  `getCurrentException` and `getCurrentExceptionMsg` (recognized by
  symbol name in `walkExpr` dispatch):
  - Guard: if `w.frame.inFlightExn.isNone`, emit
    `SymexErrorInfo{kind: eeNotInHandler, severity: sevError}` and
    return `svUnknown`.
  - `getCurrentExceptionMsg()`: return
    `svString(w.frame.inFlightExn.get.msg.get(""))`.
  - `getCurrentException()`: construct a fresh constant name
    `freshSym("Exn_" & w.frame.inFlightExn.get.typeId)` and return
    `svUninterpRef(sortName: "Exn_" & typeId, typeTag: typeId)`.
  - In `extractFromSymVal`: add `of svUninterpRef:` arm that emits
    `SymexErrorInfo{kind: eeUninterpRefExtraction, severity: sevHint}`
    and returns a default value.

**DoD:**
- [ ] All four E8 test cases pass under both backends
- [ ] `getCurrentExceptionMsg` returns correct string from `w.frame.inFlightExn.msg`
- [ ] `getCurrentExceptionMsg` with no-msg raise returns `""` (test case 4)
- [ ] `getCurrentException` returns `svUninterpRef` with `sortName = "Exn_" & typeId` and correct `typeTag`
- [ ] `extractFromSymVal(svUninterpRef)` emits `eeUninterpRefExtraction` hint (`severity: sevHint`)
- [ ] Out-of-handler call produces `eeNotInHandler` classified error (`severity: sevError`), not panic
- [ ] E1–E7 tests still green

<!-- CLUSTER_G -->
## Cluster G — generics

### Preamble

**ADR-0008 summary.** Generic proc support in the symex engine uses
per-call-site monomorphization with a global instantiation cache keyed
by `(symBodyHash(calleeSym), instTypeTuple)`. Every distinct
instantiation is stored as its own typed-body `ProcSig`; the walker
dispatches to the cached `ProcSig` for each call site. `distinct T` and
concept-constrained generics participate in the same cache under their
resolved concrete type tuples. The decision is final: no symbolic
generic walking, no type-variable theory in Z3. ADR-0008 is authored as
pre-cycle work and must land before G1a.

**Why not symbolic generic walking.** Z3 has no type-variable theory.
Modeling a generic `proc foo[T](x: T): T` symbolically would require
inventing one — essentially encoding parametric polymorphism as a Z3
uninterpreted-function family indexed by a synthetic sort. This is
neither sound (you cannot express Z3 constraints over an unknown sort's
operations) nor necessary: Nim's semchecker already monomorphizes every
call site before proptest's macro sees the typed AST. Per-call-site
monomorphization at the IR layer matches Nim's own compilation model and
is provably sound — the concrete body parsed at instantiation time is
the exact code the program runs.

**`distinct T` is a fresh Z3 sort, not an alias.** When a user writes
`type Meters = distinct float`, the semantic intent is that `Meters` and
`float` are incompatible at the type level. The symex engine honors this
wall: `distinct T` is mapped to a new uninterpreted Z3 sort allocated via
`Z3_mk_uninterpreted_sort` (through `sort.nim`'s `mkUninterpretedSort`,
which returns `Z3Sort[stUninterpreted]` directly). The phantom-typed
`Z3UninterpretedVal[T]` API cannot be used here because `T` is a
runtime-known type name, not a compile-time type parameter. An explicit
`inject_T: Base → Distinct` function maps base-type values into the
distinct sort; a matching `eject_T: Distinct → Base` function maps back.
Bijectivity axioms are asserted: `∀ x: Base. eject(inject(x)) == x` and
`∀ y: Distinct. inject(eject(y)) == y`. No implicit coercion is ever
emitted. Witness extraction for `distinct`-typed parameters goes through
ejection — the extractor calls `eject_T(witness)` then the base-type
extractor. This is not a conservative approximation — it is the correct
model. A symex that aliased `Meters` to `float` would prove false
equalities and miss real type-boundary bugs.

**Open question 5 — closed.** The cap on instantiations per proc is
`maxInstantiationsPerProc = 64`. This matches the existing settings
family (`maxFrontierSize`, `maxCallDepth`) and is sufficient for all
known generic-heavy PBT patterns. Overflow yields `sxUnknown` with
`SymexErrorInfo{kind: geInstantiationCapped, procSym, observedCount}`.

**Error prefix convention.** All error kinds introduced in Cluster G use
the `ge` prefix (generics errors): `geInstantiationCapped`,
`geConceptViolation`, `geUnresolvedGeneric`, `geDistinctBarrier`,
`geVtableDispatch`. Documented in `determinism.md`. The formerly-named
`heInstantiationCapped`, `heConceptViolation`, and `heUnresolvedGeneric`
are renamed accordingly throughout this cluster.

**Subtype polymorphism is explicitly out of scope.** Cluster G covers
parametric polymorphism (`proc foo[T]`). Subtype polymorphism — dispatch
through an inheritance hierarchy via `RootRef`/`RootObj`-rooted vtables
— is a separate modeling problem (vtable encoding) and is deferred to
Phase 16+ per the parent RFC's scope table. Any call site in a SUT that
dispatches through a vtable will produce `sxUnknown` with a classified
`geVtableDispatch` error rather than silently falling back.

**Out of scope for this cluster.**

| Item | Rationale / deferral |
|------|----------------------|
| Subtype polymorphism via `RootRef`/`RootObj` vtable dispatch | Phase 16; vtable encoding is a separate modeling problem. Produces `geVtableDispatch` classified error. |
| Variance annotations | Nim has no variance annotations; the question is trivially moot. |
| `concept` bodies with effect tracking | Semchecker enforces concept constraints; effect-aware re-validation is out of scope for Phase 15. |
| Generic parameter constraints requiring SMT-solvable type-arithmetic (e.g., `T: static[int] where T mod 2 == 0`) | Semchecker enforces these at compile time; the walker receives the resolved literal and treats it as such. |

**Cluster G cycle table.**

| Cycle | Topic | Key dependency |
|-------|-------|----------------|
| G0-ADR | Author `docs/symex/ADR-0008-generic-instantiation.md` | — |
| G1a | IR extension: `isGenericCall`, `mkGenericCall`, runtime dispatch stubs | G0-ADR |
| G1b | Parser: `gatherTypeSubst`, `parseCalleeImpl`, `emitGenericCall` | G1a |
| G1c | Walker dispatch + instantiation cache + cap (folds former G2 + G9) | G1b |
| G3 | Type-substitution path through `classifyType`; `auto` return type safety | G1c, Cluster F |
| G4 | `distinct T` as fresh uninterpreted sort + inject + eject + bijectivity | G1c |
| G5 | `distinct` borrow semantics | G4 |
| G6 | Concept constraints: trust boundary + compound constraints | G1c |
| G7 | `static[T]` parameters as instantiation-key components | G1c |
| G8 | Multi-parameter generics | G1c, Cluster S |
| G10 | Regression smoke against Cluster E + walker version bump `"7"→"8"` | G8, G7, G6, G5 |
| G2 | ~~Instantiation cache~~ | Folded into G1c (v2 revision history) |
| G9 | ~~Concept stdlib table~~ | Folded into G1c (v2 revision history) |

---

### G0-ADR — Author ADR-0008: generic instantiation policy

**What it does:** Authors `docs/symex/ADR-0008-generic-instantiation.md`
before any Cluster G feature code lands. This is a doc-authoring cycle
only: no RED test, no production source changes. The ADR establishes the
architectural constraints that all subsequent G-cluster cycles implement.

**Coverage (per ADR-0008):**

- **Per-call-site monomorphization** as the only supported strategy; no
  symbolic generic walking (rejected: Z3 has no type-variable theory).
- **Instantiation-key schema**: `symBodyHash(calleeSym)` as the primary
  name component; fallback to `getImpl.lineInfo.filename & ":" &
  calleeSym.strVal` when `symBodyHash` returns 0 or is unavailable.
  Explicitly **not** `repr(calleeSym.getImpl).hash` — structurally
  ambiguous across modules (Feas-H5).
- **Instantiation cache schema**: `ParseCtx.instCache: Table[string,
  ProcSig]` and `ParseCtx.instCountPerProc: Table[string, int]`;
  per-walker (created once per `runSymex`); distinct from the DB-layer
  verdict cache.
- **`distinct T` as a fresh uninterpreted sort**: inject/eject functions;
  bijectivity axioms only for base types in `{int, BV, bool}`; skipped
  for `{FP, String}` with `geDistinctBijectivitySkipped` hint;
  distinct sort cache on `WalkerStatics.distinctSorts` (not per-frame).
- **Nested distinct chains**: recursive ejection + bijectivity at each
  level (where decidable).
- **Concept policy**: stdlib concepts validated against membership table;
  user-defined concepts trusted to the semchecker.
- **`maxInstantiationsPerProc = 64`**: rationale and overflow behaviour.
- **Rejected alternatives**: symbolic walking, `repr.hash` key,
  per-frame sort cache.

**GREEN:**
- `docs/symex/ADR-0008-generic-instantiation.md`: authored with all
  sections above. Matches ADR-0001..0004 depth (Context, Decisions,
  Rejected alternatives, Consequences, Validation).

**DoD:**
- [ ] `docs/symex/ADR-0008-generic-instantiation.md` committed
- [ ] ADR covers: monomorphization policy, key schema with fallback,
  cache schema, `distinct T` encoding, bijectivity decidability
  boundary, concept policy, `maxInstantiationsPerProc`, all rejected
  alternatives
- [ ] ADR index table in cross-cluster section updated with ADR-0008
  row (governs: Cluster G; depends-on: ADR-0001 integer semantics)

---

### G1a — IR extension: `isGenericCall`, `mkGenericCall`, runtime dispatch stubs

**What it does:** Introduces the `isGenericCall` IR statement kind and
the `mkGenericCall` constructor into `types.nim`, and adds a stub `of
isGenericCall:` arm to every `case stmt.kind` dispatch in `runtime.nim`.
Each new arm appends a `SymexErrorInfo{kind: geUnresolvedGeneric}` to
`w.errors` and returns without panicking — no silent fallback, no panic.
The `itInstantiated` IR type kind is also introduced here (wraps a
monomorphized-body `ProcSig` under its instantiation key). The
canonicalize round-trip for `isGenericCall` is implemented and tested.
No parser or real walker logic beyond the stubs ships in this cycle.

**Instantiation-key schema.** Keys in `ctx.procs` follow two forms that
coexist in the same `Table[string, ProcSig]`:
- Generic procs: `name#typeargs` (e.g. `"foo#int"`, `"foo#int;string"`)
- Non-generic procs: `name` (e.g. `"bar"`)

`name` is derived from `symBodyHash(calleeSym)` (Nim's `std/macros`
`symBodyHash`) so that same-name procs across modules do not collide. If
`symBodyHash` returns 0 or is unavailable for a given callee, fall back to
`getImpl.lineInfo.filename & ":" & calleeSym.strVal`. This encodes the
defining module's file path plus the proc name and is unambiguous across
modules. Bare `calleeSym.strVal` alone is not permitted (module-collision
risk). `repr(calleeSym.getImpl).hash` is explicitly **not** used as a
fallback — `repr` is structurally ambiguous across modules (two procs with
identical bodies in different modules produce identical `repr` strings)
and does not survive across recompilations (Feas-H5). Per-walker state
derived from instantiation keys lives on `WalkerStatics`; no `EffectCtx`
reference is made in this cycle.

**RED test:** `tests/tsymex_phase15_g1a_ir_roundtrip.nim`, test name
`"isGenericCall IR node survives canonicalize round-trip"`. Specifies:
construct an `isGenericCall` node directly, canonicalize it, parse it
back, and assert structural equality. The walker stubs must compile (all
`case stmt.kind` arms exhaustive) and return a classified
`geUnresolvedGeneric` error, not panic.

**Additional RED test (Feas-H5 — module-collision avoidance):** A second
test in the same file, `"two modules each defining proc id[T](x:T):T=x
produce distinct cache keys"`. Specifies: simulate the `lineInfo` fallback
path by constructing two `isGenericCall` nodes whose `gcCallee` strings
are derived from different hypothetical `lineInfo.filename` values but
whose proc names are identical (`"id"`). Assert that the two keys are
distinct strings and that a `ParseCtx` seeded with both produces two
separate `ProcSig` entries under their respective keys.

**GREEN:**
- `src/proptest/smt/types.nim`: add `isGenericCall` to `IRStmtKind`
  with fields `gcCallee: string`, `gcTypeArgs: seq[string]`
  (canonical type-tuple string), `gcRetName: string`, `gcArgs:
  seq[IRExpr]`, `gcRetTy: IRType`; add `mkGenericCall` constructor.
  Add `itInstantiated` to `IRTypeKind`. Add `geUnresolvedGeneric` and
  `geInstantiationCapped` to `SymexErrorKind`.
- `src/proptest/smt/canonicalize.nim`: add `of isGenericCall:` encoding
  and round-trip.
- `src/proptest/smt/runtime.nim`: add `of isGenericCall:` stub to every
  `case stmt.kind` dispatch in `walk` — each stub appends
  `SymexErrorInfo{kind: geUnresolvedGeneric}` to `w.errors` and
  returns without panicking. (Real dispatch added in G1c.)

**DoD:**
- [ ] RED test passes on both backends (smtlib2 and z3 native)
- [ ] Module-collision avoidance test passes: two modules each defining
  `proc id[T](x: T): T = x` produce TWO distinct cache entries under
  the `lineInfo`-fallback key path (Feas-H5)
- [ ] `nimble test` is green across all existing test files
- [ ] All `case stmt.kind` dispatch arms exhaustive (Nim exhaustiveness
  check passes — no `{.warning[Exhaustive]: off.}` suppressions added)
- [ ] ADR-0008 authored via G0-ADR; this cycle references it but does
  not re-author it

---

### G1b — Parser: `gatherTypeSubst`, `parseCalleeImpl`, `emitGenericCall`

**What it does:** Implements the parser-side generic machinery in
`dsl_parser.nim`. Extends `ensureProcRegistered` (the generic-aware
overload, currently at line ~1043) to detect `hasGenerics and callSite
!= nil`, call `gatherTypeSubst`, call `parseCalleeImpl` with the
substitution map, and register the result under the instantiation key
`symBodyHash(callee) & "#" & typeArgsTuple`. Adds `emitGenericCall` in
`emitStmt`'s `of isGenericCall:` branch (parallel to existing `isCall`
emission) and arranges for `parseStmt`'s `nnkCall`/`nnkCommand` branch
to emit `isGenericCall` nodes at typed call sites carrying generic
`typeArgs`. After this cycle the parser produces `isGenericCall` nodes;
the G1a stubs still fire (returning `geUnresolvedGeneric`), so no
end-to-end SAT yet.

**RED test:** `tests/tsymex_phase15_g1b_parser.nim`, test name
`"parser produces isGenericCall from generic-call SUT body"`. Specifies:
a SUT body containing a call to `proc foo[T](x: T): T = x` is parsed;
the resulting IR contains exactly one `isGenericCall` node with
`gcCallee` set to the `foo` key and `gcTypeArgs = @["int"]`; `ctx.procs`
contains a registered `ProcSig` under the `"foo#int"` key.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim`: extend `ensureProcRegistered` to
  emit `isGenericCall` from `parseStmt`'s `nnkCall`/`nnkCommand` branch
  when `hasGenerics`. Implement `emitGenericCall` in `emitStmt`'s
  `of isGenericCall:` branch parallel to existing `isCall` emission.
  `monomorphize` and `gatherTypeSubst` are already present (lines ~999
  and ~1013) and require no structural changes.

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` green
- [ ] Parser emits `geUnresolvedGeneric` (not panic) when a generic call
  site's callee `getImpl` is unavailable (Invariant 3)

---

### G1c — Walker dispatch + instantiation cache + cap

**What it does:** Replaces the G1a stubs with real walker logic. The
`of isGenericCall:` dispatch in `runtime.nim` looks up the instantiation
key in `ctx.procs`, finds the registered `ProcSig` from G1b, and
delegates to the existing `isCall` walk path with the monomorphized body.
This cycle also folds the cache and cap machinery (formerly separate
cycles G2 and G9):

- **Instantiation cache** — keyed by
  `(symBodyHash(calleeSym), instTypeTuple)`, stored in
  `ParseCtx.instCache: Table[string, ProcSig]`. Two call sites
  instantiating the same generic proc at the same type tuple share one
  `ProcSig`; body parsed exactly once. A
  `when defined(proptest_testing): cacheHitsFor(ctx, key): int` accessor
  is exposed for test assertions.
- **Instantiation cap** — `maxInstantiationsPerProc = 64` (from
  `SymexSettings`; `0` means unlimited, matching `maxFrontierSize = 0`
  convention). This setting is defined in Z3 (already shipped as part
  of the `SymexSettings` surface); G1c wires the cap check into
  `ensureProcRegistered` without re-adding the field. When exceeded,
  `ensureProcRegistered` registers a sentinel `ProcSig` with
  `isCapped = true`. The walker arm for a capped `ProcSig` appends
  `SymexErrorInfo{kind: geInstantiationCapped, procSym, observedCount}`
  to `w.errors` and sets `w.sawUnknown = true`.
- **Heap threading contract** — the `of isGenericCall:` dispatch must
  pass `path.heaps` into the callee frame and merge the callee's exit
  `heaps` back out (matching the C2b / R1b inter-proc heap-threading
  contract from Clusters C and R).

**RED test:** `tests/tsymex_phase15_g1c_dispatch.nim`, test name
`"end-to-end SUT calling foo[T](x: T): T at T=int returns sxSat for
foo(3) == 3"`. Specifies: `symexFind` on a SUT body containing
`assert foo(3) == 3` (where `foo` is a generic identity proc) returns
`sxSat` with a witness containing `x = 3`. Both smtlib2 and z3 native
backends.

**GREEN:**
- `src/proptest/smt/runtime.nim`: replace `of isGenericCall:` stub with
  real dispatch: look up `instKey` in `ctx.procs`; if `isCapped`, report
  `geInstantiationCapped`; else delegate to the `isCall` walk path.
- `src/proptest/smt/dsl_parser.nim`: add `instCache: Table[string,
  ProcSig]` and `instCountPerProc: Table[string, int]` to `ParseCtx`;
  add cap check before `parseCalleeImpl`; expose `cacheHitsFor` under
  `when defined(proptest_testing)`.
- `src/proptest/smt/types.nim`: `maxInstantiationsPerProc*: int = 64`
  is already present in `SymexSettings` (shipped in Z3); add
  `isCapped: bool` to `ProcSig` only.
- `src/proptest/smt/canonicalize.nim`: `maxInstantiationsPerProc`
  participates in the cache key (analogous to `maxFrontierSize`).

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` green
- [ ] Cache hit confirmed via `cacheHitsFor` accessor (two call sites
  sharing an instantiation record one hit)
- [ ] `maxInstantiationsPerProc = 0` is unlimited (assertion in RED test)
- [ ] `withSymexSettings(base = defaultSettings()) do (s): s.maxInstantiationsPerProc = 2`
  wires through correctly: a SUT with 3+ distinct instantiations of the
  same generic proc hits the cap and returns `sxUnknown` with
  `geInstantiationCapped` (confirmed by test)
- [ ] `geInstantiationCapped` error kind documented in `determinism.md`
  as the fourth UNKNOWN sub-case (alongside Z3-rlimit-exhausted,
  walker-loop-unwind-exhausted, frontier-pruned)
- [ ] Comment in `ParseCtx` distinguishes parse-time instantiation cache
  from the verdict cache (Cluster C / db layer)

---

### G3 — Type-substitution path through `classifyType`

**What it does:** When a generic parameter `T` is bound to a concrete
type in the monomorphization substitution table, `classifyType` on that
bound type must resolve correctly through `gatherTypeSubst`'s output.
This cycle audits the end-to-end path from `gatherTypeSubst` →
`monomorphize` → `classifyType` for all type families the substitution
may produce, and adds a `float`-instantiation test that exercises the
Cluster F float bridge (G3 depends on Cluster F being complete). Where
`classifyType` previously produced a partial classification for a
substitution-derived node shape, this cycle tightens or errors cleanly.

**`auto` return type safety.** A DoD item verifies that a SUT with
`auto` return type instantiated in the called generic produces a correct
`IRType` classification for the return value. Nim's semchecker resolves
`auto` before `getImpl` is called, so `ProcSig.retTy` must not contain
`nnkEmpty` after monomorphization. The guard: if the resolved return-type
node after substitution is `nnkEmpty`, emit
`error("symex G3: type-substitution produced nnkEmpty retTy ...")` rather
than returning a default or silently using `itVoid`.

**`sink T` / `lent T` stripping.** The `nnkSinkTy`/`nnkLentTy` strip in
`classifyType` is already present in Z3 (shipped as part of the
`dsl_typebridge.nim` completeness pass). This cycle references it: a
generic `proc foo[T](x: sink T)` is lifted to `proc foo[T](x: T)` for
symex purposes (the ownership annotation is stripped before classification;
symex models by-value semantics). A test in G3 exercises this path: a SUT
calling `proc foo[T](x: sink T): T = x` at `T = int` must classify the
parameter as `itInt` (not fail with an unhandled `nnkSinkTy` node)
(Breadth-H5).

**G+C composition note.** Proc-type substitution `T = int` in
`proc(x: T): T` to `proc(x: int): int` is correctly classified by
`classifyProcTy` after `monomorphize`. This is asserted by C6's
`applyTwice` test (composition cycle); G3 does not need a separate test
for this path but the dependency is noted here for cross-cluster tracing.

**RED test:** `tests/tsymex_phase15_g3_type_subst.nim`, test name
`"identity proc instantiated at float64 classifies correctly"`. Specifies:
`proc id[T](x: T): T = x` instantiated at `T = float64` has its param
and return type classified as the `itFloat` IR type introduced by Cluster
F; the walker symex's the float-specialized body without falling back to
`sxUnknown`; a target label inside `id` is reachable and produces a
float witness.

**GREEN:**
- `src/proptest/smt/dsl_typebridge.nim`: audit `classifyType` for the
  `nnkSym` case after monomorphization — specifically verify that a
  float sym, string sym, bool sym, and enum sym produced by
  substitution all resolve to their correct `IRType`. Add guards: if
  the resolved node after substitution is `nnkEmpty`, emit a compile
  error naming the G3 cycle rather than returning a default. The
  `nnkSinkTy`/`nnkLentTy` strip is already in Z3 (no new edit needed);
  confirm it is exercised by the sink-param test in this cycle.
- `src/proptest/smt/dsl_parser.nim`: no structural changes; audit only.
- Test exercises the round-trip: `gatherTypeSubst` builds the
  substitution from the typed call-site AST; `monomorphize` replaces
  the formal `T` node; `classifyType` is called on the replaced node.

**DoD:**
- [ ] RED test passes on both backends (depends on Cluster F being
  merged — G3 is sequenced after F)
- [ ] `nimble test` green
- [ ] `classifyType` does not return a silent default for any type family
  reachable through monomorphization (Invariant 3)
- [ ] `nnkEmpty` does not appear as `ProcSig.retTy` after monomorphization
  for a proc with `auto` return type (Nim semchecker resolves `auto`
  before `getImpl`)
- [ ] `sink T` param: generic `proc foo[T](x: sink T)` lifts to
  `proc foo[T](x: T)` for symex; `nnkSinkTy` strip (already in Z3)
  is exercised; parameter classifies as `itInt` (Breadth-H5)
- [ ] Comment added at the `gatherTypeSubst` call site documenting the
  Cluster F dependency

---

### G4 — `distinct T` as a fresh uninterpreted Z3 sort

**What it does:** Maps `type Foo = distinct Bar` to a fresh
uninterpreted Z3 sort in the IR and at the walker layer. The IR gains
`itDistinct` (a new `IRTypeKind`) carrying the distinct type name and its
base `IRType`. The walker allocates a new sort for each `itDistinct` seen
in a SUT, keyed by the type name, using
`mkUninterpretedSort(ty.distinctName)` from `sort.nim` (which calls
`Z3_mk_uninterpreted_sort` and returns `Z3Sort[stUninterpreted]`
directly — the phantom-typed `Z3UninterpretedVal[T]` API is not used
because `T` is runtime-known). The sort is cached in
**`WalkerStatics.distinctSorts: Table[string, Z3Sort[stUninterpreted]]`**
— per-walker, shared across all call frames. This placement ensures that
a distinct type appearing in both caller and callee maps to the same Z3
sort; per-frame storage would produce inconsistent sorts (ADR-0008 D4,
Depth-MED-D4, M10). The `WalkCtx` itself holds a reference to
`WalkerStatics` via `WalkCtx.statics`.

Two uninterpreted functions are declared per distinct type:
- `inject_T: Base → Distinct` — maps base-type values into the distinct
  sort
- `eject_T: Distinct → Base` — maps back (the inverse)

**Bijectivity axioms are asserted only for base types in the decidable
fragment `{int, BV, bool}`** (Depth-H6, Depth-MED-D4, Des-MED-D5).
For base types in `{FP, String}`, bijectivity is skipped and a
`geDistinctBijectivitySkipped` error (severity: `sevHint`) is emitted.
Rationale: universally-quantified axioms over FP or string sorts push Z3
into the incomplete quantified fragment, producing `UNKNOWN` rather than
`SAT`/`UNSAT` on otherwise decidable queries. Users receive the hint and
can manually verify that the injection model is adequate for their use
case.

**Axioms are asserted at most once per `(sortName, runSymex)`** (Feas-MED-2,
M15). The cache key is the sort name (equal to the distinct type name).
A SUT using `Meters` in both caller and callee produces exactly ONE entry
in `WalkerStatics.distinctSorts`.

**Nested distinct chains** (Breadth-H6): `type KiloMeters = distinct Meters`
causes recursive sort allocation — one sort for `Meters`, one for
`KiloMeters`, with `eject_KiloMeters` producing a `Meters`-typed value,
and `eject_Meters` producing the float base value. Bijectivity is asserted
at each level (where the base is in the decidable fragment).

**`emitTyAndReader` for `itDistinct`** (Breadth-CRIT-1, C7): The
`emitTyAndReader` / `primTyAndReader` dispatch in `src/proptest/symex.nim`
gains an `itDistinct` case that emits an ejection-then-base-reader chain
for `distinct`-typed SUT parameters. Without this, distinct-typed SUT
params produce a silent empty reader, and witnesses cannot be rendered.

No implicit coercion is ever emitted. Operations on the distinct type
require explicit lift through injection. Witness extraction for
`distinct`-typed parameters goes through ejection: `eject_T(witness)`
is called, then the base-type extractor is applied to the result.
Operations that attempt implicit conversion produce a classified
`geDistinctBarrier` error.

**RED test:** `tests/tsymex_phase15_g4_distinct_sort.nim`, test name
`"distinct type becomes fresh Z3 sort distinct from base type"`. Specifies:
a SUT with `type Meters = distinct float64; proc foo(m: Meters)` causes
the walker to allocate a `Z3Sort[stUninterpreted]` named `"Meters"` that
is not the float64 Z3 sort; Z3 cannot prove `meters_val == float_val` for
symbolically allocated values of each type; a target label in `foo`
reachable only through a `Meters`-typed path is found.

**Additional RED tests:**
- `"distinct sort cache lives on WalkerStatics, asserted at most once"`:
  a SUT using `Meters` in caller AND callee; after `symexFind`, the
  test-only accessor `walkerStatics.distinctSorts.len` equals 1 (exactly
  one entry). Confirms `WalkerStatics` placement and once-per-walk
  axiom assertion (Depth-MED-D4, Feas-MED-2).
- `"nested distinct chain KiloMeters = distinct Meters"` (Breadth-H6):
  a SUT with `type Meters = distinct float64; type KiloMeters = distinct
  Meters`; two sorts allocated; ejection recurses through the chain;
  bijectivity asserted at the `Meters` level (base = `float64`, skipped
  with hint) and at `KiloMeters` level (base = `Meters`-sort, uninterpreted
  — also skipped with hint). Witness for `KiloMeters`-typed param renders
  through the chain.
- `"distinct-typed SUT param produces witness through emitTyAndReader"`:
  `proc f(m: Meters): bool = m > Meters(0)` SUT; symexFind returns
  witness `m: Meters = 3.14` (rendered through the ejection chain in
  `emitTyAndReader`). Confirms Breadth-CRIT-1 / C7 fix.

**GREEN:**
- `src/proptest/smt/types.nim`: add `itDistinct` to `IRTypeKind` with
  fields `distinctName: string`, `distinctBase: IRType`; add
  `tDistinct(name: string, base: IRType): IRType` constructor. Add
  `geDistinctBijectivitySkipped` to `SymexErrorKind` (severity: `sevHint`).
- `src/proptest/smt/dsl_typebridge.nim`: in `classifyType`'s `nnkSym`
  branch, before the enum check, add detection of `nnkDistinctTy` in
  `impl[2]`; when found, recurse on the base type and return
  `unranged(tDistinct(s, baseCls.ty))`.
- `src/proptest/smt/dsl_parser.nim`: add `of itDistinct:` to
  `emitIRType` emitting `newCall(bindSym"tDistinct", ...)`.
- `src/proptest/smt/runtime.nim`: add `of svDistinct:` to `SVKind`;
  add `svDistinct` case to `SymVal` with fields
  `distSort: Z3Sort[stUninterpreted]`, `distName: string`,
  `distBase: IRType`; in `allocateSym`, `of itDistinct:` looks up
  `w.statics.distinctSorts[ty.distinctName]`; if missing, allocates via
  `mkUninterpretedSort(ty.distinctName)`, stores in
  `WalkerStatics.distinctSorts`, declares `inject_T` and `eject_T`
  uninterpreted functions, and asserts bijectivity axioms only when
  base ∈ `{int, BV, bool}` (emitting `geDistinctBijectivitySkipped`
  hint otherwise). For nested chains, recurse: if `distBase` is itself
  `itDistinct`, allocate the inner sort first.
- `src/proptest/smt/canonicalize.nim`: add `of itDistinct:` encoding
  `"distinct(" & ty.distinctName & ";" & canonicalize(ty.distinctBase)
  & ")"`.
- `src/proptest/symex.nim`: add `itDistinct` case to `emitTyAndReader` /
  `primTyAndReader` producing an ejection-then-base-reader chain.
  Without this case distinct-typed SUT params produce a silent empty
  reader (Breadth-CRIT-1, C7).

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` green
- [ ] Z3 query in the RED test asserts that `Meters` sort != `float64`
  sort (checked via `Z3Sort` identity, not just name)
- [ ] `extractFromSymVal` handles `svDistinct` — extracts via `eject_T`
  then the base-type extractor (or raises `geDistinctBarrier` if
  ejection is unavailable for the target extraction type)
- [ ] Bijectivity axioms asserted only for base ∈ `{int, BV, bool}`;
  `geDistinctBijectivitySkipped` hint emitted for FP/String base;
  confirmed that FP-base distinct sort does NOT produce `UNKNOWN`
- [ ] Distinct sort cache on `WalkerStatics.distinctSorts`: exactly ONE
  entry for `Meters` when it appears in both caller and callee
  (test-only accessor; Feas-MED-2, M10)
- [ ] Nested distinct chain `KiloMeters = distinct Meters`: two sorts
  allocated; ejection recurses; bijectivity handled at each level
  (Breadth-H6)
- [ ] `emitTyAndReader` itDistinct case: `proc f(m: Meters): bool` SUT
  has witness `m: Meters = 3.14` rendered through ejection chain
  (Breadth-CRIT-1, C7)

---

### G5 — `distinct` borrow semantics

**What it does:** When a `distinct` type is declared with `{.borrow.}`
procs, the walker recognizes the pragma and threads operations on the
distinct type through the base type's operator, with appropriate
injection/ejection through the distinct sort's functions from G4. The
canonical borrow form is `proc \`+\`(a, b: Meters): Meters {.borrow.}`;
the walker emits a Z3 expression `inject_T(eject_T(a) + eject_T(b))`
where `inject_T` and `eject_T` are the sort's functions (bijectivity
axioms from G4 make this sound). Borrow procs for all arithmetic and
comparison operators are supported.

**RED test:** `tests/tsymex_phase15_g5_distinct_borrow.nim`, test name
`"distinct borrow proc threads arithmetic through base type"`. Specifies:
a SUT with `type Meters = distinct float64` and a borrowed `+` proc
allows a target gated on `m1 + m2 > Meters(10.0)` to be reached; the
witness gives `m1` and `m2` as `Meters`-typed values whose base-type
sum exceeds 10.0; the walker does not require explicit lifts at the call
site.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim`: in `ensureProcRegistered`, detect
  `nnkPragma` child of the `nnkProcDef` containing `ident"borrow"`;
  when found, record the proc as a borrow shim for its distinct-typed
  params; emit a specialized `isCall` that routes through the borrow
  path rather than a body parse.
- `src/proptest/smt/runtime.nim`: add `isDistinctBorrowCall` handling
  in `walk`'s `of isCall:` branch: when the callee is registered as
  a borrow shim, look up the base-type operation by name, apply it
  to ejected args, and inject the result back into the distinct sort.
- `src/proptest/smt/dsl_typebridge.nim`: no structural changes; the
  `itDistinct` IR type from G4 carries the base type needed for
  injection/ejection.

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` green
- [ ] Borrow procs for non-arithmetic operations (e.g., comparison) also
  produce correct Z3 expressions (add a second assertion in the RED
  test for `m1 < m2`)
- [ ] A non-borrowed proc on a distinct type that is called without an
  explicit body raises `geDistinctBarrier`, not a silent fallback
  (Invariant 3)

---

### G6 — Concept constraints: trust boundary and compound constraints

**What it does:** When a generic proc is constrained by a type class
(`proc foo[T: SomeNumber](x: T)`), Nim's semchecker already enforces the
constraint at the call site — a non-conforming `T` is a compile error
that never reaches proptest's macro. This cycle specifies and tests the
precise trust boundary:

- **stdlib concepts** (`SomeNumber`, `SomeInteger`, `SomeFloat`, etc.):
  validate against a compile-time membership table in the walker. If a
  type does not satisfy the constraint, emit `geConceptViolation`.
- **User-defined concepts**: trust the Nim semchecker. The semchecker
  verified the constraint at the call site before proptest's macro saw
  the typed AST; proptest does not re-validate. `geConceptViolation`
  fires only for IR nodes constructed maliciously (e.g., test-only
  invariant violations) — not for real Nim source.
- **Compound concept constraints** (`T: A and B`): the semchecker
  resolves these to a single elaborated type at the call site; G6 does
  not need explicit handling. A DoD test confirms a
  compound-constrained generic call works without special-casing.

The cycle also tests the positive case: concept-constrained generic
procs instantiated at conforming types work correctly end-to-end.

**RED test:** `tests/tsymex_phase15_g6_concept_constraint.nim`, test
name `"concept-constrained generic instantiated at conforming type
reaches target"`. Specifies: `proc foo[T: SomeNumber](x: T)` instantiated
at `T = int` (a conforming type) reaches a target label inside `foo`;
the walker produces a correct int witness. A second test in the same
file, `"malformed generic call node with non-conforming type is
classified"`, constructs an IR `isGenericCall` node with a non-conforming
type string in `gcTypeArgs` and asserts the walker raises
`SymexErrorInfo{kind: geConceptViolation}` rather than silently
proceeding (Invariant 3). A third test confirms a compound-constrained
generic (`T: SomeNumber and Comparable`) works without special-casing.

**GREEN:**
- `src/proptest/smt/runtime.nim`: in `of isGenericCall:` dispatch, add
  a concept-conformance guard for stdlib concepts only: look up the
  callee's concept-constraint metadata (stored as `seq[string]`
  type-class names in `ProcSig.conceptConstraints`) and verify each
  `gcTypeArgs[i]` against a static stdlib membership table. For
  non-stdlib (user-defined) concepts, skip validation — trust the
  semchecker. Document the trust boundary in a comment at this site.
- `src/proptest/smt/types.nim`: add `conceptConstraints: seq[string]`
  to `ProcSig`; add `geConceptViolation` to `SymexErrorKind`.
- `src/proptest/smt/dsl_parser.nim`: extend `parseCalleeImpl` to parse
  `nnkGenericParams` children for `nnkIdentDefs` whose type node is a
  constraint sym (not `nnkEmpty`), and populate `conceptConstraints`.

**DoD:**
- [ ] RED test passes on both backends (positive, negative, and compound
  cases)
- [ ] `nimble test` green
- [ ] `geConceptViolation` error kind added to `SymexErrorKind` enum in
  `src/proptest/smt/types.nim`
- [ ] Trust boundary comment at the `of isGenericCall:` dispatch site
  distinguishes stdlib vs user-defined concept validation
- [ ] Compound-constraint test confirms no special-casing needed (the
  semchecker already resolved `T: A and B` to a concrete type)

---

### G7 — `static[T]` parameters as instantiation-key components

**What it does:** `proc foo[N: static[int]](x: array[N, int])` —
`N` is a compile-time constant, not a runtime value. The walker treats
`static[T]` parameters as part of the instantiation key rather than as
symbolic values: two calls with different `static N` get separate cache
entries with separate parsed bodies. The body of each instantiation has
`N` substituted to its literal value at parse time (by `monomorphize`,
which already handles literal `nnkIntLit` replacements). This cycle
verifies that the instantiation-key derivation in `gatherTypeSubst`
correctly captures static-param values alongside type-param values.

The instantiation key includes the static value, so `foo[N: static[int]]`
instantiated with `N = 3` and `N = 5` get separate cache entries with
key suffixes `";static=3"` and `";static=5"` respectively.

**RED test:** `tests/tsymex_phase15_g7_static_param.nim`, test name
`"two static[int] instantiations get separate cache entries"`. Specifies:
a SUT calling `foo[3](arr3)` and `foo[5](arr5)` registers two distinct
`ProcSig` entries in `ctx.procs` (keyed `"foo#int;static=3"` and
`"foo#int;static=5"`); each body has `N` bound to its respective literal
(assertable via the walker symex'ing a target gated on `x[N-1] > 0` —
the literal index value differs between instantiations); the
`cacheHitsFor` accessor records zero hits for both (both are fresh
instantiations).

**GREEN:**
- `src/proptest/smt/dsl_parser.nim`: extend `gatherTypeSubst` to
  detect `nnkStaticTy` in the generic param's constraint position and
  extract the call-site literal value via `callSite[argIx].intVal` or
  `.floatVal`; include the literal in the key string as
  `";static=" & $val`; include the substitution as `subst[paramName]
  = newLit(val)` so `monomorphize` replaces uses of the static param
  with the concrete literal.
- `src/proptest/smt/types.nim`: no changes needed (the key is a
  string; the cache is a `Table[string, ProcSig]`).

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` green
- [ ] Separate cache entries confirmed via `cacheHitsFor` accessor (zero
  hits for both fresh instantiations)
- [ ] Static param with non-int type (e.g. `static[bool]`) also produces
  a correct key and substitution (add a second assertion to the RED
  test)
- [ ] Static value included in instantiation key (confirmed by the key
  string containing `";static=3"` and `";static=5"` respectively)

---

### G8 — Multi-parameter generics

**What it does:** `proc foo[T, U](a: T, b: U)` with a mixed
instantiation (e.g. `T = int, U = string`). This cycle verifies that
`gatherTypeSubst` and `monomorphize` handle two independent type params
correctly: the substitution table accumulates both bindings, the
instantiation key encodes both in a deterministic order, and the parsed
body resolves both params to their concrete types. The walker symex's
the body under the mixed types without conflating T and U.

**Instantiation-key ordering (Depth-LOW-D3, L6).** The type-arg tuple in
the key is derived from `gatherTypeSubst`'s output — a
`Table[string, NimNode]` mapping formal param name to bound type — then
**sorted by formal param name** before joining with `";"`. Two call sites
with the same bound types but different syntactic argument order (e.g.,
`foo[T=int, U=string]` and `foo[U=string, T=int]`) produce the same
canonical key and share the same `ProcSig` cache entry.

**RED test:** `tests/tsymex_phase15_g8_multi_param.nim`, test name
`"multi-param generic instantiated at int U=string reaches target"`.
Specifies: a SUT with `proc foo[T, U](a: T, b: U) = if a > 0 and b == "ok": symexTarget("hit")` instantiated at `T = int, U = string` (Cluster S
`itString` required) — the walker finds a witness `(a=1, b="ok")` that
reaches the target; the two type params are independently resolved in
the body.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim`: `gatherTypeSubst` already
  iterates formal params and collects one entry per generic-named param;
  multi-param generics work if each param's formal type node is an
  independent `nnkIdent` in `genericNames`. The function returns a
  `Table[string, NimNode]`; the caller (key-builder in
  `ensureProcRegistered`) sorts the table's keys before joining. Audit
  and add test. If there are interaction bugs (e.g., both params
  resolving to the first arg's type due to an off-by-one in `argIx`),
  fix in `gatherTypeSubst`'s loop.
- No structural changes beyond any bug fixes surfaced by the RED test.

**DoD:**
- [ ] RED test passes on both backends (depends on Cluster S for the
  string half; L3 Cluster S dependency documented at call site)
- [ ] `nimble test` green
- [ ] A second RED assertion: instantiation at `T = bool, U = int` also
  works (no accidental param order dependency)
- [ ] Key encoding is deterministic (sorted param names, not insertion
  order) — add an assertion that `"foo#bool;int"` and `"foo#int;bool"`
  produce different keys even if the proc body happens to be the same
  shape
- [ ] Swapped-argument-order cache hit (Depth-LOW-D3, L6): `foo[T=int,
  U=string]` and `foo[U=string, T=int]` produce the same canonical key
  and share one `ProcSig` entry; confirmed via `cacheHitsFor` accessor
  (records one hit for the second call)

---

### G10 — Regression smoke against Cluster E + walker version bump

**What it does:** Re-runs all Cluster E test files under the G-patched
walker to catch state-threading bugs introduced by the generic machinery.
The G-cycle changes touch `ParseCtx` (new fields), `ProcSig` (new
fields), `runtime.nim`'s `walk` dispatch (new `isGenericCall` branch),
and `types.nim` (new IR kinds and error kinds). Any of these can silently
break Cluster E's exception-path tests if a new dispatch case is
incomplete or a `ParseCtx` field is not correctly initialized across
recursive parse calls. This cycle adds no new features; it confirms
backward compatibility and closes the cluster.

The **walker version is atomically bumped `"7"-->"8"`** as the last step
of this cycle, after all regression tests pass. This is consistent with
the per-cluster bump policy (v2 revision history): G10 is the cluster's
closing cycle and no mid-cluster bump is permitted.

**RED test:** `tests/tsymex_phase15_g10_regression_e.nim`, test name
`"Cluster E tests pass under Cluster G walker"`. Specifies: every
`symexFind` and `symexForAll` call from the Cluster E test suite
(`tsymex_phase15_e*`) produces the same verdict (SAT/UNSAT/UNKNOWN) and
the same witness shape as it did before G1a landed. The regression test
imports the Cluster E SUT procs directly and re-asserts their expected
outcomes under the current walker version.

**GREEN:**
- No new production source files modified. If any E-cluster test
  regresses, the regression smoke RED test fails first — the fix goes
  in whichever G cycle introduced the regression, and G10 is re-run.
- `tests/tsymex_phase15_g10_regression_e.nim`: imports E-cluster SUTs
  and asserts their expected outcomes. Uses the same `symexFind` /
  `symexForAll` entry points as the original E tests.
- `src/proptest/smt/canonicalize.nim`: bump walker version constant
  `"7"` to `"8"` as the final step, after all regressions pass. The
  single source-of-truth for the walker version is `canonicalize.nim`,
  not `runtime.nim` (M12 / Depth-6). DoD: `canonicalize.walkerVersion
  == "8"` asserted by the closing test.

**DoD:**
- [ ] RED test passes on both backends
- [ ] `nimble test` is green across all test files (full suite, not just
  G-cluster)
- [ ] Walker version bumped to `"8"` in `canonicalize.nim` as the final
  commit of this cycle; `canonicalize.walkerVersion == "8"` asserted
  (M12; per Cross-cluster Invariant 1: one bump per cluster, at the
  closing cycle)
- [ ] `withSymexSettings(base = defaultSettings()) do (s): s.maxInstantiationsPerProc = 2`
  is confirmed to wire through from G1c: a SUT exercising 3 distinct
  instantiations of the same proc under this settings override returns
  `sxUnknown` with `geInstantiationCapped` (regression confirmation)
- [ ] No `# TODO: defer until consumer demand` comments introduced in
  any G-cycle source file (Invariant 5 / `complete-lib-not-consumer`)
- [ ] `docs/symex/determinism.md` updated: `geInstantiationCapped`
  UNKNOWN sub-case added; `distinct` sort + inject/eject/bijectivity
  semantics noted in the supported-fragment table; `ge` error prefix
  documented; ADR-0008 reference added
<!-- CLUSTER_C -->
## Cluster C — closures and procs-as-values

Cluster C brings first-class procs and closures into the symex engine's
supported fragment. Before this cluster, any SUT containing a lambda
expression, a proc-as-value binding, or a call through a proc variable is
classified `isUnsupported` at parse time and produces a `{.warning.}` via
the B67 diagnostic. After this cluster, a well-formed closure — one whose
captured locals have symex-representable types — is fully analyzed.

**Out of scope for this cluster.**

| Topic | Reason / future home |
|-------|----------------------|
| Closure iterators (`iterator foo(): T {.closure.}`) | Phase 16; C1 emits `ceNotImplemented` with a detail string |
| `{.closure.}` vs `{.nimcall.}` calling-convention surfaces in symex | Cluster C assumes `{.closure.}` only; nimcall proc values are handled via the unit-env path in C3 |
| `func` purity / effect-tracking in symex | Phase 16; symex treats `func` identically to `proc` within this cluster |

**Cycle table.**

| Cycle | Topic | Key dependency |
|-------|-------|----------------|
| C0-ADR | Doc: `ADR-0009-closure-encoding.md` + `closures.md` skeleton (Breadth-LOW-L6) | None (doc-only) |
| C1 | IR + parser: `iekLambda`, `iekClosureCall`, `svClosure` stub | C0-ADR |
| C2a | Walker: closure construction (`iekLambda` → `svClosure` with env snapshot) | C1 |
| C2b | Walker: closure call dispatch (`iekClosureCall` descent + multi-return-path axiom + proc-valued params) | C2a |
| C3 | Top-level procs as values (module-scope `nnkSym` in expression position, unit-env encoding) | C2b |
| C4 | DSL HOFs: `filter`, `map`, `fold` over `seq[T]` (bounded inline + symbolic axiom paths) | C2b, Cluster G (instantiation cache) |
| C5 | Closure equality semantics (`bEq`/`bNe` on `svClosure`; nominal-for-site + structural-for-env) | C2a |
| C6 | Regression smoke against Cluster G; walker version bump `"8"→"9"` | C1–C5, all G cycles |

**ADR-0009 summary.** A closure is encoded as an ordered pair
`(funcSym, envRecord)`. `funcSym` is a Z3 uninterpreted function symbol
declared once per syntactic lambda site (keyed by
`(symBodyHash(lambdaBody), declOrderIndex)` — see "Lambda site keying"
below); its Z3 signature is `(envRecord_sort, params...) -> ret`, where
`envRecord_sort` is the Z3 datatype sort of the environment tuple.
`envRecord` is a Z3 tuple (concretely, a `svTuple` SymVal) of the captured
locals at construction time — the values the locals hold on the path where
the lambda expression is evaluated. Together, `(funcSym, envRecord)` is a
symbolic value of kind `svClosure` (new SymVal variant introduced in C1).
Top-level procs with no captures use a distinguished unit-sort envRecord so
they fit the same pair encoding without a special case in the walker.

**Lambda site keying (Des-H6).** The `lambdaSite` key is
`(symBodyHash(lambdaBody), declOrderIndex)` — NOT `"file:line:col"`.
`symBodyHash` hashes the semantic AST of the lambda body (same approach as
`symBodyHash` in G-cluster generic caching), making the key stable under
whitespace/comment/formatting changes. `declOrderIndex` is the
monotone integer index of the lambda declaration within its enclosing scope
(disambiguates two lambdas with identical bodies). This avoids the
formatting-sensitivity trap (Des-H6) where re-indenting source breaks
nominal equality. The `closureSite` field on `svClosure` carries the
`(siteHash: int64, declOrder: int)` pair; string-based `lambdaSite` keys
used in v1 are removed entirely.

**Monomorphization timing (Depth-H4).** `iekLambda` nodes are emitted
**after monomorphization** — that is, the parser emits `iekLambda` only
when the containing generic proc has been instantiated at concrete types.
Consequently, `lambdaParams` always carry concrete `IRType` values (never
type-variable placeholders). The same lambda site instantiated at `T=int`
and `T=string` produces two distinct `iekLambda` nodes with different
`lambdaParams`, different `paramsSortTupleId`s in `WalkerStatics.closureSyms`,
and therefore distinct `funcSym` entries in Z3.

**`Z3_mk_app` application path (Feas-H2).** Closure application cannot use
the phantom-typed `Z3FuncDecl[ArgsTup, Ret]` wrapper because type
parameters are compile-time and the domain sorts are known only at walk
time. The application path goes through raw
`Z3_mk_app(ctx.raw, fd.raw, nArgs, argsPtr)` via `ffi.nim`. A helper
`sortOfTuple(sv: SymVal): RawZ3Sort` derives the domain sort from the
`svTuple` components at walk time. The result is a `Z3AnyAst` cast to the
appropriate typed wrapper via `wrap[T]` based on the known return `IRType`.
C1 includes a proof-of-concept fixture validating this path before C2b
wires it into the full closure-call descent.

**Why uninterpreted functions.** The body of a lambda may be arbitrarily
complex and can itself contain calls, branches, or inner closures. Rather
than inlining the body symbolically at the declaration site (which would
require the walker to descend without a concrete call target, and would
duplicate the body into every path that constructs the closure), the walker
treats `funcSym` as a pure first-order name. The solver reasons over
`funcSym` via the axioms the walker asserts whenever it sees an
`iekClosureCall` node: it descends into the lambda's IR body with the
captured `envRecord` fields bound in a fresh environment, derives the
return value symbolically, and asserts
`implies(path.pc, funcSym(env, args) == returnVal)` as an additional path
constraint (under the path condition, not unconditionally — prevents
cross-path axiom accumulation from over-constraining the solver). This is
the standard lazy-body approach used by KLEE, CBMC, and angr for
procedure-valued data. The critical invariant is that descent happens
exactly once per `iekClosureCall` node per path, not at lambda-construction
time.

**DSL higher-order targets: C4's two-strategy approach.** For `filter`,
`map`, and `fold` over `seq[T]` in proptest's own DSL layer, C4 mixes two
complementary strategies. The inline vs axiom choice is controlled by
`inlinePolicy: InlinePolicy` in `SymexSettings` (default `ipHybrid`).
`InlinePolicy` is defined in the Z-cluster cross-cluster types section
(Des-H4 / H18); C4 consumes it and does NOT redefine it. When `inlinePolicy`
is `ipHybrid` or `ipAlwaysInline` and the sequence has a concrete Z3Int
length at most `settings.seqInlineThreshold` (default 8), the walker
unrolls the closure body once per element — concrete expansion avoids
universal quantification and keeps the resulting constraints in the
quantifier-free fragment that Z3's DPLL(T) core handles cheaply. When the
length is symbolic (or policy is `ipAlwaysAxiomatize`), the walker emits a
universally-quantified rewrite using Z3's `Z3Array.map` surface (via
`mapArray` in `z3/funcdecl.nim`) for `map`; for `fold`, the axiom path
uses raw `Z3_mk_app` via `ffi.nim` as above. For `filter`, the axiomatize
path is **deferred to Phase 16** (no Z3 `seqFilter` HOF in nim-z3 today;
quantifier construction non-trivial) — C4 emits `ceUnsupportedHof`
(`severity: sevError`) when `filter` would take the axiomatize branch.
Both `inlinePolicy` and `seqInlineThreshold` participate in the
canonicalize cache key. `seqInlineThreshold` is coupled to `ipHybrid`
(ignored when `inlinePolicy` is `ipAlwaysInline` or `ipAlwaysAxiomatize`);
the settings validator emits a warning when `seqInlineThreshold` is set
explicitly without `ipHybrid`.

This replaces the v1 `maxInlineSeqLen` sentinel scheme (`0 = always
axiomatize`, `maxInt = always inline`) which inverted the convention of
`maxFrontierSize` and `maxCallDepth` (where 0 = unlimited).

**Closure equality semantics (Open Question 6 closed).** Two `svClosure`
values are equal under **nominal-for-site + structural-for-env** semantics.
Two closures from different sites (different `(siteHash, declOrder)` pairs)
are always unequal regardless of their environments; two closures from the
same site are equal iff their `envRecord` tuples are Z3-equal. This matches
Nim runtime proc-value semantics (proc pointer identity for inter-site;
closure environment matters for same-site).

At `==` walk:
- If `(c1.siteHash, c1.declOrder) != (c2.siteHash, c2.declOrder)`
  (Nim-side integer-pair comparison) → emit `mkBool(false)`.
- If site pairs are equal → emit `c1.closureEnv == c2.closureEnv`
  (Z3 tuple equality via `svTupleEq`).

Open Question 6 is closed; the v1 "architect should challenge" framing is
removed.

---

### C0-ADR — doc: `ADR-0009-closure-encoding.md` + `closures.md` skeleton

**What it does:** Authors the two reference documents that all subsequent
Cluster C cycles build upon. This is a doc-only cycle — no RED/GREEN/test
file, no production source change. Both files must exist (even if skeletal)
before C1 begins, because C1's DoD references them.

**No RED test.** This cycle is checklist-DoD only.

**Documents produced:**

1. **`docs/symex/ADR-0009-closure-encoding.md`** — full-depth ADR matching
   the structure of ADR-0001..ADR-0004. Required sections:
   - **Context** — why first-class procs require a new SymVal variant; prior
     art (KLEE, CBMC, angr lazy-body approach).
   - **Decision** — closure encoded as `(funcSym, envRecord)` pair;
     `funcSym` is a Z3 uninterpreted function, `envRecord` is a `svTuple`.
   - **Lambda site keying** — `(symBodyHash(lambdaBody), declOrderIndex)`
     NOT `"file:line:col"`; rationale (Des-H6 formatting-sensitivity
     avoidance); `symBodyHash` hashes semantic AST.
   - **`Z3_mk_app` application path** — why phantom-typed wrapper cannot be
     used at walk time; `sortOfTuple` helper; `Z3AnyAst` + `wrap[T]` cast.
   - **Closure equality** — nominal-for-site (`(siteHash, declOrder)`
     integer-pair) + structural-for-env (`svTupleEq`); Nim runtime divergence
     note (Nim `==` on closures is undefined/Defect).
   - **Monomorphization timing** — `iekLambda` emitted post-monomorphization;
     concrete `lambdaParams` invariant; two-instantiation example.
   - **Rejected alternatives** — (a) `"file:line:col"` string key: rejected
     due to formatting sensitivity; (b) inlining body at declaration site:
     rejected due to path explosion and missing call-target at parse time;
     (c) phantom-typed `Z3FuncDecl` wrapper for apply: rejected because
     compile-time type params cannot be satisfied at walk time.
   - **Consequences** — `svClosure` added to `SVKind`; `closureSyms` on
     `WalkerStatics`; `closureInlineCount` on `CallFrameCtx`; `sortOfTuple`
     helper added to runtime.

2. **`docs/symex/closures.md`** — skeleton (Breadth-LOW-L6). C0-ADR
   authors the top-level structure; later cycles append subsections.
   Skeleton sections:
   - **Overview** — one-paragraph summary pointing to ADR-0009.
   - **Encoding** — stub (C2a fills in).
   - **Capture restrictions** — stub (C2a fills in; `var T` → `ceUnsupportedCapture`).
   - **Equality semantics** — stub (C5 fills in).
   - **Generics interaction** — stub (C6 fills in).
   - **Known divergences from Nim runtime** — stub (C5 fills in).

**DoD:**
- [ ] `docs/symex/ADR-0009-closure-encoding.md` exists with all 7 required
      sections present; depth matches ADR-0001..ADR-0004 (≥300 words,
      rationale for every decision point).
- [ ] `docs/symex/closures.md` exists with skeleton headings; no placeholder
      "TODO" stubs — instead, each stub section says "See cycle CX for
      implementation notes."
- [ ] Cross-references from other ADRs: ADR-0008 cross-references ADR-0009
      for the closure-equality and monomorphization decisions.

---

### C1 — IR + parser: `iekLambda` and `iekClosureCall`

**What it does:** Introduces the two new IR expression kinds needed to
represent closures: `iekLambda` (a value-producing lambda expression with
explicit capture list — prefix `iek` per the `IRExprKind` convention) and
`iekClosureCall` (a call through a proc-valued variable). The `IRExprKind`
prefix convention is: `iek` for value-producing expressions, `is` for
statements, `it` for types. Extends the parser to detect `nnkLambda` /
`nnkProcDef` expression nodes, enumerate free variables in the body to
build the capture list, and emit `iekLambda` **after monomorphization** so
`lambdaParams` always carry concrete types. Detects calls where the callee
is a proc-valued variable and emits `iekClosureCall`. Adds a `svClosure`
variant to `SymVal` as a stub (no walker descent yet — C2a wires that up).
All walker dispatch arms for `iekLambda` and `iekClosureCall` raise a
classified `SymexErrorInfo(kind: ceNotImplemented)` until C2a arrives,
honoring Invariant 3.

Also adds the **`sortOfTuple` helper** and a **PoC fixture** for raw
`Z3_mk_app` (Feas-H2), validating the application path before C2b
uses it in full closure-call descent.

**RED test:** `tests/tsymex_phase15_C1_ir.nim`, test name
`"C1: iekLambda + iekClosureCall parsed and round-trip through canonicalize"`.
Specifies: a hand-constructed `iekLambda` IR node with one capture and one
parameter round-trips through `canonicalize`; a matching `iekClosureCall`
produces a distinct canonical key from a plain `isCall` to the same
target. Both nodes compile through every case-dispatch stub site without
`{.warning.}` or compile error.

**GREEN:**
- `src/proptest/smt/types.nim` — add `iekLambda` and `iekClosureCall` to
  `IRExprKind` (value-producing expression variants); add `LambdaCapture`
  object and the two IR node shapes. Comment block at `IRExprKind`
  documents the `iek`/`is`/`it` prefix convention:
  ```nim
  ## IRExprKind prefix convention:
  ##   iek* — value-producing expressions (may appear in rvalue position)
  ##   is*  — statements (sequenced; may not produce a value)
  ##   it*  — type-level IR nodes
  of iekLambda:
    lambdaSite*:     (siteHash: int64, declOrder: int)  ## body-hash + order index
    lambdaParams*:   seq[IRParam]   ## concrete types post-monomorphization
    lambdaBody*:     IRStmt
    lambdaCaptures*: seq[string]   ## names of captured locals (free vars)
    lambdaRetTy*:    IRType

  of iekClosureCall:              ## A-normalised like isCall
    ccCallee*:  string            ## name of the proc-valued variable
    ccArgs*:    seq[IRExpr]
  ```
- `src/proptest/smt/runtime.nim` — add `svClosure` to `SVKind`:
  ```nim
  svClosure ## Phase 15 Cluster C: (funcSym, envRecord) pair.
            ## funcSym is the (siteHash, declOrder)-keyed uninterpreted Z3 function.
            ## envRecord is a svTuple of captured locals at construction.
  ```
  Add stub arms in `allocateSym`, `walk`, `extractFromSymVal`. Add
  `sortOfTuple(sv: SymVal): RawZ3Sort` helper that derives a Z3 sort from
  the components of a `svTuple` at walk time (used by C2b application path).
- `src/proptest/smt/dsl_parser.nim` — extend `parseExpr` to detect
  `nnkLambda` / `nnkProcDef` in expression position; compute free
  variables via scope-stack diff; emit `iekLambda` (post-monomorphization,
  so `lambdaParams` carry concrete types from the instantiated `ProcSig`).
  Extend `parseCallExpr` to detect proc-valued callee variables (typebridge
  check: callee `getTypeInst` is `nnkProcTy`); emit `iekClosureCall`
  (A-normalised).
- `src/proptest/smt/canonicalize.nim` — add encoding for `iekLambda`
  (`"Lam:site=<siteHash>/<declOrder>;caps=[<names>];params=[<types>]"`) and
  `iekClosureCall` (`"CC:<callee>(<arg_keys>)"`).
- `src/proptest/smt/dsl_typebridge.nim` — add `classifyProcTy` helper that
  extracts param/return IRTypes from `nnkProcTy` nodes; used by the parser
  to type-check `iekClosureCall` arguments.

**DoD:**
- [ ] RED test passes: IR round-trips through canonicalize; keys are
      distinct from analogous `isCall` / plain `iekVar` nodes.
- [ ] All case-dispatch sites compile cleanly (no exhaustive-match
      warnings); stub arms raise `ceNotImplemented` classified error.
- [ ] `dsl_parser.nim` free-variable detection: test with a nested scope
      where an outer local is captured and an inner local is not; assert
      only the outer name appears in `lambdaCaptures`.
- [ ] Closure iterator (`iterator foo(): int {.closure.}`) in expression
      position emits `ceNotImplemented` with
      `detail: "closure iterators not yet supported"` — not a crash.
- [ ] A closure with `{.raises: [], gcsafe.}` pragmas parses without
      residual `nnkPragma` nodes in the IR; pragmas are dropped (semchecker
      metadata only).
- [ ] **Monomorphization DoD (Depth-H4):** same lambda site instantiated at
      two type bindings (`T=int` and `T=string`) produces two DISTINCT cache
      keys from `canonicalize`; the key includes `params=[<concrete-type>]`
      at each instantiation; no cache collision.
- [ ] **PoC DoD (Feas-H2):** the test file includes a fixture
      `"C1 PoC: Z3_mk_app with runtime-constructed sorts"` that constructs a
      `RawZ3FuncDecl` via `Z3_mk_func_decl` (ffi.nim) with domain sorts
      derived from `svTuple` components via `sortOfTuple`, calls `Z3_mk_app`,
      and asserts Z3 accepts the application without sort-mismatch error.
- [ ] Regression: full `nimble test` passes (no prior test broken by the
      new IR arms in shared dispatch).
- [ ] `docs/symex/ADR-0009-closure-encoding.md` already exists (created in
      C0-ADR); C1 DoD confirms it is referenced from the test file's header
      comment.
---

### C2a — walker: closure construction as `(funcSym, envRecord)`

**What it does:** Wires up the `iekLambda` walker path. When the walker
encounters an `iekLambda` node, it (1) retrieves or creates the per-site
uninterpreted function declaration — one symbol per
`((siteHash, declOrder), envSortId, paramsSortTupleId)` tuple, memoized in
`WalkerStatics.closureSyms`; (2) snapshots free variables from the current
env, constructing the `envRecord` as a `svTuple` of the current-path SymVals
of each captured local; (3) binds the resulting `svClosure` into the
environment under the let-binding name. The `iekClosureCall` walker arm is
left as `ceNotImplemented` at this cycle — C2b wires that up.

**RED test:** `tests/tsymex_phase15_C2a_closure_capture.nim`, test name
`"C2a: closure capturing a local, resulting svClosure.closureEnv contains correct captured SymVals"`.
Specifies: a SUT
```nim
proc sut(x: int): int =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  f(3)
```
The test introspects the walker state via the test-only accessor pattern and
asserts that the resulting `svClosure.closureEnv` is a `svTuple` with one
field whose value equals the SymVal of `offset` (i.e., `x * 2`) at
construction time. No full `symexFind` call — construction only, confirmed
without body descent.

**GREEN:**
- `src/proptest/smt/runtime.nim` — implement `walk(iekLambda)`: iterate
  `lambdaCaptures`, look each name up in the current env, build `svTuple`
  snapshot; bind `svClosure`. `WalkerStatics.closureSyms` (Des-CRIT-D1 /
  cross-cluster invariant 7) carries the memoized symbols; key is
  `((siteHash, declOrder), envSortId, paramsSortTupleId)`. Add
  `extractFromSymVal(svClosure)` stub (returns `ceNotImplemented` classified
  error — closures as top-level SUT result types are unsupported; classified
  rather than silent).
- `src/proptest/smt/types.nim` — `svClosure` fields:
  ```nim
  of svClosure:
    closureSite*:   (siteHash: int64, declOrder: int)  ## body-hash + order index
    closureEnv*:    SymVal          ## svTuple of captured locals at construction
    closureRawFD*:  RawZ3FuncDecl  ## the uninterpreted symbol handle
  ```
- `src/proptest/smt/dsl_typebridge.nim` — no changes (IR already carries
  enough type info from C1).
- `src/proptest/symex.nim` — `emitTyAndReader` stub for closure result
  type returns `(NimNode for "proc", default-proc-construction)` with a
  `{.warning.}` — closures as top-level SUT result types are classified
  unsupported (Invariant 3).

**DoD:**
- [ ] RED test passes: `svClosure.closureEnv` contains the correct captured
      SymVals (assertable via test-only accessor pattern).
- [ ] Closure construction does not descend into the lambda body — confirmed
      by asserting no Z3 assertion is added to the solver during
      `walk(iekLambda)`.
- [ ] `sink T` parameter annotation in a closure parameter is captured
      by-value (semchecker has already resolved ownership semantics), same
      as plain `T`.
- [ ] Regression: full `nimble test` passes.

---

### C2b — walker: closure call dispatch

**What it does:** Wires up the `iekClosureCall` walker arm. On a closure
call, the walker (a) looks up the callee's `svClosure` in the current env;
(b) builds a fresh environment seeded with the captured locals from
`envRecord` fields and the call arguments; (c) descends into the lambda's
`lambdaBody` IR, tracking descent count against
`settings.maxClosureInlineCount` (default 64) via `CallFrameCtx.closureInlineCount`
(per-call-frame, per cross-cluster invariant 7); (d) collects the
`seq[InternalVerdict]` produced by body descent. **Multi-return-path axiom
(Depth-CRIT-2):** for each sub-path `(pc_i, v_i)` with `vrSat` outcome,
assert `implies(path.pc and pc_i, funcSym(env, args) == v_i)`. The main
axiom uses Z3 `ite`-merge of sub-path results conditioned on the
corresponding sub-conditions. **Proc-valued parameters** are resolved from
the current env via `svClosure` lookup — same dispatch path as a captured
closure. The `ceClosureUnknownCallee` classified error fires only for
genuinely-unbound call targets (not in env and not resolvable as an
`svClosure`).

**Closure application via raw FFI.** The phantom-typed
`Z3FuncDecl[ArgsTup, Ret]` wrapper cannot be instantiated at walk time
(type parameters are compile-time). Closure application goes through
`Z3_mk_app(ctx.raw, fd.raw, nArgs, argsPtr)` via `ffi.nim`, producing a
`Z3AnyAst` that is then cast to the appropriate typed wrapper via
`wrap[Z3Bool]` / `wrap[Z3Int]` / etc. based on the known return `IRType`.
The `sortOfTuple` helper (introduced in C1) derives the domain sort at walk
time. This is the same `Z3_mk_app` call that `funcdecl.nim`'s `emitApplyArity`
macro emits at its core — the raw-FFI path is identical, just without the
phantom-type wrapper.

**Memoization key.** `WalkerStatics.closureSyms` keys on
`((siteHash, declOrder), envSortId, paramsSortTupleId)` (Des-CRIT-D1;
cross-cluster invariant 7 places this on `WalkerStatics`, not `WalkCtx`
directly). The same syntactic lambda site instantiated with `T=int`
vs `T=string` produces two distinct `funcSym` entries with distinct Z3
signatures, preventing aliasing across generic instantiations.

**RED test:** `tests/tsymex_phase15_C2b_closure_call.nim`.
- Sub-test 1, `"C2b: closure call observes captured value"`: the C2a SUT
  is fully symex'd via `symexFind`; verdict is `sxSat`; witness `x`
  satisfies `f(3) = 3 + x * 2`; concretely `x = 5` yields result 13.
- Sub-test 2, `"C2b: proc-valued parameter resolved from env"`:
  ```nim
  proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))
  proc sut(n: int): int = applyTwice(proc(x: int): int = x + 1, n)
  ```
  symex'd produces `sxSat` with `n == 40` (target `== 42`). Validates
  proc-valued parameters are resolved via `svClosure` env lookup, not
  classified as unknown callees.
- Sub-test 3, `"C2b: 2-branch lambda body produces both axiom arms"`:
  ```nim
  proc sut(cond: bool, a: int, b: int): int =
    let f = proc(x: bool, p: int, q: int): int =
      if x: return p
      return q
    f(cond, a, b)
  ```
  symex'd produces `sxSat`. The test introspects the path-level axiom
  assertions and confirms: both `implies(pc and cond, funcSym(...) == a)`
  and `implies(pc and not cond, funcSym(...) == b)` are present. A second
  call `f(not cond, a, b)` on the same path reaches the complementary
  branch with a different `cond` value.

**GREEN:**
- `src/proptest/smt/runtime.nim` — implement `walk(iekClosureCall)`: env
  lookup → fresh env seeded from `envRecord` + args → body descent
  collecting `seq[InternalVerdict]` → multi-return-path axiom loop. For
  each sub-path `(pc_i, v_i)` with `vrSat` outcome, assert
  `implies(path.pc and pc_i, funcSym(env, args) == v_i)`. Main axiom
  uses Z3 `ite`-merge of sub-path results conditioned on sub-conditions.
  Descent counter lives on `CallFrameCtx.closureInlineCount: int`
  (pushed/popped per call frame per cross-cluster invariant 7); overflow
  yields `ceClosureInlineLimitExceeded` classified error.
- `src/proptest/smt/types.nim` — add `maxClosureInlineCount*: int = 64`
  to `SymexSettings`.

**DoD:**
- [ ] All three RED sub-tests pass.
- [ ] Multi-return-path axiom: the 2-branch lambda sub-test confirms both
      axiom arms are present for the same `funcSym` on the same path.
- [ ] The `funcSym` axiom is asserted under `path.pc`: unit test constructs
      two mutually-exclusive branches each calling the same closure with
      different args; asserts neither branch's axiom bleeds into the other.
- [ ] `maxClosureInlineCount` exceeded → `ceClosureInlineLimitExceeded`
      classified error, not a stack overflow.
- [ ] `WalkerStatics.closureSyms` key is
      `((siteHash, declOrder), envSortId, paramsSortTupleId)`: negative
      test instantiates the same lambda site at two different type signatures
      (generic SUT) and asserts they get distinct `funcSym` entries.
- [ ] Walker descent into lambda body uses a fresh env copy — mutation
      inside the body does not affect outer-path bindings.
- [ ] Regression: full `nimble test` passes.

---

### C3 — procs-as-values without captures (top-level procs)

**What it does:** Handles the case where a proc value is a reference to a
top-level (module-level) proc with no free variables. Such a proc-as-value
is encoded as `(funcSym, unitEnv)` where `unitEnv` is a zero-field
`svTuple`. The parser detects the top-level-proc case: a `nnkSym` node in
expression position whose `symKind` is `nskProc` at module scope (not a
local variable, not a `nnkParam`). The parser emits an `iekLambda` node
whose `lambdaCaptures = @[]` and whose `lambdaSite` uses a stable hash of
the proc's body via `symBodyHash` (same keying scheme as generic procs in
Cluster G). For top-level procs with stable qualified names, the
`declOrderIndex` is `0`. The `funcSym` is keyed by this hash pair in
`WalkerStatics.closureSyms`. The walker materializes `unitEnv` as an empty
tuple. Calling the proc-as-value is semantically equivalent to a direct
`isCall` to the same proc; the walker descends into the body with no env
bindings beyond the call arguments.

**RED test:** `tests/tsymex_phase15_C3_proc_as_value.nim`, test name
`"C3: top-level proc stored as value and called produces same witness as direct call"`.
Specifies: a SUT
```nim
proc double(x: int): int = x * 2

proc sut(n: int): int =
  let g = double
  g(n)
```
symex'd produces the same `sxSat` witness as a SUT that calls `double(n)`
directly. The test asserts both `symexFind` calls yield witnesses with the
same `n` value for the same target.

**GREEN:**
- `src/proptest/smt/dsl_parser.nim` — in `parseExpr`, detect when a
  `nnkSym` in expression position resolves to a top-level proc (not a
  local variable); emit `iekLambda` with `lambdaCaptures = @[]` and the
  proc's IR body (via `parseProc` on the resolved `getImpl`). This reuses
  the same `SymexProgram.procs` table populated by `isCall` parsing; no
  new IR table needed.
- `src/proptest/smt/runtime.nim` — no new walker code: `walk(iekLambda)`
  already handles empty `lambdaCaptures` (unitEnv is a zero-field
  `svTuple`). Add an assertion in the C3 walker path that confirms
  `closureEnv.fields.len == 0` for the no-capture case.
- `src/proptest/smt/canonicalize.nim` — no change: the site key already
  distinguishes top-level proc sites from lambda literal sites (different
  `siteHash` values from distinct bodies).

**DoD:**
- [ ] RED test passes; witnesses from proc-as-value call and direct call
      are equal (same field values, same Z3 model assignment).
- [ ] Parser does not emit `iekLambda` for proc-valued PARAMETERS (those
      are `nnkParam`-kinded syms, not top-level procs); classified error
      for that case until C4.
- [ ] Negative test: a local proc with captures passed to a proc-valued
      parameter still produces a classified `ceNotImplemented` error
      (not a silent fallback) — C4 handles that case.
- [ ] Regression: full `nimble test` passes.

---

### C4 — DSL higher-order targets: `filter`, `map`, `fold`

**What it does:** Adds walker special-cases for proptest's own DSL
higher-order operations on `seq[T]` — specifically `filter`, `map`, and
`fold` (the three HOFs that take a closure argument). When the walker
encounters an `isCall` node whose callee is one of these DSL procs **from
`std/sequtils`** (callee origin verified via
`callee.owner.strVal == "sequtils"` or equivalent `getTypeImpl` check —
Des-LOW-L3), it dispatches to a dedicated handler rather than the generic
`isCall` descent. The handler selects the inline or axiom path according to
`settings.inlinePolicy` (see preamble). (a) **Inline when bounded** — if
`inlinePolicy` permits and the sequence has a concrete Z3Int length at most
`settings.seqInlineThreshold` (default 8), the handler unrolls the closure
body once per element, producing quantifier-free constraints. (b)
**Axiomatize when symbolic** — for `map`, emits a universally-quantified
constraint using `mapArray` (from `z3/funcdecl.nim`); for `fold`, the axiom
path uses raw `Z3_mk_app(ctx.raw, fd.raw, nArgs, argsPtr)` via `ffi.nim`
(producing a `Z3AnyAst` cast via `wrap[T]` based on the known return
`IRType`) because the phantom-typed `seqFoldl` wrapper cannot be
instantiated at walk time. For `filter`, the axiomatize path is **deferred
to Phase 16** — no Z3 `seqFilter` HOF exists in nim-z3 today and
quantifier construction for a sequence filter predicate is non-trivial; C4
emits `ceUnsupportedHof` (`severity: sevError`) when `filter` would take
the axiomatize branch. The inline path for `filter` (bounded length) is
fully supported. Both `inlinePolicy` and `seqInlineThreshold` participate
in the canonicalize cache key. `seqInlineThreshold` is documented as
coupled to `ipHybrid` (ignored otherwise); the settings validator warns
when `seqInlineThreshold` is set without `ipHybrid`.

**RED test:** `tests/tsymex_phase15_C4_hof.nim`, test name
`"C4: filter over bounded seq with predicate closure produces sat with predicate body realized"`.
Specifies: a SUT
```nim
proc sut(xs: seq[int]): seq[int] =
  xs.filter(proc(x: int): bool = x > 0)
```
where `xs` has a statically-bounded length (via a strategy with `maxLen=4`)
is symex'd; the verdict is `sxSat`; the witness `xs` contains at least one
positive element; the filtered result is non-empty. The test uses the
bounded inline path (length ≤ 8). A second sub-test asserts that when
length is symbolic the `filter` axiomatize path emits `ceUnsupportedHof`
with `severity: sevError` (Phase 16 deferred — no Z3 `seqFilter` HOF). A
third sub-test asserts `map` and `fold` axiomatize paths terminate without
Z3Error when length is symbolic (verdict may be `sxUnknown` if rlimit hit).

**GREEN:**
- `src/proptest/smt/runtime.nim` — add `walkHofFilter`, `walkHofMap`,
  `walkHofFold` handlers. Each handler: (1) verifies callee origin via
  `callee.owner.strVal == "sequtils"` (or `getTypeImpl(callee).owner.strVal`
  equivalent) — non-sequtils same-named procs fall through to standard
  `isCall` descent; (2) reads `settings.inlinePolicy` and
  `settings.seqInlineThreshold`; (3) dispatches to inline or axiom path.
  Inline path: loop `0..<concreteLen`, call `walk(lambdaBody)` with element
  bound, accumulate results. Axiom path for `map`: `mapArray` from
  `z3/funcdecl.nim`. Axiom path for `fold`: raw `Z3_mk_app` via `ffi.nim`
  (produces `Z3AnyAst`, cast via `wrap[T]` based on return `IRType`). Axiom
  path for `filter`: emit `ceUnsupportedHof` (`severity: sevError`, deferred
  to Phase 16). Settings validator: warn when `seqInlineThreshold` is set
  explicitly and `inlinePolicy != ipHybrid`. Register the three handlers in
  the main `walk(isCall)` dispatch table.
- `src/proptest/smt/types.nim` — add to `SymexSettings`:
  ```nim
  inlinePolicy*:       InlinePolicy = ipHybrid   ## defined in Z-cluster
  seqInlineThreshold*: int = 8                   ## coupled to ipHybrid
  ```
  `InlinePolicy` is imported from Z-cluster; DO NOT redefine here.
- `src/proptest/smt/canonicalize.nim` — include `inlinePolicy` and
  `seqInlineThreshold` in the settings digest.
- `src/proptest/symex.nim` — no change (HOF handling is entirely walker-
  side).

**DoD:**
- [ ] Bounded inline RED test passes (filter witness is non-empty, all
      elements positive).
- [ ] Symbolic-length `filter` emits `ceUnsupportedHof` with
      `severity: sevError` (not a crash, not a silent fallback).
- [ ] `map` and `fold` axiomatize sub-tests terminate without Z3Error
      (verdict may be `sxUnknown` if rlimit hit — acceptable).
- [ ] `fold` axiom path uses raw `Z3_mk_app` via `ffi.nim`; test confirms
      no compile error from attempting phantom-typed `seqFoldl` at walk time.
- [ ] **Callee origin negative test (Des-LOW-L3):** a user-defined
      `proc filter[T](s: seq[T], f: proc(x: T): bool): seq[T]` is NOT
      intercepted by the HOF handler; it falls through to standard `isCall`
      descent and produces a `ceNotImplemented` classified error (not an
      incorrect HOF dispatch).
- [ ] `seqInlineThreshold` set without `ipHybrid` → settings validator
      emits a warning (checked in a unit test of the validator).
- [ ] Classified error (not silent fallback) when a HOF closure argument
      is not a locally-resolvable `svClosure` (e.g., a closure passed in
      as a SUT parameter — not yet supported; produces `ceNotImplemented`).
- [ ] `ipAlwaysInline` emits a `{.warning.}` and is documented as unsound
      for symbolic lengths (unit-test use only).
- [ ] Regression: full `nimble test` passes.

---

### C5 — closure equality semantics

**What it does:** Wires up the `bEq` / `bNe` binop cases in
`walk(iekBinop)` when both operands resolve to `svClosure`. Per ADR-0009
(Open Question 6 closed), equality uses **nominal-for-site +
structural-for-env** semantics (Des-H6):
- If `(c1.siteHash, c1.declOrder) != (c2.siteHash, c2.declOrder)` (Nim-side
  integer-pair comparison) → emit `mkBool(false)`. Two closures from
  different syntactic sites are always unequal, regardless of their
  environments.
- If site pairs are equal → emit `c1.closureEnv == c2.closureEnv`
  (Z3 tuple equality via `svTupleEq`).

This matches Nim runtime proc-value semantics (proc pointer identity for
inter-site; closure environment matters for same-site) and is correct for a
correctness-oriented symex. The Nim runtime divergence (Nim's `==` on
closures is undefined / may raise `Defect`) is documented in
`docs/symex/closures.md` and `determinism.md`. Also appends the
`closures.md` subsections (skeleton was in C0-ADR): C2a/C2b/C3/C4/C5
subsections are completed here.

**RED test:** `tests/tsymex_phase15_C5_closure_eq.nim`, test name
`"C5: nominal-for-site + structural-for-env closure equality"`.
Specifies: a SUT containing
```nim
proc sut(x: int): bool =
  let f = proc(y: int): int = y + x
  let g = proc(y: int): int = y + x
  f == g  # two distinct lambda sites → distinct (siteHash, declOrder) pairs
```
The test asserts that `f == g` is `sxUnsat` (two distinct sites → always
unequal, regardless of `x`). A second SUT:
```nim
proc sut(x: int): bool =
  let mk = proc(): (proc(y: int): int) = proc(y: int): int = y + x
  let f = mk(); let g = mk()
  f == g
```
asserts `sxSat` with a witness where `x` is any value (same site, same env
→ equal). A third negative test documents the runtime-divergence case with
an explicit comment: "Nim runtime behaviour for closure comparison is
undefined; symex nominal-for-site + structural-for-env semantics documented
in ADR-0009 and closures.md." A fourth sub-test validates formatting
stability: two versions of the same lambda (differing only in whitespace
and inline comments) produce the same `siteHash`, confirming that `symBodyHash`
hashes the semantic AST rather than source text.

**GREEN:**
- `src/proptest/smt/runtime.nim` — in `walk(iekBinop)`, add `of bEq, bNe:`
  branch that detects `svClosure` operands. If
  `(c1.siteHash, c1.declOrder) != (c2.siteHash, c2.declOrder)` (Nim
  integer-pair compare at walk time) → emit `mkBool(false)`. Otherwise →
  emit `svTupleEq(c1.closureEnv, c2.closureEnv)`.
- `docs/symex/closures.md` — append subsections (skeleton was authored in
  C0-ADR): "Encoding" (C2a fill-in), "Capture restrictions" (C2a fill-in),
  "Equality semantics" (C5 fill-in), "Generics interaction" (stub — C6 fills
  in), "Known divergences from Nim runtime" (C5 fill-in with C2b multi-path
  and equality divergence notes).
- `docs/symex/determinism.md` — add "closure equality" row to the
  known-divergences table.

**DoD:**
- [ ] All four RED sub-tests produce the expected verdicts.
- [ ] Formatting-stability test: two lambdas at semantically-same position
      with different whitespace/comments produce the same `siteHash` (since
      `symBodyHash` hashes the body AST, not the source text).
- [ ] Runtime-divergence case is documented in both the test file (as a
      comment) and `closures.md` (as a subsection).
- [ ] `docs/symex/closures.md` covers: ADR-0009 recap, nominal-for-site +
      structural-for-env semantics (`(siteHash, declOrder)` integer-pair),
      capture restrictions, the `var T` capture error case (Invariant 3),
      and the `InlinePolicy` / `seqInlineThreshold` settings reference.
- [ ] Regression: full `nimble test` passes.

**Invariant 3 note.** Closures whose capture list contains a `var T`
(captured by reference, not by value) produce a classified
`SymexErrorInfo(kind: ceUnsupportedCapture, detail: "var T capture not
supported — closure captures mutable reference; symex models by-value
only")` at walker time. Captures of `ref T` types produce
`ceUnsupportedCapture` until R13 (the closure-capturing-ref composition
cycle in Cluster R) lifts the classification. These are the only capture
shapes explicitly classified as errors in C1–C5; all other unsupported
shapes fall under the `ceNotImplemented` path.

---

### C6 — regression smoke against Cluster G

**What it does:** Verifies that closures interact correctly with Cluster
G's generic instantiation machinery (which lands before Cluster C in the
phase ordering). The canonical breakage pattern from Phase 14 applies: a
shared-module edit in the walker's `iekLambda` / `iekClosureCall` dispatch
can silently corrupt the `WalkCtx.instantiationCache` used by Cluster G.
C6 is a pure regression smoke cycle — no new IR kinds, no new walker
paths. It re-runs a representative sample of Cluster G's test suite under
the C1–C5 walker state and adds two composition tests that exercise both
clusters simultaneously. **Walker version is bumped `"8"→"9"` at this
cycle via `canonicalize.nim`** (cross-cluster Invariant 1 and M12 — the
single source-of-truth constant lives in `canonicalize.nim`, not
`runtime.nim`).

**RED test:** `tests/tsymex_phase15_C6_regression.nim`, test name
`"C6: generic higher-order proc with closure argument produces correct witness"`.
Specifies: a generic SUT
```nim
proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))

proc sut(n: int): int =
  applyTwice(proc(x: int): int = x + 1, n)
```
symex'd produces `sxSat` with `n` such that `applyTwice(..., n) == 42`,
i.e., `n == 40`. This validates G's instantiation machinery + C's closure
application interact correctly: G `classifyProcTy` must survive
`monomorphize` substitution. A second sub-test uses a generic `map` over a
concrete-typed seq with a closure element transformer and asserts the
witness is coherent. Both tests must pass with the full Cluster G
instantiation cache active (not with a fresh `WalkCtx`).

**GREEN:**
- No new source files. The RED tests drive any fixes needed in:
  - `src/proptest/smt/runtime.nim` — if `WalkerStatics.closureSyms` and
    `WalkCtx.instantiationCache` share mutable state across a generic
    instantiation boundary, separate their scopes.
  - `src/proptest/smt/dsl_parser.nim` — if `parseProc` for a generic
    proc monomorphized with a proc-type argument misclassifies the
    argument as `isUnsupported`, extend the `classifyProcTy` path
    introduced in C1.
- `src/proptest/smt/canonicalize.nim` — bump walker version constant
  `"8" → "9"` (M12: single source-of-truth in `canonicalize.nim`).
- `tests/tsymex_phase15_C6_regression.nim` — the two composition tests
  described above.
- A targeted re-run of all `tsymex_phase15_G*` test files (CI step, not
  a new test file): if any G-cluster test regresses under the C1–C5
  walker, C6 is not done until fixed.

**DoD:**
- [ ] Both C6 RED tests pass.
- [ ] Full re-run of `tsymex_phase15_G*` tests passes with no
      regressions.
- [ ] Full `nimble test` passes (all ~76+ test files green).
- [ ] Walker version constant in `canonicalize.nim` updated to `"9"`;
      assert `canonicalize.walkerVersion == "9"` in the DoD test.
- [ ] `withSymexSettings(...) do (s): s.maxClosureInlineCount = 8`
      override confirmed in at least one C-cluster test.
- [ ] `docs/symex/closures.md` completed: "Generics interaction"
      subsection cross-referencing ADR-0008 added (C6 fill-in).
- [ ] SYMEX_PLAN.md Phase 15 Cluster C row marked complete; cycle count
      and test file count updated.

<!-- CLUSTER_R -->
## Cluster R — ref/ptr aliasing (logical heap)

### Cycle table

| Cycle | Topic | Key dependency | Version bumps |
|-------|-------|---------------|---------------|
| R1a | IR + SVKind variants + exhaustive dispatch stubs (`itRef`, `itPtr`, `isDeref`, `isNew`, `svRef`, `svPtr`) | Cluster H (H1 done) | — |
| R1 | Ref sort introduction — `WalkerStatics.refSorts`, `nilConsts`, `allocRefSort`, `isDeref` select | R1a | — |
| R1b | Inter-procedural heap threading — pass/merge `path.heaps` across call frames; `max(caller,callee)` write-back | R1 | — |
| R2 | `new T` semantics — per-path `allocCounters`, fresh ref distinctness; `maxFreshnessAssertions` cap | R1b | — |
| R3 | `p[]` read — `select(heap_T, p)`; per-path heap isolation; `seq[ref T]` element path | R2 | — |
| R4 | `p[] = v` write — `store(heap_T, p, v)` heap replace; alias observable | R3 | — |
| R5 | `nil` handling — `nil_T` constant, nil-path fork → `sxRaised(NilAccessDefect)`; nil-fork short-circuit | R4, Cluster E | — |
| R6 | `ref object` field access — select+field-project / store+field-modify; inherited fields; variant-field guard | R5 | — |
| R7 | Ref equality + alias chain — `let q = p`; `q := r` breaks alias | R6 | — |
| R8 | `ptr T` family + pointer arithmetic — same heap model; `inc`/`dec` → `hePtrArith` hint | R7 | — |
| R8b | `var ref T` parameter handling — ref rebinding write-back + heap merge; `heUnsupportedVarRef` fallback | R8 | — |
| R9 | Recursive ref structures — `path.heapDepth` counter; `heDepthExhausted` on overflow; `maxHeapDepth = 0` semantics | R8b | — |
| R10 | `maxHeapDepth` setting — cache-key participation; `determinism.md` section | R9 | — |
| R11 | `cast[ptr T](addr x)` — `sxUnknown(heUnsafeCast)`; `isUnsafeCast` IR node | R10 | — |
| R11b | Cross-cluster regression sweep + `docs/symex/witness-format-v3.md` authoring | R11 | — |
| R12 | Walker version `"9"→"10"`, rendering version `"2"→"3"`, heap-snapshot witness format | R11b | walker → `"10"`, rendering → `"3"` |
| R13 | Closures capturing `ref T`; `ptr T` + `try`/`finally` composition | R12, Cluster C | — |

**R0 removed.** R0 (preparatory `Path` refactor) was promoted to Cluster H's H1 cycle. Cluster H now lands before Cluster E. `Path` already carries `heaps`, `heapDepth`, and `allocCounters` when Cluster R begins.

### Preamble

**Path field inheritance from Cluster H.** Cluster H's H1 cycle (which
lands before Cluster E) has already extended `Path` with three new
per-path fields: `heaps: Table[string, Z3AnyAst]`,
`heapDepth: int`, and `allocCounters: Table[string, int]`. All fork
sites have been audited and deep-copy these fields correctly. Cluster R
inherits this infrastructure and does not repeat that work.

**WalkerStatics field allocation.** `EffectCtx` was split into
`WalkerStatics` (per-walker, immutable post-parse) and `CallFrameCtx`
(push/pop per call descent) in the C6/round-2 `WalkerStatics` refactor.
Ref-cluster per-walker state lives on `WalkerStatics`:

- `WalkerStatics.refSorts: Table[string, RawZ3Sort]` — **per-walker**. Once
  a `Ref_T` uninterpreted sort is allocated for a given `typeId`, it is
  shared across all paths in that walker invocation. Sorts are allocated
  via `mkUninterpretedSort(ctx, "Ref_" & typeId)` (from `z3/sort.nim`,
  which wraps `Z3_mk_uninterpreted_sort`). Two calls with the same name
  in the same context yield the same sort — this is the idempotency
  guarantee from the Z3 API.

- `WalkerStatics.nilConsts: Table[string, Z3AnyAst]` — **per-walker**.
  One nil constant per ref sort, allocated once and cached. Named
  `"nil_<typeId>"` per ref sort.

- `Path.heaps: Table[string, Z3AnyAst]` — **per-path** (from H1). Each
  entry is a type-erased `Z3Array[Ref_T, T_sym]` for the heap associated
  with that pointee type. Deep-copied at every fork site.
  `p[]` is `select(path.heaps[T], p)`; `p[] = v` replaces
  `path.heaps[T]` with `store(path.heaps[T], p, v)`.

- `Path.heapDepth: int` — **per-path** (from H1). Read-counter incremented
  by every `isDeref`/`isDerefWrite`. Starts at 0; overflow at
  `settings.maxHeapDepth` → `sxUnknown(heDepthExhausted)`. Deep-copied
  at fork.

- `Path.allocCounters: Table[string, int]` — **per-path** (from H1). Monotone
  freshness counter per ref type. Deep-copied at fork so allocations on
  disjoint forked paths produce independent name sequences with no
  cross-path freshness constraints.

This is consistent with v2 top matter invariant 1 (per-cluster version
bumps) and the `WalkerStatics` refactor described in the v2 revision history.

**Out of scope for this cluster.**

| Type / pattern | Classified error | Breadth priority |
|----------------|-----------------|-----------------|
| `owned T` | `heUnsupportedOwnership` (`sevError`) | Breadth-LOW-L4 |
| `WeakRef[T]` | `heUnsupportedOwnership` (`sevError`) | Breadth-LOW-L4 |
| `Atomic[T]` | `heUnsupportedOwnership` (`sevError`) | Breadth-LOW-L4 |
| `seq[seq[T]]` (heap element) | `seNestedSeqUnsupported` (`sevError`) | Phase 16 |
| `cast` between non-ref types beyond `cast[ptr T]` | existing `heUnsafeCast` path | R11 |
| `addr` of stack locals (non-pointer context) | `heUnsafeCast` (`sevError`) | R11 / Phase 16 |

**Why a logical heap, not static points-to analysis.** The proptest
symex engine already owns a path-condition that Z3 evaluates per-path.
Once you have path-sat, may-alias and must-alias are consequences of
Z3 equality queries on the symbolic ref values that inhabit each path:
two symbolic refs `p` and `q` alias on a given path iff adding `p == q`
to that path's constraint set is satisfiable. This is strictly more
precise than any flow-insensitive static analysis. Andersen-style
points-to analysis over-approximates by collapsing all allocation sites
reachable along any path into a single abstract location; Steensgaard
further collapses via union-find; region-based analyses colour by source
region rather than by path feasibility. All three report may-alias pairs
that are unreachable under the current path constraint — producing false
positives the symex engine would then need to filter. KLEE, Pex, angr,
and CBMC all use the logical-heap model for exactly this reason: symbolic
memory is the natural domain of an engine that already runs Z3.

The decision (ADR-0010) is: one `Z3Array[Ref_T, T_sym]` per concrete
pointee type `T`, where `Ref_T` is a Z3 uninterpreted sort. `p[]` is
`select(path.heaps[T], p)`; `p[] = v` replaces `path.heaps[T]` with
`store(path.heaps[T], p, v)`; `p.field = v` expands to a full
field-modify record update under the same heap-replace. Every
heap-mutating operation produces a new functional-array term —
Z3's array theory is purely functional, so the "old heap" and "new
heap" terms coexist in the solver's model, which is exactly what we
want: aliased reads on different paths remain independent.

**Allocation freshness via per-path monotone counter.** The counter is
per-`Path` (not per-walker): if the `new` node is reachable only on path
P, the counter increment happens under P's constraints, and the fresh ref
constant is asserted disjoint from all refs allocated on prior increments
of the counter along the SAME path. Disjoint paths do not share counters
— two `new T` calls on forked paths produce independent ref constants
with no cross-path `!=` constraints asserted. The alternative, a
universally-quantified freshness axiom `∀ q. new_p ≠ q`, forces Z3 into
the quantifier-instantiation regime and destroys query performance for
any SUT with more than two or three allocations. The per-path monotone
counter avoids that cost entirely.

**Sort-per-pointee-type prevents cross-type aliasing.** `ref int` refs
live in the `Ref_int` sort; `ref string` refs live in `Ref_string`. A
Z3 equality `p_int == q_string` would be a sort-mismatch error at the
Z3 API level, surfaced as a `Z3SortMismatchError` (caught by C4's
top-level `Z3Error` handler and mapped to `sxUnknown(heUnsafeCast)`).
This is correct: in Nim's type system, comparing a `ref int` identity
with a `ref string` identity is also a type error — the sort boundary
enforces the same invariant at the Z3 level and eliminates an entire
class of false-alias bugs that would otherwise require additional solver
lemmas to exclude.

**Recursive structures and depth bounding.** A singly-linked list node
`type Node = ref object; val: int; next: Node` is a self-referential
heap type. The walker materialises a fresh `Ref_Node` symbol for each
logical allocation, but without a recursion bound the walker would chase
`next` pointers indefinitely. Cluster R introduces `maxHeapDepth` (added
to `SymexSettings`, default 8 — chosen to cover 2-level trees comfortably
without blowing up linear linked-list exploration) as an explicit hop
count on heap reads: each `p[]` deref increments `path.heapDepth`; when
it exceeds the budget, the walker halts the current path with `sxUnknown`
and a classified `SymexErrorInfo{kind: heDepthExhausted}`. This is the
same classified-error pattern C4 established for Z3 internal errors:
invariant 3 (no silent fallbacks) requires the error kind to be
machine-readable. Widening is noted in the backlog for Phase 16+.

**Open question 7 (unsafe cast) — CLOSED.** `cast[ptr T](addr x)` and
similar unsafe address-taking patterns are modeled as `sxUnknown` with
`SymexErrorInfo{kind: heUnsafeCast}` — a classified, machine-readable
halt. Safe-cast patterns in PBT-tested code are rare; modeling
cost-benefit favors deferral to Phase 16 backlog (recorded). R11
implements this.

**Witness format and version bumps.** Witnesses for SUTs with heap-typed
parameters must record the initial heap state. Accordingly, rendering
version bumps from `"2"` to `"3"` in R12. Per v2 invariant 1, walker
version bumps per cluster: Cluster R's bump is `"9"→"10"` in R12. The
heap-snapshot witness format spec lives in `docs/symex/witness-format-v3.md`
(authored before R12 begins). R11b handles the cross-cluster regression
sweep with no format/version changes; R12 handles the bumps and format
extension only.

**Standing rules:**

- PhD-CS bar; no external consumers; API breaks are free.
- Invariant 3 (no silent fallbacks): nil-deref, depth exhaustion, unsafe
  cast, and pointer arithmetic are all classified `he`-prefix errors with
  non-empty `SymexErrorInfo.errors`. No cycle may emit `sxUnknown` with
  an empty `errors` field for any R-cluster error condition.
- Error-kind prefix: all R-cluster errors use `he` prefix, expressed as
  `SymexErrorKind` enum variants: `heDepthExhausted`, `heUnsafeCast`,
  `hePtrArith`, `heFreshnessCapExceeded`, `heRefVariantUnsupported`,
  `heUnsupportedOwnership`, `heUnsupportedVarRef`. No `ge`, `ce`, `ee`,
  `se`, or `fe` errors appear in this cluster's code or tests.
- Severity split: halting errors (`heDepthExhausted`, `heUnsafeCast`,
  `heRefVariantUnsupported`, `heUnsupportedOwnership`, `heUnsupportedVarRef`)
  use `sevError`; annotation hints (`hePtrFamily`, `heFreshnessCapExceeded`)
  use `sevHint`. Invariant: `sxUnknown` implies at least one `sevError` entry.
- All bare `kind: "he..."` string literals in GREEN code and tests must use
  `SymexErrorKind` enum variants (wired by the Z0-Enum cycle before R begins).
- All `EffectCtx` references in R-cluster source are replaced by `WalkerStatics`
  where the field is per-walker, or `CallFrameCtx` where per-call-frame.
- Invariant 4 (regression smoke): R11b re-runs a curated subset of every
  prior cluster's tests under the heap-state-threaded walker.
- Version bumps (walker `"9"→"10"`, rendering `"2"→"3"`) land atomically
  in R12's GREEN only. Both bumps edit `src/proptest/smt/canonicalize.nim`.

---

### R1a — IR + SVKind variants + exhaustive dispatch stubs (Feas-H11)

**What it does:** Introduces the new IR nodes and `SVKind` variants that
every subsequent R cycle depends on, and adds exhaustive dispatch stubs
so the project compiles at R1a exit. Nothing is executed at runtime yet;
walker stubs emit `heUnresolvedRef` (`sevError`) for any `itRef`/`itPtr`
node they encounter.

New IR nodes added to `src/proptest/smt/types.nim`:
- `IRTypeKind`: `itRef` (phantom-typed ref; carries `refPointeeTy: IRType`),
  `itPtr` (same for ptr).
- `IRStmtKind`: `isDeref` (A-normalised `p[]` read, binds fresh let-name),
  `isNew` (allocation, binds fresh ref).
- Constructors: `tRef`, `tPtr`, `mkDeref`, `mkNewT`, `mkPtrDeref`.
- `SymexSettings.maxHeapDepth: int` field (default 8; 0 = unlimited).

New `SVKind` variants added to `src/proptest/smt/runtime.nim`:
- `svRef(refAst: Z3AnyAst)` — a `Ref_T`-sorted symbolic ref constant.
- `svPtr(ptrAst: Z3AnyAst, ptrFamily: bool = true)` — same for ptr.

Exhaustive dispatch stubs added (compile-time coverage, no runtime
semantics yet) in every `case sv.kind` / `case stmt.kind` site:
`walk`, `typeOf`, `svEq`, `iteSymVal`, `toDefaultLiteral`,
`symValHash`, `extractLeaf`, `emitChoices`.

`classifyType` in `src/proptest/smt/dsl_typebridge.nim` gains:
- `nnkRefTy` → `tRef(pointeeTy)`
- `nnkPtrTy` → `tPtr(pointeeTy)`
- `owned T` / `WeakRef[T]` / `Atomic[T]` → emit `heUnsupportedOwnership`
  (`sevError`) classified error at parse time (Breadth-LOW-L4 coverage).

`src/proptest/smt/dsl_parser.nim` stubs for `nnkDerefExpr` /
`nnkHiddenDeref` → `isDeref` IR; `nnkCall` to `new` → `isNew`.

**RED test:** `tests/tsymex_phase15_r1a_stubs.nim`, test name
`"R1a: itRef/itPtr/isDeref/isNew IR round-trips through canonicalize; walker stubs emit heUnresolvedRef"`.
Specifies: (a) `tRef(tInt(64))` round-trips through `canonicalize` and
back without error; (b) `tPtr(tInt(64))` likewise; (c) a SUT with a
`ref int` param (no deref) compiles and runs, returning `sxUnknown` with
`heUnresolvedRef` in `errors` (stubs are in place).

**GREEN:**

- `src/proptest/smt/types.nim` — IR additions above.
- `src/proptest/smt/runtime.nim` — `svRef`/`svPtr` SVKind variants +
  exhaustive stubs. Walker stubs for `itRef`/`itPtr`/`isDeref`/`isNew`
  emit `heUnresolvedRef` (`sevError`) classified error.
- `src/proptest/smt/dsl_typebridge.nim` — `classifyType` extensions
  including `owned T`/`WeakRef`/`Atomic` → `heUnsupportedOwnership`.
- `src/proptest/smt/dsl_parser.nim` — deref/new parse stubs.
- `tests/tsymex_phase15_r1a_stubs.nim` — new test file (RED → GREEN).

**DoD:**
- [ ] `tsymex_phase15_r1a_stubs.nim` passes both backends
- [ ] `tRef`/`tPtr` IR round-trips through `canonicalize` (sub-test a/b)
- [ ] Walker stubs produce `heUnresolvedRef` classified error (sub-test c)
- [ ] Every `case sv.kind` dispatch site compiles exhaustively (no
  wildcard catch-all needed for `svRef`/`svPtr`)
- [ ] `nim c src/proptest/smt/runtime.nim` succeeds with no new warnings
- [ ] `owned T` SUT param produces `heUnsupportedOwnership` classified error
  at parse time (DoD coverage for Breadth-LOW-L4)
- [ ] No walker version bump

---

### R1 — ref sort introduction

**What it does:** Promotes R1a's stubs to real Z3 semantics. For each
`ref T` in the SUT's parameter or local signature, the walker allocates a
Z3 uninterpreted sort `Ref_T` via `mkUninterpretedSort(ctx, "Ref_" &
typeId)` (nim-z3's `z3/sort.nim`, which wraps `Z3_mk_uninterpreted_sort`
returning `Z3Sort[stUninterpreted]` with a `raw: RawZ3Sort` field). The
sort handle is stored in `WalkerStatics.refSorts: Table[string, RawZ3Sort]`
— **per-walker, not per-path** — so sorts are allocated once and shared
across all paths. Each path's `path.heaps[typeId]` is initialized to a
free `Z3Array[Ref_T, T_sym]` variable (the initial heap for that type on
that path). `nil_T: Ref_T` is a sort-level distinguished constant named
`"nil_<typeId>"` per ref sort, allocated once and cached in
`WalkerStatics.nilConsts`.

`allocRefSort(ctx, statics, pointeeTy)` is the helper that calls
`mkUninterpretedSort` once per `typeId` and caches in
`WalkerStatics.refSorts`.

On the first deref of any `ref T` param, the walker performs a `select`
on `path.heaps[typeId]` via `Z3_mk_select` with the param's `Ref_T`-sorted
symbol and returns the resulting `T_sym`-typed `SymVal` for further
evaluation.

**RED test:** `tests/tsymex_phase15_r1_refsort.nim`, test name
`"R1: SUT with ref int param materialises ref sort and deref returns sat witness"`.
Specifies: SUT `proc f(p: ref int): bool = p[] == 42`;
`symexFind(f, tLabel("sat"))` returns `sxSat` with a witness that
satisfies `p[] == 42`; the walker does not crash or emit `sxUnknown`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — promote `svRef`/`svPtr` stubs from R1a
  to real semantics. `WalkerStatics` gains `refSorts: Table[string,
  RawZ3Sort]` and `nilConsts: Table[string, Z3AnyAst]`. New
  `allocRefSort(ctx, statics, pointeeTy)` helper. Walker `of isDeref:`
  replaces the `heUnresolvedRef` stub with real `Z3_mk_select` on
  `path.heaps[typeId]` and binds the resulting `SymVal` to the let-name.

- `src/proptest/smt/dsl_typebridge.nim` — promote `nnkRefTy`/`nnkPtrTy`
  stubs from R1a to full `tRef(pointeeTy)` / `tPtr(pointeeTy)` emission.

- `src/proptest/smt/dsl_parser.nim` — promote `nnkDerefExpr` /
  `nnkHiddenDeref` stubs from R1a to real `isDeref` IR emission via
  A-normalisation. Promote `nnkCall` to `new` stub to real `isNew` emission.

- `src/proptest/symex.nim` — `emitTyAndReader` gains a case for `itRef` /
  `itPtr` (Breadth-CRIT-1, C7): produces heap-snapshot-based readers.
  DoD: `proc f(p: ref int): bool` SUT yields a witness whose
  `heapSnapshot` field contains the `p`→42 mapping.

- `tests/tsymex_phase15_r1_refsort.nim` — new test file (RED → GREEN).

**DoD:**
- [ ] `tsymex_phase15_r1_refsort.nim` passes both backends
- [ ] `WalkerStatics.refSorts` is per-walker (not per-path); verified by
  asserting that two paths in the same walker share the same sort handle
- [ ] `Path.heaps` is per-path; each path has an independent `Z3AnyAst`
  heap variable
- [ ] `nim c src/proptest/smt/runtime.nim` succeeds with no new warnings
- [ ] `SymexSettings.maxHeapDepth` documented in `docs/symex/determinism.md`
  under a new "Heap depth budget" subsection
- [ ] `emitTyAndReader` for `itRef`/`itPtr` produces a witness with a
  `heapSnapshot` field for a `proc f(p: ref int): bool` SUT (C7 / Breadth-CRIT-1)

---

### R1b — inter-procedural heap threading

**What it does:** Every `isCall` / `isGenericCall` / `iekClosureCall`
walker arm must thread heap state across the call boundary:

1. **Call entry:** pass the caller's `path.heaps`, `path.heapDepth`, and
   `path.allocCounters` into the callee's initial `Path` as its starting
   heap state.
2. **Call return:** merge the callee's exit `Path.heaps` back into the
   caller's path. The merge for `heaps` is a replacement (the callee's
   final `heaps` becomes the caller's). The merge for `allocCounters`
   uses `max(caller[T], callee[T])` for each type key — NOT replacement.
   This preserves the freshness invariant: subsequent caller allocations
   after the call returns will use counter values higher than any callee
   allocation, so they cannot collide with callee-allocated refs on the
   same path.

Without R1b, each call descent starts with a fresh empty `Path.heaps`
(the R1 default), so writes inside the callee are silently discarded
and the caller never observes them.

**RED test:** `tests/tsymex_phase15_r1b_callheap.nim`, test name
`"R1b: caller write through ref observed by callee reading aliased ref"`.
Specifies: SUT
```nim
proc inner(q: ref int): bool = q[] == 7
proc f(p: ref int) =
  p[] = 7
  if inner(p): symexTarget("hit")
```
`symexFind(f, tLabel("hit"))` returns `sxSat`. Without R1b, `inner`
operates on a fresh empty heap and `q[]` is unconstrained; the test
would fail or return `sxUnknown`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — at each `isCall`/`isGenericCall`/
  `iekClosureCall` walker arm, before constructing the callee's initial
  `Path`, copy `caller.path.heaps`, `caller.path.heapDepth`, and
  `caller.path.allocCounters` into the callee's initial path. After
  the callee walk completes, copy the callee's exit `heaps` (and
  `allocCounters`, for counter continuity) back into the caller's path.

- `tests/tsymex_phase15_r1b_callheap.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r1b_callheap.nim` passes both backends
- [ ] Caller write through ref `p` observed by callee reading aliased
  ref `q == p` in the sat witness
- [ ] Caller's post-call `new T` produces a ref distinct from any callee
  allocation (freshness invariant: `allocCounters` write-back uses `max`)
- [ ] Regressions R1a, R1 pass

---

### R2 — `new T` semantics

**What it does:** Implements `isNew` walker semantics. Each `new T`
increments `path.allocCounters[typeId]` (per-path), derives a fresh Z3
constant of sort `Ref_T` named `"ref_<typeId>_<n>"`, asserts
`p != nilConst(Ref_T)` (freshly allocated refs are never nil), and
asserts `p != q` for every prior live ref of this sort on the current
path (the counter-based distinctness guarantee). The fresh ref constant
is bound in the walker env under the let-name from the `isNew` statement.

Disjoint forked paths do not share counters. A `new T` on path A
produces `ref_T_0`; a `new T` on disjoint path B also produces
`ref_T_0` (counter restarted from the fork point's snapshot). No
`ref_T_0 != ref_T_1` constraint is emitted on path B for path A's
allocation — verified by the additional DoD test below.

**RED test:** `tests/tsymex_phase15_r2_new.nim`, test name
`"R2: two new T allocations produce non-equal refs on sat path"`.
Specifies: SUT `proc f() = let p = new int; let q = new int; if p == q: symexTarget("alias")`;
`symexFind(f, tLabel("alias"))` returns `sxUnsat` (the two freshly
allocated refs are provably distinct, so the branch is unreachable).

**GREEN:**

- `src/proptest/smt/runtime.nim` — implement `of isNew:` walker branch.
  `freshRef(ctx, sort, typeId, path)` increments `path.allocCounters[typeId]`
  and wraps `Z3_mk_const` with the derived name `"ref_<typeId>_<n>"`.
  `assertFreshness(ctx, path, newRef, liveRefs)` emits `newRef != prior`
  inequalities into the path condition for all prior live refs on this path.
  Before emitting, check `settings.maxFreshnessAssertions`: if the count of
  freshness assertions already on this path would exceed the cap (default 256;
  0 = unlimited), append `heFreshnessCapExceeded` (`sevHint`) to `path.errors`
  and skip the new inequality. The path remains sound — we do not assert false,
  we simply stop asserting distinctness (Z3 may allow aliasing beyond the cap,
  which is conservative/over-approximate, not unsound). The new
  `SymexSettings.maxFreshnessAssertions: int = 256` field follows the
  `maxFrontierSize = 0` unlimited convention.

- `tests/tsymex_phase15_r2_new.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r2_new.nim` passes both backends
- [ ] Additional test: two `new T` calls on disjoint forked paths do not
  emit cross-path freshness constraints — verified by asserting no
  `ref_T_0 != ref_T_1` constraint appears in the second branch's pc
- [ ] Cap test: SUT with 300 allocations on one path emits
  `heFreshnessCapExceeded` hint and does not crash (sound, no false UNSAT)
- [ ] Regression: `tsymex_phase15_r1_refsort.nim` still passes

---

### R3 — `p[]` read (deref select)

**What it does:** Completes the `isDeref` walker path for expression
contexts. `p[]` in a read position emits `select(path.heaps[typeId], p)`
where `path.heaps[typeId]` is the current binding on this path. The
result is a fully typed `SymVal` for the dereffed type `T`. Read does
not modify the heap. Per-path heap isolation is the critical property
to verify here: forked paths must carry independent heap bindings.

**RED test:** `tests/tsymex_phase15_r3_deref_read.nim`, test name
`"R3: read-after-write through same ref returns the written value"`.
Specifies: SUT
`proc f(p: ref int) = p[] = 99; if p[] == 99: symexTarget("hit")`;
`symexFind(f, tLabel("hit"))` returns `sxSat`. The deref-read on the
second line must see the `store`-updated heap from the write on the
first line.

**GREEN:**

- `src/proptest/smt/runtime.nim` — `of isDeref:` already stubs select
  from R1; confirm it correctly threads `path.heaps[typeId]` (per-path,
  not a global or WalkerStatics field). Write path (covered in R4) uses
  `store`; read path uses `select` against whatever `path.heaps[typeId]`
  currently holds on this path.

- `src/proptest/smt/types.nim` — add `isDerefWrite` IR statement kind
  for `p[] = v` (write path, implemented in R4; stub `discard` here).

- `tests/tsymex_phase15_r3_deref_read.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r3_deref_read.nim` passes both backends
- [ ] Per-path heap isolation verified: forked paths carry independent
  heap bindings (assert via a test that writes through `p` on one branch
  and reads on the other; the unwritten branch must not see the update)
- [ ] `seq[ref int]` element path: SUT `proc f(xs: seq[ref int]): bool`
  where `xs[0][] == 7` is correctly modeled — `svRef` array element lands
  and `select` on heap array produces sat witness (Breadth-MED-M4)
- [ ] Regressions R1a, R1, R1b, R2 pass

---

### R4 — `p[] = v` write (heap store)

**What it does:** Implements `isDerefWrite` walker semantics. `p[] = v`
is `path.heaps[typeId] := store(path.heaps[typeId], p, v)` — the walker
replaces the current per-path heap binding with the new functional-array
term. Subsequent reads on this path (via R3's `select`) see the update.
Aliased reads — reads through a ref `q` on the same path — see the
update conditionally: `select(store(heap_T, p, v), q)` evaluates to `v`
when Z3 decides `p == q` is satisfiable under the current path
constraint, and to `select(heap_T, q)` otherwise. Z3's array axioms
encode this automatically — the symex walker does not need to fork.

**RED test:** `tests/tsymex_phase15_r4_deref_write.nim`, test name
`"R4: write through p observable through aliased q; invisible through distinct r"`.
Specifies: SUT
`proc f(p, q, r: ref int) = p[] = 7; if q[] == 7 and r[] != 7: symexTarget("alias_and_distinct")`;
`symexFind(f, tLabel("alias_and_distinct"))` returns `sxSat` with a
witness where `p == q` and `p != r`.

Additional DoD test: write through `p`, then read through `p` (non-alias
case) returns the written value — verifies the basic read-your-own-write
property independently of aliasing.

**GREEN:**

- `src/proptest/smt/runtime.nim` — implement `of isDerefWrite:`.
  `path.heaps[typeId] := store(current_heap, p_sym, v_sym)` where
  `p_sym` is the `svRef`/`svPtr` SymVal's inner Z3 constant and
  `v_sym` is the RHS SymVal lifted to Z3 via the existing `toZ3Ast`
  helpers. Heap update is per-path (assigned into `path.heaps`).

- `tests/tsymex_phase15_r4_deref_write.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r4_deref_write.nim` passes both backends
- [ ] Alias-observable write confirmed by the sat witness: `p == q` in model
- [ ] Distinct-ref non-observable confirmed: no sat model with `r[]`
  seeing the write when `r != p` is asserted
- [ ] Non-alias read-your-own-write sub-test: write through `p`, read
  through `p` returns written value
- [ ] Regressions R1–R3 pass

---

### R5 — nil handling

**What it does:** `nil` is the per-ref-sort distinguished constant
`nilConst(Ref_T)` allocated once and cached in `WalkerStatics.nilConsts` (see R1).
`p == nil` is an observable Z3 equality on `Ref_T`-sorted terms, decided
by path-sat as usual. `p[]` when `p` is (or may be) nil is a defect:
the walker forks the deref path into a nil-path (where `p == nil` is
asserted) and a non-nil path (where `p != nil` is asserted). The nil
path emits `sxRaised(NilAccessDefect)`, composing with Cluster E's
exception verdict shape (E always lands before R — Cluster E is at
position 5, Cluster R is at position 8 in the cluster ordering). The
non-nil path continues normally. If the target is `tLabel(...)`, only
the non-nil path can satisfy it; the nil-path report is a separate
finding under the `tNilAccess` target kind (new in this cycle).

**RED test:** `tests/tsymex_phase15_r5_nil.nim`, test name
`"R5: deref of possibly-nil ref produces sxRaised on nil path and sxSat on non-nil path"`.
Specifies: SUT
`proc f(p: ref int) = if p[] == 1: symexTarget("hit")`;
when target is `tLabel("hit")`, `symexFind` returns `sxSat` (non-nil
path finds a witness); when target is `tNilAccess()`, `symexFind`
returns `sxSat` with a witness where `p == nil` (nil path found the
defect).

**GREEN:**

- `src/proptest/smt/types.nim` — new `SymexTargetKind.stkNilAccess`
  and constructor `tNilAccess()`. `sxRaised("NilAccessDefect")` is the
  Cluster E verdict shape; this cycle adds `"NilAccessDefect"` as a
  valid raise type string in the structured finding.

- `src/proptest/smt/runtime.nim` — `of isDeref:` (and `isDerefWrite:`)
  now forks: one path asserts `p != nil`, continues normally; one path
  asserts `p == nil`, emits the nil-access verdict using `sxRaised`.
  Fork is only emitted when `p` is a ref-sorted symbolic value — literal
  `nil` LHS is caught at parse time as a constant-false guard.

  **Nil-fork short-circuit (Depth-LOW-D4):** before emitting the nil
  sub-path, perform a literal scan of `path.pc` for a constraint of
  the form `p != nil` or `p == fresh_ref_N` (the latter is asserted by
  `isNew` and implies non-nil). If such a constraint is present, the nil
  path is UNSAT by construction and the fork is skipped entirely. The
  mechanism: iterate `path.pc` and check for Z3 `not(eq(p_sym, nil_T))`
  or `eq(p_sym, ref_T_N)` terms using a shallow AST pattern match
  (no Z3 check-sat call). This is a sound optimization — the nil path
  would return `sxUnsat` — and avoids redundant solver queries.

- `tests/tsymex_phase15_r5_nil.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r5_nil.nim` passes both backends
- [ ] `tNilAccess()` finding has `sxSat` with witness `p == nil`
- [ ] `tLabel("hit")` finding has `sxSat` with witness `p != nil` and
  `p[] == 1`
- [ ] Invariant 3 confirmed: no `sxUnknown` with empty `errors` on
  any nil-related path
- [ ] Nil-fork short-circuit: SUT where `p` was just allocated by `new T`
  (non-nil by construction) does not fork a nil sub-path; verified by
  asserting the `tNilAccess()` target returns `sxUnsat` (not `sxSat`)
- [ ] Regressions R1a, R1, R1b, R2, R3, R4 pass

---

### R6 — `ref object` field access

**What it does:** `p.field` (field read through a ref to an object type)
is `select(path.heaps[T], p).field` — a select producing a record `SymVal`
followed by a positional field projection. Field write `p.field = v`
is a heap store of a modified record:
`path.heaps[T] := store(path.heaps[T], p, modifyField(select(path.heaps[T], p), field, v))`,
where `modifyField` reconstructs the `svTuple` SymVal with the
designated field replaced. The walker reuses the existing `svTuple`
field-projection and field-update machinery from Phase 4; the only new
logic is the heap select+store envelope.

**RED test:** `tests/tsymex_phase15_r6_refobj.nim`, test name
`"R6: write field through ref, aliased read observes update"`.
Specifies: SUT
```nim
type Point = object
  x, y: int
proc f(p, q: ref Point) =
  p.x = 42
  if q.x == 42: symexTarget("alias_field")
```
`symexFind(f, tLabel("alias_field"))` returns `sxSat` with witness
`p == q` (aliased read observes the field write).

**GREEN:**

- `src/proptest/smt/dsl_parser.nim` — extend `parseExpr` to recognise
  `nnkDotExpr` on a ref-typed receiver and emit a two-step IR:
  `isDeref` (select the record) then `iekField` on the result.
  Field-write through ref: recognise the `lhs` of an assignment
  statement where `lhs` is `nnkDotExpr(nnkDerefExpr(p), field)` and
  emit `isDerefWrite` with a field-modified RHS expression.

- `src/proptest/smt/runtime.nim` — implement field-modify helper:
  given an `svTuple` SymVal and a field index, return a new `svTuple`
  with that field replaced. Wire into `of isDerefWrite:` when the
  write target is a record-typed heap entry.

- `src/proptest/smt/runtime.nim` — inherited field resolution
  (Depth-H8): when `nnkDotExpr` resolves to a field whose declaring type
  is different from the dereffed type, resolve to flat layout (base fields
  first, then derived). Detect via Nim's `getTypeImpl` on the field's
  owner symbol vs the dereffed type. Index into `svTuple` uses the flat
  offset, not the derived-type-local offset.

- `tests/tsymex_phase15_r6_refobj.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r6_refobj.nim` passes both backends
- [ ] Aliased field write observable through a sat witness `p == q`
- [ ] Nil fork still fires on field access through possibly-nil
  ref-to-object (R5 composition)
- [ ] Inherited field test (Depth-H8): SUT `proc f(p: ref Child): bool`
  accessing `p.x` (inherited from `Base`) and `p.y` (own field); both
  produce correct witnesses. Type: `type Base = object; x: int` +
  `type Child = object of Base; y: int`.
- [ ] Variant-fielded ref object test (Feas-MED-4 / M17): SUT containing
  `ref T` where `T` has variant fields produces `heRefVariantUnsupported`
  (`sevError`) classified error, not a `Defect` on `svTuple` dispatch.
  Negative DoD: `type Node = ref object; tag: bool; case tag of true: (val: int) | false: (next: Node)`
  → `sxUnknown` with `heRefVariantUnsupported` in `errors`.
- [ ] Regressions R1a, R1, R1b, R2, R3, R4, R5 pass

---

### R7 — ref equality and assignment aliasing

**What it does:** `let q = p` binds `q` to the same `Ref_T`-sorted Z3
constant as `p` — they are structurally the same SymVal, so `p == q`
evaluates to Z3 `true` trivially (the Z3 equality of a term with itself
is a tautology, decided without a `check-sat` call). `q == r` for an
unrelated ref `r` is path-sat-decided as usual. This cycle verifies
that alias chains of arbitrary depth — `p == q == r` established by two
sequential let-bindings — remain consistent under the Z3 model: the
walker correctly propagates the identity, and transitivity requires no
extra axioms.

Additional test: `let q = p; q = r` (assignment of a new ref value to `q`)
breaks the alias chain — `q` is no longer equal to `p` after the
re-assignment, and a write through `q` should not be observed through `p`.

**RED test:** `tests/tsymex_phase15_r7_alias_chain.nim`, test name
`"R7: alias chain p == q == r consistent under sat"`.
Specifies: SUT
```nim
proc f(p: ref int) =
  let q = p
  let r = q
  r[] = 5
  if p[] == 5: symexTarget("transitive")
```
`symexFind(f, tLabel("transitive"))` returns `sxSat`: the write
through `r` is visible through `p` because all three names hold the
same Z3 constant.

**GREEN:**

- `src/proptest/smt/runtime.nim` — `of isLet:` for `svRef`/`svPtr`
  typed RHS: bind the LHS name to the same Z3 constant (copy the
  `SymVal` struct — it is a value type, so the copy shares the
  underlying `Z3AnyAst` ref-count handle). No new heap machinery is
  needed; Z3's array theory axioms handle the rest.

- `tests/tsymex_phase15_r7_alias_chain.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r7_alias_chain.nim` passes both backends
- [ ] Transitivity holds: write through `r` visible through `p` in sat
  witness
- [ ] Alias-break sub-test: `let q = p; q = r` — write through `q` NOT
  observable through `p` after re-assignment
- [ ] Verify the reverse: a SUT that writes through `p` after setting
  `r[] = 5` and then tests `r[]` sees the overwrite (heap-threading
  is ordered correctly)
- [ ] Regressions R1–R6 pass

---

### R8 — `ptr T` family + pointer arithmetic

**What it does:** `ptr T` uses identical logical-heap machinery as
`ref T` — same sort-per-pointee-type model, same `select`/`store`
pattern, same per-path monotone counter for fresh addresses. The
distinction is semantic rather than structural: Nim's `ref T` is
GC-managed and nil is the only invalid value; `ptr T` is unmanaged
and may legally be non-nil-invalid in the Nim spec (dangling,
arithmetic-derived, etc.).

**Pointer arithmetic (`inc(p)` / `dec(p)`) is NOT modeled.** These are
Nim magic calls detected at parse time via proc-name match (`inc` or
`dec`) with a `ptr T` receiver type. The walker emits `isUnsupported`
with a classified `SymexErrorInfo{kind: hePtrArith, msg: "pointer arithmetic (inc/dec) not modeled"}` halt. This is invariant-3-compliant: the error kind is
`hePtrArith` enum variant (not the generic `isUnsupported` reason string).

`ptr T` params are tagged with `ptrFamily: bool = true` in their
`svPtr` SymVal, which is propagated into the finding's `SymexErrorInfo`
so consumers can distinguish managed-ref witnesses from unmanaged-ptr
witnesses.

**Severity split (Des-CRIT-D2 / H16):** `hePtrArith` is a halting error
(`sevError`) — the walker cannot model the resulting address. `hePtrFamily`
is a `sevHint` annotation on a successfully-modeled `ptr T` witness —
it does NOT halt the walker. Both use `SymexErrorKind` enum variants, not
raw string literals.

**RED tests:**

1. `tests/tsymex_phase15_r8_ptr.nim`, test name
   `"R8: ptr T uses same heap model as ref T; finding tagged ptrFamily"`.
   Specifies: SUT `proc f(p: ptr int) = if p[] == 7: symexTarget("hit")`;
   `symexFind(f, tLabel("hit"))` returns `sxSat`; the `SymexFinding` has
   `errors` containing
   `SymexErrorInfo{kind: hePtrFamily, msg: "witness involves unmanaged ptr"}`
   (severity `sevHint`). A parallel ref-typed SUT produces `sxSat` with
   no such entry.

2. `"R8: SUT calling inc(p) on ptr T produces hePtrArith classified error"`.
   Specifies: SUT `proc f(p: ptr int) = inc(p)`;
   `symexFind(f, tLabel("any"))` returns `sxUnknown` with
   `SymexErrorInfo{kind: hePtrArith}` in `errors`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — `svPtr` SymVal variant already
  introduced in R1 as a stub distinct from `svRef`. This cycle wires
  `svPtr` through the full deref/write/alias machinery identically to
  `svRef`. At the finding-recording site, when any path witness contains
  an `svPtr`-typed param or local, append `SymexErrorInfo{kind: hePtrFamily,
  msg: "witness involves unmanaged ptr", severity: sevHint}` to the
  finding's `errors` field. `of isUnsupported:` extended to recognise
  `inc`/`dec` on `ptr T` receiver and emit `kind: hePtrArith`.

- `src/proptest/smt/dsl_parser.nim` — in `parseStmt`, recognise `nnkCall`
  to `inc`/`dec` where the first argument is `ptr T`-typed; emit
  `mkUnsupported("hePtrArith")` (or a specialised `isPointerArith` IR node
  if added in types.nim).

- `tests/tsymex_phase15_r8_ptr.nim` — new test file covering both sub-tests.

**DoD:**
- [ ] `tsymex_phase15_r8_ptr.nim` passes both backends
- [ ] `ptrFamily` hint present in `SymexFinding.errors` for ptr-typed
  witnesses; absent for ref-typed witnesses
- [ ] `inc(p)` on `ptr T` → `sxUnknown` with `errors[0].kind == hePtrArith`
- [ ] Both `ref int` and `ptr int` SUTs reach `sxSat` with correct
  field witnesses
- [ ] Regressions R1a, R1, R1b, R2, R3, R4, R5, R6, R7 pass

---

### R8b — `var ref T` parameter handling (Breadth-H4 / H25)

**What it does:** Handles the case where a SUT callee receives a `var ref T`
parameter and rebinds it (e.g. `p = newRef()`). The rebinding must be
written back to the caller's environment after the callee returns — the
caller's continuation sees the new binding. This composes the `isVar`
write-back mechanism (from the base walker) with the heap merge from R1b.

**Fallback:** if full rebinding support proves infeasible within this
cycle (e.g. the `isVar` + heap path interaction is too complex), emit
`heUnsupportedVarRef` (`sevError`) classified error for any `var ref T`
parameter, producing `sxUnknown`. This is invariant-3-compliant and
preferable to a silent wrong answer.

**RED test:** `tests/tsymex_phase15_r8b_varref.nim`, test name
`"R8b: callee rebinding var ref T visible in caller continuation"`.
Specifies: SUT
```nim
proc rebind(p: var ref int) = p = new int; p[] = 99
proc f() =
  var q = new int
  q[] = 0
  rebind(q)
  if q[] == 99: symexTarget("rebound")
```
`symexFind(f, tLabel("rebound"))` returns `sxSat`. Without R8b, the
rebinding is invisible to the caller and the test returns `sxUnsat` or
`sxUnknown`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — at `isCall`/`isGenericCall` walker
  arm for callees with `var ref T` parameters: after callee walk
  completes, write back the callee's final binding for each `var ref T`
  param into the caller's env (parallel to the existing `isVar` int/bool
  write-back). Heap merge follows R1b's `max(caller, callee)` rule for
  `allocCounters`. If the `isVar` + ref path is not implementable in this
  cycle, emit `heUnsupportedVarRef` (`sevError`) instead.

- `tests/tsymex_phase15_r8b_varref.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r8b_varref.nim` passes both backends (rebound case
  → `sxSat`; OR `sxUnknown` with `heUnsupportedVarRef` if fallback path taken)
- [ ] Fallback path is classified (`heUnsupportedVarRef`, `sevError`),
  not a silent `sxUnknown` with empty `errors`
- [ ] Regressions R1a, R1, R1b, R2, R3, R4, R5, R6, R7, R8 pass

---

### R9 — recursive ref structures (linked list, tree)

**What it does:** `path.heapDepth` (inherited from Cluster H's H1 cycle)
bounds traversal of self-referential heap structures. A SUT that walks a
singly-linked list by following `node.next` pointers will cause the
walker to recursively deref `node`, then `node.next`, then
`node.next.next`, indefinitely. Each `isDeref` or `isDerefWrite`
increments `path.heapDepth`; when the counter exceeds
`settings.maxHeapDepth` (checked with `if settings.maxHeapDepth > 0 and
path.heapDepth >= settings.maxHeapDepth`), the walker halts the path
with `sxUnknown` and a classified
`SymexErrorInfo{kind: heDepthExhausted, msg: "heap depth budget of N exceeded"}`.
The halt is per-path — other concurrently active paths with shallower
depth continue normally.

**`maxHeapDepth = 0` semantics (Des-LOW-D1 / M9):** `0` is the unlimited
sentinel, consistent with `maxFrontierSize = 0`. When `maxHeapDepth = 0`,
fall back to `settings.maxCallDepth`; if `maxCallDepth` is also 0, apply
a hard cap of 256. The guard `if settings.maxHeapDepth > 0 and ...` is
the sole check site — there is no separate unlimited-mode code path.

**RED test:** `tests/tsymex_phase15_r9_recursive.nim`, test name
`"R9: linked-list SUT with unknown depth halts cleanly at budget"`.
Specifies: linked-list type
```nim
type Node = ref object
  val: int
  next: Node
```
SUT walks `n.next.next.next` to depth 4 and then tests a field.
With `maxHeapDepth = 3`, `symexFind` returns `sxUnknown` with
`SymexErrorInfo{kind: heDepthExhausted}`; with `maxHeapDepth = 8`
(default), `symexFind` returns `sxSat`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — `of isDeref:` and `of isDerefWrite:`
  check `if settings.maxHeapDepth > 0 and path.heapDepth >= settings.maxHeapDepth`
  before performing `select`/`store`. For `maxHeapDepth = 0`, resolve the
  effective limit as `maxCallDepth` if > 0, else 256. On budget exhaustion,
  set `path.uncertain = true` and record
  `SymexErrorInfo{kind: heDepthExhausted, ...}` into `path.errors`,
  then return without binding the let-name (path is dead). Otherwise,
  increment `path.heapDepth` and proceed.

- `tests/tsymex_phase15_r9_recursive.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r9_recursive.nim` passes both backends
- [ ] `maxHeapDepth = 3` → `sxUnknown(heDepthExhausted)`; `maxHeapDepth = 8`
  → `sxSat`
- [ ] `sxUnknown` result has non-empty `errors` with `kind == heDepthExhausted`
  (invariant 3)
- [ ] `maxHeapDepth = 0` with 20-deref chain → `sxSat` (falls back to
  `maxCallDepth` or hard cap 256; no infinite loop)
- [ ] Regressions R1a, R1, R1b, R2, R3, R4, R5, R6, R7, R8, R8b pass

---

### R10 — `maxHeapDepth` setting

**What it does:** Confirms the `maxHeapDepth` setting is fully wired
into the cache key (so that a solve result under depth 3 does not
incorrectly serve a cache lookup under depth 8), documented in
`determinism.md`, and exercised with a two-budget test confirming the
monotone exhaustion boundary — a SUT that hits `sxSat` under depth N
must also hit `sxSat` under any depth M > N (the UNSAT-monotonicity
analogue for heap depth). Also confirms `maxHeapDepth = 0` means
unlimited (consistent with `maxFrontierSize = 0` convention).

**RED test:** `tests/tsymex_phase15_r10_budget.nim`, test name
`"R10: same SUT reaches sxSat at depth 2 and sxUnknown at depth 1"`.
Specifies: SUT that performs exactly 2 levels of deref (e.g.
`node.next.val`). `symexFind` with `maxHeapDepth = 2` returns `sxSat`;
with `maxHeapDepth = 1` returns `sxUnknown(heDepthExhausted)`.
Additional sub-test: `maxHeapDepth = 0` returns `sxSat` (unlimited).

**GREEN:**

- `src/proptest/smt/canonicalize.nim` — add `maxHeapDepth` to the
  serialised settings block in the cache key (parallel to the existing
  `maxFrontierSize` and `maxCallDepth` entries). Document that
  `maxHeapDepth = 0` serialises as `"heapDepth=unlimited"` to keep
  the key human-readable.

- `docs/symex/determinism.md` — new subsection "Heap depth budget"
  under the walker-settings section: default value (8), unlimited
  sentinel (0), cache-key participation, monotone exhaustion property.

- `tests/tsymex_phase15_r10_budget.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r10_budget.nim` passes both backends (depth 1 →
  `sxUnknown`; depth 2 → `sxSat`; depth 0 → `sxSat`)
- [ ] Cache key includes `maxHeapDepth`; a cached entry under depth 1
  is NOT served for a depth-2 query (verify by inspecting the
  serialised key string in the test)
- [ ] `determinism.md` "Heap depth budget" subsection committed
- [ ] Regressions R1–R9 pass

---

### R11 — `cast[ptr T](addr x)` (unsafe cast → classified unknown)

**What it does:** `cast[ptr T](addr x)` and analogous unsafe
address-materialisation expressions (`addr`, `unsafeAddr`, `cast` to
pointer types) lie outside the logical-heap model. The walker cannot
track the provenance of an address derived by casting an arbitrary
integer or by taking the address of a stack variable — the result may
alias with any logical-heap ref, with no ref, or with a dangling
address. The correct response under invariant 3 is a classified halt:
`sxUnknown` with `SymexErrorInfo{kind: heUnsafeCast, msg: "cast to pointer type outside logical heap model"}`.
The halt is emitted when the parser encounters any of the following
patterns in the SUT body: `cast[ptr T](expr)`, `addr expr` used in a
pointer context, `unsafeAddr expr`. The `isUnsupported` IR node already
handles unrecognised AST; this cycle adds an explicit `isUnsafeCast` IR
statement kind so the error carries the `heUnsafeCast` kind string
rather than the generic `isUnsupported` reason.

**RED test:** `tests/tsymex_phase15_r11_unsafecast.nim`, test name
`"R11: SUT using cast to ptr produces sxUnknown with heUnsafeCast"`.
Specifies: SUT
`proc f(x: int) = let p = cast[ptr int](addr x); if p[] == 1: symexTarget("hit")`;
`symexFind(f, tLabel("hit"))` returns `sxUnknown` with
`SymexErrorInfo{kind: heUnsafeCast}` in `errors`; the error kind is
exactly `heUnsafeCast`, not a generic `isUnsupported` reason.

**GREEN:**

- `src/proptest/smt/types.nim` — new `IRStmtKind.isUnsafeCast` with
  field `ucReason: string` (e.g. `"cast[ptr T]"`, `"addr"`,
  `"unsafeAddr"`). New constructor `mkUnsafeCast(reason: string)`.
  Render as `"unsafeCast(" & s.ucReason & ")"`.

- `src/proptest/smt/dsl_parser.nim` — in `parseExpr` / `parseStmt`,
  recognise `nnkCast` to pointer target types, `nnkAddr`, `nnkHiddenAddr`,
  `nnkDerefExpr` on a cast result. Emit `mkUnsafeCast(reason)` and push
  into the statement preamble. The outer expression position receives
  a fresh `mkVar` placeholder (consistent with A-normalisation pattern).

- `src/proptest/smt/runtime.nim` — `of isUnsafeCast:` sets
  `path.uncertain = true` and appends
  `SymexErrorInfo{kind: heUnsafeCast, msg: "cast to pointer type outside logical heap model; " & s.ucReason, severity: sevError}`
  to `path.errors`. Does NOT bind any let-name (the unsafely-derived
  pointer value is unavailable to the walker). All subsequent
  statements on this path become unreachable (path is dead).

- `tests/tsymex_phase15_r11_unsafecast.nim` — new test file.

**DoD:**
- [ ] `tsymex_phase15_r11_unsafecast.nim` passes both backends
- [ ] Result is `sxUnknown`, not `sxSat`; `errors[0].kind == heUnsafeCast`
- [ ] `errors` is non-empty (invariant 3 — no silent `sxUnknown`)
- [ ] `tLabel("hit")` not reached on any path
- [ ] Regressions R1–R10 pass

---

### R11b — cross-cluster regression sweep

**What it does:** Two parts:

1. **Authors `docs/symex/witness-format-v3.md`** (Feas-MED-6 / M20, H21).
   This document must be committed before R12's GREEN begins. It specifies
   the heap-snapshot witness schema at ADR depth:
   - Heap-snapshot schema (consistent with Cluster H preamble invariants):
     `heapSnapshot: seq[{name, sort, value, pointsTo}]`.
   - Alias-group dedup: lexicographically-first param name holds `pointsTo`;
     other params aliasing the same Z3 constant get `aliasRef: "<primary>"`.
   - Nil shape: `{name, sort, value: "nil", pointsTo: null}`.
   - Recursive `pointsTo` for `ref object` bounded by `maxHeapDepth`:
     nested `ref` fields recursively expand their `pointsTo` up to
     `maxHeapDepth` hops.
   - Wire format: JSON-shaped, consistent with rest of witness rendering.

2. **Cross-cluster regression sweep.** Re-runs a curated subset of tests
   from every prior cluster (Z, L, F, S, E, G, C) under the
   heap-state-threaded walker to verify that the invasive
   `heaps`/`heapDepth`/`allocCounters` fields added to `Path` and the
   `refSorts`/`nilConsts` fields added to `WalkerStatics` did not silently
   break any non-heap SUT. **No format changes. No version bumps.** The
   sole purpose is heap-threading bug detection across the existing test
   corpus.

The curated regression subset is drawn from:
- Z cluster: `tsymex_phase15_z2_regression.nim`
- L cluster: `tsymex_phase15_l3_regression.nim`
- E cluster: any `tNilAccess`-related test (composing E + R5)
- G cluster: any generic SUT instantiated with a ref-typed type parameter
- C cluster: any closure capturing a ref-typed variable
- Existing Phase 14 regression driver (`tests/tsymex_phase14_*.nim` canary)

Regression DoD (existing tests must pass unmodified): if any prior test
returns `sxUnknown` where it previously returned `sxSat`/`sxUnsat`, the
walker has a heap-threading regression.

**RED test:** `tests/tsymex_phase15_r11b_regression.nim`, test name
`"R11b regression sweep: prior-cluster SUTs correct under heap-threaded walker"`.
Specifies: the test file compiles and runs the curated subset inline
(or via `testament` delegation) and asserts every result matches its
Phase-14-era expected outcome. If any prior test now returns `sxUnknown`
where it previously returned `sxSat`/`sxUnsat`, the walker has a
heap-threading regression.

**GREEN:**

- No runtime or types changes. Fix any regressions found.

- `tests/tsymex_phase15_r11b_regression.nim` — new test file (RED → GREEN).

**DoD:**
- [ ] `docs/symex/witness-format-v3.md` committed with heap-snapshot schema,
  alias-group dedup, nil shape, recursive `pointsTo`, and wire format
  sections (H21 / Feas-MED-6)
- [ ] `tsymex_phase15_r11b_regression.nim` passes both backends with no
  regressions from prior clusters
- [ ] No version bump of any kind (walker version stays `"9"`, rendering
  version stays `"2"`)
- [ ] All R1a, R1, R1b, R2–R11 test files pass as part of this sweep

---

### R12 — walker version bump + rendering version bump + heap-snapshot witness format

**What it does:** Three coupled changes that land atomically; no
regression-fix work happens in this cycle (that was R11b).

1. **Walker version bump `"9"→"10"`.** Per v2 invariant 1, Cluster R's
   walker version increment lands here. The bump edits
   `src/proptest/smt/canonicalize.nim` (single source of truth per M12).

2. **Rendering version bump `"2"→"3"`.** The heap-snapshot section is new
   information absent from the current on-disk witness format. Any `sxSat`
   witness for a SUT with ref/ptr-typed params now includes a
   `heapSnapshot` field. Witnesses for non-heap SUTs are unchanged —
   the `heapSnapshot` key is absent (not `null`, omitted) to preserve
   backward compatibility. This bump also edits `src/proptest/smt/canonicalize.nim`
   (the single source of truth for both version constants per M12).

3. **Heap-snapshot witness format extension.** The witness format spec
   lives in `docs/symex/witness-format-v3.md` (authored in R11b before
   R12 begins). The spec covers:
   - Aliased refs: lexicographically-first param name holds `pointsTo`;
     other params aliasing the same Z3 constant get `aliasRef: "<primary>"`.
   - Nil refs: `{value: "nil", pointsTo: null}`.
   - Per-param schema: `{name, sort, value, pointsTo, aliasRef?}`.

**RED tests:** `tests/tsymex_phase15_r12_bumps.nim` — three independent
sub-tests (Feas-MED-6 / M19 sub-test independence):

- **Sub-test 1** (pure constants): `canonicalize.walkerVersion == "10"` and
  `canonicalize.renderingVersion == "3"`. Does NOT depend on witness
  serialisation; passes even if sub-test 2 fails.
- **Sub-test 2** (heap witness): a SUT `proc f(p: ref int): bool` produces a
  sat witness with a populated `heapSnapshot` field. Isolated from the
  version-bump check so a serialisation regression does not obscure the
  pure-bump result.
- **Sub-test 3** (backward compat): a SUT `proc f(x: int): bool` produces a
  sat witness WITHOUT a `heapSnapshot` field (key absent, not null).

**GREEN:**

- `src/proptest/smt/canonicalize.nim` — bump both version constants:
  `walkerVersion = "10"` and `renderingVersion = "3"`. These are the
  single source-of-truth constants (per M12; not in `runtime.nim`).

- `src/proptest/symex.nim` — extend the on-disk witness serialiser to
  emit a `heapSnapshot` object when the witness contains at least one
  `svRef`/`svPtr` param: for each such param, record
  `{name: "p", sort: "Ref_int", value: "ref_int_0",
  pointsTo: <extracted T witness>}` from the Z3 model; aliased params
  get `aliasRef: "<primary>"` per `witness-format-v3.md` spec.
  For witnesses with no ref/ptr params, the `heapSnapshot` key is absent.

- `docs/symex/witness-format-v3.md` — new file authored before R12
  GREEN begins. Specifies the `heapSnapshot` schema as described above.

- `docs/symex/determinism.md` — new "Walker and rendering version
  history" entry:
  - `"9" → "10"` (walker): Phase 15 Cluster R — ref/ptr/logical heap,
    nil-access, depth-bounded recursive structures, unsafe-cast classified
    error, ptr-family tagging, pointer-arithmetic classified error,
    heap-snapshot witness format.
  - `"2" → "3"` (rendering): heap-snapshot field added to sat witnesses
    for ref/ptr-typed SUT params.

- `tests/tsymex_phase15_r12_bumps.nim` — new test file (RED → GREEN).

**DoD:**
- [ ] `docs/symex/witness-format-v3.md` committed in R11b before this
  cycle's GREEN begins
- [ ] `tsymex_phase15_r12_bumps.nim` sub-test 1 passes: `canonicalize.walkerVersion == "10"`
  AND `canonicalize.renderingVersion == "3"` (pure constants in `canonicalize.nim`)
- [ ] Sub-test 2 passes: `ref int` SUT witness has populated `heapSnapshot` field
- [ ] Sub-test 3 passes: `int` SUT witness lacks `heapSnapshot` field (backward compat)
- [ ] Sub-test independence: sub-test 1 passes even if sub-test 2 fails
- [ ] `determinism.md` version-history entry committed
- [ ] `docs/symex/SYMEX_PLAN.md` Cluster R row marked SHIPPED with
  commit SHA

---

### R13 — closures capturing `ref T`

**What it does:** Two composition sub-tracks:

**Sub-track A: closures capturing `ref T`.** Lifts the C5
`ceUnsupportedCapture` classification for ref-typed captures. Once the
R-cluster heap machinery exists, closures can properly capture `svRef`
(or `svPtr`) values in their `envRecord`. This cycle modifies the
C-cluster `itLambda` walker arm (added in C2a) to accept `svRef`-typed
free variables; their `envRecord` entry is encoded as an `svRef` SymVal
field holding the captured ref's Z3 constant (the same constant the
outer scope uses). Calling the closure dereferences the captured ref
through `path.heaps` exactly as any other `svRef` deref does — the
heap state is threaded in via R1b's call-frame mechanism.

`extractFromSymVal` for `svClosure` is extended to follow captured refs
through the heap when extracting witnesses: for each captured `svRef`
field in the `envRecord`, extract the `pointsTo` value from the Z3 model
and include it in the `heapSnapshot` output.

**Sub-track B: `ptr T` + `try`/`finally` composition (Feas-H4 fold from E7).**
This test was moved out of E7 because `isDeref` does not exist until R1.
SUT: `proc f(p: ptr int) = try: p[] = 7; finally: if p[] == 7: raise newException(ValueError, "written")`.
Expected: `sxRaised(ValueError)` with witness `p[] = 7`. Verifies that
heap state threads correctly through `try`/`finally` exit continuations
(E5 mechanism) when the SUT param is `ptr T`-typed.

**RED tests:**

- `tests/tsymex_phase15_r13_closure_ref.nim`, test name
  `"R13-A: closure capturing ref int local observes write through heap"`.
- `tests/tsymex_phase15_r13_ptr_finally.nim`, test name
  `"R13-B: ptr T + try/finally composition produces sxRaised(ValueError) with witness p[]==7"`.
Specifies: SUT
```nim
proc f() =
  var x = new int
  x[] = 42
  let capture = proc() = if x[] == 42: symexTarget("hit")
  capture()
```
`symexFind(f, tLabel("hit"))` returns `sxSat`. Without R13, the closure
construction emits `ceUnsupportedCapture` and the test returns
`sxUnknown`.

**GREEN:**

- `src/proptest/smt/runtime.nim` — `itLambda` arm: accept `svRef`/`svPtr`
  free variables when constructing `envRecord`. Each captured ref's Z3
  constant is stored as an `svRef` SymVal field in the env record.
  `iekClosureCall` arm: R1b's heap-threading mechanism carries
  `path.heaps` into the closure body — no additional change needed beyond
  accepting `svRef` in the env.

- `src/proptest/smt/runtime.nim` — `extractFromSymVal` for `svClosure`:
  iterate captured fields; for `svRef`-typed captures, extract the
  `pointsTo` witness value from the Z3 model and include in the
  `heapSnapshot`.

- `tests/tsymex_phase15_r13_closure_ref.nim` — new test file (sub-track A).

- `tests/tsymex_phase15_r13_ptr_finally.nim` — new test file (sub-track B).
  No new walker code needed beyond R8 (`ptr T` heap model) + E5
  (`try`/`finally` exit continuations); this test validates the composition.

**DoD:**
- [ ] `tsymex_phase15_r13_closure_ref.nim` passes both backends (sub-track A)
- [ ] `ceUnsupportedCapture` is no longer emitted for `ref T`-capturing
  closures
- [ ] Sat witness includes the correct heap observation (`x[] == 42`)
- [ ] `tsymex_phase15_r13_ptr_finally.nim` passes both backends (sub-track B)
- [ ] Sub-track B: `proc f(p: ptr int) = try: p[] = 7; finally: if p[] == 7: raise ...`
  → `sxRaised(ValueError)` with witness `p[] = 7`
- [ ] Regressions R1a, R1, R1b, R2–R12 pass; C-cluster closure tests pass

---

## Open questions for round 2

The seven v1 open questions all resolved into clear-best
answers during the round-1 bake-in. Round 2 starts with a
clean slate; nothing currently open. Questions surfaced by
round 2 land here.

### Closed during round 1

| # | Original (v1) | Resolution |
|---|---------------|------------|
| 1 (L) | Template/macro re-check per instantiation? | **Trust Nim semchecker.** Verified by L1's boundary test that asserts walker never sees `nnkTemplateDef`/`nnkMacroDef`. |
| 2 (F) | Int→float rounding mode? | **rmRNE for int→float; rmRTZ for float→int.** Matches Nim's observable behavior under `-d:release`. |
| 3 (S) | `cstring` interop scope? | **Deferred to Phase 16.** `cstring` is FFI; FFI is out of scope. |
| 4 (E) | Defects as `sxRaised` or `sxUnreached`? | **`sxRaised(typeId, isDefect=true)`.** Silent-pass risk under `sxUnreached` is unsound for a correctness oracle (`complete-lib-not-consumer` directive). |
| 5 (G) | `maxInstantiationsPerProc` value? | **64.** Matches `maxFrontierSize`/`maxInlineSeqLen`/`maxClosureInlineCount` family default. |
| 6 (C) | Closure equality structural vs nominal? | **Nominal-for-site + structural-for-env.** Matches Nim runtime proc-value semantics; resolves the v1 description ambiguity that made this look like a fork when the C2 design already locked it in. |
| 7 (R) | `cast[ptr T]` modeling? | **`sxUnknown(heUnsafeCast)`.** Safe-cast in PBT-tested code is rare; modeling cost-benefit favors deferral to Phase 16. |

## Backlog (post-Phase-15 / Phase 16+)

- GC type erasure / vtable dispatch on inheritance hierarchies
- Channels, locks, threads
- FFI / `importc` / `emit`
- `cstring` interop deepening
- Style insensitivity / Unicode identifier folding
- `{.async.}` continuation expansion (if not incidentally
  covered by Cluster C)
- Heap-depth widening (vs. the bounded budget in Cluster R)
