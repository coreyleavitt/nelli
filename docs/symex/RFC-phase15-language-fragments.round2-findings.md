# Phase 15 RFC — Round 2 findings (consolidated)

Four lenses (Depth/Breadth/Design/Feasibility), 85 raw findings deduped to ~67. Round 1's bake-in is assumed live; nothing below repeats round-1 items.

Severity scheme: CRIT = will break compile, soundness, or RED-GREEN discipline; HIGH = significant correctness/feasibility risk; MED = polish/observability/perf; LOW = minor / doc.

## CRIT

| # | Source | Cluster | Issue | Fix |
|---|--------|---------|-------|-----|
| C1 | Feas-1 | E→R | E3/E5/E7 read `path.heaps`/`heapDepth`/`allocCounters` but R0 lands 3 clusters later. RED-GREEN broken (code won't compile at E-time). | **Pull R0 forward** to before E1 (R0 has zero dependency per its own spec). Cluster table updated; cross-cluster invariant 5 updated. |
| C2 | Feas-2, Des-D2 | All | `SymexErrorKind` enum migration has no cycle home. F1/S1/E1 RED tests reference enum constants that don't yet exist. R8/R9/R11 use raw `"he…"` strings despite the enum direction. | **Add Z0+ cycle "Z0-Enum"**: migrate `SymexErrorInfo.kind: string → SymexErrorKind`, populate enum with all Phase-14 kinds + Phase-15 kinds (`fe*/se*/ee*/ge*/ce*/he*`). All RED tests reference enum variants. Replace string lits in R8/R9/R11 GREEN with enum variants. |
| C3 | Depth-1 | E | Multi-exception SUT cache: serializer drops second `sxRaised` finding, deserializer can't reload set. | E2a: serializer iterates `found: seq[RawResult]`, writes every `sxRaised` under `":raised:" & typeId`. `loadAll(sutKeyPrefix)` reconstructs the seq. DoD: SUT with two distinct raise paths round-trips both. |
| C4 | Depth-2 | C | Closure body descent may produce multiple sub-paths with different `returnVal`; axiom only binds one. | C2b GREEN: collect `seq[WalkResult]` from body descent; for each sub-path `(pc_i, v_i)` assert `implies(path.pc and pc_i, funcSym(env, args) == v_i)`. Main axiom uses Z3 `ite`-merge of sub-path results. DoD: 2-branch lambda body produces both axiom arms. |
| C5 | Depth-3 | R | `allocCounters` write-back from callee uses replacement; must be `max(caller, callee)` to preserve freshness on subsequent caller allocations. | R1b: `path.allocCounters[T] = max(...)`. DoD test: caller allocs after callee call ⇒ ref distinct from callee's. |
| C6 | Des-D1 | All | `EffectCtx` round 1 extraction still mixes per-walker (`refSorts`, `closureSyms`, `userExnHierarchy`) and per-call-frame (`handlerStack`, `inFlightExn`, `closureInlineCount`) lifetimes. | Split into `WalkerStatics` (per-walker, immutable post-parse) + `CallFrameCtx` (push/pop per call descent). `WalkCtx.statics` + `WalkCtx.frame`. Updates E1, C2a, R1 GREEN. |
| C7 | Breadth-C1 | G, R | `emitTyAndReader` / `primTyAndReader` in `symex.nim` has no `itDistinct`/`itRef`/`itPtr` case — silent empty reader for `distinct`/`ref` SUT params. | G4 GREEN list adds `symex.nim` edit; R1 GREEN list adds `symex.nim` edit. DoD items added. |
| C8 | Breadth-C2, Des-D7 | E | `svUninterpRef` used in E8 but never added to `SVKind`. Every `case sv.kind` site breaks. | E1 (or pre-E8 sub-cycle) adds `svUninterpRef(sortName, typeTag)` to `SVKind` with stubs in `walk`/`extractFromSymVal`/`allocateSym`/`typeOf`/`symValHash`. |

## HIGH

| # | Source | Cluster | Issue | Fix |
|---|--------|---------|-------|-----|
| H1 | Depth-1 | F/R | NaN through `seq[float]`/`array[N, float]` extraction path uses `evalFloat64Opt` on `Z3_mk_select` AST — untested; may not return NaN via `modelCompletion`. | F9 DoD adds array-NaN extraction test; F7 GREEN forces `model.eval(expr, model_completion=true)` before `fpBitsToUint64`. |
| H2 | Depth-2 | S | `split(s, "")` ⇒ Z3 `contains(parts[i], "")` always true ⇒ UNSAT for valid Nim semantics. | S5 GREEN: detect `sep == ""` (numeral zero-length check); skip the `contains` constraint; assert `forall i. len(parts[i]) == 1 and seqLen(parts) == len(s)`. |
| H3 | Depth-3, MED-D1 | S/E | `parseInt(non-digit)` returns `mkInt(-1)` ⇒ false SAT vs Nim runtime `ValueError`; negative strings also broken. | S10 forks: digits-path uses `Z3String.toInt(s) ≥ 0`; raises-path asserts `< 0` ⇒ `sxRaised("ValueError")`. Move S10 to **after E1 lands** (re-sequence within S or split S10 into pre-E stub + post-E real). Pre-process `"-"` prefix. |
| H4 | Depth-4 | C | `itLambda.lambdaParams` may carry pre-monomorphization type variables ⇒ cache collision between `T=int`/`T=string` instantiations. | C1: specify `itLambda` emitted **after** monomorphization; RED test runs same lambda site under two instantiations; assert distinct cache keys. |
| H5 | Depth-5 | E | `finally` block's heap threading unspecified for multi-path try-body exits (normal-exit vs raised-exit, conditional writes). | E5 GREEN: enumerate all try-body exit continuations; walk finally per-continuation; cross-product. E7 DoD adds conditional-write try + finally read. |
| H6 | Depth-6 | G | Bijectivity `forall` axioms over FP/String distinct sorts push query into undecidable quantified fragment ⇒ UNKNOWN. | G4: assert axioms only for base ∈ {int, bv, bool}. For FP/String base, skip + emit `geDistinctBijectivitySkipped` classified hint. Document in ADR-0008. |
| H7 | Depth-7 | E | Inter-procedural `WalkRaised` propagation unspecified at `isCall` walker arm. | E3 GREEN: `isCall` callee returning `WalkRaised` propagates as `WalkRaised` into caller's handler stack; merge heaps at raise point. E7 DoD test: SUT calls helper that raises, outer try catches it ⇒ `sxSat`. |
| H8 | Depth-8 | R | `ref object` with inheritance: R6 reuses `svTuple` machinery which uses positional indices in derived type's own fields; inherited fields hit wrong index. | R6 GREEN: detect inherited field via `defining type of field ≠ deref'd type`; resolve to flat layout (base fields first). DoD: `Base.x` + `Child.y` both correct. |
| H9 | Feas-1 | E | `WalkCtx.found: Option→seq` change touches `shouldStop` + every `w.found` site simultaneously inside E2a. | Add **E2a-prep** micro-cycle (or fold into E1 DoD): change field type, update all sites, update `shouldStop` semantics, full `nimble test` green. E2a then adds only the structural `sxRaised` cascade. |
| H10 | Feas-2 | C | C2b raw `Z3_mk_app` with runtime-constructed sorts + `RawZ3FuncDecl` `wrap[T]` cast has no prior proof-of-concept. | C1 DoD adds PoC: construct `RawZ3FuncDecl` runtime, call `Z3_mk_app`, assert Z3 accepts + correct sort. Sort-construction helper `sortOfTuple(svTuple): RawZ3Sort` added. |
| H11 | Feas-3 | R | R1 conflates new IR (`itRef`/`itPtr`/`isDeref`/`isNew`), new `SVKind` variants, parser, EffectCtx fields, walker stubs — multi-concern; mirrors G1 split rationale. | Split R1 → R1a (IR + SVKind + exhaustive dispatch stubs) + R1 (`refSorts`, `nilConsts`, `allocRefSort`, `isDeref` select). |
| H12 | Feas-4 | E | E7 composition test uses `ptr int` deref but `isDeref` doesn't exist until R1. RED test will produce sxUnknown not sxSat. | E7: rewrite SUT using integer locals (`var n = x; try: n+=1; finally: if n>x: raise`). Move `ptr T` E+R composition into R13 or new R11c after R4 lands. |
| H13 | Feas-5 | G | `symBodyHash` collision for trivial procs across modules silently produces same key ⇒ wrong cached body. | G1a fallback: `getImpl.lineInfo.filename & ":" & strVal`, not `repr.hash`. DoD: two modules each define `proc id[T](x:T):T = x` ⇒ distinct cache keys. |
| H14 | Feas-6, Breadth-M6 | All | 6 ADRs + `witness-format-v3.md` blocking cluster firsts; no cycle home; doc authoring has no test, no GREEN. | Add explicit **doc-authoring cycles** before each cluster's first feature cycle: F0-ADR, S0-ADR, E0-ADR (folded into E2a-prep), G0-ADR, C0-ADR, R0-ADR (folded into R0). `witness-format-v3.md` into R11b DoD. Each is checklist-DoD (no RED). |
| H15 | Des-D1 | All | No `withSymexSettings` composition; 9 knobs grow without override fluency. | Add `withSymexSettings(base = defaultSettings()) do (s: var SymexSettings): ...` builder to public API surface; documented in Cross-cluster section. |
| H16 | Des-D2 | R | `he` prefix conflates halting errors (`heDepthExhausted`) with hint diagnostics (`hePtrFamily`). | `SymexErrorInfo` gains `severity: sevHint | sevWarning | sevError`. Halting kinds = `sevError`; family hints = `sevHint`. Invariant: `sxUnknown` ⇒ ≥1 `sevError`. |
| H17 | Des-D3 | E | `WalkResult` and `RawResult` are duplicate parallel unions; both carry `sxRaised`. | Make `WalkResult`/`InternalVerdict` internal-only; `RawResult` public; sole `toPublic` conversion at `runSymex` boundary. |
| H18 | Des-D4 | C | `InlinePolicy` enum buried in C4; should live with `SymexSettings` types. | Move definition into Cluster C preamble setup or cross-cluster types section. Mark exported. List in `SymexSettings` surface. |
| H19 | Des-D5 | S | `regex_parser.nim` has no standalone unit-test DoD; only tested via full `symexFind`. | S6 DoD: `tests/smt/tregex_parser.nim` tests parser directly on ≥8 supported + ≥3 unsupported constructs. |
| H20 | Des-D6 | C | `lambdaSite = "file:line:col"` ⇒ formatting changes break nominal equality. | Key by `(symBodyHash(lambdaBody), declOrderIndex)` — matches G's `symBodyHash` pattern. Update ADR-0009 + C5 equality semantics. |
| H21 | Des-D7 | R | `witness-format-v3.md` underspecified: aliased-ref, nil, nested ref-object format. | Add "Heap witness invariants" subsection to R preamble: alias dedup (lexicographically-first param holds `pointsTo`; others get `aliasRef:`), `nil` shape, recursive `pointsTo` for ref-object bounded by `maxHeapDepth`. |
| H22 | Breadth-H1 | S | `Table[string, V]` for V ≠ int not classified; silent runtime `ValueError`. | Add `seUnsupportedTableValType` classified at parse time. Z0 sweep or new S10.5 cycle. |
| H23 | Breadth-H2 | F | `seq[float32/64]` / `array[N, float32/64]` SUT param type allocation untested. | F9b cycle (or F9 DoD extension): full seq/array of float param works through allocate → extract → emitTyAndReader. |
| H24 | Breadth-H3 | F/G | `object variant` arm fields of type `float`/`string`/`ref` untested. | F9c cycle: variant arm-field bridge audit. |
| H25 | Breadth-H4 | R | `var ref T` parameters: heap write-back + ref rebinding interaction unspecified. | R cluster scope amended; add R8b sub-cycle covering `var ref T` rebinding, or classified `heUnsupportedVarRef` until Phase 16. |
| H26 | Breadth-H5 | G | `sink T` / `lent T` parameter annotations crash `classifyType`. | Pre-G1b typebridge audit: strip `nnkSinkTy`/`nnkLentTy` (symex is by-value). DoD test in L1 or G1b. |
| H27 | Breadth-H6 | G | `distinct T` of `distinct U` chain (nested distinct) unspecified in G4. | G4 DoD: recursive ejection + bijectivity at each level. |

## MED

| # | Source | Cluster | Issue / Fix |
|---|--------|---------|-------------|
| M1 | Des-D1 | E | `defectExclusions: set[string]` ⇒ `set[DefectKind]` enum; `dkOther` for user defects. |
| M2 | Des-D2 | C | `itLambda` should be `iekLambda` (value-producing) with comment block in `types.nim` documenting `iek`/`is`/`it` prefix convention. |
| M3 | Des-D3 | C | `seqInlineThreshold` coupled with `InlinePolicy.ipHybrid`; document or move inside variant. |
| M4 | Des-D4 | E | `cacheKeyRaisedSuffix` constant ⇒ `cacheKeyRaised(typeId): string` proc; no caller-side concat. |
| M5 | Des-D5 | G | G4 axioms asserted into per-`runSymex` Z3 context (not pooled); at most once per (typeId, walker). |
| M6 | Des-D6 | All | Add "ADR index" table (ADR, title, governs, depends-on, status). |
| M7 | Depth-1 | S | `Z3_mk_str_to_int` non-negative only; `parseInt("-…")` needs ITE preprocessing. |
| M8 | Depth-2 | E | E3 exact-string match is unsound for base-type handlers until E4 lands; mark E3 transitional + add negative test. |
| M9 | Depth-3 | R | `maxHeapDepth = 0` unlimited sentinel ⇒ infinite loop on cyclic structures. Fall back to `maxCallDepth` or hard cap 256. |
| M10 | Depth-4 | G | Distinct-sort cache lifetime: lives on `WalkerStatics` (per-walker), not per-frame. |
| M11 | Depth-5 | S | `parseNimRegexToZ3Regex` missing `\d`, `\w`, `\s`, `[^…]`, `(?:…)` spec. |
| M12 | Depth-6 | All | Walker version: single source-of-truth constant in `canonicalize.nim`; `canonicalize.nim` is the file (not `runtime.nim`) — fixes Feas-LOW-4. |
| M13 | Depth-7 | E | E5: `WalkRaised` produced by finally carries heap state at point of raise (including pre-raise finally mutations). |
| M14 | Feas-1 | S | S5 split: concrete-string special case = inline enumeration (no quantifier). |
| M15 | Feas-2 | G | G4 axioms: at most once per `(sortName, runSymex)`. |
| M16 | Feas-3 | R | R2: `maxFreshnessAssertions: int = 256` (0 = unlimited); overflow ⇒ `heFreshnessCapExceeded` hint. |
| M17 | Feas-4 | R | R6 with variant ref-object: emit `heRefVariantUnsupported` classified, not Defect. |
| M18 | Feas-5 | C | C4 `filter` axiomatize path: defer symbolic `filter` to Phase 16, emit `ceUnsupportedHof` (no Z3 `seqFilter` HOF exists). |
| M19 | Feas-6 | R | R12 sub-test independence: pure-bump test #1 stays green even if heap-serialization sub-test #2 fails. |
| M20 | Feas-7 | R | `witness-format-v3.md` authoring landed in R11b (see H14). |
| M21 | Breadth-M1 | All | `docs/symex/SYMEX_PLAN.md` doesn't exist; Z0 authors it with row schema `\| cluster \| cycle \| status \| commit \|`. |
| M22 | Breadth-M2 | F | F6 adds `isNaN`/`isInf`/`isFinite`/`isNormal` (Z3 FP-native); `classify(f)` defers as `feUnsupportedOp`. |
| M23 | Breadth-M5 | E | `$EffectCtx` debug printer; `determinism.md` "Debugging EffectCtx state" subsection. |
| M24 | Breadth-M8 | All | `char` classification missing: add `of "char": unranged(tInt(8, signed=false))` to `classifyType`; Z0 sweep. |
| M25 | Breadth-M9 | S | `s[i] in set[char]` codepoint/BV8 mismatch ⇒ `seUnsupportedSetCharInterop` classified. |

## LOW

| # | Source | Issue / Fix |
|---|--------|-------------|
| L1 | Des-LOW-1 | R9 `maxHeapDepth = 0 = unlimited` needs guard `if settings.maxHeapDepth > 0 and …`; DoD test for unlimited. |
| L2 | Des-LOW-2 | `SYMEX_PLAN.md` "Documentation index" section in R12 DoD. |
| L3 | Des-LOW-3 | C4 HOF dispatch qualifies by `std/sequtils` module via `getTypeImpl(callee).owner.strVal`; DoD: user `filter` not intercepted. |
| L4 | Des-LOW-4 | Walker-version invariant 1 documents "+1 per walker-semantic cluster" rule for Phase 16. |
| L5 | Depth-LOW-1 | E8 `getCurrentExceptionMsg` test: `raise newException(ValueError)` returns `""`. |
| L6 | Depth-LOW-3 | G8 multi-param key: name→type mapping via `gatherTypeSubst` table, then sort by name. DoD: swapped-arg-order calls cache-hit. |
| L7 | Depth-LOW-4 | R5 nil-fork: skip when `p != nil` already in path condition (sound optimization). |
| L8 | Depth-LOW-5 | S7a `bytes(s)`: `maxBytesEncodingLen: int = 32` cap; `seBytesLengthTooLarge` hint. |
| L9 | Feas-LOW-1 | E4 `ExnTypeTable` source-of-truth: list in spec or document the manual coverage table. |
| L10 | Feas-LOW-2 | R0 fork-site enumeration: grep `Path(` constructor, expect 25-30 (not 15-20) post-E/G. |
| L11 | Feas-LOW-3 | S6 split: S6a (`regex_parser.nim` + standalone tests) + S6b (walker integration). Subsumes H19. |
| L12 | Feas-LOW-4 | (folded into M12) |
| L13 | Breadth-LOW-1 | F + S preambles add "Out of scope for this cluster" tables listing classified-error ops. |
| L14 | Breadth-LOW-3 | G cycle table: footnote rows for folded G2 + G9. |
| L15 | Breadth-LOW-4 | R cluster: `owned T` / `WeakRef` / `Atomic[T]` ⇒ `heUnsupportedOwnership` classified. |
| L16 | Breadth-LOW-5 | S11 GREEN file `walker.nim` → `canonicalize.nim` (per M12). |
| L17 | Breadth-LOW-6 | `closures.md` authored in C1 alongside ADR-0009; C5 appends. |

## Open forks (after fork-filter)

**None.** Every item above carries a PhD-CS-recommended fix; none requires user-priority judgment that the standing bar doesn't already resolve.
