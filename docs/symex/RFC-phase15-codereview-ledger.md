# Phase 15 Code-Review Ledger

Multi-agent review of the Phase 15 "language fragments" delta (`242e6e6..26b0e82`, ~3,678 lines across `src/proptest/smt/`). 7 dimension reviewers → adversarial verification of every High claim → consolidation. Status legend: `open` / `fixed` / `deferred` / `wontfix` / `refuted`.

## Confirmed findings (post-verification)

| id | sev | status | file:line | finding | verify |
|----|-----|--------|-----------|---------|--------|
| CR-1 | High | fixed | runtime.nim:6144-6154 | Closure-body heap writes (`p[]=v`) never merged back to caller path → **false UNSAT** for refs mutated inside a closure | HOLDS (verifier: no return-merge after closure descent; comment "inert until R4" stale, R4 shipped). **Fixed**: added `currentClosureExitHeaps/AllocCounters/LiveRefs/DidMutateHeap` threadvars + `drainClosureExitHeap` helper; `applyClosureGround` merges exit paths' heaps after body descent; `isLet`/`isAssign`/`isIf` walk arms drain back to the survivor path. Also fixed spurious `sawUnknown = true` for void closures (no-value body with non-empty fallThrough no longer degrades to sxUnknown). Tested in `tests/tsymex_phase15_CR1_CR5_closure_heap.nim` (CR-1 tests 1–4). |
| CR-2 | High | open | canonicalize.nim:590-604 | 4 verdict-affecting settings absent from cache key → stale-cache unsoundness: `defectExclusions`, `maxClosureInlineCount`, `maxBytesEncodingLen` (flip sxSat↔sxUnknown), `maxFreshnessAssertions` (false-SAT dir) | HOLDS (verifier confirmed 4/6; `maxInstantiationsPerProc` refuted=self-protected via prog.procs; `maxSplitParts` harmless=unwired) |
| CR-3 | Med | fixed | runtime.nim:2637-2720 | float→int out-of-range: silent unsound witness, no sxUnknown/hint (won't round-trip; Nim RangeDefects) | HOLDS (documented "unsoundness window"; no guard). **Fixed**: domain-bounded + exclusion hint. Added `convFloatToIntBoundConds` threadvar; `iekConvFloatToInt` arm deposits `f >= lo and f < hi` constraint (which also excludes NaN/Inf via IEEE comparison semantics) drained into `p.pc` by walker arms (mirrors `parseIntRaiseConds`); `feConvDomainExcluded` (sevHint) emitted to `convFloatToIntDomainHints` and drained into `RawResult.errors`. RangeDefect modeling remains Phase-16. Tested in `tests/tsymex_phase15_CR3_CR4_CR6_float.nim` (CR-3 tests 1-4). |
| CR-4 | Med | fixed | runtime.nim:2637-2720 | `convWidth` set by parser but never read; `int32(f)` modeled as 64-bit truncation → wrong witness in (INT32_MAX,INT64_MAX] | HOLDS. **Fixed**: `iekConvFloatToInt` now reads `e.convWidth`; for width 32 uses `toSbv[..,32]` and returns `svBV32` (signed); domain bounded to `[-2^31, 2^31)`. Composes with CR-3 bounds. Tested in `tests/tsymex_phase15_CR3_CR4_CR6_float.nim` (CR-4 tests 1-2). |
| CR-5 | Med | fixed | runtime.nim:6146 | closure-descent `descentBase.liveRefs` empty → closure-body `new T` not asserted distinct from caller refs → spurious aliasing witness | HOLDS. **Fixed**: added `currentCallerLiveRefs` threadvar seeded by `seedCallerHeapThreadvars` from the caller path's `liveRefs`; `descentBase` now includes `liveRefs: currentCallerLiveRefs` so `assertFreshness` for closure-body `new T` sees the caller's already-minted refs and emits `newRef != callerRef`. Tested in `tests/tsymex_phase15_CR1_CR5_closure_heap.nim` (CR-5 test 1). |
| CR-6 | Med | fixed | runtime.nim:2407-2447 | `cmpFloat` `doAssert a.kind==b.kind` crashes (not sxUnknown) for float32-var vs float64-var compare (Invariant-3) | PARTIAL (narrow case holds; retBindEq path refuted). **Fixed**: mixed-FLOAT reconciliation added at the top of `cmpFloat`: when a.kind==svFloat32 and b.kind==svFloat64 (or vice versa), widen the float32 to float64 via `toFp(rmRNE(), fp32, Z3Float64)` before the comparison — mirrors Nim semantics and the mixed-integer reconciliation at ~3204-3210. The `doAssert` now checks `in {svFloat32, svFloat64}` (not `==`) for a clean classified error if a non-float somehow arrives. Tested in `tests/tsymex_phase15_CR3_CR4_CR6_float.nim` (CR-6 tests 1-3). |
| CR-7 | Med | open | runtime.nim (god module) | runtime.nim 7057 lines; 5 independent theory subsystems inlined in lower()/walk(); split into runtime_{heap,closures,exceptions,floats,strings}.nim | design judgment |
| CR-8 | Med | fixed | E7_smoke.nim / dt-bounded.sh | C/C++ backend parity is a manual workflow step, not an automated regression gate; exception witnesses not replayed against SUT at runtime. **Fixed**: (Part A) `scripts/parity-check.sh <test.nim>` runs the same test under both `c` and `cpp` via `dt-bounded.sh` and fails if either backend fails or they diverge — this is now the canonical RFC DoD "both backends" gate. (Part B) `tests/tsymex_phase15_E_roundtrip.nim` adds exception-witness runtime replay across three E-cluster shapes (condRaise/ValueError, finallyReplaces/IOError, finallyReplaces/ValueError, assertDefect/AssertionDefect): after `symexFind` reports `sxRaised`, the actual Nim proc is called at runtime with `raisedWitness[...]` and the expected exception is confirmed raised; contrasting inputs confirm no spurious raise. 7/7 tests pass on both `c` and `cpp`. | reviewer (coverage) |
| CR-9 | Med | open | types.nim / canonicalize.nim | design: SymVal.signed phantom field; 5-way svInt/svBV split; ad-hoc caps → ResourceBudget; 28 threadvars → LowerCtx | design judgment |
| CR-10 | Low | open | regex_parser.nim:272-281 | `{n,m}` repetition parsed as int64 then passed cuint → silent truncation >2^32 → wrong regex bound (absurd trigger) | reviewer (security) |
| CR-11 | Low | open | runtime.nim:2775-2789 | `iekStrSplit` concrete-inline paths lack parts-count cap → compile-time DoS on huge literal | reviewer (security) |
| CR-12 | Low | open | runtime.nim:839-843 | `liveRefs` grows O(N) memory even after `maxFreshnessAssertions` stops emitting Z3 assertions | reviewer (security) |
| CR-13 | Low | open | runtime.nim:6767-6769 | `currentWalkCtxPtr` left dangling if `walk()` raises (no current deref-after path; add try/finally) | reviewer (security) |
| CR-14 | Low | open | exn_hierarchy.nim:39-66 | `EOFError`/`LibraryError`/`ResourceExhaustedError` absent from table → sxUnknown+warn instead of subtype match (conservative) | reviewer (FSE) |
| CR-15 | Low | open | dsl_parser.nim:2341-2357 | `SomeOrdinal` concept table omits user enums → spurious geConceptViolation (safe direction) | reviewer (generics) |
| CR-16 | Low | open | types.nim:743,750 | dead enums `ceUnsupportedCapture`, `geUnresolvedGeneric` never emitted (cosmetic; underlying constructs classify/crash-visibly) | downgraded by verifier |
| CR-17 | Low | open | runtime.nim:2664-2665,2068 | latent Z3 hazards: `s[i]` ordering (String+Int+BV) and `toBv64ForFp` svInt int2bv arm — no current parser trigger | reviewer (Z3) |
| CR-18 | Low | open | runtime.nim:2792 | `maxSplitParts` cap defined but unwired (symbolic split throws sxUnknown first); wire + add to cache key when implemented | verifier |

## Refuted (false positives — recorded, not presented)

| claim | why refuted |
|-------|-------------|
| float→int ordering HANG (FP+BV+Int) ×2 reviewers | `toSbv` consumes FP, `bv2int` lifts to Z3Int; ordering goal is pure integer arith — not the F5 pathology |
| closureInlineCount budget non-transitive (HC1) | line 6136 overwrites zero-init with `frameStack[^1].closureInlineCount + 1` — accumulates correctly |
| heapDepthExhausted in-place mutation inflates nil branch (HC4) | `forkPath` builds fresh Path objects; both branches inherit copied depth uniformly, no asymmetry |
| buildClosure capture-drop → svTupleEq doAssert crash | different env arities → different funcSym keys → svTupleEq never called cross-arity |
| `owned T` → silent verdict (heUnsupportedOwnership dead) | enum IS emitted via SymexOwnershipUnsupportedError catch → sxUnknown |
| unsupported capture → silent wrong verdict | Table[int,int] crashes visibly (ValueError); absent-name drop carries no SymVal, benign |
| unresolved generic → silent verdict | compile-time error() or geInstantiationCapped + sawUnknown → sxUnknown |
| retBindEq doAssert crash via int(float) return | both sides svInt; reconciliation guard handles it; no mismatch |
| maxInstantiationsPerProc missing from cache key | self-protected: cap changes prog.procs, which IS in the program key |
| pcImpliesNonNil ref-prefix collision | self-retracted; trailing `_` separator prevents collision |

## Verified-correct (positives confirmed by reviewers)

G1a bare-name collision fix · distinct-sort bijectivity is ground (no ∀) · freshness pairwise-ground · mapArray is not a quantifier · mkStringVar ≤0xFF byte constraint · toBv64ForFp (int→float) · string mutation/iteration classified honestly · IEEE float-eq semantics · finally on normal+exceptional paths · getCurrentException-outside-handler classified · Z3 FFI cstring lifetimes / no use-after-free / refcount leak benign · witness ≤0xFF round-trip · NaN/Inf, alias-visibility, heapDepth, nil-fork all tested.
