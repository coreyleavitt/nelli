# Phase 15 RFC — Architect Round 1 Consolidated Findings

Four lenses (Depth, Breadth, Design & Ergonomics, Implementation Feasibility) reviewed the RFC. This doc preserves every finding's substance for the bake-in pass. Severities deduped across lenses; cross-lens overlap noted in **[brackets]**.

## Counts

| Lens | CRIT | HIGH | MED | LOW |
|------|------|------|-----|-----|
| Depth | 4 | 7 | 8 | 5 |
| Breadth | 3 | 5 | 8 | 6 |
| Design | 3 | 7 | 7 | 4 |
| Feasibility | 2 | 5 | 7 | 5 |
| **Deduped** | **8** | **~18** | **~22** | **~14** |

## CRIT (deduped, all 8)

| # | Title | Lenses | Resolution path |
|---|-------|--------|-----------------|
| C1 | Heap state / alloc counter / heap depth must be per-`Path`, not per-`WalkCtx`. RFC contradicts itself (R1 places on WalkCtx, R3 says per-path). Counter under control-flow merge produces cross-path freshness leaks. | Depth-1, Design-3, Feasibility-2 | Add preparatory **R0** cycle that grows `Path` with `heaps`, `allocCounters`, `heapDepth` and audits every fork site copies them. R1+ build on this foundation. |
| C2 | Inter-procedural heap threading unspecified. Every `isCall`/`isGenericCall`/`iekClosureCall` descent must pass caller `path.heaps` in and merge callee's exit `heaps` out, else writes are silently lost. | Depth-2 | Add **R1b** cycle: thread heap state through call frames. Spec heap-pass-through contract in C2b, G1c, C4 DoDs. |
| C3 | `mkString(nimStr)` encodes UTF-8 bytes that Z3 then interprets as codepoints. `mkString("é").len` is 1 (Z3 codepoint) but Nim's `s.len` is 2 (bytes). ADR-0006 codepoint model is broken at the lift layer for multi-byte literals. | Depth-3 | ADR-0006 explicit handling of multi-byte literal encoding. S2 DoD: documented codepoint-length divergence from Nim's byte-length. |
| C4 | `inFlightExn` lifecycle unspecified: not cleared on handler-body exit; bare `raise` inside `finally` on normal path produces wrong error. | Depth-4 | Spec lifecycle in E5 GREEN: (a) set on handler entry, (b) cleared on handler exit, (c) bare-raise-in-finally-on-normal-path produces `sxRaised` from finally itself. |
| C5 | `sxRaised` verdict cascades structurally through `symex.nim` macro-emitted code: `case raw.status` exhaustive matches at 3+ sites, `toFindingStatus`, `saveSymexVerdictImpl`, `loadSymexVerdictImpl`, cache-key suffix table. E2 cannot be one cycle. Plus: `:raised` cache key needs `:raised:<typeId>` qualifier (collision risk) and `found` must accumulate, not be `Option`. | Depth-3 (HIGH), Design-2, Feasibility-1 | Split **E2 → E2a (structural cascade with stub `sfRaised`) + E2b (real `walk(isRaise)` semantics)**. Cache key becomes `:raised:<typeId>`. `WalkCtx.found` becomes `seq[RawResult]`. |
| C6 | Cluster S scope claims `&` (concat), `toLower`, `toUpper` are in-scope but **no cycle delivers them**. `$int`, `parseInt`, `$float`, `parseFloat` likewise missing. | Breadth-1, Breadth-HIGH-1 | Add **S8** (`&` concat), **S9** (toLower/toUpper either Z3-regex-range approx or classified `seUnsupportedStringOp`), **S10** (`$int`/`parseInt` via nim-z3's `Z3Int.toStr`/`Z3String.toInt`; `$float`/`parseFloat` classified errors). |
| C7 | User-defined exception types (`type MyError = object of ValueError`) not in static `ExnTypeTable`. Walker silently fails to catch via base type. Soundness failure: SUTs with custom exceptions report exception-escaped when it would be caught at runtime. | Depth-HIGH-6, Breadth-3 | Add **E4a** cycle: dynamic user-exception hierarchy table built at parse time from SUT type defs via `getImpl` walk. |
| C8 | `WalkCtx` is already a 12-field god object. Phase 15 adds ~6 more concerns (handler stack, in-flight exn, closure sym table, heap map, ref sorts, alloc counters). Per-path subset (heaps, heapDepth) lives on `Path`. Walker dispatch becomes 30+ arms touching one mutable record. | Design-1 | **GENUINE FORK** — see "Forks for user" below. |

## HIGH (selected, key ones)

| # | Title | Lenses | Resolution |
|---|-------|--------|------------|
| H1 | ADRs 0005-0010 inline in RFC at half-page summary depth; prior ADRs 0001-0004 are standalone files. ADR-0010 (heap) underspecified for sort identity (same-uninterp-sort or per-pointee-sort?). | Design-MED-1 (escalated to HIGH due to implementer-block risk) | Author **ADR-0005..0010 as standalone files** matching ADR-0001-0004 depth before each cluster's TDD begins. |
| H2 | `sxRaised` at wrong abstraction level: it's used both for internal "handler-stack propagation in flight" and external "SUT escaped with exception" states. Should be `WalkRaised` private intermediate, mapping to `sxRaised` only at SUT boundary. | Design-2 | Introduce `WalkResult` private union; only top-level `runSymex` maps `WalkRaised → sxRaised`. |
| H3 | Closure phantom-typed `Z3FuncDecl[ArgsTup, Ret]` cannot be instantiated at walk time because `ArgsTup` is compile-time. Closure memoization keyed by site alone aliases instantiations across types. | Depth-2, Feasibility-1 | Spec: use raw `Z3_mk_app` via `ffi.nim` for closure application. Closure key becomes `(site, envSortId, paramsSortTupleId)`. |
| H4 | G1 conflates IR + parser + walker + cache + cap into one cycle. Multi-file Nim exhaustiveness-check cascade. | Design-1, Feasibility-CRIT-1 | Split **G1 → G1a (IR + canonicalize), G1b (parser), G1c (walker dispatch + cache + cap)**. G2 and G9 folded into G1c. |
| H5 | R12 bundles cross-cluster regression sweep + walker version bump + rendering bump + heap-snapshot witness format. | Design-3 | Split **R12 → R11b (regression smoke only) + R12 (version bumps + witness format only)**. |
| H6 | C2 conflates closure construction (`itLambda` → `svClosure` with env snapshot) with closure call (`iekClosureCall` → axiom + descent). | Design-4 | Split **C2 → C2a (construction) + C2b (call dispatch)**. |
| H7 | Error-kind naming: `heInstantiationCapped`/`heConceptViolation` use `he` prefix (heap) but are generics errors. `seNotImplemented`/`seUnsupportedCapture` use `se` (string) but are closure errors. | Design-5 | Adopt prefix scheme: `he` (heap/R), `fe` (float/F), `se` (string/S), `ge` (generics/G), `ce` (closures/C), `ee` (exceptions/E). Document in `determinism.md`. |
| H8 | Closure equality "structural-vs-nominal" Open Question 6 already locked in by C2 design: site-key compared as Nim string (nominal-for-site), env-record compared via Z3 (structural-for-env). Punting to architect is misleading. | Design-6 | Close OQ 6. Document semantics as "nominal-for-site + structural-for-env" — this is the right answer for a correctness-oriented symex (matches Nim runtime semantics for proc-typed values). |
| H9 | C2's "unknown closure callee → classified error" contradicts C6's `applyTwice` test, which requires resolving a proc-valued parameter from the env. Distinct from "truly unknown callee." | Design-7 | C2b spec: proc-valued parameter resolved from env via `svClosure` lookup; only genuinely-unbound calls produce classified errors. |
| H10 | F5's `toFpFromSigned` requires `Z3BitVec` operand but SymVal carries `Z3Int` (`svInt`). Helper `symValToBV64` referenced but does not exist. Cycle won't compile as written. | Feasibility-2 | F5 GREEN spec: `intToBv[64](sv.zi, Z3BitVec[64])` then `toFpFromSigned`. Width-dispatch for svBV32/svBV64. |
| H11 | Walker version stays `"4"` through all 55 cycles. During the multi-cluster /loop session, mid-cluster cycles may stale-cache hit on Phase 14 entries for newly-supported SUT shapes (e.g., float-typed). | Feasibility-3 | **GENUINE FORK** — see "Forks for user." |
| H12 | G2 `signatureHash` referenced but not defined; bare-name `ctx.procs["foo"]` collision risk for same-name procs across modules. | Feasibility-4, Depth-MED-1 | Spec key as `calleeSym.symBodyHash` or `repr(calleeSym.getImpl).hash`; key schema is `name#typeargs` for generics, `name` for non-generics. |
| H13 | `split` symbolic decomposition is nearly always UNKNOWN; missing `∀i. not contains(parts[i], sep)` constraint makes it unsound for concrete inputs (multiple decompositions). | Depth-4, Design-MED-7, Feasibility-5 | Bound to `maxSplitParts` setting (default 8); add sep-non-substring constraint; UNKNOWN on overflow with `seZ3StringIncomplete` classified error. |
| H14 | `ptr T` arithmetic (`inc(p)`, `dec(p)`) not modeled; R11 only catches `cast[ptr T]`. `inc(p)` is a magic call not a cast. | Depth-5 | R8 spec: `inc`/`dec` on `ptr T` → `heUnsafeCast` classified error (or new `hePtrArith` kind). |
| H15 | `getCurrentException()` / `getCurrentExceptionMsg()` not addressed. `raiseMsg: IRExpr` field exists but E2 doesn't say whether it's walked. | Breadth-2, Breadth-MED-4 | Add **E8** cycle. E2 GREEN: `raiseMsg` evaluated via `walkExpr`, stored in `RawResult.raisedMsg`. |
| H16 | E+R heap-state threading through finally underspecified. E5 must explicitly carry `Path.heaps` into finally body. | Breadth-3 | Spec in E5 GREEN; add R12 composition test. |
| H17 | `float32` array elements, `system.signbit`/`copySign`/`nextafter` missing from F cluster. | Breadth-4 | F6 extension: `signbit` via `fpIsNegative`; `copySign`/`nextafter` classified `feUnsupportedOp`. Add **F9** (array element type-bridge audit). |
| H18 | Phase 14 carryover: B4 (named-field tuple strategies), `constraintDigest` empty on `floats`/`strings`/`lists`/`tables`/`sets` strategies. Phase 15 float/string clusters cache-collide on bound variations. | Breadth-5, Breadth-LOW-6 | Add **Z0** cycle: close B4 + populate the five empty `constraintDigest`s. |

## MED (selected, condensed)

- **M1.** ADR-0010 inline summary doesn't specify whether `Ref_int` and `Ref_string` are same or distinct uninterpreted sorts. Standalone ADR-0010 must resolve. *[Design-MED-1]*
- **M2.** S7 `bytes(s)` UTF-8 encoding undermespecified for non-ASCII; symbolic-length seq construction not decidable. Split S7 into S7a (encoding) + S7b (smoke). `bytes(s)` restricted to concrete-length strings; else `seBytesSymbolicLength`. *[Depth-MED-5, Design-MED-2]*
- **M3.** Open Question 4 (Defects as `sxRaised` vs `sxUnreached`): no genuine fork — silent-pass risk forces `sxRaised(isDefect=true)`. Close it now. *[Design-MED-3]*
- **M4.** `IRRegex` recursive sum type boxing unspecified; replace with `rePatternStr: string` at IR layer, parse at walk time. *[Design-MED-4]*
- **M5.** `heapSnapshot` witness format unspecified for aliased refs / nil / nested refs. Author `docs/symex/witness-format-v3.md` before R12. *[Design-MED-5]*
- **M6.** `iuFpNeg` breaks type-erasure consistency with FP binops. Drop it; runtime-dispatch `uNeg` on `sv.kind`. *[Design-MED-6]*
- **M7.** `SymexErrorInfo.kind: string` — RFC introduces 14+ new error kinds without an enum. Add `SymexErrorKind` enum before E1. *[Feasibility-MED-2]*
- **M8.** `distinct T` injection in G4 declared but inverse ejection not. Witness extraction fails. Add ejection + bijectivity axioms. *[Depth-MED-3]*
- **M9.** Closure body re-descent at each `iekClosureCall` can explode exponentially. Add `maxClosureInlineCount` (default 64). *[Depth-MED-4]*
- **M10.** Closure `funcSym` axiom must be asserted under path condition: `implies(path.pc, funcSym(env,args) == ret)`, not unconditional. Else cross-path over-constraint. *[Depth-MED-6]*
- **M11.** `s.high` (byte-length-minus-one) and `for c in s` (byte iterator) contradict codepoint-indexed model in S3. *[Depth-MED-7, Breadth-MED-6 (related: string mutation `s[i]=c`)]*
- **M12.** G6 concept conformance: user-defined concepts not in stdlib table produce false `geConceptViolation`. Trust semchecker; skip validation for unknown concepts. *[Depth-MED-8, Feasibility-MED-7]*
- **M13.** `float(x)` for out-of-range `int64` is Z3 UB and Nim implementation-defined. Spec: assert range on main path, emit `sxRaised(RangeDefect)` on overflow path. *[Depth-MED-2]*
- **M14.** `Z3UninterpSort` referenced (G4, R1) doesn't exist as standalone type. Use `Z3_mk_uninterpreted_sort` via FFI → `RawZ3Sort`. *[Feasibility-LOW-5]*
- **M15.** `string` mutation (`s[i] = c`, `s.add(c)`) absent from S cluster. Classify as `seUnsupportedStringOp` (or add S11 cycle). *[Breadth-MED-6]*
- **M16.** G+C composition: generic type args that are proc types. Verify `classifyProcTy` after `monomorphize` substitution. *[Breadth-MED-7]*
- **M17.** Closure capturing `ref T`: C5 punts to "Cluster R will cover" but R never lifts the classification. Add **R13** composition cycle. *[Breadth-MED-8]*
- **M18.** Cluster-close cycle wall-clock budget (full regression suite each) not flagged. Each closing cycle = ~2× normal budget. *[Feasibility-MED-6]*

## LOW (selected, condensed)

- L1. F4 NaN bit-pattern DoD item depends on F7 extraction; move to F7. *[Feasibility-LOW-2]*
- L2. S1 `string.len` may silently route through `iekSeqLen` causing sort crash. Add explicit guard. *[Feasibility-LOW-3]*
- L3. G8 Cluster S dependency unstated. *[Feasibility-LOW-4]*
- L4. R5 dead text "If Cluster E has not landed". Remove. *[Feasibility-LOW-1, Breadth-LOW-4]*
- L5. `:raised` cache suffix needs `:raised:<typeId>` (covered in C5); standardize on full-word suffixes (`:unknown` not `:unk`). *[Design-LOW-2]*
- L6. `sfUnknown` vs `sxUnknown` mixed in S5/S6 DoD. Audit and correct. *[Design-LOW-4]*
- L7. `maxInlineSeqLen=0` convention inverts meaning vs other 0-sentinel settings (`maxFrontierSize`, `maxCallDepth`). Use `InlinePolicy` enum. *[Design-LOW-3]*
- L8. Per-cluster cycle tables with "Key dependency" column missing from G, C, R. *[Design-LOW-1]*
- L9. `float` vs `float64` cache-key disambiguation. *[Depth-LOW-1]*
- L10. F1 precondition: no `:unk` cache entries for float-typed SUTs before F1 (parser rejected them). Confirm in DoD. *[Depth-LOW-2]*
- L11. S6 regex pattern → IRRegex parser non-trivial; explicitly scope to Z3-representable subset. *[Depth-LOW-3]*
- L12. `maxInlineSeqLen = maxInt` documented as unsound; add settings validation warning. *[Depth-LOW-4]*
- L13. Add OQ 8 (heap threading through calls — closed by C2 fix above), OQ 9 (`for c in s` byte iter handling). *[Depth-LOW-5]*
- L14. Cluster L `{.dirty.}` template variant test. *[Breadth-LOW-2]*

## New cycles introduced by Round 1

| Cluster | New cycles | Reason |
|---------|-----------|--------|
| Z | +Z0 | Phase 14 carryover close (B4, constraintDigests) |
| F | +F9 | float32 array element audit |
| S | +S8, +S9, +S10, +S11; split S7→S7a/S7b | concat, case ops, parseInt/$, mutation classification, UTF-8 encoding split |
| E | E2→E2a/E2b split, +E4a, +E8 | structural sxRaised cascade; user-exn dynamic table; getCurrentException |
| G | G1→G1a/G1b/G1c split (G2/G9 folded) | IR/parser/walker independence |
| C | C2→C2a/C2b split | construction vs call independence |
| R | +R0, +R1b, R12→R11b/R12, +R13 | preparatory heap-on-Path; inter-proc heap threading; regression-vs-bumps split; closure-capturing-ref |

**Pre-Round-1 total:** ~55 cycles. **Post-Round-1 projection:** ~70 cycles.

## Genuine forks for user (4)

1. **EffectCtx refactor (C8/Design-CRIT-1).** Extract `EffectCtx` record from `WalkCtx` bundling handler stack + closure syms + heaps + ref sorts + alloc counters. ~1-2 cycles of refactor work, every walker arm changes to `w.effects.X`. PhD-CS bar favors it; cost is ~30 walker-arm rewrites. **Recommend: YES** — Phase 14's lesson was that shared-module bugs in 12-field WalkCtx were the highest-cost class.

2. **Walker version policy during /loop (H11/Feasibility-3).** Current RFC: single bump `"4"→"5"` at R12. Stale-cache risk during the multi-cluster /loop session because mid-cluster /tdd cycles may hit Phase 14 cache entries for newly-supported SUT shapes. Options:
   - **(a)** Per-cluster bumps: `"4"→"5"` at F8, `"5"→"6"` at S7, ... `"9"→"10"` at R12. Six bumps. Eliminates stale-cache risk entirely. **Recommend: YES.**
   - **(b)** Single bump at R12 + cache-clear instruction at each cluster's first cycle in the handoff doc. Operationally fragile.
   - **(c)** Status quo (single bump). Implementer must remember to clear cache; bugs from forgetting are subtle.

3. **`maxInstantiationsPerProc` cap value (Open Question 5).** RFC default 64. Architect was asked to pick the number. **Recommend: 64** — matches `maxFrontierSize` and `maxInlineSeqLen` defaults; consistent with the existing settings family. Or **128** if generic-heavy SUTs (e.g., type-class macros) are expected.

4. **`cast[ptr T]` modeling (Open Question 7).** Current default: emit `sxUnknown(heUnsafeCast)`. Architect asked whether common safe-cast patterns warrant modeling. **Recommend: keep the default** (sxUnknown). Safe cast patterns in Nim are vanishingly rare in PBT-tested code; modeling them is a heavy lift for a low-prior payoff. Deferred to Phase 16 backlog explicitly.

## Resolved here (clear-best — apply directly to RFC)

All 8 CRIT (except #8/EffectCtx pending fork), all HIGH except #11/walker-version (fork), all MED, all LOW. Closed Open Questions 4, 6 (now resolved with documented rationale, not punted). Added OQ 8/9 → resolved as part of clear-best fixes. ADRs 0005-0010 to be authored as standalone files before respective clusters' TDD begins; inline summaries stay as pointers.
