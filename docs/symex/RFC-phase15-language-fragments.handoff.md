# Phase 15 (language fragments) — handoff

- **Stage:** 2 architect → round 2 COMPLETE → **reconciliation IN PROGRESS** (RFC drifted from real codebase; see `RFC-phase15-reconciliation.md`) → stage 3 TDD grind
- **Resume:** `/loop implement the next unimplemented RFC slice with /tdd, following the standing rules; stop when every slice is implemented`
- **Reconciliation:** global drift resolved in `RFC-phase15-reconciliation.md` §A–§E; per-cluster specifics filled into §F just-in-time before each cluster. Z0 fully reconciled (§C). Item-1 named tuples resolved as a `map`-keyword generalization (§D). Z0 item-3 `:unk` guard struck (would break live caching).
- **Toolchain (established at Z1):** dev/test runs use `localhost/proptest-dev:latest` (built from `ghcr.io/coreyleavitt/nim:latest`, Nim 2.2.10, + `z3-devel`) via `scripts/build-dev-image.sh`. **nim-z3 v2.0.0 needs Nim >= 2.2.10** (2.2.0/2.2.4 fail on a funcdecl tuple-type parser bug). Single test: `scripts/dt.sh <c|cpp> tests/<file>.nim`.
- **Shipped:** Z0 (carryover), Z1 (nim-z3 v2.0.0 pin bump + canary), Z2 (regression smoke, 17 tests, 0 drift), **Z3 complete** (a: error/severity/settings enums; b: svUninterpRef/itUninterp; c: classifyType char + sink/lent; d: withSymexSettings/+ merge; e: cacheKeyRaised + suffix rename; f: SYMEX_PLAN.md). **Z4 done** (`WalkCtx.found` Option→seq + WalkerStatics/CallFrameCtx empty records + ADR-0007). **Cluster Z COMPLETE (Z0–Z4).** **Cluster L COMPLETE** (L1 boundary audit, L2 untyped templates, L3 getAst/quote — all verification-only; templates-macros.md authored). **Cluster F (float) in progress:** F0-ADR (on disk), **F1 SHIPPED** (type-bridge: itFloat32/64 + svFloat32/64 + 12-arm ripple). **F2 SHIPPED** (literals + IEEE ==/!=). **F3 SHIPPED** (arith). **F4 SHIPPED** (ordering compare). **F5 SHIPPED** (int<->float conv: `float(x)`/`float32(x)` via toFpFromSigned/rmRNE, `int(f)` via toSbv/rmRTZ; **fix:** int→float takes the BV pattern directly via `toBv64ForFp` — the `int2bv(bv2int(x))` round-trip hung Z3 forever on ordering goals). **Next: F6** (math-module ops + FP predicates), then F7 (bit-exact extraction), F8 (regression+walker bump 4→5), F9a/b/c.

## Status
- RFC v3 on disk: `RFC-phase15-language-fragments.md` (7,795 lines, 82 cycles, **9 clusters**: Z, L, F, S, H, E, G, C, R).
- Round 2 findings preserved at `RFC-phase15-language-fragments.round2-findings.md` (85 raw findings deduped to 67 across 4 lenses; reference for any future architect rounds).
- Round 2 bake-in complete. Zero open forks survived the fork-filter. Every fix is PhD-CS clear-best applied directly.
- ADR-0005 (float NaN/Inf) and ADR-0008 (generic instantiation) authored ahead of TDD by F/G bakers; the rest (0006/0007/0009/0010 + SYMEX_PLAN.md + witness-format-v3.md + closures.md) ship via their explicit doc-authoring cycles at TDD time.

## Major structural changes in v3
- **New Cluster H** (heap preparation) inserted between S and E. Single cycle H1 promotes the former R0 forward so E3/E5/E7 can reference `path.heaps` at compile time. Cluster R now starts at R1a.
- **Cluster Z expanded to 5 cycles**: Z0 (carryover) → Z1 (pin) → Z2 (smoke) → **Z3** (cross-cutting infra: `SymexErrorKind` enum, `severity` field, `DefectKind`, `InlinePolicy`, `svUninterpRef` in `SVKind`, `withSymexSettings`, `char` classification, sink/lent strip, `cacheKeyRaised` proc, SYMEX_PLAN.md authored) → **Z4** (`WalkCtx.found: Option → seq`, `EffectCtx → WalkerStatics + CallFrameCtx` split, ADR-0007 authored).
- **`EffectCtx` split into `WalkerStatics` + `CallFrameCtx`** with lifetime-tagged separation; closes round-1's god-object regression (Des-CRIT-D1). Invariant 7 codifies the split.
- **`WalkResult → InternalVerdict`** rename; `toPublic(iv): RawResult` is the sole conversion at the `runSymex` boundary. Invariant 9.
- **Walker/rendering version constants** single-sourced in `canonicalize.nim` (not `runtime.nim`/`walker.nim`); every closing cycle's GREEN file list corrected. Invariant 6.
- **Cycle splits applied**: R1 → R1a/R1; S6 → S6a/S6b; S10 → S10a/S10b (S10b deferred to post-E); F9 → F9a/F9b/F9c; new R8b for `var ref T`.
- **ADR-authoring cycles** named explicitly: F0-ADR, S0-ADR, G0-ADR, C0-ADR; E0-ADR folds into Z4; R0-ADR folds into H1.

## Key decisions locked in round 2
- **Lifetime-tagged walker state** — three buckets: `WalkerStatics` (per-walker immutable post-parse), `CallFrameCtx` (push/pop on call descent), `Path` (per-path; deep-copied at every fork). No mutable per-walker state outside `statics`/`frame`/`errors`/`found`.
- **Severity contract** — `sxUnknown` ⇒ ≥1 `sevError`; `sxSat`/`sxUnsat` with non-empty errors ⇒ all `sevHint`/`sevWarning` (annotations only).
- **`withSymexSettings`** composition primitive added; every cluster exercises it via a confirmation test.
- **Multi-`sxRaised` cache** — serializer writes every finding under its own `:raised:<typeId>` key; `loadAll(sutKeyPrefix)` reconstructs.
- **Closure axiom is multi-return-path** — body descent collects sub-paths; per-sub-path `implies(path.pc and pc_i, funcSym(env, args) == v_i)`; Z3 ITE-merge for main axiom.
- **`allocCounters` merge is `max`**, not replace (preserves freshness across nested calls).
- **`lambdaSite` keyed by `(symBodyHash(body), declOrderIndex)`** — formatting-stable, NOT `"file:line:col"`.
- **`distinct T` bijectivity axioms only for decidable base sorts** {int, BV, bool}; FP/String base ⇒ `geDistinctBijectivitySkipped` hint.
- **`split(s, "")`** special-case: skip `contains` constraint; assert one-codepoint-per-element.
- **`parseInt` raises-path** moves to S10b (post-E); S10a documents explicit unsoundness window.
- **`maxHeapDepth = 0`** falls back to `maxCallDepth` then hard cap 256.
- **Settings family**: `maxInstantiationsPerProc=64`, `maxClosureInlineCount=64`, `maxSplitParts=8`, `maxHeapDepth=8`, `maxFreshnessAssertions=256`, `maxBytesEncodingLen=32`, `inlinePolicy=ipHybrid`, `seqInlineThreshold=8`, `defectExclusions={dkOutOfMemoryDefect, dkStackOverflowDefect}`.

## Cluster summary (post-round-2)
| Cluster | Cycles | Walker bump | Notes |
|---------|--------|-------------|-------|
| Z | 5 (Z0..Z4) | — | Z3 + Z4 land all cross-cutting infra |
| L | 3 | — | Mostly verification; `char` + sink/lent regression here |
| F | 12 (F0-ADR, F1..F8, F9a/b/c) | 4→5 at F8 | F9 split; F6 FP-native predicates |
| S | 15 (S0-ADR, S1..S11 with S6a/b, S7a/b, S10a/b splits) | 5→6 at S11 | S10b deferred to post-E |
| H | 1 (H1) | — | Promoted R0 + ADR-0010 |
| E | 10 (E1..E8 with E2a/b, E4a splits) | 6→7 at E7 | ADR-0007 in Z4; E7 SUT rewritten |
| G | 11 (G0-ADR, G1a/b/c, G3..G8, G10) | 7→8 at G10 | G2/G9 folded |
| C | 8 (C0-ADR, C1, C2a/b, C3..C6) | 8→9 at C6 | `itLambda → iekLambda` |
| R | 16 (R1a/R1, R1b, R2..R8, R8b, R9..R11, R11b, R12, R13) | 9→10 at R12; rendering 2→3 | R0 removed; R8b new |
| **Total** | **82** | | (+12 vs round 1's 70) |

## Open forks for round 3
None. All round 2 findings closed with PhD-CS clear-best fixes. No genuine forks surfaced.

## ADR / doc files to author at TDD time
Already on disk (ahead of TDD by F/G bakers):
- `docs/symex/ADR-0005-float-nan-inf.md` ✓
- `docs/symex/ADR-0008-generic-instantiation.md` ✓

Authored at their TDD cycle:
- `docs/symex/ADR-0006-string-codepoint-indexing.md` (S0-ADR)
- `docs/symex/ADR-0007-exception-flow.md` (Z4)
- `docs/symex/ADR-0009-closure-encoding.md` + `docs/symex/closures.md` skeleton (C0-ADR)
- `docs/symex/ADR-0010-logical-heap.md` (H1)
- `docs/symex/SYMEX_PLAN.md` 78-row plan table (Z3)
- `docs/symex/witness-format-v3.md` (R11b DoD)

## Next steps
1. Safe `/compact` point — RFC v3 on disk, round-2 findings preserved, handoff current.
2. `/loop implement the next unimplemented RFC slice with /tdd, following the standing rules; stop when every slice is implemented`
3. Eventually: `/code-review` cycles.
