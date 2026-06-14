# RFC Phase 15 — Code-Reality Reconciliation (authoritative override layer)

> **Status:** authoritative. This document overrides the file paths, current-state
> premises, and a handful of cycle specifics in `RFC-phase15-language-fragments.md`
> wherever the two disagree. The RFC's *design* (cluster ordering, semantics, Z3
> modelling, invariants) stands; what is corrected here is its **map to the real
> codebase**, which was written against an idealized layout.
>
> Built from a four-subsystem ground-truth inventory (strategy/DSL, symex core +
> walker, cache/canonicalize, type-bridge/parser/stdlib) on 2026-06-14.
>
> **The implementation loop consults this file first, then the RFC cycle text.**
> Global drift (§A–§E) is resolved here once. Per-cluster specifics are reconciled
> into §F just-in-time, immediately before that cluster's cycles are implemented —
> verified against the real files, never improvised in code.

---

## §A — File-path reality map

The RFC assumes a `strategies/` directory, an `smt/db.nim`, and an `smt/walker.nim`.
None exist. The real layout is flat. Map RFC paths → real files:

| RFC-assumed path | Real file(s) | Notes |
|---|---|---|
| `src/proptest/strategies/floats.nim` etc. | `src/proptest/strategy.nim` | **All** strategy constructors + combinators live in one file. No `strategies/` dir. |
| `src/proptest/strategies/tuples.nim` (`tupleOf`) | `src/proptest/strategy.nim` (`map` macro, line 303) | No `tupleOf`. The N-ary `map` macro is the product combinator. See §D. |
| `src/proptest/smt/db.nim` (symex cache) | `src/proptest/symex.nim` (load: `loadSymexVerdictImpl` :283, `loadSymexWitnessesImpl` :224) + `src/proptest/smt/canonicalize.nim` (suffix/version consts, cache key) | The symex verdict/witness cache is split between these two. |
| `src/proptest/db.nim` | `src/proptest/db.nim` ✓ | This is the **general example-DB**, not the symex cache. Do not touch it for symex work. |
| `src/proptest/smt/walker.nim` | `src/proptest/smt/runtime.nim` | The walker (WalkCtx, Path, all `walk*` arms, RawResult, SVKind, SymVal, `runSymex` impl) lives here. |
| IR types file | `src/proptest/smt/types.nim` ✓ | IRStmtKind, IRExprKind, IRTypeKind, SymexStatusKind, SymexTargetKind, SymexErrorInfo, IR constructors. |
| Nim-AST→IR parser | `src/proptest/smt/dsl_parser.nim` ✓ | `monomorphize`, `gatherTypeSubst` (generics already monomorphized here). |
| Nim-type→IR-type bridge | `src/proptest/smt/dsl_typebridge.nim` ✓ | ref/ptr currently unwrapped here (`:128`, "aliasing is a follow-up" = Cluster R). |
| stdlib proc models | `src/proptest/smt/stdlib_models.nim` ✓ | |
| version/suffix consts | `src/proptest/smt/canonicalize.nim` ✓ | `symexWalkerVersion="4"` (:63), `renderAsChoicesVersion="2"` (:40), suffixes (:23/:28/:30). **Single source — confirmed no duplication in runtime.nim.** Invariant 6 already holds. |

## §B — Current-state premise corrections

Places where the RFC misdescribes **what exists today** (its end-state design is fine;
only the "currently…" claims are wrong):

1. **`ints` → `integers`.** The integer strategy is `integers(lo, hi, weights)`
   (`strategy.nim:380`), digest `"integers:lo=" & $lo & ";hi=" & $hi`. It is the
   **only** constructor that sets a non-empty `constraintDigest` today.
   **`booleans()` does NOT** set a digest (RFC implies it does) — model item-2 work on
   `integers` alone.

2. **No `tupleOf` exists.** RFC: "the `tupleOf` macro currently errors on named
   fields." Reality: there is no `tupleOf`. The product combinator is the N-ary
   `map` macro (positional tuples only). Item-1 is net-new design — see §D.

3. **`EffectCtx` is *introduced*, not *extracted*.** RFC v2 history says "EffectCtx
   record extracted from WalkCtx." Reality: `WalkCtx` (`runtime.nim:1511`) is
   monolithic; no `EffectCtx`/`WalkerStatics`/`CallFrameCtx` exists. The round-2
   `WalkerStatics`+`CallFrameCtx` split (Z4/E/C clusters) is **net-new construction**.
   `WalkCtx.found` is `Option[RawResult]` today (Z4 changes it to `seq`).

4. **`:unk` is the *current, live* suffix — NOT legacy.** RFC Z0 item 3 calls `:unk`
   "pre-Phase-13 legacy" needing a skip-load guard. **This is false and dangerous.**
   `cacheKeyUnkSuffix = ":unk"` (`canonicalize.nim:30`) is read by
   `loadSymexVerdictImpl` (`symex.nim:314`) on every unknown-verdict lookup. **A
   guard that skips `:unk` would break current unknown-verdict caching.** See §C item 3
   for the reconciled, sound treatment.

5. **No error-kind prefix scheme exists yet.** Today: `SymexTargetKind` enum
   (`stkLabel/stkAssertionViolation/stkIndexError/stkFieldDefect`, `types.nim:361`)
   and `SymexErrorInfo{kind: string, msg: string}` (`types.nim:406`). The `he/fe/se/
   ge/ce/ee` prefixes and the `SymexErrorKind` enum are net-new (Cluster Z3). No
   collision to reconcile — additive.

## §C — Reconciled Z0 (the next slice)

Z0's three sub-items, reconciled:

1. **Named-field tuple strategies (item 1).** Implement via §D (extend `map`), in
   `src/proptest/strategy.nim`. RED test exercises `map(x = integers(0,9), y = strings())`
   producing a `tuple[x:int, y:string]`.

2. **`constraintDigest` population (item 2).** In `src/proptest/strategy.nim`, give
   these five constructors a non-empty digest derived from their config params,
   mirroring `integers`:
   - `floats(min, max, allowNan)` (:541) → e.g. `"floats:min=…;max=…;nan=…"`
   - `strings(minLen, maxLen)` (:522) and `strings(intervalSet, minLen, maxLen)` (:531)
     → include length bounds and (for the interval overload) an interval digest
   - `lists(elem, minLen, maxLen)` (:421) → include bounds **and `elem.constraintDigest`**
   - `tables(keyStrat, valStrat, minSize, maxSize)` (:455) → bounds + key/val digests
   - `sets(elemStrat, minSize, maxSize)` (:479) → bounds + elem digest
   RED test asserts each has `constraintDigest != ""` for ≥2 distinct parameterizations.

3. **`:unk` migration (item 3) — RECONCILED: documentation only, NO skip-load guard.**
   - **Do NOT add a guard skipping `:unk`** — it is the live suffix (§B.4).
   - Staleness across walker versions is **already handled**: `symexWalkerVersion` is
     part of the content-addressed cache key (`symexCacheKey`, `canonicalize.nim:410`),
     so a walker bump (`"4"→"5"` at F8) produces entirely new keys; pre-bump entries
     are orphaned automatically and never looked up. No pollution is possible.
   - The cosmetic `:unk` → `:unknown` rename is **deferred to the cluster that next
     bumps the walker version** (F8), bundled with that bump so old keys are orphaned
     in the same step. Z0 records this rationale as a `## :unk` comment near the suffix
     constants in `canonicalize.nim`; no behavioural change, no test.
   - Net effect on Z0 DoD: the "skip-load guard + its test" bullet is **struck**;
     replaced by the documented rationale above.

## §D — Item-1 design resolution: named tuples via `map`, not `tupleOf`

**Decision (locked):** generalize the existing N-ary `map` macro (`strategy.nim:303`)
to accept **keyword-named strategy components**, producing a named tuple. Do **not**
add a separate `tupleOf` macro.

```nim
map(integers(0,9), strings())            # positional  -> Strategy[(int, string)]   (unchanged)
map(x = integers(0,9), y = strings())    # keyword      -> Strategy[tuple[x:int, y:string]]   (new)
map(sa, sb, f)                            # combining fn -> Strategy[R]  (unchanged; positional only)
```

Rationale (PhD-level, best-in-class):
- **Nim analog of Hypothesis `builds(target, *args, **kwargs)`** — the canonical
  applicative constructor. Keyword components = field names; this is exactly `builds`
  with a tuple target. Forward-compatible with a future `map(T, x=…, y=…)` /
  `builds(T, …)` for object construction (what C4/G8 likely need).
- **One deep module, not two shallow ones.** `map` already owns "draw each component
  in declaration order from one `DataSource`" + uniform choice-sequence shrinking.
  Names are a typing/presentation facet over the *same* draw mechanism — they belong
  on the same combinator; a sibling `tupleOf` would duplicate draw/shrink logic and
  risk divergence.
- **Unambiguous parsing rule:** keyword components arrive as `nnkExprEqExpr`. If any
  component is keyword-named, **all** strategy components must be named (mixing is a
  compile-time error) and the result is a named `nnkTupleConstr` (`(x: v0, y: v1)`);
  the trailing-combining-function form remains positional-only.
- **Zero downstream breakage:** Nim tuples are structural — `tuple[x:int,y:string]`
  is assignment-compatible with `(int,string)` — so a named-tuple strategy is drop-in
  wherever a positional one was expected.

This closes the round-2 "named-field" gap on the real construct. A one-paragraph
note belongs in an ADR at TDD time (fold into the Z-cluster doc work; no separate
ADR file needed unless object-construction `builds` is added later).

## §E — Net-new symbol registry (what the RFC creates, and where it lands)

These are correctly absent today; the listed cycle creates each in the listed real file.
This registry exists so the loop treats "absent" as "to be built here," not as drift.

| Symbol / change | RFC cycle | Real home file |
|---|---|---|
| `SymexErrorKind` enum; `severity` field on `SymexErrorInfo`; `DefectKind`; `InlinePolicy` | Z3 | `smt/types.nim` |
| `svUninterpRef` in `SVKind` | Z3 | `smt/runtime.nim:44` |
| `WalkCtx.found: Option → seq[RawResult]` | Z4 | `smt/runtime.nim:1515` |
| `WalkerStatics` + `CallFrameCtx` (split of conceptual `EffectCtx`) | Z4/E/C | `smt/runtime.nim` |
| `svFloat32` / `svFloat64`; `itFloat32/64`; FP IR exprs | Cluster F | `smt/runtime.nim` (SVKind), `smt/types.nim` (IR) |
| String ops (len/concat/substr/contains/split) IR + walk arms | Cluster S | `smt/types.nim` (IR), `smt/runtime.nim` (walk), `smt/dsl_parser.nim` (parse) |
| `Path.heaps/heapDepth/allocCounters` | Cluster H | `smt/runtime.nim:130` |
| `isRaise/isTry`, handler stack, `sxRaised` status, `InternalVerdict` | Cluster E | `smt/types.nim` (IR+status), `smt/runtime.nim` (walk) |
| `:raised:<typeId>` cache suffix | Cluster E | `smt/canonicalize.nim` |
| `isGenericCall` distinction / instantiation cache / `distinct` bijection | Cluster G | `smt/dsl_parser.nim`, `smt/runtime.nim` |
| `iekLambda`/`iekClosureCall`, `svClosure`/`closureSyms` | Cluster C | `smt/types.nim`, `smt/runtime.nim` |
| `itRef/itPtr`, `svRef`, logical heap (Z3 array theory), freshness | Cluster R | `smt/types.nim`, `smt/runtime.nim`, `smt/dsl_typebridge.nim` |
| walker version bumps (`"4"→"5"`@F8 … `"9"→"10"`@R12); rendering `"2"→"3"`@R12 | per-cluster | `smt/canonicalize.nim` (single source) |

## §F — Per-cluster reconciliation (filled in just-in-time)

Reconciled immediately before each cluster's cycles are implemented, verified against
the real files. Global maps (§A–§E) already cover the systematic drift; this section
captures cluster-specific corrections as they're discovered.

- **Cluster Z** — see §C (Z0 reconciled). Z1–Z4 reconciled when reached.
- *(L, F, S, H, E, G, C, R: pending)*
