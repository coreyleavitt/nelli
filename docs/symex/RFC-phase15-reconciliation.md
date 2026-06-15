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

- **Cluster Z**
  - **Z0 — SHIPPED.** Items 1+2 implemented in `strategy.nim` (keyword `map`
    macro for named tuples; `constraintDigest` on floats/strings/lists/tables/
    sets). Item 3 reconciled to a doc-only `:unk` rationale in `canonicalize.nim`
    (no guard). Tests: `tests/tsymex_phase15_z0_carryover.nim` (6 tests, green on
    `nim c` + `nim cpp`); regressions clean (tstrategies/tderive/tdsl/tcombine/
    tnested). Registered in `proptest.nimble`. SYMEX_PLAN.md row to be marked at Z3
    (plan doc is authored then).
  - **Z1 — SHIPPED (pin bump to nim-z3 v2.0.0).** Major reconciliation finding:
    proptest was building against a **stale pre-v1.0.0 nim-z3 snapshot**, and the
    canonical test image (`nimlang/nim:2.2.0`) **cannot compile nim-z3 v2.0.0** —
    Nim 2.2.0 **and 2.2.4** reject its tuple-type generic args in `funcdecl.nim`
    (`Z3FuncDecl[(Z3Int, E), F]` → "Mixing types and values in tuples"). **Fix:
    the toolchain is now Corey's prebuilt `ghcr.io/coreyleavitt/nim:latest`
    (Nim 2.2.10, openSUSE) + `z3-devel`**, under which v2.0.0 compiles clean.
    - Tooling: `scripts/Containerfile` + `scripts/build-dev-image.sh` build
      `localhost/proptest-dev:latest`; `scripts/runtest.sh` + `scripts/dt.sh`
      rewritten to use it (was Debian+apt `libz3-dev`). Both mount the milpa CAS
      at its host-absolute path too, so v2.0.0's `_deps/softlink` symlink resolves.
    - `_deps/z3` re-vendored to v2.0.0 (`milpa fetch`); `milpa.lock` z3 identity
      updated. NOTE: the lock's `version "0.0.1"` is milpa's **local-path identity
      placeholder**, not semver — the RFC DoD "lock shows version 2.0.0" does not
      apply to a `local=` dep. Effective version is verified by source + canary.
    - 8-name v1-symbol grep over `src/`+`tests/`: **0 matches** (RFC DoD met).
    - Canary `tests/tsymex_phase15_z1_canary.nim` (reconciled to real API:
      `sortOf(Z3String, ctx)` → "String") green on `nim c` + `nim cpp`; registered
      in `proptest.nimble`.
  - **Z2 — SHIPPED (regression smoke, verification-only).** Curated subset + a
    broader sweep — **17 symex tests across all major subsystems** (arith/bool/BV/
    overflow/seq/hashset/models/Z3Error-hierarchy/multivariant-walker/canonicalize/
    typebridge/verdict-cache/...) — **all green under v2.0.0**. **0 drift findings.**
    Reconciliation: the RFC's `tsymex_phase15_z2_regression.nim` gorge/testament
    meta-runner is **not** created (fragile); the curated subset is already in
    `proptest.nimble`'s test task, which is the durable regression gate.
  - **Z3 — IN PROGRESS (staged into sub-slices).** Z3 is 8 mutually-referential
    changes; reconciled into sub-slices to keep each TDD-testable:
    - **Z3a — SHIPPED.** Enum/type scaffolding in `types.nim`: `SymexErrorSeverity`,
      `SymexErrorKind` (32 variants), `DefectKind`, `InlinePolicy`; `SymexErrorInfo`
      migrated `kind: string` → `kind: SymexErrorKind` + `severity` field;
      `SymexSettings` gains `defectExclusions` (default `{dkOutOfMemoryDefect,
      dkStackOverflowDefect}`) + `inlinePolicy` (default `ipHybrid`). The migration
      had **exactly one** construction site (`runtime.nim:2401`, the Z3Error catch),
      now mapping `$e.name` → `ek*` with `sevError`. Test
      `tests/tsymex_phase15_z3_infra.nim` (5 tests) green c+cpp; regressions clean
      (incl. `phase7_assertcovered`'s manual `SymexSettings(...)`). Registered.
    - **Z3b — SHIPPED.** `svUninterpRef` (in `SVKind`/`SymVal`, real home `runtime.nim`,
      NOT `types.nim` as RFC #5 says) + `itUninterp`/`tUninterp` in `IRType`. The
      `itUninterp` ripple was **14 arms** (not ~34 — many cases had `else`), enumerated
      compiler-guided across runtime/types/canonicalize/dsl_parser/symex. Real impls:
      `tyOf`→`tUninterp(sortName)`, `symValHash`→`astHash`, `==`/`$`/`canonicalize`/
      `emitIRType` for itUninterp. The rest are unreachable-until-cluster-E guards
      (raise/discard) since `svUninterpRef` isn't produced until E8. Tests added to
      `tsymex_phase15_z3_infra.nim` (7 total) green c+cpp; regression clean (walker/
      typebridge/canonicalize). **Lesson:** per-test `nim check` only compiles reachable
      code — full regression surfaced the `canonicalize`/`dsl_parser`/`symex` arms that
      the infra test alone missed.
    - **Z3c — SHIPPED.** `classifyType` (`dsl_typebridge.nim`) `char` branch
      (`unranged(tInt(8, signed=false))`) + `sink`/`lent` strip. Two reconciliation
      findings beyond the RFC: (1) a usable `char` needs **char-literal expression
      parsing** too — added `nnkCharLit -> mkIntLit(ordinal)` in `dsl_parser.nim`
      (the RFC only specced the type); (2) `sink T`/`lent T` are **NOT** `nnkSinkTy`/
      `nnkLentTy` (those node kinds don't exist) and are **not** pre-normalized by Nim —
      they reach `classifyType` as `sink[T]`/`lent[T]` **`nnkBracketExpr`**, stripped
      structurally. Test `tests/tsymex_phase15_z3c_classify.nim` (char + sink SUTs via
      `symexFind`) green c+cpp; lent uses the identical strip path. Registered.
    - **Z3d — SHIPPED.** `withSymexSettings` builder + `+` merge combinator, in
      `types.nim` (next to `defaultSymexSettings`; pure-settings helpers, no new file).
      Reconciliation: the RFC's signature `withSymexSettings(base, f)` is wrong for the
      `do`-block call — the trailing `do` binds to the **first** param, so `f` must come
      first (`withSymexSettings(f, base = default)`); explicit base via named arg.
      `+` merges b's non-default fields over a (all 8 SymexSettings fields). Tests in
      `tsymex_phase15_z3_infra.nim` (now 9) green c+cpp; settings regression clean.
    - **Z3e — SHIPPED.** `cacheKeyRaised(typeId)` proc (`:raised:<typeId>`) added to
      `canonicalize.nim`; suffix consts renamed `cacheKey{Sat,Unsat,Unk}Suffix` →
      `cacheKey{Sat,Unsat,Unknown}` with `:unk`→`:unknown` (**supersedes Z0 §C.3's
      deferral to F8** — done here per the RFC; old `:unk` entries orphaned, harmless).
      Updated all callers (symex.nim re-export + 6 uses) and 2 test files
      (`phase13_satsuffix`, `phase13_layer1_wire`). Tests in `tsymex_phase15_z3_infra.nim`
      (now 11) green c+cpp; cache round-trip regression clean (satsuffix, unknown/unsat
      roundtrip, layer1_wire, verdict_primitives, c1_fromcache). Invariant 6 (single-source
      version consts) already holds (verified Z1) — no extra version-doc edit needed.
    - **Z3f — SHIPPED.** Authored `docs/symex/SYMEX_PLAN.md` — 89-row cycle tracker
      (Z3 sub-sliced a–f; G2/G9 folded) + documentation index. Doc-only cycle.
    - **Z3 COMPLETE** (a–f). Cross-cutting infrastructure fully in place.
  - **Z4 — SHIPPED. Cluster Z COMPLETE.** `WalkCtx.found` `Option[RawResult]`→
    `seq[RawResult]` (9 sites migrated: decl, `shouldStop` (loop form, sxSat-only
    until E2a adds sxRaised), 5 `=some()`→`.add()`, init `none`→`@[]`, extract
    `isSome`/`get`→`len>0`/`[0]`). `WalkerStatics`/`CallFrameCtx` added as empty
    records + WalkCtx fields (net-new — no `effects` existed, §B.3). `ADR-0007-
    exception-flow.md` authored. WalkCtx is private, so verified **behaviorally**
    (the RFC's `typeof(WalkCtx.found)` external assertion is impossible); test
    `tests/tsymex_phase15_z4_walkctx.nim` (sat/unsat/branchy) green c+cpp; broad
    9-test regression clean (all verdict classes + walker depth + caching).
- **Cluster L** (templates/macros — verification-only)
  - **L1 — SHIPPED.** Boundary audit reconciled to a **behavioral** test
    (`tsymex_phase15_l1_boundary.nim`): template-defined, macro-emitted (`quote do`),
    and `{.dirty.}`-template SUTs all symex to `sxSat` — the trust boundary holds.
    Stronger than the RFC's internal `parseProc(fn.getImpl)` structural assertion
    (exercises the whole pipeline; no dependency on internal `parseProc`). Doc
    `docs/symex/templates-macros.md` authored. Green c+cpp. Registered.
  - **L2 — SHIPPED.** untyped-template params. Reconciled sub-test 2: the RFC's
    "unsupported residual → classified `errors`" doesn't match reality — `symexFind`
    returns the public `SymexResult` which has **no `errors` field** (diagnostics are
    on internal `RawResult`), and the walker handles `isUnsupported` via `discard`
    (no errors populated). So sub-test 2 instead verifies untyped expansions are
    **faithfully walked** (a template `if n!=5: return` constraint → downstream
    contradiction is `sxUnsat`). **Finding logged** (templates-macros.md): the
    walker silently *skips* `isUnsupported` statements without marking uncertainty —
    sound for no-op constructs, a pre-existing conservative-incompleteness risk for
    effectful ones; narrowed as E/R model those constructs. Green c+cpp.
  - **L3 — SHIPPED. Cluster L COMPLETE.** `quote do` `len` SUT is walker-identical
    to hand-written (both sxSat); a `quote do`-emitted user-generic call
    monomorphizes + symexes to sxSat. Invariant-4 smoke (re-ran Z-cluster phase15
    tests) clean. Minor finding logged (templates-macros.md): expression-`if`
    (`nnkIfExpr`) is unsupported (compile-time error). Green c+cpp.
- **Cluster F** (float — first feature cluster)
  - F0-ADR — SHIPPED (ADR-0005 on disk).
  - **F1 — SHIPPED.** Type-bridge: `itFloat32`/`itFloat64` (IRTypeKind) + `svFloat32`/
    `svFloat64` (SVKind, carrying `fp32: Z3Float32`/`fp64: Z3Float64`); `tFloat32`/
    `tFloat64` ctors. Compiler-guided ripple = **12 arms** (allocateSym→`mkFloat*Var`,
    tyOf→`tFloat*`, symValHash→`astHash`, emitTyAndReader/primTyAndReader→`readFloat`,
    canonicalize/emitIRType/classifyType real; iteSV/symLit/defaultZero/return-eq
    stubs since floats have no ops until F2–F4). **Reconciliations:** (1) RFC's RED
    SUT `x > 0.0` needs F2+F4 — reduced to a pure type-bridge test (float param →
    target → sxSat); (2) RFC's var-ctor `mkFloat32Var`/`mkFloat64Var` confirmed real
    (not `mkFpVar`); (3) float extraction returns a **default** (not raise — sxSat
    needs it) since the public `SymexResult`/`RawWitness` has no float slot until F7.
    Gotcha logged: a `discard ## doc-comment` in an object-variant arm misparses —
    use `#`. Green c+cpp; 9-test ripple regression clean.
  - **F2 — SHIPPED.** Float literals: `iekFloatLit` IR node (fval/fwidth) + 7-arm
    `IRExprKind` ripple (parser/abstraction/canonicalize/render/probeProto/lower).
    `mkFloatLitSym` lowers via Nim `classify` → `mkFpNaN`/`mkFpInf`/`mkFpZero`/
    `mkFloat*` per ADR-0005. Parser: `nnkFloat*Lit` + parse-time `-<float>` fold
    (`-0.0`/`-Inf`). **Reconciliation:** RFC put `==` in F4, but a literal can't be
    tested without equality — F2 adds IEEE `==`/`!=` (`cmpFloat`, wired into both
    binop comparison branches); F4 adds ordering. `Inf`/`NaN` fold to literals (no
    sym handling needed). `import std/math` added to runtime for `classify`. Key
    result: `f == NaN` → **sxUnsat** (IEEE). Green c+cpp; 9-test ripple regression
    clean (int arith/compare unaffected).
  - **F3 — SHIPPED.** Float arithmetic + - * / (arithFloat, Z3Fp ops, rmRNE) + unary -; `/` infix added to binopForInfix (float div; operands are float in typed AST). No new IR variants. UNSAT check (x*0==5) confirms arithmetic is real. Green c+cpp; regression clean (int/BV arith unaffected).
  - **F4 — SHIPPED.** Ordering < <= > >= filled into cmpFloat (Z3 fpa_lt/leq/gt/geq; IEEE: false on NaN). x<x is sxUnsat (irreflexive). Green c+cpp.
  - **F5 — SHIPPED.** int↔float conversions: `float(x)`/`float32(x)` via
    `toFpFromSigned(rmRNE)`; `int(f)` via `toSbv(rmRTZ)` truncation (OQ2). Parser
    detects `nnkConv` int↔float and emits `iekConvIntToFloat`/`iekConvFloatToInt`;
    operand type resolved via `valueTypeName` (getTypeInst), target via
    `typeNodeName` (n[0] strVal). **Critical fix:** int→float must take the
    operand's bitvector pattern *directly* (`toBv64ForFp`: sign/zero-extend to 64);
    the initial `intToBv[64](toZ3Int(sv))` form emitted `int2bv(bv2int(x))`, a
    Int+BV+FP mixed-theory query that **never terminates** on ordering goals
    (`float(x) > 1.5` pegged a core for 24min+). Equality goals masked it (Z3
    guesses a model). Out-of-range float→int overflow → `sxRaised(RangeDefect)` is
    deferred to post-cluster-E (documented unsoundness window). Green c+cpp; F1–F4
    + phase1_arith + phase2_overflow regression clean, no hangs.
  - **F6 — SHIPPED.** std/math float ops + FP predicates, all Z3-FP-native.
    New `iekMathCall` IR (op string + arg list); parser intercepts float-receiver
    calls by name (`mathFpModeledOps`/`mathFpDeferredOps` in stdlib_models.nim)
    before the user-proc fall-through, and routes *any* other float-receiver
    stdlib call (detected via `isStdMathProc` on the callee's defining file path)
    to the same path. Lowering (`lowerMathCall`, width-symmetric f32/f64):
    `abs→abs`, `sqrt→sqrt(rmRNE)`, `min→min`, `max→max`,
    `floor/ceil/round/trunc→roundToIntegral(rmRTN/rmRTP/rmRNE/rmRTZ)`,
    `signbit→isNegative`, `isNaN→isNaN`. Deferred (`classify`/`copySign`/any
    unmodeled `math.<name>`) raise `SymexUnsupportedOpError`, caught at the
    `runSymex` boundary → `sxUnknown` + `errors[0] = {feUnsupportedOp, sevError}`
    (Invariant 3 — never a silent UNSAT). `SymexResult.errors` added so callers
    can read the classified error. **RFC deviations:** (1) nim-z3 predicate
    wrappers are `isNaN`/`isInf`/`isNegative`/`isNormal`/`isFinite` (NOT the
    RFC's `fpIsNaN`/`fpIsInfinite`/`fpIsNegative`/`fpIsNormal` guesses);
    `isFinite` is a built-in composite wrapper. (2) Nim's std/math (2.2.x)
    has no `isInf`/`isFinite`/`isNormal`/`nextafter` procs — only
    `isNaN`/`signbit`/`classify`/`copySign` — so those three predicates are
    modeled in the runtime for forward-compat but are unreachable from a real
    Nim SUT and thus untested; `nextafter` likewise can't be called (dropped
    from the deferred test, `classify`+`copySign`+`math.ln` cover the deferred
    path). (3) `FloatClass`'s NaN tag is `fcNan`, not the RFC's `fcNaN`.
    `SymexErrorInfo` has no `op` field, so the `math.<name>` op string rides in
    `.msg`. Green c+cpp (15/15 each); F1–F5 + phase1_arith + phase2_overflow
    regression clean, no hangs.
  - **F7 — SHIPPED.** Eval-side bit-exact float witness round-trip. The F1
    `extractLeaf` stub is replaced: `svFloat64`/`svFloat32` SymVals are
    evaluated against the SAT model into two new `RawWitness` tables
    (`float64Vals`/`float32Vals`), read out by `readFloat`/`readFloat32`
    (now real, not 0.0 stubs) and exposed to callers as concrete
    `r.witness[i]` values. `renderAsChoices` gains a `SomeFloat` arm
    (`floatChoice(v, -Inf, Inf, allowNan = true, smallestNonzeroMagnitude
    = 0.0)`) so float witnesses serialise into the choice-IR / `floats`
    replay strategy. New error kind `feExtractionFailed` + a `runSymex`-reset
    threadvar sink (`extractionErrors`) drained into `RawResult.errors` on a
    sat finding. **RFC deviations:** (1) the RFC's two-step `m.eval(raw,
    modelCompletion=true)` then `Z3Float64(raw: evaled)` reconstruction is
    unnecessary — nim-z3's `evalFloat64Opt(a, modelCompletion = true)` already
    does `m.eval(a, true).toFloat64` internally, so we call it directly on the
    typed `sv.fp64`/`sv.fp32`. (2) **NaN can't go through `evalFloat*Opt`:**
    Z3's `Z3_mk_fpa_to_ieee_bv` on a NaN is *unspecified* and does not fold to
    a numeral, so `fpBitsToUint64` raises and `evalFloat*Opt` returns `none`,
    losing the NaN. F7 therefore tests `m.evalBool(isNaN(sv.fpXX),
    modelCompletion=true)` first and emits Nim's canonical `NaN` (ADR-0005:
    single canonical NaN, no payload). ±Inf/±0/normals extract losslessly via
    `evalFloat*Opt`. (3) The RFC located the choice-seq float rendering in
    `canonicalize.nim`, but the actual `RawWitness`→choice rendering is
    `renderAsChoices` in `symex.nim` (canonicalize.nim only canonicalizes IR);
    the float arm landed there. The `formatFloat(_, ffDefault, 17/9)`
    precision note applies to `serialize.nim`'s float-numeral string encoding,
    not to `floatChoice` which stores the raw exact float64. Green c+cpp (7/7
    each); F1–F6 + phase1_arith + phase2_overflow regression clean, no hangs.
  - **F8 — SHIPPED.** Closes Cluster F: F-cluster regression smoke +
    arbitrary-float64 SUT round-trip property + `withSymexSettings` wiring +
    walker version bump `"4" → "5"`. New test `tsymex_phase15_F8_smoke.nim`,
    no new source files (the cycle budget was reserved for fixes; none were
    needed beyond the bump). **23-shape hand-enumerated round-trip suite:**
    each shape is a (symex SUT, runtime predicate) pair sharing an identical
    boolean condition; `symexFind` → `sxSat`, the concrete float witness is
    read from `r.witness[i]` (F7's `float64Vals`/`float32Vals` tables via
    `readFloat`/`readFloat32`) and plugged back into the Nim predicate at
    runtime, asserting it returns true — a genuine round-trip of the SUT body,
    not a classify-only check. **`withSymexSettings` wiring:** confirmed
    threading `ipAlwaysAxiomatize` through `symexFind` on a float SUT yields
    `sxSat`. **Broken-SUT check:** `ln(x)` (unmodeled transcendental) →
    `sxUnknown` whose every error kind is `feUnsupportedOp` (no silent
    empty-errors). **Walker bump** done as the final edit, single-sourced in
    `canonicalize.nim:symexWalkerVersion` (no duplicate in `runtime.nim`);
    `symexWalkerVersion == "5"` asserted in the smoke. **API deviations vs the
    RFC spec text:** (1) the base settings ctor is `defaultSymexSettings()`
    (the RFC/spec say `defaultSettings()`, which is the *engine's* unrelated
    proc); (2) `withSymexSettings`'s real signature is
    `withSymexSettings(f, base = defaultSymexSettings())` — the `do`-block
    binds the *mutator* `f`, so the faithful form is
    `withSymexSettings() do (s: var SymexSettings): s.inlinePolicy = ...`
    (NOT `withSymexSettings(defaultSettings()) do ...`, which fails to compile
    — `defaultSettings()` would bind to `f`); (3) round-trip shape `int(x)==3`
    is windowed to `x > 3.0 and x < 4.0` because Z3 models out-of-range
    float→int as unconstrained (RFC F5 range-overflow deferral), so the
    unbounded form is SAT-by-NaN/huge-float and would not round-trip through
    Nim's `int()`. Green c+cpp (4/4 each). Regression subset run (all green,
    no hangs): F1–F7, l1/l2/l3, phase1_arith, phase1_bool, phase2_overflow,
    phase2_abstraction, phase3_recursion, phase4_tuple, phase5_seq,
    phase5_table, phase14_disc_promotion, phase14_frontier_pruning.
  - **F9a — SHIPPED.** `array[N, float32/float64]` element type-bridge audit +
    array-derived NaN extraction. Mostly a completeness confirmation: the
    Phase-4 array walker allocates elements via `allocateSym(elemTy)` recursion,
    so `svFloat32`/`svFloat64` elements allocate; `classifyType` recurses on the
    element type, so `array[4, float64]` classifies as `itArray(itFloat64, 4)`;
    `emitTyAndReader` recurses per element, routing float elements to F7's
    `readFloat`/`readFloat32`; `extractFromSymVal`'s `svArray` arm recurses to
    `extractLeaf`, which populates `float64Vals`/`float32Vals` (NaN via the
    `model_completion=true` path). **One GREEN fix:** literal array indexing
    builds an `iteSV` ite-chain merge over the elements, and `iteSV`'s float
    arm was an F3/F4-era `raise "float path-merge lands with F3/F4"` stub — now
    implemented as `ite(cond, t.fp32/fp64, e.fp32/fp64)` (Z3 FP `ite`). New test
    `tsymex_phase15_F9a_array_float.nim` (xs[2]>0.0 float64, float32 parallel,
    array-element NaN `not(xs[0]==xs[0])` classifying `fcNan`). Green c+cpp 3/3.
  - **F9b — SHIPPED.** `seq[float32]`/`seq[float64]` SUT parameter type, a real
    GREEN extension of the Phase-5 dynamic-seq machinery (mirroring seq[int]) at
    four sites: (1) `allocateSeqDataRaw` — new `itFloat32`/`itFloat64` arms
    building `mkArrayVar[Z3Int, Z3Float32/Z3Float64]`; (2) the seq-index walker
    path (`isIndex`/seq) — float arms `wrap[Z3Array[Z3Int, Z3FloatN]]` +
    `SymVal(kind: svFloatN, fpN: select(typed, idxZi))`; (3) `extractSeqElements`
    — float arms build the per-element FP SymVal and **delegate to
    `extractLeaf`** so the F7 NaN/model_completion path is reused verbatim;
    (4) `emitTyAndReader(itSeq{itFloat64/32})` → `("seq[float]"/"seq[float32]",
    readSeqFloat64/readSeqFloat32)` + new `readSeqFloat64`/`readSeqFloat32`
    readers in runtime.nim (analogous to `readSeqInt`, indexing
    `float64Vals`/`float32Vals`). New test `tsymex_phase15_F9b_seq_float.nim`
    (seq[float64] `xs[0]!=xs[0]` NaN classifying `fcNan`; seq[float32]
    `xs[0]>1.0`; seq[float64] ordered `xs[0]<xs[1]`). Green c+cpp 3/3;
    regression F1/F7/F8/F9a + phase5_seq + phase4_array clean, no hangs.
  - **F9c — SHIPPED. Cluster F COMPLETE.** `object variant` arm fields of type
    `float32`/`float64` (closes Cluster F). The arm FIELDS themselves were
    already supported transitively — the Phase-11 variant walker allocates arm
    fields via `allocateSym(fieldTy)` recursion (svFloat32/svFloat64 fields),
    arm-field access is parser-routed through `isVariantField` (binding the
    float SymVal into the env, then F3/F4 ops consume it), and
    `extractFromSymVal`'s `svVariant` arm recurses to `extractLeaf` (populating
    `float64Vals`/`float32Vals` for the active arm). The real GREEN territory
    turned out to be the **`bool` discriminator** the spec SUT uses (enum discs
    lift to BV, but `bool` was explicitly skipped in the enum-lift and so stayed
    `svBool` — never previously exercised as a variant disc in symex). Three
    fixes: (1) `discEq` (allocateSym variant range-constraint) + (2) the
    `isVariantField` arm-gate `discEq` both gained an `svBool` arm
    (`disc.bo == mkBool(tagOrd != 0)`, false=0/true=1); (3) the Phase-14 A6
    Z3Int disc-promotion (under `isOptimised`, default) is now **skipped for
    `itBool` discs** — a bool disc is only ever compared to true/false, never
    arithmetic, and promoting it to svInt made `if v.k:` read an svInt that
    tripped `lowerBool`'s `svBool` assert. New test
    `tsymex_phase15_F9c_variant_float.nim` (true-arm float64 `v.x>0.0`,
    false-arm int `v.y<0`, true-arm float32 `v.a>0.0`; each branch carries its
    own target so symexFind witnesses each arm; witness round-trips `.k`/`.x`/
    `.a`/`.y`). Green c+cpp 3/3. Regression (phase11_walker/fielddefect,
    phase14_multivariant_walker/witness, typebridge_variants, rectify_variants,
    F8/F9a/F9b) all green, no hangs — the enum-disc promotion path is untouched
    (only `itBool` is excluded). **Cluster F (F1–F8, F9a/b/c) COMPLETE.**
- **Cluster S** (full strings — reconciled at S0-ADR, 2026-06-15)
  - **String model — BYTE-FAITHFUL (Corey-locked, see ADR-0006).** The Cluster S
    string model is **byte-faithful, NOT codepoint-indexed**. `mkString` lowers to
    `Z3_mk_lstring` (each Nim byte → one Z3 character), and free `string` vars
    (`mkStringVar`) **must assert at allocation that every character is ≤ 0xFF**
    (Latin-1 byte range). Under that constraint **Z3 position == Nim byte index**,
    so Z3's positional model and Nim's byte model **coincide — there is NO
    divergence**. Consequences for the per-cycle work below:
    - `s.len`, `s[i]` read, `s[a..b]`, and `s.high` are
      **byte-faithfully SUPPORTED** (lower directly to `len`/`at`/`substr`;
      `s.high == len-1`). They are NOT classified errors. **`for c in s` is NOT
      supported** — corrected at S3: byte-faithful removes the byte/codepoint
      objection but not the *unbounded symbolic iteration length* one (no sound
      bounded encoding), so it classifies `sxUnknown` for that honest reason
      (not `seByteIterUnsupported`). See the S3 — SHIPPED note for the fix.
    - **Only** `s[i] = c` / `s.add(c)` (Z3 strings are **immutable**) and
      `toLower`/`toUpper` (**no Z3 case-folding**; regex-range approx is Phase 16)
      stay unsupported → `seUnsupportedStringOp`. The reason is immutability /
      missing-Z3-op, **not** byte/codepoint mismatch.
    - The ≤ 0xFF char-range constraint is the **soundness mechanism** (without it
      Z3 picks full-Unicode codepoints that don't round-trip to Nim bytes). S1 and
      S3 must add this constraint on string allocation.
    - **Coverage boundary:** free-var witnesses are limited to one byte per char
      (no synthesized multi-byte runes). A multi-byte *literal* like `"é"` still
      works — it lowers to its raw bytes `[0xC3,0xA9]` (len 2) and a free var can
      match those byte values; `s == "é"` is SAT at `s.len == 2`.
    - **Error-kind note:** `seByteIndexUnsupported` is **no longer needed for
      `s.high`** (now supported, `len-1`). `for c in s` IS unsupported (corrected
      at S3: unbounded symbolic iteration length) but is classified with an
      explicit message, NOT `seByteIterUnsupported`. Both kinds remain in the
      `SymexErrorKind` enum (don't delete during type planning — other ops may
      still reference them), but S3 does NOT emit either for `s.high`/iteration.
    - **`bytes(s)` (S7a) shrinks to near-trivial:** the base model is already a
      byte sequence (chars 0..255), so `bytes(s)` is essentially the **identity
      view** (map each char position to its byte value as BV8/int) — not a separate
      UTF-8-decoding subsystem.
  - **Reality baseline (Phase 5 string support).** `string` is already a
    first-class Z3 sort end-to-end: `itString` (`types.nim:45`, no payload
    fields — `:118`), `svString{str: Z3String}` (`runtime.nim:57`/`:90`),
    allocation `mkStringVar(baseName)` (`runtime.nim:404`), literal lowering
    `of iekStrLit: SymVal(svString, mkString(e.sval))` (`runtime.nim:1067`),
    extraction `w.strVals[path] = m.evalStr(sv.str)` (`runtime.nim:1436`),
    canonicalize `Ty<S>` / `Ex<S:…>` (`canonicalize.nim:118`/`:274`). The
    parser already lifts `nnkStrLit`/`nnkRStrLit`/`nnkTripleStrLit` →
    `mkStrLit(n.strVal)` (`dsl_parser.nim:444`; IR field is **`sval`**, not
    `strVal`). What exists today is exactly equality + table-key indexing;
    **no** string op surface (`len`/`at`/`substr`/`find`/`contains`/`split`/
    `replace`/regex/`bytes`) is modeled, and there is **no** `StdlibModelKind`
    `smkStr*` family yet (grep: 0 hits) — those are net-new for S1. So the RFC's
    S1 "audit confirms `mkStringVar`/`evalStr` already wired" premise is
    **correct**; S1's real work is adding the IR variants + stdlib-model stubs.
  - **nim-z3 string/regex API surface (verified against `_deps/z3/src/z3/`).**
    The modules are flat (`z3/strings`, `z3/sequence`, `z3/regex`) — the RFC's
    `z3/strings`/`z3/regex` references are fine as import paths but the op procs
    live mostly in **`sequence.nim`** (re-exported by `strings.nim`):
    - `mkString(s)` / `mkStringVar(name)` / `evalStr(m, a, modelCompletion=true)`
      (`strings.nim:54/62/95`); `Z3String = Z3Seq[Z3Char]` (`:45`).
    - `len` (`:109`), `at(a, i): Z3Seq` single-codepoint (`:147`), `nth`/`[]`
      element (`:88`/`:97`), `substr(a, offset, length)` — **(offset, length)
      signature**, out-of-range → empty seq (`:157`), `contains` (`:167`),
      `startsWith(a, prefix)` / `endsWith(a, suffix)` — **already Nim arg-order**
      (`:171`/`:176`), `indexOf(a, sub[, start]): Z3Int` returning −1 when absent
      (`:180`) — **this is the real `find`** (there is no proc literally named
      `find`), `replace(a, old, new)` first-occurrence (`:194`),
      `lastIndexOf` (`:199`), `&`/`concat` (`:143`), lexicographic `<`/`<=`
      (`strings.nim:210/214`; **no `Z3_mk_str_gt`/`ge`** — `>`/`>=` flip args).
    - int interop: `Z3String.toInt: Z3Int` (`strings.nim:126`, `Z3_mk_str_to_int`)
      and `Z3Int.toStr: Z3String` (`:134`, `Z3_mk_int_to_str`) — these are the
      S10a `$int`/`parseInt` primitives (RFC's "z3/strings int-interop").
    - codepoint interop (S7a `bytes`): `toCode(s): Z3Int` (`Z3_mk_string_to_code`,
      `strings.nim:107`) and `fromCode(c): Z3String` (`:114`). RFC S7a cites
      `z3/strings.toCode` — **correct**.
    - regex (`regex.nim`): `mkRegex(s)` = `to_re` (`:56`), `matches(s, r): Z3Bool`
      = `in_re` (`:93`), `mkRegexEmpty`/`mkRegexFull`/`mkRegexAllChar`,
      `star`/`plus`/`option`/`complement` (`:101`–`:113`),
      `concat`/`union`/`intersect` varargs (`:130`–`:132`),
      `loop(r, lo, hi)` / `power(r, n)` / `range(lo, hi)` (`:138`/`:145`/`:151`).
      So S6's `to_re`/`in_re` map to **`mkRegex`/`matches`**, and `{n,m}` maps to
      `loop`, `[a-z]` to `range`.
  - **mkString → Z3_mk_lstring: confirmed, with a load-bearing caveat.**
    `mkString(s)` does call `Z3_mk_lstring(ctx.raw, cuint(s.len), s.cstring)`
    (`strings.nim:57-58`) — the RFC/ADR claim `Z3_mk_lstring(ctx, nimStr.len,
    nimStr.cstring)` is **accurate** (modulo the `cuint` cast). BUT the doc
    comment (`strings.nim:17`) is explicit: it carries "**the bytes of `s`**."
    `Z3_mk_lstring` maps each input **byte** to one Z3 character. For an ASCII
    string byte==codepoint and everything the RFC says holds. For a multi-byte
    UTF-8 literal it does **not**: `mkString("é")` feeds bytes `0xC3 0xA9`, so the
    Z3 string has **length 2** with codepoint values `[195, 169]` — *not* length
    1 with U+00E9 (233). **This contradicts the RFC/ADR-amendment claim that
    `mkString("é").len == 1` (== `runeLen`).** The real invariant is
    `mkString(s).len == s.len` (byte count) for all `s`, and the codepoint
    *values* of non-ASCII literals are raw UTF-8 byte values, not Unicode scalar
    values. ADR-0006 is written to the **true** semantics (see that ADR's "Reality
    note") and adopts the **byte-faithful** model on top of them; S2's
    `s == "é"; s.len == 1` DoD test as written in the RFC would **FAIL** (it is
    SAT only at `s.len == 2`). S2 implementers must flip that expectation. There is
    **no `Z3_mk_u32string`** in this FFI (grep: 0 hits), so there is no scalar-value
    literal constructor available; the byte-as-character behavior is the only
    literal path — which is exactly why the model is byte-faithful (the ≤ 0xFF
    free-var constraint extends that byte-faithfulness to free variables). Since the
    base char model is already bytes 0..255, S7a's `bytes(s)` is a trivial identity
    view, not a `fromCode`/`toCode` UTF-8-decode subsystem.
  - **replaceAll / regex-replace version gates: confirmed present.** Both
    `when defined(z3WithSeqReplaceAll)` (`sequence.nim:205`, wrapping
    `replaceAll`, `Z3_mk_seq_replace_all`) and `when defined(z3WithSeqReplaceRe)`
    (`regex.nim:193`, wrapping the regex-replace, `Z3_mk_seq_replace_re`) exist,
    with matching FFI gates in `ffi.nim:3110`/`:3115`. **Drift:** the RFC names
    the regex-absent symbol `Z3_mk_seq_re_replace_all`; the real FFI name is
    **`Z3_mk_seq_replace_re`** (words transposed; no `_all` suffix). S5/S6b error
    messages should cite the real symbol.
  - **Path / premise drift table:**

    | RFC reference (Cluster S) | Reality | Action for S1–S11 |
    |---|---|---|
    | `tests/symex/tphase15_S*.nim`, `tests/smt/tregex_parser.nim` | Flat layout; convention is `tests/<file>.nim`, established phase15 files are **`tests/tsymex_phase15_<CYCLE>_<topic>.nim`** (e.g. `tsymex_phase15_F9c_variant_float.nim`). No `tests/smt/` or `tests/symex/` dir. | Name S-cycle tests `tests/tsymex_phase15_S1_typebridge.nim` etc.; register in `proptest.nimble`. |
    | `symex_settings.nim` (S5) | **Does not exist.** `SymexSettings` is defined in **`smt/types.nim:518`**; `defaultSymexSettings()`/`withSymexSettings`/`+` also there (`:878`/`:895`). | S5 adds `maxSplitParts` to `SymexSettings` in `types.nim`, not a new file. |
    | `SymexSettings.maxSplitParts` / `maxBytesEncodingLen` (S5/S7a) | **Not present.** Current fields: `integerSemantics, queryRLimit, maxFrontierSize, maxCallDepth, maxLoopUnwind, acceptUnknownAsCovered, defectExclusions, inlinePolicy` (8 total — matches Z3d's "all 8 fields" merge). The handoff "Settings family" list (`maxSplitParts=8`, `maxBytesEncodingLen=32`, …) is a **locked decision, not yet in the type**. | S5 adds `maxSplitParts`; S7a adds `maxBytesEncodingLen`. The Z3d `+` merge + `withSymexSettings` must gain arms for each new field (currently merges exactly the 8). |
    | `regex_parser.nim` (S6a) standalone module | Does not exist (grep: 0 hits, incl. `_deps`). | S6a **creates** `src/proptest/smt/regex_parser.nim` as net-new (the RFC's intent), test `tests/tsymex_phase15_S6a_regex_parser.nim`. It is a Nim-regex→`Z3Regex` translator built on the `regex.nim` combinators above. |
    | `seZ3VersionMissing` error kind (S5/S6b preamble) | **Not in the `SymexErrorKind` enum** (`types.nim:441-459`). The enum has `seUnsupportedStringOp, seUnsupportedRegex, seZ3StringIncomplete, seBytesSymbolicLength, seBytesLengthTooLarge, seByteIndexUnsupported, seByteIterUnsupported, seUnsupportedTableValType, seUnsupportedSetCharInterop, seNestedSeqUnsupported`. | S5 (first user) must **add `seZ3VersionMissing`** to the enum, or reuse `seUnsupportedStringOp`/`seZ3StringIncomplete`. Decide at S5; the RFC assumes it pre-exists — it does not. |
    | `seParseIntPreE` error kind (S10a) | **Not in the enum.** | S10a must add it (a `sevHint`), or fold its intent into an existing hint. Net-new. |
    | `seBytesBeyondBMP` (S7a, RFC line ~3520) | **Not in the enum** (only `seBytesSymbolicLength`/`seBytesLengthTooLarge` exist). | S7a adds it if the BMP cap is enforced as a distinct kind. |
    | `Table[string, V]` V∉{int} → `seUnsupportedTableValType` "at parse time via `dsl_typebridge.nim`" (preamble) | Today this is a **runtime `raise ValueError`** inside `allocateSym` (`runtime.nim:436-443`), not a parse-time classified error. | S1's type-bridge sweep should move this to a parse-time `seUnsupportedTableValType` per the preamble; until then it is an uncaught `ValueError`, not `sxUnknown`+classified error. Flag for S1. |
    | `string.len` routing guard: "if current code routes to `iekSeqLen`, add a guard" (S1/S3) | `s.len` interception is at `dsl_parser.nim:620` (`calleeSym.strVal in ["len","card"]`); the `[]`/`contains` paths at `:625`/`:634`/`:655`. The receiver-type discrimination the RFC wants must be threaded here. | Real S1 work is in `dsl_parser.nim` around `:620-655`, not a hypothetical separate router. |
    | `at`/`substr` out-of-bounds → empty string "per Z3 spec" (S3) | **Confirmed** (`sequence.nim:158-160`: "Out-of-range offsets / lengths yield the empty sequence"). | No drift — RFC correct. |
    | `find` → `Z3_mk_seq_index`, −1 when absent (S4) | **Confirmed** but the proc is named **`indexOf`** (`sequence.nim:180`), not `find`. | S4 lowers `strutils.find` → `indexOf`. |
    | `mkString(nimStr)` via `Z3_mk_lstring(ctx, nimStr.len, nimStr.cstring)` (S2 GREEN, ADR Decision) | **Confirmed** call shape; **but** the byte-faithful semantics above invalidate the `len==runeLen`/`"é".len==1` claim. | See the mkString caveat above; S2 DoD test must assert `s.len == 2` for `"é"`, not `== 1`. ADR-0006 adopts the byte-faithful model. |
    | `s.high` / `for c in s` → `seByteIndexUnsupported`/`seByteIterUnsupported` (S3, old codepoint draft) | Under byte-faithful (≤0xFF chars), **`s.high` IS SUPPORTED** (Z3 position == Nim byte, `len-1`). **`for c in s` is NOT** — corrected at S3: the objection is *unbounded symbolic iteration length*, not byte/codepoint. | S3 supports `s.high` (do **not** emit `seByteIndexUnsupported`). `for c in s` classifies `sxUnknown` for the unbounded-iteration reason (NOT `seByteIterUnsupported`). The two kinds stay in the enum but are unused. |

  - **S1 — SHIPPED.** String type-bridge scaffolding. Added the **17 `iekStr*`
    IR variants** (`iekStrLen/At/Substr/Find/Contains/StartsWith/EndsWith/
    Replace/ReplaceAll/Split/Join/Match/Bytes/Concat/IntToStr/StrToInt/
    Unsupported`) to `types.nim` with a **uniform payload** (`strArgs:
    seq[IRExpr]` + `strOp: string`) and a `StrOpKinds` set + `mkStrOp`
    constructor, so the per-arm ripple collapses to a single `of StrOpKinds:`
    case in every dispatch. **Exhaustiveness ripple was 6 arms** (not the
    feared 12–14, because the uniform-payload set lets each `case e.kind`
    handle all 17 kinds in one arm): `render` (types.nim), `canonicalize`
    (canonicalize.nim), `tryEvalInterval` + `collectVarRefs` (abstraction.nim —
    `collectBanFromExpr` already had an `else`), `probeProto` + `lower` +
    `emitExpr` ripple... concretely the compiler-required arms were:
    types.`render`, canonicalize.`canonicalize(IRExpr)`,
    abstraction.`tryEvalInterval`, abstraction.`collectVarRefs`,
    runtime.`probeProto`, runtime.`lower`, dsl_parser.`emitExpr` (the
    collector/`else`-bearing dispatches needed none). Added the `smkStr*`
    `StdlibModelKind` family (net-new) + the `of itString:` dispatch in
    `getStdlibModelFor`. Parser: an **`itString`-receiver call guard** in
    `dsl_parser.nim` (before the seq-`len` and user-proc paths) routes every
    string call to its `iekStr*` kind (unrecognised → `iekStrUnsupported`) —
    this is the `string.len` routing guard, and it fixes the pre-existing
    `getImpl`-on-`len` compile crash. The walker `lower(StrOpKinds)` raises a
    new `SymexUnsupportedStringOpError`, caught at the `runSymex` boundary →
    `sxUnknown` + `seUnsupportedStringOp` (ADR-0006, Invariant 3).
    - **Bonus fix (was a latent Phase-5 gap, NOT just a stub):** free-`string`
      **`s == "lit"` equality did not actually work** — Phase 5 only wired
      *table-key* string equality; a bare `s == "hello"` fell into the BV
      comparison `else` and crashed on `eqBV on non-BV SymVal`. S1 adds a real
      `cmpString` (`svString` arm in both comparison branches of `lower`) using
      Z3 `Z3String ==`/`!=`. Lexicographic `<`/`<=` raise the classified
      string-unsupported error (deferred to S3). This is what makes the S1 RED
      test's `s == "hello"` → `sxSat` pass.
    - **≤0xFF byte-faithful constraint — DEFERRED to S3** (decision recorded).
      S1's only SUTs use `s == "hello"`, where equality pins each char to a
      literal byte, so the soundness constraint is not yet *needed*; and
      `allocateSym(itString)` has **no solver/constraint sink** threaded through
      it (it is a pure `SymVal` producer), while the assertion machinery is set
      up in S3 alongside the first real positional op where the constraint
      becomes load-bearing. Asserting a regex/char-range membership now would
      also risk the Z3 string-solver hang the bounded runner guards against,
      untested. A `# byte-faithful ≤0xFF constraint: deferred to S3` marker sits
      at `runtime.nim:allocateSym(itString)`.
    - **`Table[string,V]` V≠int guard — left as the existing runtime
      `ValueError` for now** (NOT moved to a parse-time
      `seUnsupportedTableValType`). S1's RED test does not exercise it, and
      moving it risks the table-test regression surface for no S1-visible
      benefit; folded into a later S-cycle. Flagged here so it isn't lost.
    - Test `tests/tsymex_phase15_S1_typebridge.nim` (2 tests: `s == "hello"` →
      `sxSat` witness `"hello"`; `s.len > 3` → `sxUnknown`, clean) green on c +
      cpp. Regression clean (phase5 seq/table/models/hashset, phase14
      multivariant, F2/F6, canonicalize, phase1_dsl), no hangs. Registered in
      `proptest.nimble` after F9c.
  - **S2 — SHIPPED.** String literal lifts. **No production source change was
    needed** — S1 had already wired the whole literal path: the parser lowers
    `nnkStrLit`/`nnkRStrLit`/`nnkTripleStrLit` → `mkStrLit(n.strVal)` →
    `iekStrLit`, and `lower(iekStrLit)` → `SymVal(svString, mkString(e.sval))`
    (`Z3_mk_lstring`, byte-faithful NUL-safe length-prefixed encoding), with
    `cmpString` (S1 bonus) handling `s == "lit"` and witness extraction via
    `evalStr`. S2's deliverable was confirmation + byte-faithful coverage. Test
    `tests/tsymex_phase15_S2_strlit.nim` (6 tests): `s == "hello"`/`""`/`"\n"`
    (1 byte)/`"\x61"`→`"a"` all `sxSat` with the exact witness; contradictory
    literals (`s == "hello" and s == "world"`) → `sxUnsat`; and the
    **byte-faithful multi-byte** case `s == "é"` → `sxSat` with the extracted
    Nim witness asserted `== "é"` **and `.len == 2`** (Nim byte count — confirms
    `Z3_mk_lstring` maps each UTF-8 byte `[0xC3, 0xA9]` to one Z3 char, NOT a
    length-1 scalar; the RFC's `== 1` claim is corrected). Escapes are decoded
    by the Nim semchecker before `strVal`, so no parser escape handling is
    needed. **A symex `s.len` constraint is NOT used in S2** — that op is
    deferred to S3 (`iekStrLen` still raises `seUnsupportedStringOp`); S2 asserts
    byte-faithfulness on the *extracted Nim witness* instead. Green on c + cpp
    (6/6). Regression clean (S1 typebridge, phase5 seq/table, F2 float literals),
    no hangs. Registered in `proptest.nimble` after S1.
  - **S3 — SHIPPED.** String len/index/slice + the ≤0xFF byte-faithful
    constraint (the deferred-from-S1 soundness mechanism). Test
    `tests/tsymex_phase15_S3_strindex.nim` (7 tests) green on c + cpp (7/7 each).
    - **≤0xFF constraint mechanism — regex membership, does NOT hang.** At
      `allocateSym(itString)` (the S1 deferral marker), the free string asserts
      `matches(s, star(range(mkString("\x00"), mkString("\xff"))))` — i.e.
      `s ∈ (re.range '\x00' '\xff')*` — threaded into the path condition via the
      same `pcOut` sink that carries `seqLen >= 0` and the table/set size floors.
      `range(lo, hi: string)` is the nim-z3 ergonomic overload (asserts each
      endpoint is one byte; `"\x00"`/`"\xff"` are single-byte lstring endpoints);
      `star`/`matches` are the `regex.nim` combinators. **This is the highest
      hang-risk code in the cluster (Z3 string-solver + regex), but it did NOT
      hang**: every S3 test and the full regression set completed well within the
      bounded-runner budget (no raise of the timeout, no exit-137). No fallback
      (per-op-only constraint / bounded-length) was needed.
    - **`s[i]` → char bridge IMPLEMENTED (not deferred).** `s[i]` lowers to a Nim
      `char` (`svBV8` unsigned, per Z3c's `char` classification) via
      `at(s, i)` (1-char Z3String) → `toCode(.)` (Z3Int codepoint == byte value
      under ≤0xFF) → `intToBv[8]`. So `s[i] == 'c'` compares two `svBV8` values
      through the existing mixed-int comparison path. Out-of-range `i` makes `at`
      the empty string and `toCode` return −1 (→ BV8 0xFF) — no crash (Z3 spec).
    - **`s[a..b]` → `iekStrSubstr`** = Z3 `substr(s, lo, hi-lo+1)` (the
      (offset, length) convention); the parser folds `..<` to an inclusive `hi`.
      Both the `[]`-call form and the `nnkBracketExpr` form are handled (typed AST
      emits either shape by context). **`s.high`** is parser-level `len(s) - 1`
      (byte index of last byte) — supported, never classified unsupported.
    - **`for c in s` — honestly classified unsupported (reality matches docs).**
      The reconciliation/ADR claim that `for c in s` is "supported" under
      byte-faithful is **over-promised**: byte-faithful removes the *semantic*
      (byte/codepoint) objection but NOT the *unbounded-iteration* one — the loop
      count is the string's unknown symbolic length, which has no sound bounded
      encoding. S3 classifies it `mkUnsupported` with an HONEST reason
      ("unbounded symbolic iteration length, not a byte/codepoint mismatch") at
      parse time (BEFORE parsing the loop body, so the body's loop-var references
      don't trip user-proc registration), yielding `sxUnknown` (Invariant 3,
      never a silent UNSAT). It does NOT emit `seByteIterUnsupported`. **Doc fix:
      the §F-S "all SUPPORTED including `for c in s`" line below is corrected — the
      five positional ops (`len`/`s[i]`/`s[a..b]`/`s.high`) are supported;
      `for c in s` is honestly unsupported for the unbounded-iteration reason.**
    - **Exhaustiveness arms:** `lower(StrOpKinds)` split into `iekStrLen`/
      `iekStrAt`/`iekStrSubstr` + a `StrOpKinds - {those}` residual-raise arm;
      `probeProto` likewise gained the three protos (svInt / svBV8 / svString) +
      residual. Parser: `nnkBracketExpr` `itString` arm + `[]`/`high` handling in
      the string-call guard.
    - **S1 test update:** `tsymex_phase15_S1_typebridge.nim`'s `s.len > 3` case
      flipped `sxUnknown` → `sxSat` (the op is live as of S3; was a stub in S1).
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, phase5_seq/
      table/hashset, phase15_F2/F6, canonicalize, phase14_multivariant_walker.
  - **S4 — SHIPPED.** `find` / `contains` / `startsWith` / `endsWith` substring
    predicates + search, lowered direct (no stdlib model lookup). Test
    `tests/tsymex_phase15_S4_strpred.nim` (8 tests) green on c + cpp (8/8 each).
    - **Parser + stdlib_models work was already in place from S1's scaffolding.**
      S1 registered the full `smkStr*` family AND wired the `getStdlibModelFor`
      `itString` map (`contains`/`startsWith`/`endsWith`/`find`→the matching
      `smkStr*`) AND the parser's `itString`-receiver call-guard dispatch
      (`smkStrContains`→`iekStrContains`, etc., `dsl_parser.nim:687`). So S4's
      ONLY production change is the **runtime lowering** — no parser/model edit.
    - **`sub in s` routing CONFIRMED → `iekStrContains` (string path), NOT
      `iekContains`.** In typed AST `sub in s` semchecks to `contains(s, sub)`
      (an `nnkCall`, never `nnkInfix` — `binopForInfix` has no `in` case, which is
      why `42 in set` works only via the desugared `contains` call). For an
      `itString` receiver that call hits the line-653 string-call guard FIRST and
      routes through `smkStrContains`→`iekStrContains`, before the line-712
      `contains`/`hasKey` guard (which only fires for `itTable`/`itSet`). The
      seq/table/set `in` path is untouched — regression `phase5_seq`/`table`/
      `hashset` all green. Test `inEll` (`"ell" in s and s == "hello"`) → sxSat.
    - **Runtime lowering (real nim-z3 names from `sequence.nim`, verified):**
      `iekStrContains` → `SymVal(svBool, bo: contains(recv.str, sub.str))`
      (`Z3_mk_seq_contains`); `iekStrStartsWith` → `startsWith(recv.str,
      prefix.str)` (`Z3_mk_seq_prefix`; nim-z3 arg order `(a, prefix)` already
      matches Nim's `(s, prefix)`); `iekStrEndsWith` → `endsWith(recv.str,
      suffix.str)` (`Z3_mk_seq_suffix`); `iekStrFind` → `SymVal(svInt, zi:
      indexOf(recv.str, sub.str))` — the no-start overload (starts at 0),
      `Z3_mk_seq_index`, returns the **byte** offset (== position offset under
      ≤0xFF, no codepoint handling) or **−1** when absent (a valid SMT int, no
      crash). The RFC said `find`; the real nim-z3 name is **`indexOf`**.
    - **Exhaustiveness arms:** `lower(StrOpKinds)` and `probeProto(StrOpKinds)`
      each split out `iekStrContains`/`iekStrStartsWith`/`iekStrEndsWith` (svBool
      protos via `mkBool(true)`) + `iekStrFind` (svInt proto) from the residual-
      raise arm; the residual set is now `StrOpKinds - {iekStrLen, iekStrAt,
      iekStrSubstr, iekStrContains, iekStrStartsWith, iekStrEndsWith, iekStrFind}`.
    - **Test SUTs need `import std/strutils`** — Nim's `contains`/`find`/
      `startsWith`/`endsWith` on `string` live in strutils, not system.
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
      phase5_seq/table/hashset (the `in`/contains paths — string guard did NOT
      break seq/table/set membership), phase15_F2_float_literals.
  - **S5 — SHIPPED.** `replace` / `replaceAll` / `split` / `join` — the densest,
    highest-hang-risk Cluster-S cycle. **No hang** at any point (c + cpp, full
    regression all inside the bounded-runner budget). Test
    `tsymex_phase15_S5_strops.nim` (7 tests) green c+cpp 7/7.
    - **New error kind + setting.** `seZ3VersionMissing` added to the
      `SymexErrorKind` enum (`seZ3StringIncomplete` was ALREADY present — not
      net-new as the drift table guessed). `maxSplitParts: int` (default `8`)
      added to `SymexSettings` (`types.nim`), to `defaultSymexSettings()`, and
      to the `+` merge — the settings ripple did NOT break the
      `withSymexSettings` tests (phase13_verdict_primitives, F8_smoke both green).
    - **replace (tractable).** `iekStrReplace` → `replace(recv.str, old.str,
      neu.str)` (`Z3_mk_seq_replace`, FIRST-occurrence) → svString. (Note: Nim's
      `strutils.replace` is global, but the byte-faithful Z3 primitive this
      cycle models is the first-occurrence op per the S5 spec.)
    - **replaceAll (version-gated → seZ3VersionMissing on THIS build).**
      `z3WithSeqReplaceAll` is NOT defined in this dev image (Z3 4.15.0), so the
      `when defined(z3WithSeqReplaceAll):` MANDATORY guard takes its `else`
      branch: raise new `SymexZ3VersionMissingError` → caught at the `runSymex`
      boundary → `sxUnknown` + `errors[0].kind == seZ3VersionMissing` (Invariant
      3 — never a crash, never silent UNSAT). The unguarded `replaceAll` symbol
      does not exist on this build, so the `when` guard is load-bearing for
      compilation. Nim has no `replaceAll` stdlib proc, so the test SUT defines a
      local `replaceAll` shim (the parser dispatches on the callee NAME for an
      `itString` receiver → `smkStrReplaceAll`→`iekStrReplaceAll`; the body never
      runs under symex).
    - **join (tractable, over a CONCRETE seq[string]).** `iekStrJoin` →
      `joinStrSeq`: a Z3 `concat` chain with `sep` interleaved
      (`p0 ++ sep ++ p1 ++ … ++ pn`). Requires the receiver's `seqLen` to be a
      Z3 numeral (`getAstKind == akNumeral`); a symbolic-length join →
      `seZ3StringIncomplete`. New parser guard routes `xs.join(sep)`
      (`seq[string]` receiver, which `classifyType` rejects) to `iekStrJoin`
      BEFORE the itString-receiver classify.
    - **split — special cases only; general path classified (NO quantifier, NO
      hang).** `iekStrSplit` dispatches on IR-level concreteness of the operands:
      **(a) empty-sep** (sep is literal `""`): byte-faithful single-BYTE parts
      computed in Nim → `split("abc","") == @["a","b","c"]`. **(b)
      concrete-inline** (receiver AND sep are string literals): split computed in
      Nim, emitted as a concrete `svSeq` of literal parts — NO Z3 quantifier.
      **(c) general** (symbolic receiver or sep): the RFC's
      `join(parts,sep)==s` + universal `not contains(parts[i],sep)` +
      `seqLen<=maxSplitParts` encoding is a universal quantifier over a symbolic
      `seq[string]` — the cluster's biggest hang risk — so it is CONSERVATIVELY
      classified `seZ3StringIncomplete` → `sxUnknown` (Invariant 3) via new
      `SymexZ3StringIncompleteError`, NOT encoded. The DoD-mandated "special
      cases work, general → sxUnknown" outcome. Concrete-inline detection is at
      the IR level (`strArgs[0].kind == iekStrLit`), NOT via Z3 `isStringValue`
      (which is absent from this nim-z3 — there is only `Z3_is_string` via
      `getStringLength`/`checkStringLiteral`); test SUTs call `split` on string
      LITERALS so the receiver IR is `iekStrLit`.
    - **seq[string] support — PARTIALLY added (only what S5 exercises).** A
      concrete `svSeq[string]` is built by `mkConcreteStrSeq`
      (`mkConstArray[Z3Int,Z3String]("")` + `store` per part; `seqLen` pinned).
      Added `itString` arms to `allocateSeqDataRaw` (backing array) and to the
      statement-level seq-INDEX walker (`parts[i]` → svString element via
      `select`, compared through `cmpString`). `.len` works via the existing
      `iekSeqLen` svSeq arm. **NOT added: seq[string] WITNESS extraction**
      (`extractSeqElements`/`emitTyAndReader`) — split results live only in env
      locals, never in a SUT parameter (witness extraction iterates `params`
      only), so it is genuinely unreachable in S5; a `seq[string]` SUT param
      would still error cleanly at macro time. Left for a future cycle that
      needs it (no untested gold-plating).
    - **Exhaustiveness arms:** `lower` and `probeProto` split
      `iekStrReplace`/`iekStrReplaceAll`/`iekStrSplit`/`iekStrJoin` out of the
      `StrOpKinds` residual-raise arm (replace/replaceAll/join get svString
      protos; split produces an svSeq consumed only via `.len`/index so needs no
      comparison proto). Two new boundary catches
      (`SymexZ3VersionMissingError`→seZ3VersionMissing,
      `SymexZ3StringIncompleteError`→seZ3StringIncomplete) added before the
      generic `Z3Error` catch.
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
      S4_strpred, phase5_seq, phase5_table, phase15_F2_float_literals,
      phase13_verdict_primitives + phase15_F8_smoke (the two `withSymexSettings`
      exercisers — confirming the `maxSplitParts` field ripple is clean).
      Walker version unchanged at `"5"`. Registered after S4.
  - **S6a — SHIPPED.** Standalone Nim-regex → `Z3Regex[Z3String]` parser
    (`src/proptest/smt/regex_parser.nim`), NO walker/`symex.nim` import, NO Z3
    solving — a pure recursive-descent translator over the `z3/regex`
    combinators. Test `tsymex_phase15_S6a_regex_parser.nim` (21 tests: 17
    supported + 4 rejected) green c+cpp 21/21. Regression S4/S5 clean.
    - **Real nim-z3 regex combinators used (vs the RFC/drift-table guesses).**
      All confirmed in `_deps/z3/src/z3/regex.nim`: `mkRegex(Z3Seq)`,
      `star`/`plus`/`option`/`complement` (unary), `concat`/`union`/`intersect`
      (varargs, `≥1` required), `loop(r, lo, hi)` (={n,m}), `power(r, n)`
      (=exact {n}), `range(lo, hi: string)` / `range(lo, hi: Z3String)`
      (=[a-z]). `mkRegexEmpty`/`mkRegexFull`/`mkRegexAllChar` exist — but the
      byte-faithful `.` does **NOT** use `mkRegexAllChar` (see below).
    - **Import gotcha (logged).** The `union`/`intersect`/`concat` **varargs
      templates** expand `checkErr` + raw FFI symbols in the *caller's* scope,
      so `regex_parser.nim` must additionally `import z3/error` (checkErr) and
      `import z3/ffi` — importing only `z3/regex`/`z3/strings`/`z3/context`
      fails to compile ("attempting to call undeclared routine: 'checkErr'").
    - **Result idiom (no `results` dep).** The repo has no `results` package;
      matching its `isOk`-duck-typed convention (`engine/eval.nim`, `fuzz.nim`),
      the parser returns `RegexParseResult{isOk: bool, regex: Z3Regex[Z3String],
      error: string}`. Rejected/malformed → `isOk == false` + descriptive
      `error` (the three rejected families embed `"seUnsupportedRegex"` in the
      message so S6b can classify directly).
    - **Byte-faithful `.`/`\w`/`\s`/classes (ADR-0006, ≤0xFF).** `.` =
      `range('\x00','\xFF')` (NOT `mkRegexAllChar`, whose full-Unicode basis
      would admit codepoints >0xFF that don't round-trip to a Nim byte — the
      byte-range keeps `.` in the same ≤0xFF alphabet as every other construct).
      `\d` = `range("0","9")`; `\w` = union of `[A-Za-z0-9_]`; `\s` = union of
      `' ' \t \n \r \f \v` (standard PCRE set). `[a-z]` ranges use the
      **`Z3String`-typed** `range(mkString, mkString)` (the `(string,string)`
      overload asserts a single ASCII codepoint and rejects 0x80..0xFF). `[^…]`
      = `intersect(complement(class), range('\x00','\xFF'))` so the negated
      class still matches exactly one byte (bare `complement` admits any-length
      sequences). `(...)` capturing and `(?:...)` non-capturing are both
      transparent for language membership. `{n,}` = `power(r,n) ++ star(r)`.
    - **Rejected → isErr** with `seUnsupportedRegex` in the message:
      backreferences `\1`..`\9`; lookahead `(?=…)`/`(?!…)`; named groups
      `(?P<n>…)` / `(?<n>…)` / `(?'n'…)`. Registered after S5; walker version
      unchanged at `"5"` (no walker touched).
  - **S6b — SHIPPED.** Regex match walker integration — wires S6a's
    `parseNimRegexToZ3Regex` into `runtime.nim`. Test
    `tsymex_phase15_S6b_regex.nim` (5 tests) green c+cpp 5/5.
    - **NO HANG (the key risk).** Regex membership on a FREE string under the
      ≤0xFF constraint (S3) is the cluster's highest hang risk; every S6b test
      and the full regression completed well inside the bounded-runner budget
      (no exit-137, no timeout raise). The byte-faithful char-range constraint
      keeps membership decidable, exactly as S6a/S3 predicted.
    - **`rePatternStr` carried in the existing `strOp` field (option a, least
      disruption).** Decision: reuse the uniform-payload `strOp: string` to hold
      the raw `re"…"` pattern for `iekStrMatch`/`iekStrFindRe`/`iekStrReplaceRe`
      — NO new field, NO recursive `IRRegex` type. `strArgs == [recv]` (match/
      findRe) or `[recv, replacement]` (replaceRe). Bonus: `canonicalize` already
      folds `strOp` into the content-addressed cache key, so distinct patterns
      content-address distinctly with zero extra work.
    - **`matches` API confirmed; `iekStrFindRe` DEFERRED (no indexOf-on-regex).**
      `matches(Z3String, Z3Regex[Z3String]): Z3Bool` (`regex.nim:93`,
      `Z3_mk_seq_in_re`) is real — `iekStrMatch` → `SymVal(svBool, matches(...))`.
      nim-z3's `indexOf` (`sequence.nim:180`) takes a `Z3Seq` sub ONLY — there is
      **no `indexOf`/regex overload** — so `s.find(re"…")` has no sound Z3
      primitive and is classified `seUnsupportedRegex` (sxUnknown) via a new
      `SymexUnsupportedRegexError` (documented S6b deferral; the pattern is still
      parsed first so a rejected pattern reports the precise S6a reason). No SAT
      test asserts findRe — only the deferral path exists.
    - **Pattern extraction from `re"…"`.** In the typed AST a `re"…"` literal is
      `nnkCallStrLit(Sym "re", RStrLit "<pat>", Curly(Sym "reStudy"))`; the
      surrounding `match`/`find`/`contains` call carries a trailing default
      `start` `nnkIntLit 0` (dropped), while `replace` has the replacement as its
      other string arg. The parser (`dsl_parser.nim`, in the itString-receiver
      block, BEFORE the uniform `sArgs` parse that chokes on `nnkCallStrLit`)
      scans args ≥2 for the `re`/`rex` CallStrLit, lifts `[1].strVal` into
      `strOp`. `contains(s, re"…")` routes to `iekStrMatch` (same membership
      predicate). A non-literal (symbolic) Regex value has no CallStrLit and
      falls through → `iekStrUnsupported` (can't parse at walk time).
    - **`replaceRe` version-gate (OFF on this build).** `iekStrReplaceRe` →
      `when defined(z3WithSeqReplaceRe):` `replaceRe(recv, re, repl)`
      (`regex.nim:194`, `Z3_mk_seq_replace_re`); `else:`
      `SymexZ3VersionMissingError` → sxUnknown + `seZ3VersionMissing`. Confirmed
      the gate is NOT defined (grep: the dev image is Z3 4.15.0; the symbol is
      absent), so the `else` branch is exercised by the test. The `when` guard is
      load-bearing (the `replaceRe` proc only exists under the gate).
    - **Exhaustiveness arms:** `lower` split `iekStrMatch`/`iekStrFindRe`/
      `iekStrReplaceRe` out of the `StrOpKinds` residual-raise arm (match→svBool;
      findRe→raise deferral; replaceRe→svString or version-raise). `probeProto`
      gained match→svBool, findRe→svInt, replaceRe→svString protos.
      `abstraction.tryEvalInterval`'s explicit string-op list gained the two new
      kinds (the only non-set string dispatch); `canonicalize`/`types.render`/
      `dsl_parser.emitExpr` use `of StrOpKinds:` set arms (no edit needed). New
      `SymexUnsupportedRegexError` catch added at the `runSymex` boundary →
      `seUnsupportedRegex`. Walker version unchanged at `"5"`.
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
      S4_strpred, S5_strops, S6a_regex_parser, phase5_seq,
      phase15_F2_float_literals. Registered after S6a. **Next: S7a.**
  - **S7a — SHIPPED.** `bytes(s)` byte-faithful **trivial byte-view** — NOT the
    RFC §S7a multi-byte UTF-8 BMP `ite`-encoding (that is rejected under
    byte-faithful, ADR-0006). Every Z3 string char is ALREADY one byte (≤0xFF,
    S3), so `bytes(s)` is the identity view: an `svSeq` of `svBV8`,
    `seqLen == len(s)` (**EQUAL**, not `>=` — byte count == char count), each
    `bytes[i] == intToBv[8](toCode(at(s, i)))` (reuses S3's exact at→toCode→BV8
    bridge). Test `tsymex_phase15_S7a_bytes.nim` (5 tests) green c+cpp 5/5.
    - **Concreteness detected at the IR level (mirrors S5 split):** a string
      LITERAL receiver (`iekStrLit`) has a known byte count
      (`recvIR.sval.len`); a bare `string` parameter (symbolic length) →
      `SymexBytesSymbolicLengthError` → `sxUnknown` + `seBytesSymbolicLength`.
      No Z3 numeral-extraction needed — the concrete-length cases call `bytes`
      on a LITERAL while the `string` param is pinned (the S5 split idiom).
    - **New setting `maxBytesEncodingLen: int = 32`** added to `SymexSettings`
      (`types.nim`), `defaultSymexSettings()`, and the `+` merge — the same
      ripple S5 did for `maxSplitParts`. Threaded into `lower` via a per-run
      `currentMaxBytesEncodingLen` threadvar (set in `runSymexImpl`, mirroring
      F7's `extractionErrors`) since `lower` has no settings parameter. Under
      byte-faithful this caps the concrete CHAR count directly (1 byte/char,
      NOT `/3`). A concrete length above it → `SymexBytesLengthTooLargeError` →
      `sxUnknown` + `seBytesLengthTooLarge`. F8_smoke (the `withSymexSettings`
      exerciser) green — settings ripple clean.
    - **`seBytesBeyondBMP` UNREACHABLE — omitted.** A free char is ≤0xFF by
      construction and a literal char is a raw byte 0..255, so `toCode` always
      fits BV8; no multi-byte branch is ever needed. The error kind is NOT
      added (documented unreachable). The RFC's "codepoint > 0xFFFF" test is
      dropped for the same reason.
    - **One supporting fix:** `classifyType` (`dsl_typebridge.nim`) gained a
      `"byte"` arm (`= uint8` → `tInt(8, unsigned)`); `bytes` returns
      `seq[byte]` and the seq-element classify previously errored on the `byte`
      alias (only `uint8`/`char` were mapped). `byte` IS `uint8` — a real gap,
      not scope-creep.
    - **Exhaustiveness:** `iekStrBytes` split out of `lower`'s
      `StrOpKinds - {…}` residual-raise arm (added to the exclusion set);
      `probeProto`'s `none(SymVal)` residual already covers it (produces an
      svSeq, consumed only via `.len`/index — no comparison proto). Two new
      boundary catches added before the generic `Z3Error`. Walker version
      unchanged at `"5"`.
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
      S4_strpred, S5_strops, S6a_regex_parser, S6b_regex, phase5_seq,
      F8_smoke, F2_float_literals. Registered after S6b. **Next: S7b.**
  - **S7b — SHIPPED.** Z3-string regression smoke + determinism doc. **No new
    source files** (verification-only cycle; no fixes were needed). New test
    `tests/tsymex_phase15_S7b_smoke.nim` (8 tests) green c+cpp 8/8 — a hermetic
    in-process smoke exercising MULTIPLE string ops TOGETHER on the same/related
    SUTs to catch cross-op state-threading bugs from the S1–S7a multi-file edits:
    (1) a multi-op SUT `s.len==5 and s[0]=='h' and s.contains("ell") and
    s.startsWith("he")` → sxSat with a witness that round-trips through the
    runtime predicate; a second `len+slice+endsWith+find` SUT pinned to "world";
    (2) a concrete split+join round-trip AND a `bytes(literal)` check in ONE SUT;
    (3) a regex `match(re"[a-z]+")` SUT + a string-equality SUT; (4) a
    `withSymexSettings` exerciser on a STRING SUT (confirms the settings builder
    threads through for strings too, mirroring F8); (5) the ≤0xFF byte-faithful
    invariant (free `s` with `s.len==1` → single Nim byte); (6) an assertion that
    `symexWalkerVersion == "5"` (NOT bumped — that is S11).
    - **Finding (logged):** a bool-returning *string* helper proc does NOT inline
      under symex — even a trivial `proc p(s:string):bool = s=="hello"` called as
      `if p(s)` yields `sxUnknown` (the call isn't inlined into the path
      condition; outside S7b's scope). The S-cluster convention of inlining the
      condition directly in the SUT body sidesteps this; the smoke follows it and
      uses a textually-identical runtime predicate only for the witness
      round-trip check (the F8 (symex SUT, runtime predicate) split).
    - **Broad regression SWEEP (representative subset, all green c, no hangs / no
      exit-137):** ALL Cluster S — S1_typebridge, S2_strlit, S3_strindex,
      S4_strpred, S5_strops, S6a_regex_parser, S6b_regex, S7a_bytes; the L-cluster
      — l1_boundary, l2_untyped_template, l3_quote_do; a Cluster-F sample —
      F2_float_literals, F6_float_math, F8_smoke; and pre-existing string-bearing
      tests — phase5_seq, phase5_table, phase5_hashset, phase5_models,
      phase14_multivariant_walker, phase14_frontier_pruning. (No `tsymex_phase15_L*`
      tests exist; the L-cluster tests are lowercase `tsymex_phase15_l{1,2,3}_*`.)
    - **determinism.md updated:** new "String type-bridge: byte-faithful model +
      supported ops (Phase 15 Cluster S)" section (after the float type-bridge
      section, matching F8's tone) — covers the ≤0xFF byte-faithful model
      (Z3 char ≤0xFF == Nim byte, ADR-0006); byte-indexed `len`/`[i]`/`[a..b]`/
      `.high`; the supported-op list; the classified-unsupported ops + error-kind
      table (`for c in s`→explicit unbounded-iteration; `s[i]=c`/`add`/`toLower`/
      `toUpper`→`seUnsupportedStringOp`; `replaceAll`/regex-replace→`seZ3VersionMissing`
      on Z3 4.15.0; symbolic `split`/`join`→`seZ3StringIncomplete`;
      `bytes(symbolic-len)`→`seBytesSymbolicLength`; `bytes(>cap)`→`seBytesLengthTooLarge`;
      regex `find`→`seUnsupportedRegex`); and the Latin-1 witness-coverage limitation.
    - Walker version unchanged at `"5"`. Registered after S7a. **Next: S8.**
  - **S8 — SHIPPED.** `&` string concatenation. `iekStrConcat` (a StrOpKinds
    stub since S1) given its real lowering. **Parser `&` itString-guard (the
    load-bearing decision):** `&` is an INFIX operator, not a named call, so it
    arrives at `parseExpr`'s `nnkInfix` arm (line ~473) — where `binopForInfix`
    has NO `&` case and would `error("unsupported infix operator")` (this was the
    RED failure). S8 intercepts `&` THERE, **before** `binopForInfix`, gated on
    `n[0].strVal == "&" and classifyType(n[1]).ty.kind == itString and
    classifyType(n[2]).ty.kind == itString` → `mkStrOp(iekStrConcat, "&",
    @[lhs, rhs])`. The guard is purely **additive**: any non-itString operand
    (seq concat, other types) fails the `itString` check and falls through to
    `binopForInfix` exactly as before — and in fact symex never wired a parser
    `&` for SEQ concat at all (`binopForInfix` has no `&`; phase5_seq uses no
    `&`), so there was no seq-`&` path to break. **Chained `a & b & c`** is
    left-associative — the typed AST nests it as `(a & b) & c`, each `&` its own
    binary node, so recursion on the operands handles the chain with no special
    casing. **runtime `lower`:** split `iekStrConcat` out of the StrOpKinds
    residual-raise arm → `SymVal(kind: svString, str: concat(l.str, r.str))`.
    **nim-z3 concat API used: `concat(a, b)`** (`sequence.nim:141`,
    `Z3_mk_seq_concat`; the two-arg `&` sugar at `:143` and the lifted-string `&`
    at `strings.nim:197` are equivalent — `concat` chosen per the RFC/recon spec
    text). Both operands lower to svString via `lower` (a string-literal operand
    lowers through the existing `iekStrLit`→`mkString` path, so no separate
    literal coercion is needed). **`probeProto`:** `iekStrConcat` added to the
    svString-proto group (alongside replace/replaceAll/join) so `(a & b) ==
    "lit"` lowers its literal side as a string through `cmpString`; also added to
    the probeProto residual exclusion set. **Exhaustiveness arms:** `lower`
    (new `of iekStrConcat:` + added to residual exclusion), `probeProto`
    (svString group + residual exclusion) — 2 edited dispatches in runtime.nim;
    no types/canonicalize/abstraction edit (the uniform-payload StrOpKinds set
    arms already cover it). Byte-faithful (ADR-0006): concat is byte-wise, so
    `(a & b).len == a.len + b.len` (S3's `iekStrLen`) holds — tested SAT. Test
    `tsymex_phase15_S8_concat.nim` (5 tests: `s == "foo" & "bar"`→sxSat witness
    "foobar"; var concat `(a&b)=="hello" and a=="he"`→sxSat b=="llo"; chained
    `"a"&"b"&"c"=="abc"`→sxSat; additive `(a&b).len==a.len+b.len`→sxSat;
    contradiction `(a&b)=="xy" and a=="zzz"`→sxUnsat) green c+cpp 5/5.
    Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
    S4_strpred, S5_strops, S6a_regex_parser, S6b_regex, S7a_bytes, S7b_smoke,
    phase5_seq (the seq path — itString guard did NOT break it), F2_float_literals.
    Registered after S7b. Walker version unchanged at `"5"`. **Next: S9.**
  - **S9 — SHIPPED.** `toLower`/`toUpper` (and ASCII `toLowerAscii`/`toUpperAscii`)
    classified unsupported. Per ADR-0006 Z3 has **no native case-folding
    primitive** (a regex-range approximation is deferred to Phase 16), so these
    must NOT be modeled. `dsl_parser.nim` adds an explicit guard in the
    `itString`-receiver call arm (alongside S3's `high` guard, BEFORE the
    `getStdlibModelFor` dispatch): a callee in
    `["toLower","toUpper","toLowerAscii","toUpperAscii"]` on an `itString`
    receiver routes to `iekStrUnsupported` carrying the real op name, which the
    runtime's `StrOpKinds` fall-through raises as `SymexUnsupportedStringOpError`
    and the runSymex boundary maps to **sxUnknown + `seUnsupportedStringOp`**
    (Invariant 3 — never a silent UNSAT, never a crash). Reuses the existing
    `iekStrUnsupported`/`SymexUnsupportedStringOpError`/`seUnsupportedStringOp`
    mechanism — **no new IR kind, no new error kind**. The explicit guard (rather
    than the `getStdlibModelFor` else-fallthrough that would also have classified
    these) keeps the routing intentional and self-documenting. Test
    `tsymex_phase15_S9_caseconv.nim` (5 tests: the 4 case-conv ops → sxUnknown +
    `errors[0].kind == seUnsupportedStringOp`; plain `s == "abc"` → sxSat, proving
    S9 only classifies case-conv and doesn't break the string path) green c+cpp
    5/5. Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
    S4_strpred, S5_strops, S8_concat, S7b_smoke. Registered after S8. Walker
    version unchanged at `"5"`. **Next: S10a.**
  - **S10a — SHIPPED.** `$int` / `parseInt` **digits-path only** (the raises-path
    is S10b, still **DEFERRED post-E1** — exceptions aren't built yet). Test
    `tsymex_phase15_S10a_strconv.nim` (4 tests) green c+cpp 4/4. **No hang** —
    `str.to_int` + the prefix/substr/len ops on a free string are decidable under
    the ≤0xFF byte-faithful constraint (S3); every test + the full regression
    completed well inside the bounded-runner budget.
    - **New error kind `seParseIntPreE`, severity `sevHint`** (NOT `sevError`),
      added to `SymexErrorKind` (`types.nim`). A path carrying it stays **sxSat**
      — this exercises the Invariant-7 severity contract (sxSat with non-empty
      errors ⇒ all sevHint/sevWarning). It marks the pre-E1 unsoundness window.
    - **`$n` arrives as `nnkPrefix` `$`, NOT `nnkCall`** (the RED failure was
      "unsupported prefix operator `$`"). Intercepted in the `nnkPrefix` arm (an
      itInt operand → `iekIntToStr`; non-int `$` errors at parse time, deferred).
      A redundant `nnkCall` `$`-guard is also present for robustness. `parseInt(s)`
      on an itString → `iekStrToInt`, intercepted in the `nnkCall` arm before the
      itString-receiver classify (its operand/result straddle int and string).
    - **runtime lowering.** `iekIntToStr` → `SymVal(svString, toStr(toZ3Int(op)))`
      (`toStr` on Z3Int = `Z3_mk_int_to_str`). The operand is coerced via
      **`toZ3Int`** because an int param is a BV under the abstraction layer
      (ADR-0001), not an svInt — the `==`-goal keeps the BV→int (`bv2int`) mix at
      low F5 hang risk (F5's pathology was ORDERING goals).
      `iekStrToInt` → `ite(startsWith(s,"-"), -toInt(substr(s,1,len-1)), toInt(s))`.
    - **nim-z3 name/semantics corrections (verified `_deps/z3/src/z3/`).** The RFC
      named the prefix check `prefixOf` — the real proc is **`startsWith(a, prefix)`**
      (`sequence.nim:171`, `Z3_mk_seq_prefix`); used as `startsWith(s.str, mkString("-"))`.
      And `toInt` (`Z3_mk_str_to_int`) returns the fixed value **−1** for a
      non-digit string (`strings.nim:126-128`), **NOT** "unconstrained" as the RFC
      premised. That reality reshapes the gate (below) and the window.
    - **Negative-prefix ITE + gate.** The digits gate is asserted on the
      **NEGATIVE branch ONLY** (`isNeg ⇒ negInner >= 0`): if the suffix after `-`
      is non-digit, `toInt` is −1 and `-(-1)=+1` would be a FALSE positive, so the
      gate excludes it. The POSITIVE branch needs NO gate — Z3's `toInt` already
      returns the faithful value (true digits, or −1 for non-digit), so gating it
      would wrongly force non-digit → UNSAT and erase the window. The gate clauses
      accumulate in a `parseIntGateConstraints` threadvar (lower has no pc sink —
      Env is a pure value table) drained into EVERY `trySolve` solver check (sound:
      each clause references the param string's Z3 AST, identical across paths).
    - **seParseIntPreE sevHint emission.** Emitted **whenever `parseInt` is lowered
      on a not-provably-digit string** (a conservative, honest over-emission of a
      HINT — explicitly permitted by the spec), collected in a `parseIntPreEHints`
      threadvar and surfaced (deduped to one) on the sxSat result in
      `runSymexImpl`. The window: nim-z3's `str.to_int` returns −1 for non-digit,
      so `parseInt(s) == -1` is sxSat for a non-digit `s` — whereas Nim's
      `parseInt` would RAISE `ValueError`. Modeling the raise needs E1 → **S10b**.
    - **Exhaustiveness arms (runtime.nim only — uniform-payload StrOpKinds set arms
      cover types/canonicalize/abstraction).** `lower`: `iekIntToStr` + `iekStrToInt`
      split out of the residual-raise arm. `probeProto`: `iekStrToInt` joins the
      svInt proto group (so `parseInt(s) == 42` lowers `42` as Z3Int), `iekIntToStr`
      joins the svString group (so `$n == "42"` lowers the literal as a string).
      `trySolve` drains the gate threadvar; `runSymexImpl` resets both threadvars
      and surfaces the hint.
    - Regression (all green, no hangs): S1_typebridge, S2_strlit, S3_strindex,
      S4_strpred, S5_strops, S8_concat, S9_caseconv, S7b_smoke, phase1_arith
      (int path — `$`/`parseInt` touch int↔string), F2_float_literals. Registered
      after S9. `determinism.md` string section gained the S10a `$int`/`parseInt`
      digits-path + pre-E1 window note. Walker version unchanged at `"5"`.
      **Next: S11 (S10b deferred to post-E1).**
  - **S11 — SHIPPED, Cluster S walker version now 6, S10b remains deferred to
    post-E1.** Closes Cluster S. Immutable-string mutations (`s[i] = c`,
    `s.add(c)`/`s.add(otherStr)`) classified `seUnsupportedStringOp` → `sxUnknown`
    (ADR-0006 — the reason is **immutability**, NOT a byte/codepoint mismatch;
    Invariant 3 — never a silent UNSAT, never a crash). Two dsl_parser
    interception points, both reusing the S9/S3 idiom (route to
    `iekStrUnsupported` carrying the surface op name; the residual `lower` arm
    raises `SymexUnsupportedStringOpError`, mapped at the runSymex boundary to
    `seUnsupportedStringOp`) — **no new IR kind, no new error kind**:
    - `s[i] = c` is detected in the **`nnkAsgn`** arm (`dsl_parser.nim`) when the
      LHS `nnkBracketExpr` receiver classifies `itString` (alongside the existing
      `itTable` set arm; previously this shape fell to the generic `mkUnsupported`
      → a SILENT sxUnknown with no classified error). **This path IS reachable in
      the SUT grammar** — a SUT with a local `var s: string` and `s[0] = c` parses
      cleanly into the itString `nnkAsgn` arm (confirmed by the RED→GREEN test).
    - `s.add(c)`/`s.add(otherStr)` is intercepted in the statement-`nnkCall` arm
      with an explicit `itString`-receiver guard placed **before** the `itSeq`
      `add` arm (a string is not an itSeq, so it would otherwise fall through to
      user-proc registration → a spurious sxUnsat).
    - **Walker version bumped `"5"→"6"`** as the final edit, single-sourced in
      `canonicalize.nim:symexWalkerVersion` (re-exported via `symex.nim`; confirmed
      no duplicate — Invariant 6 holds). The bump orphans every "5"-era cache key,
      so the broad regression re-solves from scratch. Two prior version-pin
      assertions (F8_smoke's "5", S7b_smoke's "5") were advanced to "6" — the
      expected, intended consequence of the close-out bump (S7b's own comment said
      "the Cluster-S bump is S11").
    - `determinism.md`: unsupported-op table row updated (now covers
      `s.add(otherStr)` + the immutability/detection detail) + a "Cluster S
      op-table COMPLETE (closed at S11)" note. Test
      `tsymex_phase15_S11_mutation.nim` (5 tests) green c+cpp 5/5. Broad
      regression under v6, all green, no hangs: S1–S10a (incl. S7b/F8 version
      assertions updated to "6"), F2, F6, F8, phase1_arith, phase5_seq,
      phase14_multivariant_walker/disc_promotion/frontier_pruning. Registered
      after S10a. **Cluster S COMPLETE through S11; S10b (parseInt raises-path)
      remains deferred to post-E1 and will carry its own walker bump when it
      lands.**
  - **S10b — SHIPPED (post-E6; Cluster S now FULLY complete).** Closes the S10a
    pre-E1 unsoundness window: a `parseInt(s)` on a non-digit, non-`-`-prefixed
    `s` now RAISES `ValueError` (was sxSat + `seParseIntPreE` hint). Also
    classifies `$float`/`parseFloat` (no Z3 float↔string conversion).
    - **Raises-path fork in `iekStrToInt` lowering.** S10a's digits ITE
      (`ite(startsWith(s,"-"), -negInner, posVal)`) + negative gate are unchanged;
      S10b ADDS a raise predicate `(not isNeg) and (posVal < 0)` — exactly the
      `not (toInt(s) >= 0) and not startsWith(s, "-")` case (the spec scopes the
      raise to the non-`-`-prefixed non-digit input; the `-`-prefixed non-digit
      case stays handled by S10a's `negInner >= 0` gate). The `-1` value posVal
      carries means non-digit (Z3's `Z3_mk_str_to_int` honest `-1`).
    - **Expression-level raise plumbing (the tricky part).** `parseInt(s)` is an
      EXPRESSION (→ int) but can raise, and `lower` has NO WalkCtx/Path/routeRaise
      access (Env is a pure value table). The minimal sound mechanism: the
      lowering pushes the raise predicate onto a new `parseIntRaiseConds`
      threadvar (mirrors `parseIntGateConstraints`); the ENCLOSING STATEMENT WALK
      drains it via a new `drainParseIntRaises(p, w): seq[Path]` helper. Each
      statement arm that lowers a value/cond (`isLet`, `isAssign`, `isIf`
      per-branch cond, `isAssert`) RESETS `parseIntRaiseConds = @[]` immediately
      BEFORE its `lower`/`lowerBool` (so predicates never leak across
      paths/statements) then calls the drain. The drain FORKS per predicate: a
      RAISES sub-path (`p.pc & @[rc]`) handed to **E3's `routeRaise(rp,
      "ValueError", some(msg), w)` — reused UNCHANGED**, which either transfers it
      into a surrounding `except` (continuations flow out via the `caught`
      channel) or surfaces `sxRaised{ValueError}` at the SUT boundary
      (target-gated, E2b), then TERMINATES the raise path; plus a DIGITS
      continuation (`p.pc & @[not rc …]`) that carries S10a's int value forward.
      In the `isIf` arm the digits continuation threads across all branch conds +
      the else (a cond may raise regardless of which arm is taken). No
      path-explosion: drain returns `@[p]` untouched when no `parseInt` was
      lowered (the common case), and `routeRaise` always returns `@[]` on the
      straight-line raise path.
    - **`seParseIntPreE` emission REMOVED.** The `parseIntPreEHints` threadvar,
      its reset in `runSymexImpl`, and its surfacing on the sxSat result are all
      deleted. The enum variant is RETAINED (enum/cache-key stability) with a
      "no longer emitted" comment — the window is now correctly closed by the
      raises-path.
    - **`$float`/`parseFloat` → `seUnsupportedStringOp`.** dsl_parser: the
      `nnkPrefix` `$` arm routes a float operand (itFloat32/itFloat64) to
      `mkStrOp(iekStrUnsupported, "$float")` (was a parse-time `error()`); a new
      `nnkCall` guard routes `parseFloat(s)` (itString) to
      `mkStrOp(iekStrUnsupported, "parseFloat")`. Both reuse the S9
      `iekStrUnsupported` mechanism → the residual `lower` arm raises
      `SymexUnsupportedStringOpError` → runSymex boundary maps to
      `seUnsupportedStringOp`/sxUnknown (Z3 String theory has no float↔string
      conversion). The int conversions (`$int`/`parseInt`) are unaffected.
    - **S10a's test UPDATED** (same pattern as E2a/E2b/E4 updating prior tests):
      its 4th case asserted non-digit `parseInt(s) == -1` → sxSat +
      `seParseIntPreE` hint (the window); now `let n = parseInt(s)` under
      `tRaisedExn("ValueError")` → `sxRaised{ValueError}`, asserting no
      `seParseIntPreE` in `errors`. S10a stays green under S10b.
    - **No walker version bump** (Cluster S's bump was S11 → "6"; stays "6").
      Test `tsymex_phase15_S10b_strconv.nim` (4 tests) green c+cpp 4/4.
      Regression (S10a (updated), S5_strops, S3_strindex, S9_caseconv,
      S11_mutation, E2b_raise, E3_try, E6_defect, phase1_arith, F8_smoke) all
      green, no hangs. Registered after S10a. **Cluster S COMPLETE (all of
      S1–S11 + S10b shipped).** Next: E7.
  - **Per-cycle notes for S1–S11 implementers:**
    - **S1:** add `iekStr*` IR variants to `types.nim` (every `case e.kind`
      dispatch in `types.nim`, `canonicalize.nim`, `abstraction.nim`,
      `runtime.nim`, `dsl_parser.nim` needs an arm — the F-cluster ripple was
      12–14 arms; expect similar). Add the `StdlibModelKind` `smkStr*` family
      (net-new — no `smk*` string kinds today). Move the `Table[string,V]`
      V≠int guard to parse-time `seUnsupportedTableValType`. **Byte-faithful:**
      `mkStringVar` allocation must assert **every character ≤ 0xFF** (the
      soundness constraint, ADR-0006) so Z3 position == Nim byte index.
    - **S2:** the literal path already works (`dsl_parser.nim:444`,
      `runtime.nim:1067`); the real deliverable is the byte-faithful
      **documentation** + the corrected multi-byte DoD test, which asserts
      **`"é".len == 2`** (byte count), **not `== 1`**. Use IR field **`sval`**
      (not `strVal`).
    - **S3 — DONE (see S3 — SHIPPED above). S4:** lower to `contains`/
      `startsWith`/`endsWith`/`indexOf` from `sequence.nim` (names above).
      **Byte-faithful — SUPPORTED (done in S3):** `s.len`, `s[i]` read (char-
      bridged via `at`→`toCode`→BV8), `s[a..b]`, `s.high` (= `len-1`) all model
      byte-for-byte under the ≤0xFF char constraint (S3 asserts it at
      `allocateSym(itString)` via regex membership — see above; it does NOT
      hang). **`for c in s` is NOT supported** — honestly classified `sxUnknown`
      for *unbounded symbolic iteration length* (not byte/codepoint). **Only**
      `s[i] = c` → `seUnsupportedStringOp` (Z3-string immutability; S11). Do
      **not** emit `seByteIndexUnsupported` for `s.high`, nor
      `seByteIterUnsupported` for `for c in s` (those kinds stay in the enum but
      are unused — the for-loop classification carries an explicit message).
    - **S5:** add `seZ3VersionMissing` + `maxSplitParts` (net-new); extend the
      Z3d `+`/`withSymexSettings` arms. `replaceAll` is gated behind
      `z3WithSeqReplaceAll` (not compiled in by default) — the runtime probe the
      RFC wants must guard the call site under the same `when defined`.
    - **S6a/S6b:** create `regex_parser.nim`; lower via `mkRegex`/`matches`/
      `star`/`plus`/`option`/`loop`/`range`/`union`/`concat`. Regex-replace is
      gated behind `z3WithSeqReplaceRe` (real symbol `Z3_mk_seq_replace_re`).
    - **S7a:** under byte-faithful, `bytes(s)` is **near-trivial** — the base
      model is already a byte sequence (chars 0..255), so `bytes(s)` is the
      **identity view**: map each Z3 char position to its byte value (BV8/int).
      No UTF-8 decode. `maxBytesEncodingLen`/`seBytesBeyondBMP` are largely moot
      (the BMP-cap subsystem the codepoint draft needed is gone); add them only
      if a specific guard still wants them, otherwise S7a is a thin convenience
      lift, not a decoding subsystem.
    - **S10a/b:** `$int`→`Z3Int.toStr`, `parseInt`→`Z3String.toInt`; add
      `seParseIntPreE` (net-new hint). S10b depends on E1.
    - **S11:** walker bump `"5"→"6"` single-sourced in
      `canonicalize.nim:symexWalkerVersion` (currently `"5"` post-F8).
- **Cluster H** (heap preparation — pure infrastructure, no semantics)
  - **H1 — SHIPPED.** `Path` heap-state fields + `deepCopyHeapState` +
    `forkPath` fork-deep-copy contract + fork-site registry + ADR-0010.
    **No walker version bump, no rendering bump** — H1 introduces no
    walker-semantic change (the fields are inert/empty on every path; the
    walker neither reads nor writes them). Walker stays **"6"** (asserted by
    the S11/F8 regression tests, re-run clean).
    - **Path structure (reality vs RFC).** `Path` is a **private `ref object`**
      (NOT exported, NOT a value object), defined in **`runtime.nim`** — the
      §A/§E reference to `runtime.nim:130` is stale; it is now at ~`:206`. The
      three new fields (`heaps: Table[string, Z3AnyAst]`, `heapDepth: int`,
      `allocCounters: Table[string, int]`) were appended after `uncertain`.
      Because `Path` is a `ref object`, every `Path(...)` already allocates a
      FRESH ref — fork isolation reduces to ensuring the two `Table` fields are
      **value-copied, not aliased**, from the parent (Nim `Table` assignment is
      a value copy, so `deepCopyHeapState` suffices).
    - **`Z3AnyAst` confirmed.** The erased-AST type is `Z3AnyAst` (carries
      `raw`+`ctx`), produced via `toAnyAst` — the SAME handle already used for
      `seqDataRaw`/`tabDataRaw`/`setMembersRaw`/`uninterpAst` in `SymVal`. No
      ambiguity; `Z3AnyAst` is correct for `heaps`. `std/tables` is already
      imported in `runtime.nim` (line 19).
    - **Fork-site audit: 26 child sites + 1 root.** `grep -n "Path(" runtime.nim`
      found **27 construction sites** (RFC expected ~15–20; the post-Phase-14
      total is higher). **26 are CHILD-of-parent forks** — all migrated to the
      new `forkPath(parent, pc, env, uncertain)` template (which routes the
      three fields through `deepCopyHeapState`): isIf (arm+else), isLet,
      isAssign, isWhile (body/exit/unwind-uncertain), isIndex (table / seq-oob /
      seq-survivor / array-oob / array-survivor), isVariantReassign,
      isVariantReassignSymbolic (svVariant + svMultiVariant), isVariantField
      (fieldDefect + survivor), isReturn, isCall (opaque / depth-bail /
      recursion-cycle / cache-hit / descent / return-merge), isAssert
      (violation + holds). The **1 ROOT site** (`let initial = Path(...)` in
      `runSymex`) is the only remaining raw `Path(` — it has no parent and
      correctly gets empty-default heap fields. Two call sites thread heap
      state per ADR-0010 R1b (inert in H1): descent forks from the caller `p`;
      return-merge forks from the returned callee path `cp`.
    - **Fork-isolation tested via two exported test hooks** in `runtime.nim`
      (`h1PathHasHeapFields`, `h1ForkIsolation`) — `Path` is private, so the
      RED test cannot name it; the hooks construct a Path, seed
      `parent.heaps["x"]`, fork a child through the real `forkPath`, mutate the
      child, and assert the parent's entry is unchanged. Black-box was
      insufficient (the fields are inert until Cluster R, so there is no
      observable walker behaviour to assert against). `tsymex_phase15_H1_path_heap_fields.nim`
      green c+cpp 2/2. Regression (phase1_arith, phase3_recursion, phase4_tuple,
      phase5_seq, S3_strindex, S11_mutation, F8_smoke) all green, no hangs,
      walker still "6". Registered after S11.
- **Cluster E** (exceptions — reconciled at E1, 2026-06-15)
  - **Real WalkCtx split state (verified against current code, NOT §B.3's
    monolithic inventory premise).** §B.3 was captured BEFORE Z4 shipped; Z4
    (`f52f1b8`) DID land the split. As of HEAD (`32de64b`), `WalkCtx`
    (`runtime.nim`) is **already split** into `.statics: WalkerStatics` (per-walker,
    immutable post-parse) and `.frame: CallFrameCtx` (per call descent) — both
    were net-new empty records in Z4, populated by E1. **This matched the RFC's
    EffectCtx→WalkerStatics+CallFrameCtx mapping** (§4032-4035); no adaptation
    needed. E1 filled them: `WalkerStatics` gained `exnTable: Table[string,string]`
    + `userExnHierarchy: Table[string,string]` (both empty until E4a);
    `CallFrameCtx` gained `handlerStack: seq[HandlerFrame]` + `inFlightExn:
    Option[ExnRecord]`. `WalkCtx.found` is already `seq[RawResult]` (Z4).
  - **RawResult / verdict reality (E2a not yet shipped).** `RawResult`
    (`runtime.nim`) is a **flat object** (not a variant union) with
    `status: SymexStatusKind` ∈ {sxSat, sxUnsat, sxUnknown} + an `errors:
    seq[SymexErrorInfo]` field; the `case status` only branches the sat-witness
    payload. **There is NO `sxRaised` and NO `InternalVerdict` yet** — those land
    E2a (the structural cascade). E1 needs neither: the walker stubs surface via
    the existing `errors`/sxUnknown path.
  - **How raise/try parsed BEFORE E1.** They didn't — `nnkRaiseStmt`/`nnkTryStmt`
    fell into `parseStmtInner`'s final `else: mkUnsupported(…)`, yielding an
    `isUnsupported` IR node → a **silent** `sxUnknown` (`walk(isUnsupported)` just
    sets `w.sawUnknown`, no classified error). E1 replaces that with explicit
    parser cases + classified walker stubs (Invariant 3: non-silent).
  - **Classified-error mechanism = exception boundary (the established idiom).**
    The walker has no `w.errors` accumulator that surfaces on the silent-sawUnknown
    path (`runSymexImpl`'s tail emits `RawResult(status: sxUnknown)` with EMPTY
    errors). Every existing classified sxUnknown (F6 feUnsupportedOp, S1
    seUnsupportedStringOp, S5/S6b/S7a kinds) is produced by **raising a typed
    `*Error` from the walker, caught at the `runSymex` boundary** → sxUnknown +
    populated `errors`. E1 follows this exactly: `walk(isRaise)`/`walk(isTry)` raise
    `SymexRaiseUnimplementedError`/`SymexTryUnimplementedError`, caught at the
    boundary → `eeRaiseUnimplemented`/`eeTryUnimplemented` (sevError). This is the
    ONLY way to guarantee a non-silent classified sxUnknown given the current
    RawResult shape.
  - **IRStmtKind exhaustiveness ripple = 5 compiler-required arms across 3 files.**
    Of the ~10 `case …kind` dispatches over `IRStmtKind`: `types.render`,
    `canonicalize`, `runtime.collectSetLitMembers`, `runtime.collectTableLitKeys`,
    `abstraction.collectBan`, `scan.scanStmt` (1st dispatch) are **exhaustive (no
    else)** and needed `of isRaise:`/`of isTry:` arms; `dsl_parser.emitStmt` is also
    exhaustive (needed branches but those are deliverables, not ripple);
    `abstraction.collectAssertRanges`, `scan`'s 2nd dispatch, and the various
    `IRExprKind` dispatches have `else: discard` (no edit). The walk dispatch
    itself got the two STUB arms. raiseTypeId extraction was unambiguous (probed
    the typed AST: `RaiseStmt[StmtListExpr[Empty, ObjConstr[Par[RefTy[Sym T]], …]]]`;
    unwrap Par/RefTy/PtrTy to the `Sym`/`Ident`).
  - **Push/pop protocol.** `WalkCtx` gained a `frameStack: seq[CallFrameCtx]`;
    `pushFrame(w)` saves `w.frame` + installs a fresh empty `CallFrameCtx`,
    `popFrame(w)` restores it. Wired into the `isCall` descent arm symmetrically
    around `walk(sig.body, …)` (handler stack is PER-FRAME: a try opened in a
    callee is invisible to the caller after return). Inert in E1
    (handlerStack/inFlightExn always empty), wired so E3/E5 raise-flow threading is
    correct by construction. Generic-call (Cluster G) / closure-call (Cluster C)
    descent arms don't exist yet; they will adopt the same push/pop when they land.
  - **E1 — SHIPPED.** Structural IR (`isRaise`/`isTry` + `ExceptHandler`),
    parser cases, handler-stack scaffolding, and classified walker stubs. New
    error kinds `eeRaiseUnimplemented`/`eeTryUnimplemented`. **No walker version
    bump** (stays "6"; E-cluster bumps at E7). Test `tsymex_phase15_E1_ir.nim`
    (4 tests) green c+cpp 4/4. Regression (phase1_arith/let/assert,
    phase3_recursion (call-descent push/pop), phase4_tuple, phase5_seq,
    S3_strindex, S11_mutation, F8_smoke, phase11_walker) all green, no hangs.
    Registered after H1. **S10b (parseInt raises-path) is now UNBLOCKED** — can
    land after any E-cycle (it will carry its own walker bump). **Next: E2a.**
  - **E2a — SHIPPED.** Structural `sxRaised` cascade — `sxRaised` wired through
    the whole type/dispatch surface with **NO handler matching, NO propagation,
    NO witness, NO Z3** (those land E2b+). **What Z4/Z3e already provided
    (reused, not re-added — Invariant 6):** `WalkCtx.found` is already
    `seq[RawResult]` (Z4); `cacheKeyRaised(typeId)` (`:raised:<typeId>`) already
    exists in `canonicalize.nim` (Z3e). **What E2a added:** `sxRaised` to
    `SymexStatusKind` + the `RawResult` variant branch (`raisedTypeId` live;
    `isDefect`/`raisedMsg: Option`/`raisedWitness` inert until E6/E2b); `sfRaised`
    to `SymexFindingStatus` (engine/types.nim); `stkRaisedExn{typeFilter}` to
    `SymexTargetKind` + a `tRaisedExn()` ctor — **NOTE: `SymexTargetKind` lives
    in `smt/types.nim`, not `engine/types.nim`** (the prompt hedged; confirmed
    smt/types). **Structural emission level:** the walker `isRaise` arm now emits
    one `sxRaised` `RawResult` per *feasible* (forked) raise-path into `w.found`
    (uncertain paths set `sawUnknown`), then terminates the path (returns `@[]`) —
    this REPLACES E1's `eeRaiseUnimplemented` classified stub (the `isTry` arm
    keeps its E1 `eeTryUnimplemented` stub). `shouldStop`'s stop-set is now
    `{sxSat, sxRaised}`. **Multi-`sxRaised` cache reconciliation (the one real
    deviation from the RFC GREEN text):** the RFC specs `loadSymexVerdictImpl`
    using `loadAll(sutKeyPrefix)` to read all `:raised:*` matches — but the
    general example-DB (`db.nim`) has **no key-prefix scan / key-enumeration
    primitive** (`loadPrimary` is exact-key only). So the multi-finding protocol
    is realised as a **dedicated `saveSymexRaisedImpl`/`loadSymexRaisedImpl`
    pair** (symex.nim) that writes each distinct raised type as a per-type
    sentinel under `cacheKeyRaised(typeId)` **plus an index slot** (`:raised`)
    enumerating the type ids (each `bytesChoice`-encoded); load reads the index
    and reconstructs the full `seq[RawResult]`. This honours the RFC's intent
    (per-type keys, multi-finding round-trip, no Z3 on reload) while being
    implementable against the real DB. A two-raise SUT (ValueError, IOError)
    round-trips both findings. `saveSymexVerdictImpl` gets `of sfRaised: return`
    (raised goes through the dedicated path); `symexFindAllWitnesses` gets a
    cold-path save + a 4th cache-cascade load level. **Exhaustiveness ripple =
    11 compiler-required arms across 4 files** (chased via bounded compiles +
    the phase13_layer1_wire regression surfacing the `symexFindAllWitnesses`
    cold-path arm that the E2a test alone didn't reach): SymexStatusKind →
    `SymexResult[T]` variant, `symexFind` `case raw.status`, 5 walker
    `trySolve`-dispatch sites (unreachable `discard`), `symexFindAllWitnesses`
    cold-path; SymexTargetKind → describeTarget, canonicalize, 4 macro-time
    `case target.kind` rebuild/cover sites. **E1 test UPDATED** — its 4th case
    asserted the now-removed `eeRaiseUnimplemented` stub; it now asserts
    `res.status == sxRaised` + `res.raisedTypeId == "ValueError"`. **No walker
    version bump** (stays "6"; E-cluster bumps at E7). Test
    `tsymex_phase15_E2a_cascade.nim` (4 tests) green c+cpp 4/4; registered after
    E1. Regression (phase13 verdict/cache round-trip ×5, phase1_arith/assert,
    phase3_recursion, phase11_walker, S11_mutation, F8_smoke) all green, no
    hangs. **Next: E2b** (real `walk(isRaise)` semantics + `InternalVerdict`).
  - **E2b — SHIPPED.** Real `walk(isRaise)` semantics + the private
    `InternalVerdict` boundary. **Walk-return structure found: ACCUMULATOR-based,
    NOT a `WalkResult` type.** `walk(stmt, paths, w): seq[Path]` returns the
    SURVIVING continuation paths and side-effects findings into
    `w.found: seq[RawResult]` (Z4). There is no `WalkResult`/`InternalVerdict`
    walk-return type and the Des-H3 "WalkResult→InternalVerdict rename" does NOT
    apply to the current code. So `InternalVerdict` is a **LOCALIZED helper for
    the raise/return path**, not a wholesale walk-return refactor: a private
    union (`ivSat`/`ivUnsat`/`ivUnknown`/`ivRaised`) built inside the `isRaise`
    arm and converted by `toPublic(iv): RawResult` — the SINGLE boundary
    conversion (Invariant 9), called once per finding immediately before
    `w.found.add`. (Field names `satWitness`/`raisedWitness` differ across the
    variant branches because Nim forbids a repeated field name across case
    arms — the same constraint forced `SymexResult[T].sxRaised` to use
    `raisedWitness*: T` rather than reusing `witness`.) **Raise witness
    extraction = the EXACT `sxSat` mechanism:** the `isRaise` arm calls the
    existing `trySolve(w.z3, p, w.params, …, w.initialEnv)` on the (already
    forked, non-uncertain) raise path; on `sxSat` it takes the returned
    `RawWitness` (extracted from `initialEnv`/`path.env` by `extractWitness`,
    identical to the assertion/label arms) and wraps it as
    `ivRaised(typeId, msg, witness)`. `raiseMsg` is evaluated by `evalRaiseMsg`:
    a string-literal `iekStrLit`→`some(sval)`, nil/non-literal→`none` (a
    non-literal message has no exact value without a string-sort Z3 model;
    deferred, never guessed — Invariant 3). **Target-gated emission (the real
    behavior change from E2a's untargeted structural stub):** the raise surfaces
    a finding ONLY under `stkAssertionViolation` (reachable raise = violation) or
    `stkRaisedExn` (matching `typeFilter`, empty=any); under an `stkLabel`/other
    search the raise just terminates the path (`@[]`) so a post-raise label is
    correctly `sxUnsat`. **Bare-raise handling:** `raiseIsReraise` with
    `w.frame.inFlightExn.isSome` → re-raise that `ExnRecord` (typeId+msg
    propagated); empty handler stack + no in-flight → `SymexRaiseOutsideHandlerError`
    → boundary `eeRaiseOutsideHandler` (sevError, Invariant 3); non-empty handler
    stack without a recorded in-flight exn → `sawUnknown` (handler-stack re-raise
    is E3). **isTry STAYS the E1 `eeTryUnimplemented` stub — E2b does NOT touch
    try/except (E3 does).** New `eeRaiseOutsideHandler` `SymexErrorKind` +
    `SymexRaiseOutsideHandlerError` boundary clause. **E1 test UPDATED** (4th case
    asserted E2a's untargeted `sxRaised` under `tLabel`; now `tLabel`→`sxUnsat`,
    `tRaisedExn("ValueError")`→`sxRaised`). **No walker version bump** (stays "6";
    E-cluster bumps at E7). Test `tsymex_phase15_E2b_raise.nim` (5 tests,
    isExact+isOptimised) green c+cpp 5/5; registered after E2a. Regression (E1_ir
    updated, E2a_cascade, phase13 satsuffix/unsat_roundtrip/layer1_wire,
    phase1_arith/assert, phase3_recursion, phase11_walker, S11_mutation,
    F8_smoke) all green, no hangs. **Next: E3** (try/except matching by type +
    inter-procedural `ivRaised` propagation).
  - **E3 — SHIPPED.** `try`/`except` matching by type (first-match, catch-all)
    + inter-procedural raise propagation — the exception-control-flow CORE. The
    walker stays **accumulator-based** (no walk-return refactor); E3 is realised
    with a shared **`routeRaise(p, typeId, msg, w): seq[Path]`** primitive plus
    two per-frame channels (`caught`, `escaped`).
    - **`walk(isTry)`** (replaces the E1 `eeTryUnimplemented` stub): push a
      `HandlerFrame{handlers, finallyBlock}` onto `w.frame.handlerStack` at
      `myDepth = handlerStack.len`; walk `tryBody`; pop to `myDepth`; then CLAIM
      the `caught` entries tagged with `depth == myDepth` (clearing them) and
      merge with the body's normal fall-through. **This depth-tagged `caught`
      channel is the key insight:** a caught raise's handler continuation must
      EXIT the try, NOT flow back inline into the try body at the raise site
      (the first GREEN attempt let it resume the body — a `done` label after the
      raise was wrongly reached on the raising input). `routeRaise` therefore
      records handler continuations on `w.frame.caught` and returns `@[]`; only
      the owning `isTry` (matched on depth) re-introduces them.
    - **handler-aware `isRaise`:** resolves typeId/msg (re-raise via
      `inFlightExn` unchanged from E2b), then delegates each path to
      `routeRaise`, which searches `w.frame.handlerStack` top-down for the first
      `ExceptHandler` whose `typeIds` contains `typeId` — **EXACT-STRING
      membership** (`typeId in h.typeIds`; empty `typeIds` = bare `except:`
      catch-all). MATCH → truncate the stack below the matched frame, set
      `inFlightExn` for the handler-body duration (outward re-raise), walk the
      handler body, restore, record continuations on `caught`. NO MATCH in a
      callee frame → record `EscapedRaise{path, typeId, msg}` on `w.frame.escaped`.
      NO MATCH in the root frame → E2b boundary behavior (target-gated
      `trySolve` → `toPublic(ivRaised)`).
    - **Inter-proc propagation rides the `isCall` arm:** it captures the callee
      frame's `escaped` list BEFORE `popFrame`, then AFTER the pop (caller frame
      restored) re-routes each escaped raise through the CALLER's handler stack
      via `routeRaise` on a caller-env fork of the raise-site `Path`. So a raise
      in `helper()` is caught by `f`'s surrounding `try/except`. Heap/pc state at
      the raise point travels on `EscapedRaise.path` (R1b merge — structural now,
      inert until Cluster R). A callee that escaped a raise is **NOT cached**
      (`calleeEscaped.len == 0` guard) — its function summary is incomplete (a
      cache hit would replay the normal return and silently drop the raise).
    - **`tryFinally` DEFERRED to E5:** stubbed — walked on the normal
      fall-through paths only (raised-path finally is E5). No finally appears in
      the E3 tests, so it is a no-op there.
    - **Exact-string (NOT subtype) confirmed** by the negative DoD test (case 5):
      `except CatchableError:` does NOT catch `ValueError` → it propagates as
      `sxRaised{ValueError}`. E4 supersedes with `isSubtypeOf`.
    - **No path-explosion / hang:** the try+call interaction terminates because
      `routeRaise` always returns `@[]` on the straight-line raise path (it never
      re-walks the same statement) and the escaped channel is drained exactly
      once per call descent. **No walker version bump** (E-cluster bumps at E7;
      stays "6"). Test `tsymex_phase15_E3_try.nim` (10 tests) green c+cpp 10/10.
      Regression (E1_ir, E2a_cascade, E2b_raise, phase3_recursion (call-descent —
      inter-proc rides this), phase3_mutual, phase1_arith/assert, phase11_walker,
      S11_mutation, F8_smoke, phase13_satsuffix) all green, no hangs. **Next: E4**
      (exception type hierarchy — subtype catch via static `ExnTypeTable`).
  - **E4 — SHIPPED.** Exception-type subtype catch — replaces E3's exact-string
    handler match with `isSubtypeOf` over a static `ExnTypeTable`.
    - **New file `src/proptest/smt/exn_hierarchy.nim`** (standalone, per the RFC's
      preferred option): a compile-time `const exnTypeTable: Table[string,
      seq[string]]` mapping each standard exn type name → its FULL ancestor chain
      (nearest parent first, up to the `Exception` root; storing the full chain
      makes `isSubtypeOf` a membership test). **The encoded ancestry is Nim's REAL
      hierarchy** (verified against Nim 2.2.10 `lib/system.nim` +
      `lib/system/exceptions.nim`, NOT improvised): `Exception` is the root (of
      RootObj); `Defect` and `CatchableError` are its direct children;
      `ValueError`/`IOError`/`OSError` are `CatchableError` subtypes; **`KeyError`
      is-a `ValueError`** (the RFC/prompt's "KeyError→ValueError→CatchableError" is
      CORRECT — KeyError is NOT directly under CatchableError); `IndexDefect`/
      `FieldDefect`/`AssertionDefect`/`RangeDefect`/`StackOverflowDefect` are
      `Defect` subtypes. **Naming reconciliation:** the real Nim type is
      **`OutOfMemDefect`**, not the RFC/checklist's `OutOfMemoryDefect` — both
      spellings are entered with the `Defect`→`Exception` chain so a SUT written
      against either resolves. The checklist minimum (Exception, CatchableError,
      Defect, ValueError, IOError, OSError, KeyError, IndexDefect, FieldDefect,
      AssertionDefect, OutOfMemoryDefect, StackOverflowDefect) is all covered.
    - **`isSubtypeOf(raised, ht, exnTable, userExnHierarchy)`** = `ht == raised or
      ht in ancestorsOf(raised)`; `ancestorsOf` returns the static chain for a
      known type, else walks `userExnHierarchy` (child→direct-parent, E4a-populated
      — **EMPTY in E4**) one link at a time, splicing in the static chain of the
      first standard ancestor reached. `isDefect(exnTable, typeId,
      userExnHierarchy=…)` = `typeId == "Defect" or "Defect" in ancestorsOf(...)`.
      `isKnownExnType` = resolvable in either table.
    - **runtime.nim swap into `routeRaise`:** `WalkerStatics.exnTable` retyped
      `Table[string,string]` (E1's empty placeholder) → `Table[string, seq[string]]`
      and populated from `exnTypeTable` in the WalkCtx ctor (`statics:
      WalkerStatics(exnTable: exnTypeTable)`). The handler-search loop's exact
      `typeId in h.typeIds` check is replaced by a per-handler-type `isSubtypeOf`
      loop; a bare `except:` (empty `typeIds`) still matches all.
    - **Unknown-type behavior (Invariant 3):** a raised type not in `exnTable` nor
      `userExnHierarchy` records `eeUnknownExnType{severity: sevWarning, msg:
      typeId}` on a new `unknownExnWarnings` threadvar (mirrors F7's
      `extractionErrors`: reset at runSymex entry, dedup'd by type name, drained
      into `RawResult.errors` on EVERY verdict branch since a sevWarning never
      halts — Invariant 7) and is matched ONLY against a bare `except:`
      (conservative — no silent false-negative). New `eeUnknownExnType` added to
      `SymexErrorKind` (types.nim).
    - **User-Defect dkOther (test 3) — dynamic capture DEFERRED to E4a.** E4 ships
      the static membership/`isDefect` LOGIC; the parser pass that fills
      `userExnHierarchy` from a SUT exn type's `getImpl` ancestor walk is E4a's
      deliverable (explicitly, per RFC §E4a) — so `userExnHierarchy` is empty in
      E4. Test 3 therefore supplies the `{MyDefect: Defect}` chain the way E4a will
      capture it, proving the dkOther fallback resolves once the parent link is
      known. The public `SymexResult` carries no `isDefect` field (only the
      internal `RawResult` does, inert until E6), so the finding's defect-ness is
      asserted via the observable `sxRaised{raisedTypeId: "MyDefect"}` rather than
      a public flag (the RFC permits asserting observable behavior).
    - **E3's test 5 (2 cases) UPDATED.** They asserted E3's transitional negative
      (`except CatchableError:` does NOT catch `ValueError`); E4 reverses this, so
      they now assert CatchableError CATCHES ValueError — handler body reached
      (`sxSat`) and nothing escapes the boundary (`sxUnsat`). The E3 file stays
      green under E4 (same pattern E2a/E2b used to update E1's test).
    - **No walker version bump** (E-cluster bumps at E7; stays "6"). Test
      `tsymex_phase15_E4_hierarchy.nim` (4 tests) green c+cpp 4/4. Regression
      (E1_ir, E2a_cascade, E2b_raise, E3_try (updated), phase1_arith/assert,
      phase3_recursion, phase11_walker, S11_mutation, F8_smoke) all green, no
      hangs. **Next: E4a** (dynamic user-exn hierarchy via `getImpl` ancestor walk
      → `userExnHierarchy`; closes the user-subtype soundness gap).
  - **E4a — SHIPPED.** Dynamic user-exception hierarchy capture — fills the
    `userExnHierarchy` table that E4 left empty, closing the user-subtype
    soundness gap (round-1 CRIT C7). E4 already shipped the consuming logic
    (`isSubtypeOf`/`ancestorsOf` in `exn_hierarchy.nim` walk `userExnHierarchy`
    child→parent and splice into the static chain at the first known base); E4a
    is purely the PARSE-TIME PRODUCER.
    - **`collectUserExnAncestors(typeSym, ctx)` (dsl_parser.nim):** `typeSym.getImpl`
      yields `nnkTypeDef[Sym, Empty, ObjectTy[…]]` (Ref/PtrTy-unwrapped). The
      inherit clause is an `nnkOfInherit[Sym Parent]` CHILD of the ObjectTy —
      **NOT at a fixed index.** The confirmed Nim 2.2.10 shape for
      `type Child = object of Parent` is `ObjectTy[ Empty, OfInherit[Sym Parent],
      Empty ]` (the OfInherit sits at child 1, after an Empty pragma slot); a bare
      `nnkEmpty` in its place means `of RootObj` = end of chain. So the helper
      SCANS the ObjectTy children for the `nnkOfInherit` rather than assuming an
      index. It records `child→parent` into `ctx.userExnHierarchy` and recurses on
      the parent until the parent is in the static `exnTypeTable` (the bridge
      point) or there is no inherit clause. Guarded against cycles by a depth cap
      (64) plus an "already recorded" short-circuit.
    - **RECONCILIATION beyond the RFC (documented per prompt):** the RFC §E4a says
      walk "type symbols appearing in `nnkExceptBranch`". That is INSUFFICIENT for
      the RFC's OWN test 1 — it raises `MyError` but catches `ValueError`, so the
      required `MyError→ValueError` link appears ONLY at the
      `raise newException(MyError, …)` site, never in an except branch. E4a
      therefore calls `collectUserExnAncestors` at BOTH sites: the raised type node
      (`tn`, after Par/Ref/PtrTy unwrap) in the `nnkRaiseStmt` arm AND each handler
      type node in the `nnkExceptBranch` arm. (Note: in the typed AST the stdlib
      handler type `ValueError` arrives as `nnkType`, not `nnkSym`, so the helper
      no-ops on it — only user `nnkSym`/`nnkIdent` types are walked; stdlib types
      need no dynamic link.)
    - **Threading:** `ParseCtx` gains `userExnHierarchy: Table[string,string]`;
      `parseProc` emits it via a new `emitStrStrTable` (block + per-entry assign,
      mirroring `emitProcs`) into `ParseResult.userExnHierarchyNimNode`;
      `symexFind`'s `quote do` adds `userExnHierarchy: <emitted>` to the
      `SymexProgram(…)` construction (`SymexProgram` gains the field, types.nim);
      `runSymexImpl`'s `WalkCtx` ctor passes `userExnHierarchy: prog.userExnHierarchy`
      into `WalkerStatics` (was the bare `WalkerStatics(exnTable: exnTypeTable)`).
    - **dkOther now DYNAMIC.** E4's deferred user-Defect dkOther fallback (E4 test 3
      hand-supplied the `{MyDefect: Defect}` chain) is now captured automatically: a
      user type whose `getImpl` chain reaches `Defect` makes `isDefect` true with no
      manual chain. Unknown types (in neither table) still emit the E4
      `eeUnknownExnType{sevWarning}` and match ONLY a bare `except:` (Invariant 3 —
      no silent false-negative).
    - **No walker version bump** (E-cluster bumps at E7; stays "6"). Test
      `tsymex_phase15_E4a_userexn.nim` (2 tests) green c+cpp 2/2. Regression
      (E1_ir, E2a_cascade, E2b_raise, E3_try, E4_hierarchy, phase1_arith,
      phase3_recursion, phase11_walker, S11_mutation, F8_smoke) all green, no
      hangs. **Next: E5** (`finally` semantics — both exit paths;
      finally-raises-replaces).
  - **E5 — SHIPPED.** Completes `walk(isTry)`: the `finally` block now runs on
    BOTH the normal AND the raised exit paths and composes per Nim's documented
    semantics (E3 had STUBBED finally to the normal fall-through only).
    - **`pendingRaise` channel (extends E3's depth-tagged channel mechanism).**
      E3 introduced two per-frame channels — `caught` (handler-body
      continuations, depth-tagged, claimed by the owning `isTry`) and `escaped`
      (raises that left a callee frame, drained by the caller's `isCall` arm).
      E5 adds a third, `pendingRaise: seq[(depth, path, typeId, msg)]`, the
      RAISED-path analogue of `caught`. In `routeRaise`, AFTER the `except`-arm
      search fails but BEFORE the escape/boundary fall-through, the handler stack
      is scanned top-down for the deepest frame with a non-nil `finallyBlock`; if
      found, the raise is recorded on `pendingRaise` tagged at that frame's depth
      and `routeRaise` returns `@[]`. This is what makes a `try: raise … finally:
      …` (no except) run its finally before the raise propagates.
    - **`isTry` finally composition.** After walking the body and claiming
      `caught` continuations at `myDepth`, the arm also claims `pendingRaise` at
      `myDepth` (the raised exits this try's finally must wrap). With a finally
      present: **(a) NORMAL exits** — walk the finally on the merged normal set;
      finally fall-through survives, and a raise inside the finally is routed by
      `routeRaise` (it REPLACES — there is no in-flight exn on a normal exit, so a
      finally raise is a fresh raise). **(b) RAISED exits** — for each, set
      `w.frame.inFlightExn` to the original exn for the finally's duration (so a
      bare re-raise inside the finally sees it), walk the finally on the raised
      path; the fall-through survivors RE-RAISE the ORIGINAL (re-routed outward
      via `routeRaise`), while any sub-path where the finally ITSELF raised had
      that new exn already routed by `routeRaise` (REPLACES — the original is
      dropped). The conditional `if x>100: raise IOError` finally naturally splits
      into the x>100 (IOError replaces) and x<=100 (ValueError re-raised)
      sub-paths via this single mechanism. With NO finally, raised continuations
      simply re-propagate immediately.
    - **`inFlightExn` lifecycle:** set to the original exn while a raised
      continuation runs its finally; restored after. (The DoD's bare-`raise`-in-
      finally-on-a-NORMAL-path case — fresh `ivRaised`, not
      `eeRaiseOutsideHandler` — is not exercised by a test case; the shipped tests
      use the `raise newException(…)` form.)
    - **Path-explosion tamed:** the finally runs ONCE per exit continuation (once
      on the merged normal set; once per raised continuation) — never
      combinatorially. The handler stack is popped to `myDepth` BEFORE the finally
      walk, so a raise inside the finally routes to the NEXT-OUTER try/finally
      (escape/boundary) and can NEVER re-enter this same finally — no loop.
    - **Test 3 (ptr-deref heap-write visibility through finally) DEFERRED to
      Cluster R.** RFC §E5 test 3's SUT (`p: ptr int`/`q: ptr int`, `p[]=7` in
      the try and `q[]=99` before a finally raise, asserting both writes visible
      in the witness) is logical-heap (pointer deref/assignment) semantics —
      Cluster R, NOT landed. `path.heaps` exists (H1) but is INERT until Cluster R
      fills it, so the engine cannot yet PRODUCE ptr-write witness values; faking
      the assertion would be unsound. E5 ships the finally CONTROL-FLOW
      composition (tests 1 & 2) and threads each exit continuation's path state
      (`heaps`/`heapDepth`/`allocCounters`, carried on `Path`) into the finally
      walk structurally — so the threading is in place and will exercise once
      Cluster R makes `path.heaps` live. Test 3 is marked `skip()` with a
      `# deferred to Cluster R: ptr-deref heap writes` note (mirrors the S10b →
      E1 deferral pattern).
    - **No walker version bump** (E-cluster bumps at E7; stays "6"). Test
      `tsymex_phase15_E5_finally.nim` (5 tests + 1 deferred skip) green c+cpp
      5/5. Regression (E1_ir, E2a_cascade, E2b_raise, E3_try, E4_hierarchy,
      E4a_userexn, phase3_recursion, phase1_arith, phase11_walker, S11_mutation,
      F8_smoke) all green, no hangs. **Next: E6** (`Defect` modeling — `sxRaised`
      with `isDefect = true`; `defectExclusions: set[DefectKind]`; OQ 4).
  - **E6 — SHIPPED. OQ4 CLOSED.** `Defect` modeling: a Nim `Defect` raise now
    surfaces as `sxRaised{isDefect: true}` rather than silently passing as
    `sxUnsat`.
    - **DefectKind/defectExclusions REALITY (reused, not re-added — Invariant
      6).** Both `DefectKind` enum and `SymexSettings.defectExclusions:
      set[DefectKind]` (default `{dkOutOfMemoryDefect, dkStackOverflowDefect}`)
      already shipped in **Z3a** and live in **`smt/types.nim`, NOT
      `engine/types.nim`** as RFC §E6's GREEN text says (the prompt's hedge is
      CONFIRMED). The enum also carries an EXTRA `dkRangeDefect` variant beyond
      the RFC's six-variant list (Z3a's choice; kept). E6 only added the
      `dkOther` API comment (user defects excludable all-or-none).
    - **isDefect population.** `RawResult.sxRaised.isDefect: bool` already
      existed from **E2a** (init `false`). E6 populates it at the routeRaise SUT
      boundary via the **E4** `isDefect(exnTable, typeId, userExnHierarchy)`
      helper; `InternalVerdict.ivRaised` gained `raisedIsDefect` and `toPublic`
      copies it into `RawResult.isDefect`. New `SymexFinding.defectTypeId:
      string` (engine/types.nim) for display, set from `raw.raisedTypeId` when
      `raw.isDefect` on the sxRaised recording path (symex.nim). New
      `typeIdToDefectKind(typeId): DefectKind` (runtime.nim) for the exclusion
      test — both `OutOfMemDefect`/`OutOfMemoryDefect` spellings → kept enum
      `dkOutOfMemoryDefect`; user defects → `dkOther`.
    - **assert→implicit-AssertionDefect raise = PARSER (not walker).** A raw
      `assert cond, msg` lowers (after semcheck) to gensym scaffolding (`const
      loc…`/`bind`/`mixin`) + `PragmaBlock[Pragma, IfStmt[ElifBranch[not (cond),
      Call failedAssertImpl]]]`. New `callsFailedAssertImpl`/`findAssertFailsCond`
      (dsl_parser.nim) recognise this expansion at the StmtList/PragmaBlock head
      (the scaffolding statements would otherwise land `isUnsupported`) and lower
      it to `mkIf(@[mkBranch(<not cond>, mkRaise("AssertionDefect", nil))])` — the
      assert-FAILS branch raises an implicit `AssertionDefect`. The
      `symexAssert(...)` MARKER (→ `mkAssert`/`isAssert`) and its
      `tAssertionViolation` semantics are UNCHANGED (separate code path).
    - **defectExclusions filter (routeRaise boundary).** `raisedIsDefect =
      isDefect(...)`; `defectExcluded = raisedIsDefect and
      typeIdToDefectKind(typeId) in settings.defectExclusions`. An EXCLUDED
      defect is SUPPRESSED (no finding, regardless of target). A NON-excluded
      defect ALWAYS surfaces as `sxRaised{isDefect:true}` EVEN under a
      label/non-raise search (a reachable contract violation is never silently
      dropped). A non-defect `CatchableError` keeps E2b's target-gating
      (assertion or matching `stkRaisedExn` only).
    - **Auto-discovery.** New `irHasAssertDefect`/`scanAssertDefect` (scan.nim)
      detect the implicit `AssertionDefect` raise so `symexFindAllWitnesses` adds
      a `tRaisedExn("AssertionDefect")` target (+ a `tRaisedExn` `excludeTargets`
      arm). This is how the defect reaches `Report.symexFindings`.
    - **Existing defect targets UNCHANGED (confirmed by regression).**
      `tAssertionViolation` (phase1_assert, via `symexAssert`), `stkIndexError`
      (phase4_tuple), `stkFieldDefect` (phase11_fielddefect) all green c+cpp —
      they produce `sxSat` under their own semantics; E6 only adds the
      sxRaised-Defect path.
    - **No walker version bump** (E-cluster bumps at E7; stays "6"). Test
      `tsymex_phase15_E6_defect.nim` (4 tests) green c+cpp 4/4. Regression
      (E1_ir, E2a_cascade, E2b_raise, E3_try, E4_hierarchy, E4a_userexn,
      E5_finally, phase1_assert, phase4_tuple, phase11_fielddefect, phase1_arith,
      phase7_assertcovered, phase11_walker, phase13_layer1_wire, F8_smoke) all
      green, no hangs. **Next: E7** (regression smoke vs Cluster S + multi-frame
      re-raise; walker version `"6"→"7"`).
  - **E7 — SHIPPED, walker version now "7". CLUSTER E COMPLETE through E7.**
    Hermetic E-cluster regression smoke that exercises the FULL exception
    machinery (E1–E6) TOGETHER in one in-process file, to catch state-threading
    bugs from the multi-file E1–E6 `WalkCtx` edits, plus the close-out walker
    version bump.
    - **`tsymex_phase15_E7_smoke.nim` (12 tests) green c+cpp 12/12.** Composes:
      inter-proc raise caught by the caller's handler (E3 escaped-channel) + its
      nothing-escapes dual; finally re-raises original / finally-raises-replaces
      (E5); a **multi-frame re-raise** (nested try; inner `except IOError:` does
      not match a `ValueError`, the bare `raise` pops through the inner frame to
      the OUTER `except ValueError:` — rides `inFlightExn`); subtype catch
      (`except CatchableError:` ⊇ `ValueError`, E4) + a user exn caught by its
      stdlib base (E4a) + its nothing-escapes dual; an `assert`-false →
      `sxRaised{AssertionDefect, isDefect:true}` (E6); the Report-surface
      `sfRaised` defect entry (E6 recording path); a semantically-complete
      multi-finding `sxRaised` cache round-trip (two-raise SUT solved via the
      real walker, persisted with `saveSymexRaisedImpl`, reloaded from a fresh
      DB-only state with `loadSymexRaisedImpl` — both findings reconstruct, no
      Z3); and the walker-version pin (`symexWalkerVersion == "7"`).
    - **No production-code change beyond the bump.** The composition smoke found
      NO state-threading regression — `WalkCtx`/`w.frame` zeroing
      (`handlerStack`, `inFlightExn`, `caught`/`escaped`/`pendingRaise`) is
      correct across the combined machinery; all 12 cases pass with the existing
      E1–E6 code.
    - **Walker version bump `"6"→"7"`** in `canonicalize.nim:symexWalkerVersion`
      — the SINGLE source of truth (Invariant 6; confirmed no duplicate). The
      bump orphans every "6"-era cache key so the broad regression re-solves from
      scratch. Three prior version-pin assertions (**F8_smoke**, **S7b_smoke**,
      **S11_mutation**, all pinned "6") advanced to "7" — the intended close-out
      consequence (mirrors S11 advancing F8/S7b "5"→"6").
    - **Broad regression sweep under v6 (before bump) then v7 (after):** ALL E
      tests (E1_ir, E2a_cascade, E2b_raise, E3_try, E4_hierarchy, E4a_userexn,
      E5_finally, E6_defect); Cluster S sample (S1_typebridge, S3_strindex,
      S5_strops, S6b_regex, S7a_bytes, S9_caseconv, S10a/S10b_strconv,
      S11_mutation); Cluster F (F2_float_literals, F6_float_math, F8_smoke); H1;
      earlier phases (phase1_arith, phase1_assert, phase3_recursion, phase4_tuple,
      phase11_walker, phase11_fielddefect, phase13_layer1_wire,
      phase7_assertcovered) — all green c, NO hangs. Re-ran E7 (c+cpp), F8_smoke,
      S11_mutation, S7b_smoke, E6_defect under v7 — all green.
    - **E8 — SHIPPED, Cluster E complete.** `getCurrentException()` /
      `getCurrentExceptionMsg()` — additive under "7" (NO bump). Findings:
      (1) **inFlightExn-in-handler-body prerequisite was ALREADY satisfied** —
      E3/E5's `routeRaise` match arm sets `w.frame.inFlightExn = some(...)`
      before `walk(h.body)` and restores after (covers the WHOLE handler body,
      not just bare re-raise), so `getCurrentExceptionMsg` reads the live msg
      with no E3/E5 change needed; E3/E5 stay green. (2) **svUninterpRef real
      field names** (from Z3b): `uninterpAst: Z3AnyAst`, `sortName: string`,
      `typeTag: string`; the fresh constant is built via
      `mkUninterpretedSort("Exn_"&typeId)` + `Z3_mk_const` erased through
      `wrap[Z3AnyAst]`. (3) **Dispatch:** intrinsics recognised by callee symbol
      name in `parseExpr`'s `nnkCall` arm BEFORE the user-proc fall-through →
      new no-payload IR kinds `iekGetCurrentExn`/`iekGetCurrentExnMsg`; lowered
      in `lower` against threadvars (`currentInFlightTypeId`/`currentInFlightMsg`)
      mirrored from `w.frame.inFlightExn` (since `lower` has no WalkCtx access).
      (4) **Error kinds:** `eeNotInHandler` (NEW, sevError, out-of-handler call →
      sxUnknown via `SymexNotInHandlerError` boundary catch); `eeUninterpRefExtraction`
      (pre-existing, sevHint, emitted from the `extractFromSymVal(svUninterpRef)`
      arm). Test `tsymex_phase15_E8_getcurrentexn.nim` (4) green c+cpp 4/4;
      13-test regression all green c, no hangs. **Next: G0-ADR (Cluster G —
      generics).**
- **Cluster G** (generics — reconciled at G0-ADR, 2026-06-15)
  - **Reality baseline (the load-bearing finding).** Generic procs **already
    symex end-to-end TODAY via parse-time monomorphization** — there is NO
    `isGenericCall` IR, and the basic case does not need one. The mechanism, in
    `dsl_parser.nim`:
    - `ensureProcRegistered` (`dsl_parser.nim:1618`) detects a generic callee by
      sniffing for `nnkGenericParams` at `impl[2]` or nested in `impl[5][1]`
      (the `hasGenerics` flag, :1635-1638). When `hasGenerics and callSite != nil`
      it calls `gatherTypeSubst(callSite, impl)` (:1640) to build a
      `Table[string, NimNode]` of `T → concreteTypeNode`, then hands it to
      `parseCalleeImpl`.
    - `gatherTypeSubst` (`dsl_parser.nim:1588`) reads the generic-param names,
      then walks formal params against the **call-site arg nodes' `getType`**
      (:1613) to bind each `T`. So the concrete types come from the typed AST at
      the call site, exactly as ADR-0008 D1 describes.
    - `parseCalleeImpl` (`dsl_parser.nim:1645`) runs `monomorphize(impl, typeSubst)`
      (:1653 → :1574) to substitute the type params throughout the proc def, then
      parses the **monomorphized concrete body** into an ordinary `ProcSig`.
    - The resulting `ProcSig` is registered under the **bare proc name** key
      (`ctx.procs[name] = sig`, :1642) and the call site emits a plain `mkCall`
      (:1035, :1423, :1429) — i.e. it is dispatched by the **existing `isCall`
      walk path** with zero generic-specific walker code.
    - **Confirmed by an existing passing test:** `tests/tsymex_rectify_generics.nim`
      — `proc doubleIt[T](x: T): T = x * 2` called as `doubleIt(a)` at `T=int`
      yields `sxSat`, witness `a=5`. The mental test in the cycle prompt
      (`id(5)` → `5`) is the same shape and already works.
  - **MAJOR DRIFT — the RFC's G1a/G1b/G1c net-new `isGenericCall` IR is
    REDUNDANT with the shipped parse-time monomorphization.** This is a
    byte-faithful-string-class fork. The RFC (preamble + cycle table, RFC lines
    5088-5102, 5156-5333) specs an `isGenericCall` IR kind + `mkGenericCall`
    constructor + `itInstantiated` IR type + a canonicalize round-trip + a
    walk-time `of isGenericCall:` dispatch arm + a runtime `instCache`/`instCountPerProc`
    on `ParseCtx`, keyed by `(symBodyHash, instTypeTuple)`. **None of that
    machinery exists, and the feature it would deliver — symex of a generic call
    — already works without it.** Reality monomorphizes at PARSE time and reuses
    `isCall`; the RFC's design monomorphizes at WALK time behind a new IR node.
    These are two *different* architectures for the same outcome. Building the
    RFC's version as written would (a) add a parallel, redundant generic-dispatch
    path, (b) leave two ways to lower a generic call (the existing `mkCall` path
    and the new `isGenericCall` path) that must be kept consistent, and (c) bump
    the canonicalize/walker-version surface for a round-trip that buys nothing
    the current monomorphization doesn't. **Recommendation: do NOT build the
    `isGenericCall` IR.** Treat G1a/G1b/G1c as *formalize-and-harden the existing
    monomorphization* cycles instead (details per-cycle below). The ADR is
    already self-consistent with reality on D1 ("the walker performs per-call-site
    monomorphization matching Nim's own compilation model"); the only mismatch is
    ADR D1's incidental phrasing ("for each `isGenericCall` IR node") and D3's
    `instCache`/`instCountPerProc` field names, which describe the *RFC's*
    not-yet-built cache. **FLAG FOR HUMAN: confirm the "extend monomorphization,
    drop isGenericCall IR" call before G1a starts** — it materially rewrites
    three cycles.
  - **Premise / path drift table.**

    | RFC-G premise | Reality | Action |
    |---|---|---|
    | `monomorphize`/`gatherTypeSubst` at `dsl_parser.nim:~999/~1013` (RFC G1b GREEN) | They live at **`:1574`/`:1588`**; `ensureProcRegistered` at **`:1618`** (fwd-decl at `:405`); the "~1043" `ensureProcRegistered` line is also wrong | Use real line numbers |
    | G1a: net-new `isGenericCall`, `mkGenericCall`, `itInstantiated` IR | **None exist** in `src/` (grep: 0 hits). Generic calls lower to plain `mkCall` + `isCall` | Drop the new IR; formalize existing path |
    | G1b: emit `isGenericCall` nodes, register under `name#typeargs` key | Calls emit `mkCall`; procs register under **bare `name`** (`:1642`) | Keep bare-`name` reg OR add type-tuple keying *only if* a collision is demonstrated (see G8 note) |
    | G1c: `instCache`/`instCountPerProc` on `ParseCtx`; cap wired into `ensureProcRegistered` | Neither field exists; no cap; no `cacheHitsFor` accessor | Net-new if a cache is wanted; but parse-time reg already de-dupes by `name in ctx.procs` (`:1624`) for same-name calls |
    | `maxInstantiationsPerProc = 64` "already shipped in `SymexSettings`" (RFC G1c GREEN) | **FALSE** — not in `SymexSettings` (`types.nim:651`, fields: integerSemantics/queryRLimit/maxFrontierSize/maxCallDepth/maxLoopUnwind/acceptUnknownAsCovered/defectExclusions/inlinePolicy/maxSplitParts). It is **NET-NEW** | Add the field in the cycle that needs it; correct the RFC's "already shipped" claim |
    | `ge*` error kinds net-new in G1a | **Already present** in `types.nim:575-576`: `geInstantiationCapped`, `geConceptViolation`, `geUnresolvedGeneric`, `geDistinctBijectivitySkipped` (added during Z3a's `SymexErrorKind` build) | Reuse; do NOT re-add |
    | Preamble's `geDistinctBarrier`, `geVtableDispatch` | **Absent** from the enum | Net-new if G5/subtype-OOS errors are emitted |
    | `he*`→`ge*` rename ("formerly-named heInstantiationCapped…") | **No `he*`-named generics kinds ever existed** (grep: 0). The `he*` prefix is owned by Cluster H (`heDepthExhausted`, `heUnsafeCast`, …, `types.nim:578-580`) | No rename needed; strike the rename claim from the RFC |
    | `mkUninterpretedSort` / `Z3_mk_uninterpreted_sort` for distinct sorts (G4) | **Exists and is already used**: `_deps/z3/src/z3/sort.nim:113` (`mkUninterpretedSort(ctx, name): Z3Sort[stUninterpreted]`, also a `requireCurrentContext` overload :127 and `declareSort` alias :130). Already called in `runtime.nim:1757` (E8 exn refs) | G4 has its primitive; reuse the exact E8 pattern (`mkUninterpretedSort` + `Z3_mk_const` + `wrap[Z3AnyAst]`) |
    | `WalkerStatics.distinctSorts` (ADR D4) | `WalkerStatics` exists (added empty at Z4) but has **no `distinctSorts` field** yet | Net-new in G4 |
    | Walker version `"7"→"8"` at G10 | Current `symexWalkerVersion = "7"` (`canonicalize.nim:75`) — correct baseline | Bump at G10 only if walker *semantics* change (a pure-additive monomorphization-formalization may NOT need a bump — decide at G10) |

  - **Per-cycle recommendations (early cycles).**
    - **G1a — SHIPPED (2026-06-15).** Repurposed exactly as recommended below:
      NO `isGenericCall` IR. The bare-name `ctx.procs`/`parsing` collision is
      FIXED. Design: a shared `instKeyFor(calleeSym, typeSubst, impl)` +
      `bodyHashPart` (`dsl_parser.nim`) builds the ADR-0008 D2 instantiation key
      `name#<symBodyHash, lineInfo-fallback>#<T=Type tuple sorted by param
      name>`. Non-generic procs (empty `typeSubst`) → bare name, so non-generic
      behavior is byte-identical to pre-G1a. `ensureProcRegistered` now RETURNS
      the key; the short-circuit and `parsing` set are keyed by it; and **all
      three call-emission sites** (expr `:1029`, stmt method-call fallthrough,
      stmt non-method fallthrough) pass the returned key as the `mkCall` callee
      name — so registration and the walker's `w.procs[stmt.callee]` dispatch
      (`runtime.nim:3567/3571`) compute and use ONE key. Mutual-recursion /
      self-recursion stay correct (the `parsing` set is keyed by instKey). RED
      demonstrator: the collision is invisible for an identity generic (body
      same at every `T`); it only bites when the monomorphized body DIFFERS by
      type, so the test uses `proc szof[T](x:T):int = sizeof(T)` at `int8`+`int64`
      (1 vs 8) — sxUnsat (wrong reuse) → sxSat after the fix.
      `tests/tsymex_phase15_G1a_instkey.nim` 4/4 c+cpp; 9/9 regression
      (rectify_generics, phase3_recursion/mutual/summarization, phase4_tuple,
      phase1_arith, E3_try, S11_mutation, F8_smoke). Walker version stays "7".
      **Next: G1b/G1c (cap + net-new `maxInstantiationsPerProc`).**
    - **G1c — SHIPPED (2026-06-15).** (G1b folded into G1a — the registration
      key is already fixed; G1c is purely the instantiation CAP.) NET-NEW
      `SymexSettings.maxInstantiationsPerProc` (default 64, ADR-0008 D7/OQ5;
      the RFC's "already shipped in `SymexSettings`" claim was FALSE — confirmed
      net-new) plus its `defaultSymexSettings` entry and `+`-merge clause (the
      same field-add exhaustiveness ripple S5/S7a did for
      `maxSplitParts`/`maxBytesEncodingLen`). The cap is PER-BASE-PROC: a
      counter in `ensureProcRegistered` keyed by the generic's DEFINITION site
      (`impl.lineInfoObj` = file:line:column — the ONLY identity invariant
      across instantiations AND module-disambiguating; `symBodyHash`/`bodyHashPart`
      could NOT key it because each monomorphized symbol hashes differently).
      When a NEW instantiation would exceed the cap it is NOT registered, so its
      `mkCall` key is absent from `w.procs`; the missing-callee walker arm
      (`runtime.nim`, G1c-hardened) now binds a fresh unconstrained retSym +
      marks the path uncertain → `sxUnknown` instead of KeyError. A
      `SymexErrorInfo{kind: geInstantiationCapped, severity: sevError}` (kind
      REUSED from Z3a; the record carries no `procSym`/`observedCount` fields so
      those go in `msg`) is accumulated into `ParseCtx.parseErrors`, emitted via
      `ParseResult.parseErrorsNimNode` → `SymexProgram.parseErrors`, and drained
      into `RawResult.errors` by `runSymexImpl` — which also forces `sxUnknown`
      whenever any parse-error is `sevError` (Invariant 3, never silent). The cap
      value threads settings→parser: every symex macro passes
      `settings.maxInstantiationsPerProc` into `parseProc(impl, …)` →
      `newParseCtx` → `ParseCtx.maxInstantiationsPerProc` (so the count/cap check
      lives at parse time, with the limit carried from the active
      `SymexSettings`). `withSymexSettings` sets the new field (verified by the
      RED→GREEN test using `maxInstantiationsPerProc = 2`). NOTE: `SymexProgram`
      moved below `SymexErrorInfo` in `types.nim` so the new `parseErrors` field
      can name that type (cross-`type`-section forward refs don't resolve).
      `tests/tsymex_phase15_G1c_instcap.nim` 2/2 c+cpp (RED: one generic at 3
      distinct types under cap=2 → sxUnknown + geInstantiationCapped; negative:
      default cap → sxSat, no false-positive). Regression 8/8
      (G1a_instkey, rectify_generics, phase3_recursion/summarization/mutual,
      F8_smoke, S11_mutation, phase1_arith). Walker version stays "7".
      **Next: G3 (type-substitution path through `classifyType`; `auto` return).**
    - **G3 — SHIPPED (2026-06-15).** Audit + guards cycle.
      - **What already worked.** `classifyType`'s text-match fallthrough
        (`dsl_typebridge.nim:343`) already resolved a substitution-derived
        concrete SYM (`float64`/`float32`/`string`/`bool`/`int`/enum) to the
        correct `IRType` and already `error`ed cleanly on anything unsupported —
        so DoD's "no silent default for any type family reachable through
        monomorphization" (Invariant 3) held pre-G3, and the centerpiece's
        PARAM classification was already sound. The float text-match
        (`itFloat32`/`itFloat64`) from Cluster F was the load-bearing piece.
      - **What had to be FIXED (gaps the float/sink RED surfaced — the
        substitution path was sound but the WALK path and the `sink` AST shape
        were not).** (1) **float/string proc-RETURN (walk-time).** The
        `isReturn` arm's retConstraint raised *"composite-typed proc return not
        yet wired"* for floats/strings, and ALL FIVE call-return retSym
        allocations used `bvVar` (which `doAssert`s `itInt`) — so a
        value-returning generic instantiated at `float64` CRASHED on the int
        assertion before its target was reachable (NOT an sxUnknown fallback, a
        hard abort). Added `retBindEq` (a NaN-safe *structural* binding eq for
        float — `(a==b) or (both NaN)`, so a NaN-returning callee is never
        pruned — and native eq for int/bool/string) and `freshRetSym` (routes
        every retSym through the type-aware `allocateSym`, threading its
        init-side constraints — the string byte-range floor etc. — onto the
        post-call survivor paths AND into the call-cache `pcDelta`), and wired
        all five sites (`runtime.nim`). (2) **`sink T` through generics.** The
        typed GENERIC AST presents `sink T` as `nnkCommand[sink, T]`, NOT the
        `sink[T]` `nnkBracketExpr` the Z3c strip handled; and `gatherTypeSubst`
        only bound a BARE `nnkIdent` formal, so `T` never bound for a
        `sink`/`var`/`lent`-wrapped param and the body's `T` stayed
        un-monomorphised → `classifyType` errored on the literal `T`. Fixed
        `gatherTypeSubst.unwrapGenericTy` to strip `var`/`sink`/`lent`
        (command + bracket forms) before generic-name matching, and taught
        `classifyType` to strip the `nnkCommand` sink/lent form on the RAW node
        BEFORE `getTypeInst` (the substituted `sink int` command carries no
        type, so `getTypeInst` would raise *"node has no type"*).
      - **Auto-return guard ADDED (DoD item).** In `parseCalleeImpl`: if a
        monomorphised proc whose ORIGINAL impl DECLARED a (generic/`auto`)
        return type resolves it to `nnkEmpty`, emit
        `error("symex G3: type-substitution produced nnkEmpty retTy …")` rather
        than silently treating it as `void` (Invariant 3). Defensive — Nim's
        semchecker resolves `auto` before `getImpl`, so `retTy` is normally
        concrete; the guard catches the failure case loudly.
      - **DoD.** Float64 instantiation symex's correctly — the Cluster F float
        bridge is reached THROUGH a generic call (param + return classify
        `itFloat64`, walker symex's the float body, sxSat with a float witness,
        not an sxUnknown fallback). `sink T` at `T=int` classifies `itInt` and
        is sxSat (Breadth-H5). The `nnkEmpty`-retTy guard is in place. The
        (optional, spec-marked) string-instantiated case is DEFERRED: the
        type-substitution path classifies `string` fine, but full string
        proc-RETURN value EXTRACTION is a separate pre-existing unwired path
        (not a generic concern) — out of G3 scope; it degrades soundly to
        sxUnknown. `tests/tsymex_phase15_g3_type_subst.nim` 2/2 c+cpp.
        Regression 10/10 (G1a_instkey, G1c_instcap, rectify_generics,
        F2_float_literals, F5_float_conv, F8_smoke, phase3_recursion,
        phase4_tuple, S3_strindex, phase1_arith). Walker version stays "7".
        **Next: G4 (`distinct T` as a fresh uninterpreted Z3 sort).**
    - **G1a — RECOMMEND REPURPOSE (no new IR).** Do not add `isGenericCall`/
      `mkGenericCall`/`itInstantiated` or a canonicalize round-trip. Instead make
      G1a a *characterization + hardening* cycle: add a RED test that pins the
      existing behavior (a generic identity/`doubleIt` SUT → `sxSat`, mirroring
      `tsymex_rectify_generics.nim`) PLUS the Feas-H5 module-collision case
      (two modules each with `proc id[T](x:T):T=x`). **Feas-H5 is a REAL latent
      bug in reality, not a hypothetical:** `ensureProcRegistered` keys
      `ctx.procs` by **bare `calleeSym.strVal`** (`:1623`, `:1642`) and
      short-circuits on `name in ctx.procs` (`:1624`) — so two same-named generic
      procs from different modules (or the *same* generic proc at two different
      `T`s) **collide on the bare name** and the second registration is silently
      skipped. This is the single concrete correctness gap the cluster should fix,
      and it argues for the type-tuple/`symBodyHash` key from ADR D2 — but applied
      to the **existing `ctx.procs` registration**, not a new IR. G1a should
      expose/confirm this collision as its RED.
    - **G1b — RECOMMEND REPURPOSE to "fix the registration key."** Rather than
      "emit `isGenericCall` nodes," make G1b change `ensureProcRegistered`'s key
      from bare `name` to the ADR-D2 key (`symBodyHash`-or-`lineInfo`-fallback `#`
      type-tuple) so distinct instantiations and cross-module same-names get
      distinct `ProcSig`s. The call-site `mkCall` already carries the callee name;
      the only change is that the **emitted call name and the registered key must
      agree** on the instantiation-qualified key (today both use bare `name`, so
      they trivially agree — the fix must keep them in lockstep). This is a
      surgical change to one proc, not a parser-wide new emission path.
    - **G1c — RECOMMEND REPURPOSE to "cap + de-dupe on the real key."** The
      `instCache` the RFC wants is *mostly already there*: `ctx.procs` keyed by
      the G1b instantiation key IS the per-walker instantiation cache, and the
      `name in ctx.procs` guard (`:1624`) IS the cache-hit short-circuit (parse
      once, reuse). G1c's real net-new work is: (a) add
      `maxInstantiationsPerProc` to `SymexSettings` (it does NOT exist — RFC is
      wrong); (b) add an `instCountPerProc` counter + cap check in
      `ensureProcRegistered`; (c) on cap, register a sentinel/`isCapped` `ProcSig`
      and have the `isCall` walk arm emit `geInstantiationCapped` +
      `sawUnknown`; (d) expose `cacheHitsFor` under `proptest_testing`; (e)
      participate `maxInstantiationsPerProc` in the canonicalize cache key. NO
      `of isGenericCall:` walker arm is needed.
    - **G3/G4/G6/G7/G8 — these are the genuine net-new feature cycles** and are
      LARGELY UNAFFECTED by the IR decision (they extend the monomorphization/
      `classifyType`/sort path, not the dispatch IR): G3 (substitution →
      `classifyType` audit, `auto` return) extends `classifyType` over the
      `monomorphize` output; G4 (`distinct T` fresh sort) reuses the shipped
      `mkUninterpretedSort` + a net-new `WalkerStatics.distinctSorts` cache + a
      net-new `geDistinctBijectivitySkipped` emission (kind already in the enum);
      G6 (concepts) needs the net-new `ProcSig.conceptConstraints` + stdlib
      membership table (`geConceptViolation` kind already present); G7 (`static[T]`)
      extends the instantiation key with `;static=<val>` (depends on the G1b key
      fix); G8 (multi-param) needs the sorted-by-param-name tuple in the G1b key.
      **These are "extend what exists," low fork-risk.**
  - **Net-net for the orchestrator.** Cluster G's *real* deliverables are:
    (1) fix the bare-name `ctx.procs` collision bug (G1a/b — the only correctness
    gap), (2) instantiation cap + `maxInstantiationsPerProc` setting (G1c —
    genuinely net-new), (3) `distinct T` sorts (G4/G5), (4) concepts (G6),
    (5) `static[T]` (G7), (6) multi-param keys (G8). The `isGenericCall` IR +
    walk-time instantiation cache from G1a–G1c is **redundant scaffolding** and
    should be dropped in favor of extending the existing parse-time
    monomorphization. **ADR-0008 confirmed on disk** (`ADR-0008-generic-instantiation.md`,
    Status Accepted, dated 2026-06-06) and matches the preamble on policy
    (D1 monomorphization, D2 key schema, D3 cache, D4 distinct sort, D5 concepts,
    D6 order-independent multi-param key, D7 cap=64); its D1/D3 *phrasing* assumes
    the `isGenericCall` IR exists, which is the one wrinkle to reconcile when the
    repurpose decision lands.

**Toolchain (cross-cutting, established at Z1):** all dev/test runs use
`localhost/proptest-dev:latest` (built from `ghcr.io/coreyleavitt/nim:latest` +
`z3-devel`). nim-z3 v2.0.0 requires **Nim >= 2.2.10**. Run a single test with
`scripts/dt.sh <c|cpp> tests/<file>.nim`.
