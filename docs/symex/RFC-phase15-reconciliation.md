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
    - **G4 — SHIPPED (2026-06-15).** `distinct T` as a fresh uninterpreted Z3
      sort.
      - **`itDistinct`.** New `IRTypeKind itDistinct{distinctName: string,
        distinctBase: IRType}` (ctor `tDistinct`; the exhaustiveness ripple
        was chased across `==`/`$`/canonicalize/`emitIRType`/`classifyType`/
        `allocateSym`/`tyOf`/`iteSV`/`coerceIntLit`/`symValHash`/
        `extractFromSymVal`/`extractLeaf`/`defaultZero`/the `runSymexImpl`
        param-loop, each confirmed by a bounded compile). `classifyType`
        recognises `type Foo = distinct Bar` via the `nnkDistinctTy` in the
        sym's `getImpl`, checked BEFORE the object/enum/range-alias unwrap
        paths (a distinct over an object base must be walled off, not
        unwrapped).
      - **`distinctSorts` placement.** ADDED `WalkerStatics.distinctSorts:
        Table[string, Z3Sort[stUninterpreted]]` per ADR-0008 D4, but the LIVE
        populator is a per-run threadvar `currentDistinctSorts:
        Table[string, DistinctSortEntry{sort, inject, eject}]` (reset at
        `runSymexImpl` entry — `allocateSym` is a pure type→SymVal allocator
        with NO `WalkCtx` access, exactly E8's in-flight-exn threadvar
        mechanism); the field is MIRRORED from the threadvar after the walk
        for inspection.
      - **SymVal representation = NEW `svDistinct`, NOT a reuse of E8's
        `svUninterpRef`.** `svDistinct{distinctAst: Z3AnyAst, distinctName:
        string, distinctBaseSym: ref SymVal}`. `svUninterpRef` carries only
        `(uninterpAst, sortName, typeTag)` — no base value; G4 needs the
        boxed ejected base for the witness eject-chain AND for explicit
        `T(distinctVal)` conversions, so a dedicated kind was the right call.
      - **inject/eject.** Two uninterpreted func-decls per distinct type via
        raw `Z3_mk_func_decl` (the phantom-typed `Z3FuncDecl[ArgsTup,Ret]`
        cannot be used — the sorts are RUNTIME-known, not compile-time type
        params, exactly as ADR D4 anticipates), declared once per (name,
        run): `inject_T: Base→Distinct`, `eject_T: Distinct→Base`.
      - **Round-trip ("bijectivity") — decidable-base-only + the HANG
        finding.** For base ∈ {int, BV, bool} the round-trip is asserted as a
        GROUND per-occurrence pin `eject(dConst) == baseSym` (the witness
        leaf rides `baseSym`; the distinct const stays walled off). It is
        **NOT** a universal quantifier: the ADR's `∀x. eject(inject(x))==x`
        form HANGS (180s MBQI loop); WITH triggers it stops hanging but
        returns `unknown`; and even a GROUND REVERSE pin
        `inject(baseSym)==dConst` ALSO hangs (the uninterpreted-fn-over-BV
        combination). Per the HARD "never ship a hang" rule the eject-pin
        alone is the decidable model (QF_UFBV → sxSat/sxUnsat) and satisfies
        the DoD (target reachable, witness via eject, type wall, int base
        decidable). `inject` is still DECLARED (for a future explicit
        `Distinct(baseVal)`) but never APPLIED at allocation. **int-base
        confirmed NON-HANGING** under the bounded runner. For base ∈
        {float32, float64, string} the round-trip is SKIPPED entirely and
        `geDistinctBijectivitySkipped` (sevHint, REUSED from Z3a) is emitted
        (drained into `RawResult.errors` on EVERY verdict branch, dedup'd by
        msg — mirrors E4's `unknownExnWarnings`).
      - **Z3 4.15 footguns fixed.** The uninterpreted sort needs an explicit
        `Z3_inc_ref(Z3_sort_to_ast(sort))` held for the run, else Z3 GCs the
        un-referenced sort during the heavy following ast allocation and it
        reads back as `Z3_UNKNOWN_SORT` (→ SIGSEGV in every func-decl that
        names it). `Z3_mk_app` arg arrays AND `Z3_mk_func_decl` domain arrays
        must be HEAP `seq`s, not stack arrays. Intermediate app results
        (`inject(x)` before `eject(...)`) must be `wrap`-ped (inc-ref'd)
        before being re-applied.
      - **emitTyAndReader eject-chain (Breadth-CRIT-1).** The `itDistinct`
        arm renders `DistinctName(baseReader)`; `extractFromSymVal(svDistinct)`
        extracts the boxed base at the SAME path (populated from the eject
        pin), so a distinct param produces a non-empty witness instead of a
        silent empty reader. `ejectBase` (RECURSIVE, for nested chains)
        auto-ejects a `svDistinct` operand to its ground base in every binop
        compare/arith + unop site, so `float64(m)` / `int(u)` — which the
        parser passes through as the bare distinct var (the `nnkConv`'s src
        type is the distinct name, matching neither `intTyNames` nor
        `fltTyNames`) — lower correctly.
      - **`geDistinctBarrier` (net-new, sevError).** ADDED to
        `SymexErrorKind` per the preamble (G0-ADR reconciliation noted it as
        absent). Implicit distinct↔base coercion is rejected by the Nim
        semchecker BEFORE the macro sees the typed AST (the D5 "trust the
        semchecker" rationale), so the kind exists for test-injectable /
        defensive use; no synthetic emission site is manufactured.
      - **Nested chains.** `type KiloMeters = distinct Meters` classifies to
        an `itDistinct` whose base is itself an `itDistinct("Meters")`; two
        sorts are allocated (Meters + KiloMeters); `ejectBase` recurses to
        the ground float; the FP ground base means both skip the round-trip.
      - **DoD.** `tests/tsymex_phase15_g4_distinct_sort.nim` 4/4 c+cpp
        (distinct-FP target reachable + skip-hint; distinct-INT decidable
        no-hang; FP witness non-empty via eject-chain; nested → 2 sorts).
        Regression 10/10 (G1a_instkey, G1c_instcap, g3_type_subst,
        rectify_generics, phase4_tuple, phase5_seq, F2_float_literals,
        S3_strindex, phase1_arith, E8_getcurrentexn). Walker version stays
        "7" (Cluster G bumps at G10). **Next: G5 (distinct borrow
        semantics).**
    - **G5 — SHIPPED (2026-06-15).** `distinct` borrow semantics.
      - **Borrow via the BOXED-BASE SymVal op, NOT the hanging Z3 inject
        function.** The RFC §G5 text describes the borrow as a Z3 expression
        `inject_T(eject_T(a) + eject_T(b))`. **That form HANGS** — G4 proved the
        `inject`/`eject` uninterpreted-fn-over-BV application chain
        non-terminates (MBQI). So G5 does NOT build it. Instead, the borrow
        operates at the SymVal level on G4's BOXED base (`svDistinct`'s
        `distinctBaseSym`): eject both operands (`ejectBase`), apply the BASE
        operator (the existing `arithInt`/`arithFloat`/BV + `cmpInt`/`cmpFloat`/
        `cmpString`/BV paths), and re-box (arithmetic) or return the raw bool
        (comparison). The G4 eject-pin (`eject(dConst)==baseSym`) ties each
        operand's distinct const to its base, so this is sound. **Confirmed
        non-hanging under the bounded runner.**
      - **Parser (`dsl_parser.nim`).** `hasBorrowPragma` detects an `nnkPragma`
        child of the `nnkProcDef` holding `ident"borrow"`; `borrowInfoFor`
        classifies an operator SYMBOL as a borrow shim and reads its return
        type (`impl[3][0]` → `itDistinct` = arithmetic re-box, else =
        comparison bool). A borrow proc has NO real body (`getImpl` body is a
        bare `Sym` = the base op), so it must NEVER be body-parsed. The typed
        AST presents `m1 + m2` as an `nnkInfix` whose `n[0]` is the borrow proc
        sym (NOT an `nnkCall`); the `nnkInfix` arm intercepts it and emits a
        new `iekBorrowOp` IR via `mkBorrowOp(baseOp, lhs, rhs, returnsDistinct,
        distinctName)` (base op from `binopForInfix(operatorName)`). The
        exhaustiveness ripple was chased across `emitExpr`/`render`/
        `canonicalize`/`abstraction` (`collectVarRefs` recurse; `tryEvalInterval`
        none-group)/`probeProto` — each confirmed by the bounded compile.
      - **Runtime (`runtime.nim`).** The `iekBorrowOp` lower arm does the
        eject → base-op → (re-box | raw-bool) above. `reboxDistinct` makes a
        fresh opaque const of the distinct sort (looked up in
        `currentDistinctSorts` — guaranteed present because the operands were
        already allocated as that distinct type) and boxes the COMPUTED base
        underneath, so the result ejects back correctly and the witness renders
        through the eject-reader chain. The per-occurrence const name is
        uniquified by the new `currentBorrowReboxCounter` threadvar (reset at
        `runSymexImpl` entry, mirroring E8/G4).
      - **`Meters(10.0)`.** A distinct CONSTRUCTION (`nnkConv` float→Meters);
        the G4 parser already passes it through to its base float literal
        (`10.0`), so the `> Meters(10.0)` comparison lowers as float-vs-float —
        no new construction code needed.
      - **`geDistinctBarrier` (Invariant 3, NOT silent).** A NON-borrowed proc
        on a distinct type WITHOUT a parseable body is the realistic barrier
        trigger: a truly forward-declared bodyless proc is rejected by Nim
        itself ("implementation expected"), but an `{.importc.}`/magic taking a
        distinct param COMPILES with an empty body (`impl[6]==nnkEmpty`). In
        `ensureProcRegistered`, such a proc (empty body + no `{.borrow.}` +
        ≥1 distinct-typed param) emits `geDistinctBarrier` (sevError, REUSED
        from G4 — finally given a live emission site) into `ctx.parseErrors`
        and is NOT registered; the walker's missing-callee arm degrades the
        path to sxUnknown and the sevError forces the verdict to sxUnknown
        (never a silent sat/unsat). A `{.borrow.}` op is routed at parse time
        and never reaches this arm.
      - **DoD.** `tests/tsymex_phase15_g5_distinct_borrow.nim` 3/3 c+cpp
        (borrowed `+` threads arithmetic through base, target reachable, witness
        base-sum > 10.0; borrowed `<` produces a correct Z3 bool, target
        reachable; non-borrowed bodyless distinct op → geDistinctBarrier /
        sxUnknown). Regression 9/9 (g4_distinct_sort, g3_type_subst,
        G1a_instkey, rectify_generics, F2_float_literals, F3_float_arith,
        F4_float_compare, phase4_tuple, phase1_arith). Walker version stays
        "7" (Cluster G bumps at G10). **Next: G6 (concepts).**
    - **G6 — SHIPPED (2026-06-15).** Concept constraints / trust boundary.
      - **NO `isGenericCall` node — RFC §G6 GREEN reconciled.** The RFC's
        GREEN puts the conformance guard in an `of isGenericCall:` walker arm
        reading `gcTypeArgs`; that IR was DROPPED at G1a. The check moved to
        PARSE TIME, on the RESOLVED concrete type (from `gatherTypeSubst`'s
        binding), in `parseCalleeImpl`.
      - **`ProcSig.conceptConstraints: seq[string]` (net-new, types.nim).**
        Captures the per-generic-param type-class constraint names. Populated
        in `parseCalleeImpl` by walking the ORIGINAL impl's `nnkGenericParams`
        (`impl[2]` untyped / `impl[5][1]` typed): each `nnkIdentDefs` whose
        constraint node (`gp[gp.len-2]`) is NOT `nnkEmpty` contributes its sym
        name (a compound `A and B` the semchecker elaborated is captured by
        `.repr`, no special-casing). Added to `canonicalize(ProcSig)` (`cc=[…]`)
        so two sigs differing only in constraints get distinct cache keys;
        `emitProcSig` leaves it defaulted (the runtime never reads it — the
        check already ran at parse time).
      - **Stdlib membership table + trust boundary.** `stdlibConceptMembers`
        encodes the closed sets for SomeNumber / SomeInteger / SomeFloat /
        SomeOrdinal / SomeUnsignedInt / SomeSignedInt. `conformsToStdlibConcept(
        conceptName, resolvedTypeName)` is the SINGLE conformance entry point:
        for a stdlib concept it returns membership; for a NON-stdlib (user)
        concept name (empty member set) it returns `true` — "no violation to
        assert", i.e. TRUST THE SEMCHECKER (the validator skips it). In
        `parseCalleeImpl`, a stdlib-constrained param bound to a non-conforming
        resolved type emits `geConceptViolation` (sevError, REUSED — already in
        the enum) into `ctx.parseErrors` → `SymexProgram.parseErrors` → forced
        sxUnknown (G1c/G5 plumbing, Invariant 3). Belt-and-suspenders: from
        REAL source the semchecker already guarantees conformance, so the
        stdlib check never fires on real source — it is the test-injectable
        guard only.
      - **Negative-test adaptation.** No `isGenericCall` node exists to
        construct with a malformed `gcTypeArgs`. Instead the test injects a
        non-conforming pair DIRECTLY into the real entry point
        `conformsToStdlibConcept` (e.g. `("SomeNumber","string") == false`,
        `("SomeFloat","int") == false`), asserting the violation is detected,
        not silently accepted; plus the conforming direction (`true`) and the
        user-concept trust case (`("MyUserConcept","string") == true`). This is
        the same test-injectable pattern as geDistinctBarrier's siblings.
      - **DoD.** `tests/tsymex_phase15_g6_concept_constraint.nim` 3/3 c+cpp
        (POSITIVE `proc clampPos[T: SomeNumber]` at `T=int` → sxSat, witness
        > 10; NEGATIVE conformance-helper injection classifies non-conforming
        pairs; COMPOUND `proc onlyInts[T: SomeInteger]` at `T=int` → sxSat,
        witness 42, no special-casing). Regression 9/9 (g4_distinct_sort,
        g5_distinct_borrow, g3_type_subst, G1a_instkey, G1c_instcap,
        rectify_generics, phase1_arith, phase4_tuple, F2_float_literals).
        Walker version stays "7" (Cluster G bumps at G10).
        **Next: G7 (`static[T]`).**
    - **G7 — SHIPPED (2026-06-15).** `static[T]` params as instantiation-key
      components.
      - **AST reality vs RFC §G7 GREEN.** Probed on the typed AST: the
        static-param CONSTRAINT is `nnkCommand[Ident "static", <T>]` (NOT the
        `nnkStaticTy` the GREEN guessed — `nnkStaticTy` is the untyped/bracket
        `static[int]` form, accepted defensively too). The static VALUE is NOT
        a call-site arg (`foo[3](a)` lowers to `Call[Sym "foo", a]` — the `[3]`
        brackets are gone); Nim's semchecker has ALREADY monomorphized the
        value INTO THE BODY (`x[N-1]`→`x[2]`, `x>N`→`x>3`, and a `static bool`
        `B`→`IntLit 0/1`). The ONLY un-substituted residue is a FORMAL param
        TYPE naming the static param as an array DIMENSION (`array[N, int]`),
        which `classifyType` cannot size until N resolves. The two
        instantiation callee Syms are DISTINCT and their `symBodyHash` ALREADY
        differs.
      - **Real key shape vs the RFC's idealized string.** RFC §G7 asserts the
        EXACT key `"foo#int;static=3"`. That is NOT the real key. G1a's key is
        `name#<bodyHash>#<sorted T=Type tuple>`, so the real G7 key is:
        (a) for a static ARRAY-DIMENSION param — the value is bound into the
        type tuple, `name#<bodyHash>#N=3` vs `…#N=5` (distinct, no collision);
        (b) for a SCALAR static param (`bar[N:static int](x:int)` /
        `gate[B:static bool]`) — N/B appears in NO formal-type position so the
        type subst is EMPTY; `instKeyFor` would collapse to the BARE name (the
        G1a collision class), so G7 appends `#<bodyHash>#static` (the bodyHash
        already differs per value → distinct keys). The TEST therefore asserts
        BEHAVIOR — two distinct instantiations each with the literal
        substituted, dispatching correctly — NOT the RFC's key string.
      - **Implementation.** `dsl_parser.nim`: `staticParamNames`/
        `genericParamsNode` (shared with `gatherTypeSubst`) detect static
        params; `gatherTypeSubst` recovers a static array-dimension N from the
        ARG's `array[range[lo..hi], _]` getType (→ `newLit(hi-lo+1)`) and adds
        `subst[N]=newLit(val)` so `monomorphize` rewrites `array[N,int]`→
        `array[3,int]`; `instKeyFor` includes the value (array case) or the
        bodyHash-discriminated `#static` suffix (scalar case). `parseCalleeImpl`
        single-expr-RHS path now emits a lifted preamble (the array index
        `x[N-1]` A-normalises) instead of asserting `preamble.len == 0`.
        `dsl_typebridge.nim`: `classifyType` matches a monomorphized
        synthesized `array[<IntLit>, T]` on the RAW node BEFORE `getTypeInst`
        (the synthesized node carries no type). `runtime.nim`: `coerceToBoolSV`
        + a widened bool `==`/`!=` arm coerce a `static bool` literal that
        arrives as `IntLit 0/1` (`value != 0`) so `(pred) == B` compares
        bool-to-bool, not bool-to-int.
      - **`cacheHitsFor`.** No such accessor exists (the RFC DoD's
        `cacheHitsFor`-zero-hits check is not buildable); distinctness is
        asserted via BEHAVIOR (per-instantiation literal index `x[2]` vs `x[4]`,
        and per-value bool polarity) instead.
      - **DoD.** `tests/tsymex_phase15_g7_static_param.nim` 2/2 c+cpp
        (static[int] arrays: `lastPos[N](x:array[N,int])=x[N-1]>0` at N=3,N=5 →
        sxSat with `a3[2]>0` AND `a5[4]>0` — the witnessed index differs,
        proving per-instantiation substitution; static[bool]: `gate[B](x)=
        (x>0)==B` at B=true,false → sxSat with opposite polarity). Regression
        9/9 (G1a_instkey, G1c_instcap, g3_type_subst, g4_distinct_sort,
        g6_concept_constraint, rectify_generics, phase4_tuple, phase4_array,
        phase1_arith). Walker version stays "7" (Cluster G bumps at G10).
        **Next: G8 (multi-parameter generics).**
    - **G8 — SHIPPED (2026-06-15).** Multi-parameter generics
      (`proc foo[T, U](a: T, b: U)`). Mostly an AUDIT + REGRESSION-GUARD cycle
      (per RFC §G8: "no structural changes beyond any bug fixes the RED test
      surfaces").
      - **Multi-param ALREADY worked — no conflation, no argIx bug.**
        `gatherTypeSubst` already iterates the formal params binding ONE entry
        per generic-named param from the matching call-site arg's `getType`;
        `argIx` advances exactly once per formal NAME (`for j in 0 ..< id.len-2`
        inside `for i in 1 ..< formal.len`), so `T` and `U` bind to their OWN
        args — there was no off-by-one collapsing both to the first arg's type
        and no T↔U conflation. G1a's `instKeyFor` already sorts the
        concrete-type tuple BY formal-param NAME (ADR-0008 D6 order-independence),
        so two DIFFERENT type tuples (e.g. `T=int,U=string` vs `T=string,U=int`)
        produce DIFFERENT keys and never collide. The RED test CONFIRMS this
        rather than driving a structural change.
      - **`T`+`U` resolve INDEPENDENTLY.** `foo[T,U]` at `T=int, U=string`:
        `a > 0` lowers as integer arithmetic on the `int` param, `b == "ok"` as
        Z3 String equality on the `string` param, in ONE proc — sxSat, witness
        `(1, "ok")`. `bar[T,U]` at `T=bool, U=int` (`a and b > 5`) → sxSat,
        witness `(true, 6)` — no accidental param-ORDER dependency.
      - **Order-independence WITHOUT collision (sorted-key for multi-param).**
        The SAME `pick[T,U]` (a `when T is int and U is string` / `elif T is
        string and U is int` body) instantiated at the REVERSED tuples
        `(int,string)` and `(string,int)` in one SUT dispatches to its
        CORRECTLY-typed body at each site SIMULTANEOUSLY (witness
        `(p=7, q="x", r="y", s=9)`). If the sorted key had collapsed the two
        tuples onto one entry, one body would be reused for both calls and the
        conjunction would be unreachable — so the simultaneous sxSat IS the
        behavioral proof the sorted multi-param key keeps distinct tuples
        distinct (the `cacheHitsFor` accessor the RFC DoD names does not exist;
        distinctness asserted via behavior, as in G1a/G7).
      - **BUG FIXED (surfaced by the RED test, ORTHOGONAL to multi-param /
        generics).** A call whose FIRST arg is an `itString` was unconditionally
        claimed by the Cluster-S `itString`-receiver call-routing guard
        (`dsl_parser.nim`, the `if recvCls0.ty.kind == itString:` block). For an
        UNRECOGNISED string-op name the guard fell through to
        `getStdlibModelFor(name, itString) == smkUnregistered → iekStrUnsupported`,
        so an ORDINARY USER PROC whose first parameter happens to be `string`
        (`proc foo(a: string, …)`, e.g. `solo(s)`) was mis-classified
        `seUnsupportedStringOp` → sxUnknown (proven minimal: even a string-first
        param NEVER compared, body `b == 9`, failed; a string-SECOND param always
        worked). Fix: when the string-receiver model is `smkUnregistered` AND the
        callee resolves to a real user `nnkProcDef`
        (`calleeSym.getImpl.kind == nnkProcDef`), `discard` (fall through) to the
        user-proc call path instead of emitting `iekStrUnsupported`. A genuinely
        unsupported stdlib string call (no user impl) still routes to
        `iekStrUnsupported` (Invariant 3 — never a silent UNSAT). This is the
        only code change; the generic / multi-param machinery is untouched.
      - **DoD.** `tests/tsymex_phase15_g8_multi_param.nim` 3/3 c+cpp
        (int+string independent; bool+int param-order-independent; reversed
        tuples dispatch distinct). Regression 10/10 (G1a_instkey, G1c_instcap,
        g3_type_subst, g4_distinct_sort, g6_concept_constraint, g7_static_param,
        rectify_generics, S3_strindex, phase1_arith, phase1_bool) + extra
        S-cluster (S1_typebridge, S4_strpred, S5_strops) green for the
        string-routing fix. Walker version stays "7" (Cluster G bumps at G10).
        **Next: G10 (Cluster G regression smoke vs E + walker version bump 7→8;
        G9 folded into G1c).**
    - **G10 — SHIPPED, Cluster G complete, walker version now 8 (2026-06-15).**
      The close-out cycle. A hermetic in-process G-cluster regression smoke
      (`tests/tsymex_phase15_g10_smoke.nim`, 7/7 c+cpp) composes the G1a–G8
      machinery TOGETHER in ONE file to catch state-threading bugs from the
      multi-file G1a–G8 edits (the `instKeyFor`/`ctx.procs` registration path,
      the per-run `currentDistinctSorts` threadvar + `WalkerStatics.distinctSorts`
      mirror, `ProcSig.conceptConstraints`, and the `maxInstantiationsPerProc`
      cap): a multi-param generic at int+string (G8); the same
      `szof[T]=sizeof(T)` at int8+int64 in one SUT (G1a collision); a
      `distinct float64` with borrowed `+`/`<` (G4+G5); a `static[int]`
      `array[N,int]` at N=3+5 (G7); a `T: SomeNumber` concept generic at int
      plus the `conformsToStdlibConcept` membership table (G6); and the cap via
      `withSymexSettings(maxInstantiationsPerProc=2)` → `geInstantiationCapped`/
      sxUnknown (G1c). The composition found NO state-threading regression —
      no production-code change beyond the bump.
      - **Walker version bumped "7"→"8"** as the final edit, single-sourced in
        `canonicalize.nim:symexWalkerVersion` (re-exported via `symex.nim`;
        Invariant 6, confirmed no duplicate). The bump orphans every "7"-era
        cache key so the broad regression re-solves. Four prior version-pin
        tests (F8_smoke, S7b_smoke, S11_mutation, E7_smoke — all pinned "7")
        advanced to "8" (the intended close-out consequence, mirroring E7
        advancing F8/S7b/S11 "6"→"7"). `determinism.md` gains the "8" history
        row + a Generics subsection.
      - **DoD.** `tests/tsymex_phase15_g10_smoke.nim` 7/7 c+cpp. Broad
        regression all green c, no hangs: ALL G tests (G1a_instkey, G1c_instcap,
        g3_type_subst, g4_distinct_sort, g5_distinct_borrow,
        g6_concept_constraint, g7_static_param, g8_multi_param),
        rectify_generics, Cluster E (E3_try, E7_smoke), Cluster S (S3_strindex,
        S5_strops, S9_caseconv, S11_mutation), Cluster F (F2_float_literals,
        F6_float_math, F8_smoke), H1_path_heap_fields, and earlier phases
        (phase1_arith, phase3_recursion, phase4_tuple, phase4_array,
        phase11_walker, phase13_unsat_roundtrip). **Cluster G COMPLETE.
        Next: C0-ADR (Cluster C — closures).**
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
- **Cluster C** (closures and procs-as-values — reconciled at C0-ADR, 2026-06-15)
  - **Reality baseline.** Closures are **UNSUPPORTED today**, full stop. There is
    NO `iekLambda`, NO `iekClosureCall`, NO `svClosure`, NO `closureSyms`, NO
    `lambdaSite` — grep over `src/` returns **zero** hits for every one of those
    symbols. A lambda / expression-position `proc(...) = …` is NOT recognised by
    the parser: `parseExpr` (`dsl_parser.nim`) has no `nnkLambda` arm, so it falls
    through its `else` to `error("symex: unsupported expression kind " & $n.kind &
    " in `" & n.repr & "`")` (`dsl_parser.nim:1144`). Nested unsupported constructs
    surface via the Phase-14 **B67** diagnostic (`scanForUnsupported`,
    `dsl_parser.nim:1620-1648`), which hints `"symex: `…` is inside an unsupported
    …"` when an `isUnsupported` statement is reached. So unlike Cluster G (where the
    feature already worked via parse-time monomorphization and the RFC's new IR was
    *redundant*), Cluster C is **genuinely net-new** — the RFC's `iekLambda` /
    `iekClosureCall` / `svClosure` machinery has no shipped counterpart and must be
    built. **No major architectural-redundancy fork here** (contrast G).
  - **★ THE LOAD-BEARING RECONCILIATION — closure-call axiom MUST be GROUND
    (the G4 hang lesson). ★** ADR-0009's `funcSym` is a Z3 **uninterpreted
    function** and the closure-call axiom relates `funcSym(env, args)` to the
    lambda body's return value(s). This is in **exactly the same hazard class** as
    G4's distinct-sort bijectivity, which the codebase proved HANGS:
    - The runtime documents it verbatim: the
      `inject_T(eject_T(a) op eject_T(b))` chain "HANGS (uninterpreted-fn-over-BV /
      MBQI; the G4 finding)" — `runtime.nim:2440-2444`.
    - The G10 handoff records the empirical finding in full: the universal
      `∀x. eject(inject(x)) == x` **HANGS 180s (MBQI loop)**, returns `unknown`
      even with triggers; **and even a GROUND but *reverse* application**
      (`inject(baseSym) == dConst`) **ALSO hangs**. The ONLY decidable model is a
      **ground per-occurrence pin** in QF_UFBV (`eject(dConst) == baseSym` — the
      fn applied to a *ground* term, equated to a value).
    - **Assessment of ADR-0009 / the RFC's closure design: GROUND, SAFE.** The
      round-2 CRIT-C4 decision text is ground/per-call-site — "for each sub-path
      `(pc_i, v_i)` assert `implies(path.pc and pc_i, funcSym(env, args) == v_i)`"
      (round2-findings line 14) — where `env`/`args` are the **concrete terms of
      the call occurrence**, not bound `∀` variables. `funcSym(env, args) == v_i`
      is structurally the same shape as G4's decidable pin (fn applied at a GROUND
      tuple, equated to a value). **ADR-0009 § D6 pins this explicitly** and
      rejects the universal axiom (Rejected Alt E). **C2b MUST implement it ground:
      one `implies(path.pc and pc_i, …)` per body sub-path, `ite`-merge for the
      result, NEVER a `∀env,args` axiom.** A universal closure axiom would hang
      exactly as G4's did. If a non-decidable need ever surfaces, the correct
      fallback is the G4 fallback (skip the relating constraint, emit a classified
      hint, degrade to `sxUnknown`) — never a quantifier.  ← **headline for C2b.**
  - **Premise / path drift table.**

    | RFC-C premise | Reality | Action for C1–C6 |
    |---|---|---|
    | `envRecord` = "the **Z3 datatype sort** of the environment tuple"; `funcSym : (envRecord_sort, params) -> ret` | **DRIFT.** The engine has **no Z3 tuple/record/datatype sort anywhere.** `svTuple` is a **Nim-side `seq[SymVal]` + `fieldNames`** (`runtime.nim:170-172`); aggregates are Nim-side trees whose *leaves* are Z3 ASTs. There is no single Z3 sort that *is* the environment. | C2b: **flatten** the env to its leaf Z3 args; `funcSym`'s domain = concatenation of per-leaf sorts ++ param sorts (via `sortOfTuple`), NOT a 1-element record sort. ADR-0009 § D2 + Rejected Alt D record this. (`Z3_mk_tuple_sort` *exists* — `ffi.nim:781` — but is deliberately NOT used.) |
    | `Z3_mk_app` / `Z3_mk_func_decl` raw FFI buildable | **TRUE.** `Z3_mk_app` (`ffi.nim:836`), `Z3_mk_func_decl` (`ffi.nim:842`), `Z3_mk_fresh_func_decl` (`:852`) all present. G4 already drives them for inject/eject (phantom `Z3FuncDecl` unusable for runtime-known sorts; "args + domains must be HEAP seqs; results must be `wrap`-ped"). | C1 PoC + C2b reuse the **exact G4 raw-FFI pattern**. Feas-H2/H10 PoC is buildable. |
    | `svTupleEq` for env equality (C5) | **DRIFT — net-new.** No `svTupleEq` (grep: 0). There is **no `svTuple` `==` arm at all** in the binop dispatch (`runtime.nim` comparison arm handles scalars/BV/bool/float/string only). | C5 adds a structural field-by-field tuple-equality helper (`svTupleEq`); net-new. |
    | `ce*` error kinds net-new (preamble's `ce` prefix; C1 `ceNotImplemented`) | **Already present** (`types.nim:611`, added at Z3a): `ceNotImplemented`, `ceUnsupportedCapture`, `ceUnsupportedHof`. | **REUSE; do NOT re-add.** C1 emits `ceNotImplemented`; C2a `ceUnsupportedCapture`; C4 `ceUnsupportedHof`. |
    | `inlinePolicy: InlinePolicy` in `SymexSettings` (C4) | **Already present** (`types.nim:731`, default `ipHybrid`; enum at `types.nim:631`). | C4 **consumes** it; do NOT redefine (matches RFC H18/M3). |
    | `seqInlineThreshold` (default 8) in `SymexSettings` (C4) | **DRIFT — net-new.** NOT in `SymexSettings` (fields: integerSemantics/queryRLimit/maxFrontierSize/maxCallDepth/maxLoopUnwind/acceptUnknownAsCovered/defectExclusions/inlinePolicy/maxSplitParts/maxBytesEncodingLen/maxInstantiationsPerProc — `types.nim:708-752`). | C4 adds the field + `defaultSymexSettings` entry + `+`-merge clause (the same field-add ripple G1c/S5/S7a did). |
    | `maxClosureInlineCount` (=64, "settings family") | **Net-new** — not in `SymexSettings`; only `maxInstantiationsPerProc`/`maxFrontierSize`/etc. exist. The preamble also speaks of a `closureInlineCount` *field on `CallFrameCtx`* (per-frame budget) — distinct from a settings cap. | If C4 wants a hard inline cap, add it; reconcile the name (`seqInlineThreshold` vs `maxClosureInlineCount`) at C4 — they may collapse to one knob. |
    | `WalkerStatics.closureSyms` (per-site funcSym memo); `CallFrameCtx.closureInlineCount` | **DRIFT — comment-only today.** Both are *mentioned in comments* (`runtime.nim:2985` "C2a (closureSyms)"; `runtime.nim:3013` "C2a closureInlineCount") but **neither field exists** on the records yet (`WalkerStatics` has exnTable/userExnHierarchy/distinctSorts; `CallFrameCtx` has handlerStack/inFlightExn/escaped/caught). | C2a adds both fields (net-new), per ADR-0009 Consequences. |
    | `symBodyHash(lambdaBody)` for site keying (Des-H6) | **Partial / verify in C1.** `symBodyHash` is used in G1a on a proc **symbol** (`calleeSym`, `nnkSym`) with a `lineInfo` fallback (`dsl_parser.nim:1890`). A lambda presents as an `nnkLambda`/`nnkProcDef` **node**; its *body* is a statement node, not necessarily a symbol `symBodyHash` accepts. | C1: confirm the exact node passed to `symBodyHash` (proc-def sym if present, else structural body hash) + carry the ADR-0008 D2 `lineInfo` fallback. The *decision* (formatting-stable hash + `declOrderIndex`) stands; the node plumbing is a C1 detail. ADR-0009 § D3 flags this. |
    | `iekLambda` emitted post-monomorphization (Depth-H4) | Consistent with G's shipped model (parse-time monomorphization, `dsl_parser.nim:1574/1588/1618`). | C1: emit `iekLambda` only on the monomorphized body; same-site `T=int`/`T=string` ⇒ distinct keys (RED test asserts). |
    | Walker version `"8"→"9"` at C6 | Current `symexWalkerVersion = "8"` (`canonicalize.nim`, bumped at G10) — correct baseline. | Bump `"8"→"9"` at C6 (closures are a walker-semantic cluster). |
    | `M2`: `iekLambda` (value-producing, `iek` prefix) not `itLambda` | The handoff's "round-2 deltas" table still says `itLambda → iekLambda`; the IR convention is `iek*`=value-producing exprs. | C1 uses `iekLambda` + the `iek`/`is`/`it` prefix comment block (M2). |

  - **Per-cycle notes.**
    - **C0-ADR — SHIPPED (this cycle, 2026-06-15).** `ADR-0009-closure-encoding.md`
      authored (Status Accepted; 8 decisions D1–D8 + 5 rejected alternatives +
      Consequences; LEADS with the ground-axiom headline invariant). `closures.md`
      skeleton authored (Overview + Encoding/Capture/Dispatch/Top-level/HOF/
      Equality/Generics/Divergences sections, each pointing to its filling cycle —
      no bare "TODO" stubs). §F-C (this subsection) reconciled. **No production
      code, no test, no build** — doc + reconciliation cycle. ADR-0008's
      closure-equality/monomorphization cross-reference is satisfied by ADR-0009's
      Related row pointing back to ADR-0008 (the DoD's "ADR-0008 cross-references
      ADR-0009" is bidirectional-in-spirit; ADR-0008 is dated 2026-06-06 and not
      edited this cycle to avoid churning a shipped doc — the linkage lives in
      ADR-0009's Related row + § D3/D8 prose).
    - **C1 — SHIPPED (2026-06-15).** Net-new `iekLambda`/`iekClosureCall`
      IRExprKind (value-producing; `iek`/`is`/`it` prefix comment block added, M2)
      + node shapes/ctors/render/canonicalize/emitExpr; `svClosure` SVKind stub
      `(closureSite: (siteHash,declOrder), closureEnv: ref svTuple)`. **REUSED**
      `ceNotImplemented` (not re-added). **`symBodyHash`-on-lambda REALITY (the C1
      verification the ADR D3 / drift table flagged): it does NOT apply.** A lambda
      in expression position is a NAMELESS `nnkLambda` / expr-position
      `nnkProcDef`/`nnkFuncDef` NODE — `symBodyHash` is a `std/macros` builtin over
      a proc SYMBOL, and there is no symbol here. So C1 uses the **ADR-0008 D2
      lineInfo fallback** directly: `siteHash = hash("file:line:col" of the lambda
      node)`, `declOrder` from a new `ParseCtx.lambdaCounter`. The *decision*
      (formatting-tolerant key + order index) stands; the node plumbing is the
      lineInfo branch, never the symBodyHash branch. (D8's concrete param types in
      the canonical key disambiguate `T=int`/`T=string` instantiations — RED test
      asserts distinct keys.) **Free-var capture approach:** scope-stack diff —
      enumerate the lambda body's `nnkSym` references whose `symKind ∈
      {nskParam,nskLet,nskVar,nskForVar}` (runtime VALUE bindings; excludes
      top-level procs/types/consts by symKind) and subtract the lambda's own params
      ++ body-local definitions (`let`/`var`/`for` LHS). First-seen source order is
      preserved (deterministic key). RED test: an outer local IS captured, an
      inner body-local and a param are NOT. (Body read at `body(n)`, the routine
      body index — `n.len-1` is a trailing synthetic `result` sym, a C1 gotcha
      found+fixed.) **Proc-valued-variable call** (vs a named-proc call): callee
      `getImpl` is NOT a routine def (it's the variable's `nnkIdentDefs`) AND
      `getTypeInst.kind == nnkProcTy` → `iekClosureCall`; top-level procs-as-values
      stay C3. Proc-typed `let` binding is placeholder-typed (no scalar IRType).
      **`svClosure` stub representation:** the lambda-site key + a boxed `svTuple`
      env placeholder (per-site `funcSym` decl is C2a's `closureSyms`, not built
      here). **`sortOfTuple` (D5):** flattens an env `svTuple` to its per-leaf Z3
      sorts via `Z3_get_sort∘rawAnyAstOf`, recursing nested tuples — the C2b
      `funcSym` domain. **`Z3_mk_app` PoC result (Feas-H2):** `c1ClosurePoCApply`
      builds an `svTuple{int,bool}` env, derives flattened domain sorts via
      `sortOfTuple`, declares an uninterpreted func-decl over the runtime-known
      sorts (`Z3_mk_func_decl`), and applies it with **HEAP-seq args**
      (`Z3_mk_app` — the G4 raw-FFI discipline; stack args SIGSEGV in Z3 4.15);
      the application round-trips (result sort == declared range). **C2b
      application path is de-risked** — the raw-FFI apply over runtime sorts works.
      **Walker STUBS both kinds** (no semantics): `lower(iekLambda)` /
      `lower(iekClosureCall)` raise `SymexClosureUnimplementedError`, caught at the
      `runSymex` boundary → `ceNotImplemented`/sevError → `sxUnknown` (Invariant 3
      — never a silent UNSAT, never a crash). **Closure iterators**
      (`nnkIteratorDef` in expr position) → an `iekLambda` carrying an
      `isUnsupported`-bodied marker so the walker stub fires `ceNotImplemented`
      (detail "closure iterators not yet supported"), not a crash — Deferred-table
      compliant. **Dual exhaustiveness ripple:** IRExprKind = **6** arms (render,
      canonicalize, emitExpr, probeProto, lower-stub, abstraction
      tryEvalInterval+collectVarRefs — collectBanFromExpr/collectAssertRangesExpr
      have `else`); SVKind = **5** arms (tyOf, iteSV, coerceIntLit, extractLeaf,
      symValHash — rawAstOf/rawAnyAstOf/bvToZ3Int/toZ3Int/toBv64ForFp/symEq/
      retBindEq/extractFromSymVal have `else`; `allocateSym` is IRType-keyed and
      there is NO `itClosure`, so it is untouched). `tests/tsymex_phase15_C1_ir.nim`
      7/7 c+cpp; 11-file regression green, no HANG. Walker version stays **"8"**
      (C6 bumps). S-cluster note: no impact. **Next: C2a.**
    - **C2a — SHIPPED (2026-06-15).** Closure CONSTRUCTION. `lower(iekLambda)`
      replaces the C1 `ceNotImplemented` stub with real construction:
      **(1) env snapshot** — each `lambdaCaptures` name is looked up in the
      CURRENT env and its SymVal collected into an `svTuple` `closureEnv` (the
      captured-locals record; a capture absent from the env is dropped, and the
      funcSym domain follows the snapshot). **NO body descent** — the lambda
      body is lowered only at APPLICATION (C2b). **(2) per-site funcSym** —
      get-or-create the uninterpreted decl over runtime-known sorts (domain =
      flattened env-leaf sorts via `sortOfTuple` ++ param sorts; range =
      `lambdaRetTy`'s sort) via raw `Z3_mk_func_decl` + `incRefFD` (the
      G4/C1 raw-FFI discipline — heap domain seq, decl held for the run).
      **(3)** assemble `svClosure{closureSite, closureEnv, closureRawFD}`.
      **`closureSyms` placement decision:** the memo is the **net-new
      `currentClosureSyms` threadvar** (`Table[ClosureSymKey, RawZ3FuncDecl]`,
      reset at `runSymexImpl` entry), NOT populated directly on a `WalkerStatics`
      field — because `lower(iekLambda)` runs in the pure env→SymVal evaluator
      with **no `WalkCtx` in scope** (exactly the G4 `currentDistinctSorts`
      situation). The **net-new `WalkerStatics.closureSyms` field** mirrors the
      threadvar after the walk for inspection (the drift-table row's "C2a adds
      both fields" is honoured: `closureSyms` lands as a real WalkerStatics
      field PLUS its live threadvar populator). **Key = `ClosureSymKey =
      ((siteHash, declOrder), envSortId, paramsSortTupleId)`** where the sort
      ids are `Z3_get_sort_id` fingerprints of the flattened env-leaf sorts and
      the param sorts (so the SAME site at two monomorphizations — distinct
      leaf/param sorts — memoizes distinct funcSyms, D8). **Net-new
      `svClosure.closureRawFD: RawZ3FuncDecl`** field (verified the real nim-z3
      raw func-decl type — the same handle `Z3_mk_func_decl`/`incRefFD` take and
      G4's inject/eject use; nil in the C1 stub). `extractFromSymVal(svClosure)`
      → classified `ceNotImplemented`/sevError (closure as a top-level SUT
      RESULT unsupported — classified, not silent; Invariant 3).
      `symex.nim emitTyAndReader`: a proc/closure type
      (`classifyType(nnkProcTy)` → `tUninterp("__closure")` placeholder) renders
      a `proc` placeholder + a compile-time `{.warning.}` (closures as a
      top-level param/result type unsupported, Invariant 3) — note `emitTyAndReader`
      renders only SUT INPUT-PARAM witnesses, so this path is the
      classified-rejection guard, never reached for the C2a RED SUT which
      returns `int`. **`closureInlineCount` (CallFrameCtx) deferred to C2b** —
      it's an APPLICATION-descent budget (no descent in C2a), added when C2b
      wires the call. **`iekClosureCall` arm STAYS `ceNotImplemented`** (C2b).
      **Test hook:** the RED test introspects the non-exported
      `svClosure.closureEnv` via the exported `c2aClosureProbe` /
      `c2aClosureProbeRelowered` hooks (runtime.nim) — they set up a context,
      reset `currentClosureSyms`, build the construction-time env at the
      `let f = …` binding point, lower a hand-built `iekLambda` against it via
      the real `lower`/`buildClosure` path, and return a plain
      `C2aClosureProbe` record (env-tuple kind/fieldNames/field-hash-matches-
      offset, funcDecl-live, closureSyms len) — keeping `Env`/`lower`/
      `symValHash` encapsulated. `tests/tsymex_phase15_C2a_closure_capture.nim`
      3/3 c+cpp; 10-file regression green (C1_ir, phase4_tuple, phase1_let,
      phase1_arith, phase3_recursion, g4_distinct_sort, E3_try, S11_mutation,
      F8_smoke, g10_smoke) no HANG. Walker version stays **"8"** (C6 bumps).
      **Next: C2b.**
    - **C2b — SHIPPED (2026-06-15).** ★ Closure CALL dispatch, the cluster
      CORE. `lower(iekClosureCall)` (a C1/C2a `ceNotImplemented` stub) now
      dispatches via the net-new `lowerClosureCall`. **The GROUND axiom confirmed
      NO-HANG (the headline risk).** For each body return sub-path `(pc_i, v_i)`
      the walker asserts `implies(and(branch_conds_i), funcApp == v_i)` — the
      per-site `funcSym` applied at the GROUND `(env, args)` of THIS occurrence
      (raw `Z3_mk_app`), equated to a value; structurally identical to G4's
      decidable eject-pin. NO `∀env,args` anywhere; the axioms drain into every
      `trySolve` like `parseIntGateConstraints` (each is a closed implication,
      vacuously true off its branch). Empirically the 3 sub-tests + 11-file
      regression run to completion (no 137/HANG). **How `svClosure` reaches the
      lambdaBody:** `svClosure` carries `closureSite` + `closureEnv` +
      `closureRawFD`, NOT the body IR — so `buildClosure` (C2a path) now ALSO
      stashes the `lambdaBody`+params+captures+retTy into the **net-new
      `currentClosureBodies` site→body map** keyed by `(siteHash, declOrder)`;
      the call resolves the closure, keys back into the map, and descends. (Sound
      because the site key uniquely identifies the monomorphized lambda IR.)
      **Descent + sub-path collection:** `lowerClosureCall` runs in the `lower`
      evaluator (no `WalkCtx`), so it reaches the live walk via the **net-new
      `currentWalkCtxPtr` threadvar** (a `ptr WalkCtx` published in `runSymexImpl`
      just before the top-level `walk`); it pushes a CallFrame whose retSym = the
      funcApp, `walk`s the body once, and harvests sub-paths from BOTH the
      explicit-`return` channel (`frame.returnedPaths`, the E2b/E3 machinery) and
      the implicit-`result`/fall-through channel (a value-returning lambda whose
      last stmt is `result = EXPR` leaves the value in `cp.env["result"]`).
      **`closureInlineCount` budget:** the C2a-deferred **net-new
      `CallFrameCtx.closureInlineCount`** field is bumped per nested descent and
      checked against the **net-new `SymexSettings.maxClosureInlineCount`**
      (default 64; +default+merge clause); overflow → **net-new
      `ceInlineBudgetExceeded`**/sevError/sxUnknown. **Raw `Z3_mk_app`
      application + result-SymVal shape:** the funcSym is applied (C1 PoC pattern,
      heap arg seq) over the flattened env-leaf asts ++ flattened call-arg asts
      (net-new `flattenLeafAsts`, the ast-side mirror of `sortOfTuple`); the
      `Z3AnyAst` result is `wrap`-ped to the typed SymVal per `lambdaRetTy` (net-
      new `symValFromRawAst`) — that funcApp IS the call's result SymVal, the
      ground axioms tie it to the sub-path values (ADR-0009 D6: "the funcSym
      application IS the result"). **Proc-valued-param resolution:** a
      `proc(x:T):T` PARAM (e.g. `applyTwice[T]`'s `f`) is bound in the env as an
      svClosure when the lambda arg is C2a-constructed at the call site; the SAME
      `iekClosureCall` dispatch resolves it (NOT `ceClosureUnknownCallee`) — no
      separate path. Two parser fixes this needed: (a) a synthesized `nnkProcTy`
      formal carries no type, so `classifyType` matches it structurally BEFORE
      `getTypeInst` (→ the `__closure` placeholder); (b) the closure CALL is now
      detected EARLY in `parseExpr` (`earlyClosureCallDetect`, before the
      string-builtin routing, which would `classifyType(n[1])`-crash on a
      closure-call arg like `f(f(v))`). **net-new `ceClosureUnknownCallee`** for
      an unresolved callee (Invariant 3). `tests/tsymex_phase15_C2b_closure_call.nim`
      3/3 c+cpp. C1_ir's stale "walker STUBS a lambda SUT" test updated to assert
      the now-modeled sxSat. Walker version stays **"8"** (C6 bumps). **Next: C3.**
    - **C3 — SHIPPED (2026-06-15).** Top-level procs as VALUES (unit-env). A
      module-scope proc referenced in EXPRESSION position (`let g = double`, or
      `double` passed as a proc-valued ARG) is now encoded as an `iekLambda` with
      `lambdaCaptures = @[]` (a **unit-env closure**: a zero-field `svTuple` env),
      reusing the C2a `buildClosure` construction + C2b `lowerClosureCall`
      dispatch wholesale — **no new walker semantics, no new IR table, no
      canonicalize change**. **Parser:** the bare-`nnkSym` VALUE-position branch
      of `parseExpr` (the `mkVar` fall-through) detects `symKind(n) == nskProc`
      with a resolvable `nnkProcDef` `getImpl` and routes to the net-new
      `parseProcAsValue` → `iekLambda`; body/params/retTy come from the proc's
      `getImpl` via the net-new **shared `parseRoutineToLambda` core** (factored
      out of `parseLambda`; a `forceNoCaptures` flag skips the free-var scan — a
      module-scope proc has no enclosing runtime scope to capture). **The
      value-vs-callee distinction (the headline regression risk) is structural,
      not heuristic:** a proc in CALLEE position is `n[0]` of an `nnkCall`, parsed
      STRUCTURALLY and never through `parseExpr`, so `double(n)` stays a normal
      `isCall` (Phase 3); a call THROUGH a proc-valued LOCAL (`g(n)`) is C2b's
      `earlyClosureCallDetect` → `iekClosureCall`; a proc-valued PARAM is
      `nskParam` (≠ `nskProc`) → stays C2b's svClosure path. ONLY a bare
      module-proc symbol in value position reaches the new branch — verified by
      the full proc-call-heavy regression (recursion/mutual/summarization)
      staying green. **`symBodyHash` on a top-level proc WORKS** (verifying the
      ADR D3 / drift-table open question for the top-level case): unlike C1's
      nameless lambda — where `symBodyHash` does NOT apply and C1 fell back to a
      lineInfo hash — a top-level proc HAS a symbol, so the site key reuses the
      existing `bodyHashPart` helper (`symBodyHash(procSym)` with the ADR-0008 D2
      lineInfo fallback), `declOrder = 0` (D3). **Runtime:** `buildClosure`
      already materialises the zero-field unitEnv on the empty-capture path; a
      `doAssert envRecord.fields.len == 0` guard is added on the
      `lambdaCaptures.len == 0` path (the spec's "C3 walker assertion"). **The
      proc-as-value call gives the SAME witness AND verdict as a direct call:**
      `let g = double; g(n)` gated at `result == 10` → sxSat, witness `n == 5`,
      EQUAL to a SUT that calls `double(n)` directly (the encoding is
      semantically transparent). `tests/tsymex_phase15_C3_proc_as_value.nim` 2/2
      c+cpp; 10-file regression green (C1_ir, C2a_closure_capture,
      C2b_closure_call, phase3_recursion, phase3_mutual, phase3_summarization,
      g8_multi_param, rectify_generics, phase1_arith, F8_smoke) no HANG. Walker
      version stays **"8"** (C6 bumps). **Next: C4.**
    - **C4 — SHIPPED (2026-06-15).** DSL HOFs `filter`/`map`/`fold` over
      `seq[T]`. A net-new **walker HOF dispatch** (parser `hofDispatch` block in
      the `nnkCall` arm) intercepts `filter`/`map`/`fold` **GUARDED on origin**
      (`calleeSym.owner.strVal == "sequtils"`) → net-new `iekHofCall`; a
      non-sequtils same-named proc owns to its own module and **falls through**
      to the normal isCall descent (the Des-LOW-L3 regression guard — verified:
      a user `filter` is NOT hijacked, no `ceUnsupportedHof`). Net-new
      `iekSeqLit` (`@[a,b,c]`/`@[]` → concrete-length svSeq) supplies the
      concrete length the inline path needs. **mapArray reality:** `mapArray`
      (`z3/funcdecl`) is `Z3_mk_map` — a **decidable pointwise array-map, NOT a
      universal-∀** — so the symbolic-`map` axiom path TERMINATES (confirmed no
      hang; the closure funcSym is left opaque — a sound over-approximation, the
      G4 lesson). **`fold` reality:** `std/sequtils` `foldl`/`foldr` are
      **TEMPLATES** the typed macro EXPANDS to a `for…items` loop **before** the
      parser runs, so fold never reaches the HOF handler through std/sequtils;
      `walkHofFold` exists/is wired but the realised closure HOFs are
      `map`/`filter` (real `{.closure.}` procs). **INLINE path** (concrete
      `simplify(seqLen)` ≤ `seqInlineThreshold`, under `ipHybrid`/
      `ipAlwaysInline`): unroll `0..<N`, apply the closure per element via the
      net-new `applyClosureGround` (factored out of C2b `lowerClosureCall` — the
      ground funcSym-app + body-descent + GROUND axiom, reused once per element);
      map = per-element store; filter = compacted keep-mask
      (`keptLen += ite(pred_i,1,0)`); quantifier-free, bounded by N≤8 (no
      fan-out). **AXIOM path** (symbolic length): map → `mapArray`
      (capture-free int→int; else classified); **filter →
      `ceUnsupportedHof` (sevError → sxUnknown)**, axiomatize-filter DEFERRED to
      **Phase 16** (no Z3 seqFilter). Net-new `SymexSettings.seqInlineThreshold`
      (= 8) with the defaultSymexSettings / `+`-merge ripple + net-new
      `validateSymexSettings` warning when set with a non-`ipHybrid` policy;
      `inlinePolicy` + `seqInlineThreshold` added to the **canonicalize settings
      digest**. `tests/tsymex_phase15_C4_hof.nim` 5/5 c+cpp; 10-file regression
      green no HANG (C1_ir, C2a/b, C3, phase5_seq, F9b_seq_float, g8_multi_param,
      phase3_recursion, F8_smoke, S11_mutation). Walker version stays **"8"**
      (Cluster C bumps at C6). **Next: C5.**
    - **C5 — SHIPPED (2026-06-15).** Closure EQUALITY (nominal-for-site +
      structural-for-env, ADR-0009 D7). `bEq`/`bNe` on two `svClosure` operands
      now dispatch via the net-new `closureEq` — inserted in the comparison arm
      of `lower(iekBinop)` (BOTH the probe-hit and probe-miss branches), right
      after `ejectBase(lower(...))` and before the int/bool/float/string/BV
      dispatch (`ejectBase` passes `svClosure` through unchanged). **Different
      site** (`(c1.siteHash,c1.declOrder) != (c2.…)`, a pure Nim-side
      integer-pair compare, NO Z3) → always unequal (`==`→`mkBool(false)`,
      `!=`→`mkBool(true)`); the common case stays entirely off the solver.
      **Same site** → equal iff captured envs are structurally Z3-equal via the
      **net-new `svTupleEq(a,b): Z3Bool`** — the FIRST `svTuple` `==` arm in the
      engine (none existed per the C0-ADR drift-table row): a field-by-field
      conjunction over the **net-new `svLeafEq`** (int/bool/BV8-64/float32-64/
      string; `svDistinct` ejects-to-base and recurses), recursing nested
      tuples + concrete-length arrays; a ZERO-field unit-env (C3 top-level proc)
      is vacuously `mkBool(true)`. `!=` negates. **`svTupleEq` confirmed NOT to
      break tuple handling** — the C0-ADR risk — phase4_tuple + phase11_walker
      stay green. **Sub-test-2 ADAPTATION:** the RFC's canonical same-site shape
      is a closure-RETURNING closure (`mk` returns a proc); **OUT OF REACH** in
      C5 — a closure-call result is wrapped by `symValFromRawAst`, which only
      handles SCALAR return kinds (a proc/closure return raises "unsupported
      closure return type kind", verified runtime.nim:4851-4878). Adapted to the
      closest SOUND same-site construction: `let f = proc(y:int):int = y+x;
      let g = f` — `f`/`g` share the SAME `(siteHash,declOrder)` AND env, so
      `f == g` takes the structural-env branch and asserts `svTupleEq` over the
      one-field `{x}` env → sxSat. **Sub-test-4 reconciliation (lineInfo vs
      symBodyHash):** the RFC §C5 (and ADR-0009 Rejected-Alt-A) assume
      `symBodyHash` (semantic-AST hash, formatting-stable), but C1 keys NAMELESS
      lambdas by **lineInfo** (`file:line:col`, POSITION-based, NOT
      formatting-stable across positions — a nameless lambda has no symbol).
      So the RFC's "two whitespace-differing versions → same siteHash" does NOT
      hold under lineInfo keying (different positions → different siteHash, which
      is CORRECT — they ARE different sites). Sub-test-4 was ADAPTED to test what
      lineInfo keying actually guarantees: a comment INSIDE the lambda body does
      not move the declaration `line:col`, so a same-position lambda keys STABLY
      (same-site equal → sxSat) and the verdict is DETERMINISTIC across re-runs.
      We do NOT assert the formatting-stability lineInfo cannot provide.
      `tests/tsymex_phase15_C5_closure_eq.nim` 5/5 c+cpp (distinct-site `==`→
      sxUnsat; distinct-site `!=`→sxSat; same-site alias `==`→sxSat; runtime-
      divergence documenting test; lineInfo same-position stable+deterministic).
      10-file regression green no HANG (C1_ir, C2a/b, C3, C4, phase4_tuple,
      phase11_walker, g4_distinct_sort, phase1_arith, F8_smoke). closures.md
      C2a/C2b/C3/C4/C5 subsections completed + the lineInfo-vs-symBodyHash
      reconciliation; determinism.md closure section added. Walker version stays
      **"8"** (Cluster C bumps at C6). **Next: C6.**
    - **C6 — SHIPPED (2026-06-15). Cluster C COMPLETE, walker version now 9.**
      Hermetic in-process C-cluster regression smoke
      (`tests/tsymex_phase15_C6_smoke.nim`, 9/9 c+cpp) composing the C1–C5
      machinery TOGETHER to catch state-threading bugs from the multi-file
      edits: closure construction + call observing a captured value (C2a/C2b);
      a proc-valued PARAMETER (`applyTwice[T]` — also exercises Cluster G
      generic instantiation, the RFC §C6 C+G composition); a top-level proc as
      a VALUE (C3) matching the direct call; bounded `filter`/`map` HOFs with a
      closure (C4 inline path); closure equality (C5 — distinct sites unequal →
      sxUnsat, same-site alias + same env → sxSat via `svTupleEq`); plus the
      DoD `withSymexSettings() do (s): s.maxClosureInlineCount = 8` override
      still witnessing a closure call. The composition found **NO state-threading
      regression** — the instantiation-cache / `closureSyms` / `currentClosureBodies`
      scopes are already cleanly separated, so **no production code changed
      beyond the version bump**. **Walker version bumped `"8"→"9"`** single-sourced
      in `canonicalize.nim:symexWalkerVersion` (Invariant 6 — confirmed no
      duplicate in runtime.nim); the bump orphans every `"8"`-era cache key.
      Five prior version-pin tests (F8_smoke, S7b_smoke, S11_mutation, E7_smoke,
      g10_smoke — all pinned `"8"`) advanced to `"9"`. Broad regression sweep
      all green c, no hangs: ALL C tests, the Cluster G sample (G1a_instkey,
      g4_distinct_sort, g8_multi_param, g10_smoke, rectify_generics), E3_try/
      E7_smoke, S3_strindex/S11_mutation, F2/F8_smoke, H1, and earlier phases
      (phase1_arith, phase3_recursion, phase4_tuple, phase5_seq, phase11_walker,
      phase13_verdict_primitives). Registered in `proptest.nimble`. SYMEX_PLAN.md
      C6→SHIPPED + Cluster C COMPLETE; determinism.md `"9"` version-history row +
      Closures bump note. **Next: R1a (Cluster R — ref/ptr, the FINAL cluster).**
  - **Net-net for the orchestrator.** Cluster C is **genuinely net-new** (no
    redundancy fork like G's). The single most important implementation
    constraint is the **ground closure-call axiom** (C2b) — the G4 hang lesson
    applies directly. Secondary reconciliations: env is a **Nim-side `svTuple`,
    flattened to leaf args** (not a Z3 record sort); `ce*` kinds + `inlinePolicy`
    **already exist** (reuse); `seqInlineThreshold`, `svTupleEq`, `closureSyms`,
    `closureInlineCount` are **net-new**; `symBodyHash`-on-lambda needs a C1
    node-plumbing check. No genuine architectural fork requiring a human call.

- **Cluster R** (ref/ptr aliasing via logical heap — the FINAL cluster;
  reconciled at R1a, 2026-06-15)
  - **Reality baseline (verified against real code).**
    - **H1 heap scaffolding CONFIRMED present and correct.** `Path` carries
      `heaps: Table[string, Z3AnyAst]`, `heapDepth: int`, `allocCounters:
      Table[string, int]` (runtime.nim), deep-copied at every fork via
      `forkPath`/`deepCopyHeapState`. INERT through R1a (the walker neither reads
      nor writes them yet — no heap SEMANTICS land until R1+). Cluster R inherits
      this; R1a does not touch it.
    - **`he*` error kinds — REALITY:** the `he`-prefix kinds
      `heDepthExhausted`, `heUnsafeCast`, `hePtrArith`, `hePtrFamily`,
      `heFreshnessCapExceeded`, `heUnsupportedVarRef`, `heRefVariantUnsupported`,
      `heUnsupportedOwnership` **already existed** in `SymexErrorKind`
      (types.nim, from the Z3-Enum cycle — the prefix scheme was provisioned
      ahead of the cluster). **Only `heUnresolvedRef` was NET-NEW in R1a**
      (the R1a stub kind; added to the enum).
    - **The ref-unwrap site (reconciliation §A:128).** There are TWO ref/ptr
      paths in `classifyType` (dsl_typebridge.nim): (1) the **inline** `ref T`/
      `ptr T` path — pre-R there was NO structural `nnkRefTy`/`nnkPtrTy` arm, so
      a bare inline `ref int` param fell through to the unsupported-type
      `error()`; R1a ADDS `nnkRefTy`→`tRef(pointee)` / `nnkPtrTy`→`tPtr(pointee)`
      arms. (2) the **named** `type Foo = ref object` path at `:178` (getImpl →
      nnkTypeDef → `underObj.kind in {nnkRefTy,nnkPtrTy}` → unwrap to the inner
      object/sym). **R1a leaves path (2) UNCHANGED** — a named `ref object` SUT
      still unwraps to its pointee value model, so `tsymex_rectify_refs.nim`
      (`type Counter = ref object`; `proc atZero(c: Counter)`) is **NOT
      regressed** (re-ran green). The behaviour CHANGE is strictly for INLINE
      `ref T`/`ptr T`, which now classifies to `itRef`/`itPtr` and STUBS to
      `heUnresolvedRef`/sxUnknown instead of erroring at compile time.
  - **R1a — SHIPPED.** Purely STRUCTURAL (IR + SVKind + exhaustive dispatch
    stubs; the walker STUBS `itRef`/`itPtr`/`isDeref`/`isNew` with a classified
    `heUnresolvedRef` → `sxUnknown`, Invariant 3 — no heap semantics, those land
    R1–R13).
    - **types.nim:** `IRTypeKind += itRef(refPointeeTy)/itPtr(ptrPointeeTy)`;
      `IRStmtKind += isDeref(dRetName/dPtr/dElemTy/dPtrFamily)/isNew(nRetName/
      nRefTy)`; ctors `tRef`/`tPtr`/`mkDeref`/`mkPtrDeref`/`mkNewT`; `==`/`$`/
      `render` arms; `SymexErrorKind += heUnresolvedRef` (net-new — the other
      `he*` already existed); `SymexSettings.maxHeapDepth: int` (default 8;
      0=unlimited) + default + `+`-merge (the field-ripple pattern).
    - **runtime.nim:** `SVKind += svRef(refAst)/svPtr(ptrAst,ptrFamily)`; new
      `SymexRefUnresolvedError`/`SymexOwnershipUnsupportedError` caught at the
      `runSymex` boundary → `heUnresolvedRef`/`heUnsupportedOwnership` (sevError)
      → `sxUnknown`; walker STUBS `walk(isDeref/isNew)` + `allocateSym(itRef/
      itPtr)` (the `ref T`/`ptr T` param path) with the classified halt.
    - **dsl_typebridge.classifyType:** inline `nnkRefTy`→`tRef`, `nnkPtrTy`→
      `tPtr` (the §A:128 behaviour change); `owned T` / `WeakRef[T]` / `Atomic[T]`
      → `__ownership:*` placeholder → `heUnsupportedOwnership` (Breadth-LOW-L4).
    - **dsl_parser.nim:** `emitIRType`/`emitStmt` arms for the new IR nodes
      (round-trips the runtime IR literal).
    - **The TRIPLE ripple (compiler-driven exhaustiveness arm counts):**
      - **IRTypeKind (itRef/itPtr) = 9 dispatch sites:** `emitIRType`,
        `canonicalize(IRType)`, `==`, `$`, `allocateSym`, `tyOf`, `defaultZero`,
        the runSymex param-alloc dispatch, `emitTyAndReader`.
      - **IRStmtKind (isDeref/isNew) = 8 dispatch sites:** `emitStmt`,
        `canonicalize(IRStmt)`, `render`, `collectBan`, `collectSetLitMembers`,
        `collectTableLitKeys`, `scanStmt`, `walk`.
      - **SVKind (svRef/svPtr) = 5 dispatch sites:** `tyOf`, `iteSV`,
        `coerceIntLit`, `extractLeaf`, `symValHash`.
    - **Test** `tsymex_phase15_R1a_ir.nim` (9 tests) green c+cpp 9/9. **No
      walker version bump** (Cluster R bumps `"9"→"10"` at R12; stays `"9"`).
      Regression all green, no HANG: phase1_arith, phase1_let, phase3_recursion,
      phase4_tuple, phase5_seq, phase11_walker, g4_distinct_sort, C6_smoke,
      E7_smoke, S11_mutation, F8_smoke, g10_smoke, **rectify_refs** (the
      ref-unwrap-dependent test — UNCHANGED behaviour, confirmed not regressed).
      **Next: R1** (ref sort introduction — `WalkerStatics.refSorts`/`nilConsts`/
      `allocRefSort`; promote the `isDeref` stub to a real `select`).
  - **R1 — SHIPPED.** The FIRST real heap semantics (ADR-0010). Promoted R1a's
    `itRef`/`itPtr`/`isDeref` stubs to live Z3 — a logical heap modelled as a
    per-type `Z3Array[Ref_T, T]` over an uninterpreted address sort.
    - **Ref sort (per-WALKER):** `WalkerStatics.refSorts: Table[string,
      RawZ3Sort]` (the `Ref_<typeId>` uninterpreted sort, allocated by
      `allocRefSort(ctx, pointeeTy)` via `mkUninterpretedSort(ctx, "Ref_" &
      typeId)` once per pointee typeId) + `WalkerStatics.nilConsts:
      Table[string, Z3AnyAst]` (the `nil_<typeId>` distinguished const).
      Footgun discipline reused from G4: **`Z3_inc_ref(Z3_sort_to_ast(sort))`**
      pins the fresh sort or the heavy heap/const allocation that follows lets
      Z3 GC it (the `Z3_UNKNOWN_SORT` SIGSEGV). LIVE populators are the
      `currentRefSorts`/`currentNilConsts` threadvars (the G4/C2a idiom —
      `allocateSym` has no WalkCtx); reset at `runSymexImpl` entry; mirrored
      into `WalkerStatics` post-walk for inspection.
    - **Heap (per-PATH):** each `path.heaps[typeId]` is lazily materialised on
      first deref to a free `Z3Array[Ref_T, T_sym]` variable (built via raw
      `Z3_mk_array_sort` + `Z3_mk_const` — the key sort `Ref_T` is a RUNTIME
      uninterpreted sort, which the typed generic `mkArrayVar[K, V]` cannot
      express). The surviving deref path carries the heap forward so a second
      deref of the same ref reads the same array.
    - **isDeref → GROUND select:** `p[]` lowers to `Z3_mk_select(path.heaps[
      typeId], p)` — a single decidable array read (QF_AUFLIA-ish). **No
      universal-∀ axiom is ever asserted over the uninterpreted sort** (the G4
      MBQI hang lesson); the select alone is sufficient and **confirmed NOT to
      hang** (both the sat witness and the same-ref contradiction `42 ∧ 43` →
      sxUnsat resolve under the bounded runner). `allocateSym(itRef/itPtr)`
      builds the param's fresh `Ref_T` const → `svRef(refAst, refPointee)` /
      `svPtr(ptrAst, ptrFamily, ptrPointee)` (the pointee type is now carried on
      the SymVal so `tyOf` and the witness reader resolve it).
    - **dsl_parser.nim:** `nnkDerefExpr`/`nnkHiddenDeref` over a ref/ptr operand
      A-normalise into an `isDeref` stmt (fresh let binds `p[]`); a non-ref
      hidden-deref keeps the pre-R unwrap.
    - **symex.emitTyAndReader (C7 / Breadth-CRIT-1):** `itRef` renders
      `(var c = new(T); c[] = <pointeeReader>; c)` — a heap cell whose deref
      equals the value `p[]` took in the model; `extractFromSymVal(svRef/svPtr)`
      writes the dereffed value (recorded under the param name in the
      `currentHeapDerefVals` hook at deref time) at the param's witness path, or
      a default-zero leaf if never dereffed (so the reader never KeyErrors).
      `ptr T` renders a `nil` placeholder + classified `{.warning.}` (full
      pointer-family witness lands R8; the heap-snapshot witness format —
      alias groups / nil rendering — lands R11b/R12).
    - **Test** `tsymex_phase15_r1_refsort.nim` (2 tests, the deref-sat witness
      asserting `p[] == 42` and the same-ref contradiction → sxUnsat) green
      c+cpp. Two obsoleted R1a stub-assertions (ref/ptr param → sxUnknown +
      `heUnresolvedRef`) updated in `tsymex_phase15_R1a_ir.nim` to the R1
      promotion (→ sxSat, no classified ref halt). **No walker version bump**
      (stays `"9"`; Cluster R bumps at R12). Regression all green c, no HANG:
      R1a_ir, rectify_refs, phase4_tuple, phase5_seq, g4_distinct_sort,
      phase1_arith, C6_smoke, F8_smoke; cpp parity on the array/sort-touching
      tests + R1. **Next: R1b** (inter-procedural heap threading).
  - **R1b — SHIPPED.** Inter-procedural heap threading at every call boundary
    (ADR-0010 R1b). Heap state crosses call frames so a callee deref reads the
    SAME heap array the caller constrained.
    - **`isCall`/`isGenericCall` arms (structural, already correct via H1).**
      Call ENTRY: the `calleePath = forkPath(p, ...)` clone already deep-copies
      the caller's `heaps`/`allocCounters` (`deepCopyHeapState`) + `heapDepth`
      (by value) into the callee — so R1's "fresh-empty default" was actually
      already the caller's threaded heap once R1 made `heaps` live. Call RETURN:
      the survivor `forkPath(cp, ...)` forks from the returned CALLEE path `cp`,
      giving `heaps` REPLACEMENT (callee's exit heaps become the caller's — so
      callee heap mods are observed) + `heapDepth` from `cp`. **The one R1b
      code-change on this arm:** `allocCounters` is merged by **`max(caller[T],
      callee[T])` per type key** (NOT the plain replacement `forkPath` gives),
      preserving the freshness invariant — a post-call caller `new T` uses a
      counter above any callee allocation and can't collide with a
      callee-allocated ref on this path. (Inert until R2 wires the increments;
      correct by construction now.) `isGenericCall` lowers to `isCall` (no
      separate IR kind), so it's covered by the same arm.
    - **`iekClosureCall` arm (new threadvar plumbing).** A closure call is
      lowered inside `lower` (a pure env→SymVal evaluator with NO `Path` in
      scope — the `currentWalkCtxPtr` constraint), so the closure `descentBase`
      could not see the caller path's heap. R1b adds `currentCallerHeaps`/
      `currentCallerHeapDepth`/`currentCallerAllocCounters` threadvars (the E8/
      C2b idiom; reset at `runSymexImpl` entry), seeded per-path by the new
      `seedCallerHeapThreadvars(p)` at the `isCall`/`isIf`/`isLet`/`isAssign`
      arms before expression lowering; `applyClosureGround` builds the closure
      `descentBase` from them instead of a fresh-empty heap. So a deref inside a
      closure body reads the caller's threaded heap. **Closure heap WRITES back
      out** (the closure return-merge) are inert until R4 — closures cannot yet
      mutate the heap; R1b threads the closure READ (entry) direction only.
    - **Test reconciliation — the RFC test needs a WRITE that is R4.** RFC §R1b's
      literal SUT does `p[] = 7` (a heap WRITE → `store`), but heap WRITES are
      cycle R4, NOT yet implemented (R1 did only the deref/select READ). So the
      RFC SUT cannot pass at R1b without pulling R4 forward. We took **no-write
      approach (a)** — prove threading via the SAME-REF deref consistency R1
      already gives: POSITIVE caller deref-constrains `p[] == 7`, callee
      `inner(p)` reads `q[] == 7` on the SAME threaded heap → consistent →
      **sxSat**; NEGATIVE (the actual THREADING PROOF) caller `p[] == 7`, callee
      `inner2(p)` reads `q[] == 8` on the same threaded heap → the one heap can't
      map `p` to both 7 and 8 → **sxUnsat**. WITHOUT R1b threading the callee
      would get a FRESH empty heap, `q[]` would be unconstrained, and the
      conjunction would be sxSat — so the **sxUnsat verdict is what PROVES** the
      heap is genuinely threaded across the call boundary (R4 will reprove the
      same SUT through a real write). No scope creep into R4's write/alias
      semantics.
    - **Test** `tsymex_phase15_r1b_callheap.nim` (2 tests, the positive sxSat +
      the threading-proof negative sxUnsat) green c+cpp 2/2, **confirmed NOT to
      hang** under the bounded runner. **No walker version bump** (stays `"9"`;
      Cluster R bumps at R12). Regression all green c, no HANG: r1_refsort,
      R1a_ir, rectify_refs, phase3_recursion, phase3_mutual,
      phase3_summarization, C2b_closure_call (the closure-arm threadvar change —
      sound), E3_try, phase4_tuple, C6_smoke (HOF map/filter closures), F8_smoke;
      cpp parity on r1_refsort + C2b_closure_call. **Next: R2** (`new T`
      semantics — per-path `allocCounters` increments + fresh-ref distinctness;
      rides the R1b `max`-merge).
  - **R2 — SHIPPED.** `new T` allocation semantics (ADR-0010 R2), replacing
    R1a's `isNew` stub.
    - **`freshRef`/`assertFreshness` — GROUND inequalities.** `freshRef(ctx,
      refSort, typeId, path)` increments `path.allocCounters[typeId]` (per-path;
      R1b already threads + `max`-merges it across calls so the counter is
      monotone along a path and a post-call caller alloc can't collide with a
      callee one) and mints a FRESH `Ref_T` const `ref_<typeId>_<n>` (n = the
      NEW counter value) via raw `Z3_mk_const` (the G4 raw-const discipline — no
      typed phantom exists for a runtime-known uninterpreted sort).
      `assertFreshness(ctx, path, typeId, newRef, settings)` asserts into
      `path.pc`: `newRef != nil_<typeId>` (ALWAYS — a freshly allocated ref is
      never nil) AND `newRef != prior` for every PRIOR LIVE ref of this sort on
      THIS path (the counter-based distinctness). **All GROUND** (`Z3_mk_eq`
      negated) — **NO universal-∀** over the uninterpreted ref sort (the G4 MBQI
      hang lesson); confirmed NOT to hang (the alias case `p == q` resolves to
      sxUnsat under the bounded runner).
    - **Tracking prior live refs (the question R1/R1b left open).** R1/R1b kept
      `allocCounters` (a per-type COUNT) but NOT the actual minted consts, which
      `assertFreshness` needs for the `newRef != prior` pairwise inequalities.
      R2 adds **`Path.liveRefs: Table[string, seq[Z3AnyAst]]`** (keyed by the
      same `refPointeeTypeId`), threaded through `deepCopyHeapState`/`forkPath`
      exactly like `heaps`/`allocCounters`. `assertFreshness` reads
      `path.liveRefs[typeId]` then appends `newRef`.
    - **Per-path counter isolation (DoD test 2).** Because `liveRefs` (and
      `allocCounters`) are VALUE-copied at every fork, DISJOINT forked branches
      do NOT share priors — a `new T` on branch B restarts from the fork
      snapshot's list, so NO cross-path `ref_T_i != ref_T_j` is ever emitted.
      Tested observably: `disjointNews(b)` allocates a branch-local ref on EACH
      arm and reads a branch-specific deref value; armA and armB are BOTH sxSat
      (neither pruned by the other's allocation).
    - **Cap → `heFreshnessCapExceeded` (sound over-approximation).** NET-NEW
      `SymexSettings.maxFreshnessAssertions: int = 256` (0 = unlimited, the
      `maxFrontierSize` convention) + `defaultSymexSettings` + `+`-merge
      (field-ripple). Per-path `Path.freshnessAssertCount` (threaded by value
      like `heapDepth`) counts emitted pairwise inequalities; once it would
      exceed the cap the remaining `newRef != prior` inequalities are SKIPPED
      and a `heFreshnessCapExceeded` (sevHint, already in the enum) is emitted
      ONCE for that `new T` via the NEW `freshnessCapHints` threadvar (the G4
      `distinctBijectivityHints` drain idiom — reset at `runSymexImpl` entry,
      dedup'd into `RawResult.errors` on every verdict branch). SOUND: skipping
      a distinctness inequality lets Z3 allow aliasing beyond the cap (MORE
      models), which is conservative — NEVER a false UNSAT. The `newRef != nil`
      pin is uncapped (a single assertion, not pairwise). Tested with cap 3 + 5
      allocs on one path → sxSat + hint, no crash.
    - **Supporting wiring.** `refEq(a, b, op)` (NEW) lowers `svRef`/`svPtr`
      `==`/`!=` to a ground `Z3_mk_eq` over the two address consts (added to
      BOTH the probe-some and probe-miss comparison binop branches), so
      `if p == q` over two fresh allocs is a provably unreachable branch. The
      walker `of isNew:` arm forks per surviving path, `freshRef` +
      `assertFreshness`, and binds `svRef`/`svPtr` under `stmt.nRetName` (pointee
      from `nRefTy.refPointeeTy`/`ptrPointeeTy`). **Parser gap closed:** R1a
      wired the `mkNewT` IR ctor + emit round-trip but NEVER taught the parser to
      recognise `new T` from a real SUT — the let-section arm now detects a
      `new T` RHS (`isNewCall` — `nnkCommand`/`nnkCall` headed by `new`) and
      lowers it to `mkNewT(name, classifiedRefTy)` instead of `parseExpr`.
    - **Test** `tsymex_phase15_r2_new.nim` (4 tests: alias → sxUnsat; disjoint
      armA/armB both sxSat; over-cap sound) green c+cpp 4/4, confirmed NOT to
      hang. **No walker version bump** (stays `"9"`; Cluster R bumps at R12).
      Regression all green c, no HANG: r1_refsort, r1b_callheap, R1a_ir,
      rectify_refs, phase3_recursion, phase4_tuple, C6_smoke, F8_smoke (the
      `maxFreshnessAssertions` settings-ripple), S11_mutation. **Next: R3**
      (`p[]` read — `select(heap_T, p)`).
  - **R3 — SHIPPED.** Completes the `p[]` deref READ path and adds the
    **seq[ref T] element path** (the headline R3 deliverable).
    - **Read select confirmed per-path.** The R1 `of isDeref:` walker arm
      already threads `path.heaps[typeId]` (per-PATH, NOT a global or a
      `WalkerStatics` field) for the GROUND `select(heap, p)`; the result is a
      fully-typed SymVal (via `liftHeapValue`) for the dereffed T, and the read
      does NOT modify the heap (the surviving path carries the same/freshly-
      materialised array forward). R3 confirms this and builds the seq path on
      top of it.
    - **seq[ref T] element path.** `allocateSeqDataRaw(itRef/itPtr)` builds a
      FREE `Z3Array[Z3Int, Ref_T]` backing via raw FFI (`Z3_mk_array_sort` +
      `Z3_mk_const`) — the element value sort `Ref_T` is a RUNTIME uninterpreted
      sort the typed `mkArrayVar[Z3Int, V]` cannot express, so it mirrors
      `mkHeapArrayVar`'s raw discipline (two fwd-decls — `allocRefSort`/
      `refPointeeTypeId` — let the R1 definitions be reached before they appear).
      The `isIndex` seq arm gains an `itRef`/`itPtr` branch that raw-
      `Z3_mk_select`s the element at `idxZi.raw` and lifts it to an `svRef`/
      `svPtr`; a later `[]` (an `isDeref`) derefs THAT element through
      `path.heaps[T]`. So `xs[0][]` is: seq element select (→ svRef) → heap
      select (→ pointee value). Both selects are GROUND — NO universal-∀ over the
      uninterpreted `Ref_T` sort (the G4 MBQI hang lesson); confirmed NOT to
      hang.
    - **seq[ref T] WITNESS.** `extractSeqElements(itRef/itPtr)` records ONLY the
      seq LENGTH (no per-element leaf — the pointee values were observed only
      through the heap). The `emitTyAndReader` itSeq `itRef` reader renders a
      `seq[ref T]` of the model length, each element a `new(T)` DEFAULT cell (the
      pointee reader is intentionally NOT invoked — it would KeyError on the
      absent leaf). Sound + replayable (right length; pointees never individually
      rendered). The full per-element heap-snapshot witness (alias groups / nil
      rendering, ADR-0010 §Heap witness invariants) lands R11b/R12. New
      `readSeqLen` helper sizes the default-cell seq.
    - **`isDerefWrite` IRStmtKind (the `p[] = v` WRITE) — STUBBED no-op at R3.**
      `types.nim` adds `isDerefWrite(dwPtr/dwValue/dwElemTy/dwPtrFamily)` + ctor
      `mkDerefWrite` + the exhaustiveness ripple across `render`/`canonicalize`/
      `collectBan`/`collectSetLitMembers`/`collectTableLitKeys`/`scan`/`emitStmt`/
      `walk`. `dsl_parser` detects `p[] = v` (an `nnkAsgn` whose LHS is an
      `nnkDerefExpr`/`nnkHiddenDeref` over a ref/ptr operand — checked BEFORE the
      hidden-deref `unwrap`, which would otherwise strip the indirection) and
      lowers it to `mkDerefWrite`. The walker `of isDerefWrite:` arm is a NO-OP
      (returns `paths` unchanged) — the real `store(path.heaps[T], p, v)` lands
      R4.
    - **The free-heap reconciliation (the WRITE is R4).** RFC §R3's main test SUT
      does `p[] = 99` then reads `p[] == 99`. At R3 the write is a no-op, so the
      read picks 99 from the FREE heap array (R1) regardless of the (no-op)
      write — **sxSat via the free heap, NOT via real read-after-write** (that's
      R4). The per-path-isolation DoD "an unwritten branch doesn't see the
      update" genuinely needs the store and is **DEFERRED to R4**; R3 tests
      isolation via INDEPENDENT free heaps instead (two forked branches each
      deref `p` under a DIFFERENT value constraint — `p[]==11` on one, `p[]==22`
      on the other — each sxSat independently on its own per-path heap binding,
      neither pruning the other). No read-after-write semantics are faked.
    - **Test** `tsymex_phase15_r3_deref_read.nim` (4 tests: write-then-read
      free-heap sxSat; the seq[ref int] element `xs[0][]==7` sxSat — the real R3
      work; two independent-free-heap isolation sxSats) green c+cpp 4/4,
      confirmed NOT to hang. **No walker version bump** (stays `"9"`; Cluster R
      bumps at R12). Regression all green c, no HANG: r1_refsort, r1b_callheap,
      r2_new, R1a_ir, rectify_refs, phase5_seq (the seq machinery the seq[ref]
      path extends), F9b_seq_float, phase4_tuple, C6_smoke, F8_smoke. **Next: R4**
      (`p[] = v` write — `store(heap_T, p, v)` — promotes the R3 `isDerefWrite`
      no-op stub to a real heap store, enabling read-after-write + the
      write-based per-path isolation deferred here).
  - **R4 — SHIPPED.** `p[] = v` heap WRITE — the real GROUND store (ADR-0010 R4),
    promoting R3's `isDerefWrite` NO-OP stub. **This is where the heap model becomes
    real:** writes propagate and aliasing is observable.
    - **`of isDerefWrite:` store.** Per surviving path: resolve the ref/ptr SymVal
      `p` (its `Ref_T` address const via `svRef.refAst`/`svPtr.ptrAst`); lazily
      materialise `path.heaps[typeId]` on first touch (the SAME discipline as
      `isDeref`'s `mkHeapArrayVar` — so a write BEFORE any read still has an array
      to store into, and a later read of the same ref reads this stored array);
      lower the RHS `v` with a **pointee-typed prototype** (`allocateSym(stmt.dwElemTy)`
      → `lower(env, stmt.dwValue, some(proto))`) so an int literal coerces to the
      matching BV width/sort the heap array's value sort expects (the seq/table
      store idiom); extract its raw value-sorted ast via `rawAnyAstOf`; then
      `path.heaps[typeId] := wrap(Z3_mk_store(heap, refSym, v_raw))` — REPLACE the
      per-path heap binding with the stored array on the surviving (forked) path.
      GROUND store (`Z3_mk_store`) — NO universal-∀ over the uninterpreted `Ref_T`
      sort (the G4 MBQI hang lesson); confirmed NOT to hang.
    - **The sxUNSAT cases PROVE the write propagates (not the free heap).** Unlike
      R3 — where `p[]=99; p[]==99` was sxSat purely via the FREE heap (the no-op
      write irrelevant) — R4's store FIXES the value, so the *contradiction* cases
      flip to UNSAT and become the proof: (1) **real read-after-write** —
      `p[]=99; p[]==99` → sxSat AND `p[]=99; p[]==7` → **sxUnsat** (impossible under
      a free heap that could pick anything; the store pins it to 99); (2) **alias
      observability** — `let q=p; p[]=5; q[]==5` → sxSat (write through `p` seen
      through the aliased `q`: same refSym → same array index → same value, Z3's
      array theory does it automatically, NO fork) AND `q[]==6` → **sxUnsat**;
      (3) **per-path isolation-via-write** (the proof DEFERRED at R1b/R3, now REAL)
      — write on the c-true branch only: c-true read sees 5 (sxSat) and `p[]==6`
      there is **sxUnsat** (the store LANDED on that branch), while the c-false
      UNWRITTEN branch reads the free/pre-write heap (any value satisfiable —
      independent, because `heaps` is value-copied at fork so the store on c-true
      never reaches c-false). The R1b/R3 deferred proofs are thus now real.
    - **Test** `tsymex_phase15_r4_deref_write.nim` (8 tests — 5 sxSat read/alias/
      isolation + the 3 sxUnsat write-propagation proofs) green c+cpp 8/8, confirmed
      NOT to hang. **No walker version bump** (stays `"9"`; Cluster R bumps at R12).
      Regression all green c, no HANG: r1_refsort, r1b_callheap, r2_new,
      r3_deref_read, R1a_ir, rectify_refs, phase5_seq, phase4_tuple, C6_smoke,
      E3_try (inter-proc — heap writes now propagate across calls via R1b's
      threading), F8_smoke. **NOTE:** E5's deferred test 3 (ptr-write heap
      visibility through `finally`) is now potentially UNBLOCKABLE (the `store` it
      needed exists) — left for a later sweep, not pulled into R4. **Next: R5** (nil
      handling — `p == nil` observable; deref of possibly-nil forks a nil path
      emitting `sxRaised(NilAccessDefect)`).
  - **R5 — SHIPPED.** `nil` is now OBSERVABLE and the `p[]`-of-nil DEFECT is
    modelled. Two pieces — nil-equality and the deref nil-fork — plus the
    path-explosion short-circuit.
    - **`nil` literal → `iekNil` → `svRef`/`svPtr` carrying `nilConst`.** The
      parser's `nnkInfix` arm detects an `nnkNilLit` operand of a `==`/`!=`,
      classifies the OTHER (ref/ptr) operand to get its pointee, and lowers `nil`
      to a NEW `iekNil(nilPointee)` IR expr (NOT a generic literal — `nil` has no
      standalone type). The walker lowers `iekNil` to an `svRef`/`svPtr` whose
      `refAst` is the per-sort `nilConst` (`nil_<typeId>`, allocated/cached by
      `allocRefSort` — the R1 machinery), so the EXISTING `refEq` decides
      `p == nil` as a GROUND `Z3_mk_eq` over two `Ref_T` consts. A fresh `new`-ed
      ref's `p == nil` is sxUnsat (the freshness pin `newRef != nil` contradicts).
    - **IRExprKind ripple (iekNil).** `types.nim`: enum member + `nilPointee:
      IRType` variant field + `mkNil` ctor + `render` arm. `dsl_parser.emitExpr`
      (`mkNil`+`emitIRType`). `canonicalize(IRExpr)` (`Ex<Nil:…>`).
      `abstraction.nim` (`tryEvalInterval` none-group + `collectVarRefs` discard).
      `runtime.nim` `lower` (the svRef/svPtr build) + `probeProto` (none — not
      env-resident). All other IRExpr scans (`collectSetLitMembers`/
      `collectTableLitKeys`/`collectBan`) have `else: discard`.
    - **Deref nil-fork (`of isDeref:` READ + `of isDerefWrite:` WRITE).** A shared
      `nilDerefFork(p, refAst, elemTy, w)` (defined alongside `drainParseIntRaises`,
      the closest precedent) forks every deref of a SYMBOLIC ref into: (a) a NIL
      sub-path — `p == nil` asserted — the **NilAccessDefect**, GATED on the new
      `tNilAccess()`/`stkNilAccess` target (it `trySolve`s the nil path and records
      a `RawResult{sxSat, witness p == nil}`; the verdict the DoD checks is
      **sxSat**, conceptually a `sxRaised("NilAccessDefect")` — `NilAccessDefect`
      is registered in `exnTypeTable` as a `Defect` subtype so `isDefect`/
      `isSubtypeOf` classify it). The nil path is TERMINAL (never continues into
      the select/store). (b) a NON-NIL continuation — `p != nil` asserted —
      RETURNED so the R1 select / R4 store proceeds. Under any NON-`stkNilAccess`
      target the nil path terminates SILENTLY (only the non-nil deref is searched),
      so prior R tests' `tLabel`/`tNilAccess`-free searches see only the added
      (sound) `p != nil` constraint — they do NOT spuriously fork or surface a nil
      finding. The fork loops the deref body over `nilDerefFork`'s survivors.
    - **Nil-fork SHORT-CIRCUIT (Depth-LOW-D4 — the path-explosion guard).**
      BEFORE forking, `pcImpliesNonNil(ctx, p.pc, refAst, nilConst, typeId)` does a
      SHALLOW (single-level) AST pattern scan of `p.pc` (via `getAstKind`/
      `getAppDecl`/`declName`/`getAppArg`/`astEqual` — NO Z3 `check-sat`): it
      matches `not(eq(p, nil))` (an explicit `p != nil` — which is EXACTLY the term
      `assertFreshness` pins as `newRef != nil` for a `new`-ed ref) or
      `eq(p, ref_<typeId>_N)` (p aliases a fresh non-nil ref, recognised by the
      `ref_<tid>_` decl-name prefix). If found, the nil path is UNSAT BY
      CONSTRUCTION, so the ENTIRE fork is SKIPPED and `p` is returned UNCHANGED
      (no nil sub-path, no redundant `p != nil` assertion) — a SOUND optimization.
      **Consequence:** a freshly `new`-allocated ref dereffed NEVER forks a nil
      path (R5 test 2: `let p = new int; p[]…` under `tNilAccess()` → **sxUnsat**,
      no hang — this PROVES the short-circuit fires). Essential now that every
      deref would otherwise fork (nil/non-nil) — the prior deref-heavy R1–R4 tests
      confirmed NOT to explode.
    - **`stkNilAccess` target + exhaustiveness ripple.** New `SymexTargetKind.
      stkNilAccess` + `tNilAccess()` ctor (types.nim). Arms added across
      `describeTarget` ("nil-access"), `canonicalize(SymexTarget)` (`Tg<NA>`),
      `assertCoveredBy` (single-target `coveredExpr`/`failMsg`/`targetExpr` + a
      `NilAccessDefect` replay-except clause; multi-target `tNode`;
      `rebuildTargetNode`).
    - **Test** `tsymex_phase15_r5_nil.nim` (5 tests: deref non-nil → tLabel sxSat;
      deref nil → tNilAccess sxSat; SHORT-CIRCUIT fresh-`new` ref → tNilAccess
      sxUnsat; `p == nil` → sxSat; fresh-`new` `p == nil` → sxUnsat) green c+cpp
      5/5, confirmed NOT to hang. **No walker version bump** (stays `"9"`; Cluster
      R bumps at R12). Regression all green c, no HANG: r1_refsort, r2_new,
      r3_deref_read, r4_deref_write, R1a_ir, rectify_refs, E6_defect (the
      defect/sxRaised path), E3_try, phase4_tuple, C6_smoke, F8_smoke (walker
      version "9" confirmed). The deref-fork + the SymexTargetKind ripple were the
      risks — prior R tests (which deref) confirmed NOT to spuriously fork/explode
      (the short-circuit fires for new-allocated/constrained refs; the nil finding
      is target-gated). **Next: R6** (`ref object` field access — select+field-
      project read / store+field-modify write; inherited fields; variant guard).
  - **R6 — SHIPPED.** `ref object` field access (`p.field` READ + `p.field = v`
    WRITE) through a `ref`/`ptr` to an OBJECT.
    - **★ HEAP-OBJECT REPRESENTATION — FIELD-SPLIT (the key reconciliation).**
      The RFC §R6 phrasing `select(path.heaps[T], p).field` implies the heap
      array is valued by a RECORD — but a Z3 array's value sort must be a SINGLE
      Z3 sort, and an object is a Nim-side `svTuple` (MULTIPLE Z3 asts, NOT one
      Z3 sort — C0-ADR confirmed there is no Z3 tuple sort in this engine). So
      `Z3Array[Ref_T, Point]` is NOT directly buildable, and indeed R1's
      `liftHeapValue`/`heapValueSort` only ever supported PRIMITIVE pointees
      (`liftHeapValue` RAISES for a non-primitive — a bare `p[]` of an object was
      never modeled). **Chosen representation: FIELD-SPLIT heaps** — a SEPARATE
      heap array PER (object type, field): `heap_<objTid>__<field>:
      Z3Array[Ref_T, <fieldSort>]`, all keyed by the SAME `Ref_T` ADDRESS sort
      (`refPointeeTypeId` of the OBJECT — one ref → one address, observed across
      every field array). New `fieldHeapKey(objTy, field)` =
      `refPointeeTypeId(objTy) & "__" & field` (value sort = the field type). So
      `p.x` READ → `select(heap_<objTid>__x, p)`; `p.x = v` WRITE →
      `heap_<objTid>__x := store(heap_<objTid>__x, p, v)` — only that field's
      array changes; an ALIASED `q.x` (same `Ref_T` index) reads the same value
      via Z3 array theory (NO fork), a DIFFERENT field `q.y` is independent
      (different array). This REUSES R1's `mkHeapArrayVar`/`heapSelect` and R4's
      `Z3_mk_store` wholesale — only the heap KEY (field-qualified) and the value
      sort (the field's) differ. All GROUND (`select`/`store`), NO universal-∀
      over `Ref_T` (the G4 MBQI hang lesson); confirmed NOT to hang.
    - **IR (`types.nim`).** `isDeref` gains `dField`/`dObjTy`; `isDerefWrite`
      gains `dwField`/`dwObjTy` (empty/`nil` ⇒ a bare `p[]`, the R1/R4 path). New
      ctors `mkFieldDeref`/`mkFieldDerefWrite`. `render`/`canonicalize`/`emitStmt`
      arms extended (the `.field` suffix / `;fld=` content-address component /
      the round-trip via the new ctors).
    - **Walker (`runtime.nim`).** `of isDeref:` / `of isDerefWrite:` branch on
      `dField != ""`: the `Ref_T` SORT + the R5 nil-fork key on the OBJECT
      (`dObjTy`), the heap ARRAY on `fieldHeapKey`, the value sort on the field
      (`dElemTy`). The R5 nil-fork composes (a field access through a possibly-
      nil object ref forks correctly). The R1 `currentHeapDerefVals` witness hook
      is GATED to bare `p[]` (a field's scalar must not clobber the object-cell
      witness slot).
    - **Parser (`dsl_parser.nim`).** The typed AST is
      `nnkDotExpr(nnkHiddenDeref(p), field)` (READ) /
      `nnkAsgn(nnkDotExpr(nnkHiddenDeref(p), field), v)` (WRITE). When the
      dereffed operand classifies as a genuine `ref`/`ptr` whose pointee is an
      object (`itTuple`), lower to `mkFieldDeref`/`mkFieldDerefWrite`. This runs
      BEFORE the existing `classifyType(n[0])` tuple/variant routing (which would
      classify the hidden-deref's tuple value and LOSE the ref address) and
      before `unwrap` (which would strip the indirection).
    - **Inherited fields (Depth-H8) — DONE, tractable for FREE.** The field-split
      heap keys on the field NAME (UNIQUE across the flat inheritance layout —
      Nim forbids field shadowing) and the field TYPE comes from
      `classifyType(wholeDotExpr).ty` (the typed AST resolves base + own fields
      directly), so NO flat-offset arithmetic was needed (the RFC's
      "index into svTuple by the flat offset" is moot under field-split — there
      is no positional svTuple in the heap). A `ref Child` accessing inherited
      `p.bx` (from `Base`) and own `p.cy` both resolve.
    - **Variant-fielded ref (Feas-MED-4 / M17) — classified.** An INLINE
      `ref VNode` (variant object) field access: the parser routes it through the
      same field-deref IR (the field type is well-defined), and the WALKER
      detects `dObjTy.kind in {itVariant, itMultiVariant}` and raises the NET-NEW
      `SymexRefVariantUnsupportedError` → caught at the `runSymex` boundary →
      `heRefVariantUnsupported` (sevError, already in the enum) → sxUnknown
      (Invariant 3 — never a `Defect` on svTuple dispatch, never a silent UNSAT).
      A field-split heap has no flat positional layout to split a variant on. (A
      NAMED `type N = ref object` with variant fields still unwraps to a value
      variant — typebridge path (2), UNCHANGED — and is modelled as a plain
      in-memory variant; the negative DoD targets the inline ref-deref path.)
    - **Witness (`runtime.extractFromSymVal(svRef/svPtr)`).** A field-only-
      accessed `ref object` param records NO whole-object value under
      `currentHeapDerefVals`, but the `emitTyAndReader(itTuple)` reader reads a
      leaf PER field. The `svRef`/`svPtr` extract arm with an `itTuple` pointee
      now materialises a DEFAULT object SymVal (`allocateSym(pointee)`) and
      extracts its leaves so every field leaf exists (the reader never KeyErrors)
      — a sound replayable default cell (the per-field heap values were observed
      only through the heap; the full per-field heap-snapshot witness lands
      R11b/R12).
    - **Test** `tsymex_phase15_r6_refobj.nim` (5 tests: headline aliased field
      write `p.x=42; q.x==42` → sxSat with witness `p==q`; field read `p.x==7` →
      sxSat; non-alias independence via two distinct `new`-ed refs → sxSat;
      inherited base `p.bx` + own `p.cy` → sxSat; variant-ref →
      `heRefVariantUnsupported` sxUnknown) green c+cpp 5/5, confirmed NOT to hang.
      **No walker version bump** (stays `"9"`; Cluster R bumps at R12). Regression
      all green c, no HANG: r1_refsort, r2_new, r3_deref_read, r4_deref_write,
      r5_nil, R1a_ir, rectify_refs (the ref-field-access test — the reused
      svTuple/object machinery), phase4_tuple, phase11_walker (variant),
      C6_smoke, F8_smoke (walker version "9" confirmed). cpp parity on
      r4_deref_write, r5_nil, rectify_refs. **Next: R7** (ref equality + alias
      chain — `let q = p`; `q := r` breaks alias).
  - **R7 — SHIPPED.** Ref equality + alias chain (ADR-0010 R7). **CONFIRMATION
    cycle — NO code change** (the env binding already shares the `Ref_T` const
    for a ref-typed RHS, exactly as the RFC predicted).
    - **let-alias refAst SHARING — already correct.** `let q = p` (p a ref param)
      lowers (dsl_parser `nnkLetSection`) to `mkLet("q", itRef(T), mkVar("p"))` —
      the RHS is a bare `iekVar`, NOT a deref. The walker `of isLet:` arm does
      `newEnv["q"] = lower(env, mkVar("p"))`, and `lower(iekVar) = env["p"]`
      returns the param's `svRef` SymVal. `SymVal` is a Nim VALUE type, so the
      assignment COPIES the struct but SHARES the underlying `Z3AnyAst` (the
      `refAst`). So `q` and `p` are structurally the SAME svRef → the SAME
      `Ref_T` address const. **Consequences (all free):** `p == q` is a Z3
      TAUTOLOGY (`refEq` over two identical terms — no `check-sat` needed); a
      write through `q` (`q[] = v` → store at the shared refAst) is observed
      through `p` (same heap index, Z3 array theory, NO fork); an alias CHAIN
      `p == q == r` via two sequential lets needs NO extra axioms — transitivity
      is the IDENTITY of the same const (each let copies the same SymVal forward,
      so all three names hold one address).
    - **Reassignment BREAKS the alias — already correct (the var-rebind vs
      heap-write distinction).** `q = r` is an `isAssign` (a VARIABLE REBIND),
      lowered to `mkAssign("q", mkVar("r"))`; the walker `of isAssign:` arm does
      `newEnv["q"] = lower(env, mkVar("r")) = env["r"]` — `q` now holds r's
      refAst, NOT p's. This is DISTINCT from `q[] = v` (an `isDerefWrite` — a
      HEAP store at q's CURRENT address) and from `q[] = r[]` (a value copy via
      deref-read + deref-write). `q = r` rebinds the env var only; the heap is
      untouched. After the rebind a write `q[] = 9` lands on r's address and is
      NOT forced to be observed through p — p and r are DISTINCT params
      (independent `Ref_T` consts, free to differ; params are NOT
      fresh-allocated/`assertFreshness`-distinct, so they MAY alias, but are not
      FORCED to). So `p[] != 9` remains SATISFIABLE after `q = r; q[] = 9`. Had
      the alias NOT broken (q still the same const as p) the write through q
      would FORCE p[]==9 and `p[] != 9` would be UNSAT — the sxSat verdict is
      what PROVES the rebind broke the alias.
    - **Test** `tsymex_phase15_r7_alias_chain.nim` (9 tests) green c+cpp 9/9,
      confirmed NOT to hang. (1) transitive: RFC §R7 named SUT `let q=p; let r=q;
      r[]=5; p[]==5` → sxSat (write through r visible through p — all three share
      the refAst); read-back `r[]==5` → sxSat; contradiction `p[]==6` → sxUnsat
      (the chain pins p[] to 5 — PROVES the write reaches p, not a free heap).
      (2) reassignment: `var q=p; q=r; q[]=9; p[]!=9` → sxSat (alias broke — p
      not forced to 9) PROVED against the CONTROL `var q=p; q[]=9; p[]!=9` →
      sxUnsat (the alias was genuinely LIVE before `q=r`, so the break is real,
      not an artifact); read-back `var q=p; q=r; q[]=9; q[]==9` → sxSat (the
      rebound q reads its own write through r). (3) ref equality: `let q=p; p==q`
      → sxSat (tautology), `p!=q` → sxUnsat (same const), two distinct params
      `p!=r` → sxSat (may differ). **No walker version bump** (stays `"9"`;
      Cluster R bumps at R12). Regression all green c, no HANG: r1_refsort,
      r2_new, r4_deref_write, r5_nil, r6_refobj, R1a_ir, rectify_refs,
      **phase1_let** (the non-ref let/assign risk — UNAFFECTED, as expected for a
      no-code-change cycle), phase4_tuple, C6_smoke, F8_smoke. **Next: R8**
      (`ptr T` family + pointer arithmetic — same heap model; `inc`/`dec` →
      `hePtrArith` halt; `ptrFamily` hint on ptr witnesses).
  - **R8 — SHIPPED.** `ptr T` family + pointer-arithmetic classification (ADR-0010
    R8). **svPtr heap routing — ALREADY WORKED (no extension).** Both the
    `isDeref` (R1) and `isDerefWrite` (R4) arms already `case refSV.kind` with
    `of svPtr: refSV.ptrAst` and route through `path.heaps[typeId]` (same
    `Ref_T` sort, `Z3_mk_select`/`Z3_mk_store`) IDENTICALLY to `svRef` — `ptr int`
    deref `p[] == 7` is decidable exactly like `ref int`; the `ptrFamily` flag is
    the only semantic difference. R1/R4 wired BOTH SVKinds from the start, so R8
    added NO heap code.
    - **`hePtrFamily` hint (sevHint, NON-halting).** New `ptrFamilyHints`
      threadvar (the R2 `freshnessCapHints` idiom). Emitted at the `isDeref`/
      `isDerefWrite` arms whenever `refSV.kind == svPtr` (an unmanaged ptr,
      `ptrFamily = true` since R1a) — `SymexErrorInfo{kind: hePtrFamily,
      severity: sevHint, msg: "witness involves unmanaged ptr"}`. Drained
      (dedup'd by msg) into `RawResult.errors` on every verdict branch (rides
      `exnWarnings` like the G4/R2 hints), reset at `runSymexImpl` entry. A
      parallel managed-`ref T` SUT emits NOTHING — the hint is the
      ptr/ref distinguisher (Invariant 7 — a hint never changes the verdict).
    - **Pointer arithmetic `inc(p)`/`dec(p)` → `hePtrArith` (sevError, HALTING).**
      `dsl_parser.nim` `nnkCall/nnkCommand` statement arm gains a NAME-based
      guard (`n[0].strVal in {"inc","dec"}`) GUARDED on the unwrapped receiver
      (strip `nnkHiddenAddr`/`nnkHiddenDeref`/`nnkHiddenStdConv`) classifying as
      `itPtr`. Match → `ctx.parseErrors.add SymexErrorInfo{kind: hePtrArith,
      severity: sevError, msg: "pointer arithmetic (inc/dec) not modeled"}`
      (forces sxUnknown — Invariant 3; never silent) + `mkUnsupported`. The
      arithmetic is NOT modeled — the resulting address is unmodelable in the
      `Ref_T`-keyed heap.
    - **inc/dec on an INT is UNAFFECTED.** A SIBLING guard (same name match,
      receiver classifies `itInt`) lowers `inc(i)`/`dec(i)` to the equivalent
      env rebind `i = i ± step` (`mkAssign(nm, mkBinop(bAdd/bSub, mkVar(nm),
      step))`; `step` = `parseExpr(n[2])` or `mkIntLit(1)`), so the int case
      symexes natively (the `{.magic.}` body is never walked) and "behaves as
      before". The ptr guard is checked FIRST and keys strictly on `itPtr`, so an
      int operand never reaches the arith-halt arm.
    - **Note on the test SUT.** Stock Nim 2.2.10 has NO `inc(p: ptr T)` /
      `dec(p: ptr T)` — pointer arithmetic is cast-based (`system/ptrarith`
      `+!`/`-!` templates), and `inc(p)` on a `ptr int` is a SEMCHECK ERROR (the
      `symexFind` macro is `typed`, so the SUT must type-check first). To
      exercise the name+ptr-operand guard with a compiling SUT the test provides
      a local `inc`/`dec` ptr overload; the parser guard fires on name + ptr
      operand BEFORE that overload is ever registered/walked. The guard is thus
      a defensive classification (any future ptr-arith spelling routed through an
      `inc`/`dec`-named call on a ptr is honestly halted).
    - **Witness.** `symex.emitTyAndReader` still renders a `ptr T` param as a
      `nil` placeholder; the `{.warning.}` text was re-pointed from "lands R8" to
      "R8 flags the family via hePtrFamily; full pointer-family witness rendering
      lands R11b/R12" (R8's scope is the hint + arith classification, NOT the ptr
      witness VALUE format).
    - **Test** `tsymex_phase15_r8_ptr.nim` 4/4 c+cpp: (1) `ptr int` deref
      `p[]==7` → sxSat + `hePtrFamily` (sevHint); (1b) parallel `ref int`
      `p[]==7` → sxSat, NO `hePtrFamily`; (2) `inc(p)` on a ptr → sxUnknown +
      `errors[0].kind == hePtrArith` (sevError); (3) `inc(i)`/`dec(i)` on an int
      → sxSat, NO `hePtrArith` (the inc/dec-on-int guard risk — CONFIRMED
      unaffected). **No walker version bump** (stays `"9"`; Cluster R bumps at
      R12). Regression all green c, no HANG: r1_refsort, r4_deref_write, r5_nil,
      r6_refobj, r7_alias_chain, R1a_ir, rectify_refs, phase1_arith, phase1_let,
      phase4_tuple, C6_smoke, F8_smoke. **Next: R8b**.

**Toolchain (cross-cutting, established at Z1):** all dev/test runs use
`localhost/proptest-dev:latest` (built from `ghcr.io/coreyleavitt/nim:latest` +
`z3-devel`). nim-z3 v2.0.0 requires **Nim >= 2.2.10**. Run a single test with
`scripts/dt.sh <c|cpp> tests/<file>.nim`.
