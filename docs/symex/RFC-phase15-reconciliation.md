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

**Toolchain (cross-cutting, established at Z1):** all dev/test runs use
`localhost/proptest-dev:latest` (built from `ghcr.io/coreyleavitt/nim:latest` +
`z3-devel`). nim-z3 v2.0.0 requires **Nim >= 2.2.10**. Run a single test with
`scripts/dt.sh <c|cpp> tests/<file>.nim`.
