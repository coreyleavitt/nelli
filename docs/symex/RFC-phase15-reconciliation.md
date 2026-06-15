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
  - F4 (ordering compare), F5 (conversions), F6 (math ops), F7
    (bit-exact extraction), F8 (regression + walker bump), F9a/b/c — pending.
- *(S, H, E, G, C, R: pending)*

**Toolchain (cross-cutting, established at Z1):** all dev/test runs use
`localhost/proptest-dev:latest` (built from `ghcr.io/coreyleavitt/nim:latest` +
`z3-devel`). nim-z3 v2.0.0 requires **Nim >= 2.2.10**. Run a single test with
`scripts/dt.sh <c|cpp> tests/<file>.nim`.
