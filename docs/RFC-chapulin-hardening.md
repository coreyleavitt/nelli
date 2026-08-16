# RFC — nelli consumer-hardening (from chapulin v1/v2 harness)

> Empirically-sourced hardening RFC. Every item was surfaced building chapulin's
> symex + fuzz + soak verification harnesses against nelli, and **re-verified
> at HEAD `99fa2db`** before entering this doc — healed findings are dropped, live
> ones carry their reproduced symptom + locus. Source:
> `/mnt/c/Users/corey/projects/chapulin/docs/nelli-findings.md`.

## Status

| | |
|---|---|
| **Stage** | 2 (architecture review) — **rounds 1 & 2 applied** |
| **Scope** | mega-RFC across all subsystems (Corey-decided 2026-07-12), organized into per-subsystem clusters, each independently sliceable |
| **Verification** | all ~30 findings re-checked at `99fa2db` by 4 agents; results in the session's `verify_results.md` and reflected below |
| **Architecture** | rounds 1+2 applied (two 4-agent teams, all grounded in the code). Round 2 added SND-1b (closure axiom bypass), CR-2c (witness-reader `error()`), split P2, rescoped TOT-1, hardened the version-pin + cache-key + backend-divergence DoDs. See §Round-2 outcomes |
| **Open forks** | none — SW pin idiom resolved (synthesis; Corey 2026-07-12). Ready for Stage 3 (`/tdd`) |
| **Handoff** | `docs/RFC-chapulin-hardening.handoff.md` |

## §0 — Thesis (the marquee, cross-cutting)

chapulin's own top ticket: *"make the walker's failure mode total."* Verification
sharpened this into a **two-sided invariant**:

> **Totality + soundness of the failure mode.** Any construct nelli doesn't
> model must degrade to a **sound** classified `sxUnknown` — never (a) a native
> crash (uncaught `doAssert`/`KeyError`/`ValueError`), never (b) a compile-time
> macro `error()` that aborts expansion, and never (c) a **silent wrong answer**
> (a `false sxSat`/`sxRaised` with empty `errors`). Then progressively widen the
> modeled fragment.

**Three macro-`error()` site classes (round-2).** Clause (b) is not one locus but
**three** structurally-distinct macro-expansion abort surfaces, each needing its
own degrade mechanism:
1. **SUT-body parse** — `parseExpr`/`parseStmt` catch-alls (`dsl_parser.nim:1847`)
   → CR-2a.
2. **Parameter-type classify** — `classifyType` catch-all (`dsl_typebridge.nim:452`)
   → CR-2b.
3. **Witness-reader codegen** — `emitTyAndReader` (`symex.nim:697/708/716`), a
   *separate post-solve macro* → **CR-2c** (round-2 addition — invisible to
   CR-2a/b; different macro, different call site).

**Statement-dispatch totality is already compiler-enforced (round-2 precision).**
The walker's top-level `case stmt.kind` (`runtime.nim:5017-6056`) has **no `else`
branch** — Nim exhaustiveness already guarantees every `IRStmtKind` is handled.
The genuine, *un-closed* totality surfaces this RFC must backstop are exactly the
three open-ended ones where exhaustiveness is structurally unavailable: the parser
catch-all over `NimNodeKind` (CR-2a), the type-classifier text-match (CR-2b/CR-2c),
and internal `doAssert`/`raise` landmines inside otherwise-modeled arms (CR-1c).
TOT-1 is a backstop for *those three*, not a substitute for exhaustiveness where it
already holds — see TOT-1.

The (c) clause is load-bearing: verification found that today's "degrade" path
(`mkUnsupported` statements) is itself **unsound** — so the expression-level
crash/degrade work *must not ship before* the (c) soundness fix, or we'd trade
visible crashes for silent wrong answers (strictly worse under Invariant 3).

**Hard dependency:** `SND-1`/`SND-1b ≺ CR-2a` (soundness before the expression-
position degrade that synthesises dummy values). SND-1 also precedes M4/M5/P1/P2a
for the same reason (each introduces a degrade-to-dummy site). `CR-1a`/`CR-1b` are
*real bug fixes at the true locus* — they do **not** depend on SND-1 (they fix, they
do not degrade). See §Round-1/2 outcomes for why this ordering changed.

**Crash-doctrine boundary (round-1, do not violate).** nelli deliberately does
**not** catch walker-level `ValueError`/`AssertionDefect` at `runSymex`
(runtime.nim:6786-6794: *"those are real bugs in the symex layer and must
surface"*). The ~63 `doAssert` + ~90 `raise newException` internal-invariant
guards in `runtime.nim` are meant to crash **loudly** so CI catches genuine walker
bugs. This RFC does **not** blanket-convert them. A walker-internal-invariant
failure and a SUT-unmodeled-construct gap must never be indistinguishable to a
consumer — see CR-1c.

## Round-1 outcomes (what the first review changed)

The round-1 4-agent review (depth/breadth/design/feasibility) grounded every claim
in the actual code. The material changes from the round-1 draft:

1. **SND-1 mechanism already exists — reuse `Path.uncertain`, no new precedence
   logic, no ADR-0012 amendment.** `Path.uncertain` (runtime.nim:376-378) is the
   per-path taint the DoD wanted; it is already consulted at both `w.found`
   producer sites (`isTargetLabel` 5905-5919, `routeRaise` 6081-6085). The bug is
   only that `isUnsupported` (6041-6043) sets the walk-global `w.sawUnknown` but
   never taints the path. Fix is **S**, not L. The draft's "taint the precedence"
   option was *unimplementable as written* (`w.found`/`RawResult` carry no path
   identity). See SND-1.
2. **A/B split of `mkUnsupported` sites.** Class-A sites (which also
   `ctx.parseErrors.add(sevError…)`) are *already immune* — `capForcedUnknown`
   (runtime.nim:7281-7285) forces `sxUnknown` whenever any `sevError` parseError
   exists, skipping the `w.found` scan entirely. Only Class-B sites (bare
   `mkUnsupported`, no parseError — the `&=`/`/=` repro) are vulnerable. The
   walker-level SND-1 fix covers both uniformly.
3. **CR-1 is not a sweep.** Split into CR-1a (#3 fixed at its true abstraction/
   promotion locus), CR-1b (#4 fixed at tail-return lowering), and CR-1c (one
   narrow last-resort catch with a *distinct internal-fault kind*). We do **not**
   grep-and-convert the internal `doAssert` guards.
4. **CR-2 splits by `error()` class.** CR-2a expression-position (reuses the
   existing preamble-`mkUnsupported`+dummy idiom, depends on SND-1); CR-2b
   parameter-type-position (reuses the already-sound `capForcedUnknown`/`tUninterp`
   whole-run degrade, no dummy synthesis, independent of SND-1).
5. **Version-pin discipline was absent** — now a cross-cutting section. Two consts:
   `symexWalkerVersion` (canonicalize.nim:96) *and* `renderAsChoicesVersion`
   (canonicalize.nim:52).
6. **New slices:** TOT-1 (totality harness — operationalises §0) and INT-1
   (chapulin workaround-removal exit gate).
7. **Corrections:** M1 dep on CR-1 dropped (it is class-C witness-reader codegen in
   `symex.nim`, independent); M3 de-risked to **S** (nim-z3 `lastIndexOf` exists);
   SND-2 site list corrected to 12 switches; Clusters 6-7 marked a decoupled track.

## Round-2 outcomes (what the second review changed)

Round 2 hunted what was still weak after round 1, again grounded in the code. It
confirmed SND-1's chokepoint mechanism, ADR-0012 D2 precedence, the call-cache
uncertain-gate, and the 12-switch count all hold as written — and surfaced:

1. **SND-1b — closure ground-axiom path bypasses `Path.uncertain` (CRIT, NEW).**
   `applyClosureGround` (runtime.nim:6244-6531) descends a closure body via a
   *second, unregistered* raw `Path(…)` construction (line 6381, `uncertain: false`
   hardcoded) and folds returns into the **global** `currentClosureCallAxioms`
   threadvar (drained into *every* later `trySolve`, 3765-3773) with **no**
   uncertain-gate — unlike the call-cache, which refuses to cache an uncertain
   summary (5850). SND-1's fix never reaches this path. New slice SND-1b.
2. **CR-2c — third macro-`error()` class.** `emitTyAndReader` (`symex.nim:697/708/
   716`) hard-aborts on `seq[Object]`/`Table[string,string]`/`HashSet[string]`
   witnesses — a compile abort like CR-2a but in a different macro, uncovered by
   CR-2a/b. New slice CR-2c; §0 widened to three site classes.
3. **TOT-1 rescoped from generative to table-driven.** All symex entry points
   require `fn: typed` (a literal compile-time proc); `fuzz.nim`/`strategy.nim`
   generate runtime *values*, not Nim AST — "generate arbitrary unmodeled DSL
   fragments, sited in the fuzz subsystem" is unbuildable at size M. Rescoped to a
   fixed, hand-authored, table-driven `§0`-invariant corpus over the known repros.
4. **Cache-key collision hardening (SND-2).** The blanket "render `isAssume`
   identically to `isAssert`" would collide their `symexCacheKey`s
   (`canonicalize.nim:684-685`) — a silent-wrong-answer regression. `isAssume` needs
   a **distinct** render tag (`Am:` vs `At:`) + a regression test. Also:
   `collectAssertRanges` (`abstraction.nim:324-335`) has an `else: discard` that
   silently drops assume range facts — fixed in SND-2's DoD.
5. **CR-2b crash-risk closed.** The `tUninterp("__unsupported_…")` option hits an
   *uncaught* `ValueError` in `allocateSym` (only `__ownership:` is prefix-guarded,
   runtime.nim:1366-1381) — relocating a macro-time abort to a walk-time crash
   (§0(a) violation). CR-2b DoD now requires a new `allocateSym` prefix guard *or*
   the `capForcedUnknown` path with an explicit `ctx`-threading decision.
6. **CR-1c open item resolved + backend-divergence trap.** chapulin's actual config
   has **no `-d:danger`/`--panics:on`** (checked `nim.cfg`/`chapulin.nimble`), so
   the catch approach is viable. Depth added: `--panics:on` affects only `Defect`;
   CR-1a/b's `ValueError`/`KeyError` are `CatchableError` and unaffected. CR-1c must
   use `try/except`, **never** bare `try/finally` — commit `b7258f7` is a live
   precedent where a `try/finally` around walk dispatch silently swallowed re-raises
   **C-backend-only** (`sxUnsat` for `sxUnknown`). Its regression test must *diff
   both backends'* verdicts on the injected fault.
7. **Exception-carrier depth (design).** 18 near-identical `object of CatchableError`
   carriers already exist (runtime.nim:47-192) with 18 parallel `except` arms;
   CR-1c/CR-2b should introduce **one** generic `SymexClassifiedDegradeError{kind}`
   rather than mint #19/#20, and name the existing 18 as incremental debt the new
   carrier makes trivial to retire (not required in-RFC).
8. **Sizing/process:** P2 split into P2a (value-object) + P2b (`ref object`, size L;
   variant construction explicitly excluded); Q1 marked a timeboxed research spike
   (may have no viable sound-and-fast encoding); INT-1 made a *recurring* per-SW-slice
   check with a rollback clause; a `SYMEX_PLAN.md` ADR-landing + status-refresh
   obligation added; the `(t)` notation clarified with an explicit strong-form RED
   instruction.

## Slice inventory

Status legend: **LIVE** (reproduced at HEAD) · **NEW** (found during verification)
· **DROP** (healed — listed in §Healed, not sliced). Size S/M/L. Ver-bump: **SW** =
`symexWalkerVersion`, **RC** = `renderAsChoicesVersion`, **—** = neither (see
§Version-pin discipline). `Hard` deps gate build order; `Soft(t)` deps only shift a
slice's DoD (see the transient-dep note below the table).

| ID | Slice | Cluster | Sev | Size | Hard deps | Soft(t) | Ver |
|----|-------|---------|-----|------|-----------|---------|-----|
| SND-1 | Unmodeled statement taints `Path.uncertain` (no false `sxSat`) | Soundness | **CRIT** | S | — | — | SW |
| SND-1b | Closure body drops uncertain axioms → whole-run degrade | Soundness | **CRIT** | S–M | — | — | SW |
| SND-2 | `symexAssume` real filter semantics (distinct `isAssume` IR) | Soundness | **CRIT** | M | — | — | SW |
| SND-3 | Loop-guard lowering-raise silently lost on C backend → false `sxUnsat` | Soundness | **HIGH** | M | SND-1 | — | SW |
| SND-4 | String-index reads (`s[i]`) have zero `IndexError` modeling → false `sxUnsat` | Soundness | **HIGH** | M | — | — | SW |
| CR-1a | #3 bitwise-on-`svInt` fixed at abstraction/promotion locus | Crash-totality | high | S | — | — | SW |
| CR-1b | #4 tail-return-of-local fixed at lowering (env binding) | Crash-totality | high | S | — | — | SW |
| CR-1c | Narrow last-resort walker catch → distinct internal-fault `sxUnknown` | Crash-totality | high | M | — | — | SW |
| CR-2a | Expression-position `error()` → preamble-`mkUnsupported`+dummy | Crash-totality | high | M | SND-1 | — | SW |
| CR-2b | Parameter-type `error()` → whole-run forced-`sxUnknown` | Crash-totality | high | M–L | — | — | SW |
| CR-2c | Witness-reader codegen `error()` → classified degrade (`symex.nim`) | Crash-totality | high | M | — | — | RC |
| M1 | `seq[byte]`/fixed-width-int witness readers (`symex.nim`) | Model gaps | high | S–M | — | — | RC |
| M2 | `parseBiggestInt` model (unblocks chapulin B4) | Model gaps | high | S | — | CR-2a | SW |
| M3 | `rfind` model (nim-z3 `lastIndexOf`) | Model gaps | med | S | — | — | SW |
| M4 | in-place string `.add` / `&=` model | Model gaps | med | S–M | SND-1 | — | SW |
| M5 | `min`/`max` (if-expression-bodied inlining) | Model gaps | med | M | SND-1 | CR-2a | SW |
| M6 | `probeProto` sentinel completeness (defensive) | Model gaps | low | XS | — | — | — |
| P1 | general `nnkTupleConstr` return | Parser | med | S–M | SND-1 | CR-2a | SW+RC |
| P2a | value-object `nnkObjConstr` (non-ref) in expression path | Parser | med | M | SND-1 | CR-2a | SW+RC |
| P2b | `ref object` construction (expression-position allocation) | Parser | med | L | SND-1 | CR-2a | SW+RC |
| P3 | `seq` slicing `data[a..b]` (+ `openArray` type path) | Parser | med | M | — | CR-2b | SW |
| P4 | `..^` backward-index slicing | Parser | low | S | — | — | SW |
| Q1 | dependent bounded loops (defect-target search) — **LANDED** (ADR-0025) | Solver | med | L | — | — | SW |
| Q2 | loop + `string`-param under defect-target search | Solver | high | L | SND-2 (re-scope) | — | SW |
| TOT-1 | Table-driven §0-invariant regression corpus | Totality | high | M | SND-1, SND-1b, CR-1a/b/c, CR-2a/b/c | — | — |
| INT-1 | chapulin pin-bump + workaround removal (recurring exit gate) | Integration | — | S | per-SW-slice | — | — |
| F1 | non-pruned coverage-corpus channel (`dbReusePhase`) | Fuzz† | high | L | — | — | — |
| F2 | up-front coverage-replay of preloaded seeds (`minimizeCorpus`) | Fuzz† | med | M | — | — | — |
| F3 | export `minimalCovering*` | Fuzz† | low | S | — | — | — |
| F4 | `FuzzSettings.stopOnFirstCrash` | Fuzz† | low | S | — | — | — |
| F5 | document `db.nim applySave` ordering | Fuzz† | low | S | — | — | — |
| F6 | per-primary-entry metadata slot | Fuzz† | med | M | — | — | — |
| F7 | choice-IR seed protocol: document + surface dropped-seed count | Fuzz† | med | M | — | — | — |
| F8 | corpus section-size introspection helper | Fuzz† | low | S | — | — | — |
| C1 | coverage slot→`file:line:col` side-table | Coverage† | med | L | — | — | — |
| C2 | (doc-only) explain 8192-bitmap convergence | Coverage† | low | S | C1 | — | — |
| SH1 | shrinker `seq[byte]` `Int128` compile bug | Shrinker | — | ? | **deferred — needs consumer repro** | — | — |

**† Decoupled track.** Clusters 6–7 (F*, C*) touch the fuzz/corpus/coverage
subsystems — zero code or dependency overlap with the symex clusters. Per the
mega-RFC decision they stay in this one doc, but they ship on an **independent
schedule** and do **not** gate on the Cluster 1–5 soundness review (and vice
versa). Their tests live in the `tfuzz*`/`tdb*`/`tcoverage*` family and do not need
`dt-bounded.sh` hang-guarding. (Note: TOT-1 is **not** in this track — round-2
verified it cannot reuse `fuzz.nim` infrastructure; see TOT-1.)

**Transient deps `Soft(t)`.** A soft dep means: the feature slice is independently
buildable, but *if CR-2a/CR-2b lands first* the construct degrades to `sxUnknown`
instead of a macro-`error()`, so the feature slice's DoD shifts from *"no compile
error"* to *"emits correct `sxSat`/model."* It is **not** a build-order dependency.
**`/tdd` RED-state instruction (round-2):** regardless of landing order, write the
**strong-form** assertion (exact `sxSat` + witness) as the RED test. If CR-2a/b
hasn't landed, the RED step is *"this test file fails to compile"* — that is the
expected, precedented RED shape for an `error()`-catchall slice, **not** a signal to
weaken the test to `check verdict == sxUnknown` (which CR-2a would make spuriously
green). If a feature slice lands before CR-2a/b, it must still remove the
corresponding `error()` site itself.

---

## Cluster 1 — Soundness (worst class: silent wrong answers)

### SND-1 — unmodeled statement silently mis-mutates → false `sxSat`  ·  CRIT  ·  NEW
**Found during verification** (not in the original doc, but implicated by #10's `&=`).
The `isUnsupported` **statement** arm (`runtime.nim:6041-6043`) sets the
walk-global `w.sawUnknown = true` and then **continues the path with stale state**
(`paths`). ADR-0012 D2's precedence (`runtime.nim:7305-7361`: first `sxSat` wins;
`sawUnknown` consulted only when no `sxSat`/`sxRaised` exists *anywhere*) then
reports a target reached **after** the dropped mutation as `sxSat` with a
**silently wrong witness and empty `errors`**.

- **Reproduced (general, not string-specific):** `t &= "x"; if t == "ax": target`
  → `sxSat` witness `s="ax"` (real Nim: `"ax" & "x" = "axx" ≠ "ax"`, correct
  witness is `"a"`). And `acc /= 2.0; if acc == 5.0: target` → `sxSat` witness
  `x=5.0` (real needs `10.0`).

**The mechanism already exists (round-1).** `Path` is a `ref object` with
`uncertain: bool` (runtime.nim:376-378, *"true once any call along this path has
bailed… an uncertain path can't be reported as a sound witness — it degrades to
`sxUnknown`"*). It is threaded forward through every `forkPath` (never reset) and
**already consulted at both** verdict-recording chokepoints:
- `isTargetLabel` (runtime.nim:5905-5919): `if p.uncertain: w.sawUnknown = true`
  *instead of* solving/recording a witness.
- `routeRaise` (runtime.nim:6081-6085): same pattern before the E6 defect-solve.

So a path that dropped a mutation must be marked `uncertain`, exactly like a path
whose call bailed on `maxCallDepth`.

- **DoD:** the `isUnsupported` arm marks every path in its batch `uncertain` and
  continues (`paths`), so any `sxSat`/`sxRaised` found *downstream on that same
  path* is demoted to `sxUnknown` at the existing chokepoints. **Prefer
  taint-and-continue over halt-the-path** (both are Invariant-3-safe, but tainting
  preserves exploration of code reachable after the drop — a completeness win at no
  soundness cost).
- **Exact precedent to follow (round-2):** the `maxCallDepth`-exceeded bail arm in
  `isCall` (`runtime.nim:5696-5711`) is structurally identical to what SND-1 needs —
  set `w.sawUnknown`, then `out2.add forkPath(p, p.pc & pcInit, newEnv, true)` per
  path, return the batch. `uncertain` is **never** mutated in place anywhere in the
  codebase (all 30+ sites thread it through `forkPath`'s 4th positional arg). Point
  the implementer at 5696-5711 directly — this is copy-the-existing-idiom, not a
  design choice. Halt-the-path (`@[]`, mirroring `isUnsafeCast` at 6044-6056) is the
  acceptable fallback, but is idiomatically for *unbound-name* hazards (raw pointer
  never in `env`) that don't apply here — `env` still holds the stale-but-defined
  value, so taint-and-continue is correct.
- **Class A/B note:** Class-A `mkUnsupported` sites (those that also
  `ctx.parseErrors.add(sevError…)`, e.g. `dsl_parser.nim:1584-1591`,
  `2402-2409`) are **already immune** — `capForcedUnknown` (runtime.nim:7281-7285)
  forces `sxUnknown` on any program with a `sevError` parseError, skipping the
  `w.found` scan. The vulnerable set is Class-B (bare `mkUnsupported`, no
  parseError; e.g. the augmented-assign catch-all `dsl_parser.nim:2994-3002`). The
  walker-arm fix above covers **both** classes uniformly.
  *(Incidental doc fix: `capForcedUnknown`'s name implies cap-specificity, but it
  is a blanket "any `sevError` parseError anywhere → `sxUnknown`" switch — clarify
  its doc comment.)*
- **Regression:** a target reached *before* / independent of the drop still yields
  a valid `sxSat`. Add a test asserting `Path.uncertain` survives `isIf`/`isWhile`/
  `isCall` path merges.
- **ADR:** **no ADR-0012 D2 amendment** — the precedence reduction (7305-7361) is
  untouched; SND-1 only adds a new *producer* of the existing `uncertain` taint.

### SND-1b — closure body silently drops uncertain axioms → global false `sxSat`  ·  CRIT  ·  NEW (round-2)
SND-1's `Path.uncertain` taint does **not** reach the closure/lambda ground-axiom
path, which is a *separate, parallel* verdict-influencing mechanism.
`applyClosureGround`/`lowerClosureCall` (`runtime.nim:6244-6531`) descend a closure
body once via a **raw, non-`forkPath` `Path(…)` construction** (line 6381,
`uncertain: false` hardcoded — a second raw `Path(` site the fork-registry comment
at 4409-4454 wrongly claims is unique). The body's returned sub-paths are folded
into **ground** Z3 axioms via `assertArm` (6403-6424), pushed into the **global**
`currentClosureCallAxioms` threadvar (6410) and drained into **every** subsequent
`trySolve` for the rest of the run (3765-3773). `assertArm` never reads
`cp.uncertain`. There is **no** analogue of the call-cache's uncertain-gate
(`not frame.returnedPaths[0].uncertain`, 5850) anywhere on this path.

- **Consequence:** a closure whose body bails on `maxCallDepth`, or (once SND-1
  ships) contains an `isUnsupported` statement, has its (possibly wrong) return
  value asserted as an **unconditional, permanent** fact for every future solve —
  SND-1's own repro shape placed *inside a closure body* still yields false `sxSat`.
- **DoD:** in `assertArm`'s callers (6412-6424), **skip** emitting the axiom when
  `cp.uncertain`, and mark this closure application unsound for the run by reusing
  the **existing** `closureForcedUnknown` whole-run degrade (`runtime.nim:7300-7304`,
  currently fed by `ceClosureUnknownCallee`/`ceInlineBudgetExceeded`): push a new
  error kind (e.g. `ceClosureBodyUncertain`) into `closureCallErrorsLive` whenever an
  uncertain return path is dropped from axiomatization. Coarse (whole-run, not
  per-occurrence) but sound — matching the precedent CR-2b already accepts. There is
  no live `Path` at the `lower()` call site to taint per-occurrence (the same
  no-path-identity reason round-1 rejected precedence-level tainting for SND-1).
- **Regression:** SND-1's `&=`/`/=` repro wrapped in a closure body must return
  `sxUnknown`, not false `sxSat`. TOT-1's corpus must include a closure-body-wrapped
  unmodeled-construct fixture.
- **Hygiene:** fix the stale fork-site registry comment (4409-4454) to acknowledge
  the raw `Path(` at 6381.

### SND-2 — `symexAssume` == `symexAssert`, masking `sxUnsat` with false `sxRaised`  ·  CRIT  ·  LIVE
`dsl_parser.nim:2716-2717` parses `symexAssume(cond)` to `mkAssert(cond)` —
byte-identical to `symexAssert` — while `symex.nim:934-941` documents filter/prune
("conjoin into the path condition") semantics. `isAssert` (`runtime.nim:5891-5904`)
unconditionally forks an `AssertionDefect` via `forkDefect`→`routeRaise`, and E6
(`runtime.nim:6154-6167`) surfaces any reachable `Defect` regardless of target.
- **Reproduced:** a genuinely-unreachable target (`s[0]=='a' and s[0]=='b'`)
  proves `sxUnsat` cleanly; prepending `symexAssume(s.len <= 5)` (violatable) flips
  it to **`sxRaised(AssertionDefect)`** — a false defect masking a correct proof.
- **DoD:** a distinct `isAssume` IR kind. **Precise behaviour:** the `isAssert`
  walker arm (runtime.nim:5891-5904) does four things — (1) `lowerBoolInExpr` +
  `drainScalarRaiseForks`, (2) `drainConvFloatToIntRaises`, (3) `forkDefect(p, not
  cond, "AssertionDefect", …)`, (4) `forkPath(p, p.pc & [cond], …)`. `isAssume`
  shares **(1),(2),(4) verbatim** and omits **only (3)**. Steps (1)/(2) are *not*
  assert-specific — they surface raises arising from *evaluating the condition
  itself*, which `symexAssume` must still do (`symexAssume(1 div x == 0)` with
  symbolic `x` able to be `0` must still surface the `DivByZeroDefect`).
- **Exhaustive-site inventory (12 switches):** `abstraction.nim` ×2
  (`collectAssertRanges` 324-335, `collectBan` 344-396), `canonicalize.nim` ×1
  (629-720), `types.nim` ×2 (variant decl 529, `render` 1786-1852), `dsl_parser.nim`
  ×1 (`emitStmt` 269-366), `runtime.nim` ×3 (3173-3220, 3270-3321, walker dispatch
  5020-6056), `scan.nim` ×3 (56-80, 83-88, 124-142). **Most sites should treat
  `isAssume` like `isAssert`** via an `of isAssert, isAssume:` OR-arm (both add a
  `cond` conjunct to `p.pc`) — only the single walker arm diverges. Two sites need
  **specific, non-uniform** handling (round-2):
  - **`canonicalize.nim:684-685` (cache key) — MUST diverge (silent-wrong-answer
    risk).** This renders `isAssert` as `"St<At:" & … & ">"`, feeding `symexCacheKey`
    (864). If `isAssume` shares this tag, `symexAssert(c)` and `symexAssume(c)` on
    the same `c` collapse to the **same cache key** despite different verdict
    semantics → false-`sxSat`/-`sxRaised` from cache reuse. Give `isAssume` a
    **distinct** tag (`"St<Am:…>"`, mirroring the existing `VR:`/`VRS:` and `Nw:`/
    `Dr:` distinct-tag discipline at 678-701). **Test:** `canonicalize(mkAssume(c))
    != canonicalize(mkAssert(c))` for identical `c`.
  - **`abstraction.nim:324-335` (`collectAssertRanges`) — has `else: discard`
    (round-2).** Unlike its exhaustive sibling `collectBan`, this switch silently
    drops `isAssume` to `discard`, losing assume-derived range facts (a completeness
    regression the two `scan.nim` tests below don't catch). Add `of isAssert,
    isAssume:` (or strip the `else:` so future kinds are compiler-forced). **Test:**
    `symexAssume(x > 0)` narrows the abstraction the same way `symexAssert(x > 0)`.
- **`scan.nim` trap (must-test):** `scan.nim:83-88` sets `found[0] = true` for
  `isAssert` (auto-discovers a `tAssertionViolation` target) and has an `else:
  discard`. Here the safe default *is* correct — an assume-only SUT must **not**
  auto-discover an assert-violation search. **Regression tests (both required):**
  (a) a SUT using *only* `symexAssume` must NOT auto-discover a `tAssertionViolation`
  target; (b) `symexAssume(1 div x == 0)` with symbolic `x` must still surface the
  div-by-zero defect.
- **ADR:** `isAssume` filter/prune semantics distinct from `isAssert`; a **distinct
  IR kind** (not a boolean flag) so Nim's `case`-exhaustiveness forces the 10
  uniform sites to decide at compile time (the 2 non-uniform sites above are DoD'd
  explicitly because the compiler's "safe default" is either wrong (cache key) or
  a silent completeness loss (`collectAssertRanges`)).

### SND-3 — loop-guard lowering-raise silently lost on C backend → false `sxUnsat`  ·  HIGH  ·  LANDED
A relational char/string-ordering comparison (or non-int64 `HashSet`/`set` membership
test) evaluated inside a **loop guard** produces a **backend-divergent verdict**: `c`
reports a false `sxUnsat` ("unreachable"), `cpp` correctly reports `sxUnknown`. A
backend-divergent verdict is itself a soundness violation — at least one backend is
wrong.

- **Reproduced:** `while i < s.len and s[i] >= '0' and s[i] <= '9': inc i` then
  `symexTarget(...)` after the loop → `c` = `sxUnsat`, `cpp` = `sxUnknown`.
- **Root cause:** the CR-17(a) defensive guard (`runtime.nim`, `lower`'s `iekBinop`
  arm) `raise`s `SymexUnsupportedStringOpError` for an ordering comparison on a
  string-indexed char (`s[i] </<=/>/>=`). Outside a loop that raise propagates
  cleanly to the `runSymex` boundary catch → sound `sxUnknown` on both backends
  (this was already correct). **Inside a loop guard**, the raise unwinds through the
  loop's live `seq[Path]` and is **silently lost** on the C backend's goto-exception
  model (the b7258f7/CR-1c divergence class CR-1c's own doc comment already names) —
  the walk continues with a mis-lowered guard, producing the false `sxUnsat`.
- **DoD (the crux — read before reusing this pattern elsewhere):** the fix is NOT
  `w.sawUnknown = true` at the raise site. Under ADR-0012 D2 precedence (first
  `sxSat` wins; `sawUnknown` consulted only when no `sxSat`/`sxRaised` exists
  anywhere), a fresh unconstrained symbol on the tainted path could itself satisfy
  the target and fabricate a **false `sxSat`** — trading a false `sxUnsat` for a
  WORSE false `sxSat`. The fix instead taints SND-1's existing **per-path**
  `Path.uncertain` (demoted at the `isTargetLabel`/`routeRaise` chokepoints), via two
  new threadvar sinks (`loweringDegradeErrors`, `loweringDidDegrade`) consumed
  exclusively by `drainPendingLowerEffects` — the single choke-point every
  `lower()`/`lowerBool()` call site in `walk` already drains through. The raise
  becomes: append a classified error, set the degrade signal, return a fresh
  unconstrained bool (`allocateSym(tBool(), ...)`); `drainPendingLowerEffects` forks
  the path `uncertain = true` (fork-before-mutate, never aliasing a sibling path) and
  sets `w.sawUnknown` via `currentWalkCtxPtr`.
- **Systemic conversion (audit of every lowering-time `raise (ref Symex*Error)`
  site):** the mechanism is generic — any expression-lowering degrade-raise reachable
  inside a loop is the same latent hole. Converted: the CR-17(a) char-ordering guard
  (above); `cmpString`'s whole-`string`-ordering `else` arm (same `lowerCmp` call
  chain, same in-loop reachability); `lower`'s `iekContains` `svSet` arm (non-int64
  `HashSet`/`set` membership, reachable evaluating `x in mySet` in a loop). Left
  un-converted: `allocateSym`'s `itTable`/`itSet`/`itUninterp` arms — these raise
  ONCE per SUT parameter at run-**setup** time, before `walk`/any loop is ever
  entered, so the pre-existing whole-run degrade via the `runSymex`-boundary catch is
  already correct and the loop-unwind hazard does not apply.
- **Regression:** `tests/tsymex_snd3_loopdegrade.nim` — six behaviors, each asserting
  `c == cpp`: the tracer; a SUT whose ONLY route to target is through the degraded
  compare inside a loop never fabricates `sxSat` (the "worse-than-before" trap); an
  independent clean sibling path still yields real `sxSat` (per-path, not blunt,
  taint); the identical compare OUTSIDE a loop is unchanged (already sound pre-fix);
  the classified `seUnsupportedStringOp` kind rides the result (Invariant 3); the
  non-raising char-**equality** loop-guard path is untouched (still real `sxSat`).
- **ADR:** ADR-0023 (`SYMEX_PLAN.md`) — "lowering-time degrades taint IN-BAND, never
  `raise` from a site reachable inside a loop." Bumps `symexWalkerVersion` 57→58
  (verdict-surface change); `renderAsChoicesVersion` stays "7" (no new witness shape).

### SND-4 — string-index reads (`s[i]`) have zero `IndexError` modeling → false `sxUnsat`  ·  HIGH  ·  LANDED
String character index reads (`s[i]`, IR kind `iekStrAt`) have **zero** `IndexError`/
`IndexDefect` modeling, unlike seq/array/Table indexing (which already fork a defect
unconditionally). Consequence: a `tIndexError()` search over `s[i]` returns `sxUnsat`
("no OOB reachable") **even when an OOB is reachable** — a false "no defect" (a
soundness under-approximation on defect finding, the worst class for this cluster).

- **Reproduced:** `proc(s: string) = (let i = s.find(":"); let c = s[i+1])` with
  `tIndexError()` → `sxUnsat` on both backends; a bare `s[999]`-shaped read control
  also `sxUnsat`.
- **Root cause:** `iekStrAt`'s lowering (`runtime_strings.nim`) computes
  `toCode(at(recv.str, idxZi))` with **no bounds check**. Per Z3's `at`/`toCode` spec,
  an out-of-range `idxZi` makes `at` the empty string and `toCode` return `-1` (→ BV8
  `0xFF`), so the engine never crashes — but it also never raises, forks, or taints.
  The OOB read silently fabricates a byte value (`0xFF`) instead of the `IndexDefect`
  real Nim would raise.
- **DoD (the crux — mirror the EXISTING parseInt/div-by-zero pattern, do not
  reinvent):** the fix does NOT fork a defect from inside `lower()` (that would be the
  SND-3 anti-pattern — a raise/fork deep in lowering is lost through loops on the C
  backend). Instead, `iekStrAt` deposits a defect CONDITION —
  `oob = idx < 0 or idx >= len(s)` — into a new threadvar/`WalkCtx`-dual-store sink
  (`strIndexOobConds` / `syncStrIndexOobCond`), mirroring
  `parseIntRaiseConds`/`divByZeroConds`/`overflowConds` exactly. A new
  `drainStrIndexRaises`, folded into `drainScalarRaiseForks` as a 4th stage (after
  parseInt / divByZero / overflow), forks the OOB sub-path as a routed `IndexDefect`
  raise at the statement boundary and asserts the negation onto the survivor's
  `defectSurvivorPc` (ADR-0012) — the same "digits continuation" shape
  `drainParseIntRaises` uses. Unlike `drainDivByZeroRaises`/`drainOverflowRaises`, this
  drain is **unconditional** (no `arithChecks` opt-out gate) — string-index bounds
  checking mirrors the seq/array `isIndex` arm's unconditional `forkDefect`, which has
  no analogous gate either.
- **Regression:** `tests/tsymex_snd4_strindex_oob.nim` — seven behaviors, each
  asserting `c == cpp`: (1) the tracer, a concrete OOB index on an unconstrained
  string, → `sxRaised{IndexDefect}` (was `sxUnsat`); (2) the scan-then-OOB Q1-spike
  repro (`find` then `s[i+1]`) → `sxRaised`; (3) a bounds-safe read under an
  `s.len > 5` guard → `sxUnsat` (load-bearing precision — the fork does not
  over-report); (4a) a reachability target gated on both the length guard and the
  indexed char's value still resolves a real `sxSat` with a satisfying witness
  (proves the new bounds fact doesn't corrupt value semantics on the survivor); (4b) a
  companion char-value contradiction still resolves a real `sxUnsat`; (5) a
  negative-index-only SUT isolates the `idx < 0` disjunct and also forks
  `IndexDefect`.
- **Migration:** `tests/tsymex_phase15_S3_strindex.nim`'s `oobIndex` test
  (`s == "ab" and s[5] == '\0'` targeting `tLabel("hit")`) previously asserted only
  `status in {sxSat, sxUnsat}` — its own comment documented the verdict as genuinely
  underspecified (depending on Z3's choice for the fabricated `0xFF`). Post-SND-4, the
  condition is a SINGLE `and`-combined boolean expression, so `s[5]`'s OOB predicate is
  deposited BEFORE `s == "ab"` is asserted into the path condition — the OOB raise fork
  is therefore reachable via ANY short string (not just `"ab"`), so a REAL uncaught
  `IndexDefect` is reachable on this SUT. Per the pre-existing D1a raise-routing
  precedence (an uncaught raise outranks `sxUnsat` when no `sxSat` exists anywhere in
  the walk), the verdict is now **`sxRaised{IndexDefect}`**, deterministically — "hit"
  itself remains unreachable via the non-raise survivor (whose `defectSurvivorPc`
  carries `len(s) > 5`, contradicting `s == "ab"`'s `len == 2`), but the
  independently-reachable raise dominates the report. This is a genuine soundness
  correction, not a regression: real Nim `s[5]` on a 2-byte string DOES raise
  `IndexDefect`, so reporting that the SUT can raise is strictly more informative than
  the old underspecified "maybe sat"; the test was tightened accordingly.
- **ADR:** ADR-0024 (`SYMEX_PLAN.md`) — "string index reads model IndexError via the
  lowering-sink→drain-fork pattern (parity with seq/array indexing)." Bumps
  `symexWalkerVersion` 58→59 (verdict-surface change); `renderAsChoicesVersion` stays
  "7" (IndexError is a raise, not a new rendered witness shape).

---

## Cluster 2 — Crash-totality (Invariant-3: never crash, always classify)

### CR-1a — #3 bitwise-on-`svInt` fixed at the abstraction/promotion locus  ·  high  ·  LIVE
`runtime.nim:2951-2957` raises `ValueError: bitwise op on promoted Z3Int` — and the
raise's own comment says *"abstraction layer should have declined promotion under
bit-twiddling."* This is a **walker bug**, not an unmodeled construct: the fix is
at the abstraction/promotion layer (coerce the `svInt` operand via `toZ3Int` / ban
the BV-promotion under a bit-twiddling op), per the locked memory
`symex-abstraction-bv-ban-toz3int`. Repro: `s.find(x) and 1`, `len and 1` (where
the operand is an `svInt` from `.len`/`find`/`indexOf`/`parseInt`).
- **DoD:** both repros return a **sound `sxSat`/`sxUnsat`** (the bitwise op is now
  correctly modeled), not a native exit and **not** a soft-fail `sxUnknown` (that
  would be a permanent, needless capability regression). Regression: no
  currently-`svBV64`-param bitwise test flips.
- **`--panics:on` note (round-2):** `ValueError` is `CatchableError` — CR-1a needs
  **zero** extra work under `--panics:on`; only `Defect`-class raises are made
  uncatchable by that flag (see CR-1c).

### CR-1b — #4 tail-return-of-local fixed at lowering  ·  high  ·  LIVE
`runtime.nim:2629` (`of iekVar: env[e.vname]`) does a raw table index with no
`.hasKey` guard, for a construct the walker fully supports elsewhere (reading a
bound local). The KeyError is a **missing lowering step** — an implicit
tail-expression return referencing a local `let` doesn't flow that `let` into
`env`. Repro: `let hi = data[o] mod 256; hi + 1`.
- **DoD:** the repro returns a **sound `sxSat`** (the local resolves correctly),
  fixed at the lowering site that binds the tail expression's environment — not by
  soft-failing the `iekVar` read. (`KeyError` is `CatchableError` — unaffected by
  `--panics:on`.)

### CR-1c — narrow last-resort walker catch → distinct internal-fault `sxUnknown`  ·  high  ·  LIVE
The genuine safety net for the §0 invariant: a **single** narrow catch around the
walk's per-statement dispatch that converts a genuinely-**unanticipated** native
exception into a classified degrade — tagged with a **distinct internal-fault kind**
(`weInternalWalkerFault`/`sxUnknown`) that is **never** conflated with the ordinary
construct-gap `se*`/`fe*` kinds. This makes totality hold *by construction* (the §0
sweep is an audit, not the mechanism) while preserving the crash-doctrine: the
distinct kind lets CI/telemetry track "how often we hit the safety net" as a live
walker-bug backlog rather than a silently-closed invariant.
- **Do NOT** blanket-convert the ~63 `doAssert` / ~90 `raise` internal-invariant
  guards — those are meant to surface walker bugs loudly (§0 crash-doctrine).
- **Use `try/except`, NEVER bare `try/finally` (round-2, hard rule).** Commit
  `b7258f7` is a live precedent: a `try/finally` (no `except`) around walk dispatch
  hit Nim's C-backend goto-based exception model and **silently swallowed re-raises**,
  producing `sxUnsat` instead of `sxUnknown` — a silent wrong answer, **C-backend
  only, invisible on C++**. CR-1c's regression test must **diff the two backends'**
  verdicts on the injected fault, not merely assert "both green."
- **Reuse one generic carrier, don't mint an exception type (round-2, design).**
  runtime.nim:47-192 already declares **18** near-identical `object of
  CatchableError` carriers with 18 parallel `except` arms at the `runSymex`
  boundary. Introduce a single `SymexClassifiedDegradeError* = object of
  CatchableError` with a `kind*: SymexErrorKind` field + **one** `except` arm; CR-1c's
  fault path and CR-2b's degrade both use it. The existing 18 carriers are
  pre-existing debt this makes trivial to retire incrementally (each `raise (ref
  SymexXError)(msg:…)` → `raise (ref SymexClassifiedDegradeError)(kind: seXxx,
  msg:…)`) — **not required in-RFC**, but the RFC names it so the count stops climbing.
- **DoD:** an injected/synthetic unanticipated walker fault classifies as
  `weInternalWalkerFault`+`sxUnknown` (never a process exit, never conflated with a
  construct gap), *on both backends*. Regression: no existing `doAssert`-guarded
  walker-bug test is silenced.
- **`--panics:on`/`-d:danger` (round-2, RESOLVED for the current target, with a
  standing caveat):** chapulin's actual config has **neither** flag (checked
  `nim.cfg`/`tests/nim.cfg`/`chapulin.nimble`) → the catch approach is viable today.
  The open item closes. **But** the two flags differ and the RFC must state the
  residual limits plainly:
  - `--panics:on` makes every `Defect` raise (from *any* source — a stray
    `IndexDefect`/`RangeDefect`/`NilAccessDefect` in the walker's hundreds of
    unaudited indexing expressions, not just the 63 named `doAssert`s) **uncatchable**.
    `doAssert` is the *only* explicit `Defect`-class exposure in `runtime.nim` (every
    `raise` targets `ValueError`/a `CatchableError` custom type), so converting the
    reachable-during-walk `doAssert`s to `raise (ref SymexInternalFault…)` (catchable)
    is *necessary*; it is **not provably sufficient** against stray native `Defect`s
    — a full audit is a larger job than CR-1c's **M** sizing assumes.
  - `-d:danger` implies `--checks:off` → out-of-bounds indexing is silent UB with
    **nothing raised to catch** (strictly worse §0(c)). This is a build-config issue
    outside CR-1c's mechanism.
  - **Recommendation:** nelli's build docs must require the *walker's own
    compilation unit* keep `--checks:on` and not inherit a blanket `-d:danger`/
    `--panics:on`, even when the SUT or an outer harness is compiled with them. If a
    future chapulin (or other consumer) target adds these flags for the walker unit,
    CR-1c must be re-sized to include the `doAssert`→`raise` conversion + a
    stray-`Defect` audit.

### CR-2a — expression-position `error()` → preamble-`mkUnsupported`+dummy  ·  high  ·  LIVE
`parseExpr`'s catch-all (`dsl_parser.nim:1847`) `error()`s at **macro-expansion**
on an unsupported expression *kind*, aborting compilation (strictly worse than
`sxUnknown` — the SUT can't be analysed at all). Convert it to the **existing**
in-repo idiom (`dsl_parser.nim:1567-1591`, A7-S3 `runeLen(symbolic)`): register a
classified `sevError` parseError, `preamble.add mkUnsupported(reason)`, and return
a **type-correct dummy** (`classifyType(n).ty` is resolvable from the typed AST
regardless of `n.kind`). This is the catch-all safety net for the whole
expression-position macro-error class (M2/M5/P1/P2a shapes).
- **Depends on SND-1** (mechanically exact): the dummy value is only sound because
  `of isUnsupported` taints the path so the dummy can never produce a witness.
  Landing CR-2a before SND-1 would *multiply* the SND-1 surface by every new degrade
  site. **Because CR-2a registers a `sevError` parseError, it is Class-A —
  `capForcedUnknown` also backstops it** even before the SND-1 walker fix, but SND-1
  remains the correct sequencing (belt-and-suspenders + covers Class-B).
- **DoD:** a SUT using any currently-`error()`-ing expression kind returns
  `sxUnknown` with a classified kind, not a compile failure.

### CR-2b — parameter-type `error()` → whole-run forced-`sxUnknown`  ·  high  ·  LIVE
The scalar-type catch-all (`dsl_typebridge.nim:452`) `error()`s on an unsupported
**parameter type** — which fires *before* any proc body is walkable, so there is no
statement to demote and no sound "dummy value" (downstream witness-typing needs a
real `IRType`). This is a **different mechanism** from CR-2a. `classifyType*(ty:
NimNode): ClassifiedType` (`dsl_typebridge.nim:48`) takes **no** `ctx`/`preamble`
param, so there is nothing to append `mkUnsupported` to and no path to taint at
classify time — the CR-2a/CR-2b split is genuinely irreducible, not cosmetic.
- **Two viable mechanisms — pick one explicitly (round-2):**
  1. **`capForcedUnknown` path:** register a `sevError` and force `sxUnknown` for the
     whole run. Self-sufficient *today*, but needs a plumbing decision the RFC must
     make: thread a `ctx` sink into `classifyType`, **or** use a threadvar sink to
     record the `sevError` (the closure-type precedent at `dsl_typebridge.nim:421-428`
     shows the shape). State which in the slice.
  2. **`tUninterp` path:** return `tUninterp("__unsupported:" & s)` mirroring the
     `WeakRef`/`Atomic` → `tUninterp("__ownership:…")` precedent (404-410). **Crash
     trap (round-2):** `allocateSym(itUninterp)` (`runtime.nim:1366-1381`) special-
     cases exactly one prefix (`"__ownership:"`); **every other** `itUninterp` name —
     including a bare `"__unsupported_…"` — falls through to `raise
     newException(ValueError, …)`, which §0's crash-doctrine does **not** catch. So
     this option **requires** adding a new `"__unsupported:"` prefix branch to
     `allocateSym` (paralleling `__ownership:`) with its own typed
     `CatchableError`/degrade — otherwise it relocates the abort from macro-time
     (safe) to a walk-time native crash (§0(a) violation) at the very site it fixes.
- **Independent of SND-1** (the forced-`sxUnknown` path never scans `w.found`).
- **DoD:** a SUT with an unmodeled parameter type returns `sxUnknown` (whole-run),
  not a compile failure and not a walk-time crash. `IRType` may need an
  `itUnsupported`/`tUninterp` sentinel if not already sufficient.

### CR-2c — witness-reader codegen `error()` → classified degrade  ·  high  ·  NEW (round-2)
`emitTyAndReader` (`symex.nim`) — the **post-solve witness-reader codegen** macro,
a *third* macro-`error()` surface distinct from CR-2a/CR-2b — hard-aborts
compilation on unmodeled witness types:
`symex.nim:697` (`seq[...]` non-scalar), `708` (`Table[string,int]`-only), `716`
(`HashSet[int]`-only). Even after M1 widens the scalar reader set, a SUT signature
containing `seq[SomeObject]`/`Table[string,string]`/`HashSet[string]` still aborts.
- **DoD:** these three `error()` sites gain a `mkUnsupported`-style fallback
  consistent with CR-2a/CR-2b's idiom (a SUT with such a signature returns
  `sxUnknown`, not a compile failure). Because this fires on the *witness* shape for
  a literal `fn: typed` signature, its regression test enumerates unmodeled
  **signature shapes** (distinct from TOT-1's body-shape corpus). Bumps **RC** if the
  reader-emission contract changes; otherwise none.
- **Note:** M1 (below) closes the *scalar* sub-cases at 697; CR-2c is the catch-all
  degrade for the residual non-scalar/collection sites — the two are complementary,
  not overlapping.

---

## Cluster 3 — Model / stdlib gaps (clean degrade today; widen coverage)

- **M1 — `seq[byte]`/fixed-width-int witness readers** · LIVE. **Class-C** locus:
  post-solve witness-reader codegen in `symex.nim:696-698` (`emitTyAndReader`;
  `itSeq` reader handles only `int64`/`f32`/`f64`/`ref`) — a *separate macro* from
  the SUT-body walk, so **independent of CR-1 and CR-2a/b** (the class-C `error()`
  catch-all is CR-2c). Add reader cases for `byte`/`uint8..uint64`/`int8..int32`.
  Removes chapulin's `atByte` mask workaround *and* narrows the #3 surface. Bumps
  **`renderAsChoicesVersion`** (new witness shape). Size S–M.
- **M2 — `parseBiggestInt`** · LIVE (macro-error; only `parseInt` matched at
  `dsl_parser.nim:1504-1506`). Near-clone → same `iekStrToInt` IR (64-bit on this
  platform). **DoD must confirm failure-mode parity:** real Nim `parseBiggestInt`
  raises `ValueError` on malformed input exactly like `parseInt`; the `iekStrToInt`
  raise-path must model that identically (not just the happy path). **Directly
  unblocks chapulin v2 slice B4.** Size S.
- **M3 — `rfind`** · LIVE (clean `sxUnknown` degrade; `dsl_parser.nim:1727`
  catch-all). **De-risked:** nim-z3 already exposes `lastIndexOf*[E](a, sub):
  Z3Int` (`src/z3/sequence.nim:199`), a native Sequence-theory primitive mirroring
  `indexOf` — so M3 is a near-clone of the already-safe `iekStrFind` arm
  (`runtime_strings.nim:167-178`) calling `lastIndexOf`, **not** a bounded-scan
  encoding and **not** in the Q1/Q2 hang class. Size **S**.
- **M4 — string `.add` / `&=`** · LIVE. `.add` degrades cleanly; `&=` is the
  SND-1 Class-B case (silent no-op → false `sxSat`). Model both as concat
  (`iekStrConcat`). **Implementation note (round-2):** this is **not** a one-line
  set-literal extension. The augmented-assign handler (`dsl_parser.nim:2962-3000`)
  routes uniformly through `mkBinop(binopForInfix(…))`, but `binopForInfix`
  (`dsl_parser.nim:692-712`) has **no `"&"` case** and would hit its own `error()`.
  String concat is a structurally different IR family (`mkStrOp(iekStrConcat, …)`,
  1059). M4 needs a **type-classify branch** (string LHS → `mkStrOp`, else → existing
  `mkBinop`), not a set edit. **Depends on SND-1.** Size S–M.
- **M5 — `min`/`max`** · LIVE (macro-error; `nnkIfExpr` handled in `parseStmt` but
  not `parseExpr`, `dsl_parser.nim:1847`). Add an `nnkIfExpr` case to `parseExpr`
  (synthetic let+read) — also fixes any if-expression-bodied proc inlining.
  Depends on SND-1 (introduces a degrade-to-dummy path via the synthetic let);
  CR-2a `Soft(t)` backstops it transiently. Size M.
- **M6 — `probeProto` sentinel completeness** · LIVE-but-DEAD. The catch-all at
  `runtime.nim:1763-1767` omits `iekStrToLower/Upper/RadixFmt/RuneToStr` from its
  modeled set (returns `none`), but it's **inert today** (proto unused by string
  arms; `bEq` fallback recovers). Defensive-only; no verdict change → **no ver
  bump**. Size XS.
  *(Finding #7's original symptom — `toLowerAscii` unmodeled — is **HEALED** by
  A9; see §Healed.)*

## Cluster 4 — Parser expression coverage

- **P1 — general `nnkTupleConstr` return** · LIVE (macro-error at 1847; only the
  `yield (e1,e2)` special-case at 1999-2023 exists). Add a general N-ary case
  building an `itTuple` SymVal. Expression-position → CR-2a `Soft(t)` backstop; the
  synthetic construction is a degrade-to-dummy site → depends on SND-1. Bumps
  SW+RC (new tuple witness shape). Size S–M.
- **P2a — value-object `nnkObjConstr` (non-ref)** · LIVE (macro-error; only handled
  inside `newException(...)` at 2914 + codegen). Plain value-object construction
  (`itTuple`-shaped, no heap) as a first-class expression — the closest analog to
  P1's tuple work. Depends on SND-1; CR-2a `Soft(t)` backstop. Bumps SW+RC. Size M.
- **P2b — `ref object` construction (expression-position allocation)** · LIVE.
  Genuinely **new capability**: `isNewCall` (`dsl_parser.nim:805-821`) documents that
  `new T` allocation is handled **only at let-statement level** ("no expression-
  context model for allocation") — so `ref object` construction as an expression
  requires synthesizing a preamble `isNew` + N field-writes, not a near-clone.
  **Variant construction is explicitly EXCLUDED** (round-2) — the field-split heap
  deliberately declines variant *reads* today (`heRefVariantUnsupported`,
  `dsl_parser.nim:1299-1305`); adding variant *writes* needs its own ADR that also
  revisits that read gap. Depends on SND-1; CR-2a `Soft(t)`. **Likely needs its own
  ADR** (object construction as expressions vs the field-split heap model). Bumps
  SW+RC. Size L.
- **P3 — `seq` slicing `data[a..b]`** · LIVE, root cause **upstream**: Nim types
  the slice as `openArray[int]`, rejected by the scalar classifier
  (`dsl_typebridge.nim:452` — the **CR-2b** locus) before `itSeq`'s bracket case
  (1241-1247, which also lacks a slice branch, unlike `itString`). Needs both an
  `openArray`/slice-result type path *and* a seq-slice IR. CR-2b `Soft(t)` backstop.
  Size M.
- **P4 — `..^` backward-index slicing** · LIVE (incidental; `result[1..^1]` →
  parser "unsupported infix operator ..") . Size S.

## Cluster 5 — Solver capability (fail-soft; scoping matters)

Both slices are **hang-class** work: widening the model here (bounded-scan or
unwind-sensitive encodings under Sequence theory × loop-unwind) is the exact
mixed-theory divergence class that motivated `dt-bounded.sh` (the "F5 incident":
`int2bv(bv2int(x))` spun a core 24+ min; the codebase guards it at four sites —
`canonicalize.nim:208`, `runtime_floats.nim:46-68`, `runtime_strings.nim:383-385`,
`runtime.nim:1795`). `maxLoopUnwind` defaults to 5 (`types.nim:1547`). Today both
degrade cleanly to `sxUnknown` (no hang) — the risk is introduced by the fix.
- **DoD clause (both):** every candidate encoding is validated via
  `dt-bounded.sh` under an explicit tight timeout **before** it is a candidate; a
  `137` (HUNG) exit is a **rejected encoding**, not a slow test to retry. A fix that
  cannot beat the timeout must degrade to `sxUnknown` rather than ship a hang.

- **Q1 — dependent bounded loops** · **LANDED** (walker v60, ADR-0025). The
  round-2 spike found a viable sound-and-fast encoding after all, scoped narrowly:
  the canonical bounded forward scan-to-literal-delimiter idiom
  (`while i < bound and s[i] != lit: inc i`, body EXACTLY `inc i`/`i = i + 1`) is
  RECOGNIZED at parse time (`tryRecognizeScanIdiom`, `dsl_parser.nim`) and lifted to
  a closed-form `indexOf(s, lit, i)` — no unrolling, no quantifier, no mixed-theory
  conversion, so no `dt-bounded.sh` hang risk exists structurally (unlike the F5
  incident class this cluster's DoD guards against). Dependent/chained scans (a
  later scan's start derived from an earlier scan's result) compose for free under
  the same rewrite — this is finding #6, Q1's headline capability. Bundled: `iekStrFind`
  gained an optional 3rd `start` operand (`s.find(sub, start)` → Z3 3-arg `indexOf`),
  the closed form's foundation, which also fixed a latent unsoundness (a
  caller-written 3-arg `find` previously parsed but silently dropped `start`).
  **Scope LOCKED, not generalized**: `==`-guards (skip-while), char-class/predicate
  scans (`s[i] in {'0'..'9'}`, `isDigit(s[i])`), backward scans, non-`inc` bodies, and
  non-char delimiters all remain OUT of scope and still degrade to `sxUnknown` via
  the unchanged k-unroll path exactly as before — a false-positive recognition would
  be unsound, strictly worse than an honest degrade. Char-class/predicate
  generalization is explicit FOLLOW-UP work, not part of Q1 (no known
  Sequence-theory primitive gives an equivalent closed form for an arbitrary
  boolean predicate the way `indexOf` does for literal equality). See ADR-0025
  (`docs/SYMEX_PLAN.md`) for the full writeup and `tests/tsymex_q1_scanlift.nim`
  for regression coverage.
- **Q2 — loop + `string` param** · LIVE, **narrower than the original claim**: the
  doc's "ANY loop + string param → `sxUnknown`" is empirically false for `tLabel`
  (all shapes `sxSat`); real specifically for **defect-search targets over an
  `s.len`-bounded loop**. **Re-scope after SND-2:** proper `symexAssume` narrowing
  was one of the levers tried against this class; a correct `isAssume` may reduce the
  surface / change the size estimate. Size L (re-estimate post-SND-2).

## Cluster 6 — Fuzz / corpus / DB  (decoupled track; all CONFIRMED at HEAD)

- **F1** non-pruned "coverage corpus" channel, separate from the regression-replay
  primary that `dbReusePhase` prunes (`engine/phases.nim:65-84`). L.
- **F2** up-front coverage-replay pass over preloaded seeds so an external corpus
  minimizes losslessly (`fuzz.nim:381-403` seeds get zero-`Coverage`). M.
- **F3** `export minimalCovering*` (`fuzz.nim:337`). S.
- **F4** `FuzzSettings.stopOnFirstCrash` (`fuzz.nim:122-186`). S.
- **F5** document `applySave` prepend/reverse-insertion order (`db.nim:163-169`). S.
- **F6** per-primary-entry metadata slot (`db.nim:47-52,109-111`). M.
- **F7** document the 2N+1 choice-IR draw-order protocol + surface `captureIR`'s
  dropped-seed count in `FuzzReport` (`strategy.nim:451-480`, `fuzz.nim:262-277`). M.
- **F8** corpus section-size introspection helper (`db.nim:83-101`). S.

## Cluster 7 — Coverage  (decoupled track)

- **C1** emit a slot→`file:line:col` side-table at `{.cover.}` expansion
  (`coverage.nim:85-88`) — unblocks source-mapped coverage-gap reports. L.
- **C2** (doc-only) explain the fixed 8192-slot bitmap convergence
  (`coverage.nim:23`); C1 is the real lever. S.

## Cluster 8 — Shrinker

- **SH1** `shrink` 2-arg overload `seq[byte]` `Int128` compile bug
  (`shrinker.nim:274`). **Does NOT reproduce at HEAD** — three faithful repros
  compiled clean under Nim 2.2.10. **Deferred:** needs chapulin's exact repro file
  / a bisect before it can be sliced; do not fix blind.

---

## §Totality harness & integration exit

### TOT-1 — table-driven §0-invariant regression corpus  ·  high  ·  NEW (round-1, rescoped round-2)
§0's invariant is otherwise *asserted*, not *built* — a one-time grep audit catches
no future regression. **Round-2 rescope (was "generative fuzz harness"):** all symex
entry points require `fn: typed` — a **literal, compile-time** Nim proc
(`symexFind*`/`symexForAll*`, `symex.nim:461,949`; `dsl_parser.nim:4` "runs at macro
time only"). `fuzz.nim`/`strategy.nim` synthesize runtime *values* over a
`DataSource`, **not** Nim source/AST — so "generate arbitrary unmodeled DSL
fragments, sited in the fuzz subsystem" is unbuildable at size M (it would demand
either a new compile-time AST-grammar metaprogramming layer or per-fragment `nim
c/cpp` shell-outs incompatible with `dt-bounded.sh`), and carries a moving-target
"what's currently unmodeled" inventory problem.

TOT-1 is therefore a **fixed, hand-authored, table-driven regression corpus**: one
test file iterating the RFC's own known repros (bitwise-on-`svInt`,
tail-return-of-local, `&=`/`/=` no-op, `symexAssume`/`symexAssert`, tuple/obj/slice
edge shapes, **a closure-body-wrapped unmodeled construct** for SND-1b, an unmodeled
witness signature for CR-2c) and asserting the verdict is **always** ∈ {classified
`sxUnknown`} — never a native crash, a macro-`error()`, or a `false sxSat`/`sxRaised`
with empty `errors`. It backstops the **three open surfaces** §0 names
(parser/type-classifier catch-alls + internal `doAssert` landmines) — *not*
statement dispatch, which Nim exhaustiveness already proves total. Lands **after**
SND-1+SND-1b+CR-1a/b/c+CR-2a/b/c so it starts green, then stays permanently as the
CI backstop (the analogue of `tsymex_phase15_CR2_cachekey.nim` for version-pin
drift).
- **DoD:** the corpus runs bounded (`dt-bounded.sh`) on both backends and is green;
  a deliberately-reintroduced SND-1/SND-1b/CR-crash regression makes it fail.
  Size M. *(True generative AST-fuzzing is a separate, much larger (L+) future item —
  explicitly out of scope here.)*

### INT-1 — chapulin pin-bump + workaround removal (recurring exit gate)  ·  NEW (round-1, hardened round-2)
The concrete Stage-exit gate, replacing the prose "workarounds removable."
**Recurring, not big-bang (round-2):** because nearly every symex slice bumps
`symexWalkerVersion` independently, run chapulin's smoke suite against nelli
`main` **after each SW-bumping slice**, not once at the end — otherwise a red
chapulin harness at the final ~13-version jump has no bisection story. This is cheap
given `dt-bounded.sh` discipline is already per-slice. On the final landing, bump
chapulin's pin and delete/revert each named workaround, confirming the harness stays
green: `atByte` mask chokepoint, hand-unrolled loops, `p = p & x` substitution,
`parseInt`-for-`parseBiggestInt` (M2/B4), nested-if depth bound, `encodeByteSeqIR`
helper, and the others in `nelli-findings.md`'s per-finding "Workaround:" lines.
- **Rollback clause (round-2):** if a per-slice chapulin smoke run goes red, the
  offending slice's SW bump is revertable independently (each slice's `Ver` scope is
  narrow — verify no later slice's cache-key/witness format already depends on it
  before promising this). Log any workaround that *can't* yet be removed with the
  slice that would unblock it.
- **Completeness caveat:** INT-1's workaround list lives in an external repo
  (`/mnt/c/…/chapulin/docs/nelli-findings.md`) not checked into nelli — hash-pin
  or copy the "Workaround:" list into this repo so the exit criterion is verifiable
  from here.
- **DoD:** each workaround removed → chapulin harness green on the new pin (verified
  incrementally per SW-slice, not only at the end).

---

## Version-pin discipline (cross-cutting — round-1, hardened round-2)

This project has a **documented live regression** from exactly this gap
(`f54a591`: a9_casefold pin missed the 34→37 bump since A7-S1). Two independent
version consts gate the cache/witness contract:

- **`symexWalkerVersion`** (`canonicalize.nim:96`) — bumped on any **verdict or
  cache-key** change. The pin set is **found by grep**, not a fixed list:
  `grep -rl 'check symexWalkerVersion == "' tests/` (currently **7** files, incl.
  `tsymex_phase15_CR2_cachekey.nim`).
- **`renderAsChoicesVersion`** (`canonicalize.nim:52`) — bumped on any **witness
  serialization shape** change (e.g. new witness-reader shapes: M1, CR-2c, P1, P2a/b).

**Per-slice obligation (part of every slice's DoD):** the `Ver` column records which
const(s) a slice bumps. A slice that bumps either const must, *in the same slice*,
bump the const **and** update the pin set on **both** `c` and `cpp` backends. Convention
(round-2, ties to INT-1 sizing): **one new pin-assertion file per slice ID, not per
sub-letter** (CR-1a/b/c share one; CR-2a/b/c share one) — this caps pin-set growth.

**Parallel-worktree collision (round-2, must-apply):** ~17 slices bump SW. Two
`—`/no-hard-dep slices developed in parallel worktrees (e.g. SND-2, CR-1a, M3) will
**both** claim the same next SW literal (37→38), a *semantic* collision at rebase,
not just a git conflict. **SW-bumping slices must serialize their bump against a live
base** — a slice reads the current `symexWalkerVersion` at rebase time and takes the
next integer; no two in-flight SW slices share a base version.

**SW pin idiom (Corey-decided 2026-07-12 — synthesis).** The 7 SW pins used brittle
exact-equality (`check symexWalkerVersion == "37"`), which breaks on *every* future
bump regardless of relevance (the direct cause of the `f54a591` staleness) and
collides across ~17 parallel SW-bumping slices. **Decision:** keep the *canonical*
`tsymex_phase15_CR2_cachekey.nim` pin as `==` — the deliberate conscious-bump gate the
`symex-version-bump-cr2` memory mandates — and convert the *incidental* feature-test
pins to the RC-style tolerant floor (`check parseInt(symexWalkerVersion) >= N`). This
kills ~200 pin touches across the RFC and most of the collision hazard while
preserving one loud drift gate. **Per-slice obligation restated under this idiom:** a
SW-bumping slice bumps the const, bumps the canonical `==` pin to the new literal
(conscious acknowledgement), and raises any incidental `>=`-floor pins only if the
slice needs a higher floor. The serialize-against-live-base rule above still applies
to the canonical `==` pin (the one place two in-flight slices could still collide on a
literal).

---

## Healed since the findings doc (verified — not sliced)

- **#5** var-out-param helper in a loop — 5 shapes all `sxSat`/expected.
- **#11** depth-3 nested-if string helper + string op — depth 1–6 + replace→contains
  all clean.
- **#7** `toLowerAscii`/`toUpperAscii` symptom — modeled by A9 (walker v37); every
  comparison shape returns validated `sxSat`. (Residual `probeProto` gap → M6.)
- **`pred`/`succ`** — work via generic call-inlining.
- **`..<`** — matched as a literal infix; never lowered through `pred`.
- **SH1** — see Cluster 8 (does-not-reproduce; deferred, not healed-confirmed).

## Sequencing & Phase-DoD

**Order (dependency-respecting, round-2):**
1. **SND-1** (soundness root — unblocks safe expression-degrade), **SND-1b** (closure
   axiom bypass — same taint infra, whole-run degrade), then **SND-2**.
2. **CR-1a**, **CR-1b** (real bug fixes at true locus — *independent of SND-1*),
   **CR-1c** (safety net + generic carrier), **CR-2a** (needs SND-1), **CR-2b**
   (independent), **CR-2c** (witness-reader `error()`, independent).
3. Model/parser feature slices (M1–M5, P1–P4) — each turns a now-`sxUnknown`/
   -`error()` construct into real `sxSat`; independently orderable. **M2 early**
   (unblocks chapulin B4). M1/CR-2c have no SND dep (class-C).
4. Solver slices Q1 (spike)/Q2 (re-scoped after SND-2; can run parallel with 3).
5. **TOT-1** once the Cluster-1/2 slices land (starts green, stays green).
6. **INT-1** — recurring per SW-bumping slice throughout 1–4; final workaround
   removal once the symex slices land.
7. Fuzz/coverage clusters (F*, C*) — **decoupled track**, any time, no gate on 1–6.
8. SH1 deferred pending repro.

**DoD:** every LIVE/NEW slice ships with a both-backend (`c`+`cpp`) regression
green; the correct `symexWalkerVersion`/`renderAsChoicesVersion` bump + pin-set
update lands *in that slice* (serialized against a live base); each ADR from
"§ADRs likely introduced" lands in `SYMEX_PLAN.md`'s ADR section in the slice that
introduces it, and that file's stale Status table is refreshed (or explicitly marked
superseded by this RFC) as part of this RFC's landing; the §0 invariant holds under
**TOT-1** (never a crash/macro-error/false-`sxSat`); **INT-1** confirms chapulin's
harness re-runs green per SW-slice with its documented workarounds removed. SH1
excluded (no repro). Fuzz/coverage doc-only items (C2, F5) are documentation DoD.

## ADRs likely introduced

*Landing obligation (round-2): each ADR below lands in `docs/SYMEX_PLAN.md`'s
"Architectural Decision Records" section in the same slice that introduces it. That
file's Status table is stale since ~Phase 13 (claims walker version "3", 58 test
files) — refresh it or mark it superseded by this RFC.*

- **`isAssume` semantics** (SND-2) — a filter/prune IR kind distinct from
  `isAssert`; acceptance mechanism = compiler-enforced `case` exhaustiveness across
  the 10 uniform sites, plus the 2 explicitly-DoD'd non-uniform sites (cache-key tag,
  `collectAssertRanges`).
- **Closure ground-axiom soundness** (SND-1b) — an uncertain closure-body return
  must not be axiomatized; reuse `closureForcedUnknown` whole-run degrade.
- **Crash-doctrine & internal-fault classification** (CR-1c) — the boundary between
  a loud walker-internal-invariant crash and a classified construct-gap
  `sxUnknown`; the distinct `weInternalWalkerFault` kind; the `try/except`-never-
  `try/finally` backend rule; and the walker-unit `--checks:on`/no-`--panics:on`
  build requirement.
- **One generic classified-degrade carrier** (CR-1c/CR-2b) — `SymexClassifiedDegrade
  Error{kind}` superseding the 18 one-off carrier types (incremental retire).
- (Possibly) **object construction as expressions** (P2a/P2b) vs the field-split
  heap model (variant construction deferred to its own ADR).
- **Solver-capability limits** (Q1/Q2) — the loop-unwind × Sequence-theory
  divergence class and the degrade-not-diverge policy (records why these stay
  fail-soft and the `dt-bounded` rejection rule).

*Note: SND-1 does **not** introduce/amend an ADR — it extends the existing
`Path.uncertain` suppression to the `isUnsupported` producer; ADR-0012 D2 precedence
is untouched.*

## Round-3 ledger — INT-1 first run (chapulin 0.1.0 re-test, Windows, 2026-08-06)

INT-1 was blocked on a release; 0.1.0 (tag `4990026`) is that release, and
chapulin's 2026-08 re-test of its full symex twin suite against it — run natively
on Windows via the `chapulin-symex:2.2.10` toolchain image (MSVC, Z3 4.13.4
x64-win) — is effectively INT-1's first execution. This ledger records that
round's verdicts, the triage that followed on the same machine, and the v64
fixes. Meta-finding first, because it reframes two "healed" claims:

**Platform divergence was the untested axis.** nelli's own verification
(sweeps, the RFC's healed-checks, both-backend DoD) only ever ran on
Linux/podman. Windows main-thread stacks are 1 MB (MSVC) / 2 MB (MinGW) vs
8 MB on Linux, and the Windows libz3 (4.13.4 — the *bottom* of nim-z3's
supported 4.13.x–4.16.x window; `Z3_mk_seq_replace_all`-class symbols absent
below ~4.15.5) is a different build than the podman image's. "Both backends
green" could not catch either axis. The new `symex-windows` Actions leg
(`.github/workflows/symex-windows.yaml`) closes the gap: TOT-1 corpus + the
round-3 regression pins, natively on `windows-latest`, deps cloned at
`milpa.lock` provenance SHAs, Z3 pinned to the field's 4.13.4.

**Diagnostic calibration (this machine, Windows container, MSVC):** a stack
overflow exits **255 with no output whatsoever** (0xC00000FD never surfaces
through the CRT); an uncaught Defect exits 1 with a traceback; `quit(n)` = n.
Chapulin's "bare non-zero exit, no message" reports were all the 255 signature.

| Re-test item | Triage verdict | Fix (walker v64) | Pin |
|---|---|---|---|
| #11 depth-3 nested-if + string op → crash (listed "healed") | **Stack overflow.** Depth-2 STATEMENT-form twins crash too at 1 MB — the cliff was never "depth 3", it is stack size. The Linux "healed, depth 1–6 clean" claim was an 8-MB-stack artifact; nothing ever regressed and nothing was ever fixed — Windows was simply never run. 16 MB stack → both depths prove sxUnsat. | `runSymex` executes the solve on a **16 MB fiber stack** on Windows (`runSymexWithBigStack`; fiber = same thread identity + TLS, so every threadvar sink stays coherent; `-d:symexNoBigStack` opts out). | `tsymex_retest_c11_stack` |
| #3 residual: bitwise combine + boolean guard → `doAssert inner.kind == svBool` at runtime.nim:3155 | **Parser bug, platform-independent, reproduced exactly.** Nim spells boolean and bitwise `and`/`or` identically; the D1c short-circuit lift also fired for an INT-typed infix whose RHS carries a defect fork (`(uint16(data[o]) shl 8) or uint16(data[o+1])` — the index access), binding the BV16 LHS into a `tBool()` temp and emitting `uNot(temp)`. Combines with operands pre-bound to `let`s take the fast path — exactly why chapulin's bisect saw "combine alone fine, guard alone fine, composition crashes". | D1c machinery gated on the infix classifying `itBool`; bitwise `and`/`or` lowers as a plain binop with its RHS preamble hoisted unconditionally. Sibling audit: `uNot` on a BV → `notBV` (Nim `not` on ints IS the complement), `lowerBool` chokepoint + HashSet-key asserts → SND-3 in-band degrades (`svIntToBV` bridge for `.len`-derived keys). | `tsymex_retest_c3_bitwise_guard` |
| #6 chained scans → "REGRESSED sxUnknown→crash" | **Not the loop machinery.** DESTRUCTURING a tuple return from a raising, loop-bearing callee (`let (_, p1) = readCStringTwin(data, 2)`) sends a composite retSym into `retBindEq`, whose non-primitive arm RAISED ValueError from inside the walk — unwinding through live `seq[Path]` (the b7258f7/CR-1c C-backend silent-loss hazard). One raise, nondeterministic manifestation: chapulin saw a native crash; the same repro on the same commit also surfaced as a net-caught `weInternalWalkerFault`. A `discard`ed call of the same callee proves sxUnsat (P1 wired tuple return *parsing*, not the raise-fork return *bind*). | In-band classified degrade (`feUnsupportedOp`, path tainted uncertain) at the isReturn scalar-raise drain's binding site — deterministic, never a raise. (Nuance found while pinning: the STRING-building chapulin shape now degrades even earlier, at the pre-existing `seUnsupportedStringOp` gap for char-arg `.add` — the drain guard is exercised by string-free tuple scans.) | `tsymex_retest_c6_tuple_chain` |
| #5(b) sxUnknown with EMPTY `errors` (Invariant 7) | Confirmed live (probe5 + scanlen shapes). Two walk-budget sites set `w.sawUnknown` bare: `maxLoopUnwind` exhaustion and `maxFrontierSize` prune. | New tail-appended `beBudgetExhausted` kind + `WalkCtx.walkDegradeErrors` live sink (the lowering threadvar sink is reset per wrapper entry — unusable from walk arms) + a verdict-time backstop (an sxUnknown that would still escape empty is stamped `weInternalWalkerFault` as a classification-gap signal). | `tsymex_retest_c5b_unknown_errors` |
| #pred (`pred`/`succ` no DSL case; `..<` → `a .. pred(b)`) | Confirmed (zero parser hits). This was also the ACTUAL cause of the "seq slice compile abort" report — `rest[1 ..< closeBracket]` died on the pred-rewritten bound. | Arithmetic passthrough at the A7 `ord`-identity locus: `pred(x[,k])` → `x-k`, `succ(x[,k])` → `x+k` (int-classified operands, both arities). Note: `pred(x)` on UNBOUNDED int correctly reports sxRaised — pred(int.low) really overflows (R16-4). | `tsymex_retest_pred_succ` |
| seq slicing `data[a..b]` / `data[4 .. ^1]` | **Cannot reproduce on HEAD** — both shapes prove sxUnsat natively on Windows. The cataloged abort was the `pred` item above. If chapulin's real `parseTftpUri` still aborts, that is a new shape for round 4. | — | (scratch probes; superseded by the pred pin) |
| #4 loop-produced string across a named binding → sxUnknown | Not fixed this round (Q2 territory — specced, unbuilt). NOTE: check Z3 version parity first — 4.13.4 vs the podman build can legitimately diverge on Sequence-theory verdicts. | — | — |
| #5(a) var-out-param helper provability | Not fixed this round (Q2-adjacent). Its (b) half — the empty-errors violation — is fixed above; the classification now says WHERE it degrades. | — | — |
| dbReusePhase pruning (F1) | **STALE FINDING — the whole fuzz track already shipped in 0.1.0** (round-3 correction, verified in source + tests): F1's `corpus` DB section (`saveCorpus`/`loadCorpus`, format v3) is wired through `fuzz.nim`; F2's up-front coverage-replay of preloaded seeds, F3 `minimalCovering*`, F4 `stopOnFirstCrash`, F7 `FuzzReport.droppedSeeds`, F5/F6/F8 all present with `tfuzz*` pins. `dbReusePhase` still prunes `primary` BY DESIGN — the re-test's "still present (static read only)" checked the pruning, not the new channel. Chapulin action: replace the `.soak-corpus` sibling-testId workaround with the real corpus channel. | (shipped pre-0.1.0) | `tfuzzcovcorpus`, `tfuzzdroppedseed`, `tfuzzseedcov` |
| HashSet witness consistency (NEW, found this round) | Root-caused and FIXED at v65: a symbolically-keyed membership is satisfiable by a const-TRUE (universal) model array — nothing to enumerate, so the finite witness rendered `{}`. Fix: record the membership KEY TERMS per set and include their model values at extraction (plus a store-chain harvest). Witness now consistent (`s=""`, `hs={0}` verified). | Key-term registry + store-chain harvest (walker v65) | `tsymex_retest_c3_bitwise_guard` |

**Process obligations discharged:** the five `tsymex_retest_*` pins are
registered in the nimble test task; heals-without-pins is what let #11/#5/pred
regress or persist silently — TOT-1's corpus must ingest the ENTIRE chapulin
catalog *including healed items* going forward.

**Crash-doctrine decision (Corey, 2026-08-06):** the Defect net is IN — one
`except Defect` arm on the outermost `runSymex` try, classified
`weInternalWalkerFault` (supersedes CR-1c's "Defects keep crashing loudly"
carve-out for consumer-facing totality; nelli CI tracks the kind as a
walker-bug backlog). Exercised by `tsymex_retest_defect_net` via a second
fault-injection sentinel (`__inject_walker_defect__`, AssertionDefect-typed).
Caveats recorded: inert under `--panics:on`; stack overflow / libz3 aborts
are not exceptions (the fiber-stack work covers the former).

**Natural-form probe (post-fix, INT-1 stretch check):** `symexFind` on
chapulin's REAL, unmodified `parseTftpUri` — which 0.1.0 could not even
COMPILE — peeled three §0 clause-(b) aborts in sequence, each fixed in this
round: (1) the `pred` gap; (2) `binopForInfix`'s `error()` on an unmodeled
infix (`a .. b` building an HSlice value in expression position — now a
CR-2a-style classified degrade, pinned by `tsymex_retest_infix_degrade`);
(3) `classifyObjectRecordFields` crashing on `nnkPostfix`/`nnkPragmaExpr`
field names in a raw generic `getImpl` record (now unwrapped tolerantly).
The probe then ran to a CLASSIFIED sxUnknown whose error is the Defect net
working live: `weInternalWalkerFault: AssertionDefect …
runtime_strings.nim:202 iekStrFind: arg not svString` — `rest.find(']')`
passes a CHAR needle where the lowering expects a string. Exactly the net's
telemetry contract: a live walker-bug backlog entry, not a dead process.

**Round-3 follow-up landings (walker v65, post-0.2.0-tag):** char-needle
search family modeled (`needleAsStr` fromCode bridge; the Defect net's first
field catch — closed); `contains`-via-openArray receiver unwrap; HashSet
witness consistency (key-term registry — closed).

**Q2 characterization (round-4 input, probed at v65):** the "chain proves /
bound degrades" asymmetry is at least partly PARSE-ROUTING, not solver:
(a) the string-op user-proc diversion guard tests `getImpl.kind ==
nnkProcDef` only — strutils is mostly `func` (`nnkFuncDef`), so a
chain-position `strip` routes to the STUBBED `iekStrUnsupported`
("not modeled until its Cluster-S cycle") instead of inlining; (b) a
let-RHS `strip` DOES inline and then CR-2a-degrades on the default
`chars = Whitespace` set-literal (`nnkCurly` — no expression support).
Both degrade classified post-v64 (Invariant 7 holding), but chapulin's
green `stripTrailingDotSpaceTwin(path).endsWith(".md5")` sxUnsat proof
threads a third path (user-proc wrapper inlining) — map that path before
touching the guard: widening `nnkProcDef` → `{nnkProcDef, nnkFuncDef}`
changes routing for every unlisted strutils func and must not regress the
INT-1 suite. Q2 proper (defect-search over s.len-bounded loops) remains L.

**Natural-form probe, final v65 state:** every wall is now a CLEAN classified
degrade — the last probe run reports `seUnsupportedStringOp: "iekStrRfind:
operand lowered to svBV8 — not svString"`, i.e. `hostPort` (bound from the
`rest[0 ..< slashPos]` STRING SLICE) is mis-lowering as a single CHAR
(iekStrAt-shaped) instead of a substring — a precise, located round-4
lowering bug, surfaced by the v65 `requireStr` classified guards (all 21
string-op operand doAsserts converted; zero Defect-net entries left on this
path).

**Round-4 Slices A + B (walker v66, ADR-0026/ADR-0027):**
- **Slice A — bound string slices are real substrings.** The
  `rest[0 ..< n]`-binding mis-lowering root-caused: the `..<` template
  expansion wraps the slice index in `nnkStmtListExpr` (and let/var RHS in
  `nnkHiddenStdConv`), and the shape-only `nnkInfix` test fell through to
  the single-CHAR path — every downstream op degraded, and two mis-lowered
  slices would have compared as first-char equality (wrong-verdict hazard,
  pinned). v66 unwraps the wrappers and dispatches on the index TYPE.
  Calibration exposed a NEW hang class: a free-int-param bound is
  BV64-allocated and its `bv2int` bridge into Sequence theory is a Z3
  non-terminator on the UNSAT side (> 3 h, bisected) — `iekStrSubstr` now
  requires Int-sorted bounds (literals adapt via an svInt proto; find/len
  results are already Int) and declines BV bounds classified (ADR-0027);
  the Int-representation pre-pass is the recorded round-5 lift. Pins:
  `tsymex_r4_slice_binding` (find-bounded SAT/UNSAT/prefix-inequality +
  the decline pin).
- **Slice B — `strip` modeled, no loop.** ADR-0026: quantifier-free
  decomposition constraints over per-occurrence fresh strings
  (`s = pre ++ core ++ suf`, regex-star membership, boundary clause) —
  sound, complete, unique. The chapulin #9 headline shape (`strip` result
  BOUND to a name, read across statements) now PROVES: chain-SAT,
  never-lengthens-UNSAT, and bound-across-SAT all decide in seconds; the
  one divergent query (full idempotence UNSAT — nested double
  decomposition) ships as an rlimit-bounded never-SAT pin per the
  dt-bounded doctrine. Pins: `tsymex_r4_strip`.

**C1 — STALE FINDING, already shipped in 0.1.0** (round-4 correction,
verified in source + test): the slot→`file:line:col` side-table exists —
`registerEdgeSource`/`edgeSources` populated at `{.cover.}` expansion, and
`uncoveredSources()` IS the source-mapped coverage-gap report chapulin's C5
deferral wanted (collision honesty documented on the proc). The
`tcovsourcetable` pin existed but was unregistered in the nimble task — now
registered. Chapulin action: replace C5's coarse visited-edge count with
`uncoveredSources()`.

**Open for round 5:** Q2 residue (non-strip loop-produced bindings; the
routing-guard widening design); the string-adjacent Int-representation
pre-pass (ADR-0027's lift); SH1 (needs consumer repro).

*(Round-5 design update, 2026-08-08: both design passes are written —
ADR-0028 in SYMEX_PLAN.md covers the Q2 residue as accumulating-scan
recognition with the ADR-0027 pre-pass as prerequisite slice 1; ADR-0029
covers P2b literal-discriminant variant construction. Implementation is
round 6.)*

## Round-5 ledger — discard totality + P3 confirmation (2026-08-07)

Source: chapulin's `docs/nelli-findings.md` "STILL OPEN at 0.3.1" table,
cross-verified against HEAD before work started. The three tractable items
landed; the design-pass items (Q2 residue, P2b variant construction, the
&-concat shape-sensitivity bisect) remain open for the round-5 design docs.

**Discard totality (walker v68 — the round-4 CRITICAL finding).** The
`nnkDiscardStmt` arm dropped every discarded expression outside its allowlist
(E8 exception intrinsics, M2 parseInt/parseBiggestInt) to `mkBlock(@[])` —
`discard f(x)` never walked `f`, so surrounding verdicts read vacuously
narrow (Invariant 3, the same unsoundness class M2's discard-parity fix
closed for parseInt, but general). v68 lowers EVERY discarded expression to
a synthetic sink `let` (`discardSink`), typed via the let-section
`classifyType` discipline (unmodeled types map to the classified
`__unsupported` placeholder — no new macro-error wall; lambda/closure IR
binds under the let-arm's placeholder-type precedent; bare `discard` stays a
no-op). The M2 parseInt allowlist entry is subsumed by the general path and
was removed (its D1–D4/M2-5..7 pins prove parity); the E8 entry is kept for
its bespoke sink types. Pins: `tsymex_r5_discard` (defect-in-discarded-call
FOUND + guarded-UNSAT honesty, discarded non-call `data[i]` IndexDefect
FOUND + guarded-UNSAT). Consumer note for chapulin: `discard`-masked shapes
re-probe honestly now — expect previously-vacuous `sxUnsat` to surface as
`sxRaised`/`sxUnknown` (the while-scan and &-concat opens were measured
post-workaround and are unaffected). One in-repo pin was retracted on
exactly this ground: `tsymex_retest_c6_tuple_chain`'s "discarded
tuple-returning call still proves sxUnsat (capability pin)" was the
discard-drop artifact — the same call BOUND pins classified `sxUnknown`
two tests down. It now pins degrade-like-its-bound-twin. Full 83-suite
Windows-container sweep at v68: 80 green; 3 failures are pre-existing at
clean 0.3.1 (`tsymex_phase1_dsl`, `tsymex_phase15_g8_multi_param`,
`tsymex_phase15_g10_smoke` — all the `dsl_typebridge.nim:337 "node has no
type"` class, see the discovered-en-route note below).

**P3 explicit two-endpoint seq slice — CONFIRMED FIXED at v67 (0.3.1).**
The chapulin "still open" row rested on a v0.3.0 probe that predates v67's
`iekSeqSlice`. New load-bearing pins in `tsymex_r4_seq_slice`: two-endpoint
`data[4 .. data.len-1]` SAT-with-witness + view-length UNSAT, and half-open
`data[4 ..< data.len]` view-element UNSAT. No engine change needed. Chapulin
action: drop the P3 workaround (point-substitute) at the next pin bump.

**Discovered en route (pre-existing, NOT v68):** three suites fail to
COMPILE at clean 0.3.1 HEAD with `dsl_typebridge.nim:337 "node has no
type"` (each verified by stash/re-run without the v68 diff):
`tsymex_phase1_dsl` (the ADR-0002 Layer-1 parser-isolation suite — dies on
the untyped `p and q` fixture), `tsymex_phase15_g8_multi_param`, and
`tsymex_phase15_g10_smoke`. Some expression arm grown since these last ran
calls `classifyType` on AST that isn't semchecked (for phase1_dsl that is
an ADR-0002 layer-boundary leak by the suite's own doc comment). The
Windows CI leg runs only the TOT-1 corpus + round-3 pins, so the breakage
went unseen. Not in the round-5 tractable scope; filed here for triage.

**Round-5 addendum — sello consumer report (2026-08-07, second consumer).**
sello (pure-Nim Curve25519; Z3 proof harnesses `symex_recode.nim`,
`symex_mask.nim`) reports three engine issues, each validated on the 4990026
pin AND re-confirmed unfixed on v0.3.2 (v64's crash doctrine changed the
surface of two from uncaught Defects to classified `sxUnknown`, root causes
untouched):
1. **bv32/svBV64 width confusion in lowerArith/overflowCond** — two shapes,
   one suspected root cause (a 64-bit-kinded SymVal minted at a branch merge
   and along chained-call value flow, tripping 32-bit accessors and
   width-strict binops). Shape A: ≥2 chained `int32` callees threading a
   carry (`bv32` FieldDefect via `+`); shape B: branch-merged `int32` local
   in a binop with a symbolic operand (`binBV` width-mismatch assert via
   `and`). Plain-`int` twin of shape A is clean. Sub-report: neither
   `{.push overflowChecks: off.}` nor `arithChecks = {}` suppresses the
   overflow-lowering path — knobs apparently not consulted there.
2. **Composite (tuple) returns from nested callees** — the known retBindEq
   svTuple gap (catalog #6 drain degrade), now formally a capability request:
   `let (p, q) = innerTuple(x, y)` degrades `feUnsupportedOp`/`sxUnknown`.
3. **`negBV on non-BV SymVal`** for `-int32(bFlag)` — bool→int32 conversion
   yields a kind unary-minus lowering has no case for; standalone, both
   versions. The literal ref10 mask idiom.
Impact: sello re-encoded recode lemmas in plain int, split mask proofs, and
used var out-params over natural tuple returns.

**All three FIXED (walker v69, 2026-08-08):**
1. **Literal-width protos.** Root cause was `lower`'s `iekIntLit` arm
   defaulting to svBV64 when no proto is passed — and the isLet, isAssign,
   and call-argument sites passed none, so `let mask = -1'i32`, an
   if-expression arm's temp bind (the M5 A-normalisation), and bare-literal
   actuals all minted 64-bit SymVals into 32-bit flow. Fix: `intLitProto`
   (declared-type proto, the iekArrayLit elemTy precedent) at isLet/call-arg,
   `envLitProto` (current-binding proto) at isAssign. isReturn already passed
   the retSym proto. With widths right, the previously-crashing
   `rLimb + mask` probe now finds the GENUINE int32 underflow witness —
   the crash was masking a true positive. Knob sub-report resolved as
   side-effect: the crash lived in cond CONSTRUCTION (before the drain's
   `arithChecks` filter), which is why no knob suppressed it; construction
   still runs regardless of `arithChecks` (drain-time filtering is the
   designed semantic) — left as a pure-efficiency follow-up, no longer
   observable as a failure. Pins: `tsymex_r5_bv32_width` (8).
2. **svTuple retBindEq.** Structural per-field binding (recursive,
   `reconcileInt` per field); svTuple joins the drain guard's wired set.
   svArray/other composites and closures returning tuples stay in the
   degrade net. The c6 pin upgraded accordingly: the destructure-from-
   raising-scan shape now walks PAST the tuple bind and degrades at the
   honest boundary (`beBudgetExhausted`, the Q2/maxLoopUnwind class) —
   direct evidence for the round-5 Q2 design work. Pins:
   `tsymex_r5_tuple_return` (3), `tsymex_retest_c6_tuple_chain` (updated).
3. **bool→int conversion.** `int32(b)` A-normalises to a 1/0 if-statement
   at the conversion's classified width via the M5 idiom (was a
   pass-through leaving svBool at negBV). Pins: `tsymex_r5_neg_bool_conv`
   (4, incl. the ref10 `-int32(b)` mask lemma proving sxUnsat).

**Chapulin's "&-concat sxUnknown" HIGH open — ROOT-CAUSED and FIXED (v69),
and it was never about concat.** Bisected via a 9-shape probe ladder: every
concat spelling over a plain string param proves clean; the degrade fired
exactly when a MODULE-LEVEL CONST (`SidecarExt`) appeared in the
expression. A const sym in value position emitted `iekVar(name)` with no
binding in any env → KeyError → weInternalWalkerFault → sxUnknown — in
whatever expression referenced the const. That explains the reported
shape-sensitivity: chapulin's "curiously proves" variant had the const
folded/absent. Fix: parseExpr's nnkSym arm folds nskConst syms to their
getImpl value at parse time (unresolvable shapes keep prior behavior).
Pins: `tsymex_r5_const_fold` (6, incl. the writeSidecar length lemma, the
`&=` spelling, const-in-callee, and a fixed-width int const composing with
the literal-width protos). Chapulin action at the pin bump:
`t_symex_checksum` should re-probe — its honest `sxUnknown` was this.

**Discovered en route (v69 round):** `low(int32)`/`high` magics inside a
symex target produce a walker fault (probed while pinning the bounded
`rLimb + mask` variant — the literal spelling proves clean). Small,
classified-degrade-at-worst candidate for the parser's magic table; filed
untriaged (round-6 slice A0).

**Discovered by the round-6 architect review (2026-08-08): LIVE
UNSOUNDNESS in the v60 scan lift.** `tryRecognizeScanIdiom` accepts any
int-typed bound without proving `bound ≤ s.len`; Z3's `indexOf` returns
-1 for out-of-range starts instead of raising — so `while i < bound and
s[i] != lit` with `bound > s.len` (or a negative start) reports a clean
fall-through where real Nim raises IndexDefect: a false `sxUnsat` under
`tIndexError` search, shipped since v60, untested because every existing
pin uses `bound == s.len` literally. Fix is round-6 slice B0, flagged as
a queue-jumping soundness hotfix candidate.

**`maxLoopUnwind` default — DECIDED: stays 5.** The findings-doc ask was
"raise the default / document it"; v67 put the decidability-boundary
doctrine on the field itself, which resolves the actionable half. Raising
the global default trades every caller's solve budget against the dependent-
loop cases that exhaust it — and those cases are exactly the Q2/#6 class
whose real fix is the round-5 design work (closed-form lifts), not a bigger
unroll constant. Per-call override remains the sanctioned lever.

## Round 6 — scan closed forms + variant construction (RFC, 2026-08-08)

Design basis: ADR-0028 and ADR-0029 (SYMEX_PLAN.md), as revised after the
2026-08-08 grill-me session AND the round-1 architect review (4 lenses,
2026-08-08 — which retired the bitwise→LIA leg on a false premise, found a
live v60 soundness bug, and added the pair-loop slice). Two tracks; Track A
lands ENTIRELY before Track B begins (hard ordering — per-slice
`symexWalkerVersion` bumps serialize against a live base per the
Version-pin discipline above, and two parallel tracks would collide on the
SW literal exactly as the ~17-slice case did). **Naming fix (round-2
architect review):** the round-5 draft named the exit-gate releases
"v70"/"v71", distinct from SW literals in intent but IDENTICAL in
spelling to them — and the collision is not hypothetical: B0 (below) is a
queue-jumping Track-B slice that lands FIRST and already bumps
`symexWalkerVersion` to the literal **70** (confirmed in the landed
source comment at `dsl_parser.nim` ~2942). By the time Track A's own exit
gate is cut, its four SW-bumping slices (A0–A3) will have moved the
walker to roughly v71–v74 — "release v70" would name a point that is, by
construction, never the walker version current at that release. Same
issue compounds for Track B's exit gate against "v71". Renamed to match
this doc's own precedent elsewhere (round-5 ledger: "0.3.3 (walker
v69)") — a semver release tag, kept visually and lexically disjoint from
the `vNN` SW-literal counter: **release 0.4.0** at Track A's exit gate,
**release 0.5.0** at Track B's exit gate (current released version is
0.3.3). Intermediate slices still bump SW per the standing per-slice rule
(Ver column below); the SW literal reached at each release is whatever
the per-slice bumps land on, read from the grep-discoverable pin set, not
guessed from the release name.

The joint consumer milestone lives in the recurring INT-1 gate; round 6
runs INT-1 at REDUCED interim granularity: chapulin builds against
nelli git HEAD (not a release) after A3 and after B4, so a
consumer-shape regression bisects to ≤3 slices, honoring INT-1's
no-big-bang rationale without a release per slice. **Interim-check
mechanics (round-2 — nothing automates this today):** chapulin pins
nelli by git tag in `milpa.kdl` (`ref="v0.3.2"` at review time —
itself one release stale) and its CI never invokes milpa, so the interim
build is a MANUAL procedure with a written runbook: (1) capture the
exact nelli SHA at the moment A3/B4 lands — the check runs against
that pinned SHA, never floating `main` (a later-resolved HEAD silently
defeats the ≤3-slice bisection rationale); (2) edit chapulin
`milpa.kdl` `ref=` to that SHA, `milpa fetch`, run
`scripts/dev-test.ps1`; (3) REVERT the ref to the release tag and
review the `milpa.lock` diff for a leaked pin — this revert is a
checklist item in A3's and B4's Done-when. Single owner (same author on
both repos); a chapulin CI leg for milpa-driven builds is recorded as a
nice-to-have, not built this round.

**Prerequisite: DISCHARGED** — 0.3.3 (walker v69) released 2026-08-08.

**Soundness exception to the track ordering:** B0 fixes a LIVE
unsoundness shipped since v60 (false `sxUnsat` from the scan lift under
an over-length bound) — soundness fixes jump the queue; B0 may land as a
standalone hotfix release ahead of Track A rather than waiting behind
seven slices.

**Standing DoD for every slice below (round-3 process obligations):**
new/changed pins registered in the nimble `task test` list AND the
`symex-windows` CI leg; SW-bumping slices update the version-floor pin in
the same commit; every new classified-decline site (a) names and reuses an
existing taint/drain mechanism in the SND-4 "mirror, don't reinvent"
format, (b) opens its `SymexErrorInfo.msg` with `<file>:<line>:<col>: `
plus the construct's `n.repr` (new `siteMsg` helper — round-1 design
lens; the existing `beBudgetExhausted` message's missing loop identity is
the cautionary example), and (c) lands a TOT-1 corpus fixture. Two
round-2 additions: (d) every NEW `classifyType` call site (B1a's
predicate, B3/B4's recognizers) uses the `typeKind != ntyNone` guard —
the exact crash class A5 fixes must not be reintroduced by new code the
A5 regression pins don't cover; (e) any slice adding an `iek*`/`is*`
kind budgets the exhaustive-switch fan-out (~6 files: types,
dsl_parser's parse+emit sites, abstraction, canonicalize, runtime's
walker+collector arms — Nim's exhaustiveness check makes each mechanical
but none optional). A6 and B7 additionally refresh the user-facing docs
their capabilities obsolete (`docs/symex/README.md`'s variant table +
IR-kind tables; `tutorial.md` §6's "honest moves on UNKNOWN" gains the
recognized-shape fourth path, §7 gains construction).

**`siteMsg` ownership + a real gap it doesn't close (round-2 architect
review).** This convention had no owning slice through round-5 — folded
into **A0** (the first slice to land): `proc siteMsg(n: NimNode, note:
string): string` in `dsl_parser.nim`, formatting `n.lineInfoObj` +
`n.repr` + `note`, used by every PARSE-TIME decline this RFC adds (A1's
`itMultiVariant` decline, A3's budget-cap-exceeded message, P2b-style
sites generally). It does **not**, by itself, reach every decline the
round's user-journey walk hits, because two of round 6's own new sites
are WALK-TIME, where no `NimNode` exists to build the message from:
A3's `maxVariantConstructorForks` cap and B6's dt-bounded divergent-query
fallback. Neither `IRStmt` nor `IRExpr` carries a location field today
(confirmed — grep for one comes up empty), so a walk-time site can only
get a `siteMsg`-shaped message if the responsible parse-time slice
threads location INTO the IR (e.g., a `loc: string` field on
`isVariantConstructSym`, captured via `siteMsg`'s components at parse
time and rendered, not reformatted, at walk time). **A3's DoD is
extended** to carry this field on `isVariantConstructSym`; **B6's is
not** (its fallback is a `dt-bounded.sh`-level bisect, not a
`SymexErrorInfo`, so it never had a `siteMsg` obligation to begin with —
noted so it isn't mistaken for a miss). Separately: the RFC's own
cautionary example — the `beBudgetExhausted` message at
`maxLoopUnwind`/`maxFrontierSize` exhaustion — is a PRE-EXISTING site, so
the standing DoD's "every **new** classified-decline site" wording does
not require migrating it, and round 6 does not touch it. Concretely, this
means B0's own fallback path (a scan whose bound is not provably
`s.len`, which falls through unrecognized to the ordinary `mkWhile`
k-unroll) still ends at the SAME loop-identity-less
`beBudgetExhausted` message B0 was framed against — the user-journey
walk that motivated `siteMsg` in the first place is not actually fixed
for that specific path by anything in this RFC. If that gap matters
before the next round, migrating `maxLoopUnwind`/`maxFrontierSize`'s two
sites is a small, independently-shippable follow-up (thread the
enclosing `nnkWhileStmt`'s `lineInfoObj` into `IRStmt.isWhile` at parse
time, read it back at the two walk-time sites) — not sliced here because
it is pre-existing behavior, not a round-6 regression.

### Track A — variant construction (ADR-0029; release 0.4.0 at gate)

| Slice | Content | Ver | Done when |
|---|---|---|---|
| A0 | **LANDED (walker v74).** Hygiene rider: fold `low(T)`/`high(T)` int magics at parse time (const-fold-adjacent; kills the v69-round discovered fault). **Also owns the `siteMsg(n: NimNode, note: string): string` helper** (`dsl_parser.nim`) the standing DoD requires of every parse-time decline this RFC adds — no prior slice built it | SW | `rLimb > low(int32)` spelling proves; pin added; `siteMsg` unit-tested (file:line:col + `n.repr` shape) and used by at least one A0/A1 decline site |
| A1 | **LANDED (walker v75).** `iekVariantLit`: literal-discriminant construction → svVariant value. **Scope enforcement (round-2 architect review):** `dsl_parser.nim:2502`'s existing `of itVariant, itMultiVariant:` combined decline arm must be SPLIT, not widened — `itVariant` routes to the new construction path; `itMultiVariant` keeps declining verbatim (own `of itMultiVariant:` arm, message updated to cite ADR-0029's "ships as its own slice only if a consumer needs it first"). Un-split, an implementer editing one shared case arm silently changes behavior for both kinds | SW | Construction + single-arm read-back SAT/UNSAT pins green; a multi-`case`-object constructor still declines cleanly (classified `sxUnknown`, not a crash) — regression pin required |
| A2 | **LANDED (walker v76).** `retBindEq` svVariant arm — the GENERAL encoding: `discEq ∧ (⋀ arms: disc==tag → arm-field eq) ∧ plain-field eq` (sound for symbolic-disc pass-through returns, not just pinned literals) | SW | Variant-returning callee flows; pass-through-param return pin green |
| A3 | **LANDED (walker v77).** `isVariantConstructSym` STATEMENT (A-normalized, M5 idiom) cloning `isVariantReassignSymbolic` (`runtime.nim` ~6379) — fork-per-tag with parse-time `case`-branch tag-set narrowing, fresh inactive-arm fields per fork (the divergence from the reassign precedent — dedicated pin), `maxVariantConstructorForks` budget (own ResourceBudget field, default 8, structural check). Budget-exceeded decline is WALK-TIME (no `NimNode` there) — `isVariantConstructSym` carries a `vcsLoc: string` field, populated via `siteMsg`'s components (`siteLoc` helper) at parse time (A0) and rendered verbatim (not reformatted) when the fork budget is exceeded at walk time, reusing the pre-existing `beBudgetExhausted` classified kind (SND-4 mirror-don't-reinvent). A1's symbolic-disc decline pin (`tsymex_r6_a1_variantlit.nim` A1-6) MIGRATED to a construction pin — a sound capability upgrade | SW | `protocol.nim:166` two-tag shape constructs; fresh-fields + decline pins green; budget-exceeded message carries file:line:col + `n.repr` sourced from the parse-time `vcsLoc` field. Then: interim INT-1 (chapulin vs git HEAD) |
| A4 | **LANDED (no walker version bump — interaction-only).** `isVariantReassign`/`isVariantReassignSymbolic` interaction with A1's `iekVariantLit` and A3's `isVariantConstructSym` construction paths: both walker arms and the witness-extraction pipeline (`extractFromSymVal`'s `svVariant` case, `emitTyAndReader`'s `itVariant` case) already operate on the `svVariant` SHAPE, not its origin, so every interaction pin (literal-then-literal reassign incl. zero-init + stale-arm-unreachable, literal-then-symbolic reassign fork-per-tag, narrowed-symbolic-construct-then-wide-symbolic-reassign composition, and witness read-back of the params driving a constructed non-param variant's discriminant/field) resolved GREEN ON ARRIVAL — no production fix required. Confirms the `Ver: —` prediction | — | `tests/tsymex_r6_a4_construct_interactions.nim` 9/9 + 39-file c-backend regression sweep (A0–A4, B0, q1, r1b, CR-2, TOT-1, every variant/reassign/retbind/tuple-return/heap-snapshot/P2b-variant suite) green |
| A5 | **LANDED (no walker version bump — parser-only totality fix).** Scope shrank to two breaks pre-landing (upstream v71–v73 pull fixed `tsymex_phase1_dsl` via the A2b classify-first restructure): `g8_multi_param`/`g10_smoke` both crashed at `dsl_typebridge.nim:337` (`getTypeInst` "node has no type", non-catchable) inside `isResolvedBoolAndOr` (`dsl_parser.nim`), ONE root cause — reached only through Cluster G's multi-param generic dispatch, where `ensureProcRegistered`'s `monomorphize()` (~:5444) textually substitutes `T`/`U` without re-running Nim's semchecker, so the and/or call node's OWN `getTypeInst` legitimately has nothing to report even though `n[0].kind == nnkSym` (the doc-warned bogus-typeKind gap surfacing through `getTypeInst` instead of `typeKind`). The RFC's literal `typeKind != ntyNone` gate idiom does not apply directly here (that gate is unsound for and/or nodes specifically, per the proc's own pre-existing doc comment — confirmed empirically bogus non-`ntyNone` on this exact node); the applicable fix is the SAME underlying idiom applied one level over: derive boolean-vs-bitwise from `n[0]`'s own resolved proc signature (`n[0].getTypeImpl`, always genuine/unaffected by `monomorphize`) rather than from `classifyType(n)` on the unreliable call node, with the new `classifyType(retTy)` call site itself gated by `typeKind != ntyNone` per standing DoD clause (d) | — | Both files compile clean and all pre-existing assertions pass (g8_multi_param 3/3, g10_smoke 7/7); no second latent break unmasked; full sweep green |
| A6 | Chapulin: un-void `t_symex_decode` construction + EXTEND the differential oracle to compare constructed packets against real `decode()`. **Honest arm accounting (round-2 breadth):** at THIS gate only `opData`/`opAck` — the two arms with no `readCString`/`readOptions` on their path — produce real oracle-compared witnesses. The other three arms (`opRrq/opWrq`, `opError`, `opOack`) CONSTRUCT (A1/A3 land the constructor; no more macro error / void twin) but their surrounding walks stay `sxUnknown` pending Track B (B4 for the cstring scans, B5 for the chained mode scan, B6 for options) — their oracle coverage lands with B7. "All five arms" as a *witnessed* claim is a Track-B deliverable; Track A's claim is "all five arms construct, two prove end-to-end" | — | Chapulin suite green incl. oracle checks on opData/opAck, against the 0.4.0 release; the three deferred arms pinned as classified `sxUnknown` (not crashes) |

**Exit gate A:** A6 observed green. Release 0.4.0. Checked non-dependencies
(round-1 + round-2): CR-2c's `seq[Object]` witness-reader gap does NOT gate
A6 (readers run on formal params only; `TftpPacket` is internal/return) —
and the SIBLING gap, `seq[(string,string)]` as a FORMAL PARAMETER (blocks
`t_symex_uri`/`t_symex.nim` from passing `negotiateServerOptions`/
`validateAndParseOack` to `symexFind` directly), also remains OPEN and
OUT of round-6 scope: A1's `iekVariantLit` work does not touch witness
readers, despite both involving `seq[(string,string)]`.

### Track B — accumulating scans (ADR-0028; release 0.5.0 at gate; starts after 0.4.0)

| Slice | Content | Ver | Done when |
|---|---|---|---|
| B0 | **LANDED (walker v70, hotfix 0.3.4).** Fixed BOTH scan-lift soundness gaps: (round-1) any-int-bound acceptance → only a bound syntactically the scanned string's own `.len` is lifted, plus a guarded entry-read probe so a negative start deposits the real IndexDefect fork; (round-2 depth) the closed form ran UNCONDITIONALLY — a zero-iteration loop (entry index past the bound) had its index clamped to `bound` where real Nim leaves it untouched (the chained composition hit this: a second scan seeded at `s.len+1` was silently reset) — the whole form is now guarded by loop entry. **Recorded decline:** a bound via a LOCAL alias (`let n = s.len; while i < n`) is no longer lifted (pre-B0 it was, unsoundly in general) — it k-unrolls honestly; re-lifting the provably-clean alias is a possible future recognizer, not a bug | SW | DONE: 6 pins in `tsymex_r6_b0_scanlift_bound` green (both false-sxUnsat shapes → sxRaised; canonical shape proves; zero-iteration index preserved); q1 13/13, r1b 19/19 green |
| B1 | **LANDED (walker v78).** The parse-time signal IS the recognizer — `collectStringBackedByteSeqParams` (`dsl_parser.nim`) is a NimNode pre-pass invoked from `parseProc*` right after param classification and before the body walk, populating `ParseCtx.stringBackedParams` by sharing `tryMatchScanIdiomShape` (extracted from `tryRecognizeScanIdiom`'s own guard/body structural check, now receiver/literal-type-agnostic so BOTH the itString recognizer and the itSeq[byte] classifier consult the identical predicate and can never diverge) against every `seq[byte]` formal param, minus any with a syntactic mutation site (`data[i] = x` or `.add`/`.del`/`.insert`, `scanShapeReceiverMutated` — array fallback). The parser consults the set for slice/index/`.len` dispatch (`data[a..b]` → `iekStrSubstr`; `data[i]` → `iekStrAt`; `data.len`/`len(data)` → `iekStrLen`); the two DUPLICATE parser sites each for slice/index (bracket-expr `nnkBracketExpr` vs call-form `` `[]`(data, idx) ``) and `.len` (`nnkDotExpr` vs call-form `len`/`card`) collapsed into one shared helper each (`parseSeqBracketAccess`/`parseSeqLenAccess`) so they cannot diverge. New `IRParam.isStringBacked` field (the `isVar` idiom) threads the choice to `allocateSym`, which allocates via the itString machinery (ADR-0006 byte-range) plus the itSeq arm's own `[0,1024]` length ceiling (preserved explicitly — the plain `of itString:` arm carries no such cap). **Walker totality backstops:** `isIndex`'s walker arm (was a hard `doAssert arrSV.kind == svArray`) and `iekSeqLen`'s `lower` arm (was a bare `raise ValueError`) both gain an `svString` case routing through the SAME OOB-probe/read logic `iekStrAt`/`iekStrLen` use (SND-4 mirror) — this is what makes `data[i]`/`data.len` WORK, not merely not crash, through a call-chain hop whose own parse never routed the dispatch (e.g. a LOCAL bound from a string-backed slice, still declared `seq[byte]`) — plus a classified decline (`feUnsupportedExprKind` via the existing `SymexClassifiedDegradeError` carrier) for any other kind, carrying a parse-time-captured `loc` (new `IRStmt.isIndex.ixLoc`/`IRExpr.iekSeqLen.lenLoc` fields, populated via `siteLoc` at the two shared-helper call sites) rendered verbatim at walk time. `collectIntOffsetParams` (ADR-0027 leg) — not present in the codebase under that name; the existing IR-level `itInt` range-promotion in `runSymexImpl` was left untouched, per the RFC's "do not move it" instruction. Empirically verified (git-stash bisection): a plain `seq[byte]` slice/`.len` already worked fine pre-B1 (M1's existing array machinery) — the live crash/wrong-verdict gap is specifically the REPRESENTATION MISMATCH window (parser routes string-backed IR, walker doesn't yet understand `svString`), reproduced by reverting only the walker backstops against the landed parser/allocator changes (B1-1/B1-2/B1-3 flip from real verdicts to `sxUnknown`) | SW | `tests/tsymex_r6_b1_stringbacked.nim` 7/7 (opData-style `data[4 .. ^1]` slice + derived-local `.len`/`[]` backstop pin, `data.len` parser-dispatch pin, unguarded-slice IndexDefect-found pin, mutation-fallback pin cross-checked against a no-loop ground truth, no-consuming-loop regression pin, version floor); 19-file regression sweep (new file + A0–A4, B0, q1_scanlift, r1b_shortcircuit_oob, CR-2 cachekey, TOT-1, every seq/index/len/slice/string-named test) 18/19 green, the 1 red (`tsymex_phase15_S3_strindex` "s.high == 4") confirmed PRE-EXISTING via the same git-stash bisection (identical failure on unmodified baseline) |
| B2 | **LANDED (walker v80; v79 + a same-day control-loop-review rider fixing `byte`-alias recognition and adding the standing-DoD `typeKind` guard).** Int-family WIDTH-CONVERSION modeling — WIDENING only (`iekConvIntWidth`, zero/sign-extend keyed on the SOURCE value's signedness — `IRType.signed` carries the bit; `uint8→int32` zero-extends, round-2 depth). Replaces the withdrawn bitwise→LIA leg; header math rides plain `binBV` at widened widths; CR-1a's `svIntToBV` bridge untouched. **Scope locks (round-2):** NARROWING (`uint8(x)` truncation) and same-width signedness reinterpretation are CLASSIFIED DECLINES — the pre-B2 identity pass-through was silently unsound for them (value unmasked, stale signed flag steering signed/unsigned compares) and no truncate primitive exists; recorded non-goals, encode-path only in the corpus. `nnkHiddenStdConv` stays a blind pass-through (out of scope — its literal types pre-unification would misdirect a width arm; zero corpus need). New-IR fan-out landed across 5 files (`types.nim`; `dsl_parser.nim`'s `nnkConv` parse arm + `emitExpr`/`rhsHasInlineDefectFork`; `abstraction.nim`'s `tryEvalInterval`/`collectVarRefs`; `canonicalize.nim`'s cache-key arm; `runtime.nim`'s `probeProto`/`lower` — the exhaustive-switch tax, budgeted not hidden); `zeroExtend`/`signExtend` Z3 primitives already bound | SW | `uint16(b) shl 8` (call syntax — the consumer's literal spelling, `protocol.nim:93`) AND `b.uint16 shl 8` prove at 16 bits; a `probeProto` arm returns the WIDENED proto (literal-sibling pin — the exact `iekConvFloatToInt` stale-proto crash precedent); narrowing + reinterpret decline pins; sello r5 pin set green; A5's generic/untyped and-or shapes pinned as cross-track regression |
| B3 | **LANDED (walker v81).** `tryRecognizeScanPairIdiom`/`tryMatchScanPairIdiomShape` (`dsl_parser.nim`) — a NEW sibling of Q1/B0's `tryRecognizeScanIdiom`, not a widening of it (ADR-0028's "family of independently-narrow sibling recognizers" design): recognizes the OTHER canonical scan idiom chapulin's twins use, early-return-on-match (`while i < s.len: (if s[i] == lit: return <expr>); inc i`, trailing raise on fallthrough) rather than Q1's skip-while-and-clamp shape — mutually exclusive by construction (guard shape / exact 2-statement body), so B3 and a future B4 accumulating-shape sibling can never cross-fire on the same loop. Lowers to the SAME `iekStrFind` 3-arg closed form (symbolic start) Q1/B0 use, reusing B0's not-found/OOB split VERBATIM: the whole form is guarded by loop entry (B0's zero-iteration-preserved discipline), an entry-read probe deposits the real IndexDefect fork a negative start raises, and only a bound syntactically the scanned string's own `.len` is accepted. The found branch RE-PARSES the SUT's own `return <expr>` against an `i := p` rebinding (not a syntactic substitution), so a `return (i, i+1)`-shaped result correctly reports the FOUND position; the not-found branch sets `i := bound` and falls through to whatever follows the loop (typically a `raise`) unaffected — no cross-statement recognition needed, so no new IR kind and no new classified-decline site (reuses `iekStrFind`/`iekStrAt` verbatim). Same two type gates as Q1 (itString receiver, char-literal delimiter); deliberately NOT widened to a `seq[byte]` string-backed receiver this slice, per B1's own scope note. `tsymex_retest_c6_tuple_chain`'s `destructurePair` SUT migrated from the dead `seq[int]`+`mod 256` workaround spelling (ADR-0028 Leg 1) to `string`, the only receiver type the scan-lift family has ever recognized. **Standing-DoD clause (d) catch (own regression sweep, not left latent):** the shape's plain `<` guard (not and-shaped, unlike Q1's) also matches an iterator's own `while i < n: yield ...; inc i`, and the first-pass `classifyType` call on that guard's operands hit the exact "node has no type" crash class A5 fixed (surfaced by `tsymex_phase15_N3_scan_boundary`'s `iterLambdaReturn`, an unrelated file exercising the SAME call site during macro expansion for any symex-using module) — fixed by reordering the purely-structural body-shape checks before any `classifyType` call plus the `typeKind != ntyNone` guard itself at all three new call sites | SW | `tsymex_retest_c6_tuple_chain`'s `destructurePair` pin upgrades from `beBudgetExhausted` to a REAL `sxUnsat` PROOF (no `IndexDefect` reachable at all, the strongest possible verdict) — DONE. New `tests/tsymex_r6_b3_scanpair.nim` 7/7 (symbolic-start SAT + start-honored UNSAT companion, not-found `ScanError` fork reachable, negative-start OOB `IndexDefect` reachable, non-`.len`-bound trip-wire stays `sxUnknown`, accumulating-shape trip-wire stays `sxUnknown`, version floor); q1_scanlift 13/13 and b0_scanlift_bound 6/6 stay green |
| B4 | Accumulating-string variant (`readCString` family): payload = `iekStrSubstr(s, offset, terminatorIx − 1)` (inclusive-hi pinned) | SW | Solo scan proves SAT/UNSAT with witness cross-check. Then: interim INT-1 (chapulin vs git HEAD) |
| B5 | Chained composition (catalog #6): second scan's offset = first's result | — | Chained repro proves; pin retires the #6 finding |
| B6 | Option-region membership (the `readOptions` pair-loop): region ∈ `((nonzero)* "\0")*` — **STAR inner segments, not plus (round-2 depth):** the real `readCString` returns empty strings freely and `readOptions` accepts mid-region empty keys and all empty values, and the canonical double-NUL terminator is itself an empty segment; `(nonzero)+` would fail to certify exactly the inputs a property search generates. Membership is the LOOP-SAFETY invariant with PER-PREFIX scoping — a non-member region (truncated tail) falls back to the modeled ScanError raise arm (ADR-0024 class) / k-unroll degrade, never all-or-nothing. Pair values fresh-unconstrained. dt-bounded calibration | SW | Option-arm defect proof green incl. empty-key/value and double-NUL-terminator pins; truncated-region fallback pin; a divergent query becomes a bounded pin + bisect per doctrine |
| B7 | Chapulin migration — expanded DoD (round-2 breadth): twins to `seq[byte]` (drop `atByte`'s mask + the `seq[int]` typing across all four helper twins); UNIFY the three separately-scoped decode twins (`decodeFixedArmsTwin`/`decodeFixedArmsErrorTwin`/`decodeOptionArmTwin` — split precisely to dodge gaps B3–B6 close) into one natural twin; re-derive their 9 green assertions; extend the differential oracle to the unified twin (the deferred 3 arms from A6); re-probe `t_symex_checksum` (const-fold action recorded at v69, still outstanding). Passing the REAL `protocol.decode` to `symexFind` directly is a recorded STRETCH GOAL, not gated — the twin remains the vehicle | — | The natural unified decode twin proves in chapulin's suite against 0.5.0; oracle covers all five arms; checksum re-probe recorded in chapulin's findings doc |

**Exit gate B (committed):** the fully-natural single-param decode proof —
widened-BV header math, closed-form scans, and the option-region membership
on one string-backed param. Release 0.5.0.

**Recorded declines (boundaries, not apologies):** byte-wise `xor`;
bitwise shapes that would push a BV value into a Sequence-theory bound
(ADR-0027 discipline); cross-iteration-arithmetic loops outside the
recognized scan/pair-region shapes (checksums); string-backed candidates
with mutation sites (array fallback); discriminants past the cardinality
budget; NARROWING and same-width-reinterpret int conversions (B2 —
upgraded from silent identity pass-through to classified); scan bounds
via a local `len` alias (B0 — k-unrolls honestly); parse-time tag-set
narrowing does NOT cross proc boundaries (a helper-proc-per-arm refactor
of a consumer's `case` gets the declared-arm-count fork cost, absorbed
by the budget for ≤8-arm enums — an architectural boundary of parse-time
narrowing vs walk-time inlining, recorded so the budget cap isn't
mistaken for a diagnostic). All classified, all with TOT-1 fixtures per
the standing DoD.

**Consumer actions owed beyond chapulin (round-2 breadth):** sello's
three v69 fixes make its recorded workarounds removable — plain-int
re-encoded recode lemmas (width protos), `var`-out-param signatures
(svTuple returns), and the split mask lemmas (`-int32(b)` proves) — and
A0 closes the `low(int32)`/`high` fault sello's own bounded-mask probe
surfaced. A "sello action" migration note mirrors chapulin's B7
treatment: re-probe `symex_recode.nim`/`symex_mask.nim` natural forms at
the 0.3.4+ pin, drop the workarounds that prove.

**Risks accepted (grill-me + round-1 review, 2026-08-08):** B6's
regex-star × find/substr composition is the round's one uncalibrated
query family (dt-bounded doctrine budgeted); fork-per-tag cost is
budget-bounded, not analysis-bounded — a wide-enum consumer hitting the
cap gets an honest `sxUnknown` and possibly a budget-tuning conversation;
the hard A-before-B ordering trades wall-clock parallelism for SW-literal
and INT-1-bisection sanity.
