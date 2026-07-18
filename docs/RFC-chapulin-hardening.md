# RFC — proptest consumer-hardening (from chapulin v1/v2 harness)

> Empirically-sourced hardening RFC. Every item was surfaced building chapulin's
> symex + fuzz + soak verification harnesses against proptest, and **re-verified
> at HEAD `99fa2db`** before entering this doc — healed findings are dropped, live
> ones carry their reproduced symptom + locus. Source:
> `/mnt/c/Users/corey/projects/chapulin/docs/proptest-findings.md`.

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

> **Totality + soundness of the failure mode.** Any construct proptest doesn't
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

**Crash-doctrine boundary (round-1, do not violate).** proptest deliberately does
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
| Q1 | dependent bounded loops (defect-target search) — **spike** | Solver | med | L | — | — | SW? |
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
  - **Recommendation:** proptest's build docs must require the *walker's own
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

- **Q1 — dependent bounded loops** · LIVE (`sxUnknown`, empty errors; independent
  of `maxLoopUnwind`/`maxCallDepth`). **Only bites a defect/universal target**
  (`tIndexError()`), not a `tLabel` reachability search. **Marked a timeboxed
  research spike (round-2):** Q1 names *no* candidate encoding, and its DoD's own
  degrade-rule means every candidate may be `dt-bounded`-rejected, closing the slice
  as *"confirmed no viable sound-and-fast encoding"* rather than a shipped feature.
  Run it as a find-an-encoding-or-report-back gate outside the normal sequencing
  promise, so it doesn't implicitly commit a capability the solver may not deliver.
  Ver-bump only *if* a viable encoding lands. Size L.
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
`symexWalkerVersion` independently, run chapulin's smoke suite against proptest
`main` **after each SW-bumping slice**, not once at the end — otherwise a red
chapulin harness at the final ~13-version jump has no bisection story. This is cheap
given `dt-bounded.sh` discipline is already per-slice. On the final landing, bump
chapulin's pin and delete/revert each named workaround, confirming the harness stays
green: `atByte` mask chokepoint, hand-unrolled loops, `p = p & x` substitution,
`parseInt`-for-`parseBiggestInt` (M2/B4), nested-if depth bound, `encodeByteSeqIR`
helper, and the others in `proptest-findings.md`'s per-finding "Workaround:" lines.
- **Rollback clause (round-2):** if a per-slice chapulin smoke run goes red, the
  offending slice's SW bump is revertable independently (each slice's `Ver` scope is
  narrow — verify no later slice's cache-key/witness format already depends on it
  before promising this). Log any workaround that *can't* yet be removed with the
  slice that would unblock it.
- **Completeness caveat:** INT-1's workaround list lives in an external repo
  (`/mnt/c/…/chapulin/docs/proptest-findings.md`) not checked into proptest — hash-pin
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
