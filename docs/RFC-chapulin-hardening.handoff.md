# RFC — chapulin consumer-hardening — handoff

- **Stage:** 3 (tdd grind) — IN PROGRESS   •   Architect rounds 1&2 done; fork resolved
- **Resume:**
  `/loop implement the next unimplemented RFC slice with /tdd, following the standing
  rules; after each slice report one progress line; stop when every slice is done`.

## Stage-3 grind ledger
Slices land serially (each SW bump serialized against a live base). Sweep = all
`tsymex_*.nim` × {c,cpp} via `scripts/dt-bounded.sh`. Next up: **SND-2**.

| # | Slice | Commit | walker ver | Sweep | Notes |
|---|-------|--------|-----------|-------|-------|
| 1 | SND-1 | `84668ab` | 37→38 | 388/388 ✓ | isUnsupported taints Path.uncertain. Fallout: added no-op parse arm for assert-scaffolding `nnkConstSection`/`nnkBindStmt`/`nnkMixinStmt` in dsl_parser (else every assert degraded). Legit soundness corrections: a3_closure_iterators T5/T6 sxSat→sxUnknown (accidentally-correct false-sxSat SND-1 closes). New test uses `>=`-floor pin idiom; 7 legacy `==` pins bumped to "38". |
| 2 | SND-1b | `bc2c8d9` | 38→39 | 390/390 ✓ | `applyClosureGround` skips `assertArm` for uncertain closure-body sub-paths (both return channels), pushes new `ceClosureBodyUncertain` (sevError) → existing `closureForcedUnknown` whole-run degrade fires. ADR-0018 in SYMEX_PLAN. Fixed fork-registry comment (descentBase = 2nd raw `Path(`). **One-time SW pin-idiom migration executed**: canonical CR2_cachekey stays `== "39"`; 6 incidental pins → `>=`-floor. Strong-form test checks error-kind, not just verdict. Subagent died on API error post-sweep; control loop verified + committed. |

## Round-2 architecture review — applied (2026-07-12)
Second 4-agent team (depth/breadth/design/feasibility), all grounded in the code.
Round 2 CONFIRMED round-1's core claims (SND-1 chokepoints, ADR-0012 D2 precedence,
call-cache uncertain-gate, 12-switch count) and surfaced new material work:
- **SND-1b (NEW, CRIT):** closure ground-axiom path (`applyClosureGround`,
  runtime.nim:6244-6531) bypasses `Path.uncertain` — folds closure-body returns into
  GLOBAL `currentClosureCallAxioms` (drained into every solve) with no uncertain-gate.
  SND-1's fix doesn't reach it. New slice; reuse `closureForcedUnknown` whole-run
  degrade. Fork-registry comment (4409-4454) stale re raw `Path(` at 6381.
- **CR-2c (NEW):** third macro-`error()` class — `emitTyAndReader` witness-reader
  codegen (symex.nim:697/708/716). §0 widened to THREE site classes.
- **SND-2 cache-key collision (CRIT catch):** blanket "render isAssume==isAssert"
  would collide `symexCacheKey` (canonicalize.nim:684) → silent wrong answer. Needs
  distinct tag `Am:` vs `At:` + test. Also `collectAssertRanges` (abstraction.nim:324)
  has `else: discard` silently dropping assume range facts — DoD'd.
- **CR-2b crash-risk closed:** `tUninterp("__unsupported_")` → uncaught ValueError in
  allocateSym (only `__ownership:` guarded). Needs new prefix guard OR capForcedUnknown
  + explicit ctx-threading decision.
- **CR-1c open item RESOLVED:** chapulin config has NO `-d:danger`/`--panics:on`
  (checked nim.cfg/chapulin.nimble) → catch approach viable. Depth nuance: `--panics:on`
  hits only Defect; CR-1a/b (ValueError/KeyError=CatchableError) unaffected. HARD RULE:
  `try/except` never `try/finally` (commit b7258f7 = C-backend-only silent sxUnsat);
  regression must diff both backends.
- **TOT-1 rescoped generative→table-driven:** all symex entry points need `fn: typed`;
  fuzz.nim generates values not AST. Fixed hand-authored §0-invariant corpus. (3 of 4
  agents independently proved this.)
- **Design:** 18 near-identical exception carriers exist; CR-1c/CR-2b use ONE generic
  `SymexClassifiedDegradeError{kind}`, name the 18 as incremental debt.
- **Sizing/process:** P2→P2a(value)+P2b(ref,L; variant excluded); Q1=timeboxed spike
  (may have no viable encoding); INT-1 recurring per-SW-slice + rollback clause;
  SYMEX_PLAN.md ADR-landing + stale-status obligation; `(t)` RED-state instruction;
  M4 `&=` is a type-classify branch not a set edit (binopForInfix has no `&`).

## RESOLVED FORK (Corey 2026-07-12) — SW version-pin idiom
**Synthesis chosen:** canonical `tsymex_phase15_CR2_cachekey.nim` pin stays `==`
(conscious-bump gate per [[symex-version-bump-cr2]]); incidental feature-test pins
convert to tolerant `>=`-floor (`check parseInt(symexWalkerVersion) >= N`). Kills ~200
pin touches + the parallel-worktree literal collision, keeps one loud drift gate.
Serialize-against-live-base rule still applies to the canonical `==` pin. Now recorded
in the RFC's §Version-pin discipline as a settled decision, not a fork.

## Round-1 architecture review — applied (2026-07-12)
4-agent team (depth/breadth/design/feasibility), all grounded in the actual code.
No genuine forks surfaced — every finding had a goal-determined best answer;
applied all directly. Corey's mega-RFC scope preserved (Clusters 6-7 annotated a
**decoupled track**, not split out). Material changes now in the RFC:
- **SND-1 re-scoped L→S:** mechanism already exists (`Path.uncertain`,
  runtime.nim:376-378, consumed at both `w.found` producers). Fix = taint the
  `isUnsupported` arm; **no ADR-0012 D2 amendment** (only a new taint producer).
  Added Class-A/B taxonomy (Class-A already immune via `capForcedUnknown`).
- **CR-1 is NOT a sweep:** split CR-1a (#3 fixed at abstraction/BV-ban locus,
  matches [[symex-abstraction-bv-ban-toz3int]]), CR-1b (#4 tail-return lowering),
  CR-1c (one narrow last-resort catch, distinct `weInternalWalkerFault` kind).
  Respects the documented "ValueError/AssertionDefect must surface" crash-doctrine.
- **CR-2 split by error() class:** CR-2a expression-position (dep SND-1), CR-2b
  parameter-type-position (uses already-sound `capForcedUnknown`, no SND-1 dep).
- **New slices:** TOT-1 (generative totality harness — operationalises §0),
  INT-1 (chapulin workaround-removal exit gate).
- **Version-pin discipline** now a cross-cutting section (TWO consts:
  `symexWalkerVersion` + `renderAsChoicesVersion`); per-slice `Ver` column added.
- Corrections: M1 dep on CR-1 dropped (class-C, symex.nim); M3 de-risked S
  (nim-z3 `lastIndexOf`); SND-2 = 12 exhaustive switches (+ scan.nim found[0] trap
  test, + keep assert raise-forks steps 1/2/4, drop only forkDefect step 3);
  Q2 re-scope-after-SND-2.
- **Open verification for round 2 / CR-1c:** confirm chapulin build flags — under
  `-d:danger`/`--panics:on` a failed doAssert is uncatchable; CR-1c would then need
  raise-guards, not a catch.
- **Verified finding set:** consolidated in session scratch `verify_results.md`
  (4 agents, all findings re-checked @ 99fa2db). RFC reflects it.
- **★ Key architectural insight for the architect rounds:** hard dependency
  **SND-1 ≺ CR-1/CR-2** — the crash-degrade work must NOT ship before the
  mkUnsupported-statement soundness fix, else it trades visible crashes for silent
  false-`sxSat` (worse under Invariant 3). SND-1 amends ADR-0012 D2 precedence.
- **Biggest scope changes from verification:** #5/#11/#7-symptom/pred/succ/`..<`
  HEALED (dropped); #3/#9 narrowed; SH1 does-not-repro (deferred); **NEW CRIT
  soundness bug SND-1** found (silent mis-mutation → false sxSat, general).

## Scope decision (Corey, 2026-07-12)
**ONE mega-RFC covering ALL chapulin findings**, across every subsystem (symex
walker/parser/solver + fuzz + shrinker + coverage). Corey chose this over the
recommended "symex-RFC + route-the-rest" split. Mitigation for coherence: the
single doc is organized into **per-subsystem clusters** (Phase-15/16 cluster
style), each independently sliceable. Unifying thesis: *everything chapulin's
v1/v2 verification harness surfaced*, with the §0 "walker never crashes /
Invariant-3 totality" invariant as the marquee cross-cutting cluster.

Source findings: `/mnt/c/Users/corey/projects/chapulin/docs/proptest-findings.md`
(pinned at proptest `99fa2db` = current HEAD; `file:line` refs align).

## Prerequisite: verify-at-HEAD pass (IN PROGRESS)
Some findings are already HEALED by A7/A8/A9 (confirmed pre-fan-out: #7's
`toLowerAscii` symptom works now; #3 bitwise-plain-int doesn't repro in the
simple shape). Don't slice healed work. Four background verification agents
(sonnet, verify-only, no fixes) each re-check a cluster and return a
LIVE/HEALED/PARTIAL table with evidence + fix locus + size:
- **A** — §1 walker crashes: #3, #4, #5, #11. (Known: #4 KeyError = LIVE-CRASH.)
- **B** — §2 model gaps: #1 seq[byte] reader, #7 toLower/probeProto, #8 rfind,
  #10 string.add, parseBiggestInt, min/max.
- **C** — §3 parser (#2 tupleConstr, objConstr, seq-slice, pred) + §4 solver
  (#6 dependent loops, #9 loop+string-param, symexAssume==symexAssert).
- **D** — §5 fuzz/corpus/DB, §6 coverage, §7 shrinker Int128 compile bug.

## Confirmed-live so far (pre-verification spot-checks)
- **#4** implicit tail-return referencing a local → uncaught `KeyError` at
  `runtime.nim:2629` (`env[e.vname]`), native crash. **LIVE-CRASH.** Flagship of
  the §0 "walker never crashes" invariant.
- **#7** symptom HEALED (A9), but a real latent bug remains: `probeProto`
  (`runtime.nim:1763` `StrOpKinds - {...}` catch-all) returns `none` for the
  A7/A8/A9 string ops (`iekStrToLower/Upper`, `iekRadixFmt`, `iekRuneToStr`) —
  missing from its modeled subset. Masked by a lowering fallback today.

## Open forks (awaiting Corey)
- (none blocking — scope decided; drafting proceeds after verification)

## Key decisions (this session)
- Mega-RFC scope (above). • Verify-at-HEAD before drafting (drop healed findings).
- Non-symex findings STAY in this RFC (per mega-RFC choice) as their own clusters,
  rather than routing fuzz→FUZZ_PLAN.

## Review ledger (stage 4) — not started
