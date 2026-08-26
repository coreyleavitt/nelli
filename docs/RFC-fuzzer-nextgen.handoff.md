# RFC — next-generation structure-aware hybrid fuzzer — handoff

- **Stage:** 3 (implementation) — architecture rounds 1, 2 & 3 all DONE; **no open forks/escalations.** Grinding slices via `/loop`.   •   **Done:** E0 (corpus-sync spike — verdict recorded). **Next:** E1.
- **Resume (stage 3):** `/loop implement the next unimplemented RFC slice with /tdd, following the standing rules; after each slice report one progress line; stop when every slice is implemented`
- **E0 decision record:** `docs/RFC-fuzzer-nextgen.E0-findings.md` (throwaway spike lives in `scratchpad/e0_corpus_sync/`).
- **Safe to `/compact`** at any slice boundary. After compact, re-read this doc + MEMORY.md before continuing.

### Round 3 — 4-lens team in; all clear-best fixes APPLIED, no forks
User asked for an extra hardening round beyond the mandatory two. Two anchors:
**(1) orchestrator execution model made explicit** — one single-threaded
completion loop; completion-oriented `Worker` seam (no thread-per-worker); the
Z3 bridge, fresh-spawn re-verify, and `reproRate` sampling all run OFF the hot
dispatch path on bounded slot budgets like shrink; **read-before-redispatch** is
a named+pinned per-worker invariant (the shm generation word is a single check,
not a seqlock — safety rests on this). **(2) Appendix C admission surface
corrected** — three code defects: `AdmitResult` baked async-updating fields
(`reproRate`/`divergentReproduction`) into a one-shot return (→ read by
`FindingId` handle); `Observation` lacked the `ChoiceSeq` re-verify must replay
(→ `admit(input, candidate)`); `CrashInfo` was illegal Nim (common field after
`case`). Also: **`Pool`→`Orchestrator`** (type name; prose uses both); **`wouldAdmit`→`score`**.
Applied too: dedup indexes kind→findings-observing-it-as-primary-OR-variant
(closes a second `divergentReproduction` fragmentation path); macro adds a
best-effort **impurity denylist** on captured initializers (env-impurity residual
= stated limitation — the one Critical: scope-check ≠ purity-check); **E0 gains**
Windows-safe compaction rename + shrinker-vs-shrinker race + corpus-format
version tag; **G6 algebra closed + `∘` directed + `branching` descriptor** for
enumerable-flatMap; steady-state **respawn-storm breaker** (E-cleanup); config
surface section; S1 owns shared `FrontierStats` (G3 consumes); shmProbe reset is
worker-internal (capability flag). **Slice re-cuts:** E3→**E3a/E3b** (E3b sized
after E0), G1→**G1a/G1b**, S5→**S5a/S5b** (S5b G2-gated), new **S6** (learned-state
checkpoint), E1 spike strengthened (real dispatch + generic case + E's 2nd
capability), E2a N=1-until-E2b coverage pin, Eci greppable capability-flag +
E4a Linux-testable seam, SW pre-flight adds commit-time re-check + claim marker.
Full per-lens detail in the four round-3 task transcripts.

### Round 2 — 4-lens team in; all clear-best fixes APPLIED, no forks
**Anchor decision:** topology resolved to **centralized orchestrator** (Pool =
one process owning the single in-memory frontier/corpus/dedup/scheduler + the
one Z3 bridge; workers are dumb execution seams; admission single-writer).
Supersedes round-1's contradictory "AFL `-M`/`-S`" gloss (federated `-M`/`-S` =
out-of-scope cross-node #112). Restores fidelity to fork-2's own "one shared
corpus" words → clear-best, not an escalation.
Also applied: bounded-async **reproRate** N-of-M sampler (was undefined); first
**report immutable** + re-verify kind-mismatch → `divergentReproduction` (dedup
fragmentation fix); **E0 retargeted** — under single-writer orchestrator the
real race is orchestrator-vs-shrinker + orchestrator-vs-forAll-reader on the
**shared per-testId db file**, plus mandatory **delta-log compaction** design;
**macro split into two contracts** (syntactic AST for G / reconstructible
constructor for E) with **compile-time free-identifier check**, **argv
call-site-ID dispatch** (not env var), isolated-proc reconstruction, bootstrap
circuit-breaker; **shm = push/copy double-buffered** w/ atomic generation word
(not zero-copy directly-mapped — infeasible for clang counters); **`fork()`
gated to single-threaded builds**, CRIU named; **yield metric typed by walker
construct-kind** (+ superseded / intended-vs-unrelated buckets); **G6 adds
`predicated`** (filter) + chain-composition algebra; **optimistic solving
bounded** (maxAttempts + Z3 timeout); **forAll gets crash isolation** via
in-process Worker (U0); **wouldAdmit** name; ablation-harness cadence/tolerance/
per-platform policy; SW-bump **pre-flight mechanical check**; campaign
observability surface (S5); resource-leak cleanup (E-cleanup); seed provenance.
**New/re-cut slices:** E2→**E2a/E2b**, **E-cleanup**, **U0**, **S5**, **G3b**.
Full per-lens detail in the four round-2 task transcripts.
- **Escalation RESOLVED (opaque-closure boundary):** Corey — pre-v1, breaking
  changes fine if improvements; best-in-class whatever it ends up being. Design
  call taken: **the concolic-capable entry is a `macro` that captures the
  property (and strategy-construction) expression at the call site.** One
  decision solves both tracks — Track G gets the property AST for named procs
  AND inline literals (only opaque closure *values* threaded through
  indirection are sfNotApplicable); Track E gets worker reconstruction with NO
  new user-facing API (same macro emits an env-var-gated worker-mode entry
  that re-runs captured construction). Folded into §Open items (RESOLVED),
  Track G/E inline notes, E1 (now macro entry, size S→M), E4a, ADR D1/D3,
  Risks. Supersedes the grill's "symexFind API untouched" framing.

### Round 1 — all four lenses in; clear-best fixes APPLIED to the RFC
Applied: Worker/Pool seam split + AFL -M/-S topology; coverage via existing
CoverageProbe (shmProbe); typed CrashInfo + vResourceExceeded; §0 precondition
(re-verify gates admission not reporting; fresh obs authoritative); parked-
snapshot-captured-once; db.nim RMW race named + E0 spikes real backend w/ 3
candidate serializations + shared crash-dedup; live-mapped-shm vs signal-dump
+ nelli_cov.c per-input reset as E2 deliverable; clang-cl/coverage-blind
Windows fallback; slices re-cut (Eci Windows-CI-toolchain; E4→E4a/b/c; E3 test
split structural-RED vs numeric-ablation; E5 Windows persistent-mode caveat);
Track G edge-selection (frontier selects entry, walker identifies branch),
additive-mode corrected to threaded-through-dispatch, transparency descriptor
= G6, G-cmp broadened to bytes/string + identity-flow boundary; G3→S1 dep;
S4 governs persisted eviction; Track U snapshot policy + peek/admit split;
non-goals (no trajectory-reproducible parallel campaigns; processes-not-
threads); G/U1 SW mutual serialization; ADR D1–D4 updated; hybrid draft marked
SUPERSEDED. Full per-lens detail in the four task transcripts.
- **RFC:** `docs/RFC-fuzzer-nextgen.md`. **ADR:** claims **ADR-0031**
  (0030 taken by parser-normalization). **Umbrella issue #158 filed.**
  #151 commented with the fold-in disposition (worker-pool + byte-havoc
  → #158; hygiene items stay in #151).

## What this RFC is
Next-gen fuzzer from the 2026-08-14 `/grill-me ideal:` session. Four tracks:
- **E (Executor)** — portable persistent worker pool (Windows first-class),
  crash isolation, shm coverage, freshness by recycling + pristine
  re-verification; POSIX fork = recycling policy. PREREQUISITE for all.
- **G (Guidance)** — choice-space concolic bridge (new walker mode,
  draws-as-symbols, aggressive concretization, models ARE choice
  sequences) + IR-level cmp-correspondence (typed RedQueen) + auto-dict.
- **S (Scheduling)** — Entropic energy, operator bandit, havoc stacking,
  continuous culling.
- **U (Unification)** — one coverage frontier for fuzz + forAll; forAll
  gains replay-only fuzz-corpus reads; byte-mode → interop-only.
Hard order E→G; S/U interleave after E. Evaluation = committed ablation
harness (per-track exit gates) + informal scoreboard + one-time byte
comparison at E exit.

### E0 outcome (2026-08-25) — decision in `docs/RFC-fuzzer-nextgen.E0-findings.md`
Spike empirically confirmed the **append-only delta log**: 87% baseline lost-update
loss vs 0% for the log; log out-scales an advisory `flock` RMW ~70–115× and does not
degrade under contention. Corpus **split** to `<key>.corpus.log`; `.bin` writes funnel
**single-writer through the orchestrator** (kills shrinker-vs-shrinker); compaction via
**generation-file + head-pointer + reader-lease** swap (POSIX-safe by test, Windows-safe
by construction); versioned log header (refuse-on-newer / migrate-on-older; legacy
single-file corpus externalized at U3). Two findings fold forward: **F-1** orchestrator
holds ONE long-lived DB handle (concurrent constructors race on tmp-sweep); **F-2** log
also sidesteps the backend's whole-file-rewrite O(n²) cost. **E3b now sized M.** Spike
code (throwaway, untracked) in `scratchpad/e0_corpus_sync/`.

## Slices (first-pass; round-3 re-cuts folded in)
- [x] **E0 corpus-sync SPIKE — DONE** (delta log selected; 5 mandate items resolved) ·
  E1 Orchestrator/Worker seams + macro entry (AST spike = real dispatch +
  generic case; E's reconstruction capability spiked too) ·
  E2a POSIX worker+framed pipe+crash-isolation (N=1 coverage until E2b) ·
  E2b shm+nelli_cov.c reset · **E3a** freshness machinery (E0-indep) ·
  **E3b** persistence discipline per E0 (size TBD-at-E0) ·
  E-cleanup resource lifecycle + steady-state respawn-storm breaker ·
  Eci Windows toolchain (CI+local; emits greppable capability flag) ·
  E4a/E4b/E4c Windows worker (E4a: platform glue behind Linux-testable seam) ·
  E5 external tier onto seams
- [ ] **G1a** thread mode through dispatch (mechanical) · **G1b**
  draw-symbolication+bounded trace · G2 branch-flip solve+materialize ·
  G3 orchestration (Z3 bridge off hot path) · G4 cmp instrumentation ·
  G5 I2S+auto-dict · G6 transparency descriptor + closed/directed algebra +
  `branching` (or fold into G1's ADR)
- [ ] G3b wire real Entropic energy post-S1 (conditional)
- [ ] S1 Entropic energy (owns shared FrontierStats) · S2 operator bandit ·
  S3 havoc+interesting-values · S4 continuous culling · **S5a** observability
  (E-tier) · **S5b** concolic/provenance breakdown (G2-gated) ·
  **S6** learned-state checkpoint/resume
- [ ] U0 forAll through in-process Worker (crash isolation) ·
  U1 unify coverage model, score/admit split (maybe SW bump) ·
  U2 forAll corpus reads · U3 byte-mode demotion (+corpus-format migration)

## Open forks — ALL THREE RESOLVED 2026-08-14
1. **Umbrella #158 filed**; #151 execution-model items fold in, hygiene
   items stay (commented on #151).
2. **Parallel campaign IS v1** (Corey: "do it right from the start but
   prove it with a spike"). Single-node many-workers/one-shared-corpus;
   E0 spike de-risks the sync model before E2/E3 commit. Cross-node stays
   out (#112).
3. **Concolic yield: capability + measured-metric + optimistic-solving
   fallback, NOT a percentage bar.** Optimistic solving (QSYM) is
   soundness-free here because Track E re-verifies concretely; yield metric
   emits a failure taxonomy that becomes the walker-widening work-list;
   fragment widens on investment shared with symexFind. See RFC §Track G
   "Yield" subsection + ADR-0031 D3.

## Key decisions (this session — all grill-resolved, in RFC §Resolved forks)
Scope=(a1) no DBI; Windows first-class; persistent worker pool w/
re-verification; choice-space concolic (value-space+inversion rejected);
two front doors one engine; committed ablation harness. Supersedes the
earlier "#124 Shape A next" recommendation.

## Ground-truth anchors verified in code (RFC §Ground truth)
in-process no isolation (fuzz.nim:310-335, engine.nim:54-60); external
POSIX-only (fuzz.nim:858); spawn-per-input (fuzz.nim:871-935); admission-
only coverage (coverage.nim:357-370, D4); no cmp guidance; good mutation
core (fuzzir.nim); two coverage worlds one data world (engine.nim:118-153
scalar vs bucketed frontier, D10); no symex bridge; corpus channel exists
(db.nim, F1).

## Review ledger (stage 4) — not started
