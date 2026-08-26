# RFC — next-generation structure-aware hybrid fuzzer — handoff

- **Stage:** 3 (implementation) — architecture rounds 1, 2 & 3 all DONE; **no open forks/escalations.** Grinding slices via `/loop`.   •   **Done:** E0 (corpus-sync spike — verdict recorded), E1 (Orchestrator/Worker seams + macro entry), E2a (POSIX persistent worker). **Next:** E2b (shm + `nelli_cov.c` reset) or E3a (freshness machinery, E0-independent).
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

### E1 stage-2 finding (walker-ingestion, verified in code 2026-08-25)
The AST proof-spike's RFC premise is partly wrong — corrected (clear-best, not a fork):
the symex walker ingests **lowered `IRStmt`** derived from a **typed proc symbol**
(`getImpl`→`parseProc`→`walk`, `smt/runtime.nim:5939`/`:8499`); its ONLY door is
`fn: typed` (`symexForAll` symex.nim:461, `symexFindAllWitnesses` :1627). There is **no
entry that ingests a raw captured AST**, and **no `wmFollowConcrete` mode exists yet**
(single symbolic mode; Track G adds concrete-follow later). Consequences for E1 stage 2:
(a) the `fuzz(...)` macro must capture the property as an **emittable typed proc symbol**,
not an untyped AST blob — that is the shape Track G's walker consumes; opaque closure
*values* that can't be so presented stay `sfNotApplicable` (already the RFC's rule).
(b) the spike targets the **real single-mode `walk`** with a bounded step budget, not a
nonexistent stub mode. (c) generics are fine — `instKeyFor` (dsl_parser.nim:5262) already
carries the bodyHash+typeSubst collision fix; a generic `Strategy[T]` flows via
`s.getTypeInst()`. Fold this correction into the RFC E1 text when stage 2 is briefed.

### E1 — DONE (commits 768e554, d0d58d9, 26b3a5f, fbe8322, b8e3aef, 50577a6)
- typed `CrashInfo` (matched on `kind`, `message` derived) + `Observation.crash`.
- `Worker[T]`/`Orchestrator[T]` seams; Worker is the load-bearing in-process seam,
  `ChoiceSeq` currency (generate happens inside `Worker.submit`); Orchestrator drives
  a single Worker + owns admission (opaque `admit(input, candidate): AdmitResult`).
- `fuzz(...)` call-site macro (`src/nelli/fuzzmacro.nim`): captures strategy+property
  construction; lifts inline props to named proc symbols (walker-ingestible);
  in-process worker-mode re-entry + call-site-id registry (`runWorkerReentry`);
  compile-time capture checks (free-identifier + impurity denylist).
- C7 freeze-guard (`tests/tfuzzmacro_astspike.nim`): PROVEN that a macro-lifted proc
  symbol AND a generic `Strategy[T]` (+generic callee at 2 inst types) both reach and
  run the real walker (`symexFindAllWitnesses`/`symexForAll`→`getImpl`→`parseProc`→
  `walk`), bounded. Capture point validated — safe for the 7 downstream E-slices.
- **Verified GREEN**: agent 60/60 (30 files × c/cpp, twice) + independent 18/18
  dual-backend sweep, 0 fail/hung, no existing assertion edited.

### E2a — POSIX persistent worker — DONE (commits `6f684ea`, `ea0a3df`, `06ab9e2`, `910df1d`)
All four cycles landed, each its own GREEN commit, full `tfuzz*` + `tdb` on `c` green
after every cycle (32/32 files, no existing assertion edited). Files added:
`src/nelli/fuzzworker.nim`, `tests/tfuzzworkerprocess.nim`; touched: `fuzzmacro.nim`
(worker-mode branch in the macro expansion), `fuzz.nim` (`newWorker`/`newOrchestrator(worker,
frontier)` general constructors), `nelli.nim` (exports `fuzzworker`).
- **C1** (`6f684ea`): argv `--nelli-worker=<id>` dispatch + genuine self-re-exec
  (`getAppFilename()` + `fork`+`execvpe`, mirroring `runChild`'s no-GC-between-fork-
  and-exec discipline) + versioned framed pipe protocol (`magic|version|len|payload|
  checksum`, 16 MiB max-frame bound checked BEFORE the read, mirrors PCOV). Reconstruction
  sentinel (round-3 DoD): a strategy constructor bumps a process-local counter; parent's
  own front-door call leaves it at 1 in the PARENT before the worker spawns, so a COW
  fork-without-exec would inherit 1 and report 2 after one more construction, while a
  genuinely fresh process reports exactly 1 — the child's crash-message payload carries
  the marker back. Found+fixed a real obstacle: `std/unittest` treats every argv token as
  a test-name glob filter, so a `--nelli-worker=<id>` child had every `test:` silently
  filtered out; fixed via `unittest.disableParamFiltering()`.
- **C2** (`ea0a3df`): worker publishes its `{.cover.}` bitmap to `$NELLI_COV_FILE` in the
  SAME PCOV wire format `nelli_cov.c` uses (one reader, `parseCoverageMap`, serves both),
  gated to fire at most once per process (`dumpCoverageOnce`, mirrors `pt_dumped`) — this
  IS the N=1 recycle-policy mechanism, pinned by a characterization test (a worker forced
  via the `NELLI_WORKER_MAX_INPUTS` knob, off by default — the E2b seam — to serve 2 inputs
  shows the dump reflects only the first). Found+fixed a real bug: `spawnWorkerProcess` was
  forwarding `envPairs()` unfiltered, so a worker that itself spawns a nested worker (an
  artifact of an earlier test-file design with >1 `fuzz(...)` call site — since fixed by
  collapsing to ONE call site, reused across tests via `nelliLastFuzzCallSiteId`, which also
  eliminates a cascading-recursion trap any future multi-call-site worker test would hit)
  leaked its OWN inherited `NELLI_COV_FILE` into the child.
- **C3** (`06ab9e2`): `observationForDeath` maps a worker that died without answering
  (segfault/uncatchable signal) to `vCrashed`/`CrashInfo` via `reapWorker`'s exit-status
  decode. Two tests: a `kill(getpid(), SIGSEGV)` trigger (a Nim nil-deref is NOT reliably
  uncatchable under checked builds — `NilAccessDefect` is a `Defect` `observeInProcess`
  already catches, which would've defeated the test) shows the pipe read comes back
  cleanly empty, `reapWorker` reports signal 11, no hang; and the persistent-loop geometry
  (one worker forced to answer input 1 normally then die on input 2) shows the failure is
  detected cleanly and a freshly spawned worker still answers further input.
- **C4** (`910df1d`): `newProcessWorker[T](id): Worker[T]` — every `submit` spawns fresh
  (the shipped N=1 policy), round-trips one frame, maps a pipe failure to `vCrashed` via
  C3's `observationForDeath`, merges coverage from the file dump. `Orchestrator` gained a
  general `newOrchestrator(worker, frontier)` constructor over an arbitrary `Worker[T]`
  (the `(s, target, frontier)` overload is now sugar over it); `fuzz.nim` also gained
  `newWorker` (the private `submitImpl` field forced a cross-module public constructor).
  Test drives an `Orchestrator` over the process worker via `run`/`admit` and shows the
  same verdict/crash-kind/coverage an equivalent in-process `Orchestrator` produces.
Coverage-frame design note: the result frame carries ONLY `Verdict` + `Option[CrashInfo]`
+ `message` — coverage rides the file-dump path (stated, not silent), `RunResult` is
omitted (not meaningful for a Nim in-process property inside a worker).

## Slices (first-pass; round-3 re-cuts folded in)
- [x] **E0 corpus-sync SPIKE — DONE** (delta log selected; 5 mandate items resolved) ·
  **E1 Orchestrator/Worker seams + macro entry — DONE** (typed CrashInfo; Worker=
  load-bearing seam; fuzz macro + worker re-entry + capture checks; C7 freeze-guard
  green) ·
  **E2a POSIX worker+framed pipe+crash-isolation — DONE** (N=1 coverage until E2b) ·
  E2b shm+nelli_cov.c reset — **NEXT** (or E3a, E0-indep) · **E3a** freshness machinery (E0-indep) ·
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
