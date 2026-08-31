# RFC — next-generation structure-aware hybrid fuzzer

- **Status:** Implemented — shipped v0.6.0 on `main` 2026-08-28, all 32
  stage-4 review findings closed. MSVC-parity follow-on done 2026-08-26
  (all 63 `tfuzz*`/`tdb*` suites green under `cl.exe`), giving nelli three
  independent Windows legs: mingw, MSVC-in-container, and symex.
- Category: fuzzer

Close the one quadrant nelli's fuzzer cannot reach today — **structure-aware
× crash-isolated × cross-platform** — and then build on top of it the two
capabilities no other fuzzer can: a source-level **concolic bridge** that
solves branch conditions over the choice sequence itself, and a **single
execution substrate** shared by `forAll` and `fuzz`. The mandate is
best-in-class, PhD-level design and functionality; consumer reports are
context, never the driver.

## Status

| | |
|---|---|
| **Stage** | 2 (architecture review) — **rounds 1, 2 & 3 applied (2026-08-14 / 2026-08-15 / 2026-08-15)** (4-lens team each round: depth/breadth/design/feasibility). All clear-best fixes folded in; no open escalations. Round-2 anchor: topology resolved to **centralized orchestrator** (superseding the round-1 "AFL `-M`/`-S`" gloss). Round-3 anchors: the **orchestrator execution model** made explicit (single-threaded completion loop; Z3 bridge + re-verify + reproRate off the hot path on bounded slot budgets; read-before-redispatch invariant) and the **Appendix C admission surface** corrected (three signature defects fixed; `Pool`→`Orchestrator`). Ready for stage 3 (`/tdd` via `/loop`). |
| **Umbrella** | **#158.** Absorbs the execution-model half of #151 (worker-pool fan-out; byte-havoc/dictionary extension point — see the #151 disposition comment). Owns the symex↔choice-sequence bridge that Shape A #127 (concolic) and #130 (`arbitrary(myProc)`) later surface. Does **not** absorb #124 Shape A's #125/#128/#132 (a separate cluster). |
| **Scope** | `src/nelli/fuzz.nim`, `src/nelli/fuzzir.nim`, `src/nelli/coverage.nim`, the sancov runtime (`nelli_cov.c`), `src/nelli/db.nim` (corpus channel), and a new concolic **walker mode** in the symex engine (`smt/`). The `forAll` side touches `engine.nim`/`engine/targeting.nim`/`engine/phases.nim` only at the frontier-unification seam (Track U). |
| **Handoff** | `docs/rfc/0003-fuzzer-nextgen.handoff.md` |
| **Relation to other work** | Independent of the parser-normalization RFC (#146, **shipped** at tag 0.3.5 — a frozen base, not a live rebase target) and the parked chapulin round-6 RFC (the **only** live-moving `smt/` rebase target). The concolic mode (Track G) reads the walker at whatever `symexWalkerVersion` is live; rebase + re-read SW before Track G slices, exactly as the chapulin cross-RFC handoff requires. Supersedes the earlier "#124 Shape A next" recommendation. |
| **Open items** | see §Open items — none block Track E; two shape the guidance/scheduling tracks. |

## §0 — Thesis

nelli owns two assets no competitor has together: a **typed, constraint-
annotated choice sequence** as its input representation (Hypothesis has the
shape but no solver) and a **source-level symbolic executor that speaks Nim**
(the SMT fuzzers symbolically execute x86 and pay for it in cost and lost
semantics). The current fuzzer uses neither to its potential, because it is
pinned at the execution layer to an early-AFL model: spawn-per-input for
external targets, no isolation at all for the structure-aware in-process
path, and POSIX-only.

This RFC treats the fuzzer as **one engine with a portable isolated
executor at its floor**, then layers the differentiated capability on top:

1. **Track E — Executor.** A portable persistent worker pool
   (CreateProcess/`posix_spawn` once per worker, choice sequences streamed
   over IPC, coverage returned via shared memory), with per-input freshness
   recovered by **worker recycling + pristine re-verification** rather than
   by a fresh process image per input. This closes the missing quadrant,
   un-gates external fuzzing to Windows, and is every later track's
   prerequisite.
2. **Track G — Guidance.** The **choice-space concolic bridge** (a new
   walker mode) plus **IR-level cmp-correspondence** — RedQueen resolved
   against typed integer choice nodes, not guessed byte offsets.
3. **Track S — Scheduling.** Entropic-style information-gain energy and a
   bandit over mutation operators, replacing the ad-hoc `+1.0` lineage
   bonus and uniform operator choice.
4. **Track U — Unification.** One coverage-frontier model shared by `fuzz`
   and `forAll`; `forAll` gains replay-only reads of the persisted fuzz
   corpus; byte-mode demoted to interop-only.

**Load-bearing invariant (survives every track): the fuzzer may guess; the
corpus never lies.** Every candidate — from a mutator, a concolic model, or
a long-lived worker — is replayed to a fresh, pristine observation before it
is admitted to the corpus or reported as a crash. This is the same
at-the-observation-boundary validation philosophy the symex engine already
lives by (Invariant-3), applied to execution: a wrong concolic model or a
contaminated worker can only ever *waste a candidate*, never *fabricate a
result*. It is what lets Track E trade `fork()`'s per-input freshness for a
persistent worker's throughput without losing soundness, and what lets Track
G concretize aggressively without a soundness proof on the walker.

**Precondition and its boundary (round-1 depth fix).** The invariant assumes
the SUT is *deterministic given a fixed choice sequence*. That holds for the
Nim in-process tier by construction, but **not** for arbitrary rebuilt
external binaries (multi-threaded, hash-seed-randomized, or timing-dependent
targets are all in §a1 scope). Two rules are therefore binding on every
track, so re-verification never becomes a bug-suppressor:
1. **Re-verification gates *admission*, never *reporting*.** A crash /
   `vInteresting` is **reported on first observation** (as today). Corpus
   *admission*, by contrast, requires a stable re-verified observation: a
   flaky coverage delta does not earn a corpus slot. Suppressing a *report* on
   a single fresh replay would silently drop a genuine race/UAF that
   reproduces once but not on the re-verify run — a regression versus today
   and versus AFL/libFuzzer, and exactly the bug class instrumented fuzzing is
   best at.
   - **`reproRate` is a bounded, asynchronous N-of-M sample with a real
     mechanism (round-2 depth fix).** "N-of-M fresh replays" is not a
     by-product of the single admission re-verify; it is an explicit sampler:
     on a reported finding the orchestrator schedules **M** fresh replays
     (default small, e.g. `reproSamples = 5`, configurable) on recycled
     workers **off the hot path** — it never blocks the first-observation
     report and never stalls the pool. `reproRate = N/M` is attached to the
     finding record and updated as samples land. `M = 1` collapses to a binary
     reproduced-yes/no; the default is >1 precisely so a once-in-K race is
     surfaced with its frequency rather than as a false "did not reproduce."
     The Mx execution cost applies only to findings (rare relative to
     ordinary execs), and is bounded by `reproSamples`.
2. **The re-verified observation is authoritative for everything
   *admission*-persisted** (frontier bucket, corpus entry) — the
   candidate-worker observation is a cheap pre-filter, never itself recorded.
   - **The first *report* is immutable; re-verify divergence is recorded, not
     overwritten (round-2 depth fix).** For a nondeterministic in-scope target
     (multi-threaded / hash-randomized / timing-dependent, §a1), a fresh
     re-verify can genuinely yield a **different `CrashInfo.kind`** than what
     was already shown (reported `ckSignal(SIGSEGV)`, re-verify
     `ckSignal(SIGBUS)` or even `vOk`). Because crash-dedup keys on
     `CrashInfo.kind` (D1), silently overwriting the persisted key with the
     re-verify result would fragment one flaky bug into several "new" findings
     or clobber a persisted record with an unrelated crash type. Rule: the
     **reported** `CrashInfo`/dedup key is fixed once shown and never
     rewritten; a kind-mismatch on re-verify is recorded as a distinct
     **`divergentReproduction`** field on the finding (the observed variant
     set), never as a competing dedup key.
   - **The dedup index must cover divergent variants, or the same fragmentation
     reopens by a second path (round-3 depth fix).** Recording a variant as
     `divergentReproduction` rather than a competing key closes overwrite-driven
     fragmentation, but leaves a structurally identical path open under the
     highly-concurrent centralized model: while R1's async samples are still in
     flight, the ordinary fuzz loop can produce a *different* input X′ that trips
     the **same** nondeterministic race and, on **first observation**, yields the
     divergent kind (SIGBUS). If dedup only knows primary keys, SIGBUS is "new"
     and X′ opens a second top-level finding R2 — one root cause split in two,
     the exact outcome the fix exists to prevent, via first-observation of a
     variant instead of overwrite. Rule: crash-dedup indexes **kind → the set of
     findings that have observed it, whether as primary key *or* as a
     `divergentReproduction` variant.** A first-observation whose kind matches a
     live finding's recorded variant is merged into that finding (or at minimum
     cross-referenced so a reviewer sees the link), not opened as new. This keeps
     the *reported-first-key-is-immutable* rule (the primary key still never
     changes) while making variant discovery idempotent across inputs.

## Ground truth at HEAD — probed 2026-08-14

Source of these facts: a very-thorough read of `fuzz.nim`, `fuzzir.nim`,
`coverage.nim`, `nelli_cov.c`, `db.nim`, `docs/FUZZ_PLAN.md`, `docs/fuzz/`,
and the `tfuzz*` suite. No builds run (nim is container-only).

1. **The structure-aware path has no crash isolation.** `inProcessTarget`
   (`fuzz.nim:310-335`) runs the property as a closure in the fuzzer's own
   process; the `mutateIR*` family and the `#107` `coverageGuided forAll`
   path are all in-process. Under `--panics:on`, a property `Defect`
   (`IndexDefect`, nil-deref, overflow, failed `doAssert`) is fatal and
   uncatchable — it aborts the whole run (`engine.nim:54-60` warns
   exactly this). A memory-corrupting FFI target segfaults the campaign.
   So today you get structure-aware mutation **or** crash isolation, never
   both — the missing quadrant.
2. **External fuzzing is POSIX-only.** Everything from `fuzz.nim:858` down
   — `runChild`, `externalTarget`, `differentialTarget`, `fuzzBinary`, the
   oracles, `setrlimit` limits — is inside `when defined(posix)`. Windows
   has no external-target fuzzing at all.
3. **The external model is spawn-per-input, not persistent.** `runChild`
   (`fuzz.nim:871-935`) does `fork()`+`execvpe()` for **every** input,
   with three fresh temp files (stdin/stdout/stderr) and a per-run
   `mkdir`/`removeDir`, coverage arriving via a **file** dump read only
   after `waitpid` (D5/D7). This is a deliberate choice — the
   absolute-snapshot coverage model (`INV-fresh-exec`, FUZZ_PLAN D2)
   depends on a fresh image per run — but it caps throughput at low
   hundreds of execs/sec, a 100–1000× gap to a forkserver/in-process loop.
4. **Coverage is admission-only, not directed.** `CoverageFrontier.admit`
   (`coverage.nim:357-370`) folds a run into an AFL 8-bucket classifier
   (`bucketOf`, `coverage.nim:315-328`); a mutant is admitted iff it
   raised some slot's bucket (`fuzz.nim:560`). There is no
   distance-to-frontier steering and no per-edge energy (FUZZ_PLAN D4,
   explicit). The optional `powerSchedule` gives a fresh admit energy
   `2.0` and its lineage `+1.0` on each admitted child (`fuzz.nim:355-366,
   565-566`) — a coarse recency/lineage bias, nothing like Entropic or
   AFL++'s schedule family.
5. **No cmp/value-profile guidance.** Grepping the fuzz/coverage sources
   for cmplog/value-profile/taint returns nothing. Magic-byte and
   constant-comparison gates (`if h == 0xCAFEBABE`) are effectively
   unfindable by mutation — the single biggest reachability blind spot.
6. **The mutation core is genuinely good and target-agnostic.** The
   `mutateIR*` family (`fuzzir.nim`) operates on the `seq[ChoiceNode]`
   choice sequence with constraint-respecting perturbation
   (`mutateIRPerturbInteger`), kind-boundary replacement, span-aware
   **crossover** (`mutateIRSpanSplice`, using the strategy's own
   `startSpan`/`endSpan` boundaries), and span delete/duplicate — all
   total (identity on no-op), so the loop calls any unconditionally. But
   the loop picks one of five ops **uniformly** (`fuzz.nim:534-547`); no
   adaptive scheduling. Byte-mode is a separate, weaker kernel (two ops,
   old scalar `covAfter > covBefore` admission, no havoc, no dictionary
   despite `dictionary: seq[seq[byte]]` being spec'd in
   `docs/fuzz/INTERFACE.md:145` and **absent** from the real
   `FuzzSettings`, `fuzz.nim:122-202` — a doc/code drift, not a feature).
7. **Fuzzing is structure-aware by construction.** Each iteration replays a
   `seq[ChoiceNode]` through the user's `Strategy[T]`
   (`newReplaySource` + `s.generate(ds)`, `fuzz.nim:549-556`) and mutates
   that choice-IR under each node's declared constraints. A fuzz-found
   crash is directly a `ChoiceNode` sequence the existing shrinker and
   `ExampleDatabase` understand — the fuzz/PBT representation is unified at
   the *data* layer already (M12 partitioning, `fuzz.nim:1-16`). What is
   **not** unified is the *coverage* model: `forAll`'s `coverageGuided`
   reads the in-process scalar `currentCoverage()` as a single Pareto
   label (`engine.nim:71-75, 118-153`), never the bucketed frontier
   (FUZZ_PLAN D10). Two coverage worlds, one data world.
8. **The symex↔fuzz bridge does not exist.** No `symex` reference anywhere
   in `fuzz.nim`/`coverage.nim`/`fuzzir.nim`, and no fuzz coupling in the
   symex engine. Green field.
9. **`ExampleDatabase` already has the corpus channel.** `db.nim`'s
   closure-record store has three sections per testId; the `corpus`
   section (F1) is fuzz-seed storage, **never pruned**, keyed by
   `fuzzCorpusKey(persistKey, targetId)` (`fuzz.nim:397-416`) so a rebuilt
   binary starts fresh rather than replaying against a stale map. The
   downstream chapulin `.soak-corpus` sibling-testId workaround
   (RFC-chapulin-hardening.md:992) is obsoleted by F1 and is a scar worth
   noting: a consumer hand-rolled a corpus channel because the library's
   arrived late. Track U's `forAll` corpus-read must not repeat that.

**Honest tier today:** a solid, well-tested *AFL-classic-model, generic-
sancov, spawn-per-exec* external fuzzer bolted onto a mutation core that is
*architecturally ahead* of raw AFL (constraint-respecting, span-aware). Not
at libFuzzer/AFL++ execution tier; ahead of Hypothesis on external coverage
(which Hypothesis lacks entirely); disconnected from its own best asset (the
symex engine).

---

## Scope decision (a1) — resolved in the design grill

- **The product is the structure-aware Nim-native fuzzer.** Portable
  isolated worker pool, symex-hybrid concolic loop over choice sequences,
  IR-level cmp-correspondence, bandit mutator scheduling, Entropic energy.
- **External binary fuzzing is a supported secondary tier** that inherits
  the shared infrastructure (workers, shm transport, scheduling,
  persistence). Track E un-gates it to Windows. External targets must be
  **rebuildable with instrumentation** (the AFL/libFuzzer assumption too).
- **Not a goal now:** fuzzing *uninstrumented* third-party binaries (DBI —
  DynamoRIO/TinyInst/WinAFL class). Recorded as the stretch path to full
  option (b) in §Appendix B, because it slots in cleanly as another
  coverage provider behind the same frontier interface and nothing in this
  RFC forecloses it.

---

## Track E — portable isolated executor  (prerequisite for everything)

**Goal.** Replace both weak execution paths (in-process-no-isolation;
POSIX-spawn-per-input) with one **persistent worker pool** abstraction that
is crash-isolated, cross-platform (Windows first-class), parallel from the
start, and fast, without losing the `INV-fresh-exec` freshness guarantee
where it matters.

**Parallel is v1, not a follow-on (grill-resolved, fork 2). Topology =
centralized orchestrator (round-2 correction).** One orchestrator process
(the `Pool`) owns the *single* in-memory `CoverageFrontier`, corpus,
crash-dedup set, and scheduler, and dispatches replays to **many worker
processes running concurrently** — the fork-2 "one shared, evolving corpus"
call, read literally. The workers are dumb execution engines; all admission
is serialized inside the orchestrator's one in-memory critical section (cheap
relative to execution at single-node worker counts). Round 1 glossed this as
"the single-node analogue of AFL's `-M`/`-S`," but federated `-M`/`-S` means
*independent processes with no shared memory merging via disk* — flatly
incompatible with "the `Pool` owns *the* shared frontier" (a singular
in-memory object has nothing to disk-merge). The centralized model is the
better single-node design: the frontier, dedup, Entropic energy (S1), the
bandit (S2), and the Z3 bridge (Track G) all live in **one** owner with no
cross-process coherence problem. The risk parallelism still carries — the
*disk* concurrency between the orchestrator's corpus writes and other readers
/ writers of the shared `ExampleDatabase` — is retired by an **early spike
(E0)** before the real executor commits. Federated multi-instance `-M`/`-S`
is the **cross-node** design and stays out (that is #112's concern); the
`Worker`/`Pool` seams + shared `ExampleDatabase` keep it additive.

**Design.**

- **Two seams, not one (round-1 design fix): `Worker` and `Pool`.** A single
  blocking `submit → Observation` interface cannot express "N workers
  concurrently" — it is structurally today's `Target[T].run`. Split the
  responsibility:
  - **`Worker[T]`** — a 1:1 process wrapper: `submit(seq[ChoiceNode] | raw
    input) → Observation`, spawn-once, recycling policy worker-local. This is
    what E1–E2 actually build; it stays blocking and simple.
  - **`Pool[T]`** — owns N `Worker`s, the shared `CoverageFrontier`, the
    shared crash-dedup set, and the corpus-admission critical section. It is
    the **only** object that knows about cross-worker concurrency, so E3's
    serialization/merge design has exactly one home instead of being smeared
    across the fuzz loop.
  - **Topology = centralized orchestrator (round-2 correction; supersedes the
    round-1 "AFL `-M`/`-S`" gloss).** The `Pool` is the single orchestrator
    process; it owns the one in-memory frontier/corpus/dedup/scheduler and
    dispatches replays to N **dumb** worker processes that hold *no* fuzz-loop
    state of their own — a worker receives a choice sequence, replays it,
    returns an `Observation`, and forgets it. Admission is serialized inside
    the orchestrator, so there is **no multi-writer disk race from the
    workers** (the workers never write the corpus at all; the orchestrator
    does, single-writer). This is why a blocking per-worker `Worker.submit` is
    the right shape and why E1's `Target`-shaped refactor is a legitimate
    no-behavior slice: the workers are execution seams; all concurrency and
    scheduling live in the orchestrator, above the worker call. The
    orchestrator also owns the **single Z3/concolic-bridge instance** (Track
    G) and the shrink-job scheduler (§below), so neither is smeared across
    workers or duplicated per-worker.
  - **The orchestrator owns three concurrency-sensitive jobs, not one
    (round-2).** Beyond corpus-admission, the `Pool` centralizes (a) **pristine
    re-verification** — it, not the fuzz loop, performs "spawn a fresh worker,
    replay, then admit" via a single `Orchestrator.admit(input, candidate):
    AdmitResult` (round-3 name/shape; see Appendix C)
    so the fuzz loop stays a thin execution-agnostic orchestrator on *every*
    path, not just parallel-sync; (b) **seed-in-flight marking** — a
    just-admitted seed is marked so two workers do not both spend energy
    re-exploring it (the redundant-work problem federated `-M`/`-S` solves with
    its deterministic/havoc instance split, which the centralized scheduler
    solves directly); (c) **shrink scheduling** — a crash shrink job is run on
    a dedicated recyclable worker slot drawn from the same worker budget, never
    by commandeering an in-flight fuzzing worker, so concurrent crashes do not
    starve fuzzing throughput unboundedly (a bounded shrink-slot count is a
    `Pool` policy knob).
  The fuzz loop, scheduler, corpus, and shrinker code to these two seams and
  stay execution-agnostic.
- **The orchestrator's execution model is one single-threaded completion loop,
  not a thread per worker (round-3 — resolves the design lens's blocking-`submit`
  question and the depth lens's contention/ordering findings together).** The
  "workers are processes, never threads" non-goal governs a worker's *internals*;
  it left open how the one orchestrator drives N of them. It does so with a
  **completion-oriented `Worker` seam** (`submitAsync → WorkerHandle`; the
  orchestrator `poll`s many at once — Appendix C), so a single orchestrator
  thread fans out to N workers without N orchestrator-side threads and without
  serializing execution behind one blocking call. Blocking `Worker.submit`
  survives only as the convenience wrapper E1's single-worker reference impl and
  `forAll`'s Pool-of-1 (U0) use. Three consequences this pins:
  1. **The Z3/concolic bridge runs *off* the hot dispatch path (round-3 breadth
     fix).** A G3 stall-triggered solve is bounded but can legitimately run
     seconds (`maxRelaxationAttempts` × per-attempt Z3 timeout, G2); running it
     inline in the completion loop would idle every worker and queue every
     admission *exactly during a stall, when guidance matters most.* The solve
     runs on a dedicated slot (like shrink), submitting its materialized seed
     back through `Orchestrator.admit` on completion — dispatch and admission
     never block on Z3. The Risks "admission is negligible" claim is about the
     frontier-fold's O(1) cost and does **not** extend to this; the bridge is
     budgeted, not folded into the critical section.
  2. **Re-verify and `reproRate` sampling draw from *bounded* slot budgets, the
     same treatment shrink got (round-3 depth fix).** `reproRate`'s M replays
     per finding and `Orchestrator.admit`'s fresh-spawn re-verify both consume
     the finite worker resource; a burst of distinct findings must not spawn
     unbounded concurrent samplers or stall admission on worker scarcity. Named
     `Orchestrator` policy knobs bound {fuzzing, re-verify, reproRate-sample,
     shrink} concurrent slot counts against the one worker budget; `admit`'s
     re-verify spawn either draws a reserved slot or is queued with a bounded
     depth — never an unbounded synchronous stall inside the admission section.
  3. **Read-before-redispatch is an explicit per-worker invariant (round-3 depth
     fix), pinned like the fork-snapshot invariant.** The shm double-buffer's
     generation word is a single acquire-check, not a full seqlock; its
     torn-generation safety rests on the orchestrator's `probe.read()` for input
     K completing *before* the same worker is dispatched input K+1 (true under
     the request-response seam, since a worker blocks awaiting its next frame). A
     future throughput optimization that pipelines dispatch ahead of read would
     silently reintroduce the torn read. State it as a named contract of the
     `Worker`/`shmProbe` pairing and pin it: a test that delays `probe.read()`
     and asserts the worker cannot publish a second generation before the delayed
     read returns.
- **Coverage rides the existing `CoverageProbe` seam, not the worker
  protocol (round-1 design fix).** `coverage.nim:374-382` already defines
  `CoverageProbe{read, resetsPerRun}` with two live impls
  (`inProcessProbe`, `sancovFileProbe`). The persistent worker's shm region
  is exposed as a **third impl (`shmProbe`)** constructed once per worker at
  spawn; `Worker.submit` returns verdict + crash data and the caller composes
  the `Observation` via `frontier.admit(probe.read())`, exactly as
  `inProcessTarget`/`externalTarget` do today. This keeps execution and
  coverage-acquisition as separate deep modules and makes Appendix B's
  "retrofit a DBI coverage source behind the same interface" claim literally
  true rather than aspirational.
- **`Observation` carries a typed `CrashInfo`, not a stringly-typed
  `message` (round-1 design fix).** Track E adds a third crash taxonomy
  (Windows exception codes) atop POSIX signals and in-process `Defect`s;
  folding all three into a free-text `message` that `crashKey`/`sanitizerOracle`
  must string-grep back out is the wrong direction for a portability track.
  Introduce `CrashInfo = object; case kind: ckException | ckSignal |
  ckExitCode | ckWinException` now, while every crash site is already being
  touched; `Observation.message` stays as a human rendering *derived* from
  it, but de-dup, oracle matching, and reporting match on `kind`, never parse
  prose. **`Observation` is a single-execution, immutable result (round-2
  design fix):** verdict, `CrashInfo`, coverage delta, timing — constructed
  once by `Worker.submit` + coverage composition, never mutated. The
  cross-execution aggregates — `reproRate` (N-of-M samples), the
  `divergentReproduction` variant set, and seed **provenance** (which mechanism
  produced the input: structure-aware mutation / G2 concolic / G5 I2S /
  imported) — live on the **persisted finding/corpus record** built *from* N
  `Observation`s, not accreted onto one single-run object. Provenance threads
  through the orchestrator's admission critical section and gives the ablation
  harness its per-mechanism attribution (concolic- vs mutation-origin corpus
  growth) without diffing snapshots by hand. **Resource-limit kills are their
  own verdict** (`vResourceExceeded`,
  the memory/CPU/wall-clock Job-Object/`setrlimit` case), tagged distinctly so
  an unbounded-allocation non-bug does not flood the crash corpus or compete
  with genuine `vInteresting` findings — mirroring the first-class-but-distinct
  treatment `vTimedOut` already gets.
- **Persistent worker.** A worker process is spawned **once**
  (`CreateProcess` on Windows, `posix_spawn`/`fork`+`exec` on POSIX),
  initializes (loader, GC, strategy closures) **once**, then loops:
  read a choice sequence from an input pipe, replay it through the strategy
  and property, write coverage to a **shared-memory** region
  (`CreateFileMapping`+`MapViewOfFile` on Windows, `shm_open`+`mmap` on
  POSIX), signal completion. Per-input cost collapses to IPC round-trip +
  property execution — the AFL-persistent/libFuzzer amortization.
- **Freshness without a fresh image.** Two mechanisms recover what
  `fork()`-per-input gave for free:
  1. **Worker recycling** — retire a worker after N inputs and on any
     crash, bounding the contamination window.
  2. **Pristine re-verification** — any input judged `vInteresting` or
     crashing is replayed in a **freshly spawned** worker. Per the §0
     precondition rules, this **gates corpus admission** (a contaminated
     candidate is discarded on re-verify) but does **not** gate crash
     *reporting* (reported on first observation, with a `reproRate`
     attached); and the fresh worker's observation — never the candidate
     worker's — is authoritative for everything persisted.
  This preserves `INV-fresh-exec` at the **observation boundary** (where it
  is load-bearing), not at every execution (where it was merely how AFL
  happened to get it).
- **POSIX `fork()` is a recycling policy, not an architecture.** On POSIX
  the worker may `fork()` from a parked post-init snapshot per input
  (recycle-every-input, AFL-forkserver-cheap), giving Linux campaigns the
  stronger freshness guarantee at full speed. Same seam, two recycling
  economics. The Windows worker recycles on the N-inputs/crash policy.
  **Invariant (round-1 depth fix): the parked snapshot is captured exactly
  once, pre-input, at process birth — never re-parked from post-execution
  state.** A snapshot refreshed from a worker's own post-run state would bake
  accrued contamination into every subsequent "fresh" fork, silently
  defeating the freshness guarantee with no visible violation. Pinned by a
  characterization test: N forks from one snapshot are state-identical (a
  probe that would differ if state leaked between forks stays constant).
  **`fork()`-recycling is gated to single-threaded worker builds (round-2
  breadth fix).** Classic `fork()`-in-a-multithreaded-process: only the calling
  thread survives into the child, so any lock held by another thread at
  snapshot time (Nim GC/allocator helper threads, or any `--threads:on` build —
  and Eci explicitly adds `--threads:on` to the toolchain) is frozen-held in
  every "fresh" fork → deadlock/corruption with no visible violation. This is a
  bug in the *mechanism*, stronger than the §0 nondeterminism caveat. v1
  therefore restricts the fork-recycling economy to **single-threaded worker
  builds**, gated explicitly; a threaded worker falls back to the
  N-inputs/crash recycling policy (spawn a fresh image), never fork. The safer
  future path for threaded builds is **CRIU-style whole-process
  checkpoint/restore** (restores *all* threads, not just the caller, so it
  lacks this failure mode) — recorded as the threaded-fork alternative, not
  built now.
- **Crash detection, portable.** POSIX signals (`WIFSIGNALED`) and Windows
  exception codes (`STATUS_ACCESS_VIOLATION` &c. via the worker's
  unhandled-exception filter / exit code) both map to the existing
  `Verdict` enum (`vOk/vRejected/vInteresting/vTimedOut` + a crash
  verdict). Resource limits: `setrlimit` (POSIX) / **Job Objects**
  (Windows) for memory, CPU, wall-clock; the existing SIGTERM→grace→SIGKILL
  escalation generalizes to `TerminateJobObject`.
- **Instrumentation.** The Nim tier uses nelli's own `{.cover.}` bitmap
  (`coverage.nim`) — **compiler-independent**, so MSVC/vcc costs nothing.
  The external tier keeps the dual-sancov runtime (`nelli_cov.c`) but reads
  it over **shared memory** instead of a per-run file when the target
  supports shm. **The shm design is push/copy into double-buffered shm, not a
  zero-copy directly-mapped view (round-1 fix, corrected in round-2):**
  `nelli_cov.c` **copies** the counter region into a double-buffered shm region
  at end-of-run and publishes it under an atomic generation word
  (release-after-copy / acquire-before-trust); the orchestrator reads the
  published inactive buffer. (A literal directly-mapped view of the clang
  inline-8bit-counters is *not* free — they are static globals written in place
  and would need per-target linker-script placement to live in shm; out of
  scope, see E2b.) The async-signal-safe **file dump stays as the
  crash/signal-time path** (partial coverage of a crashing input) and the
  gcc/no-shm fallback. This means a persistent worker needs `nelli_cov.c` to
  support **per-input reset + republish**, which the current runtime does *not*
  have — its `pt_dumped` gate (`nelli_cov.c:65-69`) is process-lifetime-once.
  The reset must zero the *inactive* buffer and atomically flip the active
  index so a signal-time dump never observes a buffer mid-reset. That C-runtime
  work (fill the `CoverageProbe.resetsPerRun` contract `FUZZ_PLAN` D2 already
  reserved) is an **explicit E2b deliverable**, not a free transport swap.
- **Windows external coverage has a named fallback (round-1 fix).** If MSVC
  `/fsanitize-coverage` cannot match the clang inline-8bit-counters ABI
  `nelli_cov.c` depends on (see Risks), external Windows targets are built
  with **`clang-cl`** (ABI-compatible with the existing runtime), documented
  as a target-build requirement; failing that, the Windows external tier
  ships **coverage-blind** (crash-isolated, random-only) as a graceful
  degradation of the exit gate, never a hard blocker.

- **Disk concurrency sits on a real race in the shipping backend (round-1
  fix, retargeted in round-2; the concrete target of the E0 spike).** `db.nim`
  stores `primary` + `secondary` + `corpus` in **one file per `testId`**
  (`keyPath = path / safeKey(testId) & ".bin"`), and *every* mutating op —
  `saveImpl`, `saveWithMetaImpl`, `removeImpl`, `saveSecondaryImpl`,
  `saveCorpusImpl` (`db.nim:471-514`) — does the identical unsynchronized
  `readContents → apply → writeContents`. Each *write* is atomic (tmp +
  rename) but the RMW cycle is not, so a last-`rename` lost update is possible
  whenever two RMW cycles overlap on that file. **Under the centralized
  orchestrator the corpus writer is single (the orchestrator), so the
  N-workers-hammering-`saveCorpus` race is *not* the hazard** — the workers
  never touch the corpus. The residual races E0 must actually retire are
  **cross-writer/reader on the shared per-`testId` file**: (a) the
  orchestrator's `saveCorpus` vs the **shrinker's** concurrent
  `save`/`remove`/`saveSecondary` (primary/secondary section, same file); and
  (b) the orchestrator's `saveCorpus` vs `forAll`'s **snapshot read** of the
  corpus section (Track U/U2). A corpus-section-only fix does **not** close
  (a), because the shrinker rewrites the same file via the old path. E0
  therefore spikes the **real `directoryBasedDatabase` backend** (not a
  bespoke store — the race lives in shipping code) choosing among: (a) an
  advisory file lock around the whole-file RMW (POSIX `flock` + Windows
  `LockFileEx`); (b) an **append-only delta log** so concurrent appends
  compose losslessly with no global RMW (favored a priori — no lock on the hot
  path); (c) a single-writer mediator. **E0 must resolve two things round-1
  left implicit:** (1) whether `corpus` is **split into its own file/stream**
  so its write path no longer shares a rewrite target with primary/secondary;
  and (2) a **compaction design for the delta log** — under S4's continuous
  disk eviction the log grows monotonically (eviction = tombstone deltas) and
  every reader (incl. `forAll`'s snapshot) replays full history, so compaction
  is mandatory, and compaction is *itself* a batched RMW that must fold-and-
  atomically-rename under the same serialization primitive or it reintroduces
  exactly the race E0 exists to kill. **`forAll`'s snapshot needs a precise
  cut point** — a sequence-number/offset captured at open, with record-level
  atomicity so a concurrently-appended in-flight record is never read as a
  torn tail. Crash-dedup (`seenCrashKeys`, today per-`fuzz()`-local) and
  `stopOnFirstCrash` become **in-memory orchestrator state** (one owner, no
  disk race), not a per-worker set — otherwise parallel workers re-report the
  same bug as "new" exactly when parallelism makes duplicate discovery more
  likely. **E0's mandate gains two more items round-3 surfaced:** (3) **the
  compaction rename must be verified Windows-safe against a live snapshot
  reader, not only POSIX-safe.** POSIX `rename`/`unlink` over an open descriptor
  keeps the old inode valid, so a `forAll` reader on a pre-compaction cut point
  is unaffected — but Windows file replacement is governed by sharing-mode flags
  and `MOVEFILE_REPLACE_EXISTING` semantics that do **not** preserve the old
  file for existing handles; a naive in-place fold-and-rename can throw
  `ERROR_SHARING_VIOLATION` or expose reader-visible divergence. Given "Windows
  first-class," E0 must design the compaction swap (e.g. copy-then-atomic-
  directory-entry-swap) to be reader-safe on **both** platforms, not assume
  POSIX inode semantics. (4) **The shrinker-vs-shrinker write race is named:**
  round-2's shrink-slot budget is a *bounded but plural* count, so >1 shrink job
  can write `save`/`remove`/`saveSecondary` on the same per-`testId` file
  concurrently — the very N-writers-on-one-file race E0 exists to kill,
  relabeled from fuzzing workers to shrink workers. E0 states explicitly either
  that **all** primary/secondary/corpus writes (orchestrator *and* every shrink
  slot) funnel through one serialization primitive sized for N-way concurrency,
  or that shrink jobs write **through the orchestrator** (single-writer
  preserved) rather than touching `db.nim` directly from a worker slot. (5) **The
  on-disk corpus/delta-log format carries a version tag with a defined
  incompatible-format rule (round-3 breadth fix).** E2a's *wire* protocol already
  gets a version tag so a worker can't outlive a format bump mid-campaign; the
  *persisted* corpus deserves the same across a nelli upgrade. A user who runs on
  the old single-file RMW format, upgrades past E0's delta-log format, and
  reopens the same `persistKey`/`targetId` must hit a defined outcome — refuse-
  and-message or auto-migrate, mirroring SW's explicit floor-pin discipline for
  the walker — not a silent misread. E0 names the corpus-format version field;
  U3 (which already reconciles doc/code drift) may host the migration/rejection
  logic.
- **Worker-mode re-entry (RESOLVED — §Open items "opaque-closure
  boundary").** A persistent in-process worker is a *fresh-exec'd* process
  that does not inherit the user's `Strategy[T]`/`prop` closures. Resolution:
  the **same call-site macro** that captures the property for concolic also
  emits a hidden worker-mode entry (dispatched by an **argv call-site ID**, not
  an inherited env var — see §Open items) that re-runs the captured
  construction expressions to rebuild strategy+property and enters the worker
  loop — **no `nelli.workerMain` for the user to call**, the ordinary
  `fuzz(...)` site double-serves. E1 defines this entry; targets whose
  construction is not re-runnable are caught at compile time (free-identifier
  check) and degrade to POSIX-fork-only /
  Windows-spawn-per-input.

**Slices (first-pass granularity; architect will refine).**

- **E0 — parallel-corpus-sync spike (throwaway).** Before committing the
  executor architecture, prove the concurrency model for N workers sharing
  one evolving corpus: how admissions are serialized, how the frontier is
  merged across workers without a lock becoming the bottleneck, how a
  worker gets fresh seeds mid-campaign, and how the shared
  `ExampleDatabase` corpus section tolerates concurrent writers. Deliver a
  minimal spike (not production code; may be deleted) that runs M workers
  against a trivial target **through the real `directoryBasedDatabase`
  backend** (not a bespoke store — the race lives in the shipping code, so
  the spike must hammer it) and demonstrates linear-ish throughput scaling +
  a coherent merged frontier under one of the three candidate serializations
  above. **Its findings shape E2/E3's real design** — the spike exists
  precisely so a wrong sync model is discovered on a throwaway, not on the
  whole executor. Size S–M.
  **CONCLUDED 2026-08-25 — full decision record in
  `docs/rfc/0003-fuzzer-nextgen.E0-findings.md`.** Verdict: **append-only delta log**
  (spike measured 87% baseline lost-update loss vs 0% for the log; the log
  out-scales an advisory `flock` RMW ~70–115× and, unlike the lock, does not
  degrade under contention). Resolved: corpus **split** to its own
  `<key>.corpus.log`; `.bin` (primary+secondary) writes funnel **single-writer
  through the orchestrator** so plural shrink slots never race (mandate 4);
  compaction publishes via a **generation-file + head-pointer + reader-lease**
  swap that never replaces bytes under a live handle (reader-safe on POSIX by
  test, on Windows by construction — mandate 2/3); the log header carries a
  **version tag** with refuse-on-newer / migrate-on-older, legacy single-file
  corpus externalized at U3 (mandate 5). Two spike findings fold forward: the
  orchestrator must hold **one long-lived DB handle** (concurrent constructors
  race on tmp-sweep — F-1), and the log also sidesteps the backend's
  whole-file-rewrite O(n²) cost (F-2). Under the centralized topology the
  frontier is single-in-memory, so "merge across workers" is a non-issue — the
  real residual was writer-vs-writer + reader-snapshot, which the log retires.
- **E1 — `Worker`/`Pool` seams + call-site macro entry + in-process
  reference impl.** Define both seams; introduce the **call-site macro fuzz
  entry** that captures the strategy/property construction expressions (the
  boundary that later gives Track G its AST and gives the worker its
  re-runnable constructor) and reimplement today's `inProcessTarget` as an
  in-process `Worker` under a single-worker `Pool` (no behavior change, no
  isolation yet). The argv-call-site-ID worker-mode re-entry lands here
  (exercised in-process now; a real fresh process at E2/E4a). **`Orchestrator.admit`
  is opaque/synchronous-from-the-caller (round-2 feasibility fix):** its
  signature hides whether admission is a direct in-memory fold or E0's chosen
  deferred-log mechanism, so E0's outcome cannot force an E1 signature rework.
  **The macro's *AST* capability is proof-spiked here, not left for G1 (round-2
  feasibility fix — the N=1-freeze guard):** a throwaway check that the
  captured AST is ingestible by a symex entry point ships with E1, so
  the second consumer (the walker) validates the capture shape before ~7 Track-E
  slices weld onto it; if the walker needs sem-checked `NimNode`/instantiation
  info the capture point is fixed now, not after freeze. **The spike bar is the
  *real* dispatch entry, not a stub, and includes a generic-strategy case
  (round-3 feasibility fix).** A stub accepts any shape by construction and so
  proves nothing about consumability; the spike must feed the captured property to
  the walker's real ingestion path and
  include **at least one generic-instantiated `Strategy[T]` capture** (T inferred
  at the call site) — generics being the codebase's known prior failure class
  (the bare-name monomorphization-cache collision, per the `symex generics plan`
  memory). "Syntactically capturable" ≠ "consumable by the real walker"; without
  the generic case the freeze just moves one layer down to G1, nine slices later.
  **CORRECTED against the code (2026-08-25 — the exact freeze-guard this spike
  exists to fire): the walker does NOT ingest a raw captured `NimNode` AST, and no
  `wmFollowConcrete` mode exists yet.** The verified door is `fn: typed` →
  `getImpl` → `parseProc` (lowers `NimNode` → `IRStmt`) → `walk` (single symbolic
  mode) — `symexForAll` (`symex.nim:461`) / `symexFindAllWitnesses`
  (`symex.nim:1627`) → `runSymex` → `walk` (`smt/runtime.nim:5939`). Consequence
  for capture shape: **the macro must present the property as an *emittable typed
  proc symbol*** (a named module-scope proc), because that — not an untyped AST
  blob — is what the walker consumes; a property that can only be a closure *value*
  threaded through indirection stays `sfNotApplicable` (already the rule). The
  spike therefore hands the emitted proc **symbol** to `symexFindAllWitnesses` and
  drives the real single-mode `walk` under a **bounded step budget** (there is no
  stub mode to fake). Generics remain in scope: `instKeyFor`
  (`dsl_parser.nim:5262`) already carries the bodyHash+typeSubst collision fix, and
  a generic `Strategy[T]` flows via `s.getTypeInst()`. `wmFollowConcrete` is
  introduced later by Track G, not stubbed here.
  **Track E's *second* macro capability is spiked here too (round-3):** the same
  E1 spike exercises the worker-reconstruction path — a genuine
  module-scope-reconstructible constructor rebuilt in an (in-process, at E1)
  worker-mode re-entry — so E's semantic contract is validated at E1, not first
  exercised live at E2a. Characterization pins:
  existing `tfuzz*` in-process suites stay green through the macro + seams; the
  free-identifier compile-error fires on a deliberately non-reconstructible
  target; the impurity-denylist compile-error fires on a module-scope
  `let x = getEnv(...)` capture. Size M (the macro-ification is the reason this
  is no longer S).
- **E2a — POSIX persistent worker: spawn + framed pipe + crash isolation
  (round-2: split from E2).** The `posix_spawn`/`fork`+`exec` worker,
  **versioned framed input protocol** (a length-prefixed frame header —
  `magic|version|len` — analogous to the D5 coverage-dump format; names a
  **max choice-sequence frame size** so an unbounded/recursive strategy stalls
  loudly at a defined bound rather than wedging a fixed pipe buffer; a
  protocol-version tag so a persistent worker cannot silently outlive a
  wire-format bump mid-campaign), worker lifecycle. Coverage rides the existing
  **file-dump** path here (interim), so crash isolation ships without waiting
  on the C-runtime work. **But the interim file-dump path is `pt_dumped`-gated
  process-once, so multi-input coverage is INVALID until E2b — say so, don't
  ship it silently (round-3 feasibility fix).** A persistent worker loops over
  N>1 inputs, but `pt_dumped` (`nelli_cov.c:65-69`) yields a valid dump for the
  *first* input only; inputs 2..N observe stale/empty coverage, which feeds
  `frontier.admit` and steering — silently corrupting every coverage-guided
  decision in the E2a→E2b window, and E2a's crash-only DoD would go GREEN without
  touching it. E2a therefore **recycles every input (N=1) on the interim path**,
  pinned by a characterization test asserting the N=1 policy (so nothing
  downstream assumes multi-input coverage validity before E2b lifts it); E2b
  flips N-per-worker on once reset/republish lands. **DoD forces the real
  reconstruction path (round-2 feasibility fix):** the initial spawn must be a
  genuine `fork()+exec()` /
  `posix_spawn` (not a plain COW `fork()` that inherits closures and fakes the
  test). **The sentinel must discriminate reconstruction from COW inheritance,
  not just post-spawn mutation (round-3 feasibility fix):** a child not observing
  a *post-fork* parent mutation is satisfied by a plain COW `fork()` too (COW
  already isolates the address space), so it proves nothing. The pin is that the
  child's strategy/property object, **freshly rebuilt by re-running construction**,
  matches the parent's *current live* constructed object — and a naive
  fork-without-exec that inherited the pre-fork closure is detectably
  distinguishable (e.g. construction stamps a fresh per-process identity the
  inherited closure lacks). Crash isolation proven two ways: a property that
  `doAssert`s/segfaults yields a crash verdict instead of aborting the run
  (`tfuzzexternal`/`tfuzzcbuild` pattern), **and** the persistent-loop geometry
  — a worker that crashes on input K after N successful inputs makes the
  orchestrator's pipe read fail cleanly (EPIPE/SIGCHLD, no indefinite block)
  and the campaign continues via a fresh worker. Size M.
- **E2b — shm coverage transport + `nelli_cov.c` reset/republish (round-2:
  split from E2).** Replace the interim file-dump read with the shm transport.
  **Shape pinned to push/copy, not zero-copy (round-2 depth/feasibility fix):**
  `nelli_cov.c` **copies** the counter region into a double-buffered shm region
  at end-of-run — the clang inline-8bit-counters are ordinary static globals
  the instrumentation writes in place and cannot be relocated into shm without
  per-target linker-script placement, so a literal "directly-mapped view" is
  not free and is out of scope; the copy model is consistent with per-input
  reset. **Consistency has a named primitive:** an atomic generation/sequence
  word written release-after-copy, read acquire-before-trust; the per-input
  **reset zeroes the *inactive* buffer and atomically flips the active index**,
  so the async-signal-safe crash-time dump can never observe a buffer
  mid-reset (the torn-snapshot hazard between reset and a concurrent SIGSEGV).
  The current `pt_dumped` process-once gate (`nelli_cov.c:65-69`) is re-armed
  per input under this discipline. **dlopen'd modules:** state whether the shm
  region unions late-bound counter sections as the file-dump path already does
  (FUZZ_PLAN D1) or accepts a documented shm-path regression for plugin-loading
  targets. Fills the `CoverageProbe.resetsPerRun` contract. **`shmProbe` is the
  first `CoverageProbe` impl whose producer can be mid-write at `read()` time
  (round-3 design fix — `inProcessProbe` is same-address-space, `sancovFileProbe`
  reads only post-`waitpid`), so state which side drives the reset:**
  `resetsPerRun` is a **pure capability flag** and the reset action is entirely
  **worker-internal** (the worker resets+republishes between inputs, unprompted;
  the orchestrator never triggers a reset through the seam). `read()`'s only
  cross-process obligation is the acquire-before-trust generation check, safe
  under the read-before-redispatch invariant (see Track E execution-model bullet).
  This keeps `CoverageProbe` at two methods with no new orchestrator-triggered
  reset verb — the interface genuinely holds rather than straining. Size M–L.
- **E3 splits (round-3 feasibility fix): E3's old single M–L estimate was fixed
  *before* E0 chose its serialization, but the branches differ wildly in cost —
  an advisory file lock wraps the existing RMW, whereas the a-priori-favored
  delta log drags in a new on-disk log format + atomic compactor + the
  sequence-number cut point U2 needs. One estimate cannot be right for both, so
  the E0-independent work is separated from the E0-contingent work:**
  - **E3a — freshness machinery (E0-independent).** Worker recycling + pristine
    re-verification (admission-gating, report-preserving per §0; the bounded
    async `reproRate` sampler on its bounded slot budget); the `fork`-per-input
    recycling option (single-threaded builds only) with the captured-once
    snapshot invariant. **Structural tests are pure algebra, not raced processes
    (round-2 feasibility fix):** order-independence/merge-fold claims are tested
    by feeding fabricated `Coverage`/admission sequences to the `Orchestrator`'s
    fold logic in arbitrary permutations and asserting permutation-invariance —
    deterministic under `dt-bounded.sh`, *not* by spawning real concurrent
    processes (the timing-dependent class the codebase forbids). RED-able claims:
    a state-leaking property cannot produce a false admission (contaminated
    candidate discarded on re-verify); the fold is order-independent; re-verify
    divergence is recorded, not overwritten. Size M.
  - **E3b — corpus/frontier persistence discipline per E0's chosen design
    (E0-contingent; size assigned *after* E0 concludes, not before).** The real
    orchestrated corpus/frontier discipline (single-writer serialized admission,
    in-memory crash-dedup, mid-campaign seed refresh, seed-in-flight marking).
    **If E0 selects the delta log, E3b's scope explicitly includes the compactor
    and the sequence-number cut point U2 depends on** — that must not surface for
    the first time inside U2. The *numeric* throughput-scaling claim lives in the
    §Evaluation ablation harness. **Size fixed at M (E0 selected the delta log,
    2026-08-25).** Concrete scope: the `<key>.corpus.log` append/replay
    reader-writer (records `addCorpus|tombstone|resetBulk`, replay applying
    `db.nim`'s `dedupPrepend` newest-first/cap semantics so the corpus contract
    is byte-identical to today's); the size-triggered compactor
    (`logBytes > ratio × liveSetBytes`); the generation-file + head-pointer +
    reader-lease publish scheme; and the `.bin` orchestrator-funnel for shrink
    writes. **Stated invariant (E0 F-1): the orchestrator constructs the DB
    handle exactly once and shares it — no worker slot constructs
    `directoryBasedDatabase` on the shared dir** (concurrent constructors race on
    the startup tmp-sweep). The snapshot cut point U2 consumes = (pinned
    generation, byte-offset), record-atomic; E3b delivers it so it never first
    surfaces inside U2. Windows arm of the swap is design-complete here, coded at
    E4a/E4b. See `docs/rfc/0003-fuzzer-nextgen.E0-findings.md`.
- **E-cleanup — campaign-level resource lifecycle (round-2 breadth fix; a
  standalone slice after E3b — round-3 resolves the "may fold" (feasibility
  minor): an unattended loop can silently skip an unresolved either/or, so it is
  its own slice, not folded).** Persistent workers introduce OS resources the OS
  does **not** reclaim on a hard kill: POSIX `shm_open` segments linger in
  `/dev/shm`, named pipes and Windows Job Objects/handles leak, and workers
  blocked on a pipe read can outlive a `Ctrl-C`'d/OOM-killed orchestrator
  forever. Apply the existing precedent (`db.nim:436` already sweeps orphaned
  `.tmp.<pid>.<tid>` files): a **campaign-startup sweep** of stale shm/pipes
  keyed like the tmp-file sweep, **`JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`** on
  Windows, and **`PR_SET_PDEATHSIG` + process-group kill** on POSIX so workers
  die with the orchestrator. **Also carries the steady-state respawn-storm
  breaker (round-3 breadth fix):** the §Open-items circuit-breaker only catches
  *bootstrap* failure (dead-before-first-read). A worker that boots fine then
  dies systemically after ~2 inputs *every* recycle (corrupt environment, a leak
  in the harness itself, shm/disk exhaustion) never trips it — the pool respawns
  in a tight loop forever, burning process-creation cost and flooding crash-dedup
  with environment artifacts. Add a distinct post-bootstrap breaker: track
  per-slot crash rate over a rolling window and, when it exceeds a bound *and*
  dedup shows the crashes are **not diversifying** (same `CrashInfo.kind` every
  time — distinguishing an environment fault from the desirable found-a-good-
  crash-lineage case, which the reporting path already handles well), degrade to
  a paced respawn/backoff or abort with a distinct diagnostic. Size S.
- **Eci — Windows toolchain, CI *and* local (infra prerequisite for
  E4/E5).** The current `symex-windows.yaml` leg is symex-only: no C/C++
  compiler, no `--threads:on`, a hand-curated `tsymex_*` array. Install a
  Windows C toolchain (clang-cl for ABI parity, per the coverage fallback),
  wire cincludes, add `--threads:on`, and generalize the test array beyond the
  fixed symex list. **Must upgrade the *local* bounded-run container too
  (round-2 feasibility fix), not only the CI yaml:** an unattended `/loop`
  grinding E4a–c needs fast local `dt-bounded.sh` feedback, or it either stalls
  polling the slow remote array or silently declares GREEN off a non-Windows
  compile that never touches `CreateProcess`/named pipes/Job Objects. If the
  local container genuinely cannot host the Windows toolchain, E4a–c are marked
  **human-gated push-and-wait** (not unattended-grindable). **That determination
  must be a durable, greppable artifact the loop reads, not prose (round-3
  feasibility fix):** the local-toolchain question is only answered *during* Eci,
  so it doesn't exist at slicing time for a `/loop` preflight to consult — the
  mis-grind risk materializes at exactly the moment it's discovered live. Eci's
  DoD therefore **emits a checked-in capability flag** (a `docs/`-tracked marker
  or a handoff-doc field) the moment the answer is known, and **E4a–c's own
  `/tdd` invocation checks it as a precondition** — hard-stopping with an
  "awaiting Windows push-and-wait" message rather than attempting a local RED
  cycle that cannot exercise `CreateProcess`/named pipes/Job Objects. Size S–M.
- **E4a — Windows worker: re-entry + `CreateProcess` round-trip.** The
  call-site macro's worker-mode entry proven on Windows (no fork — the worker
  *must* reconstruct via the captured construction expressions) +
  `CreateProcess` spawn and named-pipe input/verdict round-trip, no coverage
  yet. **Platform-independent logic sits behind a thin seam so it is Linux-
  testable (round-3 breadth fix — the E3 "algebra, not raced processes"
  precedent extended to Windows glue):** frame parsing, argv call-site-ID
  dispatch, the circuit-breaker consecutive-failure counting, and Job-Object
  limit-threshold *policy* are factored from the actual `CreateProcess`/
  Job-Object/named-pipe syscalls, so that logic gets fast local `dt-bounded.sh`
  RED-GREEN on Linux and only the OS-call glue itself is gated to the Windows
  leg — narrowing "human-gated push-and-wait" to the genuinely-Windows-only
  syscall surface. Size M.
- **E4b — Windows shm coverage.** `CreateFileMapping`+`MapViewOfFile`
  live-mapped transport; the `nelli_cov.c` reset path on Windows. Size M.
- **E4c — Windows limits + crash mapping.** Job Object memory/CPU/wall-clock
  limits (`TerminateJobObject`), unhandled-exception-filter → `CrashInfo`
  (`ckWinException`) mapping, `vResourceExceeded` tagging. Un-gates the
  external tier to Windows. Runs on the Windows CI leg. Size M.
- **E5 — external tier onto the seams.** Port `externalTarget` /
  `differentialTarget` / `fuzzBinary` to `Worker`/`Pool` (POSIX + Windows),
  shm coverage where available, file-dump fallback preserved. **Windows
  N-inputs-per-worker requires the target to expose a persistent-mode loop**
  (libFuzzer-driver style — no `fork` to lean on); ordinary one-shot
  `main()` targets stay spawn-per-input on Windows via the file-dump path,
  stated as a documented throughput asymmetry, not an equivalence. Size M.

**Track E exit gate.** Structure-aware fuzzing is crash-isolated on both
platforms; external fuzzing runs on Windows; the one-time byte-mode
throughput sanity comparison vs libFuzzer/AFL++ (§Evaluation) is recorded.
Everything downstream has an isolated, fast executor to build on.

---

## Track G — guidance: the concolic bridge + cmp-correspondence

Depends on Track E. This is the differentiated capability.

### G-concolic — choice-space concolic bridge

**Decision (grill-resolved): symbolic variables are the draws, not the
parameter values.** Rejected alternative: run `symexFind` on the property
to get parameter values, then invert the strategy to find a choice sequence
producing them. Inversion is an unbounded second research problem (trivial
for `arbitrary[int]`, intractable for filtered/flatMapped/recursive
strategies) and Z3 can return values outside the strategy's image; encoding
the image as constraints *is* the choice-space problem, so value-space is a
lossy detour.

**Mechanism.** A new walker **mode** — concolic-along-a-trace, not
whole-proc exploration, so `symexFind`'s API is untouched:

1. Take a corpus entry (a concrete `seq[ChoiceNode]`) whose execution
   borders an uncovered frontier edge.
2. Replay it, making each recorded draw a **fresh symbolic variable** with
   its declared constraint attached (`drawInteger(min,max)` → a symbolic
   int with `min ≤ v ≤ max`; boolean/float/bytes analogously).
3. Execute `generate ∘ property` along the entry's **concrete path**,
   collecting the path constraints the walker can model. Anything the
   walker cannot model — closure-heavy strategy combinators are the known
   boundary; N3 of the parser RFC documented where the walker degrades on
   nested routines — is **concretized** to its observed value
   (SAGE/QSYM-style aggressive concretization).
4. Ask Z3 for a model that satisfies the prefix constraints but **flips**
   the target branch predicate.
5. The model **is** a choice sequence (each symbolic draw → its solved
   value, in order), structurally valid by construction. Inject it as a
   corpus seed.

**Mechanism clarifications (round-1 fixes).**

- **Where the AST comes from (RESOLVED — §Open items "opaque-closure
  boundary").** `Strategy.run`/`prop` are runtime **closures** with no
  retrievable AST, so "execute `generate ∘ property` in the walker" cannot
  start over a closure *value*. The concolic-capable entry is therefore a
  **`macro` that captures the property expression at the call site** (named
  proc *or* inline `proc(x) = …` literal — wider than `symexFind`'s
  symbol-only contract); only properties threaded in as opaque closure values
  are `sfNotApplicable` for concolic. G1 slices to this macro entry.
- **Frontier *selects the entry*; the walker trace *identifies the branch*.**
  Step 1's "borders an uncovered frontier edge" is not bitmap-slot
  arithmetic — `CoverageFrontier` is a flat hashed array with acknowledged
  C1/C2 collisions and no adjacency concept, so a slot cannot *be* the branch
  address. The frontier (via stall detection, G3) chooses *which corpus entry*
  to hand the bridge; the concrete branch to flip is identified from the
  **walker's own trace** of that replay (the untaken sibling arm), not from
  the coverage map. Any use of `edgeSources` for selection must handle a slot
  resolving to 2+ source locations.
- **"Additive mode" is threaded-through, not bolted-beside.** Concolic-along-
  a-trace makes the walker follow the *concrete* arm at every
  `if`/`case`/`while` decision instead of its normal fork/`ite`-merge search;
  that decision lives *inside* the same per-construct dispatch every existing
  (individually ADR/CR2-pinned) arm implements. Realistically this is a
  `mode: wmExplore | wmFollowConcrete` parameter threaded through that shared
  dispatch — so G1 is sized as *touching* dispatch (audited for verdict drift
  like every other walker-arm change), not as reading beside it. The
  "collisions limited to shared helpers" framing in §Cross-RFC handoff is
  corrected accordingly.
- **Strategy-combinator transparency is the yield ceiling, and needs its own
  slice.** `map`/`filter`/`flatMap` (`strategy.nim`) compose opaque closures;
  under the mechanism as stated, the draw→branch symbolic link severs at the
  *first* combinator — and `map` is the most common one users write, so the
  G2 yield taxonomy would be dominated by "combinator opacity" from day one.
  The earlier `RFC-fuzzer-hybrid.md` draft carried a **transparency
  descriptor** per combinator so an affine `map` stays symbolically
  transparent. The descriptor set is `identity` / affine `a*x+b` /
  **`predicated`** (identity plus an appended Z3 conjunct) / `span-composite` /
  `opaque`. **`predicated` is a round-2 addition:** `filter`'s accept-path is
  "identity, and `predicate(x)` holds" — without this category `filter`
  (ubiquitous: `integers().filter(...)`) falls through to `opaque` and severs
  the link for exactly a combinator G6 exists to rescue. **The descriptor that
  matters is the *composed* one from draw to branch (round-2 design fix):**
  real strategies chain (`.map(f).map(g).filter(p)`), so G6 must define a
  composition algebra — `identity ∘ x = x`; `affine ∘ affine = affine`;
  `predicated ∘ t = t` with the conjunct carried; anything `∘ opaque = opaque`;
  `span-composite ∘ affine` per the span rule — and compute the chain's
  descriptor, not any single combinator's in isolation (else G6 solves only the
  single-combinator case while the yield taxonomy stays dominated by
  multi-combinator chains). **The algebra must be *closed* and its operator
  *directed* (round-3 design fix — the round-2 rule list is neither).** (i) **Pin
  `∘`'s direction** (left-to-right pipeline order vs right-to-left mathematical
  composition): it is unstated, and it matters the moment three-plus combinators
  chain. (ii) **Give the full rule table, not five representative rows** — real
  orderings need the mixed cases the round-2 list omits (`affine ∘ predicated`,
  `predicated ∘ affine`, `predicated ∘ predicated` conjoining both predicates,
  `span-composite ∘ predicated`); "closed" means every ordered pair of the
  category set maps to a category, proven, not asserted sufficient. (iii) **Add a
  `branching` descriptor for the enumerable-`flatMap` case:** `flatMap` chooses
  the *next* strategy from the prior draw's value — under the five categories it
  can only collapse to `opaque`, which is right for an unbounded dependency but
  needlessly pessimistic when the split is a small statically-enumerable case set
  (`x.flatMap(v => if v mod 2 == 0: intRange(0,10) else: intRange(10,20))`),
  exactly the shape the walker's own fork/`ite`-merge dispatch already models
  elsewhere. `branching(cases: seq[(Constraint, Descriptor)])` composes as an ITE
  over its branch descriptors and falls back to `opaque` the instant a case is
  itself opaque or the split isn't finite/enumerable — so G6 doesn't silently
  cede a case the engine is already equipped for. Scope this as **G6** (or fold
  into G1's ADR): the descriptor mechanism and its composition algebra are a
  first-order determinant of the metric G2 commits to, not an optional polish.

**Why this is shippable, not a research program.** The bridge needs
**neither soundness nor completeness**, because Track E's pristine
re-verification replays every injected seed concretely and admits it only if
it *actually* covers new frontier. A wrong model wastes one candidate. So
concretize freely; grow yield by widening the walker fragment over time,
forever. Honest consequence to state in the ADR: **stage-1 yield
concentrates on constraints where drawn primitives flow fairly directly into
property branches** — which is exactly the magic-byte/comparison class the
fuzzer is blind to today (§Ground truth 5), so the first prize is the right
one.

**Yield: what it means and how the design earns its grade.**

*Yield* is the fraction of concolic invocations that produce a seed which
actually covers new frontier. It is bounded because the walker can only
symbolically model a **fragment** of Nim: when a drawn value flows through
unmodeled code (a closure-heavy strategy combinator, an unmodeled stdlib
call) before reaching the target branch predicate, that operand gets
concretized and the symbolic link from *draw* to *branch* is severed —
Z3 can no longer solve for a draw value that flips the branch. So yield is
low in absolute terms early (the fragment is narrow) and highest exactly
where a primitive draw flows fairly directly into a comparison (the
magic-byte class).

A naive design "accepts low yield." The best-in-class design instead makes
the limitation **graceful, visible, and systematically shrinking** — three
mechanisms, all of which are the real content of this decision:

1. **Optimistic solving (QSYM's key idea), safe here by construction.**
   When the full path constraint is unsatisfiable or partly unmodelable,
   do **not** give up — drop the hardest/unmodeled conjuncts and solve a
   **relaxation** (e.g. satisfy just the flipped-branch predicate, ignore
   some prefix constraints). The relaxed model may violate a dropped
   constraint and reach a different path than intended — but Track E's
   pristine re-verification replays it concretely and admits it only if it
   *does* cover new frontier. Elsewhere optimistic solving is a calculated
   gamble that costs a wasted exec; here the "corpus never lies" invariant
   makes it **free of soundness risk**. The failure case is a discarded
   candidate; the subtler case is an *admitted* one that covered new frontier
   via a path unrelated to the targeted flip — still sound (re-verification
   confirmed real coverage), but with misleading concolic provenance, which is
   why the yield metric separates intended-branch from unrelated-coverage
   admits (mechanism 2) rather than counting every admit as a concolic win.
   This turns "can't solve the exact constraint" from a zero-output failure
   into a still-often-useful partial result, the single biggest lever on
   effective yield.
2. **Yield is measured and reported, never hidden — and typed, not
   stringly (round-2 design fix).** The bridge emits a **concolic-yield
   metric** per campaign: invocations, exact-solves, optimistic-solves, unsat,
   unmodeled-concretized, and — crucially — a breakdown of *why* an invocation
   failed. That "why" is **keyed by the walker's own construct-kind enum**
   (the same discriminant G1's `wmExplore | wmFollowConcrete` dispatch already
   switches on), i.e. `Table[WalkerConstructKind, FailureCounts]`, **not** a
   free-text label read back out by prose-matching — reintroducing the exact
   stringly-typed anti-pattern round 1 removed from `CrashInfo` would be worse
   here, since this taxonomy *drives automation* (the prioritized walker-
   widening work-list). Two outcome buckets round-2 adds: **`solved-but-
   superseded`** (a correct solve for an edge a sibling worker covered by
   ordinary mutation before injection — distinct from unsat/unmodeled, else it
   reads as an unexplained `newEdges: 0` non-admission); and, within
   optimistic-solve *successes*, **`admitted-via-intended-branch` vs
   `admitted-via-unrelated-coverage`** (a relaxed model can be admitted for
   coverage unrelated to the targeted flip — counting it as concolic "success"
   inflates the exit-gate conversion rate without reflecting real constraint-
   directed guidance; checkable by comparing the injected trace's actual taken
   branch against the targeted one). A hidden limitation reads as "the fuzzer
   covered everything"; an instrumented one turns the failure log into the
   work-list — the same "no silent caps — `log()` what was dropped" discipline
   the rest of the codebase holds.
3. **The fragment widens on shared investment.** Every walker improvement
   that serves `symexFind` (the parser-normalization RFC's whole thesis was
   widening exactly this) *also* raises concolic yield, and vice-versa —
   the bridge's failure log tells `symex` which constructs to model next.
   Yield growth is therefore not a separate research budget; it rides
   investment the engine wants anyway.

**Exit gate, consequently, is capability + instrumentation, not a
percentage.** Track G passes when (a) the ablation harness's magic-byte and
multi-byte-constant targets — unsolvable by mutation and by pre-G nelli —
are solved by the bridge (G2) and independently by I2S (G5); (b) the
concolic-yield metric is emitted and its failure taxonomy is populated; and
(c) the optimistic-solving fallback is proven to convert at least the
constructed relaxation cases into admitted seeds. A raw "solves X% of all
uncovered branches" bar is explicitly rejected: it is unfalsifiable (the
denominator is unknowable), it punishes the design for the walker's current
breadth rather than the bridge's quality, and it hides the very taxonomy
that makes the limitation shrink.

**Relationship to Shape A.** This bridge is the keystone. #127
(coverage-guided + SMT concolic) and #130 (`arbitrary(myProc)`) become thin
user-facing surfaces over it in a follow-on RFC; they are **not** rebuilt
independently. #125/#128/#132 are unaffected.

**Slices.**

- **G1 splits (round-3 feasibility fix): a slice whose own risk mitigation is
  "check midway whether the ground moved under you" is signaling it is not one
  atomic RED-GREEN-REFACTOR unit. Round-2 offered "sub-slice tighter" but never
  took it; round-3 does, along the seam the mechanism already describes** — which
  also shrinks each SW-bump window and makes a failing-arm audit bisectable:
  - **G1a — thread `mode: wmExplore | wmFollowConcrete` through the dispatch
    (mechanical).** Every existing walker arm gets its concrete-guidance branch,
    each with an independent characterization pin (no verdict drift vs `wmExplore`)
    that can land arm-by-arm. No draw-symbolication yet. These small mechanical
    diffs tolerate a mid-flight SW rebase without invalidating half-finished work.
    Size M.
  - **G1b — draw-symbolication + concrete-trace constraint collection.** Symbolic
    roots from recorded draws, path-constraint collection along the concrete
    trace, aggressive concretization at the walker boundary. No branch-flipping
    yet — pin that the collected constraints are satisfied by the original
    concrete input (soundness-of-collection characterization). **Bounded trace
    length (round-2 breadth fix):** a recursive/streaming strategy can draw
    unboundedly many `ChoiceNode`s, growing the symbolic-variable count and Z3
    formula without limit; G1b caps trace length (graceful truncation past the
    cap, counted in the yield taxonomy) so a large corpus entry cannot make
    collection non-terminating. Short enough not to need a mid-slice checkpoint.
    Size M.
  Both rebase against live SW at start (per the pre-flight check), but neither is
  long enough to require the round-2 mid-slice checkpoint the monolithic G1 did.
- **G2 — branch-flip solve + choice-sequence materialization + optimistic
  fallback + yield metric.** Pick an uncovered frontier edge bordering the
  trace, negate its predicate, solve, materialize the model as a
  `seq[ChoiceNode]`. When the exact constraint is unsat/unmodelable, fall
  back to **optimistic solving** (drop the hardest/unmodeled conjuncts,
  solve the relaxation) — safe because Track E re-verifies concretely.
  **Optimistic solving is bounded (round-2 feasibility fix):** a fixed
  `maxRelaxationAttempts`, a deterministic drop order (not a `2^n`-subset
  search), and a per-attempt Z3 timeout — Z3 non-termination is an established
  hazard here and `dt-bounded.sh` exists to bound exactly this. Emit the
  **typed concolic-yield metric** with its failure taxonomy. Tests: a
  magic-byte gate (`if drawnInt == 0xCAFEBABE`) that mutation cannot pass is
  passed by the concolic seed within one invocation; a constructed relaxation
  case yields an admitted seed via the optimistic path; **a pathological
  fully-unsolvable case terminates within the bound** rather than hanging or
  enumerating; the metric counters (incl. the intended-branch vs
  unrelated-coverage split) are populated. Size M–L.
- **G3 — orchestration: stall detection + seed injection.** When the
  frontier stalls K rounds, select a border input, invoke the bridge, feed
  results back through Track E re-verification into the corpus. **Stall
  detection reads the *orchestrator-wide* frontier, not a worker-local view
  (round-2 depth fix):** with N workers sharing the one frontier, a per-worker
  stall count would fire the bridge for an edge a sibling is concurrently
  covering by mutation (the `solved-but-superseded` outcome); Pool-wide stall
  state avoids the redundant invocation. Energy accounting for concolic-derived
  seeds **depends on S1** (Entropic energy); if G3 ships first with a
  placeholder constant energy, the revisit is tracked as **G3b — wire real
  Entropic energy post-S1** (a real checkbox, not a subordinate clause that
  slips). The yield-metric failure taxonomy is surfaced as the walker-widening
  work-list. Size M.

### G-cmp — IR-level comparison correspondence (RedQueen, typed)

Independent of G-concolic; a cheaper, always-on complement.

**Mechanism.** Instrument comparison operations to log operand pairs
(`trace-cmp` for external targets; a `{.cover.}`-sibling for Nim targets),
then apply **input-to-state** correspondence against the **typed choice
nodes** — integer *and* bytes/string (`ckBytes`/`ckString`), so the
multi-byte-constant gate (`if bytes == "MAGIC"`, the natural byte-comparison
representation) is in scope, not just wide-integer comparisons — rather than
guessed byte offsets. nelli knows which draw produced which value, so the
"find this operand in the input and replace it with the other" step is exact.
**Boundary (round-1 fix):** "exact, not heuristic" holds for the
*identity-flow* class — where the compared value equals a drawn value
unmodified. Once a draw flows through a transform (arithmetic, a derived
length, a checksum) before the comparison, the operand→choice-node lookup
fails just as byte-level RedQueen's does once bytes are transformed; the
typed-provenance advantage removes the byte-offset guessing problem, it does
not extend past identity flow. Harvested operands also seed an
**auto-dictionary** for the mutator (Track S).

**Slices.**

- **G4 — cmp instrumentation + operand log.** `trace-cmp` runtime for the
  external tier; the Nim-tier comparison hook; the per-run operand-pair
  log over shm. Size M.
- **G5 — IR-level I2S replacement + auto-dictionary.** Map logged operands
  back to choice nodes, apply the RedQueen replacement as a mutator,
  harvest a per-campaign dictionary. Test: a multi-byte constant gate is
  solved by I2S without the concolic bridge. Size M.

**Track G exit gate.** Magic-byte/constant-gate corpus targets that neither
random mutation nor pre-G nelli can pass are passed — by concolic (G2) and
by I2S (G5) independently — proven in the ablation harness.

---

## Track S — scheduling: energy + adaptive mutation

Depends on Track E; interleaves with Track G/U.

- **S1 — Entropic energy.** Replace the `+1.0` lineage bonus with a
  Böhme-style information-gain schedule: energy ∝ the rarity of the edges an
  input reaches (favor inputs exercising globally-rare frontier slots),
  with an execution-cost term (favor fast, small inputs). Subsumes the
  opt-in `powerSchedule` flag. **S1 owns the shared frontier-statistics
  sub-object; G3 consumes it (round-3 breadth fix).** S1's per-edge rarity and
  G3's orchestrator-wide staleness/stall state are both derived statistics
  layered on the *one* `CoverageFrontier`; if each track adds its own fields in
  separately-landing slices, a merge silently drops one or the two disagree on
  update timing (e.g. rarity updates on `admit()` but the stall check reads a
  pre-`admit` snapshot in the same tick). S1 introduces a single incrementally-
  maintained `FrontierStats` sub-object (rarity counts + last-improved
  sequence-number per region) updated at the one `admit()` site; G3 reads it
  rather than rescanning or duplicating bookkeeping. Recorded in ADR-0031 D4
  alongside the `score`/`admit` split. Size M.
- **S2 — operator bandit.** Replace uniform choice over the five IR
  mutators (and G5's I2S operator) with a multi-armed bandit weighting each
  operator by its recent admission yield (MOpt in spirit). Size M.
- **S3 — havoc stacking + interesting-value tables.** Stack 1–N mutation
  ops per iteration (geometric count), add an interesting-value table for
  integer choice nodes (min/max/±1/0/powers-of-two/off-by-one), wire the
  G5 dictionary into insertion. Absorbs the FUZZ_PLAN D4 byte-havoc gap at
  the **IR** level (constraint-respecting), where it belongs. Size M.
- **S4 — continuous corpus culling.** Promote `minimalCovering*`
  (`fuzz.nim:368-395`, today a one-shot end-of-run set-cover) to a
  periodic in-campaign culling of dominated corpus entries, favored-set
  computation à la AFL. **This also governs the *persisted* corpus
  (round-1 fix):** `saveCorpus`'s on-disk eviction is today purely
  recency-based (`dedupPrepend`, `db.nim:324-348`), so it can drop a
  rare-edge seed for newer redundant ones — precisely the failure S4 exists
  to prevent, made worse by Track E's higher parallel admission rate against
  the 256-default `corpusLimit`. S4 makes disk admission/eviction
  coverage-value-aware, not recency-only; if that proves too invasive for one
  slice, S4 explicitly scopes to in-memory and files the disk-eviction
  mismatch as a stated limitation rather than leaving it silent. Size S–M.

- **S5 — campaign observability surface (round-2 breadth fix).** `fuzz`'s
  contract is open-ended/wall-clock-scheduled — the shape of workload where an
  operator needs live telemetry, and the RFC otherwise instruments only the one
  narrow concolic-yield metric. Emit an AFL-`fuzzer_stats`-equivalent campaign
  surface from the orchestrator: execs/sec, corpus size over time, frontier
  coverage, per-worker health/respawn counts, time-since-last-new-coverage,
  time-since-last-crash. Read-only, sourced from the single orchestrator's
  in-memory state, so no new synchronization. **S5's first cut is
  E-tier-only; the concolic-yield + seed-provenance breakdowns are a G2-gated
  second part (round-3 feasibility fix):** those two fields are *defined in G2*
  (Track G), but Track S only "interleaves with G/U" — so if S5 lands before G2,
  its DoD can't include them. S5a emits the executor/corpus/frontier/health
  fields (no G dependency); S5b folds in the concolic/provenance breakdowns once
  G2 lands. Size S.
- **S6 — learned-state checkpoint/resume (round-3 breadth fix).** `fuzz`'s
  open-ended/wall-clock contract means routine interruption (Ctrl-C, OOM-kill,
  CI timeout, E-cleanup's own crash-recovery) and restart. The *corpus* persists
  via `ExampleDatabase`, but S1 rarity/energy, S2 bandit weights, S3/G5 harvested
  dictionary, and S4 favored-set are all in-memory orchestrator state — every
  restart silently cold-starts them, discarding hours of schedule learning on
  the exact long-running workload the contract exists for. S6 periodically
  persists this (small, cheaply-serialized) learned state alongside the corpus
  and reloads it at campaign start, keyed like the corpus so a rebuilt binary
  starts fresh. **Following S4's own pattern, if full persistence proves too
  invasive for one slice it scopes down and files the rest as an explicit stated
  limitation** ("learned scheduling state does not survive restart; only the
  corpus does") — never silent. The corpus (the expensive asset) always
  persists; S6 recovers the cheap-but-slow-to-relearn scheduling state on top.
  Size S.

**Track S exit gate.** Ablation shows each of energy, bandit, and havoc
stacking independently improves time-to-coverage on the harness; none
regresses determinism of the `forAll` contract (Track U); a live campaign
emits the S5 observability surface.

---

## Track U — unification: one engine, two front doors

Depends on Track E; independent of G/S.

**Decision (grill-resolved): two front doors, one engine — contracts
distinct, machinery shared.**

- `forAll`'s contract stays **bounded, deterministic, CI-safe**: fixed
  example budget, reproducible from seed, exits. `fuzz`'s contract stays
  **open-ended, wall-clock-scheduled, corpus-accumulating**. The
  distinction is the *contract*, not the machinery.
- Everything beneath unifies so capability never diverges again: the
  bucketed `CoverageFrontier` becomes the **single** coverage model,
  replacing `forAll`'s scalar `__coverage__` Pareto label (FUZZ_PLAN D10);
  the `Worker`/`Pool` seams, mutators, `ExampleDatabase`, and shrinker are
  shared.
- **`forAll` gains crash isolation too (round-2 design/breadth fix).** Ground
  truth 1 indicts `forAll`'s `coverageGuided` path as in-process/no-isolation
  — a property `Defect` is fatal to the whole run — yet round-1 Track U touched
  only the coverage/corpus layer, leaving the *higher-traffic* front door
  crash-fatal forever while `fuzz` got isolation. Since E1 already builds an
  in-process `Worker` that is a drop-in for `inProcessTarget`, `forAll` routes
  through a **single in-process `Worker` under a bounded (single-worker) `Pool`**
  — crash-isolated per example, no cross-worker concurrency, `forAll`'s
  deterministic/bounded contract fully preserved. "Two front doors, one engine"
  then holds all the way down (execution included), not only at the
  coverage/corpus layer. This is a Track U slice (U0) with its own exit-gate
  line and D4 record; if per-example spawn latency proves too costly for
  CI-bounded runs, the in-process `Worker` runs **without** fresh-process
  isolation (still catching `Defect`s via the seam's boundary) as the stated
  fallback, never silent.
- `forAll` gains **replay-only** reads of the persisted fuzz `corpus`
  section as extra deterministic seeds (no campaign-state mutation, no
  coverage-energy feedback into the deterministic run) — most of the
  unification value at **zero** determinism cost. This is the honest,
  bounded form of Hypothesis's "one engine," chosen deliberately over full
  unification (which would import fuzz nondeterminism into the deterministic
  contract — an anti-feature for CI). **Snapshot policy (round-1 fix):**
  because a live fuzz campaign may be appending to the same
  `persistKey`/`targetId` corpus, `forAll` **snapshots the corpus once at run
  start** and reads only that snapshot; the determinism guarantee is "same
  seed + same corpus *snapshot* → same example order," and the snapshot read
  must not race a concurrent `saveCorpus` RMW (it goes through the same E0/E3
  serialization primitive). Reproducibility across campaign *time* (the
  corpus grew overnight) is explicitly **not** promised — the seed +
  captured-snapshot pair is the reproducibility unit.

**Slices.**

- **U0 — `forAll` through the in-process `Worker`.** Route `forAll`'s
  execution through a single in-process `Worker` under a bounded `Pool` so a
  property `Defect` is caught (crash isolation) instead of aborting the run;
  `forAll`'s bounded/deterministic contract unchanged. Determinism pin: same
  seed → same example order through the seam. Depends on E1. Size S–M.
- **U1 — unify the coverage model.** Route `forAll`'s `coverageGuided` onto
  the bucketed frontier; retire the duplicated scalar path and the
  duplicated integer-perturbation kernel (`fuzzir.nim:39-51` vs
  `targeting.nim:154-168`, split only to avoid a fuzz↔engine cycle the
  `Worker`/`Pool` seams now resolve). **Separate scoring from admission
  (round-1 fix):** `CoverageFrontier.admit` is mutating and first-time-only
  (re-admitting the same coverage yields `newEdges: 0`), but `forAll`'s
  targeted phase compares Pareto scores repeatedly across hill-climb steps —
  routing per-example *scoring* through `admit()` would collapse a re-scored
  input's value to 0 and corrupt dominance. U1 introduces a single non-mutating
  **`score`** query for scoring (round-3 renamed from `wouldAdmit` — three
  near-homonyms `wouldAdmit`/`tryAdmit`/`admit` across two types were confusable;
  the non-mutating query is `score`, the only "admit" verbs left are the two
  mutating ones, `CoverageFrontier.admit` and `Orchestrator.admit`); the
  mutating `admit()` stays the corpus-mutation call only. **Ver: may bump SW** if
  the targeting Pareto surface changes — CR2 pin discipline applies. Size M.
- **U2 — `forAll` replay-only corpus reads.** `given`/`forAll` load the
  persisted fuzz corpus as deterministic seeds ahead of the random phase;
  no state mutation. Determinism pin: same seed + same corpus → same
  example order. Size S–M.
- **U3 — byte-mode demotion.** Fold byte-mode into interop-only
  (`importCorpusDir`/`exportCorpusDir`), remove the parallel weak
  admission path; the spec'd-but-absent `dictionary` extension point is
  satisfied at the IR level by S3, so the byte-level one is dropped, not
  built. Doc/code drift (`INTERFACE.md:145`) reconciled. Size S.

**Track U exit gate.** One coverage model in the tree; `forAll` is
crash-isolated (a property `Defect` no longer aborts the run) and reads the
fuzz corpus deterministically; byte-mode is interop-only; no `forAll`
determinism regression.

---

## Evaluation — how "best-in-class" is held accountable

A PhD-grade design proves each tier earns its complexity. Committed,
CI-runnable, per the "committed tests, never one-time greps" doctrine.

- **(i) Ablation benchmark — the primary deliverable.** A committed harness
  of Nim targets with seeded, categorized defects: magic-byte gates,
  multi-byte constant gates, deep state machines, structural-validity
  walls, arithmetic-relationship bugs. Measures time-to-find and
  coverage-over-time with each tier toggled (executor throughput; concolic
  on/off; I2S on/off; energy schedule; bandit; havoc). **Each track's exit
  gate includes its ablation cells going green.** **Its execution environment
  is defined, not implicit (round-2 breadth fix):** because these are
  wall-clock/execs-per-sec measurements — exactly the timing-dependent class
  the codebase forbids as *unit* tests, which is why they live here and not in
  `dt-bounded.sh` — the harness states its **cadence** (nightly/release-gated,
  not per-PR), a **repetition + statistical-tolerance policy** (K runs, a green
  cell must clear the threshold with margin against noisy-neighbor CI variance,
  not a single lucky run), and that **Windows and Linux cells are scored
  separately** (the spawn-per-input file-dump path and the POSIX shm path are
  not interchangeable, so a Linux-only harness cannot gate E4c's Windows exit
  criteria). This is its own committed slice, distinct from correctness runs.
- **(iii) Downstream-bug scoreboard — informal.** A section in the RFC
  tracking real defects found in real Nim projects. Most honest signal,
  unfalsifiable on a schedule — informational, not a gate.
- **(ii) External baseline — one-time, not standing.** A single byte-mode
  sanity comparison vs libFuzzer/AFL++ on shared C targets at the Track E
  exit, to confirm the external tier is in the right order of magnitude.
  **Not** maintained as a standing FuzzBench-style fixture — that is a
  project unto itself and would benchmark the non-differentiated tier.

---

## Configuration surface (round-3 breadth fix)

The tracks introduce a dozen-plus new knobs — `reproSamples`,
`maxRelaxationAttempts` + per-attempt Z3 timeout, the {fuzzing, re-verify,
reproRate-sample, shrink, concolic-solve} slot budgets, worker count, the G1b
trace-length cap, the fork-recycling N-inputs threshold — atop the existing
`corpusLimit`. Ground truth #6 documents where ungoverned config growth already
bit once: `dictionary` was spec'd in `INTERFACE.md:145` yet absent from the real
`FuzzSettings` — a doc/code drift born of adding a setting nowhere coherent. To
not repeat it: each track's knobs live in **one nested config object per track**
(`ExecutorConfig`, `GuidanceConfig`, `SchedulingConfig`) hung off `FuzzSettings`,
never scattered ad hoc onto whatever struct is nearest; slot budgets that are
`Orchestrator` policy live on an `OrchestratorPolicy` sub-object. **Binding rule
(closes the ground-truth #6 drift class going forward, not just once): any slice
that adds a knob updates `docs/fuzz/INTERFACE.md` and the real settings type in
the *same* slice** — an unregistered setting is the config analogue of the C1
unregistered-pin lesson. Recorded as an ADR-0031 sub-decision.

## Version-pin & DoD discipline (inherited, binding)

- **SW (`symexWalkerVersion`, `smt/canonicalize.nim`).** Track G's concolic
  mode reads the walker; if it changes any verdict or cache-key surface it
  bumps SW and updates+runs the `tsymex_phase15_CR2_cachekey.nim` `==` pin
  **in the same slice**, serialized against the live base (per the
  `symex-version-bump-cr2` memory). Track U's U1 may bump SW if the
  targeting surface changes. **G1/G2 and U1 must serialize their SW bumps
  against *each other*, not only against the parked chapulin RFC (round-1
  fix)** — two concurrent agent sessions both touching SW would collide on the
  CR2 pin. **Enforced mechanically, not socially (round-2 feasibility fix):**
  every SW-bumping slice's DoD runs a **pre-flight check** at slice start —
  diff the CR2 pin's expected literal against the currently-committed
  `symexWalkerVersion`; if it has moved since the branch was cut, hard-fail and
  force a rebase before proceeding, so an unattended `/loop` cannot silently
  build a bump on a stale base. **A start-only check cannot catch two slices that
  both start from the *same* unbumped base concurrently (round-3 feasibility
  fix):** each one's start diff passes (SW hasn't moved from either vantage), and
  the collision only surfaces when the second commits its bump onto a base the
  first has since moved — the G1a/G1b-vs-U1 same-RFC race the "serialize against
  each other" rule names. Close it two ways: (1) **re-run the identical CR2-literal
  diff immediately before the final commit** of any SW-bumping slice, not only at
  start; and (2) a **claim marker** — a checked-in lock file / branch-name
  convention naming the in-flight SW-bumping slice — that a second SW-bumping
  slice's pre-flight detects and hard-fails on, shrinking the race window from
  whole-slice-duration to near-zero. Incidental pins stay `>=` floors. Most of
  Tracks E/S/U touch fuzz-only code and **do not** bump SW.
- **Both-backend green** on touched-path suites; new test files registered
  in `nelli.nimble`'s test task (the C1-review lesson: an unregistered pin
  never runs); bounded runs only (`scripts/dt-bounded.sh`); full sweep
  (`scripts/psweep.sh`) before commit for SW-bumping slices; watch the
  `sweep-waiter-self-match` hazard.
- **Windows CI leg** (`.github/workflows/symex-windows.yaml`, hand-curated
  array): Track E's Windows worker (E4) and every external-tier slice are
  first-class candidates for that array — platform divergence is precisely
  the class it exists for. Executor-level tests must run there.
- **Behavior-identical slices must prove it** (E1 behind the seam; U-slices
  that claim no verdict change): no verdict/key drift on the existing
  corpus.

## Release planning

Fuzz-only, no-SW slices ride patch releases. SW-bumping slices (G1/G2 if
bumped, U1 if bumped) serialize their CR2 literal against the live tip.
**0.4.0/0.5.0 stay reserved** for the parked chapulin RFC's Track A/B exit
releases — do not collide. This RFC's own milestones map to track exits
(E → G → S/U), release labels assigned at slicing-finalization once the
chapulin reservations are confirmed still-held.

## ADR plan (house `D`-lettered convention)

**ADR-0031** — next free after ADR-0030 (parser-normalization); stub lands
with E1 so interleaved work cannot claim the number while later sub-decisions
are pending — *the fuzzer is one engine with a portable isolated executor at
its floor; the corpus never lies (every candidate re-verified pristine)*:

- **D1** (with E1/E2): the **`Worker`/`Pool` two-seam** model — **centralized
  orchestrator topology (round-2):** the `Pool` is one orchestrator process
  owning the single in-memory frontier/corpus/dedup/scheduler + the single Z3
  bridge, dispatching to dumb worker processes; admission single-writer
  serialized (no worker disk-write race); federated `-M`/`-S` is the out-of-
  scope cross-node design. Coverage via the existing `CoverageProbe` seam;
  typed `CrashInfo`; `Observation` immutable single-execution (aggregates —
  `reproRate`, `divergentReproduction`, provenance — on the persisted record);
  workers-are-processes-never-threads; persistent-worker + freshness-by-
  recycling-and-re-verification via `Orchestrator.admit`; `INV-fresh-exec` as an
  observation-boundary guarantee. Re-verification **gates admission, not
  reporting** — **`reproRate` is a bounded async N-of-M sampler (round-2)**,
  the **first report is immutable and a re-verify `CrashInfo.kind` mismatch is
  recorded as `divergentReproduction`, never an overwriting dedup key
  (round-2)**; the **parked snapshot is captured once, pre-input**, and
  **`fork()`-recycling is gated to single-threaded worker builds, CRIU named as
  the threaded alternative (round-2)**. Records the **call-site macro
  worker-entry** — two contracts split (syntactic AST for G, semantically-
  reconstructible constructor for E), compile-time free-identifier check with a
  naming error, **argv call-site-ID dispatch (not env var)**, isolated-proc
  reconstruction (no in-situ side-effect replay), and a bootstrap
  circuit-breaker — resolving the opaque-closure boundary for Track E.
  **Round-3 additions:** the type is `Orchestrator[T]` (not `Pool`); its
  execution model is one single-threaded completion loop (completion-oriented
  `Worker` seam, no thread-per-worker) with the Z3 bridge, fresh-spawn re-verify,
  and `reproRate` sampling all off the hot dispatch path on bounded slot budgets
  like shrink; read-before-redispatch is a named, pinned per-worker invariant.
  `Orchestrator.admit(input, candidate)` takes the replayable input (re-verify
  re-executes it — an `Observation` alone cannot); cross-execution aggregates
  (`reproRate`/`divergentReproduction`/provenance) are read by `FindingId`
  handle, never on `admit`'s one-shot return; `CrashInfo`'s common `message`
  field precedes the case. Crash-dedup indexes kind → findings observing it as
  primary *or* divergent variant. The macro's compile-time check adds a
  best-effort impurity denylist on captured initializers (environmental-impurity
  residual documented as a stated limitation); a steady-state respawn-storm
  breaker complements the bootstrap one; the worker-reconstruction capability is
  proof-spiked at E1, not first exercised at E2a.
- **D2** (with E4): the Windows worker (CreateProcess+pipes+shm+Job Objects).
  **No fork-equivalence claim (corrected):** Windows N-inputs-per-worker
  requires a target-side persistent-mode loop; ordinary one-shot targets stay
  spawn-per-input on Windows — a stated throughput asymmetry, and the
  `nelli_cov.c` per-input reset is the enabling C-runtime work.
- **D3** (with G1/G2): the choice-space concolic bridge — draws-as-symbols,
  aggressive concretization, replay-validated injection, the
  soundness/completeness-not-required argument, **optimistic solving made
  soundness-free by re-verification** (round-2: **bounded** —
  `maxRelaxationAttempts` + per-attempt Z3 timeout + deterministic drop order),
  and the yield-metric-not-percentage exit-gate doctrine (round-2: the metric
  is **typed by walker construct-kind**, not free-text, with `solved-but-
  superseded` and intended-branch-vs-unrelated-coverage buckets). **Records the
  resolution of the opaque-closure entry contract** (§Open items), the
  frontier-selects-entry/walker-identifies-branch addressing (round-2: stall
  detection reads the orchestrator-wide frontier), the concrete-guidance-
  threaded-through-dispatch sizing, the combinator transparency descriptor (G6,
  round-2: adds the `predicated` category for `filter` + a chain-composition
  algebra), the bounded concrete-trace length, and the G-cmp identity-flow
  boundary. **Round-3: G6's algebra is closed and its `∘` operator directed —
  full rule table over the category set plus a `branching` descriptor for the
  enumerable-`flatMap` case; G1 splits into G1a (thread the mode through
  dispatch, mechanical) / G1b (draw-symbolication + bounded trace); the Z3 bridge
  runs off the orchestrator's hot dispatch path.**
- **D4** (with U0/U1): one coverage-frontier model with **`score`/`admit`
  separated** (round-3 rename from `wouldAdmit`; non-mutating scoring vs
  mutation); two front doors, one engine
  **all the way down** — **`forAll` routed through the in-process `Worker` for
  crash isolation (round-2)**, not only sharing the coverage layer; `forAll`
  replay-only corpus reads over a **once-captured snapshot** with a precise
  sequence-number cut point against the append-only log; *why not* full
  unification, and *why not* trajectory-reproducible parallel campaigns.
  **Round-3: S1 owns the shared `FrontierStats` sub-object that G3 consumes (one
  owner, no parallel-slice drift).**

## Cross-RFC handoff

- **Shares `smt/` with the parked chapulin RFC.** Track G reads the walker
  at the live SW; rebase + re-read `symexWalkerVersion` before G1, exactly
  as the chapulin cross-RFC handoff requires of Track B. If the chapulin
  round-6 walker work resumes concurrently, the concolic mode is a **new
  mode** — but, corrected in round 1, it is a `mode` parameter *threaded
  through* the shared per-construct dispatch (follow the concrete arm instead
  of fork/`ite`-merge), **not** additive code beside untouched arms. Every
  existing arm is read and gets a concrete-guidance branch, so it is audited
  for verdict drift like any walker-arm change; collisions with concurrent
  chapulin walker work are correspondingly wider than "shared helpers" and
  are resolved by rebase + the CR2 pin discipline.
- **Feeds Shape A.** After G lands, Shape A #127/#130 are follow-on
  surfaces over the bridge; a future Shape A RFC references ADR-0031 D3
  rather than re-deriving the mechanism.

## Resolved forks (from the design grill — recorded, no longer open)

1. **Scope = (a1).** Structure-aware Nim-native tier is the product;
   external tier un-gated to Windows via the shared seam,
   instrumentation-required; no DBI. Stretch path to (b) in §Appendix B.
2. **Windows first-class.** Executor is portable from day one; not a
   follow-on port.
3. **Execution = persistent worker pool**, freshness by recycling +
   pristine re-verification; POSIX `fork()` demoted to a recycling policy.
   `CreateProcess`+IPC recovers amortized-init; re-verification recovers
   per-input freshness at the observation boundary.
4. **Hybrid = choice-space concolic**, not value-space + strategy
   inversion. Aggressive concretization; models are choice sequences;
   `symexFind` untouched (new walker mode).
5. **Two front doors, one engine.** Contracts distinct (bounded/
   deterministic vs open-ended/accumulating); machinery unified;
   `forAll` gains replay-only fuzz-corpus reads; **not** full Hypothesis
   unification.
6. **Evaluation = committed ablation harness** with per-track exit gates;
   informal downstream scoreboard; one-time byte-mode external comparison
   at Track E exit; no standing external baseline.
7. **Shape A relationship.** Fuzzer RFC owns the bridge; #127/#130 become
   thin surfaces later; supersedes the "#124 next" recommendation.

## Open items (awaiting Corey)

- **RESOLVED — the opaque-closure boundary (round-1 escalation; Corey
  2026-08-14: "pre-v1, breaking changes fine if they're improvements; want
  best-in-class whatever it ends up being").** The problem was real: nelli's
  inputs are opaque runtime closures, and two tracks need to see through
  them. Track G's concolic walker needs the property's **AST**, but
  `Strategy.run`/`prop` are `{.closure.}` values Nim cannot recover source
  from at runtime. Track E's fresh-`exec`'d worker cannot inherit those
  closures either (POSIX `fork` hides it; Windows cannot). **Resolution — one
  decision solves both: the concolic-capable entry is a `macro` that captures
  the property (and strategy-construction) *expression at the call site*, not
  a `proc` taking closure values.**
  - **Track G gets the AST for named procs *and* inline literals.** A macro
    receiving `fuzz(myStrategy, proc(x: int) = check f(x))` has that lambda's
    AST directly — strictly wider than `symexFind`'s symbol-only `getImpl`
    contract. Only a property arriving as an already-constructed closure
    *value* threaded through indirection stays `sfNotApplicable` for
    concolic — a far narrower exclusion than "must be a named symbol." Such
    targets still get crash-isolation + I2S + scheduling, just not concolic.
  - **Track E gets worker reconstruction with *no new user-facing API*.** The
    same macro emits a hidden worker-mode entry at the call site: launched in
    worker mode, it re-runs the captured construction to rebuild
    strategy+property and enters the worker loop instead of the normal driver.
    The common `fuzz(...)` call site is unchanged and double-serves;
    `nelli.workerMain` is *not* a symbol the user must call.
  - **Two contracts, not one — split them explicitly (round-2 design fix).**
    Track G's need is **syntactic** (capture the expression's AST; if the
    walker can't model it, degrade to `sfNotApplicable`, no user surprise).
    Track E's need is **semantic**: the captured construction must be *safely
    re-executable, unmodified, in a fresh OS process*. These are different in
    kind and the round-1 "one deep-module win" framing conflated them. The
    macro therefore lifts strategy/property construction into a **module-scope-
    reconstructible isolated proc** invoked directly in worker mode — it does
    *not* replay the program from `main` to the lexical call site (which would
    re-run every intervening test's side effects on every spawn, a correctness
    *and* throughput hazard). **"Cannot be reconstructed" is detected at
    compile time, not by a runtime worker crash:** the macro classifies the
    captured expression's free identifiers against module scope and, on one not
    reconstructible there (an enclosing `let`, a proc param, a runtime-config
    value, a mutable global), emits a **compile error naming the offending
    identifier** ("`fuzz`'s strategy expression captures `n` from an enclosing
    scope; worker re-entry needs a module-scope-reconstructible expression —
    hoist `n` to a `const`, or this target runs fork-only").
    - **Scope-classification catches scope facts; environmental impurity is a
      *purity* fact and needs its own mechanism (round-3 depth fix — the one
      Critical).** "Enclosing `let`," "proc param," and "mutable global" are
      syntactic/scope facts a free-identifier walk decides directly. **"A
      runtime-config value" is not** — `let p = getEnv("X")` and `let p =
      "/fixed"` are *identical* under a scope-only walk (both module-scope,
      non-`var`, no enclosing/param free identifiers), yet the first reconstructs
      to a different value in a worker spawned with a different environment / at a
      different time / after a different RNG seed. A scope-only check therefore
      does **not** make "silent success with drifted values" impossible for this
      class; it silently narrows to the scope-obvious cases. The macro must
      additionally run a **best-effort impurity check on each captured binding's
      initializer**: flag an initializer that transitively reaches a known-impure
      stdlib symbol (`getEnv`/`paramStr`/`readFile`/`getTime`/`rand`/global-RNG
      reads — a maintained denylist, checked through called procs, not just the
      top-level call) and emit the same naming compile-error. This is
      best-effort, not sound (an impure proc outside the denylist, or impurity
      behind an indirect call, slips through), so the **residual is documented as
      a stated limitation** (the honest pattern S4 uses): module-init impurity the
      denylist misses reconstructs a possibly-drifted strategy with no compile
      error and no runtime diagnostic — the bootstrap circuit-breaker catches
      dead-before-first-read, not silently-different-but-live. Silent drift is
      thereby *unlikely and mostly-caught*, not "impossible."
  - **Dispatch is an argv call-site ID, not an inherited env var (round-2
    design fix).** A binary has many `fuzz`/`forAll` sites; a bare boolean
    env-gate cannot say *which* to re-enter, and env vars are inherited by
    grandchildren (a fuzzed CLI/FFI target that shells out could inherit
    "I am a nelli worker"). The `Pool` already owns the `CreateProcess`/
    `posix_spawn` call, so it passes an explicit `--nelli-worker=<callsite-id>`
    argv flag — the same channel that hands the worker its IPC handles.
    Call-site-keyed dispatch also makes **nested `fuzz`/`forAll` safe**: an
    inner call is not this worker's keyed site, so it never self-triggers
    worker mode (otherwise a non-goal to document).
  - **Bootstrap failure is distinct from a per-input crash (round-2 breadth
    fix).** If reconstruction itself dies *before the worker reads its first
    input*, no worker of the pool can ever start — categorically different from
    a property crash on a submitted input, and it must not be misattributed to
    whatever input was first in the pipe or spun on forever. The `Pool` runs a
    **circuit-breaker**: N consecutive dead-before-first-read spawns abort the
    campaign with a `construction-not-reentrant` diagnostic (the runtime
    symptom of the degradation path the compile-time check aims to prevent, for
    the residue it cannot catch statically — e.g. a non-reentrant side effect
    in construction). Degradation target when reconstruction is known-impossible
    remains POSIX-fork-only / Windows-spawn-per-input.
  - **The deep-module win, restated precisely:** call-site macro capture hands
    the AST to the walker *and* a module-scope-reconstructible constructor to
    the worker — one boundary, two *distinct* capabilities with two *distinct*
    degradation stories (G: `sfNotApplicable`; E: compile-error or fork-only).
    Supersedes the grill's "symexFind's API untouched" framing. Binds G1 and E1
    slicing; recorded in ADR-0031 D1 (worker entry) and D3 (concolic entry).
- **RESOLVED — Umbrella issue = #158.** Filed 2026-08-14. #151's
  execution-model items (worker-pool fan-out; byte-havoc/dictionary) fold
  into #158 per the #151 disposition comment; #151 keeps its remaining
  hygiene items.
- **RESOLVED — Parallel campaign is v1 (fork 2).** Many workers, one shared
  evolving corpus, single-node; de-risked by the E0 spike. Cross-node
  distributed stays out (#112). See Track E goal.
- **RESOLVED — Concolic yield framing (fork 3).** The exit gate is
  **capability on the targeted class + a measured, reported yield metric +
  an optimistic-solving fallback**, not a yield percentage. See §Track G
  "Yield: what it means and how the design earns its grade" and ADR-0031
  D3. Not a blocking bar.

## Risks acknowledged (from the grill)

- Persistent-worker contamination is *mitigated* (recycling +
  re-verification), not eliminated — accepted, since it can only waste
  candidates.
- Stage-1 concolic yield is bounded by the walker's strategy-code coverage;
  early wins concentrate on draws flowing directly into branch predicates.
- MSVC `/fsanitize-coverage` capabilities for the external tier on Windows
  need empirical verification during Track E (E4/E5); the **named fallback**
  is clang-cl (ABI-compatible with `nelli_cov.c`), or a coverage-blind
  Windows external tier as graceful degradation — see Track E Instrumentation.
- The persistent worker cannot inherit the user's runtime `Strategy`/`prop`
  closures across a fresh `exec` (Windows especially); **resolved** by the
  call-site macro worker-entry (§Open items). Residual risk: targets whose
  strategy/property construction is *not* re-runnable degrade to
  POSIX-fork-only / Windows-spawn-per-input — acceptable, stated.
- The ablation harness is a standing maintenance commitment, and is itself a
  wall-clock measurement — its cadence/tolerance/per-platform-scoring policy
  (§Evaluation i) is what keeps it from becoming a flaky gate.
- **`fork()`-recycling is unsafe under multi-threaded worker builds (round-2):**
  only the calling thread survives the fork, so a lock held by a GC/allocator
  helper or `--threads:on` thread freezes every child. Mitigated by gating
  fork-recycling to single-threaded builds; CRIU is the named future path for
  threaded builds.
- **Centralized-orchestrator admission is a serialization point (round-2):**
  accepted — admission cost is negligible beside execution at single-node
  worker counts, and the correctness/elegance win (one owner of frontier /
  dedup / energy / Z3) dominates. If it ever bottlenecks, federated `-M`/`-S`
  is the cross-node escape hatch (#112), not a v1 concern.

## Non-goals

- Fuzzing uninstrumented third-party binaries (DBI/WinAFL class) — §Appendix
  B stretch only.
- A standing external FuzzBench-style baseline.
- Cross-**node**/distributed campaigns (the corpus-backend #112 umbrella is
  a separate concern). Single-node **parallel multi-worker** IS in scope
  (Track E, de-risked by the E0 spike).
- Changing `forAll`'s deterministic contract (Track U is explicit about
  preserving it).
- **Bit-reproducible parallel *campaign trajectories* (round-1 fix).** With N
  workers racing to admit into a shared frontier/corpus under OS-scheduling
  nondeterminism, the *sequence* of admissions/discoveries is not
  reproducible run-to-run, and making it so is not a goal. What **is**
  guaranteed is that every individual admitted/crashing input is reproducible
  via its choice sequence + pristine re-verification — which is what
  debugging actually needs. (Contrast `forAll`, whose whole contract is
  trajectory-determinism; the two front doors differ here by design.)
- **Workers as OS *processes*, never Nim *threads* (round-1 fix; pinned in
  ADR-0031 D1).** `coverage.nim:127-131`'s `edgeSourceTable` is unlocked and
  single-threaded-by-contract; running workers as threads inside one
  instrumented binary would silently reintroduce that race. Process-per-worker
  is a correctness requirement, not a performance preference.
- PIT-style mutation *testing* (`src/nelli/mutation.nim`) — unrelated
  feature, not fuzz input mutation.

## Appendix B — stretch path to full option (b) (someday, not now)

If uninstrumented-binary fuzzing ever becomes a goal, the path is
incremental on this RFC's substrate, not a rewrite:

1. **Byte-level trace-cmp/RedQueen** for instrumented externals — the G4/G5
   machinery generalized from IR nodes to byte offsets (heuristic I2S, as
   AFL++ does it).
2. **Auto-dictionary from byte cmp operands** — the S3 dictionary fed from
   byte-level cmp logs.
3. **DBI coverage provider** (TinyInst/DynamoRIO on Windows; equivalent on
   Linux) — a new implementation behind the **same** `CoverageProbe`/
   frontier interface. This is the only genuinely new architecture, and it
   slots in as another coverage source; the `Worker`/`Pool` seams, scheduler,
   corpus, and shrinker are untouched.

## Appendix C — core signatures (sketch; frozen at slicing, not before)

Illustrative, so ergonomics is reviewed as code rather than prose (round-2).
Names/fields firm up per slice; this pins the *shapes*. **Round-3 reworked the
admission surface after the design lens found three signature defects (see
below).**

**Naming pinned here (round-3 design fix).** The singleton that owns the one
frontier/corpus/dedup/scheduler/Z3-bridge is the **`Orchestrator[T]`**, not a
`Pool` — "pool" connotes an interchangeable passive collection, but this type
is a decision-making singleton. The *worker pool* is the `seq[Worker[T]]` it
owns. Earlier prose still says "the `Pool`"/"orchestrator" interchangeably;
`Orchestrator[T]` is the canonical type name. "Campaign" = one
`Orchestrator[T]`'s run-to-exit lifetime (S5/E-cleanup use it in that sense).

```nim
# Track E — the two seams. Worker is a dumb execution engine; Orchestrator is
# the singleton that owns all concurrency, scheduling, and the Z3 bridge.
type
  Worker[T]       = ref object    # 1:1 process wrapper, spawn-once
  Orchestrator[T] = ref object    # owns the worker pool + the one frontier/corpus/dedup

  Verdict = enum
    vOk, vRejected, vInteresting, vTimedOut, vResourceExceeded, vCrashed

  CrashInfo = object              # typed — matched on `kind`, never prose-parsed
    message: string               # human rendering, derived — never keyed on;
                                  # common field MUST precede the case (Nim rule)
    case kind: CrashKind
    of ckSignal:       signal: int
    of ckWinException: code: uint32
    of ckExitCode:     exitCode: int
    of ckException:    defect: string     # Nim Defect name

  Observation = object            # ONE execution, immutable once built
    verdict: Verdict
    crash: Option[CrashInfo]
    coverage: CoverageDelta
    nanos: int64

  # Completion-oriented worker seam (round-3): a single-threaded Orchestrator
  # drives N workers WITHOUT a thread per worker — submit is non-blocking, the
  # Orchestrator waits on many at once. Blocking `submit` is a convenience
  # wrapper used only by E1's single-worker reference impl and forAll's Pool-of-1.
  WorkerHandle[T] = object        # in-flight ticket; carries the submitted input
  Provenance = enum pvMutation, pvConcolic, pvI2S, pvImported
  FindingId = distinct int        # handle into the orchestrator-owned finding record

  AdmitResult = object            # returned ONCE by admit(); no async fields here
    admitted: bool
    findingId: Option[FindingId]  # set iff a finding/corpus record was opened
    provenance: Provenance

proc submitAsync[T](w: Worker[T], input: ChoiceSeq): WorkerHandle[T]
proc poll[T](o: Orchestrator[T]): seq[(Worker[T], ChoiceSeq, Observation)]
  ## completions ready this tick; input returned so re-verify can replay it
proc submit[T](w: Worker[T], input: ChoiceSeq): Observation   # blocking convenience wrapper

proc admit[T](o: Orchestrator[T], input: ChoiceSeq, candidate: Observation): AdmitResult
  ## re-verify RE-EXECUTES `input` in a fresh worker (candidate is only a cheap
  ## pre-filter — hence input is passed, not recovered from the Observation);
  ## fresh-spawn re-verify + serialized admission live HERE, not in the fuzz loop.
  ## The re-verify spawn draws from a bounded slot budget (round-3), like shrink.

# Cross-execution aggregates live on the orchestrator-owned finding record and
# are READ back by handle — never smuggled onto admit()'s one-shot return
# (round-3 design fix: reproRate/divergentReproduction evolve as async samples
# land; a returned-once struct cannot be "updated as samples land").
proc reproRate[T](o: Orchestrator[T], id: FindingId): float         # N/M; 1.0 == always
proc divergentReproduction[T](o: Orchestrator[T], id: FindingId): seq[CrashInfo]

# Frontier — scoring separated from mutation (Track U). Non-mutating query is
# `score`, not `wouldAdmit` (round-3: kills the wouldAdmit/tryAdmit/admit
# near-homonym trio; the only "admit" verbs left are the two mutating ones).
proc score(f: CoverageFrontier, c: CoverageDelta): Score            # non-mutating
proc admit(f: var CoverageFrontier, c: CoverageDelta): AdmitDelta   # mutating primitive

# Track G — yield taxonomy keyed by the walker's own construct enum, not strings
type
  YieldOutcome = enum
    yoExactSolve, yoOptimisticIntended, yoOptimisticUnrelated,
    yoUnsat, yoUnmodeledConcretized, yoSupersededByRace
  ConcolicYield = object
    outcomes: array[YieldOutcome, int]
    byConstruct: Table[WalkerConstructKind, int]   # the walker-widening work-list

# User-facing surface is UNCHANGED — `fuzz` is the macro; the worker entry and
# the AST capture are emitted behind it. A non-reconstructible capture is a
# COMPILE error naming the identifier, not a runtime worker crash:
fuzz(myStrategy, proc(x: int) = check invariant(x))
```
