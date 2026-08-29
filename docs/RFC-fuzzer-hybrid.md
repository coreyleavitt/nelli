> **SUPERSEDED (2026-08-14) by `docs/RFC-fuzzer-nextgen.md`.** This is an
> earlier same-day draft of the same fuzzer work, kept only as a design-notes
> reference: the round-1 architecture review salvaged two ideas from it that
> nextgen had dropped — the `WorkerPool`/wire-protocol split (now nextgen's
> `Worker`/`Pool` seams) and the per-combinator **transparency descriptor**
> (now nextgen's G6). Do **not** treat this file as live; the authoritative
> RFC is `RFC-fuzzer-nextgen.md`.

# RFC: Hybrid structure-aware fuzzer

## Status

- **Draft — stage 1 (first pass), 2026-08-14.** Decision basis: the
  `/grill-me ideal:` session of 2026-08-14 (all forks resolved by Corey;
  synthesis table reproduced in §2). Architect rounds not yet run.
- Handoff: `docs/RFC-fuzzer-hybrid.handoff.md`.
- Supersedes the Shape A (#124) next-work recommendation: this RFC owns the
  symex↔choice-sequence bridge; #127/#130 become thin surfaces over it in a
  follow-on RFC. #125/#128/#132 are unaffected.
- Relationship to the Windows-side chapulin-hardening RFC: none shared —
  this RFC does not touch `dsl_parser.nim` parse paths or walker verdict
  semantics (see §8 versioning). The two programs may land in either order.

## 1. Motivation and current-state assessment

nelli's fuzzing subsystem has a mutation core that is architecturally ahead
of its peers — constraint-respecting choice-IR operators and span-aware
structural crossover, inherited for free from the PBT choice-sequence
substrate (`fuzzir.nim`, `datasource.nim`) — wrapped in execution and
guidance tiers that are roughly 2013-era AFL-classic:

1. **The missing quadrant: structure-aware × crash-isolated.** The
   structure-aware path runs properties in-process with no isolation — a
   segfault (FFI, memory corruption) kills the whole campaign, and under
   `--panics:on` even an `IndexDefect` is fatal and unshrinkable
   (`engine.nim:54-60`). The isolated path (`externalTarget`) exists only
   for separately-built binaries, essentially byte-mode. You can have
   structure-aware mutation OR crash isolation, never both.
2. **Windows has no external tier at all.** Everything from `fuzz.nim:858`
   down (`runChild`, `externalTarget`, `differentialTarget`, `fuzzBinary`,
   oracles, resource limits) is `when defined(posix)`.
3. **Spawn-per-input execution.** `runChild` pays fork+execvpe+3 temp
   files+mkdir/rmdir+file-based coverage dump for every single input —
   a 100–1000× throughput gap against forkserver/persistent-mode peers.
4. **Coverage is admission-only.** The bucketed frontier
   (`coverage.nim:315-370`) is a diversity filter; there is no energy
   model beyond an opt-in `+1.0` lineage bonus, no favored-seed
   computation, no information-theoretic scheduling.
5. **No comparison guidance.** Magic-byte/constant-comparison branches
   (`if h == 0xCAFEBABE`) are statistically unfindable — no trace-cmp, no
   RedQueen-class input-to-state correspondence, no dictionaries (the
   `dictionary` field in `docs/fuzz/INTERFACE.md:145` was never
   implemented — doc/code drift).
6. **Uniform mutator choice.** Five IR operators picked uniformly
   (`fuzz.nim:534-547`); no per-operator success feedback.
7. **The symex engine is disconnected.** A mature source-level symbolic
   executor (walker v73, Z3) lives in the same library and shares zero
   machinery with the fuzzer.

Gap 7 is the opportunity that defines this RFC. Every published hybrid
fuzzer (SAGE, Driller, QSYM) fights two wars nelli does not have to fight:
they symbolically execute **compiled binaries** because that is all they
have, and they solve constraints over **raw bytes** and then struggle to
keep solved inputs structurally valid. nelli has a symbolic executor that
speaks the source language, and an input representation — the choice
sequence — whose draws are already typed, range-constrained variables. A
`drawInteger(min, max)` IS a symbolic integer waiting to happen; a Z3 model
over draws IS a structurally valid input by construction. No system in the
literature has this substrate. The mandate is to build the fuzzer that
substrate makes possible.

## 2. Resolved decisions (normative)

These were resolved in the 2026-08-14 grill session and are the fixed
points of this RFC. Changing one is a wrong-spec escalation, not an edit.

| # | Decision | Resolution |
|---|----------|------------|
| D1 | Driver | Best-in-class PhD-level design mandate; consumer reports are context, not drivers |
| D2 | Platform | **Windows is first-class, day one** — no capability may be POSIX-only except the fork recycling fast path (an optimization, not a capability) |
| D3 | Execution model | Portable **persistent worker pool**: spawn-once workers (CreateProcess / posix_spawn), inputs streamed over pipes, coverage returned via shared memory, workers recycled every N inputs and on any crash; **pristine-worker re-verification of every admission and every crash report**. POSIX `fork()` is a cheap per-input recycling policy of the same seam |
| D4 | Freshness | `INV-fresh-exec` (FUZZ_PLAN D2) is **reframed at the observation boundary**: long-lived workers may contaminate candidates, never admissions or reports — re-verification in a pristine worker is the invariant's new enforcement point |
| D5 | Scope | **(a1)**: the structure-aware Nim-native tier is the product. External tier is retained, un-gated to Windows via the shared seam, and **requires instrumentation at build time**. Uninstrumented/closed-source binary fuzzing (DBI) is a non-goal (stretch path in Appendix A) |
| D6 | Hybrid architecture | **Choice-space concolic bridge**: draws are the symbolic roots; the walker executes generate∘property along a corpus entry's concrete trace with aggressive concretization; Z3 models materialize directly as choice sequences; every candidate is replay-validated before admission. Value-space (`symexFind` + strategy inversion) is rejected. `symexFind`'s API and verdict surface are untouched |
| D7 | Guidance & mutation | IR-level cmp-correspondence (typed RedQueen), auto-harvested interesting values/dictionaries, havoc stacking, bandit-scheduled operators, Entropic-style information-gain energy |
| D8 | Engine identity | **Two front doors, one engine**: `forAll` stays bounded/deterministic and gains replay-only reads of the persisted fuzz corpus; `fuzz` stays open-ended/accumulating; frontier, mutators, workers, and persistence unify beneath |
| D9 | Shape A | This RFC owns the bridge; #127/#130 become thin follow-on surfaces |
| D10 | Program shape | One RFC, four tracks: **E** (executor) → **G** (guidance); **S** (scheduling) and **U** (unification) interleave after E |
| D11 | Evaluation | Committed, CI-runnable **ablation benchmark** with seeded, categorized defects; each track's exit gate includes its ablation cells green. Informal downstream-bug scoreboard. One-time byte-mode sanity comparison vs libFuzzer/AFL++ at Track E exit. **No standing external baseline** |

## 3. Non-goals

- Fuzzing uninstrumented third-party binaries (DBI). See Appendix A.
- Byte-level RedQueen / AFL++ havoc parity for external targets (Appendix A
  phase 1–2 if ever demanded).
- Campaign-level determinism under parallel workers. Per-input replay
  determinism (choice-sequence replay) is mandatory and preserved;
  whole-campaign reproducibility is available only in single-worker mode.
- Distributed/multi-machine campaigns (#112's domain — corpus backends
  compose with this design unchanged).
- Replacing `engine/targeting.nim`'s Pareto/SA search (#107). Track U
  unifies the *coverage model*, not the targeting algorithms.

## 4. Track E — portable isolated executor

The prerequisite track: closes the missing quadrant (gap 1), un-gates
Windows (gap 2), and removes the spawn-per-input tax (gap 3). Everything
else builds on its seam.

### Architecture

**`WorkerPool`** — one abstraction, three implementations:

- `loopbackPool` (test-only): runs the worker protocol in-process against
  the real codec; every protocol/pool behavior is unit-testable without
  process machinery.
- `spawnPool` (portable, the reference implementation): workers are the
  harness binary re-executed in worker mode (`--nelli-fuzz-worker
  <channel-id>`); Windows via `CreateProcess` + named pipes +
  `CreateFileMapping` + Job Objects (memory/CPU caps, kill-on-close);
  POSIX via `posix_spawn` + pipes + `mmap(MAP_SHARED)` + `setrlimit`.
- `forkPool` (POSIX fast path): a parked pre-loop image forked per input —
  recycling-every-input at ~100µs, the strongest freshness at full speed.
  Same seam, same protocol, different recycling economics.

**Protocol.** Length-prefixed frames over the pipe: orchestrator sends a
serialized choice sequence (the existing `ChoiceNode` codec from `db.nim`)
plus a run ID; the worker replays it through the strategy, runs the
property, and replies with a verdict frame (ok / falsified / rejected /
raised{type,msg}) and a coverage epoch counter. Coverage itself never
crosses the pipe: the worker's `{.cover.}` bitmap lives in the shared
memory region, double-buffered per run ID so the orchestrator reads a
consistent snapshot without synchronization on the hot path. Worker death
(pipe EOF / process exit) is itself a verdict: the orchestrator captures
exit code, exception code (`STATUS_ACCESS_VIOLATION` et al.) or signal,
attributes it to the in-flight run ID, and recycles the worker.

**Crash semantics.** A worker crash is `vInteresting`, never campaign
death. `--panics:on` targets become fully fuzzable (a panic is just a
worker death with an exit code) — this removes the `engine.nim:54-60`
caveat for the fuzz path entirely. Timeout enforcement: Job Object CPU/wall
caps on Windows; `setrlimit` + the existing SIGTERM→grace→SIGKILL
escalation on POSIX.

**Re-verification gate (D4).** Any candidate judged interesting (frontier
admission) or crashing is replayed in a **pristine worker** (freshly
spawned/forked, zero prior inputs) before it is admitted to the corpus,
persisted, or reported. Crash de-dup keys are computed from the *verified*
run's coverage+message, never the dirty run's. Non-reproducing candidates
are counted (`FuzzReport.unreproducible`) but discarded — contamination can
waste candidates, never fabricate results.

**External tier port.** `externalTarget`/`differentialTarget`/`fuzzBinary`
move onto the same pool seam: the "worker" is the target binary itself
(spawn-per-input preserved for targets that cannot loop; a
persistent-mode delivery variant for targets that can), the `posix` gate is
deleted, oracles gain Windows arms (exit/exception codes replacing
signals; `sanitizerOracle` unchanged — ASan exists on MSVC/clang-cl), and
the file-dump coverage transport remains as the fallback for targets where
shm injection is not available.

### Slices

| id | slice | size | notes |
|----|-------|------|-------|
| E1 | Worker protocol codec + `WorkerPool` seam + `loopbackPool` | M | pure-logic TDD; frames, run IDs, verdict mapping, double-buffer discipline |
| E2 | Portable shm region + `{.cover.}` bitmap relocation | M | `CreateFileMapping`/`mmap` wrapper; bitmap writes target the mapped region when in worker mode; zero-cost when off (existing mode-flag discipline) |
| E3 | Worker mode in the harness binary | M | `--nelli-fuzz-worker` entry: pipe loop, replay+run, coverage epoch publish; clean shutdown |
| E4 | `spawnPool` on Windows + POSIX | L | CreateProcess/Job Objects and posix_spawn/setrlimit arms; crash capture; recycle-every-N; timeout escalation |
| E5 | Re-verification gate + crash-key rebase onto verified runs | S | wire into the admission and report paths; `unreproducible` counter |
| E6 | `forkPool` fast path (POSIX) | M | parked pre-loop image; recycling-per-input; same protocol tests must pass unchanged against all three pools |
| E7 | External tier port + un-gate | L | delete the `posix` gate; Windows oracle arms; retire spawn-per-input `runChild` for pooled delivery; file-dump fallback retained |
| E8 | Track E exit gate | M | ablation cells (V-track) green: crash-isolation cell, throughput floor cell (≥50× today's external path on the bench target), Windows parity cell (same cells green in the Windows container); one-time byte-mode sanity comparison vs libFuzzer on two bench C targets, results recorded in this RFC; FUZZ_PLAN D2/D5 amended (`INV-fresh-exec` reframing, shm transport) |

## 5. Track G — guidance (the hybrid core)

### G-a: concolic bridge

**New walker mode, not a change to `symexFind`.** `concolicTrace(program,
choices, targetBranch) → Option[seq[ChoiceNode]]`: execute the captured
generate∘property program with the corpus entry's draws bound as symbolic
roots (each draw contributes its kind + range constraint), following the
**concrete path** the entry took (no forking, no path explosion — one path,
one constraint set), then ask Z3 for a model that flips `targetBranch`.
Any operation outside the walker's supported fragment **concretizes**: the
symbolic value is pinned to its observed concrete value and the walk
continues. The model's draw assignments materialize directly as a
mutated choice sequence.

**Soundness stance.** The bridge requires neither soundness nor
completeness: every produced candidate goes through the Track E
re-verification/replay path and is admitted only if it actually covers new
frontier. A wrong model wastes a candidate; the corpus never lies. This is
what makes aggressive concretization acceptable and the bridge shippable
incrementally — stage-1 yield concentrates on draws flowing directly into
property branches (exactly the magic-byte class, gap 5), and yield grows
as walker fragment coverage grows, forever, with no architecture change.

**Program capture.** The `fuzz()` entry macro captures the property proc's
IR via the existing `parseEntryImpl` machinery. Strategy code is NOT
symbolically walked in this RFC's stages: strategies are closure-heavy
(the walker's documented weak fragment). Instead, strategies expose an
optional **transparency descriptor** — a per-combinator declaration of how
draws map to produced values (`identity`, affine `a*x+b`, `span-composite`
over children, or `opaque`). `arbitrary[int/uint/bool/float]`, `tuple`,
`map` with affine bodies, and span-structured combinators get descriptors
in this RFC; `opaque` combinators concretize their outputs (their draws
still perturb, they just carry no symbolic constraint into the property).
Full generator symbolication is the recorded end-state beyond this RFC.

**Orchestration.** Stall detection: when frontier admissions per N
executions fall below threshold, the scheduler selects corpus entries
bordering uncovered branches (the frontier knows which slots are
zero-bucket neighbors of an entry's covered slots via `edgeSourceTable`),
and spends a bounded solver budget (wall-clock per invocation + per-cycle
cap) on `concolicTrace` calls. Solved candidates enter the normal
mutation→execution→re-verification pipeline tagged with provenance
(`bridge`) so V-track ablation can measure bridge yield precisely.

### G-b: cmp-correspondence and harvesting

- **Cmp observation**: extend the `{.cover.}` AST pass to also instrument
  comparison operators in the SUT — recording (site-id, lhs, rhs) into a
  bounded shm ring when a comparison involves at least one non-constant.
  This is the source-level analogue of sancov trace-cmp, and like
  `{.cover.}` it is compiler-independent (Windows/vcc for free).
- **IR-level RedQueen**: when a recorded cmp's operand matches a drawn
  value (directly or through a transparency descriptor's affine map),
  patch that draw to the other operand (± the affine inverse) — typ