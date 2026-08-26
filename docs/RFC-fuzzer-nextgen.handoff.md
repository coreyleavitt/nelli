# RFC — next-generation structure-aware hybrid fuzzer — handoff

- **Stage:** 3 (implementation) — architecture rounds 1, 2 & 3 all DONE; **no open forks/escalations.** Grinding slices via `/loop`.   •   **Done:** E0 (corpus-sync spike — verdict recorded), E1 (Orchestrator/Worker seams + macro entry), E2a (POSIX persistent worker), E2b (shm + `nelli_cov.c` reset). **E3a DONE** (`561c86d` C1+C2 finding record + reproRate/divergentReproduction + re-verify-gated `admit` — `spawnFreshWorker`/`reVerify` knobs, default OFF so `fuzz()` and every existing caller are byte-for-byte unchanged; `ea84cee` C3 order-independent-fold pure-algebra permutation tests over fakes; C4 worker recycling policy (`recycleAfterInputs`, crash-forces-recycle) + `fuzzworker.nim`'s new `newForkWorker` (fork-per-input, forks only ever from the live orchestrator process itself, never from a prior child — captured-once by construction) + `tests/tfuzzforkworker.nim`'s characterization test (N forks from one snapshot are state-identical; the ONE process-spawning test in this slice, deterministic/sequential, not raced). The prior "IN FLIGHT: subagent ac53e0991da4c4fbc" note was a stalled agent from an earlier session with zero commits landed — this session took over fresh per the subagent-stall-takeover convention and redid E3a in full. `reportFinding` is the un-gated first-observation report hook (crash reporting is never gated by re-verify per §0); `admit`'s re-verify path is what's gated. Dual-backend (`c`+`cpp`) full `tfuzz*`+`tdb` suite green after every commit, no existing assertion touched.
**E3a verified** 10/10 dual-backend. **E3b — DONE** (6/6 dual-backend verified; C5 `0018a69` committed by agent). Note: E3b never-unlinks superseded corpus generations (GC scope-cut) — FOLDED into E-cleanup's startup sweep (reclaim `.corpus.<gen>.log` not referenced by head; lease-bounded live GC stays U2's). **E-cleanup — DONE** (4/4 dual-backend verified; see the `### E-cleanup — DONE` section below for full detail). C1 `f667bd0` campaign-startup sweep (stale nelli shm segments by prefix + superseded corpus generations vs the head pointer), C2 `f5f81bd` `PR_SET_PDEATHSIG` (workers die with a hard-killed orchestrator), C3 `6a8a174` `isolateOwnProcessGroup`/`killWorkerGroup` (clean-shutdown process-group-kill backstop, reaches a worker's whole subtree), C4 `44db313` steady-state respawn-storm breaker (`Orchestrator.stormWindow`/`stormBackoff`, sliding-window non-diversifying-`CrashInfo.kind` trip, distinct from the not-yet-built E4a bootstrap breaker). **⚠ WINDOWS SLICES BLOCKED — verification-channel fork (surfaced to Corey via push 2026-08-26).** This host is Linux (`os: linux, amd64`); no runnable Windows container exists here (CLAUDE.md's "Windows container" lives on CI/a Windows machine, not this host), and podman/docker on Linux cannot run Windows images. **Eci, E4a, E4b, E4c are Windows-specific and CANNOT be TDD-verified here** — blind-writing untested Windows systems code would violate the quality bar. They are HELD (not done, not skipped-and-forgotten): resume them once Corey provides a channel — authorize a CI push (branch `rfc-fuzzer-nextgen` isn't pushed yet) OR Windows-machine/container access. NOT a deferral of effort; a hard capability gap.
**E5 — DONE** (`755fb39` C1 `newExternalWorker` + shared `choiceSeqTargetWorker` bridge, `290372e` C2 external-tier-through-Orchestrator characterization — zero new prod code, the seam design paid off; 43/43 c + 5/5 cpp verified). **This completes the Linux-verifiable Track E.**
**Lesson (applied to all future briefs): agents MUST run every test synchronously via dt-bounded (blocks + returns exit code), NEVER background a suite run and yield — that orphans uncommitted work (recurred on E1-macro/E3b/E5; resumable via SendMessage to finish).**
**Track G STARTED.** **G1a — DONE** (`3a14b59`): `WalkMode = wmExplore|wmFollowConcrete` on `WalkCtx`, all 21 walker arms get a no-op `case w.mode` seam (wmExplore byte-identical), SW NOT bumped (structure-only, CR2 pin "73" unchanged — correct), `tests/tsymex_g1a_mode.nim` char test, verified synchronously dual-backend. **G1b — DONE** (`3cc275a`): draw-symbolication + concrete-trace constraint collection. `runConcolicCollectImpl(..., maxDraws=256)` in `smt/runtime.nim`: each `ChoiceNode`→symbolic var w/ its declared constraint (reuses `mkIntVar`+`min≤v≤max`); `walkIfFollowConcrete` picks the concretely-taken arm via scratch Z3 solves (draws stay FREE for G2's flip); draw→param linkage is a **caller-supplied `ConcolicParamBinding` (cbDrawLinked|cbConcretized)** — classification deferred to G3/G6 (transparency descriptor), by design. `ConcolicCollectResult.pcSatByConcreteInputs` soundness pin; `ConcolicYieldCounters` (tracesTruncated/paramsConcretized/unsupportedDrawKinds). SW not bumped (wmExplore byte-identical, CR2 "73" unchanged). Verified synchronous dual-backend, no hangs.
**G2 — DONE** (`8bca6e1`): branch-flip solve + materialize + bounded optimistic fallback + yield taxonomy. **Concolic bridge works end-to-end** — magic-byte test: 1 Z3 query materializes `0xCAFEBABE`, replay confirms `ccoIntendedCovered`. `ConcolicBranchRecord`/`runConcolicFlipImpl` (prefixPc ∧ ¬observedTruth), `materializeConcolicModel` (solved draws→ChoiceNode, clamped to declared bounds), optimistic = drop last-k prefixPc conjuncts (deterministic, bounded `min(maxRelaxationAttempts=8, len)`), `z3CheckBounded` (random_seed=0 + timeout on EVERY attempt). Sharp: re-collects on the materialized seed to verify the flip landed (clamp can undo an optimistic flip). SW not bumped (CR2 "73"). Verified synchronous dual-backend, no hangs.

**REORDER (rationale): doing S1 BEFORE G3.** RFC order is G3 next, but G3 consumes S1's `FrontierStats` + energy; doing G3 first needs a throwaway fallback energy + the later G3b rewire (do-it-twice). S1 is independent and the RFC designed it as "owns shared FrontierStats (G3 consumes)"; S/U-interleave is sanctioned. So: **S1 → G3 (real energy, no G3b) → G4 → G5 → G6 → S2/S3/S4 → S5a/S5b/S6 → U0-U3.** G3b is thereby avoided.
**S1 — DONE** (`96b0d84` C1, `eb7f40c` C2, `1b6d7d2` C3). Entropic (Böhme information-gain) power schedule, replacing the coarse recency/lineage `2.0`/`+1.0` scheme. **C1** adds `CoverageFrontier.stats: FrontierStats` (per-slot `hitCounts` + `totalAdmitted` + per-slot `lastImprovedSeq`), folded in at the ONE fold site — `coverage.nim`'s `admit` — never rescanned; structured so G3 adds its orchestrator-wide staleness/stall fields to the SAME object later (round-3 breadth fix), not a sibling one. **C2** adds the pure formula: `rarityWeight(stats, slot) = -log2(hits/totalAdmitted)` (Shannon self-information — chosen over raw `1/hits` for smooth degradation and because it's the literal information-theoretic quantity Entropic is named for), `coveredSlots(c)` (sparse nonzero-slot list, so energy recomputation never rescans the full up-to-8192-slot map), and `entropicEnergy(coveredSlots, stats, sizeChoices, execNanos) = (entropicBaseEnergy + Σ rarityWeight) * executionCostFactor(size, nanos)` — the exec-cost term is a plain `(0,1]` discount favoring fast/small inputs, degrading to size-only when `execNanos <= 0` (no timing signal). `entropicBaseEnergy` floors energy strictly positive so no corpus entry is ever permanently starved. **C3** wires it into the loop: `energy[i]` is recomputed fresh from `frontier.stats` every parent-selection tick (the rarity denominator moves on every admit, so a cached value would go stale) via each corpus entry's frozen `coveredSlots`/size/`corpusNanos`; the loop asks coverage.nim for energy, never recomputes rarity inline. `FuzzSettings.powerSchedule` is GONE — `uniformSchedule: bool` replaces it with inverted default semantics (Entropic is now the unconditional default; `uniformSchedule: true` reproduces the pre-S1 default trajectory byte-for-byte, kept as Track S's future ablation-harness uniform baseline). No test in the suite pinned an exact schedule-dependent trajectory against the old default (checked all `tfuzz*`/`tdb` call sites), so the flip needed no separate determinism gate. `observeInProcess` now measures real wall-clock duration into `Observation.runResult.durationNs` (previously only external targets set it), so the exec-cost term is live for the common in-process path, not just external targets. `tfuzzschedule.nim`'s two `powerSchedule`-dependent tests were rewritten (Entropic-as-default + `uniformSchedule` as the opt-out); `tfuzzfrontier.nim` gained two new suites (`FrontierStats`, `Entropic energy`) with the RFC's four RED-able properties (rare-edge energy > common-edge energy; smaller/faster > larger/slower covering the same edges; hitCounts increments exactly once per admit; lastImprovedSeq advances only on a bucket-raising admit) — no existing assertion in either file was weakened, only the two flag-shaped ones were re-pointed at the new default. Full `tfuzz*`+`tdb` (41 files) verified GREEN dual-backend (`c`+`cpp`) after the final cycle. **Next: Track G** (G1a/G1b/G2 already done — see above; **G3 — DONE** (C1 `641ada0` staleness on FrontierStats @ one fold site; C2 `ecba035` `Orchestrator.concolicBridge`/`tryConcolicBridge` + `admit` provenance param + `ConcolicBridgeEntry`/`ConcolicBridgeResult` type-erased Z3-free mirror keeping fuzz.nim Z3-free; C3 `66b9cd9` wired into `fuzz[T]` loop, concolic seeds through same S1 energy bookkeeping, no G3b placeholder — worked end-to-end with a FAKE bridge). Wiring the REAL bridge against a `{.cover.}`'d property surfaced a walker gap first: **G3fix** `3918eaa` — descending into `recordEdge` (every `{.cover.}`'d proc's own instrumentation) crashed on its free-standing `coverageMode` threadvar (`env[e.vname]` KeyError, no binding for a non-local/non-param name). Two-layer fix: (1) `recordEdge` tagged with a LOCAL `{.symexOpaque.}` pragma in `coverage.nim` (matched by name only, no import needed — keeps `coverage.nim` a leaf module and `fuzz.nim` Z3-free) so the parser routes it through the existing #137 `mkOpaqueCall` graceful path, confirmed already-graceful; (2) `smt/runtime.nim`'s `lower(iekVar)` degrades ANY unresolved free reference to a fresh symbolic havoc, but ONLY in `wmFollowConcrete` (gated via a new forward-declared `isFollowConcreteWalk()`, the `currentWalkCtxPtr` idiom) — `wmExplore` stays byte-identical, CR2 pin unchanged at "73". **C4** `cf3f887` — the real bridge: `fuzzmacro.nim`'s `fuzz(...)` macro now builds a real `ConcolicBridgeEntry` closing over the captured `propSym`, running `concolicFlip` with a minimal positional `cbDrawLinked` classifier (one binding per property param; G6 does full classification later) and translating the real outcome/coverage taxonomy into fuzz.nim's erased mirror types — unconditionally wired but inert unless `settings.stallRounds > 0`. `fuzzmacro.nim` now imports AND re-exports `nelli/symex` (anticipated in G3 C2's own doc comment) — the re-export was load-bearing: without it, macro-generated code for any property touching a construct outside the narrow tsymex_*-exercised set (a free global var read, a raw FFI call) failed to compile for any `import nelli`-only caller. Headline (`tests/tfuzzconcolicbridge_real.nim`, real Z3, real `{.cover.}`, plain `import nelli`): a `stallRounds: 1` campaign over a `{.cover.}`'d `0xCAFEBABE` gate reaches `coverageHits == 2`; the identical campaign at the `stallRounds` default (0) stays at `1`. Passed first try. Full `tfuzz*`/`tdb` + a broad `tsymex_*` sweep verified green (c; cpp spot-checks on both new tests) after both commits — two PRE-EXISTING unrelated failures (`tsymex_phase15_g8_multi_param`/`g10_smoke`, a `classifyType`/`node has no type` Nim-AST issue) confirmed failing identically on the pre-G3fix commit, not a regression. **Track G core (G1-G3) is now DONE. Next: G4 cmp instrumentation, G5 I2S+auto-dict, G6 transparency descriptor.**
**⚠ ESCALATION (design gate fired, RESOLVED BY ME — decided, not a fork): real-bridge wiring blocked by a WALKER GAP.** Wiring real `concolicFlip` against a `{.cover.}`'d property crashes — `lower`'s `iekVar` (`runtime.nim:2992`) has NO degrade path for a free/global/threadvar ref; `{.cover.}`'s `recordEdge` (coverage.nim:90) reads the `coverageMode` threadvar → crash when the walker descends into it. Blocks G4/G5 too (cmp hooks same shape). **DECISION (implementing now):** (1) nelli instrumentation hooks (`recordEdge`, future cmp hooks) are OPAQUE to the walker (exclude from proc registration / special-case isCall — no descent); (2) `iekVar` free-ref degrades to havoc in `wmFollowConcrete` ONLY, mode-gated so wmExplore byte-identical → NO SW bump, CR2 stays "73". **G3-fix + C4 — DONE** (`3918eaa` + `cf3f887`; full detail in the G3 entry above). Concolic bridge PROVEN end-to-end in a real `{.cover.}`'d fuzz campaign (0xCAFEBABE breakthrough). Walker free-ref gap (which would also have blocked G4/G5) is retired: instrumentation-opacity via `{.symexOpaque.}` + `wmFollowConcrete`-gated free-ref havoc (wmExplore byte-identical, CR2 "73"). **G4 — DONE** (`0bd9d8a` C1, `a42960a` C2, `da68f85` C3; a prior subagent's C1 attempt orphaned uncommitted work AGAIN — resumed synchronous-only, redone/finished in one pass, matching the standing "subagent stall takeover" convention). **C1** — the Nim-tier comparison hook: `coverage.nim`'s `{.covercmp.}` pragma macro (a `{.cover.}`-SIBLING, not an extension — composes on the same proc via two orthogonal AST rewrites) walks a proc body for `==`/`!=`/`<`/`<=`/`>`/`>=` and rewrites each into a block that evaluates both operands once, calls `logCmp(lhs, rhs, op)`, then compares the same temporaries. `logCmp` is an OVERLOADED proc (`SomeInteger`/`string`/`seq[byte]` ~ `ckInt`/`ckString`/`ckBytes`, plus a generic `[T]` no-op fallback so any other comparison type still compiles) — the macro emits an untyped `bindSym"logCmp"` closed symbol choice, resolved by ordinary overload resolution at the (fully-typed) call site, so no type info is needed at macro-expansion time. Every overload carries the SAME local `{.symexOpaque.}` pragma `recordEdge` uses (G3fix) — `tests/tsymex_g4_cmpwalk.nim` confirms a `{.cover, covercmp.}`'d property still runs through `concolicFlip` clean. `CmpOp`/`CmpLogEntryKind`/`CmpLogEntry` types + `resetCmpLog`/`currentCmpLog`/`parseCmpLog` (gracefully truncates a cut-off trailing record, never raises). SW not bumped (CR2 "73" unchanged — instrumentation, not walker semantics). **C2** — the per-run shm log: `nelli_shm.c`'s `pt_shm_*` primitives were a SINGLETON per process (one `pt_shdr`), which would have silently collided the cmp log onto the coverage channel's segment — parameterized the six core operations over an explicit `pt_shm_channel` (original zero-arg functions kept as thin wrappers over a default channel, byte-identical ABI for every existing caller) and added a second static channel (`pt_cmplog_*`) for the cmp log. `coverage.nim` gained `shmResetCmpLog`/`shmPublishCmpLog`/`shmReadCmpLog`; `fuzz.nim`'s `observeInProcess` toggles the cmp-log recording gate at the same per-run boundary as `coverageMode`; `fuzzworker.nim` wires per-input reset/publish into the persistent worker loop behind `$NELLI_CMP_SHM` (opt-in, default off, orthogonal to `$NELLI_COV_SHM`). **C3** — the external tier: `nelli_cov.c`'s `__sanitizer_cov_trace_cmp{1,2,4,8}`/`_const_cmp{1,2,4,8}` hooks, built via `-fsanitize-coverage=inline-8bit-counters,trace-cmp` (clang-only, no gcc analog — `tests/fuzzsupport.nim`'s `buildInstrumentedTraceCmp`/`traceCmpSupported`). Every entry is tagged `coUnknown` (a new `CmpOp` variant, appended last so existing ordinals are unchanged) since the sanitizer-coverage ABI never conveys which operator fired. **Two real bugs found+fixed while writing the C3 interop test** (not hypothetical — both reproduced RED first): (1) the channel-parameterized `pt_shm_ch_init`'s "idempotent: already attached" guard silently kept the FIRST shm name a process ever attached to even when asked for a DIFFERENT name later — a process reading more than one distinctly-named segment over its lifetime (a test suite moving between cases; a future orchestrator reading several workers' own segments) got the first segment's stale contents back for every later name; fixed by tracking the attached name and re-attaching (with a clean `munmap` of the stale mapping) on change, staying a no-op for the same-name case every existing caller relies on. (2) the cmp-log channel was reusing coverage's `pt_dumped` publish-once gate, so whichever channel published first in a run silently starved the other's publish for the rest of that run; each channel now carries its own gate variable — proven by a regression test with BOTH `$NELLI_COV_SHM` and `$NELLI_CMP_SHM` set on one worker run. Full `tfuzz*`+`tdb` (48 files) + a `tsymex_*` subset incl. CR2 "73" verified green dual-backend after each of the three cycles, no existing assertion touched. **G5 — DONE** (`e950b03` C1, `198e149` C2, `019f9c7` C3; a prior subagent's attempt (`a04f8afbcc1a263bf`) left only this handoff note's stale "IN FLIGHT" marker and zero commits — this session took over fresh per the standing subagent-stall-takeover convention). I2S (input-to-state) replacement + auto-dictionary, consuming G4's `{.covercmp.}` operand log. **C1** — the operand->choice-node mapping (int) + the mutator: `fuzzir.nim`'s `collectI2SMatches` walks a parent's cmp log against its OWN choice nodes — a node whose concrete value equals one side of a logged comparison earns a candidate replacing it with the OTHER side (both directions tried, since `logCmp` doesn't distinguish "the input" from "the constant"). Exactness for int despite the log not recording source signedness: `decodeIntCandidates` tries both `cast[int64]` (recovers the value if `T` was signed — sign extension preserves it up through int64) and the raw `uint64` (recovers it if `T` was unsigned), matching against the node's exact `Int128`. Out-of-range replacements are CLAMPED into the node's declared bounds (never skipped — an integer constraint is a closed interval, clamp is always well-defined). Wired as `fuzz.nim`'s 6th mutation operator behind `FuzzSettings.enableI2S` (opt-in, default off — pick distribution stays `mod 5` and the cmp log is never parsed when unset, so every pre-G5 caller's trajectory is byte-for-byte unchanged, the same convention `stallRounds`/`uniformSchedule`/`reVerify` use). `corpusCmpLog` (parallel to `corpusCov`/`corpusSlots`) captures each corpus entry's OWN log at the exact moment its run produced it (`captureCmpLog`, the one call site `currentCmpLog()` is read from — guarded to only fire on a non-rejected run, since a rejected run may never have reached `observeInProcess`'s reset and the thread-local buffer would still hold a PRIOR run's stale log). Headline (`tests/tfuzzi2s.nim`, plain `fuzzWith`, no macro/Z3): a `stallRounds:0` campaign over a `{.covercmp.}`'d `0xDEADBEEF` int gate reaches both edges with `enableI2S:true` and only one at the default — passed first try. **C2** — bytes/string (already generic from C1's design; this cycle is the headline proof): `bestBytesReplacement` clamps by truncate/zero-pad (bytes have no interval-set legality concern); `tryStringReplacement` SKIPS (never coerces) a replacement that violates the node's `StringConstraints` (codepoint-length + interval-set membership — no safe generic "clamp" exists for codepoints). Real finding: the public `bytes()` strategy is built on `lists(integers(0,255))` — one `ckInteger` node PER BYTE plus per-element continuation booleans, never a single `ckBytes` node — so it has no node an exact I2S match can land on; the `"MAGIC"` `seq[byte]` headline uses a small strategy over `datasource.drawBytes` directly (one real `ckBytes` node, matching what §G-cmp's scope actually describes), while `strings()` already draws a single `ckString` node via `drawString` and needed no such workaround. Both the `ckBytes` and `ckString` `"MAGIC"` gates are broken by I2S alone, unbroken at the `enableI2S` default. **C3** — the auto-dictionary: `harvestDictionary` folds BOTH operands of every logged comparison (int/bytes/string, deduped, capped at `maxDictEntries=512`) into a per-campaign `Dictionary`, called from the SAME `captureCmpLog` site as the log capture (harvests from every non-rejected run, not just admitted/corpus-growing ones — broader than "the surviving corpus", matching the RFC's "seen across the campaign"). `mutateIRI2SReplace` falls back to `dictReplacementCandidates` (a same-kind dictionary entry legally replacing some node, same clamp/skip discipline as direct I2S) when the parent's own log has no direct match — deliverable 3's "basic insertion"; S3 deepens havoc-style insertion later. `FuzzReport.dictionary` exposes the harvested set; stays empty at the `enableI2S` default (proven, not just asserted-inert). Full `tfuzz*`+`tdb` (49 files) + CR2 "73" pin + a `tsymex_*` subset verified green dual-backend (`c`+`cpp` spot-checks) after all three cycles, no existing assertion touched. SW not bumped throughout (mutation-loop wiring, no walker semantics touched). **Track G (G1-G5) is now DONE.** Next: G6 (transparency descriptor) → **Track S** (S2-S6) → **Track U** (U0-U3) — all Linux-verifiable. Hold Eci/E4a-c for the Windows channel. **Pre-existing (NOT ours): `tsymex_phase15_g8_multi_param`/`g10_smoke` fail on base commit (`classifyType`/"node has no type") — flagged, out of this RFC's scope.**
<!-- superseded detail below retained for history -->
_E3b build detail:_ **C1-C4 COMMITTED** (`f5590d1` corpus delta-log transport, `0c5f2ef` tombstone+size-triggered compaction, `77fa3ff` generation-files+head-pointer+snapshot cut point, `3580e32` `.bin` single-writer funnel + F-1 invariant). **C5 (versioned-header rule) UNCOMMITTED** — the agent orphaned its final suite-waiter; db.nim has ONLY a comment reflow (version-check logic already shipped in C1's reader) + `tests/tdbcorpuslog.nim` +63 lines of version-rule tests (newer→refuse naming both versions; unknown magic→refuse; older→read+migrate-on-compaction). **ON RESUME: if bg verify `byuciwuym` (tdbcorpuslog/tdb/tdbbackends/tfuzzcovcorpus/tfuzzpersist/tfuzzdbfunnel/tfuzzloop on c) is GREEN, `git add src/nelli/db.nim tests/tdbcorpuslog.nim && git commit` C5 (`feat(fuzzer): E3b C5 - versioned corpus-log header rule`), then run dual-backend confirm and mark E3b DONE.** **Next after E3b: E-cleanup** (resource lifecycle + steady-state respawn-storm breaker), then Eci/E4a-c/E5, then Track G (G1a first).
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

### E-cleanup — campaign-level resource lifecycle — DONE (commits `f667bd0`, `f5f81bd`, `6a8a174`, `44db313`)
All four cycles landed, each its own GREEN commit, full `tfuzz*` + `tdb*` on both `c` and
`cpp` green after every cycle (42/42 files each backend by C4, no existing assertion
edited). Files added: `tests/tdbcleanupsweep.nim`, `tests/tfuzzworkerlifecycle.nim`,
`tests/tfuzzrespawnstorm.nim`; touched: `db.nim` (startup sweep), `fuzzworker.nim`
(PDEATHSIG + process-group helpers), `fuzz.nim` (storm breaker).
- **C1** (`f667bd0`): `directoryBasedDatabase`'s constructor — already sweeping orphaned
  `.tmp.<pid>.<tid>` files — now also sweeps (a) superseded `<safeKey>.corpus.<gen>.log`
  generation files not referenced by `<safeKey>.corpus.head` (E3b's compactor deliberately
  never unlinks these; safe here because no reader from a PRIOR campaign can still be alive
  at a NEW campaign's construction moment — no lease machinery needed, that stays U2's job
  for the live-campaign case) and (b) stale `nelli_`-prefixed POSIX `shm_open` segments in
  `/dev/shm` (E2b's coverage transport) — prefix-only scoping, mirroring the `.tmp.` sweep,
  never touching a foreign process's differently-prefixed segment. No FIFO/named-pipe sweep
  needed — nothing in the codebase creates one (`mkfifo` unused; only anonymous
  `posix.pipe()`).
- **C2** (`f5f81bd`): `PR_SET_PDEATHSIG`, armed in the child immediately after `fork()`
  (before `execvpe`, survives exec) at both worker-spawn sites (`spawnWorkerProcess`,
  `newForkWorker`) — the kernel now `SIGKILL`s a worker the instant its parent dies,
  regardless of what the worker itself is doing (the real hazard: a worker stuck INSIDE
  `dispatch` on a hung target never comes back around to notice even a closed input pipe).
  Guards the fork/arm race via a `getppid()` re-check. Test (`tfuzzworkerlifecycle.nim`)
  is a genuine three-process-level deterministic spawn-kill-assert: a subreaper test
  process forks a surrogate "orchestrator," which spawns a REAL worker via
  `spawnWorkerProcess` and dispatches it into a self-referential-pipe hang (deliberately
  decoupled from any fd the orchestrator holds, so pipe-EOF can't be the thing saving the
  day); SIGKILLing the surrogate and blocking-`waitpid`ing the reparented worker proves
  PDEATHSIG alone ends it — RED-confirmed by temporarily disabling the `prctl` call and
  observing the test hang (`dt-bounded.sh` kill), not just inferred.
- **C3** (`6a8a174`): `isolateOwnProcessGroup(pid)` (called by the orchestrator right after
  spawning, wired into both spawn sites) puts a worker into its own process group led by
  itself, so any further descendant IT forks inherits the same pgid; `killWorkerGroup(pid)`
  then reaches the worker's WHOLE subtree via one `killpg`, without touching the caller's
  own group (unlike a shared `setpgid(0,0)` campaign-wide group would). Each worker gets its
  own single-worker group rather than one shared campaign-wide group specifically so E2a's
  N=1-recycle-per-input policy never depends on a shared group whose sole (already-reaped)
  member must stay valid for the NEXT worker to join. This is the clean-shutdown (caught
  SIGINT) counterpart to C2's hard-kill/OOM defense. RED-confirmed the same way as C2.
- **C4** (`44db313`): `Orchestrator.stormWindow`/`stormBackoff` — the STEADY-STATE breaker,
  distinct from the (E4a, not yet built) BOOTSTRAP circuit-breaker that only catches
  dead-before-first-read. Tracks the `CrashInfo.kind` of the most recent `stormWindow`
  crash-triggered recycles in a sliding window (crash-event-count-based, not wall-clock, so
  it stays deterministic/testable); once the window is full and every kind in it is
  IDENTICAL (not diversifying — an environment fault, vs. a productive crash-finding
  campaign's varied/new kinds, which must never trip it), the breaker trips:
  `stormBackoff == false` (default) raises `RespawnStormError` with a distinct diagnostic;
  `true` degrades instead (campaign continues, `stormTripped`/`stormBackoffLevel` set for a
  caller/driver to pace its own respawn loop — this layer never sleeps itself). The window
  keeps sliding after a trip, so a later diversifying crash self-corrects it back to
  untripped. `stormWindow == 0` (default) is fully inert — byte-for-byte pre-E-cleanup
  behavior. Pure algebra over a scripted fake `Worker[T]` (E3a's "order-independent fold"
  precedent) — no real process spawns, all 5 tests green on the first implementation pass.

## Slices (first-pass; round-3 re-cuts folded in)
- [x] **E0 corpus-sync SPIKE — DONE** (delta log selected; 5 mandate items resolved) ·
  **E1 Orchestrator/Worker seams + macro entry — DONE** (typed CrashInfo; Worker=
  load-bearing seam; fuzz macro + worker re-entry + capture checks; C7 freeze-guard
  green) ·
  **E2a POSIX worker+framed pipe+crash-isolation — DONE** (N=1 coverage until E2b) ·
  **E2b shm+nelli_cov.c reset — DONE** (double-buffered + generation word; N=1→N>1) ·
  **E3a freshness machinery — DONE** (finding record/reproRate/divergentReproduction;
  re-verify-gated `admit`, default off; pure-algebra order-independent-fold tests;
  worker recycling + fork-per-input captured-once snapshot invariant) ·
  **E3b persistence discipline per E0 — DONE** (delta log + compaction + generation/head +
  `.bin` funnel + versioned header) ·
  **E-cleanup resource lifecycle + steady-state respawn-storm breaker — DONE** (startup
  sweep; PDEATHSIG; process-group-kill backstop; storm breaker) ·
  Eci Windows toolchain (CI+local; emits greppable capability flag) — **NEXT** ·
  E4a/E4b/E4c Windows worker (E4a: platform glue behind Linux-testable seam) ·
  E5 external tier onto seams
- [x] **G1a** thread mode through dispatch (mechanical) — **DONE** (`3a14b59`) ·
  [x] **G1b** draw-symbolication+bounded trace — **DONE** (`3cc275a`) ·
  [x] **G2** branch-flip solve+materialize — **DONE** (`8bca6e1`) ·
  [x] **G3** orchestration (Z3 bridge off hot path) — **DONE** (`641ada0`/`ecba035`/`66b9cd9`
  + `3918eaa`/`cf3f887` G3fix; S1's real energy/`FrontierStats` used from the start, no
  G3b throwaway, see the REORDER note above) ·
  [x] **G4** cmp instrumentation + operand log — **DONE** (`0bd9d8a`/`a42960a`/`da68f85`) ·
  [x] **G5** I2S+auto-dict — **DONE** (`e950b03`/`198e149`/`019f9c7`) ·
  G6 transparency descriptor + closed/directed algebra +
  `branching` (or fold into G1's ADR) — **NEXT**
- [x] ~~G3b wire real Entropic energy post-S1 (conditional)~~ — AVOIDED by the
  S1-before-G3 reorder (see above): G3 lands with real energy from the start.
- [x] **S1** Entropic energy (owns shared FrontierStats) — **DONE** (see above) ·
  [ ] S2 operator bandit ·
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
