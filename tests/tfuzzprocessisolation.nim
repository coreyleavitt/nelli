## RFC-fuzzer-nextgen E-review: closes the code review's headline finding
## (R3, CRITICAL, verified by two independent reviewers plus a refuter).
##
## The finding: `fuzzworker.nim`'s process-isolation tier -- `newProcessWorker`/
## `newForkWorker`/`spawnWorkerProcess`, Job Object resource limits, shm
## coverage transport, the bootstrap circuit breaker, worker recycling --
## over 1000 lines, fully tested, CI-proven on real Windows -- was DARK.
## `fuzz*[T]` (fuzz.nim:1590 pre-fix) built its `Orchestrator` without ever
## supplying `spawnFreshWorker`, so `newInProcessWorker` was the only
## `Worker` any public entry point (`fuzz`/`fuzzWith`) ever constructed:
## no process isolation, no resource limits, no worker recycling,
## `CampaignStats.respawnCount`/`stormTripped`/`stormBackoffLevel`
## structurally always 0/false. `fuzzBinary`/`externalTarget` (via
## `runChild`) were NEVER part of this finding -- that path is genuinely
## process-isolated today and is untouched by this file.
##
## The fix (fuzz.nim, fuzzmacro.nim): `FuzzSettings.processIsolation`
## (default `false`, byte-for-byte unchanged) opts in; `fuzz*[T]` gained an
## optional `spawnFreshWorker` parameter (mirrors `concolicBridge`'s "only
## the macro ever supplies a real one" convention) that `fuzz(...)`
## (fuzzmacro.nim) now ALWAYS emits, built from `newProcessWorker` over the
## same call-site id its worker-mode registration already uses -- process
## isolation needs worker RECONSTRUCTION (a fresh process re-execing the
## binary and rebuilding the property from the macro's captured
## construction expressions), which only the macro can provide.
## `fuzzWith`/a direct `fuzz*[T]` call hand `fuzz*[T]` an arbitrary closure
## no fresh process can reconstruct, so setting `processIsolation` without
## going through the macro raises `ProcessIsolationError` rather than
## silently downgrading to in-process -- a silent downgrade is exactly the
## bug class this review caught.
##
## Suite 1 below is the real thing: exactly ONE `fuzz(...)` macro call
## site, and it comes FIRST in the file (see tests/tfuzzworkerprocess.nim's
## module doc: a re-exec'd worker child runs the WHOLE binary's earlier
## top-level code before it can even check whether it matches its OWN
## call-site id, so this site must be the very first thing that runs --
## confirmed empirically here too: an earlier draft with the fakes-only
## suite FIRST made every spawned child replay that whole suite before
## reaching worker-mode dispatch, multiplying output N-fold for no reason).
## It drives a REAL multi-iteration `processIsolation: true` campaign
## through genuinely re-exec'd worker processes, using the SAME
## reconstruction-sentinel technique as `tests/tfuzzworkerprocess.nim`/
## `tests/tfuzzwinworker.nim` (a counter that increments once per genuine
## reconstruction), plus a process-identity signature (the worker's own
## PID, embedded in the crash message) as a second, independent proof that
## execution left the parent process entirely.
##
## Suite 2 is pure Orchestrator-plumbing algebra over FAKES -- deterministic,
## no real process spawns, safe under `dt-bounded.sh` (the same precedent
## `tests/tfuzzrespawnstorm.nim`/`tests/tfuzzbootstrapbreaker.nim` use). It
## never calls the `fuzz(...)` macro, so its position after Suite 1 is safe.

import std/[unittest, options, strutils, os]
import nelli
import nelli/[datasource, rng]

# See tests/tfuzzworkerprocess.nim's module doc: a re-exec'd worker child is
# launched with `--nelli-worker=<id>` on argv, which `std/unittest` would
# otherwise treat as a test-name glob filter, silently dropping every
# `test:` block in the re-exec'd process before it ever reaches the
# worker-mode dispatch check.
disableParamFiltering()

# --- Suite 1: the real fuzz(...) macro, ONE call site, genuine child processes --

var rebuildCounter = 0
  ## The reconstruction sentinel (see tests/tfuzzworkerprocess.nim for the
  ## full discriminating argument): a genuinely fresh process starts this at
  ## 0 and reports exactly 1 after its own single construction call. Distinct
  ## from an in-process (non-isolated) trajectory, where the SAME parent
  ## process's copy would also read 1 (constructed once at the macro's own
  ## front door) -- the pid check below is what actually discriminates
  ## "ran in a fresh OS process" from "processIsolation was silently
  ## downgraded to in-process," since `rebuildCounter` alone reads 1 either
  ## way. Together they prove BOTH properties: genuine reconstruction
  ## (rebuildCounter) AND genuine process separation (pid).
proc isolationSentinelStrategy(lo, hi: int): Strategy[int] =
  inc rebuildCounter
  integers(lo, hi)

proc isolationCrashProp(n: int) {.cover.} =
  ## Unconditionally raises an `AssertionDefect` (a genuine `Defect`, DoD's
  ## own "a property that raises a Defect" shape) embedding both sentinels
  ## in the message, which `observeInProcess` (fuzz.nim) catches -- inside
  ## WHATEVER process is actually running this -- and reports as
  ## `vInteresting`/`ckException`, riding back to the parent over the
  ## worker's result frame (`decodeObservationLite`) exactly like
  ## tests/tfuzzworkerprocess.nim's `sentinelProp`.
  doAssert false, "pid=" & $getCurrentProcessId() & " rebuildCounter=" & $rebuildCounter

suite "fuzz: processIsolation via the real fuzz(...) macro (RFC-fuzzer-nextgen E-review)":
  var isolatedReport: FuzzReport

  test "a processIsolation: true campaign genuinely executes the property in freshly spawned child processes":
    rebuildCounter = 0
    isolatedReport = fuzz(isolationSentinelStrategy(-50, 50), isolationCrashProp,
                          FuzzSettings(maxIterations: 6, seed: 1, executor: ExecutorConfig(processIsolation: true)))

    check rebuildCounter == 1   # the PARENT's own front-door construction, per tfuzzmacro.nim's C5 pin
    check isolatedReport.irCrashes.len >= 1

    let ownPid = $getCurrentProcessId()
    var seenPids: seq[string]
    for c in isolatedReport.irCrashes:
      # Proof A (reconstruction sentinel): the message came from a process
      # whose OWN rebuildCounter read exactly 1 -- a fresh spawn's first-
      # and-only reconstruction, never accumulated across submits.
      check "rebuildCounter=1" in c.message
      # Proof A, continued (process-identity signature): the message
      # embeds a PID that is NEITHER the parent's own PID NOR any other
      # crash's PID already seen -- direct evidence execution happened in
      # a genuinely SEPARATE, freshly spawned OS process every single time,
      # not once at the parent's front door and not in one reused worker.
      let pidStart = c.message.find("pid=") + 4
      check pidStart > 3
      let pidEnd = c.message.find(' ', pidStart)
      check pidEnd > pidStart
      let pid = c.message[pidStart ..< pidEnd]
      check pid != ownPid
      check pid notin seenPids
      seenPids.add pid

  test "the campaign is not derailed by the crashing property -- it runs to completion and records findings (Track E's exit gate)":
    # Proof B: the RFC's Track E exit gate is "structure-aware fuzzing is
    # crash-isolated on both platforms" -- a per-iteration Defect must be
    # SURVIVED (reported as a finding) and the CAMPAIGN must continue past
    # it, not derail the whole `fuzz(...)` call. Reuses test 1's already-
    # completed campaign (no second `fuzz(...)` call site -- see the module
    # doc above for why).
    check isolatedReport.iterations == 6      # ran the full maxIterations budget, did not abort
    check isolatedReport.irCrashes.len >= 1   # every crashing input was reported as a finding
    check isolatedReport.irCrashes.len <= 6   # never more findings than iterations that ran

# --- Suite 2: pure Orchestrator-plumbing algebra (no real process spawns) ---

suite "fuzz: processIsolation wiring, pure algebra over fakes (RFC-fuzzer-nextgen E-review)":
  test "fuzzWith with processIsolation: true raises ProcessIsolationError naming the fuzz(...) macro constraint":
    proc trivialProp(x: int) {.cover.} = discard x
    try:
      discard fuzzWith(integers(0, 10), trivialProp,
                        FuzzSettings(maxIterations: 5, executor: ExecutorConfig(processIsolation: true)))
      check false   # unreachable -- fuzzWith must raise before running any iteration
    except ProcessIsolationError as e:
      check "fuzz(" in e.msg
      check "macro" in e.msg

  test "a direct fuzz*[T] call with processIsolation: true and no spawnFreshWorker raises the same error":
    var frontier = newCoverageFrontier()
    expect ProcessIsolationError:
      discard fuzz(integers(0, 10), inProcessTarget(proc(x: int) = discard x), frontier,
                   FuzzSettings(maxIterations: 5, executor: ExecutorConfig(processIsolation: true)))

  test "processIsolation: false (the default) ignores a caller-supplied spawnFreshWorker entirely -- unchanged behavior":
    var spawnCalls = 0
    proc fakeSpawn(): Worker[int] =
      inc spawnCalls
      newWorker(proc(input: ChoiceSeq): Observation[int] = Observation[int](verdict: vOk))

    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 10), inProcessTarget(proc(x: int) = discard x), frontier,
                       FuzzSettings(maxIterations: 5, seed: 1), spawnFreshWorker = fakeSpawn)
    check report.iterations == 5
    check spawnCalls == 0                    # never called: processIsolation is off
    check report.stats.respawnCount == 0     # still structurally 0 when isolation is off

  test "settings.processIsolation: true threads spawnFreshWorker/bootstrapWindow/stormWindow into the Orchestrator -- CampaignStats.respawnCount/stormTripped are no longer structurally dead":
    # A fake worker that ALWAYS reports vCrashed with the SAME crash kind:
    # every submit forces a recycle (`respawnCount`), and every recycle is
    # non-diversifying, so the steady-state storm breaker trips
    # (`stormTripped`). `ckException` (not `ckSignal`/`ckExitCode`/
    # `ckWinException`) deliberately does NOT count toward the bootstrap
    # breaker (see tests/tfuzzbootstrapbreaker.nim's own "the worker was
    # alive to report it" pin) -- this test isolates the recycling/storm
    # wiring specifically, not the bootstrap breaker (already proven live
    # via the constant justification in fuzz.nim, and reachable through
    # this exact same path).
    proc alwaysDiesWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vCrashed,
          crash: some(CrashInfo(kind: ckException, defect: "SyntheticIsolatedDeath",
                                 message: "synthetic isolated-worker crash"))))

    var frontier = newCoverageFrontier()
    let report = fuzz(integers(0, 10), inProcessTarget(proc(x: int) = discard x), frontier,
                       FuzzSettings(maxIterations: 12, seed: 1, executor: ExecutorConfig(processIsolation: true)),
                       spawnFreshWorker = alwaysDiesWorker)

    check report.iterations == 12          # the campaign ran to completion, not aborted
    check report.stats.respawnCount > 0    # dead before this fix: always 0 through fuzz()/fuzzWith()
    check report.stats.stormTripped        # dead before this fix: always false through fuzz()/fuzzWith()
    check report.stats.stormBackoffLevel > 0
