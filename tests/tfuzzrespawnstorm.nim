## RFC-fuzzer-nextgen E-cleanup (C4/final): the steady-state respawn-storm
## breaker — distinct from the (not-yet-built, E4a) BOOTSTRAP circuit-
## breaker, which only catches dead-before-first-read. This one catches a
## worker that boots fine and then dies SYSTEMICALLY on every recycle
## (corrupt environment, a leak in the harness, shm/disk exhaustion): track
## the most recent `stormWindow` crash-triggered recycles' `CrashInfo.kind`;
## once that window fills and every kind in it is IDENTICAL, the crashes are
## NOT diversifying — an environment fault, not a productive crash-finding
## campaign (which has varied/new kinds) — and the breaker trips.
##
## Pure algebra over FAKES (the E3a "order-independent fold" precedent,
## `tests/tfuzzreverify.nim`): a scripted `Worker[T]` returns a canned
## sequence of `Observation`s, driven through the REAL `Orchestrator.run`
## recycle/storm logic — deterministic, no real process spawns, safe under
## `dt-bounded.sh`.

import std/[unittest, options, strutils]
import nelli

suite "fuzz: steady-state respawn-storm breaker (RFC-fuzzer-nextgen E-cleanup C4)":
  test "N consecutive SAME-kind crashes trips the breaker and aborts with a distinct diagnostic":
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vOk),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "EnvFault", message: "boom1"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "EnvFault", message: "boom2"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "EnvFault", message: "boom3"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 3))

    check o.run(@[]).verdict == vOk
    check o.run(@[]).verdict == vCrashed
    check not o.stormTripped                # only 1 crash so far — window not full
    check o.run(@[]).verdict == vCrashed
    check not o.stormTripped                # 2 crashes — still short of the window

    expect RespawnStormError:
      discard o.run(@[])                    # 3rd same-kind crash: window full, non-diversifying
    check o.stormTripped
    check "ckException" in o.stormDiagnostic
    check callIdx == 4                      # the 4th script entry WAS consumed before the raise

  test "diversifying crash kinds (varied CrashInfo.kind) do NOT trip the breaker":
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "e"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "s"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckExitCode, exitCode: 1, message: "x"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 3))

    for _ in 0 ..< 3:
      discard o.run(@[])                    # never raises: a productive crash-finding campaign
    check not o.stormTripped
    check o.stormDiagnostic.len == 0

  test "stormBackoff degrades instead of aborting, and the campaign continues":
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom1"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom2"))),
      Observation[int](verdict: vOk),        # a further input AFTER the window trips
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 2, stormBackoff = true))

    check o.run(@[]).verdict == vCrashed
    check o.run(@[]).verdict == vCrashed    # window (2) fills here: tripped, but NOT raised
    check o.stormTripped
    check o.stormBackoffLevel > 0
    check o.run(@[]).verdict == vOk         # campaign continues past the trip in backoff mode

  test "a later diversifying crash un-trips the (backoff-mode) breaker — the sliding window self-corrects":
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom1"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom2"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 6, message: "boom3"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 2, stormBackoff = true))

    discard o.run(@[])
    discard o.run(@[])
    check o.stormTripped                    # 2 ckException in a row: window (2) is non-diversifying
    discard o.run(@[])                      # window slides: [ckException, ckSignal] -- diversifying again
    check not o.stormTripped

  test "stormWindow == 0 (the default) never engages the breaker, regardless of crash pattern":
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom1"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom2"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckException, defect: "E", message: "boom3"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker())
      # stormWindow left at its default (0) -- byte-for-byte pre-E-cleanup behavior.
    for _ in 0 ..< 3:
      discard o.run(@[])
    check not o.stormTripped

  test "REAL worker-death kinds (ckSignal), not ckException, trip the breaker -- the dedup key is CrashInfo.kind alone, so two DIFFERENT SIGSEGV sites (same signal, different message/site) still read as non-diversifying":
    # R22: every OTHER test in this suite scripts `ckException` -- per
    # `fuzz.nim:866-868`'s own doc comment, that kind means the worker was
    # STILL ALIVE to report (an in-process Defect/CatchableError), never what
    # a genuine process death looks like. The storm breaker exists to judge
    # REAL worker crashes (`{ckSignal, ckExitCode, ckWinException}`,
    # `fuzz.nim:1236-1237`), and its diversification check is a bare `k !=
    # recentCrashKinds[0]` comparison over `CrashInfo.kind` ONLY -- `message`/
    # `signal` detail never enters it. Three crashes that are all `ckSignal`
    # but come from CLEARLY distinct sites (different messages, as a real
    # SIGSEGV at two different faulting addresses would produce) must still
    # trip the breaker: this is the exact case "is it diversifying?" has to
    # get right, since a naive message-grep dedup would (wrongly) call these
    # diversifying.
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "worker died on signal 11 (site A, pc=0x1000)"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "worker died on signal 11 (site B, pc=0x9999)"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "worker died on signal 11 (site C, pc=0xDEAD)"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 3))

    check o.run(@[]).verdict == vCrashed
    check not o.stormTripped
    check o.run(@[]).verdict == vCrashed
    check not o.stormTripped
    expect RespawnStormError:
      discard o.run(@[])          # 3rd ckSignal, distinct site: still non-diversifying
    check o.stormTripped
    check "ckSignal" in o.stormDiagnostic

  test "REAL worker-death kinds that genuinely diversify (ckSignal then ckExitCode then ckWinException) do NOT trip the breaker":
    # The companion positive case: real process-death kinds, but VARIED --
    # this is the productive "found more than one crash lineage" campaign
    # shape the breaker must never punish.
    var callIdx = 0
    let script = @[
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "worker died on signal 11"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckExitCode, exitCode: 134, message: "worker exited 134 without a result frame"))),
      Observation[int](verdict: vCrashed,
        crash: some(CrashInfo(kind: ckWinException, code: 0xC0000005'u32, message: "worker died: structured exception 0xC0000005"))),
    ]
    proc makeWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        let obs = script[callIdx]
        inc callIdx
        obs)

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](makeWorker(), frontier, spawnFreshWorker = proc(): Worker[int] = makeWorker(), policy = orchestratorPolicy(stormWindow = 3))

    for _ in 0 ..< 3:
      discard o.run(@[])
    check not o.stormTripped
    check o.stormDiagnostic.len == 0
