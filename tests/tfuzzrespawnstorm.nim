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
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker(),
                                  stormWindow = 3)

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
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker(),
                                  stormWindow = 3)

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
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker(),
                                  stormWindow = 2, stormBackoff = true)

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
    let o = newOrchestrator[int](makeWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = makeWorker(),
                                  stormWindow = 2, stormBackoff = true)

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
