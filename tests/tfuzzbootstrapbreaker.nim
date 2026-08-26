## RFC-fuzzer-nextgen E4a (C2): the bootstrap circuit-breaker's LIVE wiring
## at `Orchestrator.run`'s spawn/first-read site (`Orchestrator.bootstrapWindow`).
##
## `workerproto.BootstrapBreaker` (E4a C1, `tests/tfuzzworkerproto.nim`)
## already exercises the pure fold in isolation — threshold/reset semantics,
## the "construction-not-reentrant" diagnostic wording. This file's job is
## narrower and complementary: prove the fold is actually WIRED into a live
## `run` call over a scripted `Worker[T]`, using the SAME "pure algebra over
## fakes" precedent `tests/tfuzzrespawnstorm.nim` uses for the sibling
## steady-state breaker — deterministic, no real process spawns, safe under
## `dt-bounded.sh`. `fuzz.nim` cannot import `workerproto` directly (that
## module itself depends on `fuzz.nim`'s types, so the reverse import would
## cycle — see `BootstrapBreakerError`'s doc comment in fuzz.nim), so the
## fold is re-inlined onto `Orchestrator`'s own fields; this suite is what
## proves that re-inlined copy stays in lockstep with the standalone one.

import std/[unittest, options, strutils]
import nelli

suite "fuzz: bootstrap circuit-breaker (RFC-fuzzer-nextgen E4a C2)":
  test "N consecutive dead-before-first-read spawns trips the breaker and aborts with a distinct diagnostic":
    proc deadWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vCrashed,
          crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "died before answering"))))

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](deadWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = deadWorker(),
                                  bootstrapWindow = 3)

    check o.run(@[]).verdict == vCrashed
    check not o.bootstrapTripped              # only 1 dead-before-first-read spawn so far
    check o.run(@[]).verdict == vCrashed
    check not o.bootstrapTripped              # 2 -- still short of the window

    expect BootstrapBreakerError:
      discard o.run(@[])                       # 3rd consecutive dead-before-first-read spawn
    check o.bootstrapTripped
    check "construction-not-reentrant" in o.bootstrapDiagnostic
    # Distinct from the sibling steady-state respawn-storm breaker's
    # diagnostic wording (fuzz.nim's `RespawnStormError`/`stormDiagnostic`) —
    # a caller must be able to tell the two failure modes apart from the
    # message alone.
    check "respawn-storm" notin o.bootstrapDiagnostic

  test "a worker that answers its first submit does not count toward the breaker, even if it crashes later":
    var callIdx = 0
    proc flakyWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        inc callIdx
        if callIdx == 1:
          Observation[int](verdict: vOk)
        else:
          Observation[int](verdict: vCrashed,
            crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "a later crash"))))

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](flakyWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = flakyWorker(),
                                  bootstrapWindow = 2)

    check o.run(@[]).verdict == vOk         # first submit answered -- proves this spawn is reentrant
    check o.run(@[]).verdict == vCrashed    # SAME worker's second submit crashes...
    check not o.bootstrapTripped            # ...but it is NOT a dead-BEFORE-FIRST-read event

  test "vCrashed with ckException on the first submit (the worker was alive to report it) does not count":
    proc immediateExceptionWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vCrashed,
          crash: some(CrashInfo(kind: ckException, defect: "AssertionDefect", message: "m"))))

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](immediateExceptionWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = immediateExceptionWorker(),
                                  bootstrapWindow = 1)

    # Every spawn's first (and only) submit answers over the pipe -- the
    # worker was ALIVE to report the crash, unlike a genuine process death
    # (`ckSignal`/`ckExitCode`/`ckWinException`) -- so a threshold-1 breaker
    # never trips even though every run crashes and every worker recycles.
    for _ in 0 ..< 3:
      discard o.run(@[])
    check not o.bootstrapTripped

  test "bootstrapWindow == 0 (the default) never engages the breaker, regardless of dead-before-first-read spawns":
    proc deadWorker(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vCrashed,
          crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "died before answering"))))

    var frontier = newCoverageFrontier()
    let o = newOrchestrator[int](deadWorker(), frontier,
                                  spawnFreshWorker = proc(): Worker[int] = deadWorker())
      # bootstrapWindow left at its default (0) -- byte-for-byte pre-E4a behavior.
    for _ in 0 ..< 5:
      discard o.run(@[])
    check not o.bootstrapTripped
    check o.bootstrapDiagnostic.len == 0
