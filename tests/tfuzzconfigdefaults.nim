## RFC-fuzzer-nextgen ADR-0031 (configuration-surface regrouping, finding
## R11): pins that grouping `FuzzSettings`'s per-track knobs into
## `ExecutorConfig`/`GuidanceConfig`/`SchedulingConfig`, and `Orchestrator`'s
## slot-budget/freshness-machinery knobs into `OrchestratorPolicy`, did not
## silently move any default. `FuzzSettings()` and `orchestratorPolicy()`
## must produce EXACTLY the same values every pre-ADR-0031 caller got
## implicitly — a caller who wrote `FuzzSettings(maxIterations: 10_000)`
## before and the equivalent now must see bit-for-bit identical behavior.
## This is a value pin, not a behavior pin: `tfuzzschedule`/`tfuzzhavoc`/
## `tfuzzoperatorbandit`/`tfuzzcull`/etc. already pin that each opt-out
## flag's `true` value reproduces the pre-track trajectory byte-for-byte;
## this file is the one place asserting the DEFAULT (all-`false`/zero)
## values themselves, so a future accidental drift in either constructor is
## caught here rather than discovered as a mysterious trajectory change
## three suites away.

import std/[unittest, times]
import nelli

suite "fuzz: FuzzSettings/OrchestratorPolicy default values (ADR-0031 regrouping)":
  test "FuzzSettings() zero-value core fields are unchanged":
    let s = FuzzSettings()
    check s.maxIterations == 0
    check s.timeBudget == initDuration()
    check s.seed == 0'u64
    check s.initialIRCorpus.len == 0
    check s.keepAllCrashes == false
    check s.crashKey == nil
    check s.persistKey == ""
    check s.corpusLimit == 0
    check s.minimizeCorpus == false
    check s.stopOnFirstCrash == false

  test "FuzzSettings().executor is the pre-ADR-0031 ExecutorConfig default":
    let s = FuzzSettings()
    check s.executor.processIsolation == false

  test "FuzzSettings().guidance is the pre-ADR-0031 GuidanceConfig default":
    let s = FuzzSettings()
    check s.guidance.stallRounds == 0
    check s.guidance.concolicMaxBranchAttempts == 0   # loop-side resolves 0 -> 8 itself
    check s.guidance.enableI2S == false

  test "FuzzSettings().scheduling is the pre-ADR-0031 SchedulingConfig default":
    let s = FuzzSettings()
    check s.scheduling.uniformSchedule == false
    check s.scheduling.uniformOperators == false
    check s.scheduling.uniformHavoc == false
    check s.scheduling.cullCadence == 0
    check s.scheduling.uniformCorpus == false
    check s.scheduling.checkpointCadence == 0

  test "ExecutorConfig()/GuidanceConfig()/SchedulingConfig() zero-value literals match FuzzSettings()'s own defaults":
    # A caller building a group directly (not through FuzzSettings) must land
    # on the identical all-off default -- no separate "zero value" convention
    # per group.
    let s = FuzzSettings()
    check ExecutorConfig() == s.executor
    check GuidanceConfig() == s.guidance
    check SchedulingConfig() == s.scheduling

  test "orchestratorPolicy() reproduces newOrchestrator's exact pre-ADR-0031 parameter defaults":
    let p = orchestratorPolicy()
    check p.reVerify == false
    check p.reVerifyBudget == 8
    check p.reproSamples == 5
    check p.recycleAfterInputs == 0
    check p.stormWindow == 0
    check p.stormBackoff == false
    check p.bootstrapWindow == 0
    check p.stallRounds == 0
    check p.concolicMaxBranchAttempts == 8

  test "newOrchestrator(worker, frontier) with no policy argument uses orchestratorPolicy()'s defaults":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    # Observable proxies for the private policy fields: re-verify/recycling/
    # breakers are all inert with no spawnFreshWorker configured, and no
    # concolic bridge was wired -- every one of these mirrors the exact
    # pre-ADR-0031 `newOrchestrator(worker, frontier)` two-arg call.
    check respawnCount(o) == 0
    check stormTripped(o) == false
    check bootstrapTripped(o) == false
    check concolicYield(o) == ConcolicYield()
