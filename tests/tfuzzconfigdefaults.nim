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
    # RFC-z3-optional moved `stallRounds`/`concolicMaxBranchAttempts` off
    # this object and onto `ConcolicAssist` (see the next test); the
    # `OrchestratorPolicy` defaults below are unaffected — that is the raw
    # seam, and it keeps both knobs.
    let s = FuzzSettings()
    check s.guidance.enableI2S == false

  test "ConcolicAssist() is the zero-value 'no assist' default":
    let a = ConcolicAssist()
    check a.bridge == nil
    check a.stallRounds == 0
    check a.maxBranchAttempts == 0   # loop-side resolves 0 -> 8 itself
    # The zero value is the ONLY spelling of "off". A bridge-bearing record
    # with a zeroed policy is coerced active, and a policy-bearing record
    # with no bridge raises -- both pinned in tfuzzconcolicbridge.nim.

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

suite "RFC-0010 C1 — the one FuzzSettings field that is not zero-valued":

  test "FuzzSettings().integerBias carries IntegerBiasConfig's declared defaults":
    # ADR-0031's rule for this surface is that every knob is designed so zero
    # IS the correct default -- one of the two ways a surface can satisfy
    # RFC-0010 §0's invariant. `integerBias` is the exception, and it is an
    # exception by nesting rather than by choice: FuzzSettings embeds
    # IntegerBiasConfig, which declares its own field defaults, and a nested
    # object field picks those up recursively.
    #
    # Behaviour is unchanged end-to-end. Before RFC-0010 this field arrived
    # all-zero and `resolved()` mapped that to defaultIntegerBias at the point
    # of use; now it arrives carrying the defaults and there is nothing to
    # resolve. What changed is the structural claim, and nothing here asserted
    # it, which is exactly why it needed writing down.
    let s = FuzzSettings()
    check s.integerBias == defaultIntegerBias
    check s.integerBias != IntegerBiasConfig(boundaryPercent: 0,
                                             smallWindowPercent: 0,
                                             smallWindowSize: 0,
                                             shrinkTowardsWeight: 0)

  test "an explicitly all-zero bias survives into FuzzSettings":
    # The zero-survival half, at this surface: writing the zeros means an
    # unbiased uniform draw, and is no longer silently rewritten to 30/30/40.
    let s = FuzzSettings(integerBias: IntegerBiasConfig(
      boundaryPercent: 0, smallWindowPercent: 0,
      smallWindowSize: 0, shrinkTowardsWeight: 0))
    check s.integerBias.boundaryPercent == 0
    check s.integerBias.smallWindowSize == 0
