## RFC-fuzzer-nextgen G3 (deliverables 2/3) — stall-gated concolic-bridge
## invocation + re-verified admission into the corpus, PURE ALGEBRA over a
## FAKE `ConcolicBridgeEntry` (never a real Z3 call — that's the macro-wired
## `fuzzmacro.nim` integration, exercised end-to-end separately). Mirrors
## E3a's `tfuzzreverify.nim` idiom: a fabricated closure standing in for the
## real mechanism, so this suite is deterministic and fast.

import std/[unittest, options, tables]
import nelli
import nelli/choice

suite "fuzz: Orchestrator.tryConcolicBridge (RFC-fuzzer-nextgen G3)":
  test "no bridge configured (the default): inert, frontier untouched":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier, policy = orchestratorPolicy(stallRounds = 1))
    for i in 0 ..< 5: discard admit(o, @[], o.run(@[]))   # drive staleness up
    let r = tryConcolicBridge(o, @[])
    check not r.ar.admitted
    check frontier.coveredEdges == 1   # only the ordinary admits folded anything in

  test "bridge configured but stallRounds == 0 (the default): inert regardless of frontier state":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                           materialized = @[integerChoice(1, 0, 10, 0)]))
    let o = newOrchestrator(just(0), target, frontier, concolicBridge = bridge)
    for i in 0 ..< 5: discard admit(o, @[], o.run(@[]))
    let r = tryConcolicBridge(o, @[])
    check not r.ar.admitted
    check bridgeCalls == 0

  test "bridge configured, stallRounds > 0, but the frontier is NOT (yet) stalled: bridge never invoked":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                           materialized = @[integerChoice(1, 0, 10, 0)]))
    let o = newOrchestrator(just(0), target, frontier, concolicBridge = bridge, policy = orchestratorPolicy(stallRounds = 3))
    discard admit(o, @[], o.run(@[]))   # 1 admit, improves -> staleness 0, not stalled at k=3
    let r = tryConcolicBridge(o, @[])
    check not r.ar.admitted
    check bridgeCalls == 0

  test "stalled: a bridge that finds an admissible seed is admitted with provenance pvConcolic":
    # Models the RFC's magic-byte gate: mutation (`admit`'s ordinary path,
    # driven directly here to simulate the loop's own repeat admits) never
    # reaches the gate's coverage bit; the bridge hands back the exact
    # ChoiceSeq that does.
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      if x == 0xCAFEBABE: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8]))
      else: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0'u8])))
    var bridgeCalls: seq[int]
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      bridgeCalls.add targetBranchIndex
      ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                           materialized = @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
    let o = newOrchestrator(integers(0, 0xFFFFFFFF), target, frontier, concolicBridge = bridge, policy = orchestratorPolicy(stallRounds = 3))
    for i in 0 ..< 4:   # staleness climbs past k=3 without ever reaching slot 1
      discard admit(o, @[], o.run(@[integerChoice(0, 0, 0xFFFFFFFF, 0)]))
    check frontier.stalled(3)
    check frontier.coveredEdges == 1   # slot 1 (the gate) not yet covered
    let r = tryConcolicBridge(o, @[integerChoice(0, 0, 0xFFFFFFFF, 0)])
    check r.ar.admitted
    check r.ar.provenance == pvConcolic
    check bridgeCalls == @[0]           # first branch index tried was the winning one
    check frontier.coveredEdges == 2    # the gate edge is now folded into the SAME frontier
    check r.choices == @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]

  test "bounded branch-index attempts: tries indices in order, stops at the first admitted one":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      if x == 7: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8]))
      else: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0'u8])))
    var tried: seq[int]
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      tried.add targetBranchIndex
      if targetBranchIndex < 2:
        ConcolicBridgeResult(flip: oneShotFlip(cfoUnsat, ccoNotApplicable))   # first 2 indices: no model
      else:
        ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                             materialized = @[integerChoice(7, 0, 100, 0)]))
    let o = newOrchestrator(integers(0, 100), target, frontier, concolicBridge = bridge, policy = orchestratorPolicy(stallRounds = 1))
    discard admit(o, @[], o.run(@[integerChoice(0, 0, 100, 0)]))   # admit #1: improves (staleness 0)
    discard admit(o, @[], o.run(@[integerChoice(0, 0, 100, 0)]))   # admit #2: no improvement -> stalled(1)
    check frontier.stalled(1)
    let r = tryConcolicBridge(o, @[integerChoice(0, 0, 100, 0)])
    check r.ar.admitted
    check tried == @[0, 1, 2]           # exactly the bounded prefix, stops once solved+admitted

  test "concolicMaxBranchAttempts bounds the attempt count when nothing ever solves":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var tried: seq[int]
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      tried.add targetBranchIndex
      ConcolicBridgeResult(flip: oneShotFlip(cfoUnsat, ccoNotApplicable))
    let o = newOrchestrator(integers(0, 100), target, frontier, concolicBridge = bridge, policy = orchestratorPolicy(stallRounds = 1, concolicMaxBranchAttempts = 4))
    discard admit(o, @[], o.run(@[integerChoice(0, 0, 100, 0)]))   # admit #1: improves (staleness 0)
    discard admit(o, @[], o.run(@[integerChoice(0, 0, 100, 0)]))   # admit #2: no improvement -> stalled(1)
    check frontier.stalled(1)
    let r = tryConcolicBridge(o, @[integerChoice(0, 0, 100, 0)])
    check not r.ar.admitted
    check tried == @[0, 1, 2, 3]         # exactly the configured bound, no more

  test "a bridge-admitted seed still goes through re-verify when reVerify is on":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8])))
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      # Only branch index 0 ever "solves" — a realistic single-attempt
      # magic-byte-gate shape, so this test isolates re-verify's effect
      # rather than incidentally exhausting `reVerifyBudget` across 8
      # identical repeated attempts (a separate, already-covered E3a
      # fallback behavior — see tfuzzreverify.nim's budget-exhaustion test).
      if targetBranchIndex == 0:
        ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                             materialized = @[integerChoice(1, 0, 10, 0)]))
      else:
        ConcolicBridgeResult(flip: oneShotFlip(cfoUnmodelable, ccoNotApplicable))
    var freshCalls = 0
    let fresh = proc(): Worker[int] =
      inc freshCalls
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))   # pristine: does NOT confirm
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true, stallRounds = 1), concolicBridge = bridge)
    # ONE admit call already stalls: reVerify is on, so it goes through the
    # fresh-worker gate; the fresh worker is pristine (no coverage), so the
    # candidate's claimed [1,1] coverage is never folded in and the
    # frontier never improves at all (staleness == totalAdmitted == 1).
    discard admit(o, @[], o.run(@[]))
    check frontier.stalled(1)
    let r = tryConcolicBridge(o, @[])
    check not r.ar.admitted              # the fresh (pristine) re-verify never confirms the bridge's claim
    check freshCalls > 0                 # proves re-verify's fresh-worker path actually ran
    check frontier.coveredEdges == 0     # the bridge's claimed coverage was NEVER trusted directly
    # RFC-fuzzer-nextgen R28: solved + cleanly replayed (verdict vOk, never
    # rejected) + not admitted is EXACTLY `caoSupersededByRace` — this test
    # already produces that shape via re-verify's non-confirmation; proves
    # the outcome is attributed, not silently dropped as an unexplained
    # non-admission.
    check concolicYield(o).admitOutcomes[caoSupersededByRace] == 1
    check concolicYield(o).byConstruct.getOrDefault(wckIf, ConstructTally())
      .admitOutcomes[caoSupersededByRace] == 1

  test "R28: a solved, cleanly-replayed seed for an edge ordinary admission already covered is superseded-by-race, not silently dropped":
    # Models the RFC's literal "solved for an edge a sibling worker covered
    # by ordinary mutation before injection" case. No real N-worker Pool is
    # needed to produce it (the RFC's Pool was never built — see R28's own
    # scoping note): `tryConcolicBridge` only ever fires on a STALLED
    # frontier, i.e. after many prior admits already happened on this same
    # orchestrator — so "something else already covered this edge" is a
    # real, reachable sequencing within a single worker, not a hypothetical.
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      if x == 0xCAFEBABE: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8]))
      else: Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0'u8])))
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      # Only branch index 0 "solves" (mirrors the other fixtures' realistic
      # single-attempt shape) — for the value the frontier below already
      # covers: a correct solve (it IS the intended-branch flip),
      # reproducing a stale/aged corpus-entry target the bridge picked
      # before the gate was covered by ordinary admission. Every other
      # index is unmodelable, so the loop stops right after the one
      # superseded attempt instead of exhausting all 8.
      if targetBranchIndex == 0:
        ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                             materialized = @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
      else:
        ConcolicBridgeResult(flip: oneShotFlip(cfoUnmodelable, ccoNotApplicable))
    let o = newOrchestrator(integers(0, 0xFFFFFFFF), target, frontier, concolicBridge = bridge,
                            policy = orchestratorPolicy(stallRounds = 2))
    # 1: an ordinary admit covers the gate edge directly — stands in for
    # "a sibling worker already covered it" without needing a real Pool.
    discard admit(o, @[], o.run(@[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
    check frontier.coveredEdges == 2
    # 2: drive staleness back up past stallRounds with non-improving admits
    # (both slots are already covered, so these add nothing new).
    for i in 0 ..< 3:
      discard admit(o, @[], o.run(@[integerChoice(0, 0, 0xFFFFFFFF, 0)]))
    check frontier.stalled(2)
    # 3: the bridge "solves" (at index 0) for the SAME value the frontier
    # already covers, then goes unmodelable for the rest of the attempts.
    let r = tryConcolicBridge(o, @[integerChoice(0, 0, 0xFFFFFFFF, 0)])
    check not r.ar.admitted   # a genuinely correct solve, but nothing new to admit
    check concolicYield(o).admitOutcomes[caoSupersededByRace] == 1
    check concolicYield(o).admitOutcomes[caoAdmitted] == 0
    check concolicYield(o).byConstruct.getOrDefault(wckIf, ConstructTally())
      .admitOutcomes[caoSupersededByRace] == 1

suite "fuzz(): loop-level concolic-bridge wiring (RFC-fuzzer-nextgen G3 C3)":
  ## Exercises the GENERIC `fuzz()` loop directly (not the macro — that is
  ## the separate real-Z3 end-to-end cycle) with a fake bridge, to pin that
  ## the loop actually offers a stalled campaign the bridge each round and
  ## folds an admitted seed into the SAME corpus/energy bookkeeping every
  ## other admission uses.

  proc gateTarget(): Target[int] =
    Target[int](run: proc(x: int): Observation[int] =
      if x == 0xCAFEBABE:
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 1'u8]))
      else:
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0'u8])))

  test "a stalled campaign is offered the bridge each round, and an admitted seed reaches the gate":
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      if targetBranchIndex == 0:
        ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                             materialized = @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
      else:
        ConcolicBridgeResult(flip: oneShotFlip(cfoUnmodelable, ccoNotApplicable))
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings,
                      assist = ConcolicAssist(bridge: bridge, stallRounds: 1))
    check bridgeCalls > 0
    check frontier.coveredEdges == 2      # BOTH edges, including the magic-byte gate
    check report.coverageHits == 2

  test "the identical campaign with NO bridge wired (the pre-G3 default) never reaches the gate":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)   # stallRounds defaults to 0
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings)
    check frontier.coveredEdges == 1      # only the ordinary (non-gate) edge
    check report.coverageHits == 1

  test "an assist with an explicitly zeroed stallRounds is COERCED active, not silently inert":
    # RFC-z3-optional's resolution rule, and a deliberate inversion of what
    # this test used to assert. Under the pre-RFC two-key model, a bridge
    # plus `stallRounds: 0` was "opt-in required" — which meant the easy
    # mistake (supply the bridge, forget the second key) was a silent
    # no-op. Under the reified assist, passing an assist IS the request:
    # `stallRounds <= 0` resolves to 1 rather than disabling it. "Off" is
    # spelled by passing no assist, which the next test pins.
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      ConcolicBridgeResult(flip: oneShotFlip(cfoSolvedExact, ccoIntendedCovered,
                           materialized = @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)]))
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)
    discard fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings,
                 assist = ConcolicAssist(bridge: bridge))   # stallRounds NOT set
    check bridgeCalls > 0
    check frontier.coveredEdges == 2

  test "no assist at all (the zero value) is the off switch: the bridge is never built or called":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings)
    check frontier.coveredEdges == 1
    check report.stats.provenanceCounts[pvConcolic] == 0

  test "an activation policy with no bridge is refused before the campaign starts":
    # The raw-construction contract's raising half — the mirror image of
    # `processIsolation: true` without `spawnFreshWorker`. Coercing here
    # would silently run an assist-less campaign the caller explicitly
    # configured for assist, which is the original auto-wiring bug wearing
    # a different field.
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)
    expect ConcolicAssistError:
      discard fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings,
                   assist = ConcolicAssist(stallRounds: 1))
