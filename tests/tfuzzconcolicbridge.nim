## RFC-fuzzer-nextgen G3 (deliverables 2/3) — stall-gated concolic-bridge
## invocation + re-verified admission into the corpus, PURE ALGEBRA over a
## FAKE `ConcolicBridgeEntry` (never a real Z3 call — that's the macro-wired
## `fuzzmacro.nim` integration, exercised end-to-end separately). Mirrors
## E3a's `tfuzzreverify.nim` idiom: a fabricated closure standing in for the
## real mechanism, so this suite is deterministic and fast.

import std/[unittest, options]
import nelli
import nelli/choice

suite "fuzz: Orchestrator.tryConcolicBridge (RFC-fuzzer-nextgen G3)":
  test "no bridge configured (the default): inert, frontier untouched":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier, stallRounds = 1)
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
      ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                           materialized: @[integerChoice(1, 0, 10, 0)])
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
      ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                           materialized: @[integerChoice(1, 0, 10, 0)])
    let o = newOrchestrator(just(0), target, frontier, concolicBridge = bridge, stallRounds = 3)
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
      ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                           materialized: @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)])
    let o = newOrchestrator(integers(0, 0xFFFFFFFF), target, frontier,
                            concolicBridge = bridge, stallRounds = 3)
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
        ConcolicBridgeResult(outcome: coUnsat, coverage: ccNotApplicable)   # first 2 indices: no model
      else:
        ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                             materialized: @[integerChoice(7, 0, 100, 0)])
    let o = newOrchestrator(integers(0, 100), target, frontier,
                            concolicBridge = bridge, stallRounds = 1)
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
      ConcolicBridgeResult(outcome: coUnsat, coverage: ccNotApplicable)
    let o = newOrchestrator(integers(0, 100), target, frontier,
                            concolicBridge = bridge, stallRounds = 1,
                            concolicMaxBranchAttempts = 4)
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
        ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                             materialized: @[integerChoice(1, 0, 10, 0)])
      else:
        ConcolicBridgeResult(outcome: coUnmodelable, coverage: ccNotApplicable)
    var freshCalls = 0
    let fresh = proc(): Worker[int] =
      inc freshCalls
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))   # pristine: does NOT confirm
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh,
                            reVerify = true, concolicBridge = bridge, stallRounds = 1)
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
        ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                             materialized: @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)])
      else:
        ConcolicBridgeResult(outcome: coUnmodelable, coverage: ccNotApplicable)
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5, stallRounds: 1)
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings,
                      concolicBridge = bridge)
    check bridgeCalls > 0
    check frontier.coveredEdges == 2      # BOTH edges, including the magic-byte gate
    check report.coverageHits == 2

  test "the identical campaign with NO bridge wired (the pre-G3 default) never reaches the gate":
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)   # stallRounds defaults to 0
    let report = fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings)
    check frontier.coveredEdges == 1      # only the ordinary (non-gate) edge
    check report.coverageHits == 1

  test "a bridge wired but stallRounds left at 0 (the default) is never invoked (opt-in required)":
    var bridgeCalls = 0
    let bridge = proc(trace: ChoiceSeq; targetBranchIndex: int): ConcolicBridgeResult =
      inc bridgeCalls
      ConcolicBridgeResult(outcome: coSolved, coverage: ccIntendedCovered,
                           materialized: @[integerChoice(0xCAFEBABE, 0, 0xFFFFFFFF, 0)])
    var frontier = newCoverageFrontier()
    let settings = FuzzSettings(seed: 42'u64, maxIterations: 5)   # stallRounds NOT set
    discard fuzz(integers(0, 0xFFFFFFFF), gateTarget(), frontier, settings, concolicBridge = bridge)
    check bridgeCalls == 0
    check frontier.coveredEdges == 1
