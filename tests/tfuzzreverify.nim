## RFC-fuzzer-nextgen E3a — freshness machinery.
##
## C1: the orchestrator-owned finding record (Appendix C) — `reportFinding`
## opens/dedups by `CrashKind`, the first report's `CrashInfo` is immutable,
## `recordDivergentReproduction`/`divergentReproduction` track the observed
## variant set, and `sampleReproduction` is the bounded, off-the-hot-path
## N-of-M `reproRate` sampler. None of this cycle touches `admit`'s
## re-verify gating (that's C2, below) — every test here either drives the
## finding-record API directly or exercises `sampleReproduction` against a
## FAKE in-process `spawnFreshWorker` (never a real process), matching the
## RFC's "pure algebra, not raced processes" mandate for the structural
## suite.

import std/[unittest, options, algorithm]
import nelli

suite "fuzz: Orchestrator finding record (RFC-fuzzer-nextgen E3a C1)":
  test "reportFinding opens a finding whose reproRate starts at 1.0 (the report IS its first sample)":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    let crash = CrashInfo(kind: ckSignal, signal: 11, message: "sig 11")
    let id = reportFinding(o, crash)
    check reproRate(o, id) == 1.0
    check divergentReproduction(o, id).len == 0

  test "reportFinding dedups by CrashKind: a second report of the same kind returns the SAME handle":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    let crashA = CrashInfo(kind: ckSignal, signal: 11, message: "first sighting")
    let crashB = CrashInfo(kind: ckSignal, signal: 11, message: "different message, same kind")
    let idA = reportFinding(o, crashA)
    let idB = reportFinding(o, crashB)
    check idA == idB

  test "recordDivergentReproduction records a distinct-kind variant, idempotent per kind":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    let primary = CrashInfo(kind: ckSignal, signal: 11, message: "SIGSEGV")
    let id = reportFinding(o, primary)
    let variant = CrashInfo(kind: ckSignal, signal: 7, message: "SIGBUS")
    recordDivergentReproduction(o, id, variant)
    recordDivergentReproduction(o, id, variant)   # repeat: must not duplicate
    check divergentReproduction(o, id).len == 1
    check divergentReproduction(o, id)[0].signal == 7

  test "recordDivergentReproduction never rewrites the finding's primary crash":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)
    let primary = CrashInfo(kind: ckSignal, signal: 11, message: "SIGSEGV")
    let id = reportFinding(o, primary)
    recordDivergentReproduction(o, id, CrashInfo(kind: ckExitCode, exitCode: 134, message: "abrt"))
    # The dedup handle for the ORIGINAL kind still resolves to the SAME
    # finding (primary untouched) — a fresh reportFinding call for the
    # primary's own kind is still idempotent, not opening a second finding.
    let idAgain = reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "re-seen"))
    check idAgain == id
    check divergentReproduction(o, id).len == 1
    check divergentReproduction(o, id)[0].kind == ckExitCode

  test "sampleReproduction is a no-op (false, no state change) when spawnFreshWorker is unset":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)   # default: no spawnFreshWorker
    let id = reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "x"))
    check sampleReproduction(o, id, @[]) == false
    check reproRate(o, id) == 1.0   # unchanged — the seed 1/1 from reportFinding

  test "sampleReproduction folds a flaky reproduction rate: 2 confirms + 1 miss out of the 1/1 seed":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var callN = 0
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        inc callN
        # sample 1 and 2 confirm SIGSEGV; sample 3 misses (clean run, no crash)
        if callN <= 2:
          Observation[int](verdict: vInteresting,
                           crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "repro")))
        else:
          Observation[int](verdict: vOk))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reproSamples = 10))
    let id = reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "orig"))
    check reproRate(o, id) == 1.0   # 1/1 seed
    check sampleReproduction(o, id, @[])   # sample 1: confirms -> 2/2
    check reproRate(o, id) == 1.0
    check sampleReproduction(o, id, @[])   # sample 2: confirms -> 3/3
    check reproRate(o, id) == 1.0
    check sampleReproduction(o, id, @[])   # sample 3: misses -> 3/4
    check reproRate(o, id) == 0.75

  test "sampleReproduction never exceeds its M cap (reproSamples), and reports false once reached":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var callN = 0
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        inc callN
        Observation[int](verdict: vInteresting,
                         crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "repro"))))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reproSamples = 2))
    let id = reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "orig"))
    # reportFinding already seeded reproTotal=1 (M's first sample, the report
    # itself) — with M=2, exactly ONE more sampleReproduction call fits.
    check sampleReproduction(o, id, @[])            # sample 2/2 -> reproTotal reaches the cap
    check callN == 1
    check sampleReproduction(o, id, @[]) == false   # capped: no further spawn
    check callN == 1                                 # confirms the cap actually skipped the spawn
    check reproRate(o, id) == 1.0

  test "sampleReproduction records a divergent-kind sample as a variant, not a primary rewrite":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vInteresting,
                         crash: some(CrashInfo(kind: ckExitCode, exitCode: 134, message: "diverged"))))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reproSamples = 5))
    let id = reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "orig"))
    check sampleReproduction(o, id, @[])
    check reproRate(o, id) == 0.5              # 1/2: the divergent sample is NOT a "hit" for the primary kind
    check divergentReproduction(o, id).len == 1
    check divergentReproduction(o, id)[0].kind == ckExitCode

# --- C2: re-verify gates ADMISSION, never REPORTING (RFC §0) --------------
#
# Every test below drives `admit` with `reVerify = true` and a FAKE
# in-process `spawnFreshWorker` — never a real subprocess (that's reserved
# for the one sanctioned characterization test, RFC-fuzzer-nextgen E3a C4,
# in tests/tfuzzforkworker.nim). `reVerify`'s enable/disable knob DEFAULTS
# to `false` (see `Orchestrator.reVerify`'s doc in fuzz.nim) — every OTHER
# `tfuzz*`/`tdb` suite, and `fuzz()`'s own internal Orchestrator, never sets
# it, so none of them observe any behavior change from this cycle. Only the
# tests below opt in explicitly.

suite "fuzz: Orchestrator.admit re-verify gates admission (RFC-fuzzer-nextgen E3a C2)":
  test "re-verify OFF (the default): admit is the exact E1/E2 direct fold over the candidate's own coverage":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier)   # reVerify defaults to false
    let obs = o.run(@[])
    let ar = admit(o, @[], obs)
    check ar.admitted
    check frontier.coveredEdges == 1

  test "re-verify ON: a candidate the fresh worker confirms IS admitted, off the fresh (authoritative) coverage":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))   # confirms
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true))
    let candidate = Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8]))
    let ar = admit(o, @[], candidate)
    check ar.admitted
    check frontier.coveredEdges == 1

  test "re-verify ON: a CONTAMINATED candidate (claims new coverage) is DISCARDED when the fresh worker doesn't confirm it":
    # Models a state-leaking property: some prior input left process-global
    # state behind, so a REUSED (contaminated) worker's candidate observation
    # reports coverage it didn't genuinely earn this run. A freshly spawned
    # worker re-executing the SAME input from a pristine state sees nothing
    # new. Admission must follow the fresh worker, not the candidate.
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))   # pristine: nothing new
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true))
    let contaminatedCandidate = Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8]))
    let ar = admit(o, @[], contaminatedCandidate)
    check not ar.admitted
    check frontier.coveredEdges == 0   # the contaminated candidate's coverage was NEVER folded in

  test "re-verify ON: a boring candidate (no new coverage, no crash) never pays for a fresh spawn (cheap pre-filter)":
    var frontier = newCoverageFrontier()
    discard frontier.admit(Coverage(counters: @[1'u8]))   # slot 0 already known
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var spawnCalls = 0
    let fresh = proc(): Worker[int] =
      inc spawnCalls
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true))
    let boring = Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8]))   # already-known edge only
    let ar = admit(o, @[], boring)
    check not ar.admitted
    check spawnCalls == 0

  test "re-verify ON: the bounded slot budget exhausts and falls back to the direct fold instead of stalling":
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var spawnCalls = 0
    let fresh = proc(): Worker[int] =
      inc spawnCalls
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))   # would NOT confirm
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true, reVerifyBudget = 1))
    let candidate = Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8, 0]))
    let arFirst = admit(o, @[], candidate)   # spends the ONE budgeted slot; fresh worker does NOT confirm
    check not arFirst.admitted
    check spawnCalls == 1
    # budget now exhausted: a SECOND interesting candidate degrades to the
    # cheap direct fold (never blocks) — admitted on the CANDIDATE's own
    # coverage this time, since no fresh spawn is available to gate it.
    let candidate2 = Observation[int](verdict: vOk, coverage: Coverage(counters: @[0'u8, 1'u8]))
    let arSecond = admit(o, @[], candidate2)
    check arSecond.admitted
    check spawnCalls == 1   # no further spawn attempted

  test "re-verify ON: a candidate crash IS reported by the caller off the CANDIDATE observation itself, regardless of admit's outcome":
    # §0 precondition 1: reporting is never gated. `admit` only ever decides
    # CORPUS admission; a caller (the fuzz loop) reports a crash off `obs`
    # (the worker/candidate observation) the moment it sees one — this test
    # demonstrates that path is entirely independent of what `admit` (and
    # therefore the fresh re-verify) decides.
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                       crash: some(CrashInfo(kind: ckException, defect: "FalsifiedError", message: "boom"))))
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))   # doesn't confirm -> admission denied
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true))
    let obs = o.run(@[])
    check obs.verdict == vInteresting
    check obs.crash.isSome   # <- this is what a caller reports, unconditionally, right here
    let ar = admit(o, @[], obs)
    check not ar.admitted    # admission still gated and denied
    check ar.findingId.isSome   # but the finding record WAS opened off the candidate's crash
    check reproRate(o, ar.findingId.get) == 1.0

  test "re-verify ON: a kind-mismatch on re-verify is recorded as divergentReproduction, primary stays the candidate's kind":
    # A genuinely different CrashKind (not just a different field within the
    # same kind) — e.g. the candidate observed a signal death, but the fresh
    # re-verify of a nondeterministic target instead exits nonzero. §0's
    # in-scope nondeterminism case (multi-threaded/hash-randomized/timing
    # targets can legitimately vary run to run).
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                       crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "sigsegv"))))
    let fresh = proc(): Worker[int] =
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                         crash: some(CrashInfo(kind: ckExitCode, exitCode: 134, message: "abrt"))))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true))
    let obs = o.run(@[])
    let ar = admit(o, @[], obs)
    check ar.findingId.isSome
    let variants = divergentReproduction(o, ar.findingId.get)
    check variants.len == 1
    check variants[0].kind == ckExitCode
    check variants[0].exitCode == 134
    # first-report immutable: reporting the SAME primary kind again still
    # resolves to this one finding, not a second one.
    check reportFinding(o, CrashInfo(kind: ckSignal, signal: 11, message: "re-seen")) == ar.findingId.get

# --- C3: order-independent fold — PURE ALGEBRA (RFC-fuzzer-nextgen E3a C3) -
#
# Feeds FABRICATED `Coverage`/crash sequences to `Orchestrator.admit` in
# every permutation of a small fixed set and asserts the resulting
# frontier/corpus state is IDENTICAL regardless of feed order —
# deterministic (a `spawnFreshWorker` fake keyed only by the input's
# `len`, never real timing or process concurrency), matching the RFC's
# explicit "pure algebra, not raced processes" mandate for this class of
# claim. `reVerifyBudget` is set generously high in every test here so no
# permutation ever falls through the budget-exhaustion fallback (a
# DIFFERENT, already-covered behavior — see C2's dedicated budget test) —
# that would make the comparison apples-to-oranges across orders.

suite "fuzz: order-independent fold — pure algebra (RFC-fuzzer-nextgen E3a C3)":
  test "disjoint-edge candidates admit identically regardless of feed order (3! = 6 permutations)":
    let coverageFor = @[
      Coverage(counters: @[1'u8, 0'u8, 0'u8]),
      Coverage(counters: @[0'u8, 1'u8, 0'u8]),
      Coverage(counters: @[0'u8, 0'u8, 1'u8]),
    ]
    proc runInOrder(order: seq[int]): tuple[coveredEdges: int, admitted: seq[bool]] =
      var frontier = newCoverageFrontier()
      let fresh = proc(): Worker[int] =
        newWorker(proc(input: ChoiceSeq): Observation[int] =
          Observation[int](verdict: vOk, coverage: coverageFor[input.len]))
      let target = Target[int](run: proc(x: int): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))
      let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true, reVerifyBudget = 100))
      var admittedByIdx = newSeq[bool](3)
      for idx in order:
        let input = newSeq[ChoiceNode](idx)              # discriminated only by length
        let candidate = Observation[int](verdict: vOk, coverage: coverageFor[idx])
        admittedByIdx[idx] = admit(o, input, candidate).admitted
      (coveredEdges: frontier.coveredEdges, admitted: admittedByIdx)

    var perm = @[0, 1, 2]
    var results: seq[tuple[coveredEdges: int, admitted: seq[bool]]]
    results.add runInOrder(perm)
    while nextPermutation(perm):
      results.add runInOrder(perm)
    check results.len == 6                                # every one of 3! orders exercised
    for r in results:
      check r.coveredEdges == 3
      check r.admitted == @[true, true, true]

  test "a state-leaking (contaminated) candidate is NEVER admitted, in EITHER feed order, next to a genuine one":
    # input 0: genuine — the fresh worker confirms exactly what the candidate claimed.
    # input 1: contaminated — the candidate claims a new edge a PRISTINE run never
    # actually earns (models a worker reused across inputs leaking prior state).
    let genuineCov = Coverage(counters: @[1'u8, 0'u8])
    let contaminatedClaim = Coverage(counters: @[0'u8, 1'u8])
    proc runInOrder(order: seq[int]): tuple[coveredEdges: int; admitted: array[2, bool]] =
      var frontier = newCoverageFrontier()
      let fresh = proc(): Worker[int] =
        newWorker(proc(input: ChoiceSeq): Observation[int] =
          if input.len == 0: Observation[int](verdict: vOk, coverage: genuineCov)
          else: Observation[int](verdict: vOk, coverage: Coverage(counters: @[0'u8, 0'u8])))  # pristine: nothing new
      let target = Target[int](run: proc(x: int): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))
      let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true, reVerifyBudget = 100))
      var admitted: array[2, bool]
      for idx in order:
        let input = newSeq[ChoiceNode](idx)
        let candidate =
          if idx == 0: Observation[int](verdict: vOk, coverage: genuineCov)
          else: Observation[int](verdict: vOk, coverage: contaminatedClaim)   # contaminated claim
        admitted[idx] = admit(o, input, candidate).admitted
      (coveredEdges: frontier.coveredEdges, admitted: admitted)

    for order in [@[0, 1], @[1, 0]]:
      let r = runInOrder(order)
      check r.admitted[0]              # genuine: admitted
      check not r.admitted[1]          # contaminated: discarded, regardless of order
      check r.coveredEdges == 1        # only the genuine edge ever entered the frontier

  test "divergent-kind recording is order-independent: one finding, one variant, in EITHER feed order":
    # Two inputs share the SAME primary crash kind (ckSignal) on first
    # observation; one of them diverges to ckExitCode on fresh re-verify.
    # Dedup-by-kind means both candidates open (or reuse) the SAME finding
    # regardless of which is processed first.
    proc runInOrder(order: seq[int]): tuple[findingCount: int; variantCount: int] =
      var frontier = newCoverageFrontier()
      let fresh = proc(): Worker[int] =
        newWorker(proc(input: ChoiceSeq): Observation[int] =
          if input.len == 0:
            Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                             crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "confirmed")))
          else:
            Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[0'u8, 1'u8]),
                             crash: some(CrashInfo(kind: ckExitCode, exitCode: 134, message: "diverged"))))
      let target = Target[int](run: proc(x: int): Observation[int] =
        Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))
      let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(reVerify = true, reVerifyBudget = 100))
      var ids: seq[FindingId]
      for idx in order:
        let input = newSeq[ChoiceNode](idx)
        let candidate = Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                                         crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "orig")))
        let ar = admit(o, input, candidate)
        check ar.findingId.isSome
        ids.add ar.findingId.get
      check ids[0] == ids[1]            # same finding, either order
      (findingCount: 1, variantCount: divergentReproduction(o, ids[0]).len)

    for order in [@[0, 1], @[1, 0]]:
      let r = runInOrder(order)
      check r.findingCount == 1
      check r.variantCount == 1

# --- C4 (pure-algebra half): worker recycling policy -----------------------
#
# The REAL fork-per-input snapshot-invariant characterization test (the ONE
# process-spawning test the RFC sanctions for this slice) lives in
# tests/tfuzzforkworker.nim. The recycling POLICY itself — retire the
# current worker after N inputs, or immediately on any crash — is pure
# bookkeeping over the `spawnFreshWorker` seam and is tested here with a
# fake worker factory, no process involved.

suite "fuzz: Orchestrator worker recycling policy (RFC-fuzzer-nextgen E3a C4)":
  test "the default (no spawnFreshWorker) never recycles — the SAME worker answers every run":
    var frontier = newCoverageFrontier()
    var calls = 0
    let target = Target[int](run: proc(x: int): Observation[int] =
      inc calls
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))
    let o = newOrchestrator(just(0), target, frontier)   # no spawnFreshWorker at all: recycling is inert
    for i in 0 ..< 5: discard o.run(@[])
    check calls == 5   # every run reached the SAME original worker/target, nothing substituted

  test "recycleAfterInputs retires the worker every N inputs (generation increments on schedule)":
    var frontier = newCoverageFrontier()
    var generation = 0
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[])))
    let fresh = proc(): Worker[int] =
      inc generation
      let myGen = generation
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, message: $myGen))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(recycleAfterInputs = 2))
    # Worker 0 (the ORIGINAL, from `target`, not `fresh`) serves inputs 1-2;
    # after the 2nd, it's retired -> generation becomes 1 (worker 1) serving
    # inputs 3-4; after the 4th, generation becomes 2 (worker 2) for input 5.
    var seenGenerations: seq[string]
    for i in 0 ..< 5:
      seenGenerations.add o.run(@[]).message
    check generation == 2
    check seenGenerations == @["", "", "1", "1", "2"]   # original worker's Target never sets .message

  test "a vCrashed observation forces immediate recycling, regardless of recycleAfterInputs":
    var frontier = newCoverageFrontier()
    var generation = 0
    var callN = 0
    let target = Target[int](run: proc(x: int): Observation[int] =
      inc callN
      if callN == 1: Observation[int](verdict: vCrashed, crash: some(CrashInfo(kind: ckSignal, signal: 11, message: "dead")))
      else: Observation[int](verdict: vOk))
    let fresh = proc(): Worker[int] =
      inc generation
      let myGen = generation
      newWorker(proc(input: ChoiceSeq): Observation[int] =
        Observation[int](verdict: vOk, message: $myGen))
    let o = newOrchestrator(just(0), target, frontier, spawnFreshWorker = fresh, policy = orchestratorPolicy(recycleAfterInputs = 100))    # count-based recycling would NOT fire this soon
    discard o.run(@[])          # crashes on the ORIGINAL worker
    check generation == 1        # recycled immediately, despite the count budget being nowhere near hit
    let obs2 = o.run(@[])
    check obs2.message == "1"    # the NEW (generation-1) worker answered this one
