## Phase 6a (docs/fuzz/FUZZ_PLAN.md): crash de-duplication in the fuzz loop. Default key is
## the coverage edge-set fingerprint combined with the crash message (keep-first), so the
## same bug hit a thousand ways is reported once. Opt out with `keepAllCrashes`, or supply a
## custom `crashKey`. Driven by stub `Target`s — pure, no subprocess.

import std/[unittest, options]
import nelli

# A stub target whose Observation we control, so dedup is driven deterministically.
proc fixedCrash(cov: Coverage; msg: string): Target[int] =
  Target[int](run: proc(x: int): Observation[int] =
    Observation[int](verdict: vInteresting, coverage: cov, message: msg))

proc countingCrash(): Target[int] =
  ## Each run reports a distinct crash (message varies), same coverage.
  var n = 0
  Target[int](run: proc(x: int): Observation[int] =
    inc n
    Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                     message: "crash-" & $n))

proc alternatingKindSameMessage(): Target[int] =
  ## RFC-fuzzer-nextgen E1 (C1): every run reports the SAME coverage+message —
  ## which, pre-C1, was the entire default crash key and would collapse to one
  ## finding — but alternates `CrashInfo.kind` between `ckException`/`ckSignal`.
  ## Pins that the default key now folds `kind` in, so the two kinds are NOT
  ## conflated, while each kind on its own still keeps-first (the existing 6a
  ## behavior, unchanged).
  var n = 0
  Target[int](run: proc(x: int): Observation[int] =
    inc n
    let cov = Coverage(counters: @[1'u8])
    let info = if n mod 2 == 1: CrashInfo(kind: ckException, defect: "Defect", message: "boom")
               else: CrashInfo(kind: ckSignal, signal: 11, message: "boom")
    Observation[int](verdict: vInteresting, coverage: cov, message: "boom", crash: some(info)))

const N = 12

suite "fuzz: crash de-duplication (Phase 6a)":
  test "same crash key collapses to one finding (keep-first, default)":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), fixedCrash(Coverage(counters: @[1'u8, 0, 1]), "boom"),
                   frontier, FuzzSettings(maxIterations: N, seed: 1))
    check rep.iterations == N
    check rep.irCrashes.len == 1                      # all N runs are the same bug

  test "distinct crash keys are all retained":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1))
    check rep.irCrashes.len == N                       # every run is a different bug

  test "keepAllCrashes opts out of de-duplication":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), fixedCrash(Coverage(counters: @[1'u8]), "boom"),
                   frontier, FuzzSettings(maxIterations: N, seed: 1, keepAllCrashes: true))
    check rep.irCrashes.len == N

  test "a custom crashKey overrides the default":
    var frontier = newCoverageFrontier()
    # countingCrash varies the message, but a key that ignores message collapses them.
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1,
                                crashKey: proc(cov: Coverage; message: string): string = "same"))
    check rep.irCrashes.len == 1

  test "same coverage+message but different CrashInfo.kind does not collapse (E1 C1)":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), alternatingKindSameMessage(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1))
    check rep.irCrashes.len == 2               # one per kind — kind is now part of the key
