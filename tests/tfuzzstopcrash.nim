## F4 (RFC-chapulin-hardening ~line 634): `FuzzSettings.stopOnFirstCrash` halts the
## fuzz loop as soon as the first NEW (de-duped) crash is recorded, instead of
## running out the full `maxIterations` budget. "New" means: the crash's
## `crashKey` was not already in the loop's de-dup set — a duplicate of an
## already-seen crash is not a new finding and must not trigger the stop.
## Default `false` preserves the pre-F4 full-budget trajectory (pinned by
## `tfuzzdedup`/`tfuzzloop`). Driven by stub `Target`s — pure, no subprocess.

import std/unittest
import nelli

proc countingCrash(): Target[int] =
  ## Each run reports a distinct crash (message varies) => every run is a NEW
  ## finding under the default coverage+message crashKey.
  var n = 0
  Target[int](run: proc(x: int): Observation[int] =
    inc n
    Observation[int](verdict: vInteresting, coverage: Coverage(counters: @[1'u8]),
                     message: "crash-" & $n))

proc fixedCrash(cov: Coverage; msg: string): Target[int] =
  ## Every run reports the exact same crash => only the first is "new".
  Target[int](run: proc(x: int): Observation[int] =
    Observation[int](verdict: vInteresting, coverage: cov, message: msg))

const N = 20

suite "fuzz: stopOnFirstCrash (F4)":
  test "stops the loop at the first new crash":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1, stopOnFirstCrash: true))
    check rep.irCrashes.len == 1
    check rep.iterations < N                # stopped early, not the full budget
    check rep.iterations >= 1

  test "default (false) runs the full budget and can record many de-duped crashes":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1))
    check rep.iterations == N
    check rep.irCrashes.len == N            # unchanged default de-dup behavior (6a)

  test "a duplicate crash is correctly identified as not-new (the break's gating condition)":
    # NOTE on what's cleanly testable here: within a single `fuzz()` call,
    # `seenCrashKeys` starts empty, so the very FIRST crash observed — of any
    # key — is unconditionally "new". That means it is impossible to observe a
    # duplicate arising *before* the loop's first (necessarily new) crash, and
    # under `stopOnFirstCrash: true` that first crash always halts the loop
    # immediately — so a run that reaches a genuine duplicate under that flag
    # can never happen (the loop is already stopped by the time one would
    # occur). "A duplicate doesn't trigger the stop" is therefore not a
    # reachable black-box scenario to assert on directly; what IS testable,
    # and what the implementation shares one boolean for (`isNewCrash`, fuzz.nim
    # ~511-519), is that the exact same predicate gates both crash retention
    # (dedup, pre-existing 6a behavior) and the new F4 break. This test pins
    # that shared predicate: with `stopOnFirstCrash: false`, the fixed-key
    # target produces N `vInteresting` runs but only 1 is ever "new" — proving
    # `isNewCrash` is false on every one of the (N-1) duplicates. Since the
    # break is `if settings.stopOnFirstCrash and isNewCrash: break`, an
    # `isNewCrash == false` run can never trigger it regardless of the flag.
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), fixedCrash(Coverage(counters: @[1'u8]), "boom"),
                   frontier, FuzzSettings(maxIterations: N, seed: 1, stopOnFirstCrash: false))
    check rep.irCrashes.len == 1            # de-duped: only the first occurrence was new
    check rep.iterations == N               # duplicates never affect loop control

  test "stopOnFirstCrash + keepAllCrashes: still stops on the first new crash (retention only)":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1, stopOnFirstCrash: true,
                                keepAllCrashes: true))
    check rep.irCrashes.len == 1
    check rep.iterations < N

  test "deterministic in the seed":
    proc run(): FuzzReport =
      var f = newCoverageFrontier()
      fuzz(just(0), countingCrash(), f,
           FuzzSettings(maxIterations: N, seed: 5, stopOnFirstCrash: true))
    let a = run()
    let b = run()
    check a.iterations == b.iterations
    check a.irCrashes.len == b.irCrashes.len
    check a.irCrashes[0].message == b.irCrashes[0].message

  test "report stays well-formed on early stop: coverageHits mirrors the frontier":
    var frontier = newCoverageFrontier()
    let rep = fuzz(just(0), countingCrash(), frontier,
                   FuzzSettings(maxIterations: N, seed: 1, stopOnFirstCrash: true))
    check rep.coverageHits == frontier.coveredEdges   # post-loop bookkeeping still ran
    check rep.corpus.kind == fckIR                    # corpus field still well-formed
