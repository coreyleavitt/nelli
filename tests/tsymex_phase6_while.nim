## Phase 6 — while loop k-unrolling.
##
## The walker unrolls each loop up to `maxLoopUnwind` times. Each
## iteration forks on the guard: the cond=true branch walks the
## body and continues; the cond=false branch exits. After k
## iterations, surviving paths get marked uncertain (sawUnknown).
import std/unittest
import proptest/symex

suite "symex Phase 6 — while":
  test "tracer: target reachable only after loop body executes":
    proc loopToThree(x: int) =
      var i = 0
      while i < x:
        i = i + 1
      if i == 3:
        symexTarget("hit")
    let r = symexFind(loopToThree, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] >= 3

  test "unwind exhaustion → sxUnknown when target needs > maxLoopUnwind":
    # Target only reachable when i == 100, which needs 100 loop
    # iterations. With the default unwindDepth = 5, the path that
    # would have reached i = 100 gets marked uncertain.
    proc loopToHundred(x: int) =
      var i = 0
      while i < x:
        i = i + 1
      if i == 100:
        symexTarget("deep")
    let r = symexFind(loopToHundred, tLabel("deep"))
    check r.status == sxUnknown
