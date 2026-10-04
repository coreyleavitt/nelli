## RFC-0005 (soundness channels) slice S8bk -- address-of-argument timing:
## a `var` formal forwarded on, the declines where a later call changes what
## an address check read (Nim then accesses through a value it never
## checked), and calls through a proc value (RFC-0005 batch 5). Split out of
## `tsymex_rfc0005_s8bk_argtiming` by RFC-0005 S8br, so each file compiles
## and runs under 60 s on each backend; that file's header has the subject.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

include s8bk_argtiming_fixture

suite "S8bk: address checks, forwarded formals, proc values":

  test "nim":
    gP = Box(x: 10)
    var old = gP
    fwd(gP.x)
    check old.x == 15 and gP.x == 100
    gArr = [10, 20, 30]
    gi = 0
    touch(gArr[gi], incI())
    check gArr == [10, 25, 30]
    block:
      # RFC-0005 batch 5: through a proc value.
      let f = touch
      gP = Box(x: 10)
      old = gP
      f(gP.x, moveP())
      check old.x == 10 and gP.x == 105
      let g = touchP
      gP = Box(x: 10)
      old = gP
      g(addr gP.x, moveP())
      check old.x == 10 and gP.x == 105
      gArr = [10, 20, 30]
      gi = 0
      f(gArr[gi], incI())
      check gArr == [10, 25, 30]

  test "a var formal forwarded on":
    replays(sutFwd, "fw")
    discard verdict(sutFwd, "fw_dead", sxUnsat)

  test "a later call changes what an address check read":
    declines(sutIdxMoved, "im")
    declines(sutSeqShrunk, "ss")
    declines(sutRefElemMoved, "rm")
    block:
      let r = symexFind(sutHeapIdx, tLabel("hx"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.errors.hasKind(feEvalOrderUnmodelled)
      check "may change what the check read" in show(r.errors)
    replays(sutIdxKept, "ik")
    discard verdict(sutIdxKept, "ik_dead", sxUnsat)

  test "through a proc value (RFC-0005 batch 5)":
    ## RED at the batch-5 S8bk merge before `closureCallIR` took the late
    ## address: `cl` unreached and `cl_dead` a false `sxSat`.
    replays(sutClosure, "cl")
    discard verdict(sutClosure, "cl_dead", sxUnsat)
    discard verdict(sutClosureAddr, "ca", sxSat)
    discard verdict(sutClosureAddr, "ca_dead", sxUnsat)
    declines(sutClosureIdxMoved, "cm")
