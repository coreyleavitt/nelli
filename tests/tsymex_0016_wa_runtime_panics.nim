## RFC-0016 WA-B S4 under `--panics:on` (`.nim.cfg`). A Defect is not
## catchable there, so it is a crash claim whose witness ends the process.
## When that witness renders lossily the replay is out of scope
## (`replayNotRun`, `endsChild` false) and used to overwrite the claim's own
## `witnessUnsafe`: `hostRunnable` was true and `assertCoveredBy` ran it in the
## host, which killed the process.
import std/[unittest, strutils]
import nelli
import nelli/symex

type
  WpDist = object
    x: int
    ys: seq[(int, int)]   # no heap cell holds this: the witness is lossy
  WpBox = object
    n: int
    s: WpDist

proc lossyOverflow(p: ref WpBox) =
  if p != nil and p.n == high(int):
    discard p.n + 1

suite "WA-B S4: a lossy Defect claim under --panics:on":
  test "the build is a panics build":
    check defined(nimPanics)
    check parseInt(symexWalkerVersion) >= 286

  test "the verdict is unsafe and not host-runnable":
    let r = symexFind(lossyOverflow, tRaisedExn("OverflowDefect"))
    checkpoint $r.status & " " & $r.soundness
    check r.status == sxRaised
    check r.soundness.witnessUnsafe
    check not hostRunnable(r.soundness)
