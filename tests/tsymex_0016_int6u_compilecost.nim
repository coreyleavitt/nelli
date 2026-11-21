## RFC-0016 CR4-H1 (round 3): compile cost. A routine declared inside a
## `suite`/`test` block is a module-level call's argument, so the scan reads
## the callee's expansion. That read once walked every module reachable from
## the imports once per identifier of every template body it met, and a file
## importing nelli, nelli/symex and the shared helpers failed to compile
## ("interpretation requires too many iterations"). It is indexed by scope
## now, each module once. No `maxLoopIterationsVM` is set here or anywhere.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

type R = range[0 .. 10]

suite "r3":
  test "x":
    proc inner(w: int): int = int(R(w))
    proc outer(v: int) =
      if inner(v) == 300: symexTarget("hit")
    let x = symexFind(outer, tLabel("hit"))
    checkpoint show(x.errors)
    check x.status in {sxRaised, sxUnsat, sxSat, sxUnknown}
  test "y":
    proc inner2(w: int): int = int(R(w))
    proc outer2(v: int) =
      if inner2(v) == 300: symexTarget("hit")
    check native(outer2(300)) == "RangeDefect"
    let x = pinFind(outer2, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
