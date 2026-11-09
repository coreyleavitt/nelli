## RFC-0016 K7 / CRH-01 (RED, NOT registered in nelli.nimble): `for l in
## s.splitLines` over an UNBOUNDED symbolic string must end in a typed cap, not
## run unbounded. Today it is killed (600 s): the nested loops multiply a
## k-unroll's active set (33, then 594 paths, ...) and a live-path cap does not
## bound total work (maxLoopFrontier=32 still took 118 s). Turn it GREEN with
## the per-walk total Z3 rlimit budget, then register it and add the cap.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc psplitU(s: string) =
  var n = 0
  for l in s.splitLines: inc n
  if n == 2: symexTarget("hit")

suite "RFC-0016 K7: splitLines over an unbounded string terminates":
  test "plain string parameter ends in a typed cap":
    let r = symexFind(psplitU, tLabel("hit"))
    check r.status != sxUnsat
    check not r.trusted()
