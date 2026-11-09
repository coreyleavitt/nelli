## RFC-0016 K7 / CRH-01: `for l in s.splitLines` over an UNBOUNDED symbolic
## string must end in a typed cap, not run unbounded. Without a total bound the
## nested loops multiply a k-unroll's active set (33, then 594 paths, ...), each
## step a fast solver check, and neither a per-query bound nor a live-path cap
## bounds the sum (maxLoopFrontier=32 still took 118 s). `walkRLimit` bounds the
## sum of Z3 units every check of the walk spends; at the limit the walk halts
## as `ckWalkWork`. The limit is explicit here: at the default
## (1_000_000_000 units) this walk was still running when dt-bounded killed it
## at 900 s (rc=137, 2026-11-09), so the default does not end it in test time
## and this pin does not move with `walkRLimit`'s default.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc psplitU(s: string) =
  var n = 0
  for l in s.splitLines: inc n
  if n == 2: symexTarget("hit")

const bounded = block:
  var s = pinSettingsConst
  s.budget.walkRLimit = 20_000_000
  s

suite "RFC-0016 K7: splitLines over an unbounded string terminates":
  test "plain string parameter ends in a typed cap":
    let r = symexFind(psplitU, tLabel("hit"), bounded)
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(psplitU, "ckWalkWork", tLabel("hit"), bounded)
