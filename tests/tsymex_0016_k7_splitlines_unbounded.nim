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

## The limit is sized from measured rates, not chosen to fit one machine. The
## walk spends Z3 units at about 220k/s locally (podman, 2026-11-09, run
## time only: 2M units 13.0 s, 5M 22.0 s, 20M 89.4 s). The 20M limit this
## test first carried stayed inside the Linux CI leg (whole test 304 s with
## compile, `.times`) but was killed at the 240 s per-test wall clock on the
## mingw leg (run 42619836849, shard 16: rc=124, wall=240.4 s), so that leg's
## rate is under 20M/240 s = 83k units/s. 4M units is 18 s locally and 48 s at
## that 83k/s bound, so the walk still ends typed with the wall clock 5x
## clear, and holds down to a 17k units/s leg. Any limit the walk reaches
## proves the property (the walk would otherwise not end); this one is only
## small enough to be reached on the slowest leg inside the time.
const bounded = block:
  var s = pinSettingsConst
  s.budget.walkRLimit = 4_000_000
  s

suite "RFC-0016 K7: splitLines over an unbounded string terminates":
  test "plain string parameter ends in a typed cap":
    let r = symexFind(psplitU, tLabel("hit"), bounded)
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(psplitU, "ckWalkWork", tLabel("hit"), bounded)
