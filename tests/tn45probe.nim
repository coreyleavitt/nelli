## N45 CONTROLLED PROBE — identical at every revision under test.
##
## Holds the SUT, the helpers and the unroll budget FIXED, so the only thing
## varying across revisions is the walker. The committed
## tsymex_r6_b5_chained.nim cannot serve this purpose: its B5-4 gained an
## explicit `maxLoopUnwind = 2` in 494ae8f, which is NOT an ancestor of v105
## (a3dba31) -- so at v105 the committed test ran the DEFAULT budget (k=5) and
## at v123 it runs k=2. Comparing those two measures a budget change, not a
## regression, and that is very likely what the recorded "~40s -> ~135s, k=2
## floor" figure actually did.
##
## Build: nim c -r --threads:on -d:symexQueryStats <this file>
## Read:  the single N45STATS line (deterministic; rlimit is Z3's own logical
##        step count, not wall time).

import std/unittest
import nelli/symex

type ScanError = object of CatchableError

proc readCStringHelper(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc scanBoundAlias(s: string, offset: int): int =
  let n = s.len
  var i = offset
  while i < n:
    if s[i] == ':':
      return i
    i.inc
  raise newException(ScanError, "unterminated")

proc sutChainSecondNonLenBoundImpossible(s: string) =
  let (_, p1) = readCStringHelper(s, 0)
  let p2 = scanBoundAlias(s, p1)
  if p2 > s.len:
    symexTarget("impossible")

const b5TripWireBudget = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxLoopUnwind = 2

suite "N45 controlled probe — B5-4 trip-wire at a FIXED k=2 budget":
  test "B5-4 at k=2":
    let r = symexFind(sutChainSecondNonLenBoundImpossible,
                      tLabel("impossible"), b5TripWireBudget)
    echo "STATUS=", r.status
    check r.status == sxUnknown
