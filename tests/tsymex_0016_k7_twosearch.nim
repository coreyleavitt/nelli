## RFC-0016 K7 (REPRODUCTION, see the handoff's k7hang line): two sequential
## binary searches over a 450-entry const table, the shape of
## `unicode.toLower`. The walk is bounded by `walkRLimit` but the units
## under-count its wall time: at 20M units it ran 190-260 s, of which Z3 spent
## about 4 s; the rest is walker-side work per query over a path condition
## carrying a 450-deep `store` chain per table. The limit here is 2M units
## (about 20 s). At the 1e9 default the same walk would take hours.
import std/[unittest, monotimes, times, strutils]
import nelli/smt/canonicalize
import nelli
import nelli/symex
import ./s8cu_helpers

const tabA = block:
  var t: array[450, int32]
  for i in 0 ..< 150:
    t[3*i] = int32(10 * i)
    t[3*i + 1] = int32(10 * i + 4)
    t[3*i + 2] = int32(500 + (i mod 7))
  t
const tabB = block:
  var t: array[450, int32]
  for i in 0 ..< 225:
    t[2*i] = int32(7 * i + 3)
    t[2*i + 1] = int32(500 + (i mod 5))
  t

proc bsearch(c: int32, tab: openArray[int32], len, stride: int): int =
  var n = len
  var t = 0
  while n > 1:
    var m = n div 2
    var p = t + m*stride
    if c >= tab[p]:
      t = p
      n = n - m
    else:
      n = m
  if n != 0 and c >= tab[t]:
    return t
  return -1

proc lower2(a: int32) =
  var c = a
  var p = bsearch(c, tabA, len(tabA) div 3, 3)
  if p >= 0 and c >= tabA[p] and c <= tabA[p+1]:
    c = c + tabA[p+2] - 500
  else:
    p = bsearch(c, tabB, len(tabB) div 2, 2)
    if p >= 0 and c == tabB[p]:
      c = c + tabB[p+1] - 500
  if c == 1234: symexTarget("hit")

const bounded = block:
  var s = pinSettingsConst
  s.budget.walkRLimit = 2_000_000
  s

suite "RFC-0016 K7: two const-table binary searches terminate":
  test "ends in a typed cap, not a hang":
    let r = symexFind(lower2, tLabel("hit"), bounded)
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(lower2, "ckWalkWork", tLabel("hit"), bounded)

## K7 contract: `walkRLimit` bounds WALL time, not only Z3 time. The walker
## charges its own per-query work (query construction and the fact passes) to
## the same budget at `walkerTermUnits` (15) units per term visit, calibrated
## so a unit costs about as much wall time of either kind (the measurement
## and derivation are by that constant in runtime.nim: arithmetic walks run
## 3.9M units/s on the calibration host, this walk about the same once
## charged). So a walk of N units must end within
##   N / floorUnitsPerSec + startupSlack
## seconds. The floor is a quarter of the calibrated rate (1M of ~3.9M units/s)
## to allow a slower CI host; the slack covers process start and Z3 load.
## Before the charge this walk ran ~106k units/s (94 s for 10M units, measured
## on the calibration host) and missed the 30 s bound below.
const
  chargedN = 10_000_000'u
  floorUnitsPerSec = 1_000_000.0
  startupSlackSec = 20.0

const charged = block:
  var s = pinSettingsConst
  s.budget.walkRLimit = chargedN
  s

suite "RFC-0016 K7: walkRLimit bounds wall time on table-heavy walks":
  test "the walker-side charge changed the walk: walker 305 or later":
    check parseInt(symexWalkerVersion) >= 305

  test "10M units end in ckWalkWork within N / rate floor + slack":
    let t0 = getMonoTime()
    let r = symexFind(lower2, tLabel("hit"), charged)
    let secs = float((getMonoTime() - t0).inMilliseconds) / 1000.0
    check r.status == sxUnknown
    check not r.trusted()
    var capped = false
    for e in r.errors:
      if e.kind == beBudgetExhaustedPrune and "walk work cap" in e.msg:
        capped = true
    check capped
    let bound = float(chargedN) / floorUnitsPerSec + startupSlackSec
    checkpoint "walk took " & $secs & " s; bound " & $bound & " s"
    check secs <= bound
