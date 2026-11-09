## RFC-0016 K7 (REPRODUCTION, see the handoff's k7hang line): two sequential
## binary searches over a 450-entry const table, the shape of
## `unicode.toLower`. The walk is bounded by `walkRLimit` but the units
## under-count its wall time: at 20M units it ran 190-260 s, of which Z3 spent
## about 4 s; the rest is walker-side work per query over a path condition
## carrying a 450-deep `store` chain per table. The limit here is 2M units
## (about 20 s). At the 1e9 default the same walk would take hours.
import std/unittest
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
