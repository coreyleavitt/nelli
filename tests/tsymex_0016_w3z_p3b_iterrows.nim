## RFC-0016 W3-z P3b: the stdlib iterators the corpus walks by their bodies.
## P3 keyed an iterator `<module>.<name>/iterator` and declined any without a
## row (`feUnadmitted`), so system `countup`/`countdown`/`..` -- inlined and
## walked exactly before -- regressed to a decline. Each iterator here has a
## row (the corpus ledger) and an exact, differentially pinned verdict.
import std/[unittest, strutils, tables, unicode]
import nelli
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/admission
import nelli/smt/stdlib_rows
import ./s8cu_helpers

proc sCountup(a: int) =
  var n = 0
  for i in countup(1, 4): n += i
  if n == 10 and a == 1: symexTarget("hit")

proc sCountdown(a: int) =
  var n = 0
  for i in countdown(4, 1): n = n * 2 + i
  if n == 26 and a == 1: symexTarget("hit")

proc sCountupStep(a: int) =
  var n = 0
  for i in countup(0, 9, 3): n += i
  if n == 18 and a == 1: symexTarget("hit")

proc sDotDot(a: int) =
  var n = 0
  for i in 1 .. 4: n += i
  if n == 10 and a == 1: symexTarget("hit")

proc sDotDotLt(a: int) =
  var n = 0
  for i in 0 ..< 4: n += i
  if n == 6 and a == 1: symexTarget("hit")

proc sDotDotSym(a: int) =
  var n = 0
  for i in 0 .. (a and 3): n += 1
  if n == 3 and a == 2: symexTarget("hit")

proc sItems(a: int) =
  let xs = [1, 2, 3]
  var n = 0
  for x in items(xs): n += x
  if n == 6 and a == 1: symexTarget("hit")

proc sPairs(a: int) =
  let xs = @[5, 6]
  var n = 0
  for i, x in pairs(xs): n += i * x
  if n == 6 and a == 1: symexTarget("hit")

proc sMitems(a: int) =
  var xs = @[1, 2]
  for x in mitems(xs): x += 1
  if xs[0] + xs[1] == 5 and a == 1: symexTarget("hit")

proc sMpairs(a: int) =
  var xs = @[1, 2]
  for i, x in mpairs(xs): x += i
  if xs[0] + xs[1] == 4 and a == 1: symexTarget("hit")

proc sSplit(a: int) =
  var n = 0
  for w in "a,b,c".split(','): inc n
  if n == 3 and a == 1: symexTarget("hit")

proc sSplitWs(a: int) =
  var n = 0
  for w in strutils.splitWhitespace("a b  c"): inc n
  if n == 3 and a == 1: symexTarget("hit")

proc sSplitLines(a: int) =
  var n = 0
  for l in "x\ny".splitLines: inc n
  if n == 2 and a == 1: symexTarget("hit")

proc sRunes(a: int) =
  var n = 0
  for r in "ab".runes: inc n
  if n == 2 and a == 1: symexTarget("hit")

proc sTblKeys(a: int) =
  var t = initTable[int, int]()
  t[1] = 2
  var n = 0
  for k in t.keys: n += k
  if n == 1 and a == 1: symexTarget("hit")

proc sTblPairs(a: int) =
  var t = initTable[int, int]()
  t[1] = 2
  var n = 0
  for k, v in t.pairs: n += k + v
  if n == 3 and a == 1: symexTarget("hit")

proc sTblValues(a: int) =
  var t = initTable[int, int]()
  t[1] = 2
  var n = 0
  for v in t.values: n += v
  if n == 2 and a == 1: symexTarget("hit")

type Pt = object
  x, y: int

proc sFields(a: int) =
  let p = Pt(x: 1, y: 2)
  var n = 0
  for f in fields(p): n += f
  if n == 3 and a == 1: symexTarget("hit")

proc sFieldPairs(a: int) =
  let p = Pt(x: 1, y: 2)
  var n = 0
  for k, v in fieldPairs(p): n += v
  if n == 3 and a == 1: symexTarget("hit")

suite "W3-z P3b: the walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 315

suite "W3-z P3b: the system counting iterators decline for their real cause":
  # Walking the body of `countup`/`countdown` (generic over `T`, stepping with
  # `cast[T](res)`) was never exact; P3 turned the decline into `feUnadmitted`
  # "no row". The row names the cause. Both overloads of each (two and three
  # arguments) share the key.
  test "system.countup":
    check hasStdlibRow("system.countup/iterator")
    pinDecline(sCountup, cellKey(axStdlibBody, "system.countup/iterator"),
               feUnsupportedExprKind, excluding = {feUnadmitted})
    pinDecline(sCountupStep, cellKey(axStdlibBody, "system.countup/iterator"),
               feUnsupportedExprKind, excluding = {feUnadmitted})
  test "system.countdown":
    check hasStdlibRow("system.countdown/iterator")
    pinDecline(sCountdown, cellKey(axStdlibBody, "system.countdown/iterator"),
               feUnsupportedExprKind, excluding = {feUnadmitted})

suite "W3-z P3b: split iterators stay unadmitted":
  # `strutils.split`/`splitWhitespace` are not in the corpus's SUTs and their
  # body walk is not exact (slice bounds are bitvector-represented,
  # seUnsupportedStringOp), so they have no row: absent is a decline.
  test "no row, declines naming the cell":
    for (fn, cell) in [("split", "strutils.split/iterator"),
                       ("splitWhitespace", "strutils.splitWhitespace/iterator")]:
      check not hasStdlibRow(cell)
      check not admitStdlibBody(cell, ssBodyWalk).admitted
    let r1 = symexFind(sSplit, tLabel("hit"), pinSettingsConst)
    check not r1.trusted
    let r2 = symexFind(sSplitWs, tLabel("hit"), pinSettingsConst)
    check not r2.trusted

suite "W3-z P3b: iterators the walker claims itself never reach the axis":
  # `..`/`..<`, items/pairs/mitems/mpairs, runes, tables keys/values/pairs and
  # fields/fieldPairs are walked by their own arms: no stdlib key, so P3 did
  # not move them. Guarded here: exact, no `feUnadmitted`.
  template ownArm(fn: untyped) =
    test astToStr(fn):
      let r = symexFind(fn, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors)
      check r.status == sxSat and r.trusted
      for e in r.errors: check e.kind != feUnadmitted
  ownArm(sDotDot)
  ownArm(sDotDotLt)
  ownArm(sDotDotSym)
  ownArm(sItems)
  ownArm(sPairs)
  ownArm(sMitems)
  ownArm(sMpairs)
  ownArm(sRunes)
  ownArm(sTblKeys)
  ownArm(sTblPairs)
  ownArm(sTblValues)
  ownArm(sFields)
  ownArm(sFieldPairs)

