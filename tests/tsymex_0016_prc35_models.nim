## RFC-0016 PRC-35 -- precision models for stdlib operations the walker
## declined: system's `toInt`/`toBiggestInt`, `$` of a float (the faithful
## sub-domain of Dragonbox's shortest round trip), the remaining `repr`
## shapes (integer, float, char, string), `$` of an enum value no member has,
## and `$bool` (exact before PRC-35, pinned here). Every verdict is pinned
## against the native run. `$float`'s domain is NaN, the infinities, the
## zeros and integral values up to 2^53 (2^24 for float32); a dyadic was
## measured out of the 10 s a check budget (`parseFloatToStr`) and declines.
## `repr` of a string is exact when no byte of it is escaped, and declines
## otherwise. `=dup` through a user hook: an explicit call and a copy are
## exact, a sink position on its source's provable last read moves, one its
## source is surely read again after runs the hook (PRC-44), and any other
## sink position declines.
import std/[unittest, strutils, math]
import nelli
import nelli/symex
import ./s8cu_helpers

type HE = enum ha = 1, hb = (5, "bee")

proc sToInt(x: float) =
  if toInt(x) == 3: symexTarget("hit")
proc sToIntTie(x: float) =
  # 0.49999999999999994 + 0.5 rounds to 1.0, so toInt is 1, not 0.
  if x < 0.5 and x > 0.4 and toInt(x) == 1: symexTarget("hit")
proc sToIntNeg(x: float) =
  # -2.5 - 0.5 is -3.0 exactly: toInt(-2.5) == -3 (half away from zero)
  if toInt(x) == -3 and x > -2.6: symexTarget("hit")
proc sToBig(x: float) =
  if toBiggestInt(x) == -7: symexTarget("hit")

proc sFloatInt(x: float) =
  if $x == "-42.0": symexTarget("hit")
proc sFloatBig(x: float) =
  if $x == "9007199254740992.0": symexTarget("hit")
proc sFloatNoExp(x: float) =
  # an integral float below 2^53 never prints in scientific notation
  if x > 1.0 and x < 1e15 and x == trunc(x) and "e" in $x:
    symexTarget("hit")
proc sFloatSpecial(x: float) =
  if $x == "-0.0": symexTarget("hit")
proc sFloatInf(x: float) =
  if $x == "-inf": symexTarget("hit")
proc sFloatDotZero(x: float) =
  # an integral float always prints its `.0`
  if x > -1e6 and x < 1e6 and x == trunc(x) and not ($x).endsWith(".0"):
    symexTarget("hit")
proc sFloat32(x: float32) =
  if $x == "-3.0": symexTarget("hit")
proc sFloatOut(x: float) =
  if x == 0.1 and $x == "0.1": symexTarget("hit")
proc sFloatHalf(x: float) =
  if x == 2.5 and $x == "2.5": symexTarget("hit")

proc sReprInt(k: int) =
  if repr(k) == "-42": symexTarget("hit")
proc sReprU8(k: uint8) =
  if repr(k) == "200": symexTarget("hit")
proc sReprFloat(x: float) =
  if repr(x) == "-42.0": symexTarget("hit")
proc sReprChar(c: char) =
  if repr(c) == "'\\10'": symexTarget("hit")
proc sReprCharBs(c: char) =
  if repr(c) == "'\\\\'": symexTarget("hit")
proc sReprCharA(c: char) =
  if repr(c) == "'a'": symexTarget("hit")
# A string with no byte `repr` escapes is the string between quotes; one
# holding such a byte declines, so each string is built from chars confined
# to the modelled bytes.
proc sReprStr(a, b: char) =
  if a in {'x', 'a'} and b in {' ', 'b'} and
     repr($a & $b) == "\"x \"": symexTarget("hit")
proc sReprStrNever(a: char) =
  if a in {'x', 'a', '~'} and repr($a) == "x": symexTarget("hit")
proc sReprStrEsc(a: char) =
  if a in {'"', 'a'} and repr($a) == "\"\\\"\"": symexTarget("hit")

proc sHole(k: int) =
  if k >= 1 and k <= 5:
    let e = HE(k)
    if $e == "": symexTarget("hit")
proc sMember(k: int) =
  if k >= 1 and k <= 5:
    let e = HE(k)
    if $e == "bee": symexTarget("hit")

proc sBool(b: bool) =
  if $b == "false": symexTarget("hit")
proc sBoolCall(b: bool) =
  if `$`(b) == "true" and not b: symexTarget("hit")

# `=dup` through a user hook. Natively (Nim 2.2.10, c and cpp) a `let`/`var`
# copy runs the generated `=copy`, an explicit call runs the hook, and a sink
# position runs it when a later read of its source is reachable from it (on
# some path: a read in a branch not taken still makes it run), and moves on
# the last read. The walk models the first two, a provable last read, and
# (PRC-44) a sink position a read of its source is surely reachable from;
# any other sink position declines.
type DupObj = object
  v: int
type DupBox = object
  o: DupObj
proc `=dup`(x: DupObj): DupObj = DupObj(v: x.v + 1)
proc dupTake(x: sink DupObj): int = x.v
proc dupPeek(t: (DupObj, int)): int = t[0].v

proc dExplicit(k: int) =
  let a = DupObj(v: k)
  let b = `=dup`(a)
  if b.v == 2: symexTarget("hit")
proc dLetCopy(k: int) =
  let a = DupObj(v: k)
  var b = a
  if b.v == 1: symexTarget("hit")
proc dLetCopyNever(k: int) =
  let a = DupObj(v: k)
  let b = a
  if b.v != a.v: symexTarget("hit")
proc dSinkMove(k: int) =
  let a = DupObj(v: k)
  if dupTake(a) == 1: symexTarget("hit")
proc dSinkMoveNever(k: int) =
  let a = DupObj(v: k)
  if dupTake(a) != k: symexTarget("hit")
proc dCtorMove(k: int) =
  let a = DupObj(v: k)
  let w = DupBox(o: a)
  if w.o.v == 1: symexTarget("hit")
proc dSinkReadAfter(k: int) =
  let a = DupObj(v: k)
  if dupTake(a) * 1000 + a.v == 2001: symexTarget("hit")
proc dAddReadAfter(k: int) =
  var s: seq[DupObj]
  let a = DupObj(v: k)
  s.add a
  if s[0].v * 1000 + a.v == 2001: symexTarget("hit")
proc dTupleReadAfter(k: int) =
  let a = DupObj(v: k)
  let t = (a, 0)
  if t[0].v * 1000 + a.v == 2001: symexTarget("hit")
proc dLoop(k: int) =
  let a = DupObj(v: k)
  var r = 0
  for i in 0 ..< 1:
    r = dupTake(a)
  if r == 2: symexTarget("hit")
proc dSinkReadAfterNever(k: int) =
  if k > 1000: return   # the hook's `+ 1` raises at high(int)
  let a = DupObj(v: k)
  if dupTake(a) == a.v: symexTarget("hit")
proc dCondReadAfter(k: int) =
  # The later read is in a branch not taken at k = 1: the hook runs anyway.
  let a = DupObj(v: k)
  let r = dupTake(a)
  var s = 0
  if k > 100: s = a.v
  if r == 2 and s == 0: symexTarget("hit")
proc dCondReadAfterNever(k: int) =
  if k > 1000: return   # the hook's `+ 1` raises at high(int)
  let a = DupObj(v: k)
  let r = dupTake(a)
  var s = 0
  if k > 100: s = a.v
  if r == k: symexTarget("hit")
proc dSiteInBranch(k: int) =
  let a = DupObj(v: k)
  var r = 0
  if k > 0: r = dupTake(a)
  if r * 1000 + a.v == 2001: symexTarget("hit")
proc dWhileOnce(k: int) =
  let a = DupObj(v: k)
  var r = 0
  var i = 0
  while i < 1:
    r = dupTake(a)
    inc i
  if r == 2: symexTarget("hit")
proc dArrayReadAfter(k: int) =
  let a = DupObj(v: k)
  let arr = [a]
  if arr[0].v * 1000 + a.v == 2001: symexTarget("hit")
proc dEarlyReturn(k: int) =
  # No path from the sink to the later read: natively the move (PRC-45).
  let a = DupObj(v: k)
  if k > 0:
    if dupTake(a) == 1: symexTarget("hit")
    return
  if a.v == 7: symexTarget("other")
iterator dupOnce(): int = yield 0
proc dOnceLoop(k: int) =
  # An iterator that yields once is no loop once inlined: natively the move.
  let a = DupObj(v: k)
  var r = 0
  for i in dupOnce():
    r = dupTake(a)
  if r == 1: symexTarget("hit")
proc dOnceLoopNever(k: int) =
  # PRC-48: the hook would have run there (`r` would not be `k`).
  let a = DupObj(v: k)
  var r = 0
  for i in dupOnce():
    r = dupTake(a)
  if r != k: symexTarget("hit")
proc dTupleTemp(k: int) =
  # A constructor passed to a non-`sink` formal is no sink position.
  let a = DupObj(v: k)
  if dupPeek((a, 0)) * 1000 + a.v == 1001: symexTarget("hit")

const fdom = sampled([0.0, -0.0, 0.1, 0.5, 2.5, 2.9, -2.9, -3.4, -7.0, 3.0,
                      0.49999999999999994, -42.0, 1e15, 0.0001220703125,
                      0.375, 1.0 / 0.0, -1.0 / 0.0, 9007199254740992.0])
const cdom = sampled(['a', '\\', '\n', '\0', '\'', '\255', 'z'])
const sdom = sampled(['x', 'a', ' ', 'b', '~', '"'])
const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])

let sCell = cellKey(axStdlibBody, "system.$/float")
let rCell = cellKey(axMagic, "Repr")

suite "PRC-35":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 416

  test "version floor (PRC-44)":
    check parseInt(symexWalkerVersion) >= 418

  test "toInt rounds half away from zero, through the RNE add":
    check pinExact(sToInt, cellKey(axStdlibBody, "math.toInt"),
                   domain = fdom).status == sxSat
    check pinExact(sToIntTie, cellKey(axStdlibBody, "math.toInt"),
                   domain = fdom).status == sxSat
    check pinExact(sToIntNeg, cellKey(axStdlibBody, "math.toInt"),
                   domain = fdom).status == sxSat
    check pinExact(sToBig, cellKey(axStdlibBody, "math.toBiggestInt"),
                   domain = fdom).status == sxSat

  test "$float: integral and special values are exact":
    check pinExact(sFloatInt, sCell, domain = fdom).status == sxSat
    check pinExact(sFloatBig, sCell, domain = fdom).status == sxSat
    check pinExact(sFloatSpecial, sCell, domain = fdom).status == sxSat
    check pinExact(sFloatInf, sCell, domain = fdom).status == sxSat
    check pinExact(sFloat32, sCell,
                   domain = sampled([-3.0'f32, 0.5, 1.0])).status == sxSat

  test "$float: no scientific notation and always `.0` in the domain":
    check pinExact(sFloatNoExp, sCell, domain = fdom).status == sxUnsat
    check pinExact(sFloatDotZero, sCell, domain = fdom).status == sxUnsat

  test "$float outside the domain declines (0.1, and a dyadic)":
    for r in [symexFind(sFloatOut, tLabel("hit")),
              symexFind(sFloatHalf, tLabel("hit"))]:
      checkpoint show(r.errors)
      check r.status == sxUnknown
      check r.errors.named(feUnsupportedOp)

  test "repr of an integer and a float is its $":
    check pinExact(sReprInt, rCell, domain = idom).status == sxSat
    check pinExact(sReprU8, rCell,
                   domain = sampled([0'u8, 200, 255])).status == sxSat
    check pinExact(sReprFloat, rCell, domain = fdom).status == sxSat

  test "repr of a char escapes as repr_v2 does":
    check pinExact(sReprChar, rCell, domain = cdom).status == sxSat
    check pinExact(sReprCharBs, rCell, domain = cdom).status == sxSat
    check pinExact(sReprCharA, rCell, domain = cdom).status == sxSat

  test "repr of a string with no escaped byte is it between quotes":
    check pinExact(sReprStr, rCell, domain = sdom).status == sxSat
    check pinExact(sReprStrNever, rCell, domain = sdom).status == sxUnsat

  test "repr of a string holding an escaped byte declines":
    check native(sReprStrEsc('"')) == "hit"
    pinDecline(sReprStrEsc, rCell, feUnsupportedOp,
               needle = "holding a byte it escapes")

  test "$ of an enum value no member has is empty":
    check pinExact(sHole, cellKey(axMagic, "EnumToStr"),
                   domain = idom).status == sxSat
    check pinExact(sMember, cellKey(axMagic, "EnumToStr"),
                   domain = idom).status == sxSat

  test "=dup: an explicit call runs the user hook; a copy does not":
    let dCell = cellKey(axMagic, "Dup")
    check pinExact(dExplicit, dCell, domain = idom).status == sxSat
    check pinExact(dLetCopy, dCell, domain = idom).status == sxSat
    check pinExact(dLetCopyNever, dCell, domain = idom).status == sxUnsat

  test "=dup: a sink position on the source's last read moves":
    let dCell = cellKey(axMagic, "Dup")
    check pinExact(dSinkMove, dCell, domain = idom).status == sxSat
    check pinExact(dSinkMoveNever, dCell, domain = idom).status == sxUnsat
    check pinExact(dCtorMove, dCell, domain = idom).status == sxSat

  test "=dup: a sink position its source is surely read after runs the hook":
    let dCell = cellKey(axMagic, "Dup")
    check pinExact(dSinkReadAfter, dCell, domain = idom).status == sxSat
    check pinExact(dSinkReadAfterNever, dCell, domain = idom).status == sxUnsat
    check pinExact(dAddReadAfter, dCell, domain = idom).status == sxSat
    check pinExact(dTupleReadAfter, dCell, domain = idom).status == sxSat
    check pinExact(dArrayReadAfter, dCell, domain = idom).status == sxSat
    check pinExact(dLoop, dCell, domain = idom).status == sxSat
    check pinExact(dWhileOnce, dCell, domain = idom).status == sxSat
    check pinExact(dSiteInBranch, dCell, domain = idom).status == sxSat

  test "=dup: a later read in a branch not taken still runs the hook":
    let dCell = cellKey(axMagic, "Dup")
    check pinExact(dCondReadAfter, dCell, domain = idom).status == sxSat
    check pinExact(dCondReadAfterNever, dCell, domain = idom).status == sxUnsat

  test "=dup: a sink position with no sure path to a later read declines":
    let dCell = cellKey(axMagic, "Dup")
    check native(dEarlyReturn(1)) == "hit"
    check native(dOnceLoop(1)) == "hit"
    check native(dTupleTemp(1)) == "hit"
    # PRC-45: no read is reachable from the site on a path the scan follows
    # to its end: the move, exact.
    check pinExact(dEarlyReturn, dCell, domain = idom).status == sxSat
    # PRC-48: the iterator is inlined, its one copy of the body no loop.
    check pinExact(dOnceLoop, dCell, domain = idom).status == sxSat
    check pinExact(dOnceLoopNever, dCell, domain = idom).status == sxUnsat
    pinDecline(dTupleTemp, dCell, feGlobalRouteUnproved,
               needle = "`a` is read after it")

  test "$bool is exact in both spellings":
    check pinExact(sBool, cellKey(axMagic, "BoolToStr"),
                   domain = sampled([false, true])).status == sxSat
    check pinExact(sBoolCall, cellKey(axMagic, "BoolToStr"),
                   domain = sampled([false, true])).status == sxUnsat
