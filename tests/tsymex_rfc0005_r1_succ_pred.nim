## RFC-0005 review R1-02 -- `succ` / `pred` / `inc` / `dec` past an ordinal's end.
##
## `succ(x[, n])` and `pred(x[, n])` on an enum or a `char` lowered to a plain
## `x + n` / `x - n` with no bound check, and `inc` / `dec` on an enum or a
## `char` variable to the same. Native Nim (probed, this toolchain) raises
## `OverflowDefect` -- not `RangeDefect` -- when the result leaves the
## operand's type:
##
##   * `succ` / `pred` check the BASE type's bounds: an enum's first and last
##     ordinal, `char`'s 0..255. A `range` operand is checked against its base
##     type, so `succ` of 3 in `range[0..3]` is 4 with no raise, and a
##     subrange of an enum is checked against the whole enum;
##   * `inc` / `dec` check the variable's OWN type, a `range` included:
##     `inc` of 3 in a `range[0..3]` variable raises `OverflowDefect`.
##
## The walk gave `sxUnsat` for an `OverflowDefect` target and a false `sxSat`
## on a label behind the wrapped value; `inc` on a ranged variable raised
## `RangeDefect` where native raises `OverflowDefect`.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

type
  C = enum ca, cb, cc
  C5 = enum d5 = 5, d6, d7
  Sub = range[cb .. cc]
  R = range[0 .. 3]
  R32 = range[0'i32 .. 3'i32]
  CR = range['a' .. 'c']

# A label behind a value only a wrap produces: native raises first.
proc succChar(x: char) =
  if succ(x) == '\0': symexTarget("hit")
proc predChar(x: char) =
  if pred(x) == '\xff': symexTarget("hit")
proc incChar(x: char) =
  var c = x
  inc c
  if c == '\0': symexTarget("hit")
proc succEnum5Wrap(x: C5) =
  if ord(succ(x)) == 8: symexTarget("hit")

# The raise itself.
proc succEnum(x: C) = discard succ(x)
proc predEnum(x: C) = discard pred(x)
proc succEnumStepRaise(x: C, n: int) =
  if n >= -3 and n <= 3: discard succ(x, n)
proc succSub(x: Sub) = discard succ(x)
proc succInt8(x: int8) = discard succ(x)
proc incEnumRaise(x: C) =
  var e = x
  inc e
proc decEnum(x: C) =
  var e = x
  dec e
proc incEnumStepRaise(x: C, n: int) =
  var e = x
  if n >= 0 and n <= 3: inc e, n
proc incRange(x: R) =
  var r = x
  inc r

# In range: the label is reached and nothing raises.
proc succEnumStep(x: C, n: int) =
  if n >= -2 and n <= 2 and ord(x) + n >= 0 and ord(x) + n <= 2:
    if succ(x, n) == ca: symexTarget("hit")
proc succEnum5(x: C5) =
  if x != d7 and succ(x) == d7: symexTarget("hit")
proc succRange(x: R) =
  if succ(x) == 4: symexTarget("hit")
proc incEnum(x: C) =
  var e = x
  if x != cc:
    inc e
    if e == cc: symexTarget("hit")
proc incEnumStep(x: C, n: int) =
  var e = x
  if n >= 0 and n <= 2 and ord(x) + n <= 2:
    inc e, n
    if e == cc: symexTarget("hit")

# `+=` / `-=` are the `Inc` / `Dec` magics.
proc plusEqRange(x: R) =
  var r = x
  r += 1
proc minusEqNatural(x: Natural) =
  var r = x
  r -= 1
proc incRange32(x: R32) =
  var r = x
  inc r
proc incCharRange(x: CR) =
  var c = x
  inc c
proc succNatural(x: Natural) =
  if x < 10 and succ(x) == 5: symexTarget("hit")
proc incNatural(x: Natural) =
  var r = x
  if r < 10:
    inc r
    if r == 5: symexTarget("hit")


# A `var` parameter wraps the value's type in `ntyVar`: the step is still
# checked against the underlying type's bounds.
proc stepIntV(a: var int) = inc a
proc stepEnumV(a: var C) = inc a
proc stepEnumDecV(a: var C) = dec a
proc stepCharV(a: var char) = inc a
proc stepRangeV(a: var R) = inc a
proc stepRangePlusV(a: var R) = a += 1
proc succVarEnum(a: var C): C = succ(a)
proc succVarRange(a: var R): int = succ(a)
proc viaIntV(x: int) =
  var v = x
  stepIntV(v)
  if v == 5: symexTarget("hit")
proc viaEnumV(x: C) =
  var v = x
  stepEnumV(v)
proc viaEnumDecV(x: C) =
  var v = x
  stepEnumDecV(v)
proc viaEnumOkV(x: C) =
  var v = x
  if x != cc:
    stepEnumV(v)
    if v == cc: symexTarget("hit")
proc viaCharV(x: char) =
  var v = x
  stepCharV(v)
  if v == '\0': symexTarget("hit")
proc viaRangeV(x: R) =
  var v = x
  stepRangeV(v)
proc viaRangePlusV(x: R) =
  var v = x
  stepRangePlusV(v)
proc viaSuccVarEnum(x: C) =
  var v = x
  discard succVarEnum(v)
proc viaSuccVarRange(x: R) =
  var v = x
  if succVarRange(v) == 4: symexTarget("hit")

# `distinct`: native checks the step against the underlying type.
type
  DI = distinct int
  DI8 = distinct int8
  DC = distinct C
proc incDistinctInt(x: int) =
  var d = DI(x)
  inc d
  if int(d) == 5: symexTarget("hit")
proc incDistinctInt8(x: int8) =
  var d = DI8(x)
  inc d
proc incDistinctEnum(x: C) =
  var d = DC(x)
  inc d

template overflows(fn: untyped; target: SymexTarget) =
  let r = symexFind(fn, target)
  checkpoint show(r.errors)
  check r.status == sxRaised
  if r.status == sxRaised:
    check r.raisedTypeId == "OverflowDefect"

template overflows(fn: untyped) = overflows(fn, tRaisedExn("OverflowDefect"))

suite "R1-02: succ / pred / inc / dec past an ordinal's end":

  test "succ / pred on an enum raise OverflowDefect at the ends":
    check native(succEnum(cc)) == "OverflowDefect"
    overflows(succEnum)                                 # was sxUnsat
    check native(predEnum(ca)) == "OverflowDefect"
    overflows(predEnum)

  test "succ / pred on a char do not wrap":
    check native(succChar('\xff')) == "OverflowDefect"
    overflows(succChar, tLabel("hit"))                  # was a false sxSat
    check native(predChar('\0')) == "OverflowDefect"
    overflows(predChar, tLabel("hit"))

  test "a step, and an enum whose first ordinal is not 0":
    check native(succEnumStep(ca, 0)) == "hit"
    check native(succEnumStep(cb, -1)) == "hit"
    decides(succEnumStep, sxSat)
    check native(succEnumStepRaise(ca, -1)) == "OverflowDefect"
    check native(succEnumStepRaise(cb, 2)) == "OverflowDefect"
    overflows(succEnumStepRaise)
    check native(succEnum5(d6)) == "hit"
    decides(succEnum5, sxSat)
    check native(succEnum5Wrap(d7)) == "OverflowDefect"
    overflows(succEnum5Wrap, tLabel("hit"))

  test "a subrange is checked against its base type":
    check native(succSub(cc)) == "OverflowDefect"
    overflows(succSub)
    check native(succRange(3)) == "hit"
    decides(succRange, sxSat)
    let r = symexFind(succRange, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "an int operand keeps its own overflow check":
    check native(succInt8(127)) == "OverflowDefect"
    overflows(succInt8)

  test "inc / dec on an enum or a char variable":
    check native(incEnum(cb)) == "hit"
    decides(incEnum, sxSat)
    check native(incEnumRaise(cc)) == "OverflowDefect"
    overflows(incEnumRaise)
    check native(decEnum(ca)) == "OverflowDefect"
    overflows(decEnum)
    check native(incChar('\xff')) == "OverflowDefect"
    overflows(incChar, tLabel("hit"))
    check native(incEnumStep(ca, 2)) == "hit"
    decides(incEnumStep, sxSat)
    check native(incEnumStepRaise(cb, 2)) == "OverflowDefect"
    overflows(incEnumStepRaise)

  test "inc on a range variable raises OverflowDefect, not RangeDefect":
    check native(incRange(3)) == "OverflowDefect"
    overflows(incRange)

  test "+= / -= on a range variable raise OverflowDefect":
    check native(plusEqRange(3)) == "OverflowDefect"
    overflows(plusEqRange)
    check native(minusEqNatural(0)) == "OverflowDefect"
    overflows(minusEqNatural)

  test "other ranges":
    check native(incRange32(3)) == "OverflowDefect"
    overflows(incRange32)
    check native(incCharRange('c')) == "OverflowDefect"
    overflows(incCharRange)
    check native(succNatural(4)) == "hit"
    decides(succNatural, sxSat)
    check native(incNatural(4)) == "hit"
    decides(incNatural, sxSat)

  test "a var parameter is checked against its underlying type":
    check native(viaIntV(4)) == "hit"
    decides(viaIntV, sxSat)
    check native(viaEnumOkV(cb)) == "hit"
    decides(viaEnumOkV, sxSat)
    check native(viaEnumV(cc)) == "OverflowDefect"
    overflows(viaEnumV)
    check native(viaEnumDecV(ca)) == "OverflowDefect"
    overflows(viaEnumDecV)
    check native(viaCharV('\xff')) == "OverflowDefect"
    overflows(viaCharV, tLabel("hit"))
    check native(viaRangeV(3)) == "OverflowDefect"
    overflows(viaRangeV)
    check native(viaRangePlusV(3)) == "OverflowDefect"
    overflows(viaRangePlusV)

  test "succ / pred on a var parameter's value":
    check native(viaSuccVarEnum(cc)) == "OverflowDefect"
    overflows(viaSuccVarEnum)
    # succ of 3 in range[0..3] is 4, within the base type: no raise.
    check native(viaSuccVarRange(3)) == "hit"
    decides(viaSuccVarRange, sxSat)

  test "a distinct receiver is declined, never a wrong verdict":
    # Native checks the step against the underlying type; `inc` on a
    # distinct is not modelled (the receiver gate), so it must not be sxUnsat.
    check native(incDistinctInt(4)) == "hit"
    declines(incDistinctInt, feUnsupportedOp)
    check native(incDistinctInt8(127)) == "OverflowDefect"
    declines(incDistinctInt8, feUnsupportedOp)
    check native(incDistinctEnum(cc)) == "OverflowDefect"
    declines(incDistinctEnum, feUnsupportedOp)
