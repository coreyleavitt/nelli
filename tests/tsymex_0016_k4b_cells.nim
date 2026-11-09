## RFC-0016 K4b (section 8.4, K4): the 52 reachable `magic:` cells that
## K4a-dispatch re-owned, each pinned through `symexFind`.
##
## One SUT per cell, reaching the magic from a `symexTarget`. A row the
## walker models is pinned `pinExact` (its verdict reproduced natively); a
## row it declines (declined, unverified, partial shape) is pinned
## `pinDecline` with the kind it records. The bodied-magic rule itself is
## `tsymex_0016_k4b`.
import std/[unittest, setutils, parseutils]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/magic_rows
import ./s8cu_helpers

type
  K4Color = enum kcRed, kcGreen, kcBlue
  K4Obj = object
    x: int
  K4Base = ref object of RootObj
  K4Derived = ref object of K4Base

proc k4LenOA(x: openArray[int]): int = x.len
proc k4SeqOA(x: openArray[int]): seq[int] = @x
proc k4Id(x: int): int = x
proc k4Col(a: int): K4Color =
  if a > 3: kcBlue elif a > 0: kcGreen else: kcRed

proc sAddr(a: int) =
  var x = a
  let p = addr x
  if p[] == 5: symexTarget("hit")
proc sArrToSeq(a: int) =
  let arr = [a, 2]
  let s = @arr
  if s.len == 2 and s[0] == 5: symexTarget("hit")
proc sAsgn(a: int) =
  var x = 0
  `=copy`(x, a)
  if x == 5: symexTarget("hit")
proc sBoolToStr(a: int) =
  if $(a > 3) == "true" and a == 9: symexTarget("hit")
proc sIntToStr(a: int) =
  if $a == "42" and a == 42: symexTarget("hit")
proc sInt64ToStr(a: int) =
  if $int64(a) == "42" and a == 42: symexTarget("hit")
proc sCard(c: char) =
  if card({c, 'a'}) == 2: symexTarget("hit")
proc sDefault(a: int) =
  if default(int) == 0 and a == 3: symexTarget("hit")
proc sDotDot(a: int) =
  var n = 0
  if a >= 1 and a < 4:
    for i in 1 .. a: n += i
  if n == 3: symexTarget("hit")
proc sEcho(a: int) =
  echo "k4b"
  if a == 5: symexTarget("hit")
proc sEnumToStr(a: int) =
  if $k4Col(a) == "kcGreen" and a == 2: symexTarget("hit")
proc sEqEnum(a: int) =
  if k4Col(a) == kcBlue and a == 9: symexTarget("hit")
proc sLeEnum(a: int) =
  if k4Col(a) <= kcGreen and a == 2: symexTarget("hit")
proc sLtEnum(a: int) =
  if k4Col(a) < kcGreen and a == -2: symexTarget("hit")
proc sEqSet(c: char) =
  if {c} == {'a'} and c == 'a': symexTarget("hit")
proc sLeSet(c: char) =
  if {c} <= {'a', 'b'} and c == 'b': symexTarget("hit")
proc sLtSet(c: char) =
  if {c, 'a'} < {'a', 'b', 'x'} and c == 'x': symexTarget("hit")
proc sMinusSet(c: char) =
  if {'a', 'b'} - {c} == {'a'} and c == 'b': symexTarget("hit")
proc sMulSet(c: char) =
  if {'a', 'b'} * {c} == {'b'}: symexTarget("hit")
proc sPlusSet(c: char) =
  if {'a'} + {c} == {'a', 'x'}: symexTarget("hit")
proc sEqRef(a: int) =
  var r: ref int
  new(r)
  var q = r
  if a > 3: new(q)
  if q == r and a == 2: symexTarget("hit")
proc sExit(a: int) =
  if a > 3: quit(1)
  if a == 1: symexTarget("hit")
proc sLenOA(a: int) =
  let arr = [a, 2]
  if k4LenOA(arr) == 2 and a == 4: symexTarget("hit")
proc sLow(a: int) =
  let s = @[a, 2]
  if s.low == 0 and a == 4: symexTarget("hit")
proc sNewSeqOfCap(a: int) =
  if a >= 0 and a < 8:
    let s = newSeqOfCap[int](a)
    if s.len == 0 and a == 3: symexTarget("hit")
proc sOf(a: int) =
  var b: K4Base
  if a > 3: b = K4Derived() else: b = K4Base()
  if b of K4Derived and a == 9: symexTarget("hit")
proc sOpenArrayToSeq(a: int) =
  let arr = [a, 2]
  let s = k4SeqOA(arr)
  if s.len == 2 and s[0] == 5: symexTarget("hit")
proc sStrToStr(s: string) =
  if $s == "ab": symexTarget("hit")
proc sNeg64(a: int64) =
  if -a == 5'i64: symexTarget("hit")
proc sZeroDefault(a: int) =
  if zeroDefault(int) == 0 and a == 3: symexTarget("hit")
proc sRepr(a: int) =
  if repr(a) == "5": symexTarget("hit")
proc sDup(a: int) =
  var x = a
  let y = `=dup`(x)
  if y == 5: symexTarget("hit")
proc sSlice(a: int) =
  let s = @[1, 2, 3]
  if a >= 0 and a < 3 and k4LenOA(toOpenArray(s, 0, a)) == 2:
    symexTarget("hit")
proc sSetLenUninit(a: int) =
  var s = @[1, 2, 3]
  if a >= 0 and a < 3:
    s.setLenUninit(a)
    if s.len == 1: symexTarget("hit")
proc sEqProc(a: int) =
  let f = proc (x: int): int = x
  let g = f
  if f == g and a == 2: symexTarget("hit")
proc sCStrToStr(a: int) =
  let c: cstring = if a > 3: "abc" else: "x"
  if $c == "abc": symexTarget("hit")
proc sEqCString(a: int) =
  let c: cstring = if a > 3: "abc" else: "x"
  if c == "abc": symexTarget("hit")
proc sGCref(a: int) =
  var r: ref int
  new(r)
  GC_ref(r)
  if a == 5: symexTarget("hit")
proc sGCunref(a: int) =
  var r: ref int
  new(r)
  GC_ref(r)
  GC_unref(r)
  if a == 5: symexTarget("hit")
proc sGetTypeInfo(a: int) =
  let p = getTypeInfo(a)
  if not p.isNil and a == 5: symexTarget("hit")
proc sTrace(a: int) =
  var s = K4Obj(x: a)
  `=trace`(s, nil)
  if a == 5: symexTarget("hit")
proc sDestroy(a: int) =
  var s = K4Obj(x: a)
  `=destroy`(s)
  if a == 5: symexTarget("hit")
proc sParseBigFloat(a: int) =
  var f = 0.0
  let n = parseBiggestFloat("1.5", f)
  if n == 3 and a == 5: symexTarget("hit")
proc sProcCall(k: int) =
  let r = procCall(k4Id(k))
  if r == 3: symexTarget("hit")
proc sXorSet(c: char) =
  if symmetricDifference({c}, {'a'}) == {'a', 'b'}: symexTarget("hit")
proc sFields(a: int) =
  var t = (a, 2)
  var n = 0
  for v in fields(t): n += v
  if n == 7: symexTarget("hit")
proc sFieldPairs(a: int) =
  var t = (x: a, y: 2)
  var n = 0
  for k, v in fieldPairs(t): n += v
  if n == 7: symexTarget("hit")
proc sFinished(a: int) =
  var it = iterator (): int {.closure.} = yield 1
  discard it()
  if finished(it) and a == 5: symexTarget("hit")
proc sLePtr(a: int) =
  var x = a
  let p = addr x
  let q = addr x
  if p <= q and a == 5: symexTarget("hit")
proc sLtPtr(a: int) =
  var x = a
  let p = addr x
  let q = addr x
  if p < q and a == 5: symexTarget("hit")

const
  k4ChDom = sampled(['a', 'b', 'x', 'y'])
  k4SDom = sampled(["", "a", "ab", "abc"])
  k4I64Dom = sampled([-5'i64, 0, 5, 7])
  k4Ints = sampled([-3, -2, -1, 0, 1, 2, 3, 4, 5, 7, 9])

var exactPinned, declinePinned: seq[string]  ## filled as the tests run

template exactCell(sut: untyped; cell: static string; dom: untyped = k4Ints) =
  test cell:
    exactPinned.add cell
    let r = pinExact(sut, cellKey(axMagic, cell), domain = dom)
    check r.status in {sxSat, sxUnsat}
template declineCell(sut: untyped; cell: static string;
                     kind: SymexErrorKind) =
  test cell:
    declinePinned.add cell
    pinDecline(sut, cellKey(axMagic, cell), kind)

suite "K4b: the reachable magic cells, through symexFind":
  exactCell(sAddr, "Addr")
  exactCell(sArrToSeq, "ArrToSeq")
  exactCell(sAsgn, "Asgn")
  exactCell(sBoolToStr, "BoolToStr")
  exactCell(sCard, "Card", k4ChDom)
  exactCell(sDefault, "Default")
  exactCell(sDotDot, "DotDot")
  exactCell(sEcho, "Echo")
  exactCell(sEnumToStr, "EnumToStr")
  exactCell(sIntToStr, "IntToStr")
  exactCell(sInt64ToStr, "Int64ToStr")
  exactCell(sEqEnum, "EqEnum")
  exactCell(sLeEnum, "LeEnum")
  exactCell(sLtEnum, "LtEnum")
  exactCell(sEqSet, "EqSet", k4ChDom)
  exactCell(sLeSet, "LeSet", k4ChDom)
  exactCell(sLtSet, "LtSet", k4ChDom)
  exactCell(sMinusSet, "MinusSet", k4ChDom)
  exactCell(sMulSet, "MulSet", k4ChDom)
  exactCell(sPlusSet, "PlusSet", k4ChDom)
  exactCell(sEqRef, "EqRef")
  exactCell(sExit, "Exit")
  exactCell(sLenOA, "LengthOpenArray")
  exactCell(sLow, "Low")
  exactCell(sNewSeqOfCap, "NewSeqOfCap")
  exactCell(sOf, "Of")
  exactCell(sOpenArrayToSeq, "OpenArrayToSeq")
  exactCell(sStrToStr, "StrToStr", k4SDom)
  exactCell(sNeg64, "UnaryMinusI64", k4I64Dom)
  exactCell(sZeroDefault, "ZeroDefault")
  declineCell(sRepr, "Repr", feUnsupportedOp)
  exactCell(sDup, "Dup")
  exactCell(sSlice, "Slice")
  exactCell(sSetLenUninit, "SetLengthSeqUninit")
  exactCell(sEqProc, "EqProc")
  declineCell(sCStrToStr, "CStrToStr", feUnsupportedOp)
  exactCell(sEqCString, "EqCString")
  declineCell(sGCref, "GCref", feUnsupportedExprKind)
  declineCell(sGCunref, "GCunref", feUnsupportedOp)
  declineCell(sGetTypeInfo, "GetTypeInfo", feUnsupportedOp)
  declineCell(sTrace, "Trace", feUnsupportedOp)
  declineCell(sDestroy, "Destroy", feUnsupportedOp)
  declineCell(sParseBigFloat, "ParseBiggestFloat", feUnsupportedOp)
  declineCell(sProcCall, "ProcCall", feUnsupportedOp)
  declineCell(sXorSet, "XorSet", feUnsupportedOp)
  exactCell(sFields, "Fields")
  exactCell(sFieldPairs, "FieldPairs")
  declineCell(sFinished, "Finished", feUnsupportedOp)
  declineCell(sLePtr, "LePtr", feUnsupportedOp)
  declineCell(sLtPtr, "LtPtr", feUnsupportedOp)

suite "K4b: the row states agree with the pins (runs after the cells)":
  test "a row pinned exact is admitted and is modelled, folded or bodied":
    check exactPinned.len > 0
    for cell in exactPinned:
      let a = admitMagic(cell, msArm)
      check a.admitted
      if a.admitted:
        check a.payload in {mmModelled, mmFolded, mmBody}

  test "a partial, unverified or declined row has no exact pin":
    for cell in exactPinned:
      let a = admitMagic(cell, msArm)
      check a.admitted            # refused (declined, unverified, never)
      if a.admitted:
        check a.payload != mmPartial

  test "a row pinned as a decline is not claimed modelled without a partial shape":
    check declinePinned.len > 0
    for cell in declinePinned:
      let a = admitMagic(cell, msArm)
      # a decline pin on an admitted row is only honest for a partial or
      # folded row (the shape that declines); a plain modelled row would be
      # a stale claim.
      if a.admitted: check a.payload in {mmPartial, mmFolded}

  test "no exact pin of a cell also pins its decline":
    for cell in exactPinned: check cell notin declinePinned
