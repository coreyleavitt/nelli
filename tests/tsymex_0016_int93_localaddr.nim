## RFC-0016 INT-93 (SOUNDNESS): the address of a named local is an address
## into an object of its own. `pointer(addr x) == pointer(addr y)` with
## `x: int` and `y: float` locals was a trusted false `sxSat` (INT-65's
## `i65PointerCrossSort`, once INT-83's pointer model met it): INT-83 tags a
## `ref`'s whole object by its type, but an address cell (`addr x`) carried no
## tag, so two sorts' cells were unrelated in the `pointer` space. INT-90
## deliberately lets two `ptr` PARAMETERS of different sorts share an address
## (a caller can pass `addr v` and `cast[ptr float](addr v)`), so the fix is
## not a decline of cross-sort pairs.
##
## Native (Nim 2.2.10, c and cpp alike): distinct locals never share an
## address, whatever their types; a caller's pointer never points into the
## callee's frame; the fields and elements of one local are at their offsets
## within it (the first field at the local's own address); an address equals
## itself.
##
## Model: the frame slot of a `var`/`let` local is an object of its own, made
## when its address is first taken (`walkAddrCell`), with an identity and a
## kind; an inline field or array element of one is that object at the
## field's or element's byte offset. Two such objects are distinct, from each
## other and from every address the routine was handed (INT-82's entry state);
## two addresses into one object are equal exactly when their offsets are.
## An array element's address has no cell in the walk and declines by name.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  L93 = object
    a: int
    b: int
  L93Mixed = object
    f: float
    n: int

proc lArrToPointer(a: int8) =
  var arr: array[3, int]
  let p = pointer(addr arr)
  if p != nil and a == 3: symexTarget("hit")

proc lSinkPtr(p: pointer): bool = p != nil

proc lSetToFormal(a: int8) =
  var s: set[uint8]
  if lSinkPtr(addr s) and a == 3: symexTarget("hit")

proc lSameType(a: int8) =
  var x = int(a)
  var y = int(a) + 1
  if pointer(addr x) == pointer(addr y): symexTarget("hit")

proc lCrossType(a: int8) =
  var x = int(a)
  var y = float(a)
  if pointer(addr x) == pointer(addr y): symexTarget("hit")

proc lCrossTypeCast(a: int8) =
  var x = int(a)
  var o = L93(a: int(a), b: 2)
  if cast[pointer](addr x) == cast[pointer](addr o): symexTarget("hit")

proc lCrossTypeLet(a: int8) =
  var x = int(a)
  var b = a > 3
  let p = pointer(addr x)
  if p == pointer(addr b) and a == 4: symexTarget("hit")

proc lVsPtrParam(q: ptr float; a: int8) =
  var x = int(a)
  if pointer(addr x) == pointer(q): symexTarget("hit")

proc lVsPtrParamSame(q: ptr int; a: int8) =
  var x = int(a)
  if pointer(addr x) == pointer(q): symexTarget("hit")

proc lVsPtrParamTyped(q: ptr int; a: int8) =
  var x = int(a)
  if addr(x) == q: symexTarget("hit")

proc lVsRef(a: int8) =
  var x = float(a)
  let r = new int
  if pointer(addr x) == cast[pointer](r): symexTarget("hit")

proc lVsPointerParam(p: pointer; a: int8) =
  var x = int(a)
  if p == pointer(addr x): symexTarget("hit")

proc lFieldsDiffer(a: int8) =
  var o = L93(a: int(a), b: 1)
  if pointer(addr o.a) == pointer(addr o.b): symexTarget("hit")

proc lFirstFieldIsObject(a: int8) =
  var o = L93(a: int(a), b: 1)
  if pointer(addr o.a) == pointer(addr o) and a == 6: symexTarget("hit")

proc lSecondFieldIsNot(a: int8) =
  var o = L93(a: int(a), b: 1)
  if pointer(addr o.b) == pointer(addr o): symexTarget("hit")

proc lFirstFieldNotApart(a: int8) =
  var o = L93(a: int(a), b: 1)
  if pointer(addr o.a) != pointer(addr o): symexTarget("hit")

proc lFieldTwice(a: int8) =
  var o = L93(a: int(a), b: 1)
  let p = pointer(addr o.b)
  o.a = 3
  if p != pointer(addr o.b): symexTarget("hit")

proc lTupleFields(a: int8) =
  var t = (int(a), 2.5)
  if pointer(addr t[0]) == pointer(addr t[1]): symexTarget("hit")

proc lMixedFields(a: int8) =
  var o = L93Mixed(f: float(a), n: 1)
  if pointer(addr o.n) == pointer(addr o.f): symexTarget("hit")

proc lFieldVsOtherLocal(a: int8) =
  var o = L93(a: int(a), b: 1)
  var y = float(a)
  if pointer(addr o.a) == pointer(addr y): symexTarget("hit")

proc lElems(i, j: int8) =
  var arr = [10, 20, 30]
  if i >= 0 and i < 3 and j >= 0 and j < 3 and
     pointer(addr arr[i]) == pointer(addr arr[j]) and i != 1:
    symexTarget("hit")

proc lElemsDistinct(i, j: int8) =
  var arr = [10, 20, 30]
  if i >= 0 and i < 3 and j >= 0 and j < 3 and i != j and
     pointer(addr arr[i]) == pointer(addr arr[j]):
    symexTarget("hit")

proc lElemZeroIsArray(a: int8) =
  var arr = [int(a), 2, 3]
  if pointer(addr arr[0]) == pointer(addr arr) and a == 2: symexTarget("hit")

proc lSelf(a: int8) =
  var x = int(a)
  if pointer(addr x) == pointer(addr x) and a == 5: symexTarget("hit")

proc lSelfTyped(a: int8) =
  var x = int(a)
  if addr(x) == addr(x) and a == 5: symexTarget("hit")

template verdict(fn: typed): SymexStatusKind =
  ## the pinned verdict, its declines on a failure
  block:
    let r = pinFind(fn, tLabel("hit"))
    checkpoint $r.errors
    r.status

template declinedBy(fn: typed; k: SymexErrorKind): bool =
  ## no verdict, and `k` among the declines
  block:
    let r = pinFind(fn, tLabel("hit"))
    checkpoint $r.errors
    var named = false
    for e in r.errors:
      if e.kind == k: named = true
    r.status == sxUnknown and named

suite "INT-93: a local's address is an object of its own":
  test "two locals of one type are two addresses":
    check verdict(lSameType) == sxUnsat

  test "two locals of two types are two addresses":
    check verdict(lCrossType) == sxUnsat
    check verdict(lCrossTypeCast) == sxUnsat
    check verdict(lCrossTypeLet) == sxUnsat

  test "a caller's pointer is no address in the callee's frame":
    check verdict(lVsPtrParam) == sxUnsat
    check verdict(lVsPtrParamSame) == sxUnsat
    check verdict(lVsPtrParamTyped) == sxUnsat
    check verdict(lVsPointerParam) == sxUnsat

  test "a local is no object `new` makes":
    check verdict(lVsRef) == sxUnsat

  test "the fields of one local are at their offsets":
    check verdict(lFieldsDiffer) == sxUnsat
    check verdict(lFirstFieldIsObject) == sxSat
    check verdict(lFirstFieldNotApart) == sxUnsat
    check verdict(lSecondFieldIsNot) == sxUnsat
    check verdict(lFieldTwice) == sxUnsat
    check verdict(lTupleFields) == sxUnsat
    check verdict(lMixedFields) == sxUnsat
    check verdict(lFieldVsOtherLocal) == sxUnsat

  test "an array element's address is not modelled: it declines by name":
    # A precision gap, not a verdict: `addr a[i]` of an array local has no
    # cell in the walk (S8be models a seq's elements), and `addr a` of an
    # array local declines in `walkAddrCell`.
    check declinedBy(lElems, feUnsupportedExprKind)
    check declinedBy(lElemsDistinct, feUnsupportedExprKind)
    check declinedBy(lElemZeroIsArray, feUnsupportedExprKind)

  test "the decline names the variable's type, not the pointer's":
    # `pointer(addr v)` and an `addr v` passed as a `pointer` formal are typed
    # `pointer`; the decline's "variable of type" once printed that
    # destination (`uninterp[__pointer]`) instead of the variable's own type.
    pinDecline(lArrToPointer, cellKey(axTypeClass, "pointer"),
               feUnsupportedOp,
               needle = "of a variable of type array[3, i64] is not modelled")
    pinDecline(lSetToFormal, cellKey(axTypeClass, "pointer"),
               feUnsupportedOp,
               needle = "of a variable of type set[u8] is not modelled")

  test "an address equals itself":
    check verdict(lSelf) == sxSat
    check verdict(lSelfTyped) == sxSat

  test "walker 455: the version floor":
    check parseInt(symexWalkerVersion) >= 455
