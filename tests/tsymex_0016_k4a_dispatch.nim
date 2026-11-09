## RFC-0016 K4a-dispatch (section 8.1): the magic axis is consumed per site.
##
## `dispatchMagic` (smt/magic_rows) checks a site's `case` against the table
## at compile time. This file pins
##   * the once-per-site registry: every dispatched site was expanded in this
##     compilation (the parser is imported, so its expansions have run), none
##     twice, and a `case` that disagrees with the table does not compile;
##   * the sites' rows: what each site's arms are, read from the table;
##   * a pin per row family through `symexFind`: a SUT that reaches the magic,
##     the walker's verdict reproduced natively, one record per `magic:` cell.
## The cells no SUT can reach (compile-time-only, folded, macro and DrNim
## magics) stay allowlisted with their reason.
import std/[unittest, options, sets, sequtils, strutils]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/magic_rows
import nelli/smt/dsl_parser
import nelli/smt/canonicalize
import ./s8cu_helpers

static:
  # The parser expanded `dispatchMagic` once at each dispatched site.
  doAssert dispatchedMagicSites() == magicDispatchSites,
    "a dispatched site was not expanded: " & $dispatchedMagicSites()

template dispatchOk(site: untyped; body: untyped): bool =
  compiles(dispatchMagic(site, body))

suite "K4a-dispatch: the registry and the generated case":
  test "every dispatched site was expanded exactly once":
    const seen = dispatchedMagicSites()
    check seen == magicDispatchSites
    check msArm notin seen
    check msProcRegister notin seen

  test "the walker version is at the dispatch floor":
    check parseInt(symexWalkerVersion) >= 295

  test "a site cannot be dispatched twice":
    # `msNewString` is already expanded by the parser.
    let ok1 = dispatchOk(msNewString):
      case "x"
      of "NewString", "NewStringOfCap": 1
      else: 0
    check not ok1

  test "a case that disagrees with the table does not compile":
    let ok2 = dispatchOk(msVarStmt):
      case "x"
      of "NoSuchMagic": 1
      else: 0
    check not ok2
    let ok3 = dispatchOk(msVarStmt):
      case "x"
      of "Swap": 1
      else: 0                        # the other arms are missing
    check not ok3
    let ok4 = dispatchOk(msVarStmt):
      case "x"
      of "Destroy": 1                 # a refused row
      else: 0
    check not ok4
    let ok5 = dispatchOk(msArm):
      case "x"
      of "Swap": 1
      else: 0                        # not a dispatched site
    check not ok5

  test "the table names each site's arms":
    check toHashSet(toSeq(magicAxis.keysAt(msCallSwitch))) ==
      ["AshrI", "Ord", "Chr", "EnsureMove", "+%", "-%", "*%", "/%",
       "%%", "<%", "<=%"].toHashSet
    check toHashSet(toSeq(magicAxis.keysAt(msInfix))) ==
      ["+%", "-%", "*%", "/%", "%%", "<%", "<=%"].toHashSet
    check toHashSet(toSeq(magicAxis.keysAt(msNewString))) ==
      ["NewString", "NewStringOfCap"].toHashSet
    check "Swap" in toHashSet(toSeq(magicAxis.keysAt(msVarStmt)))

  test "an arm's row declines at another site, naming its cell":
    let a = admitMagic("AshrI", msVarStmt)
    check not a.admitted
    check a.decline[0] == some(feUnsupportedOp)
    check "magic:AshrI" in a.decline[1]

# --- SUTs ------------------------------------------------------------------

template sutI2(name, cond: untyped) {.dirty.} =
  proc name(a, b: int) =
    if cond: symexTarget("hit")
template sutI1(name, cond: untyped) {.dirty.} =
  proc name(a: int) =
    if cond: symexTarget("hit")
template sutU2(name, cond: untyped) {.dirty.} =
  proc name(a, b: uint) =
    if cond: symexTarget("hit")
template sutF2(name, cond: untyped) {.dirty.} =
  proc name(a, b: float) =
    if cond: symexTarget("hit")
template sutF1(name, cond: untyped) {.dirty.} =
  proc name(a: float) =
    if cond: symexTarget("hit")
template sutC1(name, cond: untyped) {.dirty.} =
  proc name(a, b: char) =
    if cond: symexTarget("hit")

# Arithmetic
sutI2(sAddI, a + b == 7)
sutI2(sSubI, a - b == 7)
sutI2(sMulI, a * b == 12 and a > 1 and b > 1)
sutI2(sDivI, b > 0 and a div b == 3)
sutI2(sModI, b > 0 and a mod b == 2)
sutI1(sNegI, -a == 5)
sutI1(sPlusI, +a == 5)
sutI1(sAbsI, abs(a) == 5 and a < 0)
sutI1(sSucc, succ(a) == 5)
sutI1(sPred, pred(a) == 5)
sutI2(sMinI, min(a, b) == 3 and a > b)
sutI2(sMaxI, max(a, b) == 3 and a < b)
# Bits
sutI1(sNotI, not a == 5)
sutI2(sAndI, (a and b) == 5)
sutI2(sOrI, (a or b) == 5)
sutI2(sXorI, (a xor b) == 5)
sutI1(sShlI, (a shl 2) == 20)
sutI1(sShrI, (a shr 1) == 3)
sutI1(sAshrI, ashr(a, 1) == -3)
# Comparisons
sutI2(sEqI, a == b and a == 7)
sutI2(sLeI, a <= b and b == 3)
sutI2(sLtI, a < b and b == 3)
# The unsigned operators over the signed ints
sutI2(sAddUs, a +% b == 7)
sutI2(sSubUs, a -% b == 7)
sutI2(sMulUs, a *% b == 12)
sutI2(sDivUs, b != 0 and a /% b == 3)
sutI2(sModUs, b != 0 and a %% b == 2)
sutI2(sLtUs, a <% b and b == 3)
sutI2(sLeUs, a <=% b and b == 3)
# Unsigned
sutU2(sAddU, a + b == 7)
sutU2(sSubU, a - b == 7)
sutU2(sMulU, a * b == 12)
sutU2(sDivU, b != 0 and a div b == 3)
sutU2(sModU, b != 0 and a mod b == 2)
sutU2(sLeU, a <= b and b == 3)
sutU2(sLtU, a < b and b == 3)
# Float
sutF2(sAddF, a + b == 7.5)
sutF2(sSubF, a - b == 7.5)
sutF2(sMulF, a * b == 6.0 and a == 2.0)
# b is pinned like sMulF pins a: the division circuit over two free operands is
# a query some Z3 builds answer unknown (CI Z3 5.1.0.0 did); b == 2.5 leaves
# a / 2.5 == 2.0, witness a == 5.0, inside fDom.
sutF2(sDivF, b == 2.5 and a / b == 2.0)
sutF1(sNegF, -a == 2.5)
sutF1(sPlusF, +a == 2.5)
sutF2(sEqF, a == b and a == 2.5)
sutF2(sLeF, a <= b and b == 3.0)
sutF2(sLtF, a < b and b == 3.0)
# Bool and char
sutI2(sEqB, (a > 0) == (b > 0) and a == 3 and b == 4)
sutI2(sLeB, (a > 0) <= (b > 0) and a < 0)
sutI2(sLtB, (a > 0) < (b > 0) and b > 0)
sutI2(sNotB, not (a > 0) and b == 2)
sutI2(sAnd, a > 0 and b > 0 and a + b == 7)
sutI2(sOr, a > 0 or b > 0 and a + b == 7)
sutI2(sXorB, (a > 0) xor (b > 0) and a == 3)
sutC1(sEqCh, a == b and a == 'x')
sutC1(sLeCh, a <= b and b == 'x')
sutC1(sLtCh, a < b and b == 'x')
sutI1(sOrd, ord(a > 3) == 1 and a == 9)
sutI1(sChr, a >= 0 and a <= 255 and chr(a) == 'x')

# Statement-position magics (the msVarStmt arms and the older arms)
proc sInc(a: int) =
  var x = a
  inc x
  if x == 5: symexTarget("hit")
proc sDec(a: int) =
  var x = a
  dec(x, 2)
  if x == 5: symexTarget("hit")
proc sSwap(a, b: int) =
  var x = a
  var y = b
  swap(x, y)
  if x == 3 and y == 4: symexTarget("hit")
proc sWasMoved(a: int) =
  var x = a
  wasMoved(x)
  if x == 0 and a == 5: symexTarget("hit")
proc sMove(a: int) =
  var x = a
  let y = move(x)
  if y == 5 and x == 0: symexTarget("hit")
proc sEnsureMove(a: int) =
  var x = a
  let y = ensureMove(x)
  if y == 5: symexTarget("hit")
proc sNew(a: int) =
  var r: ref int
  new(r)
  r[] = a
  if r[] == 5: symexTarget("hit")
proc sIsNil(a: int) =
  var r: ref int
  if a > 3: new(r)
  if r.isNil and a == 2: symexTarget("hit")
proc sSetLenSeq(a: int) =
  var s = @[1, 2]
  if a >= 0 and a < 8:
    setLen(s, a)
    if s.len == 3 and a == 3: symexTarget("hit")
proc sSetLenStr(a: int) =
  var s = "ab"
  if a >= 0 and a < 8:
    setLen(s, a)
    if s.len == 3 and a == 3: symexTarget("hit")
proc sNewString(a: int) =
  if a >= 0 and a < 8:
    let s = newString(a)
    if s.len == 3: symexTarget("hit")
proc sNewStringOfCap(a: int) =
  if a >= 0 and a < 8:
    let s = newStringOfCap(a)
    if s.len == 0 and a == 5: symexTarget("hit")

# Strings, sequences, arrays and sets
proc sLenStr(s: string) =
  if s.len == 2: symexTarget("hit")
proc sLenSeq(s: seq[int]) =
  if s.len == 2: symexTarget("hit")
proc sLenArr(a: int) =
  var arr: array[3, int]
  arr[0] = a
  if arr.len == 3 and a == 4: symexTarget("hit")
proc sHigh(a: int) =
  var arr: array[3, int]
  arr[0] = a
  if arr.high == 2 and arr.low == 0 and a == 4: symexTarget("hit")
proc sEqStr(s: string) =
  if s == "ab": symexTarget("hit")
proc sLeStr(s: string) =
  if s <= "ab" and s.len == 2: symexTarget("hit")
proc sLtStr(s: string) =
  if s < "ab" and s.len == 2: symexTarget("hit")
proc sConStr(s: string) =
  if s & "x" == "abx": symexTarget("hit")
proc sAppendCh(s: string) =
  var t = s
  t.add 'x'
  if t == "abx": symexTarget("hit")
proc sAppendStr(s: string) =
  var t = s
  t &= "xy"
  if t == "abxy": symexTarget("hit")
proc sAppendElem(s: seq[int]) =
  var t = s
  t.add 7
  if t.len == 3 and t[2] == 7: symexTarget("hit")
proc sArrGet(i: int) =
  let arr = [5, 6, 7]
  if i >= 0 and i < 3 and arr[i] == 6: symexTarget("hit")
proc sArrPut(i: int) =
  var arr = [5, 6, 7]
  if i >= 0 and i < 3:
    arr[i] = 9
    if arr[1] == 9 and i == 1: symexTarget("hit")
proc sCharToStr(c: char) =
  if $c == "x": symexTarget("hit")
proc sInSet(c: char) =
  if c in {'a', 'b'} and c != 'a': symexTarget("hit")
proc sIncl(c: char) =
  var st: set[char] = {}
  incl(st, c)
  if 'x' in st: symexTarget("hit")
proc sExcl(c: char) =
  var st: set[char] = {'x', 'y'}
  excl(st, c)
  if 'x' notin st: symexTarget("hit")
proc sNewSeq(a: int) =
  if a >= 0 and a < 8:
    let s = newSeq[int](a)
    if s.len == 3: symexTarget("hit")

const
  uDom = sampled([0'u, 1, 3, 4, 5, 7, 10, 12, high(uint)])
  fDom = sampled([0.0, 1.0, 2.0, 2.5, 3.0, 5.0, 7.5, -2.5, 1.5, 6.0])
  sDom = sampled(["", "a", "ab", "abc", "x"])
  qDom = sampled(@[@[], @[1], @[1, 2], @[1, 2, 3]])
  chDom = sampled(['a', 'b', 'x', 'y'])
  cDom = sampled(['a', 'x', 'z'])
  smallInts = sampled([-3, -1, 0, 1, 2, 3, 4, 5, 7, 9, 12, 20, 255])

template pinSat(sut: untyped; cell: static string; dom: untyped = smallInts) =
  test cell:
    let r = pinExact(sut, cellKey(axMagic, cell), domain = dom)
    check r.status == sxSat

suite "K4a-dispatch: pins through symexFind, one record per cell":
  pinSat(sAddI, "AddI")
  pinSat(sSubI, "SubI")
  pinSat(sMulI, "MulI")
  pinSat(sDivI, "DivI")
  pinSat(sModI, "ModI")
  pinSat(sNegI, "UnaryMinusI")
  pinSat(sPlusI, "UnaryPlusI")
  pinSat(sAbsI, "AbsI")
  pinSat(sSucc, "Succ")
  pinSat(sPred, "Pred")
  pinSat(sMinI, "MinI")
  pinSat(sMaxI, "MaxI")
  pinSat(sNotI, "BitnotI")
  pinSat(sAndI, "BitandI")
  pinSat(sOrI, "BitorI")
  pinSat(sXorI, "BitxorI")
  pinSat(sShlI, "ShlI")
  pinSat(sShrI, "ShrI")
  pinSat(sAshrI, "AshrI")
  pinSat(sEqI, "EqI")
  pinSat(sLeI, "LeI")
  pinSat(sLtI, "LtI")
  pinSat(sAddUs, "+%")
  pinSat(sSubUs, "-%")
  pinSat(sMulUs, "*%")
  pinSat(sDivUs, "/%")
  pinSat(sModUs, "%%")
  pinSat(sLtUs, "<%")
  pinSat(sLeUs, "<=%")
  pinSat(sAddU, "AddU", uDom)
  pinSat(sSubU, "SubU", uDom)
  pinSat(sMulU, "MulU", uDom)
  pinSat(sDivU, "DivU", uDom)
  pinSat(sModU, "ModU", uDom)
  pinSat(sLeU, "LeU", uDom)
  pinSat(sLtU, "LtU", uDom)
  pinSat(sAddF, "AddF64", fDom)
  pinSat(sSubF, "SubF64", fDom)
  pinSat(sMulF, "MulF64", fDom)
  pinSat(sDivF, "DivF64", fDom)
  pinSat(sNegF, "UnaryMinusF64", fDom)
  pinSat(sPlusF, "UnaryPlusF64", fDom)
  pinSat(sEqF, "EqF64", fDom)
  pinSat(sLeF, "LeF64", fDom)
  pinSat(sLtF, "LtF64", fDom)
  pinSat(sEqB, "EqB")
  pinSat(sLeB, "LeB")
  pinSat(sLtB, "LtB")
  pinSat(sNotB, "Not")
  pinSat(sAnd, "And")
  pinSat(sOr, "Or")
  pinSat(sXorB, "Xor")
  pinSat(sEqCh, "EqCh", cDom)
  pinSat(sLeCh, "LeCh", cDom)
  pinSat(sLtCh, "LtCh", cDom)
  pinSat(sOrd, "Ord")
  pinSat(sChr, "Chr")
  pinSat(sInc, "Inc")
  pinSat(sDec, "Dec")
  pinSat(sSwap, "Swap")
  pinSat(sWasMoved, "WasMoved")
  pinSat(sMove, "Move")
  pinSat(sEnsureMove, "EnsureMove")
  pinSat(sNew, "New")
  pinSat(sIsNil, "IsNil")
  pinSat(sSetLenSeq, "SetLengthSeq")
  pinSat(sSetLenStr, "SetLengthStr")
  pinSat(sNewString, "NewString")
  pinSat(sNewStringOfCap, "NewStringOfCap")
  pinSat(sLenStr, "LengthStr", sDom)
  pinSat(sLenSeq, "LengthSeq", qDom)
  pinSat(sLenArr, "LengthArray")
  pinSat(sHigh, "High")
  pinSat(sEqStr, "EqStr", sDom)
  pinSat(sLeStr, "LeStr", sDom)
  pinSat(sLtStr, "LtStr", sDom)
  pinSat(sConStr, "ConStrStr", sDom)
  pinSat(sAppendCh, "AppendStrCh", sDom)
  pinSat(sAppendStr, "AppendStrStr", sDom)
  pinSat(sAppendElem, "AppendSeqElem", qDom)
  pinSat(sArrGet, "ArrGet")
  pinSat(sArrPut, "ArrPut")
  pinSat(sCharToStr, "CharToStr", chDom)
  pinSat(sInSet, "InSet", chDom)
  pinSat(sIncl, "Incl", chDom)
  pinSat(sExcl, "Excl", chDom)
  pinSat(sNewSeq, "NewSeq")
