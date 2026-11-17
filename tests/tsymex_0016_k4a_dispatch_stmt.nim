## RFC-0016 K4a-dispatch (section 8.1): the magic axis is consumed per site.
##
## `dispatchMagic` (smt/magic_dispatch) checks a site's `case` against the table
## at compile time. This file pins
##   * the once-per-site registry: every dispatched site was expanded in this
##     compilation (the parser is imported, so its expansions have run), none
##     twice, and a `case` that disagrees with the table does not compile;
##   * the sites' rows: what each site's arms are, read from the table;
##   * a pin per row family through `symexFind`: a SUT that reaches the magic,
##     the walker's verdict reproduced natively, one record per `magic:` cell.
## The cells no SUT can reach (compile-time-only, folded, macro and DrNim
## magics) stay allowlisted with their reason.
##
## Split (RFC-0016 INT-51) into three files so each compiles inside the CI
## ceiling: `tsymex_0016_k4a_dispatch_signed` (the registry, and the signed
## integer magics), `tsymex_0016_k4a_dispatch_scalar` (unsigned, float, bool
## and char) and `tsymex_0016_k4a_dispatch_stmt` (the statement-position
## magics, strings, sequences, arrays and sets). Every pin of the one file is
## in exactly one of them.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

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

template pinSatStd(sut: untyped; cell: static string) =
  test cell:
    let r = pinExact(sut, cellKey(axStdlibBody, cell), domain = smallInts)
    check r.status == sxSat

suite "K4a-dispatch: pins through symexFind, one record per cell":
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
