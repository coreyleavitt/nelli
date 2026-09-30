## RFC-0005 (soundness channels) slice S8z -- S8u's remainder.
##
## Seven places S8u reported (RFC §2.5, S8u's "Different mechanisms"). Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build) by the oracle test of each suite, which runs the SUT itself.
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template expectSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat

template expectUnsat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnsat

template expectExactSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat
  check r.errors.len == 0

# ---- (1) array reads with a nonzero low bound ----------------------------------

proc lowLit(x: int) =
  var a: array[1..3, int] = [7, 8, 9]
  if x == 1 and a[1] == 7 and a[3] == 9: symexTarget("s8z_lb")
  if a[1] != 7: symexTarget("s8z_lb_dead")

proc lowParam(a: array[1..3, int]) =
  if a[1] == 5 and a[3] == 6: symexTarget("s8z_lp")

proc lowSym(a: array[1..3, int]; i: int) =
  if i >= 1 and i <= 3 and a[i] == 42: symexTarget("s8z_ls")

suite "S8z (1) array reads with a nonzero low bound":
  test "oracle":
    symexCaptureBegin()
    lowLit(1); lowParam([5, 0, 6]); lowSym([0, 42, 0], 2)
    let hits = symexCaptureEnd()
    check "s8z_lb" in hits
    check "s8z_lp" in hits
    check "s8z_ls" in hits

  test "a[1] of array[1..3, int] is its first element (was a false sxUnsat)":
    let r = symexFind(lowLit, tLabel("s8z_lb"))
    expectSat(r)
    expectUnsat(symexFind(lowLit, tLabel("s8z_lb_dead")))

  test "an array[1..3, int] param's witness drives the real code":
    let r = symexFind(lowParam, tLabel("s8z_lp"))
    expectSat(r)
    if r.status == sxSat:
      check reproduces(lowParam(r.witness[0]), "s8z_lp")

  test "a symbolic index into array[1..3, int]":
    let r = symexFind(lowSym, tLabel("s8z_ls"))
    expectSat(r)
    if r.status == sxSat:
      check reproduces(lowSym(r.witness[0], r.witness[1]), "s8z_ls")

# ---- (2) an enum result with no ordinal 0 ---------------------------------------

type
  S8zE1 = enum z1A = 1, z1B = 2
  S8zR = object
    n: int
    e: S8zE1

proc mkR(x: int): S8zR =
  if x > 0: result.n = x

proc callR(x: int) =
  let r = mkR(x)
  if x <= 0 and ord(r.e) == 0: symexTarget("s8z_ez")
  if x <= 0 and ord(r.e) != 0: symexTarget("s8z_ez_dead")

suite "S8z (2) an enum result with no ordinal 0":
  test "oracle":
    check ord(mkR(0).e) == 0
    symexCaptureBegin()
    callR(0)
    let hits = symexCaptureEnd()
    check "s8z_ez" in hits

  test "an untouched enum field holds ordinal 0 (was a false sxUnsat)":
    expectSat(symexFind(callR, tLabel("s8z_ez")))
    expectUnsat(symexFind(callR, tLabel("s8z_ez_dead")))

# ---- (3) an array type alias -------------------------------------------------------

type S8zArr3 = array[3, int]

proc aliasParam(a: S8zArr3) =
  if a[0] == 4 and a[2] == 5: symexTarget("s8z_al")

suite "S8z (3) an array type alias":
  test "oracle":
    symexCaptureBegin()
    aliasParam([4, 0, 5])
    let hits = symexCaptureEnd()
    check "s8z_al" in hits

  test "an alias of array[3, int] is the array (was uninterp)":
    let r = symexFind(aliasParam, tLabel("s8z_al"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(aliasParam(r.witness[0]), "s8z_al")

# ---- (4) an inline anonymous range discriminator ------------------------------------

type
  S8zRV = object
    case d: range[0..2]
    of 0: a: int
    of 1: b: int
    else: c: int

proc rangeDisc(v: S8zRV) =
  if v.d == 1 and v.b == 3: symexTarget("s8z_rd")

suite "S8z (4) an inline anonymous range discriminator":
  test "oracle":
    symexCaptureBegin()
    rangeDisc(S8zRV(d: 1, b: 3))
    let hits = symexCaptureEnd()
    check "s8z_rd" in hits

  test "compiles, and is modelled":
    let r = symexFind(rangeDisc, tLabel("s8z_rd"))
    expectSat(r)
    if r.status == sxSat:
      check reproduces(rangeDisc(r.witness[0]), "s8z_rd")

# ---- (5) an array write at a symbolic index -----------------------------------------

proc symWrite(i: int; v: int) =
  var a = [1, 2, 3]
  if i >= 0 and i <= 2 and v >= -100 and v <= 100:
    a[i] = v
    if a[1] == 9 and a[0] == 1 and a[2] == 3: symexTarget("s8z_sw")
    if a[0] + a[1] + a[2] != 6 - (i + 1) + v: symexTarget("s8z_sw_dead")

proc symAug(i: int) =
  var a = [1, 2, 3]
  if i >= 0 and i <= 2:
    a[i] += 10
    if a[2] == 13: symexTarget("s8z_sa")

proc raiser(x: int): int =
  if x > 0: raise newException(ValueError, "s8z")
  x

proc orderW(i, x: int) =
  var a = [1, 2, 3]
  if i > 2 and x > 0:
    a[i] = raiser(x)

proc lowOrderW(i, x: int) =
  var a: array[1..3, int] = [1, 2, 3]
  if i < 1 and x > 0:
    a[i] = raiser(x)

proc lowWrite(i, v: int) =
  var a: array[1..3, int] = [1, 2, 3]
  if i >= 1 and i <= 3 and v > 100 and v < 200:
    a[i] = v
    if a[3] == v and a[1] == 1: symexTarget("s8z_lw")
    if a[i] != v: symexTarget("s8z_lw_dead")

suite "S8z (5) an array write at a symbolic index":
  test "oracle":
    symexCaptureBegin()
    symWrite(1, 9); symAug(2); lowWrite(3, 150)
    let hits = symexCaptureEnd()
    check "s8z_sw" in hits
    check "s8z_sa" in hits
    check "s8z_lw" in hits

  test "a[i] = v (was feUnsupportedStmtKind)":
    let r = symexFind(symWrite, tLabel("s8z_sw"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0] == 1
      check r.witness[1] == 9
    expectUnsat(symexFind(symWrite, tLabel("s8z_sw_dead")))

  test "a[i] += v":
    let r = symexFind(symAug, tLabel("s8z_sa"))
    expectExactSat(r)
    if r.status == sxSat: check r.witness[0] == 2

  test "oracle: the index is checked before the value is evaluated":
    expect IndexDefect:
      orderW(5, 1)
    expect IndexDefect:
      lowOrderW(0, 1)

  test "a[i] = raiser(x): an out-of-bounds index raises IndexDefect, not the value's ValueError":
    for r in [symexFind(orderW, tRaisedExn("ValueError")),
              symexFind(lowOrderW, tRaisedExn("ValueError"))]:
      checkpoint($r.status & " " & show(r.errors))
      check r.status == sxRaised
      if r.status == sxRaised:
        check r.raisedTypeId.endsWith("IndexDefect")

  test "a write through a nonzero low bound lands at the right element":
    let r = symexFind(lowWrite, tLabel("s8z_lw"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(lowWrite(r.witness[0], r.witness[1]), "s8z_lw")
    expectUnsat(symexFind(lowWrite, tLabel("s8z_lw_dead")))

# ---- (6) a closure-returning callee -------------------------------------------------

proc mkF(t: int): proc(y: int): int =
  result = proc(y: int): int = y + t

proc callF(x: int) =
  if x > -100 and x < 100:
    let f = mkF(x)
    if f(1) == 5: symexTarget("s8z_cf")
    if f(1) != x + 1: symexTarget("s8z_cf_dead")

proc mkNilF(t: int): proc(y: int): int =
  if t > 0:
    result = proc(y: int): int = y + t

proc callNilF(x: int) =
  let f = mkNilF(x)
  if x <= 0 and f == nil: symexTarget("s8z_nf")

proc callNilCmp(x: int) =
  # Both paths reach the compare: the closure one and the nil one.
  let f = mkNilF(x)
  if f == nil: symexTarget("s8z_nc")

suite "S8z (6) a closure-returning callee":
  test "oracle":
    symexCaptureBegin()
    callF(4); callNilF(0); callNilCmp(0)
    let hits = symexCaptureEnd()
    check "s8z_cf" in hits
    check "s8z_nf" in hits
    check "s8z_nc" in hits

  test "the returned closure is modelled (was weInternalWalkerFault)":
    let r = symexFind(callF, tLabel("s8z_cf"))
    expectExactSat(r)
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(callF(r.witness[0]), "s8z_cf")
    expectUnsat(symexFind(callF, tLabel("s8z_cf_dead")))

  test "a closure that is not the callee's own lambda is a scoped decline":
    let r = symexFind(callNilF, tLabel("s8z_nf"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    for e in r.errors: check e.kind != weInternalWalkerFault
    var hof = false
    for e in r.errors: hof = hof or e.kind == ceUnsupportedHof
    check hof

  test "a proc value compared with nil is a scoped decline, never a walker fault":
    # RED on cpp (path order walks the closure first): `nil` became the
    # generic unsupported-literal int dummy, compared with an `svClosure`.
    let r = symexFind(callNilCmp, tLabel("s8z_nc"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    for e in r.errors: check e.kind != weInternalWalkerFault
    var hof = false
    for e in r.errors: hof = hof or e.kind == ceUnsupportedHof
    check hof

# ---- (7) container shapes ------------------------------------------------------------
#
# A `Table[string, V]` value and a `HashSet[T]` element of any fixed-width
# int type (`int8`..`uint64`, `char`, `byte`, an enum, a `range`) or `bool`
# are now modelled in the 64-bit cell. What still declines, scoped: a non-`string`
# key, a non-integer value or element, and -- as a witness only -- a
# `char` / `byte` / `uint8` container parameter.

type S8zE3 = enum e3A, e3B, e3C

proc tabI32(t: Table[string, int32]) =
  if t.len == 1 and t.hasKey("a") and t["a"] == -5'i32: symexTarget("s8z_ti32")

proc tabEnum(x: int) =
  var t: Table[string, S8zE1]
  if x > 0: t["k"] = z1B
  else: t["k"] = z1A
  if t["k"] == z1B: symexTarget("s8z_ten")
  if x > 0 and t["k"] != z1B: symexTarget("s8z_ten_dead")

proc setU16(s: HashSet[uint16]) =
  if s.len == 2 and 7'u16 in s and 9'u16 notin s: symexTarget("s8z_su16")

proc setI8(x: int8) =
  var s: HashSet[int8]
  s.incl x
  s.incl -3'i8
  if s.len == 1 and x == -3'i8: symexTarget("s8z_si8")
  if s.len == 2 and x == -3'i8: symexTarget("s8z_si8_dead")

proc setEnumFull(s: HashSet[S8zE3]) =
  if s.len == 3 and e3A notin s: symexTarget("s8z_se_dead")
  if s.len == 2 and e3A notin s: symexTarget("s8z_se")

proc setEnumOver(s: HashSet[S8zE3]) =
  if s.len == 4: symexTarget("s8z_se4_dead")

proc tabBool(t: Table[string, bool]) =
  if t.len == 1 and t.hasKey("on") and t["on"]: symexTarget("s8z_tb")

proc setBoolOver(s: HashSet[bool]) =
  if s.len == 3: symexTarget("s8z_sb_dead")

proc setCharLocal(c: char) =
  var s: HashSet[char]
  s.incl 'a'
  if c in s: symexTarget("s8z_sc")

proc setCharParam(s: HashSet[char]) =
  if 'a' in s: symexTarget("s8z_scp")

proc tabIntKey(x: int) =
  var t: Table[int, int]
  t[x] = 1
  if t[x] == 1: symexTarget("s8z_tik")

proc tabStrVal(x: int) =
  var t: Table[string, string]
  t["a"] = "b"
  if x > 0 and t["a"] == "b": symexTarget("s8z_tsv")

proc setStr(x: int) =
  var s: HashSet[string]
  s.incl "a"
  if x > 0 and "a" in s: symexTarget("s8z_ss")

proc errKinds(r: auto): seq[SymexErrorKind] =
  for e in r.errors: result.add e.kind

suite "S8z (7) container shapes":
  test "oracle":
    symexCaptureBegin()
    tabI32({"a": -5'i32}.toTable)
    tabEnum(1)
    setU16([7'u16, 8].toHashSet)
    setI8(-3)
    setEnumFull([e3B, e3C].toHashSet)
    tabBool({"on": true}.toTable)
    setCharLocal('a')
    setCharParam(['a'].toHashSet)
    tabIntKey(3); tabStrVal(1); setStr(1)
    let hits = symexCaptureEnd()
    for l in ["s8z_ti32", "s8z_ten", "s8z_su16", "s8z_si8", "s8z_se",
              "s8z_tb", "s8z_sc", "s8z_scp", "s8z_tik", "s8z_tsv", "s8z_ss"]:
      checkpoint(l)
      check l in hits

  test "Table[string, int32] param (was seUnsupportedTableValType)":
    let r = symexFind(tabI32, tLabel("s8z_ti32"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(tabI32(r.witness[0]), "s8z_ti32")

  test "Table[string, enum] local":
    expectExactSat(symexFind(tabEnum, tLabel("s8z_ten")))
    expectUnsat(symexFind(tabEnum, tLabel("s8z_ten_dead")))

  test "HashSet[uint16] param (was seUnsupportedSetCharInterop)":
    let r = symexFind(setU16, tLabel("s8z_su16"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(setU16(r.witness[0]), "s8z_su16")

  test "HashSet[int8] local: a negative element is one cell":
    let r = symexFind(setI8, tLabel("s8z_si8"))
    expectExactSat(r)
    expectUnsat(symexFind(setI8, tLabel("s8z_si8_dead")))

  test "HashSet[enum] param: the size is bounded by the enum's domain":
    let r = symexFind(setEnumFull, tLabel("s8z_se"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(setEnumFull(r.witness[0]), "s8z_se")
    expectUnsat(symexFind(setEnumFull, tLabel("s8z_se_dead")))
    expectUnsat(symexFind(setEnumOver, tLabel("s8z_se4_dead")))

  test "Table[string, bool] param, HashSet[bool] bounded by its two values":
    let r = symexFind(tabBool, tLabel("s8z_tb"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(tabBool(r.witness[0]), "s8z_tb")
    expectUnsat(symexFind(setBoolOver, tLabel("s8z_sb_dead")))

  test "HashSet[char] local is modelled":
    let r = symexFind(setCharLocal, tLabel("s8z_sc"))
    expectExactSat(r)
    if r.status == sxSat: check r.witness[0] == 'a'.uint8

  test "scoped declines: a char-set witness, a non-string key, a non-int value or element":
    let rc = symexFind(setCharParam, tLabel("s8z_scp"))
    checkpoint($rc.status & " " & show(rc.errors))
    check rc.status == sxUnknown
    check feUnsupportedWitnessType in errKinds(rc)
    let rk = symexFind(tabIntKey, tLabel("s8z_tik"))
    checkpoint($rk.status & " " & show(rk.errors))
    check rk.status == sxUnknown
    check seUnsupportedTableKeyType in errKinds(rk)
    let rv = symexFind(tabStrVal, tLabel("s8z_tsv"))
    checkpoint($rv.status & " " & show(rv.errors))
    check rv.status == sxUnknown
    check seUnsupportedTableValType in errKinds(rv)
    let rs = symexFind(setStr, tLabel("s8z_ss"))
    checkpoint($rs.status & " " & show(rs.errors))
    check rs.status == sxUnknown
    check seUnsupportedSetCharInterop in errKinds(rs)
    for r in [rc, rk, rv, rs]:
      for e in r.errors: check e.kind != weInternalWalkerFault

# ---- (8) found on the way: `pairs` loops, uninitialised composite locals -------------
#
# `for i, x in pairs(c)` bound `i` to the ELEMENT and left `x` unbound, so
# a label reading `i` alone was a false `sxSat` (the loop index of an
# `array[3..5, T]` "reached" 0), and one reading `x` was
# `feGlobalReadUnmodelled`. An uninitialised array, object or variant
# local was a decline that left the name unbound, and the next element
# write or field read faulted (`weInternalWalkerFault`).

type
  S8zPE1 = enum pe1 = 1, pe2 = 2
  S8zPObj = object
    e: S8zPE1
    n: int
  S8zPK = enum pkA, pkB
  S8zPV = object
    case k: S8zPK
    of pkA: a: int
    of pkB: b: int

proc lbPairs(x: int) =
  var a: array[3..5, int] = [x, 2, 3]
  var s = 0
  for i, v in a:
    if i == 3: s = v
  if s == 7: symexTarget("s8z_lbp")

proc lbPairsDead(x: int) =
  var a: array[3..5, int] = [x, 2, 3]
  var s = 0
  for i, v in a:
    if i == 0: s = 1
  if s == 1: symexTarget("s8z_lbp_dead")

proc enumPairs(x: int) =
  var a: array[S8zPK, int]
  a[pkB] = x
  for k, v in a:
    if k == pkB and v == 4: symexTarget("s8z_ep")

proc seqPairs(s: seq[int]) =
  for i, v in s:
    if i == 1 and v == 5: symexTarget("s8z_sp")

proc uninitArr(x: int) =
  var a: array[3, int]
  a[1] = x
  if a[1] == 7 and a[0] == 0: symexTarget("s8z_ua")
  if a[2] != 0: symexTarget("s8z_ua_dead")

proc uninitObj(x: int) =
  var r: S8zPObj
  if ord(r.e) == 0 and r.n == 0 and x == 3: symexTarget("s8z_uo")
  if ord(r.e) != 0: symexTarget("s8z_uo_dead")

proc uninitVariant(x: int) =
  var v: S8zPV
  if v.k == pkA and v.a == 0 and x == 3: symexTarget("s8z_uv")

suite "S8z (8) pairs loops and uninitialised composite locals":
  test "oracle":
    symexCaptureBegin()
    lbPairs(7); lbPairsDead(0); enumPairs(4); seqPairs(@[0, 5])
    uninitArr(7); uninitObj(3); uninitVariant(3)
    let hits = symexCaptureEnd()
    for l in ["s8z_lbp", "s8z_ep", "s8z_sp", "s8z_ua", "s8z_uo", "s8z_uv"]:
      check l in hits
    check "s8z_lbp_dead" notin hits

  test "for i, x in pairs(array[3..5, T]): i runs 3..5 (was a false sxSat)":
    expectExactSat(symexFind(lbPairs, tLabel("s8z_lbp")))
    expectUnsat(symexFind(lbPairsDead, tLabel("s8z_lbp_dead")))

  test "for k, x in pairs(array[Enum, T]) and pairs(seq[T])":
    expectExactSat(symexFind(enumPairs, tLabel("s8z_ep")))
    let r = symexFind(seqPairs, tLabel("s8z_sp"))
    expectExactSat(r)
    if r.status == sxSat:
      check reproduces(seqPairs(r.witness[0]), "s8z_sp")

  test "an uninitialised array local is zero (was weInternalWalkerFault)":
    expectExactSat(symexFind(uninitArr, tLabel("s8z_ua")))
    expectUnsat(symexFind(uninitArr, tLabel("s8z_ua_dead")))

  test "an uninitialised object local is zero, an enum field ordinal 0":
    expectExactSat(symexFind(uninitObj, tLabel("s8z_uo")))
    expectUnsat(symexFind(uninitObj, tLabel("s8z_uo_dead")))

  test "an uninitialised variant local is its first arm, zero":
    expectExactSat(symexFind(uninitVariant, tLabel("s8z_uv")))

# ---- walker version ---------------------------------------------------------------

suite "S8z walker version":
  test "symexWalkerVersion is at least S8z's":
    check parseInt(symexWalkerVersion) >= 177
