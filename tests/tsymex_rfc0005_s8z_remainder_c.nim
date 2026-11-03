## RFC-0005 (soundness channels) slice S8z -- S8u's remainder.
##
## Seven places S8u reported (RFC §2.5, S8u's "Different mechanisms"). Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build) by the oracle test of each suite, which runs the SUT itself.
##
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8z_remainder`, `tsymex_rfc0005_s8z_remainder_b`,
## `tsymex_rfc0005_s8z_remainder_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 87 s).
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

template expectUnsat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnsat

template expectExactSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat
  check r.errors.len == 0

# ---- (2) an enum result with no ordinal 0 ---------------------------------------

type
  S8zE1 = enum z1A = 1, z1B = 2
  S8zR = object
    n: int
    e: S8zE1

# ---- (7) container shapes ------------------------------------------------------------
#
# A `Table[string, V]` value and a `HashSet[T]` element of any fixed-width
# int type (`int8`..`uint64`, `char`, `byte`, an enum, a `range`) or `bool`
# are now modelled in the 64-bit cell. What still declines, scoped: a non-
# `string` key and a non-integer value or element. (RFC-0005 S8am closed
# the THIRD decline this suite originally documented here -- a `char` /
# `byte` / `uint8` container PARAMETER, witness-only -- by adding
# `IRType.isChar`, the provenance the witness renderer needed; see
# `setCharParam`'s own test below, which S8z had pinned declined and S8am
# repins passing.)

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
  # RFC-0005 S8ar backs an integer-like key, and S8at a float one; a tuple
  # key is still unbacked.
  var t: Table[(int, int), int]
  t[(x, x)] = 1
  if t[(x, x)] == 1: symexTarget("s8z_tik")

proc tabStrVal(x: int) =
  # RFC-0005 S8ar backs a string value, S8at a container one, and S8bz a
  # tuple; a `distinct` value is still unbacked.
  type DT = distinct (int, int)
  var t: Table[string, DT]
  t["a"] = DT((1, 1))
  if x > 0 and t.len == 1: symexTarget("s8z_tsv")

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
    ## RFC-0005 S8am: `r.witness[0]` is the `c: char` PARAMETER (not the
    ## local `HashSet[char]`), and now renders Nim's own `char` (was
    ## `uint8`, per S8z, when this test was first written -- see
    ## `IRType.isChar`'s own doc comment).
    if r.status == sxSat: check r.witness[0] == 'a'

  test "HashSet[char] parameter witness is modelled (RFC-0005 S8am; was feUnsupportedWitnessType)":
    let r = symexFind(setCharParam, tLabel("s8z_scp"))
    expectExactSat(r)
    if r.status == sxSat: check 'a' in r.witness[0]

  test "scoped declines: a non-string key, a non-int value or element":
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
    for r in [rk, rv, rs]:
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
