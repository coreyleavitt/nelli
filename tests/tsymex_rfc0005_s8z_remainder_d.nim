## RFC-0005 (soundness channels) slice S8z -- S8u's remainder.
##
## Seven places S8u reported (RFC §2.5, S8u's "Different mechanisms"). Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build) by the oracle test of each suite, which runs the SUT itself.
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8z_remainder`, `tsymex_rfc0005_s8z_remainder_b`,
## `tsymex_rfc0005_s8z_remainder_c`. Split so that each part compiles and runs
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
