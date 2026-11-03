## RFC-0005 (soundness channels) slice S8z -- S8u's remainder.
##
## Seven places S8u reported (RFC §2.5, S8u's "Different mechanisms"). Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build) by the oracle test of each suite, which runs the SUT itself.
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8z_remainder_b`, `tsymex_rfc0005_s8z_remainder_c`,
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
