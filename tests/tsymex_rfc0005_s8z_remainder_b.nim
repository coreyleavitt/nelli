## RFC-0005 (soundness channels) slice S8z -- S8u's remainder.
##
## Seven places S8u reported (RFC §2.5, S8u's "Different mechanisms"). Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build) by the oracle test of each suite, which runs the SUT itself.
##
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8z_remainder`, `tsymex_rfc0005_s8z_remainder_c`,
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
