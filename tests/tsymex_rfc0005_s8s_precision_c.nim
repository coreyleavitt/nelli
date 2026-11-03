## RFC-0005 (soundness channels) slice S8s -- S8p's precision remainder.
##
## Four places the walker gave up on (or faulted over) code whose behaviour
## is fully determined, and one cpp compile failure. S8p reported them.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build) by the oracle test of each suite, which runs the SUT itself.
##   (1) a `seq[uint8]` element compared against a literal
##       (was `weInternalWalkerFault`, "field 'bv8' ... kind = svBV64");
##   (2) the zero value of a multi-variant whose ordinal 0 falls in an
##       `else` arm (was `feUnsupportedOpHavoc`);
##   (3) a callee returning an `array` (was `feUnsupportedOpHavoc`);
##   (4) a write to a variant arm field and a positional tuple-element
##       write (was `feUnsupportedStmtKind`);
##   (5) the walker version floor.
## The cpp compile failure of `tsymex_r6_n43_parity` (a deleted
## `std::atomic::operator=`) is pinned by that suite compiling on cpp.
##
## RFC-0005 S8cm: part 3 of 7 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_d`, `tsymex_rfc0005_s8s_precision_e`,
## `tsymex_rfc0005_s8s_precision_f`, `tsymex_rfc0005_s8s_precision_g`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 134 s).

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (2) a multi-variant whose ordinal 0 is in an else arm ------------------------
#
# Real Nim zero-initialises `result`: both discriminators s3A (ordinal 0, which
# each axis's `else` arm covers) and every field 0, the else arms' too. Before
# S8s the untouched result was `feUnsupportedOpHavoc`.

type
  S8sK = enum s3A, s3B, s3C
  S8sMVE = object
    case k: S8sK
    of s3B: b: int
    else: e: int
    case j: S8sK
    of s3C: c: int
    else: f: int
  S8sVE = object
    ## A single `case` whose ordinal 0 is in its `else` arm.
    case vk: S8sK
    of s3C: vc: int
    else: ve: int

proc veMaybe(x: int): S8sVE =
  if x > 0: result = S8sVE(vk: s3C, vc: x)

proc callVE(x: int) =
  let v = veMaybe(x)
  if x <= 0 and v.vk == s3A and v.ve == 0: symexTarget("s8s_ve")
  if x <= 0 and v.vk != s3A: symexTarget("s8s_ve_dead")
  if x <= 0 and v.ve != 0: symexTarget("s8s_ve_edead")

suite "S8s (2) a multi-variant whose ordinal 0 is in an else arm":
  test "a single-case variant with ordinal 0 in its else arm":
    let r = symexFind(callVE, tLabel("s8s_ve"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    let d = symexFind(callVE, tLabel("s8s_ve_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let e = symexFind(callVE, tLabel("s8s_ve_edead"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxUnsat

# ---- (3) a callee returning an array ----------------------------------------------
#
# Real Nim: mkArr(5) is [5, 2, 3]; arrMaybe(4) is [0, 4], arrMaybe(0) is
# [0, 0]. Before S8s the caller's result was `feUnsupportedOpHavoc`
# (`retBindEq` had no array arm).

proc mkArr(x: int): array[3, int] =
  result = [x, 2, 3]

proc callArr(x: int) =
  let a = mkArr(x)
  if a[0] == 5 and a[1] == 2: symexTarget("s8s_arr")
  if a[2] != 3: symexTarget("s8s_arr_dead")

proc arrMaybe(x: int): array[2, int] =
  if x > 0: result = [0, x]

proc callArrZero(x: int) =
  let a = arrMaybe(x)
  if x > 0 and a[1] == 4 and a[0] == 0: symexTarget("s8s_arrz")
  if x <= 0 and a[1] != 0: symexTarget("s8s_arrz_dead")

proc idArr(a: array[2, int]): array[2, int] = a

proc callArrPass(x: int) =
  let a = idArr([x, 9])
  if a[0] == 3 and a[1] == 9: symexTarget("s8s_arrp")
  if a[1] != 9: symexTarget("s8s_arrp_dead")

proc closArr(x: int) =
  let f = proc (y: int): array[2, int] = [y, 2]
  let a = f(x)
  if a[0] == 4 and a[1] == 2: symexTarget("s8s_carr")
  if a[1] != 2: symexTarget("s8s_carr_dead")

suite "S8s (3) a callee returning an array":
  test "oracle":
    check mkArr(5) == [5, 2, 3]
    check arrMaybe(4) == [0, 4]
    check arrMaybe(0) == [0, 0]
    symexCaptureBegin()
    callArr(5); callArrZero(4); callArrPass(3); closArr(4)
    let hits = symexCaptureEnd()
    check "s8s_carr" in hits
    check "s8s_arr" in hits
    check "s8s_arrz" in hits
    check "s8s_arrp" in hits

  test "an array result binds its elements (was feUnsupportedOpHavoc)":
    let r = symexFind(callArr, tLabel("s8s_arr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(callArr, tLabel("s8s_arr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an untouched array result is zero":
    let r = symexFind(callArrZero, tLabel("s8s_arrz"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(callArrZero, tLabel("s8s_arrz_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an array passed through a callee":
    let r = symexFind(callArrPass, tLabel("s8s_arrp"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
    let d = symexFind(callArrPass, tLabel("s8s_arrp_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a closure returning an array (was feUnsupportedOp)":
    let r = symexFind(closArr, tLabel("s8s_carr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(closArr, tLabel("s8s_carr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
