## RFC-0005 (soundness channels) slice S8aj -- S8ad's remainder.
##
## This slice closes:
##   (1) an uninitialised local array with an element write
##       (`var a: array[3, int]; a[0] = a[0] + 2; a[i]`). The parser
##       declined the zero-init (`zeroValueForType` had no array arm), left
##       the name unbound, and the element write bound it to a scalar: the
##       read then asserted (`weInternalWalkerFault`, "iekIndex on non-array
##       kind=svBV64"). An array, an object (`itTuple`) and a seq now take
##       Nim's `default(T)` (`mkZeroValue`, lowered by `defaultZero`), so
##       arrays of objects, objects holding arrays and seq fields are
##       zero-initialised too. A loop's element merge met an Int on one
##       path and a bitvector on the other (`iteSV` asserted); both are the
##       same Nim integer, so the merge reconciles them.
##   (2) an unchecked sum that wraps (`start >= 0 and y > 1 and
##       start + (y + 1) == start`, UNSAT, beside a sequence): `sxUnknown`
##       at 40.6M steps on Z3 5.1 and 40.9M on 4.13.4. `wrapIntToWidth`
##       wraps as `lo + (r - lo) mod 2^W`, and an overflowing sum puts
##       `r - lo` in `[2^W, 2^(W+1))`, one window past S8ad's `|a| < |b|`
##       pair. `divRangeFacts` now asserts that window too.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8aj_remainder`, `tsymex_rfc0005_s8aj_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 66 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8aj_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- (1) zero-init of local aggregates --------------------------------------

type
  Meters = distinct int
  P = object
    x, y: int
  H = object
    arr: array[3, int]
    n: int
  SQ = object
    s: seq[int]
    n: int
  PA = object
    ps: array[2, P]
  VK = enum vkA, vkB
  V = object
    n: int
    case k: VK
    of vkA: a: int
    of vkB: b: array[2, int]

proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}

proc zObjArr(v, i: int) =
  ## An object holding an array.
  var h: H
  h.arr[1] = v
  h.n = h.n + 1
  if i >= 0 and i < 3 and h.arr[i] == 6 and h.n == 1: symexTarget("objarr")
  if h.arr[2] != 0 or h.n != 1: symexTarget("objarr_dead")

proc zObjArrObj(v: int) =
  ## An object holding an array of objects.
  var o: PA
  o.ps[0].y = v
  if o.ps[0].y == 3 and o.ps[1].x == 0: symexTarget("nest")
  if o.ps[1].y != 0: symexTarget("nest_dead")

proc zSeqEmpty(v: int) =
  ## A seq field is empty.
  var o: SQ
  if o.s.len == 0 and o.n == 0 and v == 1: symexTarget("seq0")
  if o.s.len != 0: symexTarget("seq0_dead")

proc zSeqField(v: int) =
  var o: SQ
  o.s = @[v]
  if o.s.len == 1 and o.s[0] == 8 and o.n == 0: symexTarget("seq")
  if o.s.len != 1 or o.n != 0: symexTarget("seq_dead")

proc zSeqLocal(v: int) =
  var s: seq[int]
  s.add v
  if s.len == 1 and s[0] == 2: symexTarget("seql")
  if s.len == 2: symexTarget("seql_dead")

proc zDistinct(i: int) =
  ## `array[3, Meters]`, which S8ad found faults the same way.
  var a: array[3, Meters]
  a[0] = a[0] + Meters(2)
  if i >= 0 and i < 3 and a[i] == Meters(2): symexTarget("dist")
  if i >= 0 and i < 3 and a[i] == Meters(1): symexTarget("dist_dead")

proc zVariant(x: int) =
  ## A variant object: tag 0, its arm's fields and the plain ones zero.
  var v: V
  if v.k == vkA and v.a == 0 and v.n == 0 and x == 1: symexTarget("var")
  if v.k != vkA or v.a != 0 or v.n != 0: symexTarget("var_dead")

proc zMatrix(v, i, j: int) =
  ## An array of arrays.
  var m: array[2, array[2, int]]
  m[1][0] = v
  if i >= 0 and i < 2 and j >= 0 and j < 2 and m[i][j] == 9: symexTarget("mat")
  if m[0][0] != 0 or m[1][1] != 0: symexTarget("mat_dead")

suite "S8aj (1): a local aggregate is zero-initialised":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an object holding an array":
    let r = run(zObjArr, "objarr", sxSat)
    if r.status == sxSat: check r.witness[0] == 6 and r.witness[1] == 1
    discard run(zObjArr, "objarr_dead", sxUnsat)

  test "an object holding an array of objects":
    let r = run(zObjArrObj, "nest", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(zObjArrObj, "nest_dead", sxUnsat)

  test "a seq field is empty":
    let r0 = run(zSeqEmpty, "seq0", sxSat)
    if r0.status == sxSat: check r0.witness[0] == 1
    discard run(zSeqEmpty, "seq0_dead", sxUnsat)
    let r = run(zSeqField, "seq", sxSat)
    if r.status == sxSat: check r.witness[0] == 8
    discard run(zSeqField, "seq_dead", sxUnsat)

  test "a local seq is empty":
    let r = run(zSeqLocal, "seql", sxSat)
    if r.status == sxSat: check r.witness[0] == 2
    discard run(zSeqLocal, "seql_dead", sxUnsat)

  test "an array of a distinct type":
    let r = run(zDistinct, "dist", sxSat)
    if r.status == sxSat: check r.witness[0] == 0
    discard run(zDistinct, "dist_dead", sxUnsat)

  test "an array of arrays":
    let r = run(zMatrix, "mat", sxSat)
    if r.status == sxSat:
      check r.witness[0] == 9 and r.witness[1] == 1 and r.witness[2] == 0
    discard run(zMatrix, "mat_dead", sxUnsat)

  test "a variant object":
    let r = run(zVariant, "var", sxSat)
    if r.status == sxSat: check r.witness[0] == 1
    discard run(zVariant, "var_dead", sxUnsat)

  test "symexWalkerVersion >= 179":
    check parseInt(symexWalkerVersion) >= 179

{.push overflowChecks: off.}
{.pop.}
