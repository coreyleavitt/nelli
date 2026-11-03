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
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8aj_remainder_b`, `tsymex_rfc0005_s8aj_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
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

proc zSelf(i: int) =
  ## S8ad's exhibit, verbatim.
  var a: array[3, int]
  a[0] = a[0] + 2
  if i >= 0 and i < 3 and a[i] == 2: symexTarget("self")
  if i >= 0 and i < 3 and a[i] == 1: symexTarget("self_dead")

proc zLine(x, i: int) =
  var a: array[3, int]
  a[1] = x
  if i >= 0 and i < 3 and a[i] == 5 and a[0] == 0: symexTarget("line")
  if a[0] != 0 or a[2] != 0: symexTarget("line_dead")

proc zSymRead(x, i, j: int) =
  ## Writes at literal indices, reads at two symbolic ones.
  symexAssume(x >= -100 and x <= 100)
  var a: array[4, int]
  a[2] = x
  a[3] = x + 1
  if i >= 0 and i < 4 and j >= 0 and j < 4 and a[i] + a[j] == 15:
    symexTarget("symr")
  if i >= 0 and i < 2 and j >= 0 and j < 2 and a[i] + a[j] != 0:
    symexTarget("symr_dead")

proc zLoop(x: int) =
  symexAssume(x >= -100 and x <= 100)
  var a: array[3, int]
  for k in 0 ..< 3:
    a[0] = a[0] + x
    a[2] = a[2] + k
  if a[0] == 9 and a[1] == 0: symexTarget("loop")
  if a[0] == 10 or a[2] != 3: symexTarget("loop_dead")

proc iLoop(x, i: int) =
  ## The same loop over an initialised array, read at a symbolic index.
  symexAssume(x >= -100 and x <= 100)
  var a = [0, 0, 0]
  for k in 0 ..< 3:
    a[0] = a[0] + x
    a[2] = a[2] + k
  if i >= 0 and i < 3 and a[i] == 9: symexTarget("iloop")
  if i >= 0 and i < 3 and a[i] == 10: symexTarget("iloop_dead")

proc zBranch(x: int) =
  var a: array[2, int]
  if x > 0: a[1] = x
  if a[1] == 0: symexTarget("branch")
  if a[1] == 0 and x > 0: symexTarget("branch_dead")

proc zOr(x: int) =
  var a: array[2, int]
  if (x > 3 or (a[0] = 1; true)) and a[0] == 1: symexTarget("or")
  if x > 3 and a[0] != 0: symexTarget("or_dead")

proc zAnd(x: int) =
  var a: array[2, bool]
  if x > 3 and (a[1] = true; true): discard
  if a[1]: symexTarget("and")
  if a[1] and x <= 3: symexTarget("and_dead")

proc zArrObj(v, i: int) =
  ## An array of objects: every element's every field is zero.
  var ps: array[2, P]
  ps[1].x = v
  if i >= 0 and i < 2 and ps[i].x == 4 and ps[i].y == 0: symexTarget("arrobj")
  if ps[0].x != 0 or ps[1].y != 0: symexTarget("arrobj_dead")

suite "S8aj (1): a local aggregate is zero-initialised":

  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an element write then a symbolic read (S8ad's exhibit)":
    let r = run(zSelf, "self", sxSat)
    if r.status == sxSat: check r.witness[0] == 0
    discard run(zSelf, "self_dead", sxUnsat)

  test "untouched elements read zero":
    let r = run(zLine, "line", sxSat)
    if r.status == sxSat: check r.witness[1] == 1 and r.witness[0] == 5
    discard run(zLine, "line_dead", sxUnsat)

  test "reads at symbolic indices":
    let r = run(zSymRead, "symr", sxSat)
    if r.status == sxSat:
      let (x, i, j) = (r.witness[0], r.witness[1], r.witness[2])
      var a: array[4, int]
      a[2] = x
      a[3] = x + 1
      check i >= 0 and i < 4 and j >= 0 and j < 4 and a[i] + a[j] == 15
    discard run(zSymRead, "symr_dead", sxUnsat)

  test "writes in a loop":
    let r = run(zLoop, "loop", sxSat)
    if r.status == sxSat: check r.witness[0] == 3
    discard run(zLoop, "loop_dead", sxUnsat)
    ## RED, even over an initialised array: `weInternalWalkerFault`
    ## (`iteSV: kind mismatch svBV64 vs svInt`).
    let r2 = run(iLoop, "iloop", sxSat)
    if r2.status == sxSat: check r2.witness[0] == 3 and r2.witness[1] == 0
    discard run(iLoop, "iloop_dead", sxUnsat)

  test "a write on one branch":
    let r = run(zBranch, "branch", sxSat)
    if r.status == sxSat: check r.witness[0] <= 0
    discard run(zBranch, "branch_dead", sxUnsat)

  test "a write in a short-circuit operand":
    let r = run(zOr, "or", sxSat)
    if r.status == sxSat: check r.witness[0] <= 3
    discard run(zOr, "or_dead", sxUnsat)
    let r2 = run(zAnd, "and", sxSat)
    if r2.status == sxSat: check r2.witness[0] > 3
    discard run(zAnd, "and_dead", sxUnsat)

  test "an array of objects":
    let r = run(zArrObj, "arrobj", sxSat)
    if r.status == sxSat: check r.witness[0] == 4 and r.witness[1] == 1
    discard run(zArrObj, "arrobj_dead", sxUnsat)

{.push overflowChecks: off.}
{.pop.}
