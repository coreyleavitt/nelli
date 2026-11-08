## RFC-0005 (soundness channels) slice S8au -- the S8an / S8ag remainder.
##
## Pinned here (the RFC's "As landed (S8au)" note has the design and the
## measurements):
##   (1) a local distinct value with no distinct-typed parameter: closed by
##       S8ad (`ensureDistinctSort`, walker 175); re-pinned over more shapes
##       (borrowed `+` / `==` / `<`, default-initialised, float base, a
##       returned value, an object field). A `seq` of a distinct type was
##       a scoped decline (a different mechanism, reported); RFC-0005 S8ba
##       models it;
##   (2) `start < 0 and y > 1 and start div y == start` under the sequence
##       theory: closed by S8ad (`divRangeFacts`) and pinned in
##       `tsymex_rfc0005_s8ad_remainder`; re-measured for S8au, not
##       re-walked here;
##   (3) a copy-in/copy-out `var` actual (or an `addr` actual) whose heap
##       cell a global or a capture the callee reaches can also hold:
##       RED, a false `sxSat` (the callee's write through the global was
##       lost to the write-back); S8au declined it (`feUnsupportedOp`),
##       and RFC-0005 S8ba passes the cell by reference, so the dead
##       labels are `sxUnsat` (`tsymex_rfc0005_s8ba_remainder` (4));
##   (4) every `find` needle (a literal of any length, a computed one) and
##       `rfind` lower to S8ag's index split: the axioms by a randomized
##       differential against Z3's own terms with three mutants, and the
##       walker by hits that were `sxUnknown` at the base;
##   (5) the chain facts link consecutive splits only (counted);
##   (6) the `c notin t` form follows the linked Z3 version;
##   and `var ptr` formals: `f(addr x)` does not compile; a local `p = addr
##   x` passed to one was `heUnsafeCast`, and is now S8an's local pointer.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8au_remainder_b`, `tsymex_rfc0005_s8au_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 75 s).

import std/[unittest, strutils, random, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8au_remainder")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (1) local distinct values ------------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Secs = distinct float
proc `+`(a, b: Secs): Secs {.borrow.}
proc `<`(a, b: Secs): bool {.borrow.}

type HoldM = object
  m: Meters

proc dLine(x: int) =
  var m = Meters(0)
  m = m + Meters(1)
  if m == Meters(1) and x == 3: symexTarget("line")
  if m == Meters(2): symexTarget("line_dead")

proc dZero(x: int) =
  var m: Meters
  m = m + Meters(x)
  if m == Meters(4): symexTarget("zero")
  if m == Meters(4) and x != 4: symexTarget("zero_dead")

proc dCmp(x: int) =
  let m = Meters(x)
  if m < Meters(3) and x > 1: symexTarget("cmp")
  if m < Meters(3) and x > 5: symexTarget("cmp_dead")

proc dFloat(x: float) =
  var s = Secs(1.5)
  s = s + Secs(x)
  if Secs(2.0) < s: symexTarget("flt")

proc mkM(x: int): Meters = Meters(x) + Meters(1)

proc dRet(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `mkM`
  let m = mkM(x)
  if m == Meters(5): symexTarget("ret")
  if m == Meters(5) and x != 4: symexTarget("ret_dead")

proc dField(x: int) =
  symexAssume(x > -100 and x < 100)   # no overflow path in `+`
  var o = HoldM(m: Meters(1))
  o.m = o.m + Meters(x)
  if o.m == Meters(3): symexTarget("fld")
  if o.m == Meters(3) and x != 2: symexTarget("fld_dead")

proc dSeq(x: int) =
  ## A different mechanism at S8au (it declined, scoped); RFC-0005 S8ba
  ## models a `seq` of a distinct type.
  var s = @[Meters(1)]
  s.add(s[0] + Meters(x))
  if s[1] == Meters(3): symexTarget("sq")

suite "S8au (1): a local distinct value":
  test "line": (verdict(dLine, "line", sxSat); verdict(dLine, "line_dead", sxUnsat))
  test "zero": (verdict(dZero, "zero", sxSat); verdict(dZero, "zero_dead", sxUnsat))
  test "cmp": (verdict(dCmp, "cmp", sxSat); verdict(dCmp, "cmp_dead", sxUnsat))
  test "flt": verdict(dFloat, "flt", sxSat)
  test "ret": (verdict(dRet, "ret", sxSat); verdict(dRet, "ret_dead", sxUnsat))
  test "fld": (verdict(dField, "fld", sxSat); verdict(dField, "fld_dead", sxUnsat))
  test "a seq of a distinct type is modelled (RFC-0005 S8ba)":
    let r = symexFind(dSeq, tLabel("sq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.errors.len == 0

# ---- (3) copy-in/copy-out through a global -----------------------------------

type Box = ref object
  x: int
type Other = ref object
  y: int

var gBox: Box
var gOtherRef: Other

proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc readXG(v: var int, k: int): int =
  v = k
  gBox.x

proc viaXG(v: var int, k: int) = setXG(v, k)

proc setXO(v: var int, k: int) =
  v = k
  gOtherRef.y = 5

proc setPXG(p: ptr int, k: int) =
  p[] = k
  gBox.x = 5

proc sutHeapG(k: int) =
  let p = Box(x: 0)
  gBox = p
  setXG(p.x, k)
  if p.x == 5: symexTarget("hg")
  if p.x == k and k != 5: symexTarget("hg_dead")

proc sutHeapGRead(k: int) =
  let p = Box(x: 0)
  gBox = p
  if readXG(p.x, k) != k: symexTarget("hgr_dead")

proc sutHeapGVia(k: int) =
  let p = Box(x: 0)
  gBox = p
  viaXG(p.x, k)
  if p.x == k and k != 5: symexTarget("hgv_dead")

proc sutHeapGAddr(k: int) =
  let p = Box(x: 0)
  gBox = p
  setPXG(addr p.x, k)
  if p.x == k and k != 5: symexTarget("hga_dead")

proc sutHeapOther(k: int) =
  let p = Box(x: 0)
  gOtherRef = Other(y: 0)
  setXO(p.x, k)
  if p.x == k and k == 9: symexTarget("ho")
  if p.x != k: symexTarget("ho_dead")

proc sutHeapCap(k: int) =
  let p = Box(x: 0)
  let q = p
  proc setXC(v: var int) =
    v = k
    q.x = 5
  setXC(p.x)
  if p.x == k and k != 5: symexTarget("hc_dead")

suite "S8au (3): copy-in/copy-out through a global":
  # RFC-0005 S8ba: the cell is passed by reference; S8au's declines are
  # the verdicts Nim gives.
  test "hg":
    verdict(sutHeapG, "hg", sxSat)
    verdict(sutHeapG, "hg_dead", sxUnsat)
  test "hgr": verdict(sutHeapGRead, "hgr_dead", sxUnsat)
  test "hgv": verdict(sutHeapGVia, "hgv_dead", sxUnsat)
  test "hga": verdict(sutHeapGAddr, "hga_dead", sxUnsat)
  test "ho":
    verdict(sutHeapOther, "ho", sxSat)
    verdict(sutHeapOther, "ho_dead", sxUnsat)
  test "hc": verdict(sutHeapCap, "hc_dead", sxUnsat)
