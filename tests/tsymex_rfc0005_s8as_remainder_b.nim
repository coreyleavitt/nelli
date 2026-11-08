## RFC-0005 (soundness channels) slice S8as -- S8an's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8as_remainder`, `tsymex_rfc0005_s8as_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 80 s).

import std/[unittest, strutils, math]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8as_remainder_b")

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
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (2) an opaque call writes a module-level variable ----------------------
#
# WRONG VERDICT before S8as: an inert opaque call (statement position, value
# arguments) was a no-op for the walk, on the argument that the walker did
# not model globals; S8an made it model them. `gOp` kept the value written
# before the call: `og` was a false `sxUnsat` with `errors` empty. Probed:
# `sutOpaqueGlobal(5)` reaches `og`.

var gOp: int

# ---- (4) a closure's write to a capture or a global --------------------------

proc sutClosureCapWrite(v: int) =
  var c = 0
  let f = proc (a: int) =
    c = a
  f(v)
  if c == 5: symexTarget("cw")
  if c != v: symexTarget("cw_dead")

proc sutClosureGlobalWrite(v: int) =
  gOp = 0
  let h = proc (a: int) =
    gOp = a
  h(v)
  if gOp == 5: symexTarget("gw")
  if gOp != v: symexTarget("gw_dead")

proc sutClosureBranchWrite(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var c = 0
  let f = proc (a: int) =
    if a > 0: c = a
    else: c = -a
  f(v)
  if c == 3 and v < 0: symexTarget("cb")
  if c < 0: symexTarget("cb_dead")

proc sutClosureTwice(v: int) =
  # The body reads the global as it stands at each call.
  gOp = 0
  let f = proc (): int = gOp
  let a = f()
  gOp = v
  if f() == 5 and a == 0: symexTarget("ct")
  if f() == a and v != 0: symexTarget("ct_dead")

proc sutClosureIncTwice(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var n = v
  let inc1 = proc () =
    n += 1
  inc1()
  inc1()
  if n == 7: symexTarget("it")
  if n != v + 2: symexTarget("it_dead")

proc sutEvalOrder(v: int) =
  # Probed: `c + g()` is 15 under c and cpp -- the call runs first.
  var c = 1
  let g = proc (): int =
    c = 10
    5
  let r = c + g()
  if r == 15 and v == 1: symexTarget("eo")
  if r == 6: symexTarget("eo_dead")

proc sutShortCircuitWrite(v: int) =
  var c = 0
  let f = proc (): bool =
    c = 1
    true
  if v > 0 and f(): discard
  if c == 1 and v > 0: symexTarget("sw")
  if c == 1 and v <= 0: symexTarget("sw_dead")

proc sutShortCircuitRaise(x: int) =
  # WRONG VERDICT before S8as: the closure on the right of `and` was
  # evaluated unconditionally, so its raise on `x == 0` was reachable.
  let f = proc (): bool =
    if x == 0: raise newException(ValueError, "zero")
    true
  try:
    if x != 0 and f(): symexTarget("sr")
  except ValueError:
    symexTarget("sr_dead")

proc mkCounter(): proc () =
  var n = 0
  result = proc () =
    n += 1

proc sutOutOfFrame(v: int) =
  let c = mkCounter()
  c()
  if v == 1: symexTarget("of")

# ---- (6) two `addr` of different parts of one variable ----------------------

type
  S8asPair = object
    a, b: int
  S8asOuter = object
    inner: S8asPair
    c: int

proc twoPtr(p, q: ptr int; v: int) =
  p[] = v
  q[] = v + 1

proc pairAndPart(p: ptr S8asPair; q: ptr int; v: int) =
  p[].b = v
  q[] = v + 1

proc twoVar(x, y: var int; v: int) =
  x = v
  y = v + 1

proc sutAddrFields(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asPair()
  twoPtr(addr o.a, addr o.b, v)
  if o.a == 4 and o.b == 5: symexTarget("af")
  if o.b != o.a + 1: symexTarget("af_dead")

proc sutAddrElems(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var a: array[3, int]
  twoPtr(addr a[0], addr a[2], v)
  if a[0] == 4 and a[2] == 5 and a[1] == 0: symexTarget("ae")
  if a[1] != 0 or a[2] != a[0] + 1: symexTarget("ae_dead")

proc sutAddrNested(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asOuter()
  twoPtr(addr o.inner.a, addr o.c, v)
  if o.inner.a == 4 and o.c == 5: symexTarget("an")
  if o.inner.b != 0: symexTarget("an_dead")

proc sutVarFields(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asPair()
  twoVar(o.a, o.b, v)
  if o.a == 4 and o.b == 5: symexTarget("vf")
  if o.b != o.a + 1: symexTarget("vf_dead")

proc sutAddrOverlap(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asOuter()
  pairAndPart(addr o.inner, addr o.inner.a, v)   # a whole and its part
  if o.inner.b == 4: symexTarget("ao")

suite "RFC-0005 S8as (4): a closure's writes reach the caller":
  test "a capture written in the frame that built the closure":
    verdict(sutClosureCapWrite, "cw", sxSat)
    verdict(sutClosureCapWrite, "cw_dead", sxUnsat)
  test "a global written by a closure body":
    verdict(sutClosureGlobalWrite, "gw", sxSat)
    verdict(sutClosureGlobalWrite, "gw_dead", sxUnsat)
  test "a write on each of two arms":
    verdict(sutClosureBranchWrite, "cb", sxSat)
    verdict(sutClosureBranchWrite, "cb_dead", sxUnsat)
  test "a global read by the body at each of two calls":
    verdict(sutClosureTwice, "ct", sxSat)
    verdict(sutClosureTwice, "ct_dead", sxUnsat)
  test "two calls each read the other's write":
    verdict(sutClosureIncTwice, "it", sxSat)
    verdict(sutClosureIncTwice, "it_dead", sxUnsat)
  test "the call in an operand runs before the operands are read":
    verdict(sutEvalOrder, "eo", sxSat)
    verdict(sutEvalOrder, "eo_dead", sxUnsat)
  test "a closure on the right of `and` runs only under its guard":
    verdict(sutShortCircuitWrite, "sw", sxSat)
    verdict(sutShortCircuitWrite, "sw_dead", sxUnsat)
    verdict(sutShortCircuitRaise, "sr", sxSat)
    verdict(sutShortCircuitRaise, "sr_dead", sxUnsat)
  test "a capture written by a closure applied outside its frame is kept":
    # RFC-0005 S8ax: the capture lives in an env cell the walk threads to
    # every frame (was the scoped `ceCaptureByRefUnmodelled` decline).
    let r = symexFind(sutOutOfFrame, tLabel("of"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(ceCaptureByRefUnmodelled)

suite "RFC-0005 S8as (6): the alias check is by path":
  test "two fields of one object are two cells":
    verdict(sutAddrFields, "af", sxSat)
    verdict(sutAddrFields, "af_dead", sxUnsat)
  test "two constant indices of one array are two cells":
    verdict(sutAddrElems, "ae", sxSat)
    verdict(sutAddrElems, "ae_dead", sxUnsat)
  test "nested field paths that part":
    verdict(sutAddrNested, "an", sxSat)
    verdict(sutAddrNested, "an_dead", sxUnsat)
  test "two `var` fields of one object":
    verdict(sutVarFields, "vf", sxSat)
    verdict(sutVarFields, "vf_dead", sxUnsat)
  test "a whole and its part still decline":
    pinDecline(sutAddrOverlap, declKey, feUnsupportedOp, tLabel("ao"), "aliases another argument")
