## RFC-0005 (soundness channels) slice S8m -- S8l's remainder.
## Walker 159 -> 160.
##
## S8l reported six defects whose mechanism lay outside its design. Each is a
## claim the real SUT contradicts, or a verdict no check stands behind. Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build); the probe output is quoted beside the test, and where c and cpp
## disagree the test says so.
##   (1) `break` / `continue` leave through every enclosing `finally` (and
##       `defer`) innermost first; a labelled `break` leaves its `block`;
##       `continue` in a `for` loop still advances it;
##   (2) a Z3 sort mismatch is a recorded walker fault (`sxUnknown`), never a
##       silent verdict;
##   (3) a `ref` local assigned from a param, and a same-type `cast`, keep
##       the pointer's heap identity;
##   (4) an uninitialised `var p: ref T` local is nil;
##   (5) a closure's bare `return` returns the zero value;
##   (6) the walker version floor.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with `tsymex_rfc0005_s8m_exits`,
## `tsymex_rfc0005_s8m_exits_b`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 66 s).

import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (3) ref locals and same-type casts keep heap identity -------------------
#
# Probe (c and cpp identical):
#   refAssign(P(a: 3), 3) reaches the label; refAssign(nil, 3) does not
#   refAlias(p, 1): the write through `q` is the write through `p`
#   refCast(P(a: 3), 3) reaches the label: `cast[ref S8mObj](p)` is `p`
# Before S8m every one of these was `weInternalWalkerFault`: the uninitialised
# `q` was declined and left unbound, the cast was a declined expression whose
# dummy was an int, and `q != nil` then hit `eqBV`'s `a.kind == b.kind`
# assert (`runtime.nim:4608`).

type
  S8mObj = object
    a: int
  S8mOther = object
    b: float

proc refAssign(p: ref S8mObj; x: int) =
  var q: ref S8mObj
  if p != nil:
    q = p
  if q != nil:
    if q.a == x and x == 3: symexTarget("s8m_refassign")
  if q != nil and p == nil: symexTarget("s8m_refassign_dead")

proc refAlias(p: ref S8mObj; x: int) =
  var q: ref S8mObj
  if p != nil:
    q = p
    q.a = 41
    if p.a == 41 and x == 1: symexTarget("s8m_refalias")
    if p.a != 41: symexTarget("s8m_refalias_dead")

proc refCast(p: ref S8mObj; x: int) =
  let q = cast[ref S8mObj](p)
  if q != nil:
    if q.a == x and x == 3: symexTarget("s8m_refcast")
  if q != p: symexTarget("s8m_refcast_dead")

proc refCastOther(p: ref S8mObj; x: int) =
  let q = cast[ref S8mOther](p)
  if q != nil and x == 2: symexTarget("s8m_refcast_other")

# ---- (4) an uninitialised ref local is nil ------------------------------------
#
# Probe (c and cpp identical):
#   `var p: ref S8mObj; p == nil` is true
#   `var p: ref S8mObj; p.a = 1` is a nil access (SIGSEGV in a default debug
#     build; the walker models every nil access as NilAccessDefect, R5)
# Before S8m the declaration was `feUnsupportedStmtKind`.

proc uninitNil(x: int) =
  var p: ref S8mObj
  if p == nil and x == 2: symexTarget("s8m_uninit_nil")
  if p != nil: symexTarget("s8m_uninit_nil_dead")

proc uninitWrite(x: int) =
  var p: ref S8mObj
  if x == 2:
    p.a = 1

proc uninitNew(x: int) =
  var p: ref S8mObj
  if x > 0:
    p = new(S8mObj)
    p.a = x
  if p != nil and p.a == 4: symexTarget("s8m_uninit_new")
  if p == nil and x > 0: symexTarget("s8m_uninit_new_dead")

# ---- (5) a closure's bare return returns the zero value -----------------------
#
# Probe (c and cpp identical): closRet(-1) and closRet(1) both reach their
# labels -- f(-1) == 7, f(1) == 0 (Nim zero-initialises `result`).
# Before S8m a closure descent had no `retTy`, so the bare-return path joined
# the frame unbound, and `applyClosureGround` took its LAST BRANCH CONDITION
# (`y > 0`) for the value binding: `y > 0` became a ground axiom of the whole
# run, and `f(-1) == 7` was a false `sxUnsat`.

proc closRet(x: int) =
  let f = proc (y: int): int =
    if y > 0: return
    result = 7
  let r = f(x)
  if r == 7 and x == -1: symexTarget("s8m_closret_seven")
  if r == 0 and x == 1: symexTarget("s8m_closret_zero")
  if r != 0 and x == 1: symexTarget("s8m_closret_dead")

type
  S8mVK = enum svkA, svkB
  S8mV = object
    case k: S8mVK
    of svkA: a: int
    of svkB: b: int

proc closRetVariant(x: int) =
  ## A variant result's bare return. At S8m it had no modelled zero value
  ## and was `completeReturn`'s havoc site (`feUnsupportedOpHavoc`); RFC-0005
  ## S8n models it (Nim zero-initialises the variant: `k == svkA`, `a == 0`).
  let g = proc (y: int): S8mV =
    if y > 0: return
    result = S8mV(k: svkB, b: 3)
  let v = g(x)
  discard v
  if x == 5 and x == 6: symexTarget("s8m_closret_variant_dead")

suite "S8m (3) ref locals and same-type casts":
  test "oracle":
    var o = new(S8mObj)
    o.a = 3
    symexCaptureBegin()
    refAssign(o, 3); refAssign(nil, 3); refCast(o, 3)
    var o2 = new(S8mObj)
    refAlias(o2, 1)
    let hits = symexCaptureEnd()
    check "s8m_refassign" in hits
    check "s8m_refalias" in hits
    check "s8m_refcast" in hits
    check "s8m_refassign_dead" notin hits
    check "s8m_refcast_dead" notin hits

  test "a ref local assigned from a param keeps its identity (was weInternalWalkerFault)":
    let r = symexFind(refAssign, tLabel("s8m_refassign"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] != nil
      check r.witness[1] == 3
      check reproduces(refAssign(r.witness[0], r.witness[1]), "s8m_refassign")
    let d = symexFind(refAssign, tLabel("s8m_refassign_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a write through the local is a write through the param":
    let r = symexFind(refAlias, tLabel("s8m_refalias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(refAlias(r.witness[0], r.witness[1]), "s8m_refalias")
    let d = symexFind(refAlias, tLabel("s8m_refalias_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a same-type ref cast is the identity (was weInternalWalkerFault)":
    let r = symexFind(refCast, tLabel("s8m_refcast"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(refCast(r.witness[0], r.witness[1]), "s8m_refcast")
    let d = symexFind(refCast, tLabel("s8m_refcast_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a cast to a different pointee is a recorded decline, never a fault":
    let r = symexFind(refCastOther, tLabel("s8m_refcast_other"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, feUnsupportedExprKind)
    check not hasKind(r.errors, weInternalWalkerFault)

suite "S8m (4) an uninitialised ref local is nil":
  test "oracle":
    symexCaptureBegin()
    uninitNil(2); uninitNew(4)
    let hits = symexCaptureEnd()
    check "s8m_uninit_nil" in hits
    check "s8m_uninit_new" in hits

  test "the local is nil (was feUnsupportedStmtKind)":
    let r = symexFind(uninitNil, tLabel("s8m_uninit_nil"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2
    let d = symexFind(uninitNil, tLabel("s8m_uninit_nil_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a write through it raises NilAccessDefect":
    let r = symexFind(uninitWrite, tNilAccess())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "NilAccessDefect"
      check r.raisedWitness[0] == 2

  test "assigned a fresh cell on one branch, nil on the other":
    let r = symexFind(uninitNew, tLabel("s8m_uninit_new"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(uninitNew, tLabel("s8m_uninit_new_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

suite "S8m (5) a closure's bare return":
  test "oracle":
    symexCaptureBegin()
    closRet(-1); closRet(1)
    let hits = symexCaptureEnd()
    check "s8m_closret_seven" in hits
    check "s8m_closret_zero" in hits
    check "s8m_closret_dead" notin hits

  test "the bare-return guard is not an axiom of the run (was a false sxUnsat)":
    let r = symexFind(closRet, tLabel("s8m_closret_seven"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == -1
      check reproduces(closRet(r.witness[0]), "s8m_closret_seven")

  test "the bare return returns zero":
    let r = symexFind(closRet, tLabel("s8m_closret_zero"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 1
    let d = symexFind(closRet, tLabel("s8m_closret_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a variant result's bare return is its zero value (re-pinned by S8n)":
    let r = symexFind(closRetVariant, tLabel("s8m_closret_variant_dead"))
    checkpoint($r.status & " " & show(r.errors))
    # S8m pinned `feUnsupportedOpHavoc` + sxUnknown here: no variant zero
    # value, and a variant closure result substituted on the calling side.
    # RFC-0005 S8n models both (the zero value per real Nim, see
    # `tsymex_rfc0005_s8n_precision` (4)), so the dead label is a verdict.
    check not hasKind(r.errors, feUnsupportedOpHavoc)
    check r.status == sxUnsat

# ---- (6) walker version floor ---------------------------------------------------

suite "S8m (6) walker version":
  test "walker version is at least 160":
    check parseInt(symexWalkerVersion) >= 160
