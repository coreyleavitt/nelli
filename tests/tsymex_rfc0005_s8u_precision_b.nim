## RFC-0005 (soundness channels) slice S8u -- S8s's precision remainder.
##
## Six places the walker gave up on (or faulted over) code whose behaviour is
## fully determined. S8s reported them. Every expected value was probed
## against the real compiler (Nim 2.2.10, debug build) by the oracle test of
## each suite, which runs the SUT itself.
##   (1) a variant constructor naming an `else`-covered tag
##       (was `feUnsupportedExprKind`);
##   (2) a callee building a local `Table` / `HashSet`
##       (was `weInternalWalkerFault`, `lower`'s `doAssert recv.kind`);
##   (3) a callee allocating its `ref` result with `new(result)`
##       (was `weInternalWalkerFault`, "retBindEq: kind mismatch");
##   (4) a multi-variant with a `bool` discriminator
##       (was `weInternalWalkerFault`, "must be a BV kind (got svBool)");
##   (5) the zero value of a `distinct` result and of a type holding a
##       `HashSet` / `Table` (was `feUnsupportedOpHavoc`);
##   (6) `op=` on an array element (was `feUnsupportedStmtKind`);
##   (7) the walker version floor.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8u_precision`, `tsymex_rfc0005_s8u_precision_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 70 s).

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
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
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

# ---- (1) a constructor naming an else-covered tag ---------------------------------

type
  S8uK = enum u3A, u3B, u3C
  S8uVE = object
    case vk: S8uK
    of u3C: vc: int
    else: ve: int

# ---- (3) a callee allocating its ref result with new(result) ----------------------

type S8uNode = ref object
  v: int
  w: int

proc mkNode(x: int): S8uNode =
  new(result)
  result.v = x

proc callNode(x: int) =
  let n = mkNode(x)
  if n.v == 9 and n.w == 0: symexTarget("s8u_nr")
  if n.w != 0: symexTarget("s8u_nr_dead")

suite "S8u (3) new(result) in a callee":
  test "oracle":
    symexCaptureBegin()
    callNode(9)
    let hits = symexCaptureEnd()
    check "s8u_nr" in hits

  test "a new(result) ref result (was weInternalWalkerFault)":
    let r = symexFind(callNode, tLabel("s8u_nr"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 9
    expectUnsat(symexFind(callNode, tLabel("s8u_nr_dead")))

# ---- (4) a multi-variant with a bool discriminator --------------------------------

type
  S8uMB = object
    case b: bool
    of true: t: int
    of false: f: int
    case k: S8uK
    of u3A: a: int
    else: e: int

proc mbParam(m: S8uMB) =
  if m.b and m.t == 3 and m.k == u3C: symexTarget("s8u_mb")
  if not m.b and m.f == 2: symexTarget("s8u_mbf")

suite "S8u (4) a multi-variant with a bool discriminator":
  test "oracle":
    symexCaptureBegin()
    mbParam(S8uMB(b: true, t: 3, k: u3C, e: 0))
    mbParam(S8uMB(b: false, f: 2, k: u3A, a: 0))
    let hits = symexCaptureEnd()
    check "s8u_mb" in hits
    check "s8u_mbf" in hits

  test "a bool axis (was weInternalWalkerFault)":
    let r = symexFind(mbParam, tLabel("s8u_mb"))
    expectSat(r)
    if r.status == sxSat:
      check reproduces(mbParam(r.witness[0]), "s8u_mb")
    let f = symexFind(mbParam, tLabel("s8u_mbf"))
    expectSat(f)
    if f.status == sxSat:
      check reproduces(mbParam(f.witness[0]), "s8u_mbf")

# ---- (5) zero values: distinct, and types holding a HashSet / Table ---------------

type S8uMeters = distinct int

proc mMaybe(x: int): S8uMeters =
  if x > 0: result = S8uMeters(x)

proc callMeters(x: int) =
  let m = mMaybe(x)
  if x <= 0 and int(m) == 0: symexTarget("s8u_dz")
  if x <= 0 and int(m) != 0: symexTarget("s8u_dz_dead")
  if x > 0 and int(m) == 6: symexTarget("s8u_dz6")

type S8uBag = object
  n: int
  s: HashSet[int]
  t: Table[string, int]

proc bagMaybe(x: int): S8uBag =
  if x > 0: result.n = x

proc callBag(x: int) =
  let b = bagMaybe(x)
  if x <= 0 and b.n == 0 and b.s.len == 0 and b.t.len == 0:
    symexTarget("s8u_bz")
  if x <= 0 and b.n != 0: symexTarget("s8u_bz_dead")

suite "S8u (5) zero values of distinct and HashSet/Table-holding results":
  test "oracle":
    check int(mMaybe(0)) == 0
    symexCaptureBegin()
    callMeters(0); callMeters(6); callBag(0)
    let hits = symexCaptureEnd()
    check "s8u_dz" in hits
    check "s8u_dz6" in hits
    check "s8u_bz" in hits

  test "an untouched distinct result is its base type's zero":
    let r = symexFind(callMeters, tLabel("s8u_dz"))
    expectSat(r)
    expectUnsat(symexFind(callMeters, tLabel("s8u_dz_dead")))
    let s = symexFind(callMeters, tLabel("s8u_dz6"))
    expectSat(s)
    if s.status == sxSat: check s.witness[0] == 6

  test "an untouched result holding a HashSet and a Table":
    let r = symexFind(callBag, tLabel("s8u_bz"))
    expectSat(r)
    expectUnsat(symexFind(callBag, tLabel("s8u_bz_dead")))
