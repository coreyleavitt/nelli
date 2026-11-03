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
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8u_precision`, `tsymex_rfc0005_s8u_precision_b`. Split so
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

template expectSat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxSat

template expectUnsat(r: untyped) =
  checkpoint($r.status & " " & show(r.errors))
  check r.status == sxUnsat

# ---- (6) op= on an array element --------------------------------------------------

proc arrSet(b: int) =
  var a = [1, 2, 3]
  a[1] = b
  if a[1] == 7 and a[0] == 1 and a[2] == 3: symexTarget("s8u_as")
  if a[0] != 1: symexTarget("s8u_as_dead")

proc arrAug(b: int) =
  var a = [1, 2, 3]
  if b > -1000 and b < 1000:
    a[0] += b
  if a[0] == 10 and a[1] == 2: symexTarget("s8u_aa")
  if a[2] != 3: symexTarget("s8u_aa_dead")

suite "S8u (6) op= on an array element":
  test "oracle":
    symexCaptureBegin()
    arrAug(9); arrSet(7)
    let hits = symexCaptureEnd()
    check "s8u_aa" in hits
    check "s8u_as" in hits

  test "an array element's = at a constant index":
    let r = symexFind(arrSet, tLabel("s8u_as"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 7
    expectUnsat(symexFind(arrSet, tLabel("s8u_as_dead")))

  test "an array element's += (was feUnsupportedStmtKind)":
    let r = symexFind(arrAug, tLabel("s8u_aa"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 9
    expectUnsat(symexFind(arrAug, tLabel("s8u_aa_dead")))

# ---- (7) walker version floor -----------------------------------------------------

suite "S8u (7) walker version":
  test "walker version is at least 169":
    check parseInt(symexWalkerVersion) >= 169
