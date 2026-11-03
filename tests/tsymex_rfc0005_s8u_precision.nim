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
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8u_precision_b`, `tsymex_rfc0005_s8u_precision_c`. Split so
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

# ---- (1) a constructor naming an else-covered tag ---------------------------------

type
  S8uK = enum u3A, u3B, u3C
  S8uVE = object
    case vk: S8uK
    of u3C: vc: int
    else: ve: int

proc elseCtor(x: int) =
  let v = S8uVE(vk: u3B, ve: x)
  if v.ve == 4 and v.vk == u3B: symexTarget("s8u_ec")
  if v.vk != u3B: symexTarget("s8u_ec_dead")

suite "S8u (1) a constructor naming an else-covered tag":
  test "oracle":
    symexCaptureBegin()
    elseCtor(4)
    let hits = symexCaptureEnd()
    check "s8u_ec" in hits

  test "an else-covered tag's constructor (was feUnsupportedExprKind)":
    let r = symexFind(elseCtor, tLabel("s8u_ec"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 4
    expectUnsat(symexFind(elseCtor, tLabel("s8u_ec_dead")))

# ---- (2) a callee building a local Table / HashSet --------------------------------

proc mkTable(n: int): Table[string, int] =
  var t: Table[string, int]
  t["a"] = n
  result = t

proc callTable(n: int) =
  let t = mkTable(n)
  if t["a"] == 5: symexTarget("s8u_tbl")
  if t["a"] != n: symexTarget("s8u_tbl_dead")

proc mkSet(n: int): HashSet[int] =
  var s: HashSet[int]
  s.incl n
  result = s

proc callSet(n: int) =
  let s = mkSet(n)
  if 3 in s: symexTarget("s8u_set")
  if s.len != 1: symexTarget("s8u_set_dead")

proc mkIntTable(n: int): Table[(int, int), int] =
  ## A shape the table theory does not back: still declined, now in-band --
  ## the RFC-0005 S8u scoped decline. RFC-0005 S8ar backs an integer key
  ## (this was `Table[int, int]`) and S8at a float one (then
  ## `Table[float, int]`); a tuple key is still unbacked.
  var t: Table[(int, int), int]
  t[(1, 1)] = n
  result = t

proc callIntTable(n: int) =
  let t = mkIntTable(n)
  if t[(1, 1)] == 5: symexTarget("s8u_itbl")

suite "S8u (2) a callee building a local Table / HashSet":
  test "oracle":
    symexCaptureBegin()
    callTable(5); callSet(3); callIntTable(5)
    let hits = symexCaptureEnd()
    check "s8u_tbl" in hits
    check "s8u_set" in hits
    check "s8u_itbl" in hits

  test "a local Table (was weInternalWalkerFault)":
    let r = symexFind(callTable, tLabel("s8u_tbl"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 5
    expectUnsat(symexFind(callTable, tLabel("s8u_tbl_dead")))

  test "a local HashSet (was weInternalWalkerFault)":
    let r = symexFind(callSet, tLabel("s8u_set"))
    expectSat(r)
    if r.status == sxSat: check r.witness[0] == 3
    expectUnsat(symexFind(callSet, tLabel("s8u_set_dead")))

  test "an unbacked Table[(int, int), int] declines in-band, never a walker fault":
    let r = symexFind(callIntTable, tLabel("s8u_itbl"))
    checkpoint($r.status & " " & show(r.errors))
    for e in r.errors: check e.kind != weInternalWalkerFault
    check r.status != sxUnsat
    check r.errors.len > 0

# ---- (3) a callee allocating its ref result with new(result) ----------------------

type S8uNode = ref object
  v: int
  w: int

type S8uBag = object
  n: int
  s: HashSet[int]
  t: Table[string, int]
