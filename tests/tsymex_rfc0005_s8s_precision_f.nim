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
## RFC-0005 S8cm: part 6 of 7 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
## `tsymex_rfc0005_s8s_precision_e`, `tsymex_rfc0005_s8s_precision_g`. Split so
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

# ---- (4) variant arm field writes and positional tuple-element writes -------------
#
# Real Nim: a write to an arm field whose arm is not the active one raises
# `FieldDefect` ("field 'vb' is not accessible for type 'S8sV' using
# 'kind = s4A'"), and leaves the object unchanged. Before S8s every form here
# was `feUnsupportedStmtKind`.

type
  S8sK4 = enum s4A, s4B
  S8sV = object
    tag: int
    case kind: S8sK4
    of s4A: va: int
    of s4B: vb: int
  S8sMV = object
    case k: S8sK4
    of s4A: a: int
    of s4B: b: int
    case j: S8sK4
    of s4A: c: int
    of s4B: d: int

proc mvArmWrite(x: int) =
  var m = S8sMV(k: s4A, a: 1, j: s4B, d: 2)
  m.d = x
  m.a += 1
  if m.d == 8 and m.a == 2: symexTarget("s8s_mvw")
  if m.a != 2: symexTarget("s8s_mvw_dead")

type
  S8sHolder = object
    v: S8sV
    n: int
  S8sArmTup = object
    case kind: S8sK4
    of s4A: t: tuple[p, q: int]
    of s4B: z: int

proc plainWrite(x: int) =
  var v = S8sV(tag: 1, kind: s4B, vb: 2)
  v.tag = x
  if v.tag == 7 and v.vb == 2: symexTarget("s8s_pw")
  if v.vb != 2: symexTarget("s8s_pw_dead")

proc nestedVariant(x: int) =
  ## A variant held in an object, and a tuple held in a variant arm.
  var h = S8sHolder(v: S8sV(tag: 0, kind: s4A, va: 1), n: 3)
  h.v.va = x
  var a = S8sArmTup(kind: s4A, t: (p: 1, q: 2))
  a.t.q = x
  if h.v.va == 4 and h.n == 3 and a.t.q == 4 and a.t.p == 1:
    symexTarget("s8s_nv")
  if h.n != 3 or a.t.p != 1: symexTarget("s8s_nv_dead")

proc setVa(v: var S8sV; x: int) =
  v.va = x

proc varParamVariant(x: int) =
  var v = S8sV(tag: 2, kind: s4A, va: 0)
  setVa(v, x)
  if v.va == 9 and v.tag == 2: symexTarget("s8s_vpv")
  if v.tag != 2: symexTarget("s8s_vpv_dead")

proc tupPos(x, y: int) =
  var q = (a: 1, b: 2)
  q[0] = x
  if y > -1000 and y < 1000: q[1] += y
  if q[0] == 4 and q[1] == 7: symexTarget("s8s_tp")
  if y == 0 and q[1] != 2: symexTarget("s8s_tp_dead")

suite "S8s (4) variant arm field writes and positional tuple writes":
  test "a plain variant field write":
    let r = symexFind(plainWrite, tLabel("s8s_pw"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
    let d = symexFind(plainWrite, tLabel("s8s_pw_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a variant in an object, and a tuple in a variant arm":
    let r = symexFind(nestedVariant, tLabel("s8s_nv"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(nestedVariant, tLabel("s8s_nv_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an arm field written through a var parameter":
    let r = symexFind(varParamVariant, tLabel("s8s_vpv"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(varParamVariant, tLabel("s8s_vpv_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "arm field writes on a multi-variant":
    let r = symexFind(mvArmWrite, tLabel("s8s_mvw"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 8
    let d = symexFind(mvArmWrite, tLabel("s8s_mvw_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "positional tuple-element writes (was feUnsupportedStmtKind)":
    let r = symexFind(tupPos, tLabel("s8s_tp"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check r.witness[1] == 5
    let d = symexFind(tupPos, tLabel("s8s_tp_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
