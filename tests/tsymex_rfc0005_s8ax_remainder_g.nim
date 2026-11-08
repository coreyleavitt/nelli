## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 9 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder2`,
## `tsymex_rfc0005_s8ax_remainder3`, `tsymex_rfc0005_s8ax_remainder_b`,
## `tsymex_rfc0005_s8ax_remainder_c`, `tsymex_rfc0005_s8ax_remainder_d`,
## `tsymex_rfc0005_s8ax_remainder_e`, `tsymex_rfc0005_s8ax_remainder_f`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8ax_remainder_g")

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

# ---- (4) every signed int heap cell is Int-sorted -----------------------------
#
# S8as made the plain `int` heap Int-sorted only when every `int` parameter
# was an Int; a ranged or narrower cell stayed a bit-vector. A cell of one
# sort holding a value of the other went through `int2bv`/`bv2int` and back,
# which Z3 decides only slowly. Measured (Linux, Z3 5.1), before -> after:
# `mx_dead` 50.6 s -> 0.03 s, `rg_dead` 71.1 s -> 0.03 s, `nw_dead`
# 18.0 s -> 0.02 s; `mw_dead` and the S8an `ab_dead` shape stay under 0.02 s.
# Each cell's sort is its type's; a bit-vector stored and read back meets
# its source unconverted (`intOfBV`, and a read at the address the heap's
# last store wrote is that store's value). The rlimit below is far under
# what the slow forms needed.

type S8axBox = object
  s: range[-5000..5000]

type S8axRR = ref object
  a: int

# ---- (8) `addr` of a routine's variable is an address cell ------------------
#
# DECLINES before S8ax: `addr x` anywhere but a `let p = addr x` the alias
# rewrite took, or a `ptr` actual of a call, was `feUnsupportedExprKind`
# (CR-2a, `nnkAddr`) or `heUnsafeCast` ("unsafe pointer materialisation"):
# a pointer stored in an object, returned, compared, re-pointed on one arm,
# kept by a callee, or into a seq element. `addr x` of a routine variable
# is now a `ptr` cell that holds `x` for the frame's lifetime, with `x` kept
# equal to it after every statement. A pointer that may outlive its frame
# declines where it is dereferenced or compared; a pointer into a seq
# declines where it is used after a statement that may resize the seq.
# Every verdict probed against the compiler.

type S8axPBox = object
  p: ptr int

proc s8axGetP(x: var int): ptr int = addr x

proc s8axDangling(): ptr int =
  var y = 3
  result = addr y

type S8axPair = object
  a, b: int

proc sutAddrDangling(v: int) =
  let p = s8axDangling()
  if p[] == 3: symexTarget("ok")

proc sutAddrDeadCompare(v: int) =
  let p = s8axDangling()
  let q = s8axDangling()
  if p == q: symexTarget("ok")

proc sutAddrLostFormal(v: int) =
  var o = S8axPair(a: v, b: 0)
  let p = s8axGetP(o.a)
  p[] = 3
  if o.a == 3: symexTarget("ok")

proc sutAddrSeqElem(v: int) =
  var s = @[1, v, 3]
  let p = addr s[1]
  p[] = 9
  if s[1] == 9 and s[0] == 1: symexTarget("ok")
  if s[1] != 9 or s[0] != 1: symexTarget("bad")

proc sutAddrSeqWrite(v: int) =
  var s = @[1, v, 3]
  let p = addr s[1]
  s[1] = 4
  if p[] == 4: symexTarget("ok")
  if p[] != 4: symexTarget("bad")

proc sutAddrSeqResized(v: int) =
  var s = @[1, v, 3]
  let p = addr s[1]
  s.add 4
  if p[] == v: symexTarget("ok")

proc sutAddrIndexArr(i: int) =
  var a = [1, 2, 3]
  if i >= 0 and i < 3:
    let p = addr a[i]
    p[] = 10
    if a[1] == 10 and i == 1: symexTarget("ok")
    if (a[1] == 10) != (i == 1): symexTarget("bad")

proc sutAddrIndexSeq(i: int) =
  var s = @[1, 2, 3]
  if i >= 0 and i < 3:
    let p = addr s[i]
    p[] = 10
    if s[2] == 10 and i == 2: symexTarget("ok")
    if (s[2] == 10) != (i == 2): symexTarget("bad")

proc sutAddrIndexChecked(i: int) =
  var s = @[1, 2, 3]
  let p = addr s[i]
  if i == 1: symexTarget("ok")
  if i == 5: symexTarget("bad")

suite "RFC-0005 S8ax (8): `addr` of a routine's variable":
  test "a pointer to a returned frame's variable declines":
    pinDecline(sutAddrDangling, declKey, feUnsupportedOp, tLabel("ok"), "dereferenced here")
    pinDecline(sutAddrDeadCompare, declKey, feUnsupportedOp, tLabel("ok"), "compared here")
  test "a var formal's address bound to a field declines":
    pinDecline(sutAddrLostFormal, declKey, feUnsupportedOp, tLabel("ok"), "var` formal")
  test "the address of a seq element":
    ## RED: `heUnsafeCast` (unsafe pointer materialisation).
    verdict(sutAddrSeqElem, "ok", sxSat)
    verdict(sutAddrSeqElem, "bad", sxUnsat)
    verdict(sutAddrSeqWrite, "ok", sxSat)
    verdict(sutAddrSeqWrite, "bad", sxUnsat)
  test "a seq element's pointer used after a resize declines":
    pinDecline(sutAddrSeqResized, declKey, feUnsupportedOp, tLabel("ok"), "resize")
  test "the address of a computed index":
    ## RED: `heUnsafeCast` (unsafe pointer materialisation).
    verdict(sutAddrIndexArr, "ok", sxSat)
    verdict(sutAddrIndexArr, "bad", sxUnsat)
    verdict(sutAddrIndexSeq, "ok", sxSat)
    verdict(sutAddrIndexSeq, "bad", sxUnsat)
  test "a computed index is checked where `addr` takes it":
    verdict(sutAddrIndexChecked, "ok", sxSat)
    let r = symexFind(sutAddrIndexChecked, tLabel("bad"))
    check r.status == sxRaised

# ---- (9) two by-address arguments: a solver check of disjointness ---------
#
# DECLINES before S8ax: `setTwo(s[i], s[j])` and `setTwo(o.a1, o.a2)` (two
# fields of a variant arm) declined at parse time, the path check
# (`lvaluesDisjoint`) seeing neither a computed index nor an arm's field.
# A computed index now pairs with the other path's, and the call declines
# only on the paths where the pairs may all be equal; two arm fields are
# two locations (Nim checks the arm where it takes each address).

proc s8axSetTwo(a, b: var int) =
  a = 1
  b = 2

proc s8axSetTwoP(a, b: ptr int) =
  a[] = 1
  b[] = 2

type
  S8axK = enum skA, skB
  S8axV = object
    n: int
    case k: S8axK
    of skA:
      a1, a2: int
    of skB:
      b1: int

proc sutAliasIndex(i, j: int) =
  var s = [0, 0, 0, 0]
  if i >= 0 and i < 4 and j >= 0 and j < 4 and i != j:
    s8axSetTwo(s[i], s[j])
    if s[i] == 1 and s[j] == 2: symexTarget("ok")
    if s[i] != 1 or s[j] != 2: symexTarget("bad")

proc sutAliasIndexEq(i, j: int) =
  var s = @[0, 0, 0, 0]
  if i >= 0 and i < 4 and j >= 0 and j < 4:
    s8axSetTwo(s[i], s[j])
    if i == j and s[i] == 2: symexTarget("ok")

proc sutAliasIndexP(i: int) =
  var s = [0, 0, 0, 0]
  if i >= 0 and i < 3:
    s8axSetTwoP(addr s[i], addr s[i + 1])
    if s[i] == 1 and s[i + 1] == 2: symexTarget("ok")
    if s[i] != 1 or s[i + 1] != 2: symexTarget("bad")

proc sutAliasArm(v: int) =
  var o = S8axV(k: skA, a1: v, a2: 0)
  s8axSetTwo(o.a1, o.a2)
  if o.a1 == 1 and o.a2 == 2: symexTarget("ok")
  if o.a1 != 1 or o.a2 != 2: symexTarget("bad")

proc sutAliasArmOther(v: int) =
  var o = S8axV(k: skA, a1: v, a2: 0)
  s8axSetTwo(o.a1, o.b1)
  symexTarget("ok")

suite "RFC-0005 S8ax (9): by-address arguments that may be one location":
  test "two computed indices proven distinct":
    ## RED: `feUnsupportedOp` ("var argument write-back not modelled";
    ## the `addr` form "addr argument aliases another argument").
    verdict(sutAliasIndex, "ok", sxSat)
    verdict(sutAliasIndex, "bad", sxUnsat)
    verdict(sutAliasIndexP, "ok", sxSat)
    verdict(sutAliasIndexP, "bad", sxUnsat)
  test "two computed indices that may be equal decline":
    pinDecline(sutAliasIndexEq, declKey, feUnsupportedOp, tLabel("ok"), "one location")
  test "two fields of one variant arm":
    ## RED: `feUnsupportedOp` ("var argument write-back not modelled").
    verdict(sutAliasArm, "ok", sxSat)
    verdict(sutAliasArm, "bad", sxUnsat)
  test "fields of two arms raise where the address is taken":
    let r = symexFind(sutAliasArmOther, tLabel("ok"))
    check r.status == sxRaised
