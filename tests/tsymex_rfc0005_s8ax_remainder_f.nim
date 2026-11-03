## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 8 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder2`,
## `tsymex_rfc0005_s8ax_remainder3`, `tsymex_rfc0005_s8ax_remainder_b`,
## `tsymex_rfc0005_s8ax_remainder_c`, `tsymex_rfc0005_s8ax_remainder_d`,
## `tsymex_rfc0005_s8ax_remainder_e`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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

var gS8axP: ptr int

proc s8axSetGetP(a: var int; p: ptr int): int =
  a = 5
  p[]

proc s8axGetP(x: var int): ptr int = addr x

proc s8axKeepP(p: ptr int) = gS8axP = p

proc s8axRaiseP(p: ptr int) =
  p[] = 7
  raise newException(ValueError, "x")

proc s8axSwapP(a, b: ptr int) =
  let t = a[]
  a[] = b[]
  b[] = t

proc s8axRecP(n: int; p: ptr int) =
  var y = n
  var b = S8axPBox(p: addr y)
  if n > 0:
    s8axRecP(n - 1, b.p)
  p[] += y

type S8axPair = object
  a, b: int

proc sutAddrStored(v: int) =
  var x = v
  var b = S8axPBox(p: addr x)
  b.p[] = 6
  if x == 6: symexTarget("ok")
  if x != 6: symexTarget("bad")

proc sutAddrStoredCall(v: int) =
  var x = v
  var b = S8axPBox(p: addr x)
  let r = s8axSetGetP(x, b.p)
  if r == 5 and x == 5: symexTarget("ok")
  if r != 5 or x != 5: symexTarget("bad")

proc sutAddrReturned(v: int) =
  var x = v
  let p = s8axGetP(x)
  p[] = 7
  if x == 7: symexTarget("ok")
  if x != 7: symexTarget("bad")

proc sutAddrCompared(v: int) =
  var x = v
  var y = v
  let p = addr x
  let q = addr y
  let r = addr x
  if p == r and p != q: symexTarget("ok")
  if p == q or p != r: symexTarget("bad")

proc sutAddrBranch(c: bool) =
  var x = 1
  var y = 2
  var p = addr x
  if c: p = addr y
  p[] = 3
  if c and y == 3 and x == 1: symexTarget("ok")
  if (c and x == 3) or (not c and y == 3): symexTarget("bad")

proc sutAddrKept(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  s8axKeepP(addr x)
  x = x + 1
  if gS8axP[] == v + 1: symexTarget("ok")
  if gS8axP[] != v + 1: symexTarget("bad")

proc sutAddrRaised(v: int) =
  var x = v
  var b = S8axPBox(p: addr x)
  try:
    s8axRaiseP(b.p)
  except ValueError:
    if x == 7: symexTarget("ok")
    if x != 7: symexTarget("bad")

proc sutAddrSwap(v, w: int) =
  var x = v
  var y = w
  var bx = S8axPBox(p: addr x)
  s8axSwapP(bx.p, addr y)
  if x == w and y == v: symexTarget("ok")
  if x != w or y != v: symexTarget("bad")

proc sutAddrRec(v: int) =
  var x = 0
  var b = S8axPBox(p: addr x)
  s8axRecP(2, b.p)
  if x == 3: symexTarget("ok")
  if x != 3: symexTarget("bad")

suite "RFC-0005 S8ax (8): `addr` of a routine's variable":
  test "a pointer stored in an object":
    ## RED: `feUnsupportedExprKind` (CR-2a, `nnkAddr`).
    verdict(sutAddrStored, "ok", sxSat)
    verdict(sutAddrStored, "bad", sxUnsat)
    verdict(sutAddrStoredCall, "ok", sxSat)
    verdict(sutAddrStoredCall, "bad", sxUnsat)
  test "a pointer returned through a var formal":
    ## RED: `feUnsupportedExprKind` (CR-2a, `nnkAddr`).
    verdict(sutAddrReturned, "ok", sxSat)
    verdict(sutAddrReturned, "bad", sxUnsat)
  test "pointers compared":
    ## RED: `feUnsupportedExprKind` (CR-2a, `nnkAddr`).
    verdict(sutAddrCompared, "ok", sxSat)
    verdict(sutAddrCompared, "bad", sxUnsat)
  test "a pointer re-pointed on one arm":
    ## RED: `heUnsafeCast` (unsafe pointer materialisation).
    verdict(sutAddrBranch, "ok", sxSat)
    verdict(sutAddrBranch, "bad", sxUnsat)
  test "a pointer a callee keeps, a raise, a swap, a recursion":
    verdict(sutAddrKept, "ok", sxSat)
    verdict(sutAddrKept, "bad", sxUnsat)
    verdict(sutAddrRaised, "ok", sxSat)
    verdict(sutAddrRaised, "bad", sxUnsat)
    verdict(sutAddrSwap, "ok", sxSat)
    verdict(sutAddrSwap, "bad", sxUnsat)
    verdict(sutAddrRec, "ok", sxSat)
    verdict(sutAddrRec, "bad", sxUnsat)
