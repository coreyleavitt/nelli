## RFC-0005 (soundness channels) slice S8be -- S8ax's remainder.
##
## Items (12)-(13); (1)-(8) are in `tsymex_rfc0005_s8be_remainder`, (9)-(11)
## in `tsymex_rfc0005_s8be_remainder_b`
## (RFC-0005 S8bo split the suite, which took 83 s to compile and run).
##
## Each section below names the wrong verdict, the crash or the decline it
## closes. Every expected value was probed against the real compiler (Nim
## 2.2.10, the debug build the test binary itself is).
import std/[unittest, strutils, os]
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

template verdict(fn: typed, tgt: SymexTarget, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template verdictS(fn: typed, tgt: SymexTarget, want: SymexStatusKind,
                  s: SymexSettings) =
  block:
    let r = symexFind(fn, tgt, s)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template declines(fn: typed, tgt: SymexTarget, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (12) an element's address as a value; a case object's address ----------
#
# DECLINE before S8be: `addr s[i]` of a seq whose pointer is compared,
# stored, returned, or whose index variable is reassigned while it lives
# (`feUnsupportedExprKind`, `heUnsafeCast`); `addr o` of a case object
# (`feUnsupportedOp`); `addr o.a` of an arm field (`heUnsafeCast`). The
# element's cell is identified by the seq and the index as `addr`
# evaluated it, and dies when the seq is resized (Nim may move it).

proc sutElemPtrCompare(v: int) =
  var s = @[1, v, 3]
  let p = addr s[1]
  let q = addr s[1]
  let r = addr s[0]
  if p == q and p != r: symexTarget("ok")
  if p != q or p == r: symexTarget("bad")

proc s8beRetP(p: ptr int): ptr int = p

proc sutElemPtrReturned(v: int) =
  var s = @[1, v, 3]
  let p = s8beRetP(addr s[1])
  p[] = 9
  if s[1] == 9: symexTarget("ok")
  if s[1] != 9: symexTarget("bad")

type S8bePBox = object
  p: ptr int

proc sutElemPtrStored(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  b.p[] = 9
  if s[1] == 9: symexTarget("ok")
  if s[1] != 9: symexTarget("bad")

proc sutElemPtrIdxMoved(v: int) =
  var s = @[1, v, 3]
  var i = 1
  let p = addr s[i]
  i = 2
  p[] = 9
  if s[1] == 9 and s[2] == 3: symexTarget("ok")
  if s[1] != 9 or s[2] != 3: symexTarget("bad")

proc sutElemPtrIdxMovedCmp(v: int) =
  var s = @[1, v, 3]
  var i = 1
  let p = addr s[i]
  i = 2
  let q = addr s[i]
  if p != q: symexTarget("ok")
  if p == q: symexTarget("bad")

proc sutElemPtrWriteBack(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  s[1] = 4
  if b.p[] == 4: symexTarget("ok")
  if b.p[] != 4: symexTarget("bad")

proc s8beRetElem(s: var seq[int]; i: int): ptr int = addr s[i]

proc sutElemPtrFromCallee(v: int) =
  var s = @[1, v, 3]
  let p = s8beRetElem(s, 2)
  p[] = 9
  if s[2] == 9: symexTarget("ok")
  if s[2] != 9: symexTarget("bad")

proc sutElemPtrResized(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  s.add 4
  b.p[] = 9
  if s[1] == 9: symexTarget("ok")

proc sutElemPtrOob(i: int) =
  var s = @[1, 2, 3]
  symexAssume(i >= 3 and i < 10)
  var b = S8bePBox(p: addr s[i])
  discard b

type
  S8beK = enum kA, kB
  S8beV = object
    case k: S8beK
    of kA: a: int
    of kB: b: int

proc s8beSetV(p: ptr S8beV) =
  p.a = 7

proc sutVariantAddrCall(v: int) =
  var o = S8beV(k: kA, a: v)
  s8beSetV(addr o)
  if o.a == 7: symexTarget("ok")
  if o.a != 7: symexTarget("bad")

proc sutVariantFieldAddr(v: int) =
  var o = S8beV(k: kA, a: v)
  let p = addr o.a
  p[] = 5
  if o.a == 5: symexTarget("ok")
  if o.a != 5: symexTarget("bad")

proc sutVariantFieldRearm(v: int) =
  var o = S8beV(k: kA, a: v)
  let p = addr o.a
  o = S8beV(k: kB, b: 3)
  if p[] == 3: symexTarget("ok")

# ---- (13) the call-depth decline names its budget ----------------------------

proc s8beDown(k: int): bool =
  if k <= 0: true else: s8beDown(k - 1)

proc sutDownFree(n: int) =
  if s8beDown(n) and n == 50: symexTarget("dd")

suite "RFC-0005 S8be: walker version":
  test "symexWalkerVersion is at least 205":
    check parseInt(symexWalkerVersion) >= 205

suite "RFC-0005 S8be (12): an element's address as a value":
  test "compared":
    verdict(sutElemPtrCompare, tLabel("ok"), sxSat)
    verdict(sutElemPtrCompare, tLabel("bad"), sxUnsat)
  test "returned through a callee":
    verdict(sutElemPtrReturned, tLabel("ok"), sxSat)
    verdict(sutElemPtrReturned, tLabel("bad"), sxUnsat)
  test "stored in an object":
    verdict(sutElemPtrStored, tLabel("ok"), sxSat)
    verdict(sutElemPtrStored, tLabel("bad"), sxUnsat)
  test "a write by name seen through the pointer":
    verdict(sutElemPtrWriteBack, tLabel("ok"), sxSat)
    verdict(sutElemPtrWriteBack, tLabel("bad"), sxUnsat)
  test "the index variable reassigned while the pointer lives":
    verdict(sutElemPtrIdxMoved, tLabel("ok"), sxSat)
    verdict(sutElemPtrIdxMoved, tLabel("bad"), sxUnsat)
    verdict(sutElemPtrIdxMovedCmp, tLabel("ok"), sxSat)
    verdict(sutElemPtrIdxMovedCmp, tLabel("bad"), sxUnsat)
  test "taken by a callee of its var formal":
    verdict(sutElemPtrFromCallee, tLabel("ok"), sxSat)
    verdict(sutElemPtrFromCallee, tLabel("bad"), sxUnsat)
  test "used after a resize declines":
    declines(sutElemPtrResized, tLabel("ok"), feUnsupportedOp, "S8be")
  test "the index is checked where `addr` takes it":
    verdict(sutElemPtrOob, tRaisedExn("IndexDefect"), sxRaised)

suite "RFC-0005 S8be (12): a case object's address":
  test "passed to a routine writing an arm field":
    verdict(sutVariantAddrCall, tLabel("ok"), sxSat)
    verdict(sutVariantAddrCall, tLabel("bad"), sxUnsat)
  test "an arm field's address":
    verdict(sutVariantFieldAddr, tLabel("ok"), sxSat)
    verdict(sutVariantFieldAddr, tLabel("bad"), sxUnsat)
  test "an arm field's pointer after the object changes arm declines":
    declines(sutVariantFieldRearm, tLabel("ok"), feUnsupportedOp, "another arm")

suite "RFC-0005 S8be (13): the call-depth decline":
  test "names the budget":
    let r = symexFind(sutDownFree, tLabel("dd"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check "maxCallDepth" in show(r.errors)
