## RFC-0005 (soundness channels) slice S8bo -- S8be's remainder: address
## cells. A plain object's cell, a whole-seq assignment as a resize, an arm
## field's pointer as a value, element cells over seqs of objects.
##
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8bo_cells")

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

# ---- (2) a plain object's address cell ---------------------------------------
#
# DECLINE before S8bo: `addr o` of a plain object was a cell over one heap
# of the whole object, while a field read or write through the pointer
# (`bx.p.a`) used the field-split heaps a `ref` object lives in: the two
# clashed (`seUnsupportedCompoundSortLeaf`), and every target was
# `sxUnknown`. A whole `p[]` read or write of an object pointee likewise.

type
  S8boP = object
    a: int
    b: int
  S8boBox = object
    p: ptr S8boP
  S8boRP = ref S8boP

proc sutObjStored(v: int) =
  var o = S8boP(a: v, b: 2)
  var bx = S8boBox(p: addr o)
  bx.p.a = 9
  if o.a == 9 and o.b == 2: symexTarget("ok")
  if o.a != 9 or o.b != 2: symexTarget("bad")

proc sutObjStoredRead(v: int) =
  var o = S8boP(a: v, b: 2)
  var bx = S8boBox(p: addr o)
  o.b = 5
  if bx.p.b == 5 and bx.p.a == v: symexTarget("ok")
  if bx.p.b != 5: symexTarget("bad")

proc s8boSetA(q: ptr S8boP) = q.a = 7

proc sutObjPassed(v: int) =
  var o = S8boP(a: v, b: 2)
  s8boSetA(addr o)
  if o.a == 7: symexTarget("ok")
  if o.a != 7: symexTarget("bad")

proc sutObjDerefWrite(v: int) =
  var o = S8boP(a: v, b: 2)
  var bx = S8boBox(p: addr o)
  bx.p[] = S8boP(a: 1, b: 1)
  if o.a == 1 and o.b == 1: symexTarget("ok")
  if o.a != 1: symexTarget("bad")

proc sutObjDerefRead(v: int) =
  var o = S8boP(a: v, b: 2)
  var bx = S8boBox(p: addr o)
  let c = bx.p[]
  if c.a == v and c.b == 2: symexTarget("ok")
  if c.a != v or c.b != 2: symexTarget("bad")

proc sutRefWhole(v: int) =
  var r = S8boRP(a: v, b: 2)
  r[] = S8boP(a: 4, b: v)
  let c = r[]
  if r.a == 4 and c.b == v: symexTarget("ok")
  if r.a != 4 or c.b != v: symexTarget("bad")

# ---- (3) a whole assignment of a seq kills its element cells ----------------
#
# WRONG VERDICT before S8bo: a whole assignment kept the cells of `addr
# s[i]` live when the seq's value term did not change: a callee's `s = t`
# repeating the value the seq already held (here, the second call), or
# `s = t` after `let t = s`. Nim's assignment frees the old data and points
# the seq at another block whatever it copies, so the pointer dangles (UB),
# and the read through it was a confirmed `sxSat`. Now any write of the seq
# by name kills its cells, and the dereference declines.

type S8boPBox = object
  p: ptr int

proc s8boReFrom(s: var seq[int]; t: seq[int]) = s = t

proc sutSeqCalleeSame(v: int) =
  var s = @[1, v, 3]
  s8boReFrom(s, @[4, 5, 6])
  var b = S8boPBox(p: addr s[1])
  s8boReFrom(s, @[4, 5, 6])
  if b.p[] == 5: symexTarget("ok")

proc sutSeqLocalSame(v: int) =
  var s = @[1, v, 3]
  var b = S8boPBox(p: addr s[1])
  let t = s
  s = t
  if b.p[] == v: symexTarget("ok")

# ---- (4) an arm field's address as a value ----------------------------------
#
# DECLINE before S8bo: `addr o.a` of a case object's arm field whose
# pointer may escape (stored in an object, passed to a routine that keeps
# it) was `heUnsafeCast`, every target `sxUnknown`. It is now the field's
# cell, kept equal to the field until the object may change arm; a
# dereference after that declines (the pointer names another arm's memory).

type
  S8boK = enum kA, kB
  S8boV = object
    case k: S8boK
    of kA: a: int
    of kB: b: int
  S8boIBox = object
    p: ptr int

proc sutArmStored(v: int) =
  var o = S8boV(k: kA, a: v)
  var bx = S8boIBox(p: addr o.a)
  bx.p[] = 5
  if o.a == 5: symexTarget("ok")
  if o.a != 5: symexTarget("bad")

proc sutArmStoredRead(v: int) =
  symexAssume(v > -100 and v < 100)
  var o = S8boV(k: kA, a: v)
  var bx = S8boIBox(p: addr o.a)
  o.a = v + 1
  if bx.p[] == v + 1: symexTarget("ok")
  if bx.p[] != v + 1: symexTarget("bad")

proc s8boKeep(b: var S8boIBox; p: ptr int) = b.p = p

proc sutArmPassed(v: int) =
  symexAssume(v > -100 and v < 100)
  var o = S8boV(k: kA, a: v)
  var bx: S8boIBox
  s8boKeep(bx, addr o.a)
  bx.p[] = bx.p[] + 1
  if o.a == v + 1: symexTarget("ok")
  if o.a != v + 1: symexTarget("bad")

proc sutArmSameArm(v: int) =
  var o = S8boV(k: kA, a: v)
  var bx = S8boIBox(p: addr o.a)
  o = S8boV(k: kA, a: 3)
  if bx.p[] == 3: symexTarget("ok")
  if bx.p[] != 3: symexTarget("bad")

proc sutArmRearm(v: int) =
  var o = S8boV(k: kA, a: v)
  var bx = S8boIBox(p: addr o.a)
  o = S8boV(k: kB, b: 3)
  if bx.p[] == 3: symexTarget("ok")

proc sutArmWrongArm(v: int) =
  var o = S8boV(k: kB, b: v)
  var bx = S8boIBox(p: addr o.a)
  discard bx

# ---- (5) an element cell over a seq of objects -------------------------------
#
# Before S8bo `addr s[i]` of a seq of objects had no cell at all
# (`feUnsupportedExprKind` on the `addr`). It is an element cell now, whose
# value is the object's field-split heaps (2), kept equal to the seq's
# leaf-split element (S8bc; RFC-0005 S8cb reconciled the two: S8bo's own
# base held no element of such a seq).

type
  S8boOBox = object
    p: ptr S8boP
  S8boNamed = object
    name: string
    n: int
  S8boNBox = object
    p: ptr S8boNamed

proc sutSeqObjCell(v: int) =
  var s = @[S8boP(a: 1, b: 2), S8boP(a: v, b: 3)]
  var bx = S8boOBox(p: addr s[1])
  bx.p.a = 9
  if bx.p.a == 9 and s[1].a == 9 and s[1].b == 3 and s[0].a == 1:
    symexTarget("ok")
  if bx.p.a != 9 or s[1].a != 9 or s[1].b != 3 or s[0].a != 1:
    symexTarget("bad")

proc sutSeqObjWholeByName(v: int) =
  var s = @[S8boP(a: 1, b: 2), S8boP(a: 0, b: 3)]
  var bx = S8boOBox(p: addr s[1])
  s[1] = S8boP(a: v, b: 4)
  if bx.p.a == v and bx.p.b == 4: symexTarget("ok")
  if bx.p.a != v or bx.p.b != 4: symexTarget("bad")

proc sutSeqObjWholeThrough(v: int) =
  var s = @[S8boP(a: 1, b: 2), S8boP(a: 0, b: 3)]
  var bx = S8boOBox(p: addr s[1])
  bx.p[] = S8boP(a: v, b: 5)
  if s[1].a == v and s[1].b == 5 and s[0].b == 2: symexTarget("ok")
  if s[1].a != v or s[1].b != 5 or s[0].b != 2: symexTarget("bad")

proc sutSeqObjRaises(i: int) =
  var s = @[S8boP(a: 1, b: 2)]
  var bx = S8boOBox(p: addr s[i])
  discard bx

proc sutSeqObjSymIndex(i: int) =
  if i < 0 or i > 1: return
  var s = @[S8boP(a: 1, b: 2), S8boP(a: 3, b: 4)]
  var bx = S8boOBox(p: addr s[i])
  bx.p.a = 9
  if s[0].a == 9 and s[1].a == 3: symexTarget("zero")
  if s[0].a == 9 and s[1].a == 9: symexTarget("both")

proc s8boSetB(q: ptr S8boP) =
  q.b = 11

proc sutSeqObjPassed(v: int) =
  var s = @[S8boP(a: v, b: 2)]
  var bx = S8boOBox(p: addr s[0])
  s8boSetB(bx.p)
  if s[0].b == 11 and s[0].a == v: symexTarget("ok")
  if s[0].b != 11 or s[0].a != v: symexTarget("bad")

proc sutSeqObjResized(v: int) =
  var s = @[S8boP(a: v, b: 2)]
  var bx = S8boOBox(p: addr s[0])
  s.add S8boP(a: 0, b: 0)
  if bx.p.a == v: symexTarget("ok")

proc sutSeqNamedCell(v: int) =
  var s = @[S8boNamed(name: "x", n: v)]
  var bx = S8boNBox(p: addr s[0])
  bx.p.name = "y"
  if s[0].name == "y" and s[0].n == v: symexTarget("ok")
  if s[0].name != "y" or s[0].n != v: symexTarget("bad")

suite "RFC-0005 S8bo: walker version":
  test "symexWalkerVersion is at least 216":
    check parseInt(symexWalkerVersion) >= 216

suite "RFC-0005 S8bo (2): a plain object's address cell":
  test "stored in another object, written through it":
    verdict(sutObjStored, tLabel("ok"), sxSat)
    verdict(sutObjStored, tLabel("bad"), sxUnsat)
  test "stored in another object, a write by name seen through it":
    verdict(sutObjStoredRead, tLabel("ok"), sxSat)
    verdict(sutObjStoredRead, tLabel("bad"), sxUnsat)
  test "passed to a routine writing a field":
    verdict(sutObjPassed, tLabel("ok"), sxSat)
    verdict(sutObjPassed, tLabel("bad"), sxUnsat)
  test "the whole object written through the pointer":
    verdict(sutObjDerefWrite, tLabel("ok"), sxSat)
    verdict(sutObjDerefWrite, tLabel("bad"), sxUnsat)
  test "the whole object read through the pointer":
    verdict(sutObjDerefRead, tLabel("ok"), sxSat)
    verdict(sutObjDerefRead, tLabel("bad"), sxUnsat)
  test "a ref object read and written whole":
    verdict(sutRefWhole, tLabel("ok"), sxSat)
    verdict(sutRefWhole, tLabel("bad"), sxUnsat)

suite "RFC-0005 S8bo (3): a whole seq assignment is a resize":
  test "a callee assigning the value the seq holds":
    pinDecline(sutSeqCalleeSame, declKey, feUnsupportedOp, tLabel("ok"), "freed")
  test "an assignment of an equal value by name":
    pinDecline(sutSeqLocalSame, declKey, feUnsupportedOp, tLabel("ok"), "freed")

suite "RFC-0005 S8bo (4): an arm field's address as a value":
  test "stored in another object, written through it":
    verdict(sutArmStored, tLabel("ok"), sxSat)
    verdict(sutArmStored, tLabel("bad"), sxUnsat)
  test "stored, a write by name seen through it":
    verdict(sutArmStoredRead, tLabel("ok"), sxSat)
    verdict(sutArmStoredRead, tLabel("bad"), sxUnsat)
  test "passed to a routine that keeps it":
    verdict(sutArmPassed, tLabel("ok"), sxSat)
    verdict(sutArmPassed, tLabel("bad"), sxUnsat)
  test "the object assigned whole in the same arm":
    verdict(sutArmSameArm, tLabel("ok"), sxSat)
    verdict(sutArmSameArm, tLabel("bad"), sxUnsat)
  test "after the object changes arm, a dereference declines":
    pinDecline(sutArmRearm, declKey, feUnsupportedOp, tLabel("ok"), "changed arm")
  test "the arm is checked where `addr` takes the field":
    verdict(sutArmWrongArm, tRaisedExn("FieldDefect"), sxRaised)

suite "RFC-0005 S8bo (5): an element cell over a seq of objects":
  test "stored in another object, written through it":
    verdict(sutSeqObjCell, tLabel("ok"), sxSat)
    verdict(sutSeqObjCell, tLabel("bad"), sxUnsat)
  test "the element written whole by name, seen through it":
    verdict(sutSeqObjWholeByName, tLabel("ok"), sxSat)
    verdict(sutSeqObjWholeByName, tLabel("bad"), sxUnsat)
  test "the element written whole through it":
    verdict(sutSeqObjWholeThrough, tLabel("ok"), sxSat)
    verdict(sutSeqObjWholeThrough, tLabel("bad"), sxUnsat)
  test "at a symbolic index, which is checked where `addr` takes it":
    verdict(sutSeqObjSymIndex, tLabel("zero"), sxSat)
    verdict(sutSeqObjSymIndex, tLabel("both"), sxUnsat)
    verdict(sutSeqObjRaises, tRaisedExn("IndexDefect"), sxRaised)
  test "passed to a routine writing a field":
    verdict(sutSeqObjPassed, tLabel("ok"), sxSat)
    verdict(sutSeqObjPassed, tLabel("bad"), sxUnsat)
  test "after a resize, a dereference declines":
    pinDecline(sutSeqObjResized, declKey, feUnsupportedOp, tLabel("ok"), "freed")
  test "an object holding a string":
    verdict(sutSeqNamedCell, tLabel("ok"), sxSat)
    verdict(sutSeqNamedCell, tLabel("bad"), sxUnsat)
