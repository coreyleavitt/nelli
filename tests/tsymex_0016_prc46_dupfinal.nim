## RFC-0016 PRC-46 -- the `=dup` sink positions PRC-45 left declining: a
## `seq` of the hooked type, a generic routine's `sink` parameter read after
## the site, a copy of a local whose two last reads are tied, and the cursor
## inference through a loop, a nested routine, a `defer` and a `try`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v

# 1. A `seq` of the hooked type at a sink position. Natively (Nim 2.2.10, c
# and cpp) its generated `=dup` runs the user hook once per element, in
# index order, and never for an empty seq.
proc dTakeSeq(x: sink seq[DObj]): int =
  for e in x: result = result * 10 + e.v
proc dTakeFirst(x: sink seq[DObj]): int =
  if x.len > 0: x[0].v else: -1
proc dTakeTS(x: sink (seq[DObj], int)): int = x[0][0].v * 10 + x[0][1].v
proc mkSeq(k: int): seq[DObj] =
  if k > 0: @[DObj(v: k)] else: @[]
proc sSeq(k: int) =
  if k > 100 or k < -100: return
  let t = @[DObj(v: k), DObj(v: 2 * k)]
  if dTakeSeq(t) * 1000 + t[0].v == 23001: symexTarget("hit")
proc sSeqNever(k: int) =
  if k > 100 or k < -100: return
  let t = @[DObj(v: k), DObj(v: 2 * k)]
  if dTakeSeq(t) * 1000 + t[0].v == 12001: symexTarget("hit")
proc sSeqLen(k: int) =
  # One element for k > 0, none otherwise: the hook runs once or never. A
  # seq of a length the walk does not know maps on the walker's axiom path,
  # which takes only an `int -> int` closure: declined there, in-band.
  if k > 100 or k < -100: return
  let t = mkSeq(k)
  if dTakeFirst(t) * 1000 + t.len == (k + 1) * 1000 + 1 and k > 0:
    symexTarget("hit")
proc sSeqLenNever(k: int) =
  if k > 100 or k < -100: return
  let t = mkSeq(k)
  if dTakeFirst(t) * 1000 + t.len == k * 1000 + 1 and k > 0: symexTarget("hit")
proc sSeqTup(k: int) =
  if k > 100 or k < -100: return
  let t = (@[DObj(v: k), DObj(v: 2 * k)], 5)
  if dTakeTS(t) * 1000 + t[1] == 23005: symexTarget("hit")

# A hook with an effect beyond its result (a global): declined.
var dupCount = 0
type DGlob = object
  v: int
proc `=dup`(x: DGlob): DGlob =
  inc dupCount
  DGlob(v: x.v + 1)
proc dTakeGSeq(x: sink seq[DGlob]): int =
  for e in x: result += e.v
proc sGlob(k: int) =
  if k > 100 or k < -100: return
  dupCount = 0
  let t = @[DGlob(v: k), DGlob(v: k)]
  if dTakeGSeq(t) + t.len + dupCount == 2 * k + 6: symexTarget("hit")

# 2. A generic routine's `sink` parameter read after the site. Natively an
# instance's `sink T` has a destructor whenever T has `tfHasAsgn` (a user
# hook of its own, or one of a field's bound before T was declared), so the
# copy runs the hook; a T declared before its field's hook has none, and its
# value moves (`isLastRead`).
type DStr = object
  v: int
  s: string
proc `=dup`(x: DStr): DStr = DStr(v: x.v + 1, s: x.s)
type DBox = object
  o: DObj
type
  DEarly = object
    o: DLate
  DLate = object
    v: int
proc `=dup`(x: DLate): DLate = DLate(v: x.v + 1)
proc tk(x: sink DObj): int = x.v
proc tk(x: sink DStr): int = x.v
proc tk(x: sink DBox): int = x.o.v
proc tk(x: sink DEarly): int = x.o.v
proc vv(x: DObj): int = x.v
proc vv(x: DStr): int = x.v
proc vv(x: DBox): int = x.o.v
proc vv(x: DEarly): int = x.o.v
proc gq[T](a: sink T): int = tk(a) * 1000 + vv(a)
proc gObj(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DObj(v: k)) == 2001: symexTarget("hit")
proc gObjNever(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DObj(v: k)) == 1001: symexTarget("hit")
proc gStr(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DStr(v: k, s: "x")) == 2001: symexTarget("hit")
proc gBox(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DBox(o: DObj(v: k))) == 2001: symexTarget("hit")
proc gBoxNever(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DBox(o: DObj(v: k))) == 1001: symexTarget("hit")
proc gEarly(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DEarly(o: DLate(v: k))) == 1001: symexTarget("hit")
proc gEarlyNever(k: int) =
  if k > 1000 or k < -1000: return
  if gq(DEarly(o: DLate(v: k))) == 2001: symexTarget("hit")

# 3. Two last reads with no node between them. Natively both orders make `b`
# a cursor: the compiler's clock gives them the same time, and its rule
# needs `a`'s strictly before `b`'s.
proc dTake2(x: sink DObj; y: DObj): int = x.v * 10 + y.v
proc dTakeR(y: DObj; x: sink DObj): int = x.v * 10 + y.v
proc tTied(k: int) =
  if k > 100 or k < -100: return
  let a = DObj(v: k)
  let b = a
  if dTake2(b, a) == 21: symexTarget("hit")
proc tTiedNever(k: int) =
  if k > 100 or k < -100: return
  let a = DObj(v: k)
  let b = a
  if dTake2(b, a) - 11 * k == 0: symexTarget("hit")
proc tTiedR(k: int) =
  if k > 100 or k < -100: return
  let a = DObj(v: k)
  let b = a
  if dTakeR(a, b) == 21: symexTarget("hit")
proc tTiedRNever(k: int) =
  if k > 100 or k < -100: return
  let a = DObj(v: k)
  let b = a
  if dTakeR(a, b) - 11 * k == 0: symexTarget("hit")

# 4. The cursor inference through a loop (walked twice; a `while` condition
# a third time), a nested routine (a captured `a` lives in the closure's
# environment, which is assigned: `b` owns; a captured `b` is read from it:
# copied), a `defer` (the rest of its scope in a `try`, its body the
# `finally`) and a `try` (its tree in order). Each value is natively k = 1's.
proc l1(k: int): int =       # b declared in the loop: owned, moved
  let a = DObj(v: k)
  for i in 0 ..< 2:
    let b = a
    result += dTake(b)
proc l2(k: int): int =       # b before the loop, its site in it
  let a = DObj(v: k)
  let b = a
  for i in 0 ..< 2:
    result += dTake(b)
proc l3(k: int): int =       # a read in the loop after the site
  let a = DObj(v: k)
  let b = a
  for i in 0 ..< 2:
    result += dTake(b) * 10 + a.v
proc l4(k: int): int =       # a read in a loop before b
  let a = DObj(v: k)
  for i in 0 ..< 2:
    result += a.v
  let b = a
  result += dTake(b) * 100
proc l5(k: int): int =       # b in a `while`, a read after it: a cursor
  let a = DObj(v: k)
  var i = 0
  while i < 2:
    let b = a
    result += dTake(b)
    inc i
  result += a.v * 100
proc l6(k: int): int =       # a read in a loop after the site
  let a = DObj(v: k)
  let b = a
  result = dTake(b) * 100
  for i in 0 ..< 2:
    result += a.v
proc l7(k: int): int =       # a read in a `while` condition
  let a = DObj(v: k)
  let b = a
  var i = 0
  result = dTake(b) * 100
  while i < a.v:
    inc i
proc l8(k: int): int =       # b declared under an `if` in a loop: owned
  let a = DObj(v: k)
  for i in 0 ..< 2:
    if k > 0:
      let b = a
      result += dTake(b)
  result += a.v * 100
proc l9(k: int): int =       # a declared in the loop: owned
  for i in 0 ..< 2:
    let a = DObj(v: k)
    let b = a
    result += dTake(b) * 100 + a.v
proc n1(k: int): int =       # a captured: owned
  let a = DObj(v: k)
  let b = a
  result = dTake(b) * 100
  proc inner(): int = a.v
  result += inner()
proc n2(k: int): int =       # b captured: copied
  let a = DObj(v: k)
  let b = a
  proc inner(): int = b.v
  result = dTake(b) * 100 + inner() * 10 + a.v
proc n3(k: int): int =       # a nested routine capturing neither
  let a = DObj(v: k)
  let b = a
  proc inner(x: int): int = x + 1
  result = dTake(b) * 100 + inner(a.v)
proc d1(k: int): int =       # a read in a `defer`
  var r = 0
  block:
    let a = DObj(v: k)
    let b = a
    defer: r += a.v
    r = dTake(b) * 100
  r
proc d2(k: int): int =       # b read in a `defer`: owned, read after the site
  var r = 0
  block:
    let a = DObj(v: k)
    let b = a
    defer: r += b.v
    r = dTake(b) * 100 + a.v
  r
proc d3(k: int): int =       # a `defer` reading neither
  var r = 0
  block:
    let a = DObj(v: k)
    let b = a
    defer: r += 5
    r = dTake(b) * 100 + a.v
  r
proc mayRaise(k: int) =
  if k == 99: raise newException(ValueError, "x")
proc t1(k: int): int =       # a read in an `except` branch
  let a = DObj(v: k)
  let b = a
  try:
    result = dTake(b) * 100
    mayRaise(k)
  except ValueError:
    result = a.v
proc t2(k: int): int =       # a read in a `finally`
  let a = DObj(v: k)
  let b = a
  try:
    result = dTake(b) * 100
  finally:
    result += a.v
proc t3(k: int): int =       # a read after the `try`
  let a = DObj(v: k)
  let b = a
  try:
    result = dTake(b) * 100
    mayRaise(k)
  except ValueError:
    result = 7
  result += a.v
proc t4(k: int): int =       # a read before the site, nothing after: owned
  let a = DObj(v: k)
  let b = a
  try:
    result = a.v
    result += dTake(b) * 100
  except ValueError:
    result = 7

# Each entry: `hit` holds only with the native count of hooks.
proc eL1(k: int) =
  if k > 50 or k < -50: return
  if l1(k) == 2 * k: symexTarget("hit")
proc eL1Never(k: int) =
  if k > 50 or k < -50: return
  if l1(k) == 2 * k + 2: symexTarget("hit")
proc eL2(k: int) =
  if k > 50 or k < -50: return
  if l2(k) == 2 * k + 2: symexTarget("hit")
proc eL2Never(k: int) =
  if k > 50 or k < -50: return
  if l2(k) == 2 * k: symexTarget("hit")
proc eL3(k: int) =
  if k > 50 or k < -50: return
  if l3(k) == 22 * k + 20: symexTarget("hit")
proc eL3Never(k: int) =
  if k > 50 or k < -50: return
  if l3(k) == 22 * k: symexTarget("hit")
proc eL4(k: int) =
  if k > 50 or k < -50: return
  if l4(k) == 102 * k: symexTarget("hit")
proc eL4Never(k: int) =
  if k > 50 or k < -50: return
  if l4(k) == 102 * k + 100: symexTarget("hit")
proc eL5(k: int) =
  if k > 50 or k < -50: return
  if l5(k) == 102 * k + 2: symexTarget("hit")
proc eL5Never(k: int) =
  if k > 50 or k < -50: return
  if l5(k) == 102 * k: symexTarget("hit")
proc eL6(k: int) =
  if k > 50 or k < -50: return
  if l6(k) == 102 * k + 100: symexTarget("hit")
proc eL6Never(k: int) =
  if k > 50 or k < -50: return
  if l6(k) == 102 * k: symexTarget("hit")
proc eL7(k: int) =
  if k > 3 or k < 0: return
  if l7(k) == 100 * k + 100: symexTarget("hit")
proc eL7Never(k: int) =
  if k > 3 or k < 0: return
  if l7(k) == 100 * k: symexTarget("hit")
proc eL8(k: int) =
  if k > 50 or k < 1: return
  if l8(k) == 102 * k: symexTarget("hit")
proc eL8Never(k: int) =
  if k > 50 or k < 1: return
  if l8(k) == 102 * k + 2: symexTarget("hit")
proc eL9(k: int) =
  if k > 50 or k < -50: return
  if l9(k) == 202 * k: symexTarget("hit")
proc eL9Never(k: int) =
  if k > 50 or k < -50: return
  if l9(k) == 202 * k + 200: symexTarget("hit")
proc eN1(k: int) =
  if k > 50 or k < -50: return
  if n1(k) == 101 * k: symexTarget("hit")
proc eN1Never(k: int) =
  if k > 50 or k < -50: return
  if n1(k) == 101 * k + 100: symexTarget("hit")
proc eN2(k: int) =
  if k > 50 or k < -50: return
  if n2(k) == 111 * k + 100: symexTarget("hit")
proc eN2Never(k: int) =
  if k > 50 or k < -50: return
  if n2(k) == 111 * k: symexTarget("hit")
proc eN3(k: int) =
  if k > 50 or k < -50: return
  if n3(k) == 101 * k + 101: symexTarget("hit")
proc eN3Never(k: int) =
  if k > 50 or k < -50: return
  if n3(k) == 101 * k + 1: symexTarget("hit")
proc eD1(k: int) =
  if k > 50 or k < -50: return
  if d1(k) == 101 * k + 100: symexTarget("hit")
proc eD1Never(k: int) =
  if k > 50 or k < -50: return
  if d1(k) == 101 * k: symexTarget("hit")
proc eD2(k: int) =
  if k > 50 or k < -50: return
  if d2(k) == 102 * k + 100: symexTarget("hit")
proc eD2Never(k: int) =
  if k > 50 or k < -50: return
  if d2(k) == 102 * k: symexTarget("hit")
proc eD3(k: int) =
  if k > 50 or k < -50: return
  if d3(k) == 101 * k + 105: symexTarget("hit")
proc eD3Never(k: int) =
  if k > 50 or k < -50: return
  if d3(k) == 101 * k + 5: symexTarget("hit")
proc eT1(k: int) =
  if k > 50 or k < -50: return
  if t1(k) == 100 * k + 100: symexTarget("hit")
proc eT1Never(k: int) =
  if k > 50 or k < -50: return
  if t1(k) == 100 * k: symexTarget("hit")
proc eT2(k: int) =
  if k > 50 or k < -50: return
  if t2(k) == 101 * k + 100: symexTarget("hit")
proc eT2Never(k: int) =
  if k > 50 or k < -50: return
  if t2(k) == 101 * k: symexTarget("hit")
proc eT3(k: int) =
  if k > 50 or k < -50: return
  if t3(k) == 101 * k + 100: symexTarget("hit")
proc eT3Never(k: int) =
  if k > 50 or k < -50: return
  if t3(k) == 101 * k: symexTarget("hit")
proc eT4(k: int) =
  if k > 50 or k < -50: return
  if t4(k) == 101 * k: symexTarget("hit")
proc eT4Never(k: int) =
  if k > 50 or k < -50: return
  if t4(k) == 101 * k + 100: symexTarget("hit")

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

suite "PRC-46":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 424

  test "a seq of the hooked type runs the hook once per element":
    check native(sSeq(1)) == "hit"
    check native(sSeqLen(1)) == "hit"
    check native(sSeqTup(1)) == "hit"
    exact(sSeq, sSeqNever)
    check pinExact(sSeqTup, dCell, domain = idom).status == sxSat
    pinDecline(sSeqLen, dCell, ceUnsupportedHof, needle = "map axiom path")
    pinDecline(sSeqLenNever, dCell, ceUnsupportedHof, needle = "map axiom path")

  test "a hook with an effect beyond its result declines over a seq":
    check native(sGlob(1)) == "hit"
    pinDecline(sGlob, dCell, feGlobalRouteUnproved, needle = "=dup")

  test "a generic routine's sink parameter read after the site":
    check native(gObj(1)) == "hit"
    check native(gStr(1)) == "hit"
    check native(gBox(1)) == "hit"
    check native(gEarly(1)) == "hit"
    exact(gObj, gObjNever)
    check pinExact(gStr, dCell, domain = idom).status == sxSat
    exact(gBox, gBoxNever)
    exact(gEarly, gEarlyNever)

  test "two last reads with no node between them: a cursor":
    check native(tTied(1)) == "hit"
    check native(tTiedR(1)) == "hit"
    exact(tTied, tTiedNever)
    exact(tTiedR, tTiedRNever)

  test "the cursor inference through a loop":
    check native(eL1(1)) == "hit"
    check native(eL2(1)) == "hit"
    check native(eL3(1)) == "hit"
    check native(eL4(1)) == "hit"
    check native(eL5(1)) == "hit"
    check native(eL6(1)) == "hit"
    check native(eL7(1)) == "hit"
    check native(eL8(1)) == "hit"
    check native(eL9(1)) == "hit"
    exact(eL1, eL1Never)
    exact(eL2, eL2Never)
    exact(eL3, eL3Never)
    exact(eL4, eL4Never)
    exact(eL5, eL5Never)
    exact(eL6, eL6Never)
    exact(eL7, eL7Never)
    exact(eL8, eL8Never)
    exact(eL9, eL9Never)

  test "the cursor inference through a nested routine":
    check native(eN1(1)) == "hit"
    check native(eN2(1)) == "hit"
    check native(eN3(1)) == "hit"
    exact(eN1, eN1Never)
    exact(eN2, eN2Never)
    exact(eN3, eN3Never)

  test "the cursor inference through a defer":
    check native(eD1(1)) == "hit"
    check native(eD2(1)) == "hit"
    check native(eD3(1)) == "hit"
    exact(eD1, eD1Never)
    exact(eD2, eD2Never)
    exact(eD3, eD3Never)

  test "the cursor inference through a try":
    check native(eT1(1)) == "hit"
    check native(eT2(1)) == "hit"
    check native(eT3(1)) == "hit"
    check native(eT4(1)) == "hit"
    exact(eT1, eT1Never)
    exact(eT2, eT2Never)
    exact(eT3, eT3Never)
    exact(eT4, eT4Never)
