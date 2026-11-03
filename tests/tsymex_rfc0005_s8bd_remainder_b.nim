## RFC-0005 (soundness channels) slice S8bd -- S8ba's remainder.
##
## Pinned here (the RFC's "As landed (S8bd)" note has the design and the
## measurements):
##   (1) a string index `i` that is a bit-vector, compared with `s.len`
##       both as itself and as `i + 1`, decides: the two Int views of `i`
##       and `i + 1` are linked by an exact theorem of two's complement
##       (`bvOffsetLinks`). It ran ~41M units to `sxUnknown`;
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bd_remainder`, `tsymex_rfc0005_s8bd_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 69 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (2) a seq[distinct] parameter -------------------------------------------

type Meters = distinct int
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
# ---- (3) the heap-depth budget bounds a chain, not a count -------------------

type Box = ref object
  x: int
type Outer = ref object
  inner: Box
type Node = ref object
  val: int
  next: Node

var gBox: Box

proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc rebindThenSet(v: var int, k: int) =
  gBox = Box(x: 1)
  v = k

proc manyReads(k: int) =
  ## Twelve dereferences of one object, none of them through another.
  let p = Box(x: 0)
  p.x = k
  if p.x > 0 and p.x < 9 and p.x != 1 and p.x != 2 and p.x == k and
     p.x != 4 and p.x != 5 and p.x < 7 and p.x != 6 and p.x >= 3:
    symexTarget("mr")
  if p.x != k: symexTarget("mr_dead")

proc sutHeapRebind(k: int) =
  let p = Box(x: 0)
  gBox = p
  rebindThenSet(p.x, k)
  if p.x == k and gBox.x == 1 and k == 6: symexTarget("hr")
  if p.x != k or gBox.x != 1: symexTarget("hr_dead")

proc sutHeapNested(k: int) =
  let o = Outer(inner: Box(x: 0))
  gBox = o.inner
  setXG(o.inner.x, k)
  if o.inner.x == 5 and k == 8: symexTarget("hn")
  if o.inner.x == k and k != 5: symexTarget("hn_dead")

proc chain7(n: Node) =
  ## A chain of seven links: the last read is seven dereferences deep.
  if n != nil and n.next != nil and n.next.next != nil and
     n.next.next.next != nil and n.next.next.next.next != nil and
     n.next.next.next.next.next != nil and
     n.next.next.next.next.next.next != nil and
     n.next.next.next.next.next.next.val == 7:
    symexTarget("c7")

proc chain9(n: Node) =
  ## Nine links: past the default budget of eight.
  if n == nil: return
  let n1 = n.next
  if n1 == nil: return
  let n2 = n1.next
  if n2 == nil: return
  let n3 = n2.next
  if n3 == nil: return
  let n4 = n3.next
  if n4 == nil: return
  let n5 = n4.next
  if n5 == nil: return
  let n6 = n5.next
  if n6 == nil: return
  let n7 = n6.next
  if n7 == nil: return
  let n8 = n7.next
  if n8 != nil and n8.val == 9: symexTarget("c9")

const shallow = SymexSettings(budget: ResourceBudget(maxHeapDepth: 3))

suite "S8bd (3): the heap-depth budget bounds a chain":

  test "nim":
    let o = Outer(inner: Box(x: 0))
    gBox = o.inner
    setXG(o.inner.x, 8)
    check o.inner.x == 5

  test "many reads of one object are within the default budget":
    ## RED: `sxUnknown`, `heDepthExhausted` (the count of every dereference
    ## on the path passed 8).
    discard clean(manyReads, "mr", sxSat)
    discard clean(manyReads, "mr_dead", sxUnsat)

  test "S8ba's hr and hn decide at the default budget":
    ## RED: `heDepthExhausted` (S8ba pinned them under `maxHeapDepth: 32`).
    discard clean(sutHeapRebind, "hr", sxSat)
    discard clean(sutHeapRebind, "hr_dead", sxUnsat)
    discard clean(sutHeapNested, "hn", sxSat)
    discard clean(sutHeapNested, "hn_dead", sxUnsat)

  test "a chain within the budget decides":
    let r = clean(chain7, "c7", sxSat)
    if r.status == sxSat:
      check r.witness[0].next.next.next.next.next.next.val == 7

  test "a chain past the budget still declines, and names it":
    for (r, lbl) in [(symexFind(chain9, tLabel("c9")), "default"),
                     (symexFind(chain7, tLabel("c7"), shallow), "shallow")]:
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.errors.hasKind(heDepthExhausted)
      var named = false
      for e in r.errors:
        if e.kind == heDepthExhausted and "maxHeapDepth" in e.msg: named = true
      check named

  test "the decline names the budget it hit":
    check "maxHeapDepth" in heapDerefDecline(8, 8, 8)
    check heapDerefDecline(7, 4000, 8) == ""
    check "heapDerefsPerPathCap" in
      heapDerefDecline(1, heapDerefsPerPathCap + 1, 8)
    check "heapDerefsPerPathCap" in
      heapDerefDecline(1, heapDerefsPerPathCap + 1, 0)
    check heapDerefDecline(100, 100, 0) == ""

# ---- (4) by reference: an indexed ref, a call result, a generic callee -------

var gI: int
var gCount: int

proc bumpThenSet(v: var int, k: int) =
  ## Moves the index the caller's lvalue was spelled with, then writes.
  gI = 1
  v = k
  if gBox.x == 77: gBox.x = 78

proc nextI(): int =
  inc gCount
  gCount - 1

proc getB(): Box =
  inc gCount
  gBox

proc setGen[T](v: var T, k: T) =
  v = k
  gBox.x = 5

type Box2 = ref object
  x: int
  y: int16
var gB2: Box2

proc setGen2[T](v: var T, k: T) =
  v = k
  gB2.x = 5

proc sutArrElem(k: int) =
  var a = [Box(x: 0)]
  gBox = a[0]
  setXG(a[0].x, k)
  if a[0].x == 5 and k == 2: symexTarget("he")
  if a[0].x == k and k != 5: symexTarget("he_dead")

suite "S8bd (4): more lvalues and callees are passed by reference":

  test "nim":
    var a = [Box(x: 0), Box(x: 0)]
    gI = 0
    gBox = a[1]
    bumpThenSet(a[gI].x, 4)
    check a[0].x == 4 and a[1].x == 0 and gI == 1
    var s = @[Box(x: 0), Box(x: 0)]
    gCount = 0
    gBox = s[0]
    setXG(s[nextI()].x, 6)
    check s[0].x == 5 and gCount == 1
    gBox = Box(x: 0)
    gCount = 0
    setXG(getB().x, 2)
    check gBox.x == 5 and gCount == 1
    let p = Box(x: 0)
    gBox = p
    setGen(p.x, 1)
    check p.x == 5
    let q = Box2(x: 0, y: 0)
    gB2 = q
    setGen2(q.y, 9'i16)
    setGen2(q.x, 9)
    check q.x == 5 and q.y == 9

  test "an array element":
    ## RED: `sxUnknown`, `feUnsupportedOp` (S8au's decline; S8ba pinned it).
    discard clean(sutArrElem, "he", sxSat)
    discard clean(sutArrElem, "he_dead", sxUnsat)
