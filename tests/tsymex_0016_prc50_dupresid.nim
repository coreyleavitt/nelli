## RFC-0016 PRC-50 -- the `=dup` sink shapes PRC-49 left declining, and
## their siblings, in the body of a `for` over an inline iterator. Native
## truth (Nim 2.2.10, c and cpp), `dups` per call:
##
##   y3  `yield` of a value made there (twice), the loop variable sunk  0
##   y3b the same of a call's result                                   0
##   y3c `yield` of a local of the iterator (a cursor)                 2
##   y3d y3 with `let b = o`, `b` sunk                                 0
##   y3e y3 with `o` read after its sink                               2
##   y3i y3d with `o` read after                                       0
##   y5  `let b = o` of a cursor loop variable, `b` sunk               0
##   y5b y5 with `o` read after                                        0
##   y5c y5 with `var b`                                               0
##   y5d y5 over one `yield`                                           0
##   y5e y5 over a looping `yield`                                     0
##   y5f y5d with `a` read after the loop                              0
##   y5g y5 with `b` read after its sink                               2
##   oa3 a `for` over `0 ..< x.len` in the iterator, `let b = a`       0
##   oa4 the same with a `while`                                       0
##   oa5 oa3 sinking `a` itself                                        2
## Still declined (sound, pinned, not modelled):
##   f1  `yield x.d` (a field of a formal), `w` not read after          0
##   f2  the same, `w.d` read after the loop                           2
##   t1  `yield (x, 1)`, `dTake(t[0])`                                 1
##   s1  `system.items` over a `seq` of the hooked type                2
##   s2  `pairs` over it                                               2
##   s3  s1 with `let b = o`                                           0
##   s4  `items` over an array of it                                   0
##   y3f a looping `yield` of a value made there                       0
##   y3h `yield x` then `yield` of a value made there                  0
##
## The loop variable of an iterator whose every `yield` yields a value made
## there owns data (`varpartitions.destMightOwn`): no cursor, a new value
## sunk into it at each `yield` (`dupOwningIterVar`). `let b = o` of a loop
## variable of an inlined `for` makes `b` own: a cursor one is
## `reassignedTo` the yielded symbol (rule D), an owning one reassigned
## (rule C). A magic call (`len(x)` of an `openArray`) mutates no argument
## through a pointer (`varpartitions.traverse`: `m == mNone`).
## f1/f2: whether `o` is a cursor follows `w`'s live range against `o`'s
## (rule B) on a field path, which the scan reads for a symbol only (as in
## straight-line code: `let b = w.d` declines). t1: a field of a local at a
## sink position is not followed. s1-s4: the loop variable of a listed
## `system` iterator of the hooked type is not an event the scan keys.
## y3f: a local declared in a loop owns afresh each pass (not followed).
## y3h: a mixed iterator (a cursor `yield` and an owning one).
## (`for (o, i) in` an iterator yielding a tuple is not parsed by the walker:
## a compile-time `expectKind`, outside the `=dup` route; not pinned here.)
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v
type W = object
  d: DObj
  n: int
proc mk(n: int): DObj = DObj(v: n)
iterator objs(x: DObj): DObj =
  yield x
  yield x
iterator fresh(n: int): DObj =
  yield DObj(v: n)
  yield DObj(v: n + 1)
iterator freshCall(n: int): DObj =
  yield mk(n)
  yield mk(n + 1)
iterator freshVar(n: int): DObj =
  var t = DObj(v: n)
  yield t
  yield t
iterator fld(x: W): DObj =
  yield x.d
  yield x.d
iterator tup(x: DObj): (DObj, int) =
  yield (x, 1)
  yield (x, 2)
iterator oaLoop(x: openArray[int]): int =
  for i in 0 ..< x.len:
    yield x[i]
iterator oaWhile(x: openArray[int]): int =
  var i = 0
  while i < x.len:
    yield x[i]
    inc i
iterator objOnce(x: DObj): DObj =
  yield x
iterator loopObjs(x: DObj; n: int): DObj =
  var i = 0
  while i < n:
    yield x
    inc i
proc y5d(k: int): int =
  let a = DObj(v: k)
  for o in objOnce(a):
    let b = o
    result += dTake(b) * 100
proc y5e(k: int): int =
  let a = DObj(v: k)
  for o in loopObjs(a, 2):
    let b = o
    result += dTake(b) * 100
proc y5f(k: int): int =
  let a = DObj(v: k)
  for o in objOnce(a):
    let b = o
    result += dTake(b) * 100
  result += a.v
proc f3(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  let b = w.d
  result += dTake(b) * 100
proc f4(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  let b = w.d
  result += dTake(b) * 100 + w.d.v
proc y3(k: int): int =
  for o in fresh(k):
    result += dTake(o) * 100
proc y3b(k: int): int =
  for o in freshCall(k):
    result += dTake(o) * 100
proc y3c(k: int): int =
  for o in freshVar(k):
    result += dTake(o) * 100
proc y3d(k: int): int =
  for o in fresh(k):
    let b = o
    result += dTake(b) * 100
proc y3e(k: int): int =
  for o in fresh(k):
    result += dTake(o) * 100 + o.v
proc y5(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    let b = o
    result += dTake(b) * 100
proc y5b(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    let b = o
    result += dTake(b) * 100 + o.v
proc y5c(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    var b = o
    result += dTake(b) * 100
proc f1(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in fld(w):
    result += dTake(o) * 100
proc f2(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in fld(w):
    result += dTake(o) * 100
  result += w.d.v
proc t1(k: int): int =
  let a = DObj(v: k)
  for t in tup(a):
    result += dTake(t[0]) * 100 + t[1]
proc s1(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s:
    result += dTake(o) * 100
proc s2(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for i, o in s:
    result += dTake(o) * 100 + i
proc s3(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s.items:
    let b = o
    result += dTake(b) * 100
proc s4(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for o in s:
    result += dTake(o) * 100
proc oa3(k: int): int =
  let a = DObj(v: k)
  for i in oaLoop([0, 1]):
    let b = a
    result += dTake(b) * 100 + i
proc oa4(k: int): int =
  let a = DObj(v: k)
  for i in oaWhile([0, 1]):
    let b = a
    result += dTake(b) * 100 + i
proc oa5(k: int): int =
  let a = DObj(v: k)
  for i in oaLoop([0, 1]):
    result += dTake(a) * 100 + i

iterator freshLoop(n: int): DObj =
  var i = 0
  while i < 2:
    yield DObj(v: n + i)
    inc i
iterator mixed(x: DObj; n: int): DObj =
  yield x
  yield DObj(v: n)
proc y5g(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    let b = o
    result += dTake(b) * 100 + b.v
proc y3f(k: int): int =
  for o in freshLoop(k):
    result += dTake(o) * 100
proc y3h(k: int): int =
  let a = DObj(v: k)
  for o in mixed(a, k):
    result += dTake(o) * 100
proc y3i(k: int): int =
  for o in fresh(k):
    let b = o
    result += dTake(b) * 100 + o.v

# Each entry: `hit` holds the native value, `Never` another classification's.
template pair(name, neverName: untyped; call, hitV, neverV: untyped) =
  proc name(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == hitV: symexTarget("hit")
  proc neverName(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == neverV: symexTarget("hit")

pair(eY3, eY3Never, y3(k), 200 * k + 100, 200 * k + 300)
pair(eY3b, eY3bNever, y3b(k), 200 * k + 100, 200 * k + 300)
pair(eY3c, eY3cNever, y3c(k), 200 * k + 200, 200 * k)
pair(eY3d, eY3dNever, y3d(k), 200 * k + 100, 200 * k + 300)
pair(eY3e, eY3eNever, y3e(k), 202 * k + 301, 202 * k + 101)
pair(eY5, eY5Never, y5(k), 200 * k, 200 * k + 200)
pair(eY5b, eY5bNever, y5b(k), 202 * k, 202 * k + 200)
pair(eY5c, eY5cNever, y5c(k), 200 * k, 200 * k + 200)
pair(eY5d, eY5dNever, y5d(k), 100 * k, 100 * k + 100)
pair(eY5e, eY5eNever, y5e(k), 200 * k, 200 * k + 200)
pair(eY5f, eY5fNever, y5f(k), 101 * k, 101 * k + 100)
pair(eF1, eF1Never, f1(k), 200 * k, 200 * k + 200)
pair(eF2, eF2Never, f2(k), 201 * k + 200, 201 * k)
pair(eT1, eT1Never, t1(k), 200 * k + 103, 200 * k + 3)
pair(eS1, eS1Never, s1(k), 200 * k + 300, 200 * k + 100)
pair(eS2, eS2Never, s2(k), 200 * k + 301, 200 * k + 101)
pair(eS3, eS3Never, s3(k), 200 * k + 100, 200 * k + 300)
pair(eS4, eS4Never, s4(k), 200 * k + 100, 200 * k + 300)
pair(eOa3, eOa3Never, oa3(k), 200 * k + 1, 200 * k + 101)
pair(eOa4, eOa4Never, oa4(k), 200 * k + 1, 200 * k + 101)
pair(eOa5, eOa5Never, oa5(k), 200 * k + 201, 200 * k + 101)
pair(eY5g, eY5gNever, y5g(k), 202 * k + 200, 202 * k)
pair(eY3f, eY3fNever, y3f(k), 200 * k + 100, 200 * k + 300)
pair(eY3h, eY3hNever, y3h(k), 200 * k, 200 * k + 100)
pair(eY3i, eY3iNever, y3i(k), 202 * k + 101, 202 * k + 301)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

template declined(p: untyped) =
  pinDecline(p, dCell, feGlobalRouteUnproved, needle = "=dup")

suite "PRC-50":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 432

  test "native truth":
    for e in [eY3, eY3b, eY3c, eY3d, eY3e, eY5, eY5b, eY5c, eY5d, eY5e,
              eY5f, eF1,
              eF2, eT1, eS1, eS2, eS3, eS4, eOa3, eOa4, eOa5, eY5g,
              eY3f, eY3h, eY3i]:
      for k in [-42, 0, 1, 2, 3]:
        check native(e(k)) == "hit"

  test "owning loop variables, aliases of one, a listed inner loop":
    exact(eY3, eY3Never)
    exact(eY3b, eY3bNever)
    exact(eY3c, eY3cNever)
    exact(eY3d, eY3dNever)
    exact(eY3e, eY3eNever)
    exact(eY5, eY5Never)
    exact(eY5b, eY5bNever)
    exact(eY5c, eY5cNever)
    exact(eY5d, eY5dNever)
    exact(eY5e, eY5eNever)
    exact(eY5f, eY5fNever)
    exact(eOa3, eOa3Never)
    exact(eOa4, eOa4Never)
    exact(eOa5, eOa5Never)
    exact(eY5g, eY5gNever)
    exact(eY3i, eY3iNever)

  test "still declined":
    declined(eF1)
    declined(eF2)
    declined(eT1)
    declined(eS1)
    declined(eS2)
    declined(eS3)
    declined(eS4)
    declined(eY3f)
    declined(eY3h)
