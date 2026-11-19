## RFC-0016 PRC-51 -- the seven `=dup` shapes PRC-50 left declining, and
## their siblings. Native truth (Nim 2.2.10, c and cpp agree), `=dup` calls
## per call (`=copy` is the default, uncounted):
##
##   f1   0
##   f2   2
##   f3   0
##   f4   1
##   f5   1
##   f6   2
##   f7   0
##   f8   1
##   f9   0
##   t1   1
##   t2   3
##   t3   0
##   t4   1
##   t5   0
##   s1   2
##   s2   2
##   s3   0
##   s4   0
##   s5   0
##   s6   0
##   s7   2
##   s8   2
##   s9   2
##   y3f  0
##   y3g  0
##   y3j  2
##   y3l  0
##   y3h  0
##   y3k  0
##   y3m  0
##   y3n  2
##   f10  0    (`w.n` written in the loop body: rule A)
##   t6   1    (`t[0]` moved, `t[1]` read after its sink: copied)
##   s10  2    (an array read after the loop: rule B makes it a cursor)
##   s11  2    (an array read in the body after the sink)
##   s12  2    (`pairs` over an array read after the loop)
##   y4   0    (`yield x.d` then a made value: owns)
##
## The macro sees everything the compiler uses for each (`varpartitions`
## at 2.2.10, `injectdestructors`' last-read analysis), so each is pinned
## exact. `let b = w.d` (f3-f5, f8, f9): `b` is a cursor when `w`'s live
## range covers `b`'s and no path of `w` is written in it (f5: reading
## `w.n` after keeps `w` live; f9: writing `w.n` makes `b` own, and `w.d`'s
## last read moves); otherwise `b` owns and `w.d` is moved at its last read.
## `t[0]` of an owning tuple local is moved at its last read, path by path
## (t5: reading `t[1]` after does not copy it). `system.items` over a seq
## yields `lent T` (a cursor: copied at each sink), and `pairs` over a seq
## reads the seq again after the body (`assert(len(a) == L)`), so its
## element variable is a cursor by rule B; over an array both yield
## `a[i]`, a borrow of the array decided by rule B like `let b = w.d`: the
## loop variable owns (`=copy`, then moved) unless the array is read after
## its last read (s10-s12). A loop variable a `yield x.d` assigns borrows
## from `w` (f1, f2, f6, f7, f10: rule A on a write in the body); a
## `yield` of a value made there makes it own whatever the others yield
## (y3h, y3k, y4).
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
type W2 = object
  w: W
iterator fld(x: W): DObj =
  yield x.d
  yield x.d
iterator fld2(x: W2): DObj =
  yield x.w.d
  yield x.w.d
iterator tup(x: DObj): (DObj, int) =
  yield (x, 1)
  yield (x, 2)
iterator freshLoop(n: int): DObj =
  var i = 0
  while i < 2:
    yield DObj(v: n + i)
    inc i
iterator mixed(x: DObj; n: int): DObj =
  yield x
  yield DObj(v: n)
iterator mixF(x: W; n: int): DObj =
  yield x.d
  yield DObj(v: n)
iterator mixed2(x: DObj; n: int): DObj =
  yield DObj(v: n)
  yield x
proc f1(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in fld(w): result += dTake(o) * 100
proc f2(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in fld(w): result += dTake(o) * 100
  result += w.d.v
proc f3(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  let b = w.d
  result += dTake(b) * 100
proc f4(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  let b = w.d
  result += dTake(b) * 100 + w.d.v
proc f5(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  let b = w.d
  result += dTake(b) * 100 + w.n
proc f6(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in fld(w): result += dTake(o) * 100
  result += w.n
proc f7(k: int): int =
  let w = W2(w: W(d: DObj(v: k), n: 1))
  for o in fld2(w): result += dTake(o) * 100
proc f8(k: int): int =
  let w = W2(w: W(d: DObj(v: k), n: 1))
  let b = w.w.d
  result += dTake(b) * 100 + w.w.d.v
proc f9(k: int): int =
  var w = W(d: DObj(v: k), n: 1)
  let b = w.d
  w.n = 3
  result += dTake(b) * 100 + w.n
proc t1(k: int): int =
  let a = DObj(v: k)
  for t in tup(a): result += dTake(t[0]) * 100 + t[1]
proc t2(k: int): int =
  let a = DObj(v: k)
  for t in tup(a): result += dTake(t[0]) * 100 + t[0].v
proc t3(k: int): int =
  let a = DObj(v: k)
  let t = (a, 1)
  result += dTake(t[0]) * 100
proc t4(k: int): int =
  let t = (DObj(v: k), 1)
  result += dTake(t[0]) * 100 + t[0].v
proc t5(k: int): int =
  let t = (DObj(v: k), 1)
  result += dTake(t[0]) * 100 + t[1]
proc s1(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100
proc s2(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for i, o in s: result += dTake(o) * 100 + i
proc s3(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s.items:
    let b = o
    result += dTake(b) * 100
proc s4(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100
proc s5(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for i, o in s: result += dTake(o) * 100 + i
proc s6(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for o in s:
    let b = o
    result += dTake(b) * 100
proc s7(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100 + o.v
proc s8(k: int): int =
  let s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s: result += o.v
  for o in s: result += dTake(o) * 100
proc s9(k: int): int =
  var s = @[DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100
  result += s[0].v
proc y3f(k: int): int =
  for o in freshLoop(k): result += dTake(o) * 100
proc y3g(k: int): int =
  var i = 0
  while i < 2:
    let t = DObj(v: k + i)
    result += dTake(t) * 100
    inc i
proc y3j(k: int): int =
  var i = 0
  while i < 2:
    let t = DObj(v: k + i)
    result += dTake(t) * 100 + t.v
    inc i
proc y3l(k: int): int =
  for o in freshLoop(k):
    let b = o
    result += dTake(b) * 100
proc y3h(k: int): int =
  let a = DObj(v: k)
  for o in mixed(a, k): result += dTake(o) * 100
proc y3k(k: int): int =
  let a = DObj(v: k)
  for o in mixed2(a, k): result += dTake(o) * 100
proc y3m(k: int): int =
  let a = DObj(v: k)
  for o in mixed(a, k):
    let b = o
    result += dTake(b) * 100
proc y3n(k: int): int =
  let a = DObj(v: k)
  for o in mixed(a, k): result += dTake(o) * 100 + o.v
proc f10(k: int): int =
  var w = W(d: DObj(v: k), n: 1)
  for o in fld(w):
    w.n = 5
    result += dTake(o) * 100
  result += w.d.v
proc t6(k: int): int =
  var t = (DObj(v: k), DObj(v: k + 1))
  result += dTake(t[0]) * 100 + dTake(t[1]) * 10 + t[1].v
proc s10(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100
  result += s[0].v
proc s11(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for o in s: result += dTake(o) * 100 + s[1].v
proc s12(k: int): int =
  let s = [DObj(v: k), DObj(v: k + 1)]
  for i, o in s: result += dTake(o) * 100 + i
  result += s[1].v
proc y4(k: int): int =
  let w = W(d: DObj(v: k), n: 1)
  for o in mixF(w, k): result += dTake(o) * 100
  result += w.d.v

# Each entry: `hit` holds the native value, `Never` another classification's.
template pair(name, neverName: untyped; call, hitV, neverV: untyped) =
  proc name(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == hitV: symexTarget("hit")
  proc neverName(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == neverV: symexTarget("hit")
pair(eF1, eF1Never, f1(k), 200 * k + 0, 200 * k + 100)
pair(eF2, eF2Never, f2(k), 201 * k + 200, 201 * k + 100)
pair(eF3, eF3Never, f3(k), 100 * k + 0, 100 * k + 100)
pair(eF4, eF4Never, f4(k), 101 * k + 100, 101 * k + 0)
pair(eF5, eF5Never, f5(k), 100 * k + 101, 100 * k + 1)
pair(eF6, eF6Never, f6(k), 200 * k + 201, 200 * k + 101)
pair(eF7, eF7Never, f7(k), 200 * k + 0, 200 * k + 100)
pair(eF8, eF8Never, f8(k), 101 * k + 100, 101 * k + 0)
pair(eF9, eF9Never, f9(k), 100 * k + 3, 100 * k + 103)
pair(eT1, eT1Never, t1(k), 200 * k + 103, 200 * k + 3)
pair(eT2, eT2Never, t2(k), 202 * k + 301, 202 * k + 201)
pair(eT3, eT3Never, t3(k), 100 * k + 0, 100 * k + 100)
pair(eT4, eT4Never, t4(k), 101 * k + 100, 101 * k + 0)
pair(eT5, eT5Never, t5(k), 100 * k + 1, 100 * k + 101)
pair(eS1, eS1Never, s1(k), 200 * k + 300, 200 * k + 200)
pair(eS2, eS2Never, s2(k), 200 * k + 301, 200 * k + 201)
pair(eS3, eS3Never, s3(k), 200 * k + 100, 200 * k + 200)
pair(eS4, eS4Never, s4(k), 200 * k + 100, 200 * k + 200)
pair(eS5, eS5Never, s5(k), 200 * k + 101, 200 * k + 201)
pair(eS6, eS6Never, s6(k), 200 * k + 100, 200 * k + 200)
pair(eS7, eS7Never, s7(k), 202 * k + 301, 202 * k + 201)
pair(eS8, eS8Never, s8(k), 202 * k + 301, 202 * k + 201)
pair(eS9, eS9Never, s9(k), 201 * k + 300, 201 * k + 200)
pair(eY3f, eY3fNever, y3f(k), 200 * k + 100, 200 * k + 200)
pair(eY3g, eY3gNever, y3g(k), 200 * k + 100, 200 * k + 200)
pair(eY3j, eY3jNever, y3j(k), 202 * k + 301, 202 * k + 201)
pair(eY3l, eY3lNever, y3l(k), 200 * k + 100, 200 * k + 200)
pair(eY3h, eY3hNever, y3h(k), 200 * k + 0, 200 * k + 100)
pair(eY3k, eY3kNever, y3k(k), 200 * k + 0, 200 * k + 100)
pair(eY3m, eY3mNever, y3m(k), 200 * k + 0, 200 * k + 100)
pair(eY3n, eY3nNever, y3n(k), 202 * k + 200, 202 * k + 100)
pair(eF10, eF10Never, f10(k), 201 * k + 0, 201 * k + 200)
pair(eT6, eT6Never, t6(k), 111 * k + 21, 111 * k + 11)
pair(eS10, eS10Never, s10(k), 201 * k + 300, 201 * k + 100)
pair(eS11, eS11Never, s11(k), 202 * k + 302, 202 * k + 102)
pair(eS12, eS12Never, s12(k), 201 * k + 302, 201 * k + 102)
pair(eY4, eY4Never, y4(k), 201 * k + 0, 201 * k + 100)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")
template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

suite "PRC-51":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 433
  test "native truth":
    for e in [eF1, eF2, eF3, eF4, eF5, eF6, eF7, eF8, eF9, eT1, eT2, eT3, eT4,
              eT5, eS1, eS2, eS3, eS4, eS5, eS6, eS7, eS8, eS9, eY3f, eY3g,
              eY3j, eY3l, eY3h, eY3k, eY3m, eY3n, eF10, eT6, eS10, eS11,
              eS12, eY4]:
      for k in [-42, 0, 1, 2, 3]:
        check native(e(k)) == "hit"
  test "field paths (rule B on the root, rule A on any path)":
    exact(eF1, eF1Never)
    exact(eF2, eF2Never)
    exact(eF3, eF3Never)
    exact(eF4, eF4Never)
    exact(eF5, eF5Never)
    exact(eF6, eF6Never)
    exact(eF7, eF7Never)
    exact(eF8, eF8Never)
    exact(eF9, eF9Never)
    exact(eF10, eF10Never)
  test "a field of a local at a sink position":
    exact(eT1, eT1Never)
    exact(eT2, eT2Never)
    exact(eT3, eT3Never)
    exact(eT4, eT4Never)
    exact(eT5, eT5Never)
    exact(eT6, eT6Never)
  test "listed `system` iterators":
    exact(eS1, eS1Never)
    exact(eS2, eS2Never)
    exact(eS3, eS3Never)
    exact(eS4, eS4Never)
    exact(eS5, eS5Never)
    exact(eS6, eS6Never)
    exact(eS7, eS7Never)
    exact(eS8, eS8Never)
    exact(eS9, eS9Never)
    exact(eS10, eS10Never)
    exact(eS11, eS11Never)
    exact(eS12, eS12Never)
  test "a local declared in a loop":
    exact(eY3f, eY3fNever)
    exact(eY3g, eY3gNever)
    exact(eY3j, eY3jNever)
    exact(eY3l, eY3lNever)
  test "a mixed iterator":
    exact(eY3h, eY3hNever)
    exact(eY3k, eY3kNever)
    exact(eY3m, eY3mNever)
    exact(eY3n, eY3nNever)
    exact(eY4, eY4Never)
