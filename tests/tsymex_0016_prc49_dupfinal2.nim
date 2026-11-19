## RFC-0016 PRC-49 -- the `=dup` sink shapes PRC-48 left declining, in the
## body of a `for` over an inline iterator (and in the iterator's own body).
## The compiler inlines the iterator (`transf.transformFor`) before it
## injects the hooks. Native truth (Nim 2.2.10, c and cpp), `dups` per call:
##
##   y1 two `yield x` of the hooked type, the loop variable sunk   2
##   y2 one `yield x`, sunk                                        1
##   y4 a looping `yield x`, sunk                                  2
##   y6 the loop variable read after its sink                      2
##   y7 one `yield x` of a `var`, `a` read after the loop          1
##   y3 `yield` of a value made there, sunk                        0 (PRC-50)
##   y5 `let b = o` of the loop variable, `b` sunk                 0 (PRC-50)
##   ti a sink of a formal in the iterator's body, `a` read after   1
##   ti2 the same, `a` not read after                              0
##   ti3 two `yield`s each sinking the formal                      1
##   ti4 a looping `yield` sinking the formal                      2
##   ti5 ti3 with `a` read after the loop                          2
##   tr `yield`s in a `try` with a `finally`                       1
##   tr2 `yield`s in a `try` with an `except`                      1
##   tr3 a `finally` reading the formal                            2
##   oa an `openArray` formal over an array constructor            1
##   oa2 the same over a `seq` local                               1
##   oa3 a `for` over the `openArray` in the iterator              0 (PRC-50)
##
## The loop variable of an iterator whose every `yield` is of a variable it
## owns, called with arguments of the caller's locals and literals only, is a
## cursor (`transf.isSimpleIteratorVar`): copied at every sink position.
## Declined here, exact since PRC-50 (`tsymex_0016_prc50_dupresid`): a loop variable that owns its value
## (y3: a `yield` of a value made there is no cursor; y5: `let b = o` of a
## cursor one makes `b` own, the plain `=copy`), whose ownership the scan
## does not follow, and `let b = a` in the body of a `for` over a listed
## iterator inside the inlined body (oa3), whose cursor inference
## (`dupAliasCursor`) is not followed there.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v

iterator objs(x: DObj): DObj =
  yield x
  yield x
iterator objOnce(x: DObj): DObj =
  yield x
iterator fresh(n: int): DObj =
  yield DObj(v: n)
  yield DObj(v: n + 1)
iterator loopObjs(x: DObj; n: int): DObj =
  var i = 0
  while i < n:
    yield x
    inc i
iterator takeIn(x: DObj): int =
  yield dTake(x)
  yield 1
iterator takeTwice(x: DObj): int =
  yield dTake(x)
  yield dTake(x)
iterator takeLoop(x: DObj; n: int): int =
  var i = 0
  while i < n:
    yield dTake(x)
    inc i
iterator tryTwo(): int =
  try:
    yield 0
    yield 1
  finally:
    discard
iterator tryExc(): int =
  try:
    yield 0
    yield 1
  except ValueError:
    discard
iterator tryOf(x: DObj): int =
  try:
    yield 0
    yield 1
  finally:
    discard x.v
iterator oaTwo(x: openArray[int]): int =
  yield x[0]
  yield x[1]
iterator oaLoop(x: openArray[int]): int =
  for i in 0 ..< x.len:
    yield x[i]
proc y1(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    result += dTake(o) * 100
proc y2(k: int): int =
  let a = DObj(v: k)
  for o in objOnce(a):
    result += dTake(o) * 100
proc y3(k: int): int =
  for o in fresh(k):
    result += dTake(o) * 100
proc y4(k: int): int =
  let a = DObj(v: k)
  for o in loopObjs(a, 2):
    result += dTake(o) * 100
proc y5(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    let b = o
    result += dTake(b) * 100
proc y6(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    result += dTake(o) * 100 + o.v
proc y7(k: int): int =
  var a = DObj(v: k)
  for o in objOnce(a):
    result += dTake(o) * 100
  result += a.v
proc ti(k: int): int =
  let a = DObj(v: k)
  for i in takeIn(a):
    result += i
  result += a.v * 100
proc ti2(k: int): int =
  let a = DObj(v: k)
  for i in takeIn(a):
    result += i
proc ti3(k: int): int =
  let a = DObj(v: k)
  for i in takeTwice(a):
    result += i
proc ti4(k: int): int =
  let a = DObj(v: k)
  for i in takeLoop(a, 2):
    result += i
proc ti5(k: int): int =
  let a = DObj(v: k)
  for i in takeTwice(a):
    result += i
  result += a.v * 100
proc tr(k: int): int =
  let a = DObj(v: k)
  for i in tryTwo():
    let b = a
    result += dTake(b) * 100 + i
proc tr2(k: int): int =
  let a = DObj(v: k)
  for i in tryExc():
    let b = a
    result += dTake(b) * 100 + i
proc tr3(k: int): int =
  let a = DObj(v: k)
  for i in tryOf(a):
    let b = a
    result += dTake(b) * 100 + i
proc oa(k: int): int =
  let a = DObj(v: k)
  for i in oaTwo([0, 1]):
    let b = a
    result += dTake(b) * 100 + i
proc oa2(k: int): int =
  let a = DObj(v: k)
  let s = @[0, 1]
  for i in oaTwo(s):
    let b = a
    result += dTake(b) * 100 + i
proc oa3(k: int): int =
  let a = DObj(v: k)
  for i in oaLoop([0, 1]):
    let b = a
    result += dTake(b) * 100 + i

# Each entry: `hit` holds the native value, `Never` the one the other
# classification of a copy would give.
template pair(name, neverName: untyped; call, hitV, neverV: untyped) =
  proc name(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == hitV: symexTarget("hit")
  proc neverName(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == neverV: symexTarget("hit")

pair(eY1, eY1Never, y1(k), 200 * k + 200, 200 * k)
pair(eY2, eY2Never, y2(k), 100 * k + 100, 100 * k)
pair(eY4, eY4Never, y4(k), 200 * k + 200, 200 * k)
pair(eY6, eY6Never, y6(k), 202 * k + 200, 202 * k)
pair(eY7, eY7Never, y7(k), 101 * k + 100, 101 * k)
pair(eY3, eY3Never, y3(k), 200 * k + 100, 200 * k + 300)
pair(eY5, eY5Never, y5(k), 200 * k, 200 * k + 200)
pair(eTi, eTiNever, ti(k), 101 * k + 2, 101 * k + 1)
pair(eTi2, eTi2Never, ti2(k), k + 1, k + 2)
pair(eTi3, eTi3Never, ti3(k), 2 * k + 1, 2 * k)
pair(eTi4, eTi4Never, ti4(k), 2 * k + 2, 2 * k)
pair(eTi5, eTi5Never, ti5(k), 102 * k + 2, 102 * k + 1)
pair(eTr, eTrNever, tr(k), 200 * k + 101, 200 * k + 1)
pair(eTr2, eTr2Never, tr2(k), 200 * k + 101, 200 * k + 1)
pair(eTr3, eTr3Never, tr3(k), 200 * k + 201, 200 * k + 101)
pair(eOa, eOaNever, oa(k), 200 * k + 101, 200 * k + 1)
pair(eOa2, eOa2Never, oa2(k), 200 * k + 101, 200 * k + 1)
pair(eOa3, eOa3Never, oa3(k), 200 * k + 1, 200 * k + 101)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

suite "PRC-49":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 430

  test "native truth":
    for e in [eY1, eY2, eY4, eY6, eY7, eY3, eY5, eTi, eTi2, eTi3, eTi4, eTi5,
              eTr, eTr2, eTr3, eOa, eOa2, eOa3]:
      for k in [-42, 0, 1, 2, 3]:
        check native(e(k)) == "hit"

  test "a cursor loop variable of the hooked type is copied at each sink":
    exact(eY1, eY1Never)
    exact(eY2, eY2Never)
    exact(eY4, eY4Never)
    exact(eY6, eY6Never)
    exact(eY7, eY7Never)

  test "an owning loop variable (PRC-50: exact)":
    exact(eY3, eY3Never)
    exact(eY5, eY5Never)

  test "a sink of a formal in the iterator's own body":
    exact(eTi, eTiNever)
    exact(eTi2, eTi2Never)
    exact(eTi3, eTi3Never)
    exact(eTi4, eTi4Never)
    exact(eTi5, eTi5Never)

  test "yields in a try":
    exact(eTr, eTrNever)
    exact(eTr2, eTr2Never)
    exact(eTr3, eTr3Never)

  test "an openArray formal":
    exact(eOa, eOaNever)
    exact(eOa2, eOa2Never)

  test "a listed loop inside the inlined body (PRC-50: exact)":
    exact(eOa3, eOa3Never)
