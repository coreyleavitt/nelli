## RFC-0016 PRC-48 -- a user `=dup` at a sink position in the body of a `for`
## over an inline iterator. The compiler inlines the iterator (`transf`), the
## loop body at each `yield`, its locals fresh in each copy after the first
## (`introduceNewLocalVars`), and its cursor inference (`varpartitions.
## computeCursors`) and last-read analysis run on the inlined tree: each copy
## of a written site is classified on its own. Native truth (Nim 2.2.10, c and
## cpp), `dups` per call:
##
##   i1 two `yield`s, `let b = a` in the body               1 (copy 1 of 2)
##   i2 a looping iterator                                   0
##   i3 three `yield`s                                       2
##   h1 the header naming `a`, `b` in the body               1
##   h3 the same over a looping iterator                     0
##   d1 `dTake(a)` in a two-`yield` body                     1
##   d2 `dTake(a)` in a looping body                         2
##   s1 `b` before the loop, sunk in a two-`yield` body       1
##   s2 the same, looping                                    2
##   a1 two `yield`s, `a` read after the loop                2
##   br `yield` under if/else (k > 0: copy 1; else copy 2)   1 / 0
##   ol one `yield`, then a loop of them                     1
##   lo a loop of `yield`s, then one                         2
##   n1 an iterator over a nested inline iterator            1
##   c1 a closure iterator (not inlined: a loop)             0
##   bk a `break` after the first copy's site                1
##   w1 a `while` around a two-`yield` for                   2
##   cs `yield` per `case` arm (copy 1, 2: 1; the last: 0)
##   t1 a computed scalar argument (`upto(k mod 2 + 2)`)    0
##   ct a `continue` before the first copy's site            0
##   tw two fors over one iterator                           3
##   y1 an iterator yielding the hooked type, the loop
##      variable sunk                                        2 (declined)
##   ti a sink inside the iterator's body on a substituted
##      formal, `a` read after the loop                      1 (declined)
##   g1 a generic iterator's instance, `b` in the body       1
##   tr an iterator whose `yield`s are in a `try`            1 (declined)
##   oa an iterator with an `openArray` formal               1 (declined)
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v

iterator two(): int =
  yield 0
  yield 1
iterator three(): int =
  yield 0
  yield 1
  yield 2
iterator upto(n: int): int =
  var i = 0
  while i < n:
    yield i
    inc i
iterator twoOf(x: DObj): int =
  yield x.v
  yield x.v + 1
iterator uptoOf(x: DObj; n: int): int =
  var i = 0
  while i < n:
    yield x.v + i
    inc i
iterator branchy(c: bool): int =
  if c: yield 0
  else: yield 1
iterator oneThenLoop(n: int): int =
  yield 10
  var i = 0
  while i < n:
    yield i
    inc i
iterator loopThenOne(n: int): int =
  var i = 0
  while i < n:
    yield i
    inc i
  yield 10
iterator twoOuter(): int =
  for j in two(): yield j
iterator ci(): int {.closure.} =
  yield 0
  yield 1
iterator caseOf(c: int): int =
  case c
  of 0: yield 0
  of 1: yield 1
  else: yield 2
iterator objs(x: DObj): DObj =
  yield x
  yield x
iterator takeIn(x: DObj): int =
  yield dTake(x)
  yield 1
iterator gtwo[T](x: T): int =
  yield 0
  yield 1
iterator tryTwo(): int =
  try:
    yield 0
    yield 1
  finally:
    discard
iterator oaTwo(x: openArray[int]): int =
  yield x[0]
  yield x[1]

proc i1(k: int): int =
  let a = DObj(v: k)
  for i in two():
    let b = a
    result += dTake(b) * 100 + i
proc i2(k: int): int =
  let a = DObj(v: k)
  for i in upto(2):
    let b = a
    result += dTake(b) * 100 + i
proc i3(k: int): int =
  let a = DObj(v: k)
  for i in three():
    let b = a
    result += dTake(b) * 100 + i
proc h1(k: int): int =
  let a = DObj(v: k)
  for i in twoOf(a):
    let b = a
    result += dTake(b) * 100 + i
proc h3(k: int): int =
  let a = DObj(v: k)
  for i in uptoOf(a, 2):
    let b = a
    result += dTake(b) * 100 + i
proc d1(k: int): int =
  let a = DObj(v: k)
  for i in two():
    result += dTake(a) * 100 + i
proc d2(k: int): int =
  let a = DObj(v: k)
  for i in upto(2):
    result += dTake(a) * 100 + i
proc s1(k: int): int =
  let a = DObj(v: k)
  let b = a
  for i in two():
    result += dTake(b) * 100 + i
proc s2(k: int): int =
  let a = DObj(v: k)
  let b = a
  for i in upto(2):
    result += dTake(b) * 100 + i
proc a1(k: int): int =
  let a = DObj(v: k)
  for i in two():
    let b = a
    result += dTake(b) * 100 + i
  result += a.v * 10000
proc br(k: int): int =
  let a = DObj(v: k)
  for i in branchy(k > 0):
    let b = a
    result += dTake(b) * 100 + i
proc ol(k: int): int =
  let a = DObj(v: k)
  for i in oneThenLoop(2):
    let b = a
    result += dTake(b) * 100 + i
proc lo(k: int): int =
  let a = DObj(v: k)
  for i in loopThenOne(2):
    let b = a
    result += dTake(b) * 100 + i
proc n1(k: int): int =
  let a = DObj(v: k)
  for i in twoOuter():
    let b = a
    result += dTake(b) * 100 + i
proc c1(k: int): int =
  let a = DObj(v: k)
  for i in ci():
    let b = a
    result += dTake(b) * 100 + i
proc bk(k: int): int =
  let a = DObj(v: k)
  for i in two():
    let b = a
    result += dTake(b) * 100 + i
    break
proc w1(k: int): int =
  let a = DObj(v: k)
  var j = 0
  while j < 2:
    for i in two():
      let b = a
      result += dTake(b) * 100 + i
    inc j
proc cs(k: int): int =
  let a = DObj(v: k)
  for i in caseOf(k mod 3):
    let b = a
    result += dTake(b) * 100 + i
proc t1(k: int): int =
  let a = DObj(v: k)
  for i in upto(k mod 2 + 2):
    let b = a
    result += dTake(b) * 100 + i
proc ct(k: int): int =
  let a = DObj(v: k)
  for i in two():
    let b = a
    if i == 0: continue
    result += dTake(b) * 100 + i
proc tw(k: int): int =
  let a = DObj(v: k)
  for i in two():
    let b = a
    result += dTake(b) * 100 + i
  for i in two():
    let b = a
    result += dTake(b) * 1000 + i
proc y1(k: int): int =
  let a = DObj(v: k)
  for o in objs(a):
    result += dTake(o) * 100
proc ti(k: int): int =
  let a = DObj(v: k)
  for i in takeIn(a):
    result += i
  result += a.v * 100
proc g1(k: int): int =
  let a = DObj(v: k)
  for i in gtwo(a):
    let b = a
    result += dTake(b) * 100 + i
proc tr(k: int): int =
  let a = DObj(v: k)
  for i in tryTwo():
    let b = a
    result += dTake(b) * 100 + i
proc oa(k: int): int =
  let a = DObj(v: k)
  for i in oaTwo([0, 1]):
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

pair(eI1, eI1Never, i1(k), 200 * k + 101, 200 * k + 1)
pair(eI2, eI2Never, i2(k), 200 * k + 1, 200 * k + 101)
pair(eI3, eI3Never, i3(k), 300 * k + 203, 300 * k + 3)
pair(eH1, eH1Never, h1(k), 202 * k + 101, 202 * k + 1)
pair(eH3, eH3Never, h3(k), 202 * k + 1, 202 * k + 101)
pair(eD1, eD1Never, d1(k), 200 * k + 101, 200 * k + 1)
pair(eD2, eD2Never, d2(k), 200 * k + 201, 200 * k + 1)
pair(eS1, eS1Never, s1(k), 200 * k + 101, 200 * k + 1)
pair(eS2, eS2Never, s2(k), 200 * k + 201, 200 * k + 1)
pair(eA1, eA1Never, a1(k), 10200 * k + 201, 10200 * k + 1)
pair(eBr, eBrNever, br(k), (if k > 0: 100 * k + 100 else: 100 * k + 1),
     (if k > 0: 100 * k else: 100 * k + 101))
pair(eOl, eOlNever, ol(k), 300 * k + 111, 300 * k + 11)
pair(eLo, eLoNever, lo(k), 300 * k + 211, 300 * k + 11)
pair(eN1, eN1Never, n1(k), 200 * k + 101, 200 * k + 1)
pair(eC1, eC1Never, c1(k), 200 * k + 1, 200 * k + 201)
pair(eBk, eBkNever, bk(k), 100 * k + 100, 100 * k)
pair(eW1, eW1Never, w1(k), 400 * k + 202, 400 * k + 2)
pair(eCs, eCsNever, cs(k),
     (if k mod 3 == 2: 100 * k + 2 else: 100 * k + 100 + k mod 3),
     (if k mod 3 == 2: 100 * k + 102 else: 100 * k + k mod 3))
pair(eT1, eT1Never, t1(k), (if k mod 2 == 0: 200 * k + 1 else: 300 * k + 3),
     (if k mod 2 == 0: 200 * k + 101 else: 300 * k + 203))
pair(eCt, eCtNever, ct(k), 100 * k + 1, 100 * k + 101)
pair(eTw, eTwNever, tw(k), 2200 * k + 1202, 2200 * k + 2)
pair(eY1, eY1Never, y1(k), 200 * k + 200, 200 * k)
pair(eTi, eTiNever, ti(k), 101 * k + 2, 101 * k + 1)
pair(eG1, eG1Never, g1(k), 200 * k + 101, 200 * k + 1)
pair(eTr, eTrNever, tr(k), 200 * k + 101, 200 * k + 1)
pair(eOa, eOaNever, oa(k), 200 * k + 101, 200 * k + 1)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

template exact(hitP, neverP: untyped) =
  check pinExact(hitP, dCell, domain = idom).status == sxSat
  check pinExact(neverP, dCell, domain = idom).status == sxUnsat

template declined(p: untyped) =
  pinDecline(p, dCell, feGlobalRouteUnproved, needle = "=dup")

suite "PRC-48":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 429

  test "native truth":
    for e in [eI1, eI2, eI3, eH1, eH3, eD1, eD2, eS1, eS2, eA1, eBr, eOl,
              eLo, eN1, eC1, eBk, eW1, eCs, eT1, eCt, eTw, eY1, eTi, eG1,
              eTr, eOa]:
      for k in [-42, 0, 1, 2, 3]:
        check native(e(k)) == "hit"

  test "each inlined copy of a two-yield body":
    exact(eI1, eI1Never)
    exact(eI3, eI3Never)
    exact(eH1, eH1Never)
    exact(eD1, eD1Never)
    exact(eS1, eS1Never)
    exact(eA1, eA1Never)

  test "a looping iterator: one copy in a loop":
    exact(eI2, eI2Never)
    exact(eH3, eH3Never)
    exact(eD2, eD2Never)
    exact(eS2, eS2Never)
    exact(eT1, eT1Never)

  test "copies under branches, loops, jumps, nesting":
    exact(eBr, eBrNever)
    exact(eOl, eOlNever)
    exact(eLo, eLoNever)
    exact(eN1, eN1Never)
    exact(eBk, eBkNever)
    exact(eW1, eW1Never)
    exact(eCs, eCsNever)
    exact(eCt, eCtNever)
    exact(eTw, eTwNever)

  test "a closure iterator is a loop":
    exact(eC1, eC1Never)

  test "a generic iterator's instance is inlined":
    exact(eG1, eG1Never)

  test "a sunk loop variable of the hooked type declines":
    declined(eY1)

  test "an iterator not read inlined declines":
    # A sink inside the iterator's own body reads its formal in the walk and
    # the argument in the inlined scan: unmodelled. A `try` around the
    # `yield`s and an `openArray` formal are not inlined.
    declined(eTi)
    declined(eTr)
    declined(eOa)
