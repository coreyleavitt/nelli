## RFC-0016 W3-z P13: `break` / `continue` in the body of a `for` over an
## inline iterator.
##
## Natively `break` leaves the whole iterator expansion and `continue`
## resumes after the current `yield`. Both declined before
## (`hasBreakContinueShallow`).
import std/[unittest, options, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

const
  nanK = cellKey(axPragma, "routine/nanChecks")
  ints = sampled([0, 1, 2, 3, -1, 5])

iterator upto(n: int): int {.inline.} =
  var i = 0
  while i < n:
    yield i
    inc i

iterator four(n: int): int {.inline.} =
  yield n
  yield n + 1
  yield n + 2
  yield n + 3

iterator twice(n: int): int {.inline.} =
  for i in upto(n): yield i * 2

iterator stopAt2(n: int): int {.inline.} =
  for i in upto(n):
    if i == 2: break
    yield i

proc sutBreakWhile(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in upto(k):
    if x == 3: break
    s += x
  if s == 3: symexTarget("hit")

proc sutBreakFinite(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in four(k):
    if x == 3: break
    s += x
  if s == 3 and k == 0: symexTarget("hit")

proc sutContinue(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in upto(k):
    if x mod 2 == 0: continue
    s += x
  if s == 4: symexTarget("hit")

proc sutContinueFinite(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in four(k):
    if x mod 2 == 0: continue
    s = s * 10 + x
  if s == 13: symexTarget("hit")

proc sutLabelled(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  block search:
    for x in four(k):
      for y in four(k):
        if x * y == 6: break search
        s += 1
  if s == 11 and k == 0: symexTarget("hit")

proc sutNestedBody(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in twice(k):
    if x == 4: break
    s += x
  if s == 2: symexTarget("hit")

proc sutBreakInIter(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  var c = 0
  for x in stopAt2(k):
    s += x
    inc c
  if s == 1 and c == 2: symexTarget("hit")

proc sutBreakInner(k: int) =
  ## the caller's `break` leaves the expansion, not its own `while`'s loop
  ## twice: code after the loop runs once
  if k < 0 or k > 100: return
  var after = 0
  for x in upto(k):
    if x == 1: break
  after += 1
  if after == 1 and k == 3: symexTarget("hit")

proc sutContinueIn(k: int) =
  ## a `continue` of the caller's own inner loop stays its own
  if k < 0 or k > 100: return
  var s = 0
  for x in upto(k):
    for j in 0 ..< 3:
      if j == 1: continue
      s += 1
    if x == 1: break
  if s == 4 and k == 5: symexTarget("hit")

template decided(body: untyped) =
  if hostAdmission().isSome: skipUnadmitted() else: body

template sat(sut: untyped, call: untyped, key: CellKey) =
  ## Filed under the construct cell (`for/inlineIter/*`) and under the
  ## routine float-check cell the expansion reads (P7: the iterator's body is
  ## the routine's own).
  decided:
    check native(call) == "hit"
    let r = pinExact(sut, key, target = tLabel("hit"), domain = ints)
    check r.status == sxSat
    discard pinExact(sut, nanK, target = tLabel("hit"), domain = ints)

suite "W3-z P13: break / continue in an inline-iterator for-body":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 317
  test "break over a while iterator": sat(sutBreakWhile, sutBreakWhile(5), cellKey(axConstruct, "for/inlineIter/break"))
  test "break over a finite iterator": sat(sutBreakFinite, sutBreakFinite(0), cellKey(axConstruct, "for/inlineIter/break"))
  test "continue over a while iterator": sat(sutContinue, sutContinue(5), cellKey(axConstruct, "for/inlineIter/continue"))
  test "continue over a finite iterator": sat(sutContinueFinite, sutContinueFinite(0), cellKey(axConstruct, "for/inlineIter/continue"))
  test "labelled block break out of a nested iterator for":
    sat(sutLabelled, sutLabelled(0), cellKey(axConstruct, "for/inlineIter/labelledBreak"))
  test "break in the body of a nested iterator's caller":
    sat(sutNestedBody, sutNestedBody(5), cellKey(axConstruct, "for/inlineIter/break"))
  test "break inside a nested iterator": sat(sutBreakInIter, sutBreakInIter(5), cellKey(axConstruct, "for/inlineIter/break"))
  test "break leaves the expansion once": sat(sutBreakInner, sutBreakInner(3), cellKey(axConstruct, "for/inlineIter/break"))
  test "a caller's inner loop keeps its own continue":
    sat(sutContinueIn, sutContinueIn(5), cellKey(axConstruct, "for/inlineIter/continue"))
