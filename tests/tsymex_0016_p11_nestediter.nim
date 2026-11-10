## RFC-0016 W3-z P11: an inline iterator called from inside another inline
## iterator's body.
##
## `for i in inner(n): yield i*2` in an iterator's body declined
## (`feUnsupportedStmtKind`): the inner loop's body is the OUTER `yield`, which
## no handler answered. Natively it is ordinary Nim. Each `yield` binds to the
## loop of the iterator whose body holds it: the inner one to the inner loop's
## body, the outer one to the caller's.
import std/[unittest, options, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

const
  nanK = cellKey(axPragma, "routine/nanChecks")
  ints = sampled([0, 1, 2, 3, -1, 5])

iterator inner(n: int): int {.inline.} =
  yield n
  yield n + 1

iterator outer(n: int): int {.inline.} =
  for i in inner(n): yield i * 2

iterator outerBrk(n: int): int {.inline.} =
  for i in inner(n):
    for j in 0 ..< 3:
      if j == 2: break
      yield i * 10 + j

iterator outerTop(n: int): int {.inline.} =
  for i in outerBrk(n): yield i + 1

proc sutNest(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in outer(k): s += x
  if s == 10: symexTarget("hit")

proc sutNestOrder(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in outer(k): s = s * 100 + x
  if s == 406: symexTarget("hit")

proc sutBreak(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  var c = 0
  for x in outerBrk(k):
    s += x
    inc c
  if s == 102 and c == 4: symexTarget("hit")

proc sutThree(k: int) =
  if k < 0 or k > 100: return
  var s = 0
  for x in outerTop(k): s += x
  if s == 106: symexTarget("hit")

iterator fdiv(n: int): bool {.inline.} =
  let z = float(n)
  yield z / z != z / z

iterator fouter(n: int): bool {.inline.} =
  for b in fdiv(n): yield b

{.push nanChecks: on.}
proc sutPushed(n: int) =
  for b in fouter(n):
    if b: symexTarget("hit")
{.pop.}

proc sutDefault(n: int) =
  var touch = 1.0
  touch += 1.0
  for b in fouter(n):
    if b: symexTarget("hit")

template decided(body: untyped) =
  if hostAdmission().isSome: skipUnadmitted() else: body

suite "W3-z P11: an inline iterator inside an inline iterator":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 316

  test "one level of nesting":
    decided:
      check native(sutNest(2)) == "hit"
      let r = pinExact(sutNest, nanK, target = tLabel("hit"), domain = ints)
      check r.status == sxSat

  test "the yields keep their order":
    decided:
      check native(sutNestOrder(2)) == "hit"
      let r = pinExact(sutNestOrder, nanK, target = tLabel("hit"), domain = ints)
      check r.status == sxSat

  test "a break in the outer iterator's own loop":
    decided:
      check native(sutBreak(2)) == "hit"
      let r = pinExact(sutBreak, nanK, target = tLabel("hit"), domain = ints)
      check r.status == sxSat

  test "three levels":
    decided:
      check native(sutThree(2)) == "hit"
      let r = pinExact(sutThree, nanK, target = tLabel("hit"), domain = ints)
      check r.status == sxSat

  test "the inner iterator takes the caller's options: pushed":
    decided:
      check native(sutPushed(0)) == "FloatInvalidOpDefect"
      let r = pinExact(sutPushed, nanK, target = tRaisedExn("FloatInvalidOpDefect"),
                       domain = ints)
      check r.status == sxRaised

  test "the inner iterator takes the caller's options: default":
    decided:
      let nat = native(sutDefault(0))
      checkpoint nat
      let r = pinExact(sutDefault, nanK, target = tLabel("hit"), domain = ints)
      if nat == "hit": check r.status == sxSat
      else: check r.status != sxSat
