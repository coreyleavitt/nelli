## RFC-0016 WA-A (wiring audit, Wave 1). Builds with `--overflowChecks:off`
## (its `.nim.cfg`).
##
##   S1  a `for` over a closure iterator, in a checks-off build: the loop is
##       walked, not dropped (a label inside it was a trusted `sxUnsat`).
##   S2  `inc` / `dec` / `succ` / `pred` / `+=` on an enum, `char` or range:
##       native Nim raises the ordinal range check only under overflow checks,
##       so unchecked it neither raises nor is the out-of-range side pruned.
##   P2  a routine pushed `overflowChecks: on` in this build is checked, magic
##       bodies (`abs`) included; a closure iterator keeps its own scope.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type Col = enum cRed, cGreen, cBlue
type Small = range[0 .. 3]

iterator twoElems(): int {.closure.} =
  yield 1
  yield 2

iterator countUp(n: int): int {.closure.} =
  var i = 0
  while i < n:
    yield i
    inc i

proc sutClosureLoop(k: int) =
  for x in twoElems():
    if x == 2: symexTarget("hit")

proc sutClosureWhile(n: int) =
  for x in countUp(n):
    if x == 1: symexTarget("hit")

proc sutIncEnum(k: int) =
  if k == 1:
    var e = cBlue
    inc e
    symexTarget("hit")

proc sutDecEnum(k: int) =
  if k == 1:
    var e = cRed
    dec e
    symexTarget("hit")

proc sutSuccEnum(k: int) =
  if k == 1:
    let e = succ(cBlue)
    discard e
    symexTarget("hit")

proc sutPlusEqRange(k: int) =
  if k == 1:
    var r: Small = 3
    r += 1
    symexTarget("hit")

proc sutIncInRange(k: int) =
  ## Fully in range: unaffected.
  if k == 1:
    var e = cRed
    inc e
    if e == cGreen: symexTarget("hit")

{.push overflowChecks: on.}
proc sutAbsPushed(v: int) =
  if v == low(int):
    let a = abs(v)
    if a < 0: symexTarget("hit")

proc sutIncEnumPushed(k: int) =
  if k == 1:
    var e = cBlue
    inc e
    symexTarget("hit")
{.pop.}

{.push overflowChecks: on.}
iterator checkedIter(): int {.closure.} =
  yield 1
{.pop.}

proc sutCheckedIterFromBuild(k: int) =
  for x in checkedIter():
    if x == 1: symexTarget("hit")

suite "WA-A checks-off build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 285

  test "the build is checks-off":
    check buildWraps()

  test "S1 native: the closure loop runs":
    check native(sutClosureLoop(0)) == "hit"
    check native(sutClosureWhile(3)) == "hit"

  test "S1: a closure-iterator loop is walked, its label is sat":
    let r = symexFind(sutClosureLoop, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted

  test "S1: a while-driven closure iterator loop is walked":
    let r = symexFind(sutClosureWhile, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted

  test "S2 native: unchecked ordinal steps do not raise":
    check native(sutIncEnum(1)) == "hit"
    check native(sutDecEnum(1)) == "hit"
    check native(sutSuccEnum(1)) == "hit"
    check native(sutPlusEqRange(1)) == "hit"

  test "S2: the out-of-range step declines, it is not pruned or raised":
    template declinesOp(f: untyped) =
      let r = symexFind(f, tLabel("hit"))
      checkpoint show(r.errors)
      check r.status == sxUnknown
      check r.errors.named(feUnsupportedOp)
    declinesOp(sutIncEnum)
    declinesOp(sutDecEnum)
    declinesOp(sutSuccEnum)
    declinesOp(sutPlusEqRange)

  test "S2: an in-range step is exact":
    let r = symexFind(sutIncInRange, tLabel("hit"))
    check r.status == sxSat
    check r.trusted

  test "S2: a routine pushed overflowChecks: on still raises OverflowDefect":
    check native(sutIncEnumPushed(1)) == "OverflowDefect"
    let r = pinExact(sutIncEnumPushed, cellKey(axDefinedness, "ordStep/pushOn"))
    check r.status == sxRaised

  test "P2 native: abs(low(int)) in a pushed-on routine raises":
    check native(sutAbsPushed(low(int))) == "OverflowDefect"

  test "P2: abs in a pushed-on routine is checked":
    let r = pinExact(sutAbsPushed, cellKey(axDefinedness, "abs/pushOn"))
    check r.status == sxRaised

  test "P2: a checked closure iterator called from the build scope is not walked unchecked":
    let r = symexFind(sutCheckedIterFromBuild, tLabel("hit"))
    checkpoint show(r.errors)
    # inlined it would be walked under the caller's unchecked arithmetic, not
    # the one it is compiled with: it declines.
    check r.status == sxUnknown
    check r.errors.named(feCheckOption)
