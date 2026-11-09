## RFC-0016 K10a-float follow-up, the arithmetic traps. Built with
## `--overflowChecks:off` (its `.nim.cfg`): a signed `+`, `-` or `*` is
## undefined on overflow. Each such op names its own source site, so two
## overflowing ops in one SUT are two findings, not one collapsed under the
## construct's name.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc sutTwo(a, b: int) =
  let x = a + 1
  let y = b * 2
  if x == 5 and y == 6: symexTarget("hit")

proc sutSecondOnly(a, b: int) =
  var x = 0
  if a > 0 and a < 100:
    x = a + 1
  let y = b - 1
  if x == 5 and y == 6: symexTarget("hit")

proc lineOf(site: string): int =
  let parts = site.rsplit(':', 2)
  parseInt(parts[^2])

suite "K10a-float: one site per undefined arithmetic op":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 300

  test "two overflowing ops give two findings with distinct sites":
    let r = symexFind(sutTwo, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {13, 14}
      for u in r.undefined:
        check u.kind == UbKind(ubSignedOverflow)

  test "only the second can overflow: the one finding names it":
    let r = symexFind(sutSecondOnly, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 1
    if r.undefined.len == 1:
      check lineOf(r.undefined[0].site) == 21

proc sutTwoPlusEq(a, b: int) =
  var x = a
  var y = b
  x += 1
  y += 2
  if x == 5 and y == 6: symexTarget("hit")

proc sutTwoInc(a, b: int) =
  var x = a
  var y = b
  inc x
  inc y, 2
  if x == 5 and y == 6: symexTarget("hit")

suite "K10a-float: rebuilt binops keep their source site":
  test "two `+=` give two findings with distinct sites":
    let r = symexFind(sutTwoPlusEq, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {52, 53}
  test "two `inc` give two findings with distinct sites":
    let r = symexFind(sutTwoInc, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {59, 60}

type Cnt = distinct int
proc `+`(a, b: Cnt): Cnt {.borrow.}

proc sutTwoNeg(a, b: int) =
  let x = -a
  let y = -b
  if x == 5 and y == 6: symexTarget("hit")

proc sutTwoBorrow(a, b: int) =
  let x = Cnt(a) + Cnt(1)
  let y = Cnt(b) + Cnt(2)
  if int(x) == 5 and int(y) == 6: symexTarget("hit")

suite "K10a-float: negation and borrow keep their source site":
  test "two negations give two findings with distinct sites":
    let r = symexFind(sutTwoNeg, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check r.undefined[0].site.len > 0
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {83, 84}
      for u in r.undefined:
        check u.kind == UbKind(ubSignedOverflow)
  test "two borrowed `+` give two findings with distinct sites":
    let r = symexFind(sutTwoBorrow, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check r.undefined[0].site.len > 0
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {88, 89}
