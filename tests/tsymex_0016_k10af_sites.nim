## RFC-0016 K10a-float follow-up: every undefined-behaviour finding names its
## own source site. Two float -> int conversions in one SUT used to share the
## one string "float -> int conversion", so the second collapsed into the
## first (`haltUndefined` lists one finding per kind and site) and a user
## could not tell which conversion was undefined.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

proc sutTwo(a, b: float) =
  let x = int(a)
  let y = int(b)
  if x == 1 and y == 2: symexTarget("hit")

proc sutSecondOnly(a, b: float) =
  var x = 0
  if a > -1000.0 and a < 1000.0:
    x = int(a)
  let y = int(b)
  if x == 1 and y == 2: symexTarget("hit")

proc sutLoop(a: float) =
  let x = int(a)
  if x == 1: symexTarget("hit")

proc lineOf(site: string): int =
  ## `file:line:col` at the end of a site.
  let parts = site.rsplit(':', 2)
  parseInt(parts[^2])

suite "K10a-float: one site per undefined conversion":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 294

  test "two conversions give two findings with distinct sites":
    let r = symexFind(sutTwo, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 2
    if r.undefined.len == 2:
      check r.undefined[0].site != r.undefined[1].site
      for u in r.undefined:
        check u.kind == UbKind(ubFloatToIntRange)
        check "tsymex_0016_k10af_sites" in u.site
      check lineOf(r.undefined[0].site) != lineOf(r.undefined[1].site)
      check {lineOf(r.undefined[0].site), lineOf(r.undefined[1].site)} ==
            {13, 14}

  test "only the second can go out of range: the one finding names it":
    let r = symexFind(sutSecondOnly, tLabel("hit"))
    checkpoint show(r.errors)
    check r.undefined.len == 1
    if r.undefined.len == 1:
      check lineOf(r.undefined[0].site) == 21
      check "tsymex_0016_k10af_sites" in r.undefined[0].site

  test "a single conversion still has one named site":
    let r = symexFind(sutLoop, tLabel("hit"))
    check r.undefined.len == 1
    check "tsymex_0016_k10af_sites" in r.undefined[0].site
