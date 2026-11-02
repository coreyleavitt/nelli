## RFC-0005 (soundness channels) slice S8bk -- address-of-argument timing:
## `addr` actuals (S8an's cell, and by reference) and by-reference actuals
## (S8ba / S8bd: a symbol base, an element base, a call base). Split out of
## `tsymex_rfc0005_s8bk_argtiming` by RFC-0005 S8br, so each file compiles
## and runs under 60 s on each backend; that file's header has the subject.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

include s8bk_argtiming_fixture

suite "S8bk: addr and by-reference actuals take the address at the call":

  test "nim":
    gP = Box(x: 10)
    var old = gP
    touchP(addr gP.x, moveP())
    check old.x == 10 and gP.x == 105
    gP = Box(x: 10)
    old = gP
    touchPG(addr gP.x, moveP())
    check old.x == 10 and gP.x == 105
    gArr = [10, 20, 30]
    gi = 0
    touchP(addr gArr[gi], bumpArr())
    check gArr[0] == 55
    gP = Box(x: 10)
    old = gP
    touchG(gP.x, moveP())
    check old.x == 10 and gP.x == 105
    gP = Box(x: 10)
    old = gP
    gCalls = 0
    touchG(getB().x, moveP())
    check old.x == 15 and gP.x == 100 and gCalls == 1
    gA = [Box(x: 10), Box(x: 20), Box(x: 30)]
    old = gA[0]
    gi = 0
    touchG(gA[gi].x, moveA0())
    check old.x == 10 and gA[0].x == 105

  test "an addr actual":
    ## RED: `ad` unreached, `ad_dead` a false `sxSat` (S8an's cell was
    ## filled from the old object).
    discard verdict(sutAddr, "ad", sxSat)
    discard verdict(sutAddr, "ad_dead", sxUnsat)
    discard verdict(sutAddrRef, "ar2", sxSat)
    discard verdict(sutAddrRef, "ar2_dead", sxUnsat)
    discard verdict(sutAddrIdx, "ai", sxSat)
    discard verdict(sutAddrIdx, "ai_dead", sxUnsat)
    declines(sutAddrIdxMoved, "am")

  test "by reference: a symbol base, an element base, a call base":
    replays(sutRefSym, "rs")
    discard verdict(sutRefSym, "rs_dead", sxUnsat)
    replays(sutRefElem, "re")
    discard verdict(sutRefElem, "re_dead", sxUnsat)
    replays(sutRefCall, "rc")
    discard verdict(sutRefCall, "rc_dead", sxUnsat)
