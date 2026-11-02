## RFC-0005 (soundness channels) slice S8bk -- address-of-argument timing.
##
## Nim takes the address of a `var` (or `addr`) actual AT THE CALL, after
## every later argument has been evaluated: `touch(gP.x, moveP())` compiles
## to `T1_ = moveP(); touch(&(*gP).x, T1_);`, so when `moveP` rebinds `gP`
## the callee reads and writes the NEW object. Only the address's own checks
## (an index's bound) run where the argument stands. The walk read the value
## early (copy-in, S8an's `addr` cell, S8bd's by-reference element base) and
## wrote it back through the late address: a false `sxSat` for every dead
## label below.
##
## Pinned here (the RFC's "As landed (S8bk)" note has the design): the
## native semantics (probed on c and cpp), copy-in/out through a rebound
## ref, a field-of-field chain rebound partway, and an element the later
## call writes. RFC-0005 S8br split the suite so each file compiles and runs
## under 60 s on each backend: `_addr` has the `addr` and by-reference
## actuals, `_checks` a `var` formal forwarded on, the declines where a later
## call changes what an address check read (Nim then accesses through a
## value it never checked), and the calls through a proc value. The fixture
## is `s8bk_argtiming_fixture`.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

include s8bk_argtiming_fixture

suite "S8bk: a var / addr actual's address is taken at the call":

  test "nim":
    gP = Box(x: 10)
    var old = gP
    touch(gP.x, moveP())
    check old.x == 10 and gP.x == 105
    gP = Box(x: 10)
    old = gP
    touch(gP.x, writeOld())
    check old.x == 50 and gP.x == 105
    gO = Outer(inner: Box(x: 10))
    old = gO.inner
    touch(gO.inner.x, moveInner())
    check old.x == 10 and gO.inner.x == 105
    gArr = [10, 20, 30]
    touch(gArr[0], bumpArr())
    check gArr[0] == 55
    gs = @[10, 20, 30]
    touch(gs[0], bumpS())
    check gs[0] == 55
    gP = Box(x: 10)
    old = gP
    check touchB(gP.x, moveP())
    check old.x == 10 and gP.x == 105

  test "copy-in / copy-out through a rebound ref":
    ## RED: `cp` unreached, `cp_dead` a false `sxSat` (the copy-in read the
    ## old object, the copy-out wrote the new).
    replays(sutCopy, "cp")
    discard verdict(sutCopy, "cp_dead", sxUnsat)
    replays(sutCopyOld, "co")
    discard verdict(sutCopyOld, "co_dead", sxUnsat)
    replays(sutGuard, "gd")
    discard verdict(sutGuard, "gd_dead", sxUnsat)

  test "a field-of-field chain rebound partway":
    replays(sutChain, "ch")
    discard verdict(sutChain, "ch_dead", sxUnsat)

  test "an element the later call writes":
    replays(sutArr, "ar")
    discard verdict(sutArr, "ar_dead", sxUnsat)
    replays(sutSeq, "sq")
    discard verdict(sutSeq, "sq_dead", sxUnsat)

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 212
