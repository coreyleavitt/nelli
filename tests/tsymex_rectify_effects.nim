## Rectify #137 — effect tracking for opaque IO procs.
##
## Calls to known-effectful procs (echo, write, etc.) are modelled as
## opaque: the body is not walked, the return is a fresh-symbolic
## value, and the path is marked uncertain. A target reached only on
## such a path degrades to `sxUnknown` rather than emitting an
## unsound witness.
import std/unittest
import nelli/symex

suite "symex effects #137":
  test "echo on a path makes the path uncertain":
    proc withSideEffect(x: int) =
      if x > 5:
        echo "diagnostic"
        symexTarget("reach")
    let r = symexFind(withSideEffect, tLabel("reach"))
    check r.status == sxUnknown

  test "user proc that calls echo propagates uncertainty to caller":
    proc innerEffect(y: int) =
      echo "from inner"
    proc outer(x: int) =
      if x > 5:
        innerEffect(x)
        symexTarget("reach")
    let r = symexFind(outer, tLabel("reach"))
    check r.status == sxUnknown

  test "no echo on the only reaching path → sxSat as before":
    proc pure(x: int) =
      if x > 5:
        symexTarget("clean")
    let r = symexFind(pure, tLabel("clean"))
    check r.status == sxSat
    check r.witness[0] > 5
