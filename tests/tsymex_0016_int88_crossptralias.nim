## RFC-0016 INT-88 (witness fidelity; the verdict is sound): two `ptr`
## parameters of different pointee types that the target needs at one address
## are a trusted `sxSat`, which is right (a caller can pass `addr x` and
## `cast[ptr float](addr x)`), but the walker's witness builds a cell for each,
## at two addresses, so it replays natively without reaching the target.
## Found verifying the plan's "non-nil pointer compare across types" entry
## (K9d-12), which INT-83 was thought to have closed: INT-83 made `pointer` an
## address of its own sort; two typed `ptr`s that must share one are not
## materialised as one cell.
##
## The bar: the witness holds one cell at both positions, so the pin replays it
## and the target is hit. Two refs of different types never alias (the
## control: `sxUnsat`, pinned over the ref domains).
## Unregistered while red (`tests/0016-allowlist/ids.txt`).
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

proc crossPtr(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    symexTarget("hit")

proc crossRef(a: ref int; b: ref float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    symexTarget("hit")

suite "INT-88: a cross-type ptr alias witness":
  test "natively: one address passed as both reaches the target":
    var x = 0
    check nativeRun(crossPtr(addr x, cast[ptr float](addr x))).hitsTarget(
      tLabel("hit"))

  test "the walker's sat witness replays":
    let r = pinFind(crossPtr, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "two refs of different types never alias (the control)":
    check pinFind(crossRef, tLabel("hit")).status == sxUnsat

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 444
