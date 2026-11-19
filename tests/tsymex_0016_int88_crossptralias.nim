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
## Fixed in the witness builder: the snapshot keys a typed address the run
## cast into the `pointer` space by its `pointer` address (`addrSpaceKey`),
## so the two positions are one cell, built once as its owner's type and
## sized for the largest pointee holding it (`registerPtrSize`); the other
## position is a typed view of that allocation. A cell whose shared bytes
## the model's per-sort heaps cannot render as one is marked lossy.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

proc crossPtr(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    symexTarget("hit")

proc crossPtrRead(a: ptr int; b: ptr float) =
  # one sort's content constrained: the cell is that sort's, the other a view
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 5:
    symexTarget("hit")

proc crossPtrViewFirst(b: ptr float; a: ptr int) =
  # the view comes first in parameter order and by name: the owner is still
  # the constrained sort, and the view built first is its allocation
  if a != nil and b != nil and cast[pointer](b) == cast[pointer](a) and
     a[] == 7:
    symexTarget("hit")

proc crossPtrWide(a: ptr int8; b: ptr int64) =
  # the owner's pointee is narrower than the view's: one allocation, sized
  # for the wider
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 3:
    symexTarget("hit")

proc crossPtrBoth(a: ptr int; b: ptr float) =
  # both sorts constrained at one address: no bytes hold `5` as an int and a
  # float above 1.0, and the model's two heaps say otherwise
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 5 and b[] > 1.0:
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

  test "one constrained sort: the cell is filled from it":
    let r = pinFind(crossPtrRead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "the view first in parameter order":
    let r = pinFind(crossPtrViewFirst, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "a narrower owner than its view":
    let r = pinFind(crossPtrWide, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "both sorts constrained: never a trusted sat witness":
    # natively unreachable; a sat the model's two heaps make is lossy, so the
    # replay settles it and it is never trusted
    let r = symexFind(crossPtrBoth, tLabel("hit"))
    checkpoint show(r.errors)
    check not (r.status == sxSat and r.trusted)

  test "two refs of different types never alias (the control)":
    check pinFind(crossRef, tLabel("hit")).status == sxUnsat

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 444
