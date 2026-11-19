## RFC-0016 INT-90 (precision): two `ptr` parameters of different pointee
## types at one address (`a: ptr int`, `b: ptr float`,
## `cast[pointer](a) == cast[pointer](b)`) hold one cell's bytes, but the walk
## keeps a separate heap per pointee sort and does not relate them at a shared
## address. `a[] == 5 and b[] > 1.0` is natively unreachable (the int 5's bits
## read as a float are a subnormal far below 1.0), yet the walker answers an
## untrusted, lossy `sxSat` (INT-88 marks the witness lossy, so the replay
## settles it) instead of `sxUnsat`. Left by INT-88, whose witness builder
## made the shared cell one allocation.
##
## The bar: the cross-sort target is `sxUnsat`, pinned natively by pinFind
## over the `ptr` domains (which put the two parameters at one address).
## Red until the walk relates two sorts' heaps at one address; not
## registered, and listed in `tests/0016-allowlist/ids.txt`.
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc crossSortHeap(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 5 and b[] > 1.0:
    symexTarget("hit")

proc crossSortAlias(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    symexTarget("hit")

suite "INT-90: two sorts' heaps at one address":
  test "natively: the int 5 read as a float is no float above 1.0":
    var x = 5
    let a = addr x
    let b = cast[ptr float](addr x)
    check cast[pointer](a) == cast[pointer](b)
    check a[] == 5
    check not (b[] > 1.0)

  test "the alias alone is reachable (the control)":
    check pinFind(crossSortAlias, tLabel("hit")).status == sxSat

  test "a value at one sort constrains the other sort's read":
    let r = pinFind(crossSortHeap, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
