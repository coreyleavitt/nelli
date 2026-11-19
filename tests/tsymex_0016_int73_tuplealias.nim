## RFC-0016 INT-73 -- a conversion to an alias of an anonymous tuple type
## (`type TE = (D, int)`, then `TE((D(v: k), 5))`) aborted the compile:
## the alias classified `__unsupported` and the tuple constructor's
## `mkTupleLit` asserted an `itTuple`. The alias is the tuple (a tuple is
## structural), as a named one (`tuple[x, y: int]`) already was.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

type DL9 = object
  v: int
type TE9 = (DL9, int)
type TN9 = (int, (DL9, int))
proc f9(k: int): int =
  let t = TE9((DL9(v: k), 5))
  t[0].v + t[1]
proc g9(k: int): int =
  let t: TN9 = (k, (DL9(v: k * 2), 1))
  t[0] + t[1][0].v + t[1][1]
proc aliasConv(k: int) =
  if k > 100 or k < -100: return
  if f9(k) == 8: symexTarget("hit")
proc aliasConvNever(k: int) =
  if k > 100 or k < -100: return
  if f9(k) == k: symexTarget("hit")
proc aliasNested(k: int) =
  if k > 100 or k < -100: return
  if g9(k) == 13: symexTarget("hit")
proc aliasNestedNever(k: int) =
  if k > 100 or k < -100: return
  if g9(k) == 3 * k: symexTarget("hit")

const idom = sampled([0, 1, 2, 3, 4, -42, 42])
let tCell = cellKey(axTypeClass, "tuple")

suite "INT-73":
  test "a conversion to an anonymous tuple's alias":
    check native(aliasConv(3)) == "hit"
    check pinExact(aliasConv, tCell, domain = idom).status == sxSat
    check pinExact(aliasConvNever, tCell, domain = idom).status == sxUnsat
  test "an alias holding another tuple":
    check native(aliasNested(4)) == "hit"
    check pinExact(aliasNested, tCell, domain = idom).status == sxSat
    check pinExact(aliasNestedNever, tCell, domain = idom).status == sxUnsat
