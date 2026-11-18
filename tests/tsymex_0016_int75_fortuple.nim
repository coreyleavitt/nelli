## RFC-0016 INT-75 -- a `for` destructuring its loop variable in parentheses
## (`for (a, b) in it(k)`) failed the walker's parse at compile time: the
## typed tree holds one `nnkVarTuple` where the flat form (`for a, b in`)
## holds one symbol per name, and the `for` arm asserted a symbol
## (`iterVar.expectKind nnkSym`). `for i, (a, b) in pairs(s)` failed the
## same way on its second variable. A user's program is never a compile
## error: each shape is modelled or declined by name.
##
## In the typed tree the iterator is already resolved (`items(st)`,
## `pairs(s)`, the user's call), so `for (a, b) in X` binds exactly what
## `for a, b in X` binds: each name to its component of each yielded tuple.
## `fieldPairs` admits no parenthesised form (native: "wrong number of
## variables"), so it has none to model.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

iterator it(k: int): (int, int) =
  yield (k, 1)
  yield (k + 1, 2)
iterator it3(k: int): (int, int, int) =
  yield (k, 1, 2)
iterator itc(k: int): (int, int) {.closure.} =
  yield (k, 3)
  yield (k * 2, 4)

proc u1(k: int): int =
  for (a, b) in it(k): result += a * 10 + b
proc u2(k: int): int =
  for a, b in it(k): result += a * 10 + b
proc u3(k: int): int =
  for (a, b, c) in it3(k): result += a * 100 + b * 10 + c
proc p1(k: int): int =
  let s = @[k, k + 1, 7]
  for (i, x) in pairs(s): result += i * 100 + x
proc p2(k: int): int =
  let s = [k, 2 * k]
  for (i, x) in s.pairs: result += i * 100 + x
proc i1(k: int): int =
  let st = @[(k, 2), (3, k)]
  for (a, b) in st: result += a * b
proc i2(k: int): int =
  let st = [(k, 2), (3, 4)]
  for (a, b) in st: result += a + b * 10
proc n1(k: int): int =
  let st = @[(k, 2), (3, 4)]
  for i, (a, b) in pairs(st): result += i * 100 + a + b
proc c1(k: int): int =
  for (a, b) in itc(k): result += a + b * 10

template pair(name, neverName: untyped; call, hitV, neverV: untyped) =
  proc name(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == hitV: symexTarget("hit")
  proc neverName(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == neverV: symexTarget("hit")
pair(eU1, eU1Never, u1(k), 20 * k + 13, 20 * k + 23)
pair(eU2, eU2Never, u2(k), 20 * k + 13, 20 * k + 23)
pair(eU3, eU3Never, u3(k), 100 * k + 12, 100 * k + 21)
pair(eP1, eP1Never, p1(k), 2 * k + 308, 2 * k + 8)
pair(eP2, eP2Never, p2(k), 3 * k + 100, 3 * k)
pair(eI1, eI1Never, i1(k), 5 * k, 5 * k + 1)
pair(eI2, eI2Never, i2(k), k + 63, k + 36)
pair(eN1, eN1Never, n1(k), k + 109, k + 9)
pair(eC1, eC1Never, c1(k), 3 * k + 70, 3 * k)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let tCell = cellKey(axTypeClass, "tuple")
template exact(hitP, neverP: untyped) =
  check pinExact(hitP, tCell, domain = idom).status == sxSat
  check pinExact(neverP, tCell, domain = idom).status == sxUnsat

suite "INT-75":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 433
  test "native truth":
    for e in [eU1, eU2, eU3, eP1, eP2, eI1, eI2, eN1, eC1]:
      for k in [-42, 0, 1, 2, 3]:
        check native(e(k)) == "hit"
  test "a user iterator's tuple, destructured":
    exact(eU1, eU1Never)
    exact(eU2, eU2Never)
    exact(eU3, eU3Never)
  test "`pairs` destructured":
    exact(eP1, eP1Never)
    exact(eP2, eP2Never)
  test "`items` over a container of tuples, destructured":
    exact(eI1, eI1Never)
    exact(eI2, eI2Never)
  test "a nested destructuring under `pairs`":
    exact(eN1, eN1Never)
  test "a closure iterator's tuple, destructured":
    exact(eC1, eC1Never)
