## RFC-0016 PRC-45 -- the `=dup` sink positions PRC-44 left declining.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

# Order independence: each type below is first named by a different entry,
# so whether that entry stages the hook probes decides its verdict.
type OCov = object
  v: int
proc `=dup`(x: OCov): OCov = OCov(v: x.v + 1)
proc ocTake(x: sink OCov): int = x.v
proc oCov(k: int) =
  let a = OCov(v: k)
  if ocTake(a) * 1000 + a.v == 2001: symexTarget("hit")

type OAll = object
  v: int
proc `=dup`(x: OAll): OAll = OAll(v: x.v + 1)
proc oaTake(x: sink OAll): int = x.v
proc oAll(k: int) =
  let a = OAll(v: k)
  if oaTake(a) * 1000 + a.v == 2001: symexTarget("hit")

type OFind = object
  v: int
proc `=dup`(x: OFind): OFind = OFind(v: x.v + 1)
proc ofTake(x: sink OFind): int = x.v
proc oFind(k: int) =
  let a = OFind(v: k)
  if ofTake(a) * 1000 + a.v == 2001: symexTarget("hit")

# A sink position and an `except` branch. Natively (Nim 2.2.10, c and cpp,
# the compiler's graph: `dfa.genTry`) a call in a `try` body that may raise,
# and the body's end, reach every `except` branch, and no branch reaches
# another. Each target below holds only where the hook ran (`r - k == 1`).
type DObj = object
  v: int
proc `=dup`(x: DObj): DObj = DObj(v: x.v + 1)
proc dTake(x: sink DObj): int = x.v
proc dMayRaise(k: int) =
  if k == 99: raise newException(ValueError, "x")
proc eExcept(k: int) =
  # The site in the body, its source read only in the `except` branch.
  if k > 1000: return   # the hook's `+ 1` raises at high(int)
  let a = DObj(v: k)
  var r = 0
  try:
    r = dTake(a)
    dMayRaise(k)
  except ValueError:
    r = a.v + 1000
  if r - k == 1: symexTarget("hit")
proc eExceptNever(k: int) =
  if k > 1000: return
  let a = DObj(v: k)
  var r = 0
  try:
    r = dTake(a)
    dMayRaise(k)
  except ValueError:
    r = a.v + 1000
  if r == k: symexTarget("hit")
proc eReturn(k: int) =
  # A `return` after the site: the site's own call reaches the branch.
  if k > 1000: return
  let a = DObj(v: k)
  try:
    if dTake(a) - k == 1: symexTarget("hit")
    return
  except ValueError:
    if a.v == -5: symexTarget("other")
proc eBefore(k: int) =
  # The site before a `try` whose body cannot raise: its end reaches the branch.
  if k > 1000: return
  let a = DObj(v: k)
  let r = dTake(a)
  var z = 0
  try:
    z = 1
  except ValueError:
    z = a.v
  if r - k == 1 and z == 1: symexTarget("hit")
proc eFinally(k: int) =
  # Read only in a `finally`.
  if k > 1000: return
  let a = DObj(v: k)
  var r = 0
  try:
    r = dTake(a)
  finally:
    if a.v == -5: r = 0
  if r - k == 1: symexTarget("hit")
proc eSibling(k: int) =
  # The site in one `except` branch, the read in another: no path, the move.
  let a = DObj(v: k)
  var r = 0
  try:
    dMayRaise(k)
  except ValueError:
    r = dTake(a)
  except IOError:
    r = a.v + 1000
  if r == k and k == 99: symexTarget("hit")
proc eEarlyReturn(k: int) =
  # No path from the site to the later read (PRC-44's declining pin): the move.
  let a = DObj(v: k)
  if k > 0:
    if dTake(a) == 1: symexTarget("hit")
    return
  if a.v == 7: symexTarget("other")

# The source a parameter or a `{.cursor.}` local. Natively a parameter that is
# not `sink` (a `var` one too) is copied at every sink position, its last read
# or not; a `sink` parameter on its last read moves.
proc pPlain(a: DObj): int = dTake(a)
proc pVar(a: var DObj): int = dTake(a)
proc pSink(a: sink DObj): int = dTake(a)
# A `sink` parameter read after the site: natively (c and cpp) the compiler
# copies it only when its `sink T` type has a destructor, which a routine's
# own `sink T` has only when T's destructor is not trivial. `DObj`'s is
# trivial: no hook, the value read after is the one passed. `DStr` holds a
# `string`: the hook runs.
type DStr = object
  v: int
  s: string
proc `=dup`(x: DStr): DStr = DStr(v: x.v + 1, s: x.s)
proc dTakeStr(x: sink DStr): int = x.v
proc pSinkRead(a: sink DObj): int = dTake(a) * 1000 + a.v
proc pSinkStrRead(a: sink DStr): int = dTakeStr(a) * 1000 + a.v
proc pSinkReadSite(k: int) =
  if k > 1000 or k < -1000: return
  if pSinkRead(DObj(v: k)) == 1001: symexTarget("hit")
proc pSinkReadNever(k: int) =
  if k > 1000 or k < -1000: return
  if pSinkRead(DObj(v: k)) == 2001: symexTarget("hit")
proc pSinkStrSite(k: int) =
  if k > 1000 or k < -1000: return
  if pSinkStrRead(DStr(v: k, s: "x")) == 2001: symexTarget("hit")
proc pSinkStrNever(k: int) =
  if k > 1000 or k < -1000: return
  if pSinkStrRead(DStr(v: k, s: "x")) == 1001: symexTarget("hit")
proc pPlainSite(k: int) =
  if k > 1000: return
  if pPlain(DObj(v: k)) - k == 1: symexTarget("hit")
proc pPlainNever(k: int) =
  if k > 1000: return
  if pPlain(DObj(v: k)) == k: symexTarget("hit")
proc pVarSite(k: int) =
  if k > 1000: return
  var a = DObj(v: k)
  if pVar(a) - k == 1: symexTarget("hit")
proc pSinkSite(k: int) =
  if pSink(DObj(v: k)) == 3: symexTarget("hit")
proc pSinkNever(k: int) =
  if pSink(DObj(v: k)) != k: symexTarget("hit")

# `let b = a`, `b` then at a sink position. Natively (c and cpp, read with
# `--expandArc`) the compiler's cursor inference (`varpartitions`) makes `b`
# a cursor when `a`'s last read comes after `b`'s: the hook runs at every
# sink position of `b`, on any path. Otherwise `b` owns a's value (`=copy`
# or the move at the `let`) and is a local like any other.
proc dTake2(x: sink DObj; y: DObj): int = x.v * 10 + y.v
proc aCursor(k: int) =
  if k > 1000 or k < -1000: return
  let a = DObj(v: k)
  let b = a
  if dTake(b) * 1000 + a.v == 2001: symexTarget("hit")
proc aCursorNever(k: int) =
  if k > 1000 or k < -1000: return
  let a = DObj(v: k)
  let b = a
  if dTake(b) * 1000 + a.v == 1001: symexTarget("hit")
proc aOwned(k: int) =
  if k > 1000 or k < -1000: return
  let a = DObj(v: k)
  let b = a
  if a.v + dTake(b) * 1000 == 1001: symexTarget("hit")
proc aOwnedNever(k: int) =
  if k > 1000 or k < -1000: return
  let a = DObj(v: k)
  let b = a
  if a.v + dTake(b) * 1000 == 2001: symexTarget("hit")
proc aOwnedRead(k: int) =
  if k > 1000 or k < -1000: return
  let a = DObj(v: k)
  let b = a
  if dTake(b) * 1000 + b.v == 2001: symexTarget("hit")
proc aReturn(k: int) =
  if k > 1000: return
  let a = DObj(v: k)
  let b = a
  if k > 0:
    if dTake(b) - k == 1: symexTarget("hit")
    return
  if a.v == 7: symexTarget("other")
proc aTied(k: int) =
  # Nothing between the two last reads: not followed (declines).
  if k > 100 or k < -100: return
  let a = DObj(v: k)
  let b = a
  if dTake2(b, a) == 21: symexTarget("hit")

# A generic routine's sink positions: natively as its instance's.
proc gLocal[T](x: T; k: int): int =
  let a = DObj(v: k)
  dTake(a) * 1000 + a.v
proc gParam[T](a: T): int = dTake(a)
proc gLocalSite(k: int) =
  if k > 1000: return
  if gLocal(0, k) == 2001: symexTarget("hit")
proc gParamSite(k: int) =
  if k > 1000: return
  if gParam(DObj(v: k)) - k == 1: symexTarget("hit")

# A value holding the hooked type. Natively (c and cpp) the compiler's
# `=dup` of the container runs the user hook on each hooked field or element,
# in order (an object of two: twice; an array or seq of two: twice; an empty
# seq: never). A constructor's argument is consumed (no hook).
type DBox = object
  o: DObj
  n: int
type DBox2 = object
  p, q: DObj
type DOuter = object
  b: DBox
proc dTakeBox(x: sink DBox): int = x.o.v
proc dTakeBox2(x: sink DBox2): int = x.p.v * 10 + x.q.v
proc dTakeOuter(x: sink DOuter): int = x.b.o.v
proc dTakeTup(x: sink (DObj, int)): int = x[0].v
proc dTakeArr(x: sink array[2, DObj]): int = x[0].v * 10 + x[1].v
proc dTakeSeq(x: sink seq[DObj]): int =
  for e in x: result = result * 10 + e.v
proc cBox(k: int) =
  if k > 1000: return
  let w = DBox(o: DObj(v: k), n: 5)
  if dTakeBox(w) * 1000 + w.o.v == 2001: symexTarget("hit")
proc cBoxNever(k: int) =
  if k > 1000 or k < -1000: return
  let w = DBox(o: DObj(v: k), n: 5)
  if dTakeBox(w) * 1000 + w.o.v == 1001: symexTarget("hit")
proc cBoxLast(k: int) =
  # The container's last read, and the constructor's argument: no hook.
  let w = DBox(o: DObj(v: k), n: 5)
  if dTakeBox(w) == 3: symexTarget("hit")
proc cBoxLastNever(k: int) =
  let w = DBox(o: DObj(v: k), n: 5)
  if dTakeBox(w) != k: symexTarget("hit")
proc cBox2(k: int) =
  if k > 100 or k < -100: return
  let w = DBox2(p: DObj(v: k), q: DObj(v: 2 * k))
  if dTakeBox2(w) * 1000 + w.p.v == 23001: symexTarget("hit")
proc cOuter(k: int) =
  if k > 1000: return
  let w = DOuter(b: DBox(o: DObj(v: k)))
  if dTakeOuter(w) * 1000 + w.b.o.v == 2001: symexTarget("hit")
proc cTup(k: int) =
  if k > 1000: return
  let t = (DObj(v: k), 3)
  if dTakeTup(t) * 1000 + t[0].v == 2001: symexTarget("hit")
proc cArr(k: int) =
  if k > 100 or k < -100: return
  let t = [DObj(v: k), DObj(v: 2 * k)]
  if dTakeArr(t) * 1000 + t[0].v == 23001: symexTarget("hit")
proc cArrNever(k: int) =
  if k > 100 or k < -100: return
  let t = [DObj(v: k), DObj(v: 2 * k)]
  if dTakeArr(t) * 1000 + t[0].v == 12001: symexTarget("hit")
proc cSeq(k: int) =
  if k > 100 or k < -100: return
  let t = @[DObj(v: k), DObj(v: 2 * k)]
  if dTakeSeq(t) * 1000 + t[0].v == 23001: symexTarget("hit")

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42])
let dCell = cellKey(axMagic, "Dup")

suite "PRC-45":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 420

  test "the verdict does not depend on which entry probed the type first":
    # `oCov` is first named by `assertCoveredBy`, `oAll` by `symexForAll`,
    # `oFind` by `symexFind`: each verdict is the same exact hit.
    let cov = assertCoveredBy(oCov, tLabel("hit"))
    check cov.status == sfSat and cov.trusted
    let all = symexForAll(integers(-50, 50), oAll, inMemoryDatabase())
    let fa = findingFor(all.symexFindings, tLabel("hit"))
    check fa.status == sfSat and fa.trusted
    check pinExact(oFind, dCell, domain = idom).status == sxSat
    # And the other way round, each through the entries it was not first in.
    check pinExact(oCov, dCell, domain = idom).status == sxSat
    check pinExact(oCov, dCell, domain = idom,
                   via = viaForAll(integers(-50, 50))).status == sxSat
    check pinExact(oAll, dCell, domain = idom).status == sxSat
    check pinExact(oAll, dCell, domain = idom, via = viaCovered).status == sxSat
    check pinExact(oFind, dCell, domain = idom, via = viaCovered).status == sxSat
    check pinExact(oFind, dCell, domain = idom,
                   via = viaForAll(integers(-50, 50))).status == sxSat

  test "a read in an `except` branch or a `finally` is reached as the compiler's graph has it":
    check native(eExcept(1)) == "hit"
    check native(eReturn(1)) == "hit"
    check native(eBefore(1)) == "hit"
    check native(eFinally(1)) == "hit"
    check native(eSibling(99)) == "hit"
    check pinExact(eExcept, dCell, domain = idom).status == sxSat
    check pinExact(eExceptNever, dCell, domain = idom).status == sxUnsat
    check pinExact(eReturn, dCell, domain = idom).status == sxSat
    check pinExact(eBefore, dCell, domain = idom).status == sxSat
    check pinExact(eFinally, dCell, domain = idom).status == sxSat
    check pinExact(eSibling, dCell, domain = sampled([0, 1, 99])).status == sxSat
    check pinExact(eEarlyReturn, dCell, domain = idom).status == sxSat

  test "a parameter that is not `sink` is copied; a `sink` one on its last read moves":
    check native(pPlainSite(1)) == "hit"
    check native(pVarSite(1)) == "hit"
    check native(pSinkSite(3)) == "hit"
    check pinExact(pPlainSite, dCell, domain = idom).status == sxSat
    check pinExact(pPlainNever, dCell, domain = idom).status == sxUnsat
    check pinExact(pVarSite, dCell, domain = idom).status == sxSat
    check pinExact(pSinkSite, dCell, domain = idom).status == sxSat
    check pinExact(pSinkNever, dCell, domain = idom).status == sxUnsat

  test "a `sink` parameter read after the site is copied only when its destructor is not trivial":
    check native(pSinkReadSite(1)) == "hit"
    check native(pSinkStrSite(1)) == "hit"
    check pinExact(pSinkReadSite, dCell, domain = idom).status == sxSat
    check pinExact(pSinkReadNever, dCell, domain = idom).status == sxUnsat
    check pinExact(pSinkStrSite, dCell, domain = idom).status == sxSat
    check pinExact(pSinkStrNever, dCell, domain = idom).status == sxUnsat

  test "a copy of a local is a cursor as the compiler's inference has it":
    check native(aCursor(1)) == "hit"
    check native(aOwned(1)) == "hit"
    check native(aOwnedRead(1)) == "hit"
    check native(aReturn(1)) == "hit"
    check native(aTied(1)) == "hit"
    check pinExact(aCursor, dCell, domain = idom).status == sxSat
    check pinExact(aCursorNever, dCell, domain = idom).status == sxUnsat
    check pinExact(aOwned, dCell, domain = idom).status == sxSat
    check pinExact(aOwnedNever, dCell, domain = idom).status == sxUnsat
    check pinExact(aOwnedRead, dCell, domain = idom).status == sxSat
    check pinExact(aReturn, dCell, domain = idom).status == sxSat
    pinDecline(aTied, dCell, feGlobalRouteUnproved,
               needle = "whether the compiler makes it a cursor is not followed")

  test "a generic routine's sink position is its instance's":
    check native(gLocalSite(1)) == "hit"
    check native(gParamSite(1)) == "hit"
    check pinExact(gLocalSite, dCell, domain = idom).status == sxSat
    check pinExact(gParamSite, dCell, domain = idom).status == sxSat

  test "a value holding the hooked type runs the hook on each hooked part":
    check native(cBox(1)) == "hit"
    check native(cBoxLast(3)) == "hit"
    check native(cBox2(1)) == "hit"
    check native(cOuter(1)) == "hit"
    check native(cTup(1)) == "hit"
    check native(cArr(1)) == "hit"
    check native(cSeq(1)) == "hit"
    check pinExact(cBox, dCell, domain = idom).status == sxSat
    check pinExact(cBoxNever, dCell, domain = idom).status == sxUnsat
    check pinExact(cBoxLast, dCell, domain = idom).status == sxSat
    check pinExact(cBoxLastNever, dCell, domain = idom).status == sxUnsat
    check pinExact(cBox2, dCell, domain = idom).status == sxSat
    check pinExact(cOuter, dCell, domain = idom).status == sxSat
    check pinExact(cTup, dCell, domain = idom).status == sxSat
    check pinExact(cArr, dCell, domain = idom).status == sxSat
    check pinExact(cArrNever, dCell, domain = idom).status == sxUnsat

  test "a seq of the hooked type declines (its `=dup` loops over the elements)":
    pinDecline(cSeq, dCell, feGlobalRouteUnproved,
               needle = "may run at a sink position the walk does not model")
