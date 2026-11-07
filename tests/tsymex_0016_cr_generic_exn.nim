## RFC-0016 CR-A -- a generic exception type is identified by its full
## instantiation, not by its last type argument. `G[ValueError]` used to get
## the id `ValueError`, so `except ValueError` "caught" a `G[ValueError]` that
## escapes natively, and the walker returned a trusted `sxSat`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type G[T] = object of CatchableError

proc escapesPlain(x: int) =
  try:
    raise newException(G[ValueError], "m")
  except ValueError:
    symexTarget("inarm")
  symexTarget("hit")

proc escapesPlainArm(x: int) =
  try:
    raise newException(G[ValueError], "m")
  except ValueError:
    symexTarget("hit")

proc caughtExact(x: int) =
  try:
    raise newException(G[ValueError], "m")
  except G[ValueError]:
    symexTarget("hit")

proc caughtBase(x: int) =
  try:
    raise newException(G[ValueError], "m")
  except CatchableError:
    symexTarget("hit")

proc genInt(x: int) =
  try:
    raise newException(G[int], "m")
  except ValueError:
    symexTarget("inarm")
  symexTarget("hit")

suite "CR-A generic exception identity":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 287

  test "native: G[ValueError] escapes except ValueError":
    let a = nativeRun(escapesPlain(0))
    check a.raised == "G"
    check "inarm" notin a.hits
    check "hit" notin a.hits
    let b = nativeRun(escapesPlainArm(0))
    check b.raised == "G"
    check "hit" notin b.hits

  test "native: G[ValueError] caught by its own type and by its base":
    check "hit" in nativeRun(caughtExact(0)).hits
    check "hit" in nativeRun(caughtBase(0)).hits

  test "native: G[int] escapes except ValueError":
    let a = nativeRun(genInt(0))
    check a.raised == "G"
    check "hit" notin a.hits and "inarm" notin a.hits

  test "walker: the escaping cases never claim a trusted verdict":
    pinDecline(escapesPlain, cellKey(faGeneric, "cra/escape-after"),
               eeUnknownExnType)
    pinDecline(escapesPlain, cellKey(faGeneric, "cra/escape-inarm"),
               eeUnknownExnType, tLabel("inarm"))
    pinDecline(escapesPlainArm, cellKey(faGeneric, "cra/escape-arm"),
               eeUnknownExnType)
    pinDecline(genInt, cellKey(faGeneric, "cra/int"), eeUnknownExnType)

  test "walker: the caught cases never claim a trusted wrong verdict":
    pinDecline(caughtExact, cellKey(faGeneric, "cra/caught-exact"),
               eeUnknownExnType)
    pinDecline(caughtBase, cellKey(faGeneric, "cra/caught-base"),
               eeUnknownExnType)
