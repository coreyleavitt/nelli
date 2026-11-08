## RFC-0016 K9d-0 -- one pin through each of section 10's six public entry
## points, so each has a record before Wave 3: `symexFind`,
## `symexFindAllWitnesses`, `symexForAll`, `assertCoveredBy`, the concolic path
## (`concolicFlip`) and a cache hit (`loadSymexVerdict`).
##
## Every pin runs its witness natively through K9a's differential check; the
## entry point's verdict is compared against the native run. The record's
## `entry` is written by the `via` adapter that called the entry point.
import std/[unittest, os, sequtils, sets, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

let pinTmp = getTempDir() / ("k9d0_pins_" & $getCurrentProcessId())
createDir(pinTmp)
# Private, as in K9a's file: the final test counts this file's records.
putEnv("NELLI_PIN_DIR", pinTmp)

proc recordsFor(cell: CellKey): seq[PinRecord] =
  for r in pinRecords(pinTmp):
    if r.cell == cell: result.add r

proc sutHit(x: int) =
  if x == 7: symexTarget("hit")

proc sutNever(x: int) =
  if x > 5 and x < 3: symexTarget("hit")

proc gateHi(x: int) =
  if x > 5: symexTarget("hit")

proc gateOut(x: int) =
  ## Unreachable on the drawn range 0..10.
  if x > 20: symexTarget("hit")

const drawn = toSeq(0 .. 10)
let unsatDomain = exhaustive([0, 1, 2, 7])
let bind0 = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]

proc check1(key: CellKey; entry: string; walker: string) =
  let recs = recordsFor(key)
  check recs.len == 1
  if recs.len == 1:
    check recs[0].entry == entry
    check recs[0].walker == walker
    check recs[0].verdict == pvExact

suite "K9d-0: a pin through each public entry point":

  test "symexFind":
    let k = cellKey(faGeneric, "k9d0/find/sat")
    check pinExact(sutHit, k).status == sxSat
    check1(k, "symexFind", "sxSat")

  test "symexFindAllWitnesses, sat and unsat":
    let ks = cellKey(faGeneric, "k9d0/findall/sat")
    check pinExact(sutHit, ks, via = viaFindAll).status == sxSat
    check1(ks, "symexFindAllWitnesses", "sxSat")
    let ku = cellKey(faGeneric, "k9d0/findall/unsat")
    check pinExact(sutNever, ku, domain = unsatDomain,
                   via = viaFindAll).status == sxUnsat
    check1(ku, "symexFindAllWitnesses", "sxUnsat")

  test "symexForAll, sat and unsat":
    let ks = cellKey(faGeneric, "k9d0/forall/sat")
    check pinExact(sutHit, ks,
                   via = viaForAll(integers(0, 1000))).status == sxSat
    check1(ks, "symexForAll", "sxSat")
    let ku = cellKey(faGeneric, "k9d0/forall/unsat")
    check pinExact(sutNever, ku, domain = unsatDomain,
                   via = viaForAll(integers(0, 1000))).status == sxUnsat
    check1(ku, "symexForAll", "sxUnsat")

  test "assertCoveredBy, sat and unsat":
    let ks = cellKey(faGeneric, "k9d0/covered/sat")
    check pinExact(sutHit, ks, via = viaCovered).status == sxSat
    check1(ks, "assertCoveredBy", "sxSat")
    let ku = cellKey(faGeneric, "k9d0/covered/unsat")
    check pinExact(sutNever, ku, domain = unsatDomain,
                   via = viaCovered).status == sxUnsat
    check1(ku, "assertCoveredBy", "sxUnsat")

  test "the concolic path: a solved flip; a relaxed one is no claim":
    let ks = cellKey(faGeneric, "k9d0/concolic/sat")
    let t1 = @[integerChoice(2, 0, 10, 0)]
    check pinExact(gateHi, ks, domain = exhaustive(drawn),
                   via = viaConcolic(t1, bind0, 0)).status == sxSat
    check1(ks, "concolic", "sxSat")
    # An exactly-infeasible flip is not a claim: the concolic path falls back
    # to a relaxed model (`cfoSolvedOptimistic`, here the draw range's top),
    # which the adapter reports as `sxUnknown`, so the pin refuses it and
    # writes no record. The fuzzer's assist treats that model as a guess.
    let ku = cellKey(faGeneric, "k9d0/concolic/relaxed")
    let t2 = @[integerChoice(2, 0, 10, 0)]
    var msg = ""
    try:
      discard pinExact(gateOut, ku, domain = exhaustive(drawn),
                       via = viaConcolic(t2, bind0, 0))
    except PinFailure as e: msg = e.msg
    check "sxUnknown" in msg
    check recordsFor(ku).len == 0

  test "a cache hit":
    let k = cellKey(faGeneric, "k9d0/cache/unsat")
    check pinExact(sutNever, k, domain = unsatDomain,
                   via = viaCache).status == sxUnsat
    check1(k, "loadSymexVerdict", "sxUnsat")

  test "the six entry points each have a record":
    var seen = initHashSet[string]()
    for r in pinRecords(pinTmp):
      if r.verdict == pvExact: seen.incl r.entry
    for e in ["symexFind", "symexFindAllWitnesses", "symexForAll",
              "assertCoveredBy", "concolic", "loadSymexVerdict"]:
      check e in seen
