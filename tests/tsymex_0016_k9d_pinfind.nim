## RFC-0016 K9d -- `pinFind`, the generator that pins a suite's own
## `symexFind` call (W-54).
##
## `pinFind(fn, target, settings)` is `symexFind` with the same arguments and
## the same result, plus K9a's differential judgement of that result: a
## definite verdict (trusted `sxSat`, `sxUnsat`, `sxRaised`) is reproduced
## natively and written as a pin record; anything else (a decline, an untrusted
## or undefined-behaviour claim, a witness unsafe to run in-process) is
## returned as it came, with no record. The `sxUnsat` domain is generated per
## parameter from its type (`boundaryOf`): exhaustive for `bool` and for an
## ordinal of at most 256 values, the boundary sample otherwise. The cell is
## `family:generic:k9d/<file>/<fn>/<target>`, so the record says which suite
## and which call it evidences.
import std/[unittest, os, strutils, sequtils]
import nelli/symex
import ./s8cu_helpers

let pinTmp = getTempDir() / ("k9d_pinfind_" & $getCurrentProcessId())
createDir(pinTmp)
# Private, as in K9a's file: the tests count this file's records.
putEnv("NELLI_PIN_DIR", pinTmp)

proc records(): seq[PinRecord] =
  for r in pinRecords(pinTmp): result.add r

proc recordsWith(part: string): seq[PinRecord] =
  records().filterIt(part in it.cell.key)

proc sutHit(x: int) =
  if x == 7: symexTarget("hit")

proc sutNever(x: int) =
  if x > 5 and x < 3: symexTarget("hit")

proc sutBool(a, b: bool) =
  if a and not a and b: symexTarget("hit")

proc sutI8(x: int8) =
  if x > 100 and x < 101: symexTarget("hit")

proc sutRange(x: range[3 .. 9]; y: int) =
  if x == 2: symexTarget("hit")

proc sutWide(x: range[0'u64 .. 5_000_000_000'u64]; y: range[1 .. 1_000_000]) =
  if x > 5_000_000_000'u64 or y > 1_000_000: symexTarget("hit")

proc sutVar(x: var int) =
  if x == 4 and x == 5: symexTarget("hit")
  x = 1

proc sutRet(x: int): int =
  if x == 9: symexTarget("hit")
  x + 1

proc sutRaise(x: int) =
  if x == 3: raise newException(ValueError, "three")

suite "K9d: pinFind":
  test "boundaryOf: exhaustive for bool and a small ordinal, sampled for int":
    check boundaryOf(bool).exhaustive
    check boundaryOf(bool).values == @[false, true]
    check boundaryOf(int8).exhaustive
    check boundaryOf(int8).values.len == 256
    check boundaryOf(range[3 .. 9]).values == @[3, 4, 5, 6, 7, 8, 9].mapIt(range[3 .. 9](it))
    check not boundaryOf(int).exhaustive
    check boundaryOf(int).values == boundaryInts.values
    check low(uint64) in boundaryOf(uint64).values
    check high(uint64) in boundaryOf(uint64).values

  test "a sat verdict is returned as symexFind's and pinned on its witness":
    let r = pinFind(sutHit, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 7
    let rs = recordsWith("/sutHit/")
    check rs.len == 1
    if rs.len == 1:
      check rs[0].cell.scope == faGeneric
      check rs[0].cell.key == "k9d/tsymex_0016_k9d_pinfind/sutHit/tLabel(\"hit\")"
      check rs[0].entry == "symexFind"
      check rs[0].verdict == pvExact
      check rs[0].walker == "sxSat"

  test "an unsat verdict is pinned over the generated domain":
    check pinFind(sutNever, tLabel("hit")).status == sxUnsat
    check pinFind(sutBool, tLabel("hit")).status == sxUnsat
    check pinFind(sutI8, tLabel("hit")).status == sxUnsat
    let n = recordsWith("/sutNever/")
    check n.len == 1 and not n[0].exhaustive and "[8]" in n[0].domain
    let b = recordsWith("/sutBool/")
    check b.len == 1 and b[0].exhaustive and "[4]" in b[0].domain
    let i = recordsWith("/sutI8/")
    check i.len == 1 and i[0].exhaustive and "[256]" in i[0].domain

  test "mixed parameter types, a range, a var parameter, a result":
    check pinFind(sutRange, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutRange/").len == 1
    check pinFind(sutVar, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutVar/").len == 1
    check pinFind(sutRet, tLabel("hit")).status == sxSat
    check recordsWith("/sutRet/").len == 1

  test "a raise verdict is pinned on its raising witness":
    let r = pinFind(sutRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised or r.status == sxSat
    let rs = recordsWith("/sutRaise/")
    check rs.len == 1
    if rs.len == 1: check rs[0].verdict in {pvExact, pvRaised}

  test "the suite's own settings reach symexFind":
    const s = block:
      var s = defaultSymexSettings()
      s.budget.queryTimeoutMs = 0
      s
    check pinFind(sutHit, tLabel("hit"), s).status == sxSat
    check recordsWith("/sutHit/").len == 2

  test "a wide range parameter is generated and replayed at its declared type":
    ## the witness tuple holds a range as its base type, so the domain must
    ## come from the declared type or a native call would raise on conversion
    check pinFind(sutWide, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutWide/").len == 1
