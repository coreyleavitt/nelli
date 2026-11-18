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

type
  Color = enum cRed, cGreen, cBlue
  Holey = enum hA = 1, hB = 5, hC = 9
  Cents = distinct int
  Tiny = distinct int8
  Flag = distinct bool

proc sutEnum(c: Color; n: int) =
  if c == cBlue and n == 2 and c == cRed: symexTarget("hit")

proc sutHoley(h: Holey) =
  if ord(h) == 5: symexTarget("hit")

proc sutDistinct(c: Cents) =
  if int(c) > 5 and int(c) < 3: symexTarget("hit")

proc sutTiny(t: Tiny) =
  if int(t) > 100 and int(t) < 101: symexTarget("hit")

# symexAssume: the walker restricts to the assumption; the native replay must
# reject a run that violates it.
proc sutAssumeUnsat(x: int) =
  symexAssume(x < 5)
  if x == 7: symexTarget("hit")

proc sutAssumeSat(x: int) =
  symexAssume(x > 5)
  if x == 7: symexTarget("hit")

proc sutAssumeAll(x: int) =
  symexAssume(x == 1000)
  if x == 7: symexTarget("hit")


proc sutAssumeSwallow(x: int) =
  try:
    symexAssume(x < 5)
  except Exception:
    discard
  if x == 7: symexTarget("hit")

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

  test "boundaryOf an enum: every declared value, holes excluded":
    check boundaryOf(Color).exhaustive
    check boundaryOf(Color).values == @[cRed, cGreen, cBlue]
    check boundaryOf(Holey).exhaustive
    check boundaryOf(Holey).values == @[hA, hB, hC]

  test "boundaryOf a distinct type: its base type's domain, converted":
    check boundaryOf(Tiny).exhaustive
    check boundaryOf(Tiny).values.len == 256
    check boundaryOf(Flag).values.len == 2
    check not boundaryOf(Cents).exhaustive
    check boundaryOf(Cents).values.mapIt(int(it)) == boundaryInts.values

  test "enum, holey enum and distinct parameters are pinned":
    check pinFind(sutEnum, tLabel("hit")).status == sxUnsat
    check pinFind(sutHoley, tLabel("hit")).status == sxSat
    check pinFind(sutDistinct, tLabel("hit")).status == sxUnsat
    check pinFind(sutTiny, tLabel("hit")).status == sxUnsat
    let e = recordsWith("/sutEnum/")
    check e.len == 1 and not e[0].exhaustive and "[24]" in e[0].domain
    check "exhaustive[3]{cRed,cGreen,cBlue}" in e[0].domain
    check recordsWith("/sutHoley/").len == 1
    let t = recordsWith("/sutTiny/")
    check t.len == 1 and t[0].exhaustive and "[256]" in t[0].domain

  test "symexAssume: an unsat verdict that holds only under the assumption is pinned":
    check pinFind(sutAssumeUnsat, tLabel("hit")).status == sxUnsat
    check recordsWith("/sutAssumeUnsat/").len == 1

  test "symexAssume: a sat witness satisfies the assumption and hits":
    let r = pinFind(sutAssumeSat, tLabel("hit"))
    check r.status == sxSat
    check recordsWith("/sutAssumeSat/").len == 1

  test "symexAssume: a domain every run of which is rejected fails the pin":
    ## the assumption holds only at 1000, outside the boundary sample
    check symexFind(sutAssumeAll, tLabel("hit")).status == sxUnsat
    expect PinFailure:
      discard pinFind(sutAssumeAll, tLabel("hit"))

  test "symexAssume: a SUT that catches every exception stays rejected":
    check pinFind(sutAssumeSwallow, tLabel("hit")).status == sxUnsat

  test "symexAssume: outside a pin it is unchanged (no raise, no state)":
    sutAssumeUnsat(7)
    symexAssume(false)
    let nr = nativeRun(sutAssumeUnsat(7))
    check nr.rejected
    check nr.hits.len == 0 and nr.raised.len == 0
    symexAssume(false)   # the gate is closed again after the run
    check not nativeRun(sutAssumeUnsat(1)).rejected
