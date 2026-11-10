## RFC-0016 PRC-02m. `symexFind` over a SUT that dispatches a `method` decides
## when the toolchain's per-binary dispatch table (`hasMethodTable`) proves the
## override set; without it the route scan keeps the precise decline.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/replayproc
import ./s8cu_helpers
import helpers/prc03_types   # Base/Sub: the override of `Sub` lives in a module this file never imports
import helpers/prc03_sut

type
  MBase = ref object of RootObj
  MSub = ref object of MBase
  MSub2 = ref object of MBase

method area(x: MBase; v: int): int {.base, gcsafe.} = v
method area(x: MSub; v: int): int {.gcsafe.} = v + 1
method area(x: MSub2; v: int): int {.gcsafe.} = v + 2

proc pick(v: int): int =
  let b: MBase = if v > 0: MSub() else: MSub2()
  area(b, v)

var gBias = 0

proc sutBiased(v: int) =
  symexAssume(v > -100 and v < 100)
  if pick(v) + gBias == 10: symexTarget("hit")

proc sutHit(v: int) =
  symexAssume(v > -100 and v < 100)
  if pick(v) == 10: symexTarget("hit")

proc sutHit2(v: int) =
  symexAssume(v > -100 and v < 100)
  if pick(v) == -1: symexTarget("hit")

proc sutNever(v: int) =
  symexAssume(v > -100 and v < 100)
  if pick(v) < v: symexTarget("hit")

proc sutHiddenFind(v: int) =
  symexAssume(v > -100 and v < 100)
  let b: Base = Sub()
  if area(b, v) == v + 1: symexTarget("hit")

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & ": " & e.msg & "; "

suite "PRC-02m: symexFind over a dynamic call":
  test "a witness reaching the first override":
    let r = symexFind(sutHit, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    # a SUT that reads no global never asked the route scan, so stock decides
    # too; the table matters for the override set the walk dispatched over
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 9

  test "a witness reaching the second override":
    let r = symexFind(sutHit2, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == -3

  test "a property no override violates is unsat":
    let r = symexFind(sutNever, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnsat

  test "an override the scan cannot see still declines":
    let r = symexFind(sutHiddenFind, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    when hasMethodTable:
      # the table lists `Sub`'s override, which no scan read: the walk's
      # dispatch (the base body only) cannot stand, sat or unsat. A stock
      # build has no table to ask and still trusts that unsat (handoff).
      check r.status == sxUnknown
      check not r.trusted

  test "a global read beside a ref hierarchy still declines (blocker pin)":
    # PRC-02m's override set is proved, but `routeType` also opens every global
    # for any `ref` of an inheritance hierarchy: a subtype (declared where no
    # scan sees it) may carry a lifetime hook, and the dispatch table lists
    # receivers of methods, not subtypes. Not closable from the table.
    let r = symexFind(sutBiased, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feGlobalRouteUnproved)
    when hasMethodTable:
      check "may hold a subtype" in show(r.errors)
    else:
      check "whose overrides cannot be listed" in show(r.errors)
