## RFC-0016 PRC-02m. `symexFind` over a SUT that dispatches a `method` decides
## when the toolchain's per-binary dispatch table (`hasMethodTable`) proves the
## override set; without it nothing can confirm the override set, so any walk
## that reaches a dynamic method dispatch declines (never a trusted verdict
## over the visible overrides only).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/replayproc
from nelli/smt/runtime import hostAdmission
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
  # `gBias` is havocked (it may hold any value when the property runs), so the
  # hit names its value: a witness the solver picks then replays as found.
  if gBias == 0 and pick(v) == 10: symexTarget("hit")

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

type
  HBaseObj = object of RootObj
    k: int
  HBase = ref HBaseObj
  HSubObj = object of HBaseObj
  HSub = ref HSubObj

proc `=destroy`(x: HSubObj) = discard

var gHeld: HBase = HSub(k: 1)
  ## The one place `HSub` is built: module init, which no SUT's scan reads.

proc sutHeld(v: int) =
  symexAssume(v > -100 and v < 100)
  let h = HBase(k: v)
  if gBias == 0 and h.k == 10: symexTarget("hit")

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & ": " & e.msg & "; "

template declines(r: SymexResult) =
  check r.status == sxUnknown
  check not r.trusted
  check "whose overrides cannot be listed" in show(r.errors)

template decides(r: SymexResult) =
  ## With the table the run confirms the override set and decides; a build
  ## without it (a compiler lacking patch 0008, or a library build) cannot
  ## confirm it, so a walk that dispatches a method declines.
  when hasMethodTable:
    check r.status == sxSat
    check r.trusted
  else:
    declines(r)

suite "PRC-02m: symexFind over a dynamic call":
  # A symexFind run is decided only on a verified build row, and the Z3 4.13.4
  # row is Linux c alone (`rowOf`, buildprofile.nim), so cpp under 4.13.4 is
  # `feHostUnadmitted` by design (tsymex_0016_k5a_profile pins it refused).
  # Not a defect: the pins below skip on such a host.
  test "a witness reaching the first override":
    if hostAdmission().isSome:
      skip()
    else:
      let r = symexFind(sutHit, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      decides(r)
      if r.status == sxSat: check r.witness[0] == 9

  test "a witness reaching the second override":
    if hostAdmission().isSome:
      skip()
    else:
      let r = symexFind(sutHit2, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      decides(r)
      if r.status == sxSat: check r.witness[0] == -3

  test "a property no override violates is unsat":
    if hostAdmission().isSome:
      skip()
    else:
      let r = symexFind(sutNever, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      when hasMethodTable:
        check r.status == sxUnsat
      else:
        declines(r)

  test "an override the scan cannot see still declines":
    if hostAdmission().isSome:
      skip()
    else:
      let r = symexFind(sutHiddenFind, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      # With the table, it lists `Sub`'s override, which no scan read: the
      # walk's dispatch (the base body only) cannot stand, sat or unsat. Without
      # it nothing confirms the override set, so the walk declines at the
      # dispatch whatever it reads (it would otherwise be a trusted verdict over
      # the visible overrides only).
      check r.status == sxUnknown
      check not r.trusted

  test "a global read beside a ref hierarchy decides with the subtype table":
    if hostAdmission().isSome:
      skip()
    else:
      # `routeType` takes the hooks of the subtypes the scan reads as those a
      # `ref` of the hierarchy may run; the run's subtype table confirms no
      # subtype in the binary has another (`subtypeRouteGuard`). `MSub` and
      # `MSub2` have none. Without the table a subtype declared where no scan
      # sees it may carry a hook, so the global's route stays open.
      let r = symexFind(sutBiased, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      when hasSubtypeTable:
        check r.status == sxSat
        check r.trusted
        if r.status == sxSat: check r.witness[0] == 9
      else:
        check r.status == sxUnknown
        check r.errors.named(feGlobalRouteUnproved)
        when hasMethodTable:
          check "may hold a subtype" in show(r.errors)
        else:
          check "whose overrides cannot be listed" in show(r.errors)

  test "a subtype with a hook the scan cannot see declines":
    if hostAdmission().isSome:
      skip()
    else:
      # `HSub` is built only at module init and has a `=destroy` no scan of
      # `sutHeld` reads: the table names it, so every read declines.
      let r = symexFind(sutHeld, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.trusted
      when hasSubtypeTable:
        check "a lifetime hook the entry could not see" in show(r.errors)
      else:
        check "may hold a subtype" in show(r.errors)
