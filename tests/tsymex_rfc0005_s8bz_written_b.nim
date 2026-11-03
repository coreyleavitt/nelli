## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part A:
## the written-ness of a part (items 3, 4 and 7) and the address of an array
## element (item 5). Every expectation is Nim's (the "nim" tests run the same
## code).
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bz_written`, `tsymex_rfc0005_s8bz_written_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 65 s).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import s8ct_platform
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  ## A clean `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

template candidate(fn: typed, lbl: string,
                   raised: set[SymexStatusKind] = {}): untyped =
  ## An observed part no write reached: `feGlobalHavoc`, never `sxUnsat`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown} + raised
    var havoc = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc: havoc = true
    check havoc

# ---- 3. a partial write into an unwritten part ---------------------------------
#
# RFC-0005 S8bz item 3. The written-ness of a global is per part: a symbolic
# element write copies the element's other parts (it does not observe them), a
# case object global's entry value is modelled as any other's, and a `var` or
# `addr` actual is copied in without being read; the callee's read of it is the
# observation.

type
  O3 = object
    x, y: int
  VK3 = enum vkA, vkB
  V3 = object
    n: int
    case k: VK3
    of vkA: a: int
    of vkB: b: int

var gAA3: array[3, O3]
var gAAu3: array[3, O3]
var gAAr3: array[3, O3]
var gV3: V3
var gVw3: V3
var gU3: tuple[a, b: int]
var gUr3: tuple[a, b: int]
var gUa3: tuple[a, b: int]
var gArr3: array[4, int]
var gArrR3: array[4, int]

proc setI3(v: var int; x: int) = v = x
proc readI3(v: var int; x: int) =
  if v == x: symexTarget("vr")
proc setP3(p: ptr int; x: int) = p[] = x
proc readP3(p: ptr int; x: int) =
  if p[] == x: symexTarget("ar")

proc sutSymElem(k: int) =
  if k < 0 or k > 2: return
  gAA3[k].x = 5
  if gAA3[k].x == 5: symexTarget("se")
  if gAA3[k].x != 5: symexTarget("se_dead")

proc sutSymElemOther(k: int) =
  ## The part no write reached, through the same element.
  if k < 0 or k > 2: return
  gAAu3[k].x = 5
  if gAAu3[k].y == 5: symexTarget("seu")

proc sutSymElemRead(k: int) =
  ## A read at another index may meet an element no write reached.
  if k < 0 or k > 1: return
  gAAr3[k].x = 5
  if gAAr3[k + 1].x == 5: symexTarget("ser")

proc sutVariantPlain(k: int) =
  gV3.n = k
  if gV3.n == 5: symexTarget("vp")
  if gV3.n != k: symexTarget("vp_dead")

proc sutVariantArm(k: int) =
  ## Nim checks the branch of the entry value, so the write observes it.
  gVw3.a = k
  if gVw3.a == 5: symexTarget("va")
  if gVw3.a != k: symexTarget("va_dead")

proc sutVarActual(k: int) =
  setI3(gU3.a, k)
  if gU3.a == 5: symexTarget("vw")
  if gU3.a != k: symexTarget("vw_dead")

proc sutVarActualRead(k: int) =
  ## The callee reads the part no write reached.
  readI3(gUr3.a, k)

proc sutVarActualOther(k: int) =
  setI3(gUa3.a, k)
  if gUa3.b == 5: symexTarget("vo")

proc sutAddrActual(k: int) =
  setP3(addr gArr3[3], k)
  if gArr3[3] == 5: symexTarget("aw")
  if gArr3[3] != k: symexTarget("aw_dead")

proc sutAddrActualRead(k: int) =
  readP3(addr gArrR3[3], k)

suite "S8bz (3): a partial write into an unwritten part":

  test "nim":
    sutSymElem(1)
    check gAA3[1].x == 5
    sutVarActual(5)
    check gU3.a == 5
    sutAddrActual(5)
    check gArr3[3] == 5
    sutVariantPlain(5)
    check gV3.n == 5
    sutVariantArm(5)
    check gVw3.a == 5

  test "a symbolic index write into an element of an array of aggregates":
    ## RED: sxSat with `feGlobalHavoc` on `gAA3[0].y`, a part the write only
    ## copies; `se_dead` the same.
    confirmed(sutSymElem, "se")
    discard clean(sutSymElem, "se_dead", sxUnsat)
    candidate(sutSymElemOther, "seu")
    candidate(sutSymElemRead, "ser")

  test "a partial write of a case object global":
    ## RED: sxUnknown, `feGlobalReadUnmodelled`: a case object's entry value
    ## was not modelled.
    confirmed(sutVariantPlain, "vp")
    discard clean(sutVariantPlain, "vp_dead", sxUnsat)
    candidate(sutVariantArm, "va", {sxRaised})
    candidate(sutVariantArm, "va_dead", {sxUnsat, sxRaised})

  test "a `var` or `addr` actual whose part is unwritten":
    ## RED: sxSat with `feGlobalHavoc` on the actual: its copy-in observed it.
    confirmed(sutVarActual, "vw")
    discard clean(sutVarActual, "vw_dead", sxUnsat)
    confirmed(sutAddrActual, "aw")
    discard clean(sutAddrActual, "aw_dead", sxUnsat)
    candidate(sutVarActualOther, "vo")
    # The callee's read is the observation.
    candidate(sutVarActualRead, "vr")
    candidate(sutAddrActualRead, "ar")
