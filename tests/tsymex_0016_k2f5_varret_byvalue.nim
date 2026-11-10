## RFC-0016 K2F-5 -- a `var T` call result passed to a by-value formal.
##
## `byValueActual` read an actual that is a call returning `var T` (or `lent
## T`) as a fresh value: `lvalueRoot` is nil there and there are no steps.
## Nim passes a by-value formal larger than three words (or `{.byref.}`) by
## address (`ccgIntroducedPtr`), so `f(getBig())` hands `f` the location
## `getBig` returns, and a write `f` makes to it through another name is read
## through the formal. Native, c and cpp: `fBig` reads its own write to `gBig`
## through `o` (`big_alias` hit, `big_copy` not), and `fTab` its write to
## `gTab[1]`. The walk bound the formal to a copy: a clean sxUnsat on the live
## label and sxSat on the dead one. It now declines (`byValueWritten`); a
## three-word object is copied natively and stays exact, as does a stdlib
## accessor over a local table, whose entry no other name reaches.
##
## Walker version: 314 (from 313).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

type
  Big = object
    a, b, c, d: int
  Small = object
    a: int
  ByRef {.byref.} = object
    a: int

var gBig: Big
var gSmall: Small
var gByRef: ByRef
var gTab: Table[int, Big]

proc getBig(): var Big = gBig
proc getSmall(): var Small = gSmall
proc getByRef(): var ByRef = gByRef

proc fBig(o: Big; n: int) =
  gBig.a = n + 1
  if o.a == n + 1: symexTarget("big_alias")
  if o.a == n: symexTarget("big_copy")

proc fSmall(o: Small; n: int) =
  gSmall.a = n + 1
  if o.a == n + 1: symexTarget("small_alias")
  if o.a == n: symexTarget("small_copy")

proc fByRef(o: ByRef; n: int) =
  gByRef.a = n + 1
  if o.a == n + 1: symexTarget("byref_alias")
  if o.a == n: symexTarget("byref_copy")

proc fTab(o: Big; n: int) =
  gTab[1].a = n + 1
  if o.a == n + 1: symexTarget("tab_alias")
  if o.a == n: symexTarget("tab_copy")

proc pBig(n: int) =
  guardN()
  gBig = Big(a: n)
  fBig(getBig(), n)

proc pSmall(n: int) =
  guardN()
  gSmall = Small(a: n)
  fSmall(getSmall(), n)

proc pByRef(n: int) =
  guardN()
  gByRef = ByRef(a: n)
  fByRef(getByRef(), n)

proc pTab(n: int) =
  guardN()
  gTab = initTable[int, Big]()
  gTab[1] = Big(a: n)
  fTab(gTab[1], n)

var gOther: int
var gTR: TableRef[int, Big]

proc fLoc(o: Big; n: int) =
  ## Writes a global the actual cannot be.
  gOther = n + 1
  if o.a == n: symexTarget("loc_same")
  if o.a != n: symexTarget("loc_diff")

proc pLoc(n: int) =
  guardN()
  var t = initTable[int, Big]()
  t[1] = Big(a: n)
  fLoc(t[1], n)

proc fPure(o: Big): int =
  ## Writes nothing (a target in the callee is itself a write the walk
  ## cannot place: `symexTarget` records into a global).
  o.a

proc pPure(n: int) =
  guardN()
  gBig = Big(a: n)
  let r = fPure(getBig())
  if r == n: symexTarget("pure_same")
  if r != n: symexTarget("pure_diff")

proc fRef(o: Big; n: int) =
  gTR[1].a = n + 1
  if o.a == n + 1: symexTarget("ref_alias")
  if o.a == n: symexTarget("ref_copy")

proc pRef(n: int) =
  guardN()
  let tr = newTable[int, Big]()
  tr[1] = Big(a: n)
  gTR = tr
  fRef(tr[1], n)

template pin(fn: typed; lbl: static string; nativeHit: bool;
             want: SymexStatusKind) =
  block:
    var nat = false
    for n in ns:
      if lbl in hits(fn(n)): nat = true
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check nat == nativeHit
    check r.status == want
    check not (nat and r.status == sxUnsat)
    check not (not nat and r.status == sxSat)

suite "tsymex_0016_k2f5_varret_byvalue":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 314

  test "a var result over three words is the location it returns":
    pin(pBig, "big_alias", true, sxUnknown)
    pin(pBig, "big_copy", false, sxUnknown)
    pin(pTab, "tab_alias", true, sxUnknown)
    pin(pTab, "tab_copy", false, sxUnknown)
    pin(pRef, "ref_alias", true, sxUnknown)
    pin(pRef, "ref_copy", false, sxUnknown)

  test "a {.byref.} object declines on its pragma":
    pin(pByRef, "byref_alias", true, sxUnknown)
    pin(pByRef, "byref_copy", false, sxUnknown)

  test "precision: copied, local, or untouched stays exact":
    pin(pSmall, "small_alias", false, sxUnsat)
    pin(pSmall, "small_copy", true, sxSat)
    pin(pLoc, "loc_same", true, sxSat)
    pin(pLoc, "loc_diff", false, sxUnsat)
    pin(pPure, "pure_same", true, sxSat)
    pin(pPure, "pure_diff", false, sxUnsat)
