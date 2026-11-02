## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part A:
## the written-ness of a part (items 3, 4 and 7) and the address of an array
## element (item 5). Every expectation is Nim's (the "nim" tests run the same
## code).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
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
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

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

# ---- 5. the address of an array element ---------------------------------------
#
# RFC-0005 S8bz item 5. S8as gave `let p = addr gArr[1]` a constant index; a
# computed index (S8ax's `elemAddrNode`) stopped at a module-level root, and a
# `var` parameter's seq was no root at all: `heUnsafeCast`.

type O5 = object
  x, y: int

var gA5: array[4, int]
var gO5: array[3, O5]
var gOOB5: array[4, int]
var gS5: seq[int]
var gCall5: seq[int]

proc growCall5() = gCall5.add 1

proc sutAddrSym(i, k: int) =
  if i < 0 or i > 3: return
  for j in 0 .. 3: gA5[j] = 0
  let p = addr gA5[i]
  p[] = k
  if gA5[2] == 5: symexTarget("as")
  if gA5[i] != k: symexTarget("as_dead")

proc sutAddrSymObj(i, k: int) =
  if i < 0 or i > 2: return
  gO5[i].x = 0
  let p = addr gO5[i].x
  p[] = k
  if gO5[i].x == 5: symexTarget("aso")
  if gO5[i].x != k: symexTarget("aso_dead")

proc sutAddrOob(i: int) =
  let p = addr gOOB5[i]
  if i == 0: symexTarget("aoob_never")
  p[] = 1

proc sutAddrUnwritten(i: int) =
  if i < 0 or i > 3: return
  let p = addr gOOB5[i]
  if p[] == 7: symexTarget("aunw")

proc sutAddrSeqGlobal(i, k: int) =
  gS5 = @[0, 0, 0]
  if i < 0 or i > 2: return
  let p = addr gS5[i]
  p[] = k
  if gS5[i] == 5: symexTarget("asg")
  if gS5[i] != k: symexTarget("asg_dead")

proc sutAddrSeqCallee(i: int) =
  gCall5 = @[0, 0]
  if i < 0 or i > 1: return
  let p = addr gCall5[i]
  growCall5()       # may move the elements: `p` dangles
  p[] = 1
  symexTarget("asc")

suite "S8bz (5): the address of an array element":

  test "nim":
    sutAddrSym(2, 5)
    check gA5[2] == 5
    sutAddrSymObj(1, 5)
    check gO5[1].x == 5
    expect IndexDefect:
      sutAddrOob(7)
    sutAddrSeqGlobal(1, 5)
    check gS5[1] == 5

  test "a computed index into a module-level array":
    ## RED: sxUnknown, `heUnsafeCast` (`elemAddrNode` stopped at a
    ## module-level root).
    confirmed(sutAddrSym, "as")
    discard clean(sutAddrSym, "as_dead", sxUnsat)
    confirmed(sutAddrSymObj, "aso")
    discard clean(sutAddrSymObj, "aso_dead", sxUnsat)

  test "its index is checked where `addr` evaluates it, and nothing is read":
    ## RED: sxUnknown, `heUnsafeCast`. The check read observes no value.
    block:
      let r = symexFind(sutAddrOob, tIndexError())
      checkpoint show(r.errors)
      check r.status == sxRaised
      for e in r.errors: check e.severity == sevHint
    candidate(sutAddrUnwritten, "aunw")   # the dereference does read it

  test "a module-level seq, resized by nothing":
    ## RED: sxUnknown, `heUnsafeCast`.
    confirmed(sutAddrSeqGlobal, "asg")
    discard clean(sutAddrSeqGlobal, "asg_dead", sxUnsat)

  test "a module-level seq a callee may resize":
    let r = symexFind(sutAddrSeqCallee, tLabel("asc"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedOp and "may resize" in e.msg: named = true
    check named

suite "S8bz: walker version":

  test "the walker version is at least S8bz's":
    check parseInt(symexWalkerVersion) >= 241
