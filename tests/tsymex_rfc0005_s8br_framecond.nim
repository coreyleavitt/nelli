## RFC-0005 (soundness channels) slice S8br -- S8bk's remainder, item 2.
##
## A check no snapshot carries (`touch(gH.s[gi], f())`: the seq is reached
## through a ref, itself a read S8bk moves to the call) declined whenever a
## later argument may write anything, even when it leaves `gH`, `gH.s` and
## `gi` alone. It now declines only when a later argument may write a
## location the lvalue reads (S8as/S8ax's write summary). Item 1 is
## `tsymex_rfc0005_s8br_remainder`; the two were split so each file
## compiles and runs under 60 s per backend. The RFC's "As landed (S8br)"
## note has the design.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  ## `want`, with no decline (`hePtrFamily`, a hint, may accompany a `ptr`).
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.kind == hePtrFamily
    r

template replays(fn: typed, lbl: string) =
  block:
    let r = verdict(fn, lbl, sxSat)
    if r.status == sxSat:
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template declines(fn: typed, lbl, why: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feEvalOrderUnmodelled)
    check why in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

type Box = ref object
  x: int
type Holder = ref object
  s: seq[int]

var gi: int
var gSeen: int
var gP: Box
var gH: Holder

proc incI(): int =
  inc gi
  0

proc stampSeen(): int =
  ## Leaves `gH`, its heap and `gi` alone.
  inc gSeen
  0

proc setBox(): int =
  ## Writes another heap (`Box`), not `Holder`'s.
  gP.x = 7
  0

proc moveH(): int =
  gH = Holder(s: @[1])
  0

proc setElem(): int =
  ## Writes an element of the seq the lvalue indexes (`Holder`'s heap).
  gH.s[0] = 9
  0

proc touch(v: var int; k: int) = v = v + 5 + k

# ---- 2. a check no snapshot carries --------------------------------------------

proc sutHeapKept(k: int) =
  ## The seq is reached through a ref (`gH.s`): no snapshot carries the
  ## check. The later call leaves every location the lvalue reads alone.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  gSeen = 0
  touch(gH.s[gi], stampSeen())
  if gH.s[2] == k + 5 and gSeen == 1 and k == 7: symexTarget("hk")
  if gH.s[2] != k + 5 or gSeen != 1: symexTarget("hk_dead")

proc sutHeapKeptProc(k: int) =
  ## Through a proc value (S8bh's `closureCallIR`).
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  gSeen = 0
  let f = touch
  f(gH.s[gi], stampSeen())
  if gH.s[2] == k + 5 and gSeen == 1 and k == 9: symexTarget("pk")
  if gH.s[2] != k + 5 or gSeen != 1: symexTarget("pk_dead")

proc sutHeapMovedProc(k: int) =
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  let f = touch
  f(gH.s[gi], moveH())
  if k == 1: symexTarget("pw")

proc sutHeapOther(k: int) =
  ## The later call writes a heap, but not `Holder`'s.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gP = Box(x: 1)
  gi = 2
  touch(gH.s[gi], setBox())
  if gH.s[2] == k + 5 and gP.x == 7 and k == 8: symexTarget("hb")
  if gH.s[2] != k + 5 or gP.x != 7: symexTarget("hb_dead")

proc sutHeapMoved(k: int) =
  ## The later call rebinds the ref the check read through.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  touch(gH.s[gi], moveH())
  if k == 1: symexTarget("hw")

proc sutHeapIdx(k: int) =
  ## The later call moves the index.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 1
  touch(gH.s[gi], incI())
  if k == 1: symexTarget("hi")

proc sutHeapElem(k: int) =
  ## The later call writes the seq (`Holder`'s heap) the check read.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  touch(gH.s[gi], setElem())
  if k == 1: symexTarget("he")

suite "S8br: a check no snapshot carries":

  test "nim":
    gH = Holder(s: @[10, 20, 30])
    gi = 2
    gSeen = 0
    touch(gH.s[gi], stampSeen())
    check gH.s == @[10, 20, 35] and gSeen == 1
    gH = Holder(s: @[10, 20, 30])
    gP = Box(x: 1)
    touch(gH.s[gi], setBox())
    check gH.s == @[10, 20, 35] and gP.x == 7
    block:
      let f = touch
      gH = Holder(s: @[10, 20, 30])
      gSeen = 0
      f(gH.s[gi], stampSeen())
      check gH.s == @[10, 20, 35] and gSeen == 1

  test "a check no snapshot carries":
    ## RED: `hk`, `hb`, `pk` and their twins declined (S8bk: whenever a
    ## later argument may write anything). The writing twins declined
    ## already.
    replays(sutHeapKept, "hk")
    discard verdict(sutHeapKept, "hk_dead", sxUnsat)
    replays(sutHeapOther, "hb")
    discard verdict(sutHeapOther, "hb_dead", sxUnsat)
    declines(sutHeapMoved, "hw", "may change what the check read")
    declines(sutHeapIdx, "hi", "may change what the check read")
    declines(sutHeapElem, "he", "may change what the check read")
    replays(sutHeapKeptProc, "pk")
    discard verdict(sutHeapKeptProc, "pk_dead", sxUnsat)
    declines(sutHeapMovedProc, "pw", "may change what the check read")

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 229
