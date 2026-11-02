## RFC-0005 (soundness channels) slice S8br -- S8bk's remainder, item 1.
##
## 1. A call in a by-address actual's index (`touch(gArr[nextI()], f())`):
##    Nim evaluates `nextI()` once, where the argument stands, into a
##    temporary, and checks the index there; the element is read and written
##    at the call, through that same temporary index. The walk's copy-out
##    re-parsed the call: an array element declined (`unsupported nnkAsgn
##    shape`), and a seq element called `nextI` a second time (a false
##    `sxSat` and a false `sxUnsat`).
##
## Item 2 (a check no snapshot carries) is `tsymex_rfc0005_s8br_framecond`;
## the two were split so each file compiles and runs under 60 s per
## backend. The RFC's "As landed (S8br)" note has the design.
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

template declinesOp(fn: typed, lbl, why: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOp)
    check why in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

var gArr: array[3, int]
var gs: seq[int]
var gi: int
var gCalls: int
var gOrder: int

proc nextI(): int =
  ## The index call: counted, and stamped into the evaluation order.
  inc gCalls
  gOrder = gOrder * 10 + 1
  1

proc curI(): int =
  ## An index call whose result the later argument's call would change.
  inc gCalls
  gi

proc dblArr(): int =
  ## The later argument: stamped after the index call, and writes the
  ## element the index call chose.
  gOrder = gOrder * 10 + 2
  gArr[1] = gArr[1] * 2
  0

proc setArr(): int =
  ## As `dblArr`, writing a constant: S8an's cell at a computed index with
  ## an input-dependent value is a slow query on its own (pre-existing).
  gOrder = gOrder * 10 + 2
  gArr[1] = 50
  0

proc dblS(): int =
  gOrder = gOrder * 10 + 2
  gs[1] = gs[1] * 2
  0

proc shrinkS(): int =
  gs = @[gs[0]]
  0

proc incI(): int =
  inc gi
  0

proc touch(v: var int; k: int) = v = v + 5 + k

proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

# ---- 1. a call in a by-address actual's index ---------------------------------

proc sutIdxCall(k: int) =
  ## Evaluated once, before the later argument; the element read after it.
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  gCalls = 0
  gOrder = 0
  touch(gArr[nextI()], dblArr())
  if gArr[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 3:
    symexTarget("ic")
  if gArr[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12:
    symexTarget("ic_dead")

proc sutIdxCallSeq(k: int) =
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  gOrder = 0
  touch(gs[nextI()], dblS())
  if gs[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 4:
    symexTarget("iq")
  if gs[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12:
    symexTarget("iq_dead")

proc sutIdxCallKept(k: int) =
  ## The later call moves what the index call read: the temporary does not.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  gCalls = 0
  touch(gArr[curI()], incI())
  if gArr[0] == k + 5 and gArr[1] == 20 and gi == 1 and gCalls == 1 and
     k == 5:
    symexTarget("iv")
  if gArr[0] != k + 5 or gArr[1] != 20 or gCalls != 1:
    symexTarget("iv_dead")

proc sutIdxCallAddr(k: int) =
  ## An `addr` actual (S8an's cell), filled at the call.
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  gCalls = 0
  gOrder = 0
  touchP(addr gArr[nextI()], setArr())
  if gArr[1] == 55 and gCalls == 1 and gOrder == 12 and k == 6:
    symexTarget("ia")
  if gArr[1] != 55 or gCalls != 1 or gOrder != 12:
    symexTarget("ia_dead")

proc sutIdxCallShrunk(k: int) =
  ## The seq is shortened after the index was checked: Nim then accesses
  ## through a length it never checked.
  if k < 0 or k > 1000: return
  gs = @[k, 20, 30]
  gCalls = 0
  gOrder = 0
  touch(gs[nextI()], shrinkS())
  if k == 1: symexTarget("is")

proc sutIdxCallProcSeq(k: int) =
  ## Through a proc value (S8bh's `closureCallIR`).
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  gOrder = 0
  let f = touch
  f(gs[nextI()], dblS())
  if gs[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 4:
    symexTarget("ps")
  if gs[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12:
    symexTarget("ps_dead")

proc sutIdxCallProcArr(k: int) =
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  gCalls = 0
  gOrder = 0
  let f = touch
  f(gArr[nextI()], dblArr())
  if gArr[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 3:
    symexTarget("pa")
  if gArr[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12:
    symexTarget("pa_dead")

proc sutIdxCallValue(k: int) =
  ## The index calls through a proc value: no `result` to name its value
  ## by, so the write-back, which would call it again, declines.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  gOrder = 0
  let fv = nextI
  touch(gs[fv()], dblS())
  if gs[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12: symexTarget("fs_dead")

suite "S8br: a call in a by-address actual's index":

  test "nim":
    gArr = [10, 20, 30]
    gCalls = 0
    gOrder = 0
    touch(gArr[nextI()], dblArr())
    check gArr == [10, 45, 30] and gCalls == 1 and gOrder == 12
    gs = @[10, 20, 30]
    gCalls = 0
    gOrder = 0
    touch(gs[nextI()], dblS())
    check gs == @[10, 45, 30] and gCalls == 1 and gOrder == 12
    gArr = [10, 20, 30]
    gi = 0
    gCalls = 0
    touch(gArr[curI()], incI())
    check gArr == [15, 20, 30] and gi == 1 and gCalls == 1
    gArr = [10, 20, 30]
    gCalls = 0
    gOrder = 0
    touchP(addr gArr[nextI()], setArr())
    check gArr == [10, 55, 30] and gCalls == 1 and gOrder == 12
    block:
      let f = touch
      gs = @[10, 20, 30]
      gCalls = 0
      gOrder = 0
      f(gs[nextI()], dblS())
      check gs == @[10, 45, 30] and gCalls == 1 and gOrder == 12
      gArr = [10, 20, 30]
      gCalls = 0
      gOrder = 0
      f(gArr[nextI()], dblArr())
      check gArr == [10, 45, 30] and gCalls == 1 and gOrder == 12
      let fv = nextI
      gs = @[10, 20, 30]
      gCalls = 0
      gOrder = 0
      touch(gs[fv()], dblS())
      check gs == @[10, 45, 30] and gCalls == 1 and gOrder == 12

  test "a call in a by-address actual's index":
    ## RED: `ic`, `iv`, `ia` and their twins declined (`unsupported nnkAsgn
    ## shape`); `iq` `sxUnsat` and `iq_dead` a false `sxSat` (the seq
    ## copy-out called `nextI` a second time). `is` declined already.
    replays(sutIdxCall, "ic")
    discard verdict(sutIdxCall, "ic_dead", sxUnsat)
    replays(sutIdxCallSeq, "iq")
    discard verdict(sutIdxCallSeq, "iq_dead", sxUnsat)
    replays(sutIdxCallKept, "iv")
    discard verdict(sutIdxCallKept, "iv_dead", sxUnsat)
    discard verdict(sutIdxCallAddr, "ia", sxSat)
    discard verdict(sutIdxCallAddr, "ia_dead", sxUnsat)
    declines(sutIdxCallShrunk, "is", "never checked")

  test "an index call the walk cannot name declines":
    ## RED: `fs_dead` a false `sxSat` (the seq copy-out called `fv` again).
    declinesOp(sutIdxCallValue, "fs_dead", "evaluates once, where the argument stands")

  test "a call in a by-address actual's index, through a proc value":
    ## RED: `ps` `sxUnsat` and `ps_dead` a false `sxSat` (the seq copy-out
    ## called `nextI` a second time); `pa` and its twin declined.
    replays(sutIdxCallProcSeq, "ps")
    discard verdict(sutIdxCallProcSeq, "ps_dead", sxUnsat)
    replays(sutIdxCallProcArr, "pa")
    discard verdict(sutIdxCallProcArr, "pa_dead", sxUnsat)

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 229
