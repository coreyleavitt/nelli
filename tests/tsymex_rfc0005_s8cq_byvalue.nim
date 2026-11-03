## RFC-0005 slice S8cq, item 1 -- a by-value formal and the memory Nim shares.
##
## Nim passes a formal by address when its type is over three words, a seq, a
## string, a set or an inheritable or `{.byref.}` object, and the walk binds it to
## a copy, so a write the callee makes through another name is read back through
## the formal natively and not in the walk: a false `sxUnsat` on the value it
## wrote and a false `sxSat` on the old one. The rule is inverted: a call is
## decided only when the type is on the allowlist (`typeCopiedByValue`, pinned on
## nine settings in `tsymex_rfc0005_s8cq_native`), or the callee with everything
## it reaches is proved to write nothing the actual could be (`byValueWritten`).
## Everything else declines; the exact model belongs to RFC-0016.
##
## A local's memory has no other name but a pointer to it, and S8bs keeps that cell
## and the formal one location, so a local actual stays decided; a formal whose
## address the callee takes, a routine actual, and a `var` of the same local decline.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex

var natHits: HashSet[string]

template nat(call: untyped) =
  block:
    symexCaptureBegin()
    try:
      call
    except CatchableError:
      discard
    for h in symexCaptureEnd(): natHits.incl h

template pin(fn: typed; lbl: static string; nativeHit: bool;
             want: SymexStatusKind) =
  ## Nim's own answer on the input loop above, then the walker's. Neither may
  ## contradict the other: `sxUnknown` is the decline RFC-0016 inherits.
  block:
    let r = symexFind(fn, tLabel(lbl))
    var parts: seq[string]
    for e in r.errors: parts.add $e.kind & ": " & e.msg
    checkpoint lbl & " " & $r.status & " [" & parts.join(", ") & "]"
    check (lbl in natHits) == nativeHit
    check r.status == want
    check not (nativeHit and r.status == sxUnsat)
    check not (not nativeHit and r.status == sxSat)

template pinFree(fn: typed; lbl: static string; want: SymexStatusKind) =
  ## As `pin`, for a shape Nim gives no one answer on: only the decline holds.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status
    check r.status == want
import nelli/smt/canonicalize
import std/tables
type Sm = object
  a: int
type Big = object
  a: array[16, int]
var gs: seq[int]
var gSm: Sm
var gBig: Big
var gR: ref int
var gN: int

proc gWrite(a: seq[int]): int =
  gs[0] = 50
  a[0]
proc gWriteSm(a: Sm): int =
  gSm.a = 50
  a.a
proc gWriteBig(a: Big): int =
  gBig.a[0] = 50
  a.a[0]
proc wr() = gs[0] = 50
proc outerR(a: seq[int]): int =
  wr()
  a[0]

proc sDirect(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let r = gWrite(gs)
  if r == 50: symexTarget("dg_r50")
  if r == x: symexTarget("dg_rx")
proc sSm(x: int) =
  if x == 50: return
  gSm = Sm(a: x)
  let r = gWriteSm(gSm)
  if r == 50: symexTarget("sm_r50")
  if r == x: symexTarget("sm_rx")
proc sBig(x: int) =
  if x == 50: return
  gBig.a[0] = x
  let r = gWriteBig(gBig)
  if r == 50: symexTarget("bg_r50")
  if r == x: symexTarget("bg_rx")
proc sInner(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  var s = s0
  proc inner(a: seq[int]): int =
    s[0] = 50
    a[0]
  let r = inner(s)
  if r == 50: symexTarget("in_r50")
  if r == x: symexTarget("in_rx")
proc sOuter(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let r = outerR(gs)
  if r == 50: symexTarget("ou_r50")
  if r == x: symexTarget("ou_rx")

# item 2
proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]
proc sVc(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  let r = rab(t["a"], t, "a")
  if r == x + 1: symexTarget("vc_rx1")
  if r == x: symexTarget("vc_rx")

# item 3
proc getR(): ref int =
  inc gN
  gR
var gSeqR: ref seq[int]
proc getSeqR(): ref seq[int] =
  inc gN
  gSeqR

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(sDirect(@[x]))
  nat(sSm(x))
  nat(sBig(x))
  nat(sInner(@[x]))
  nat(sOuter(@[x]))
  nat(sVc({"a": x}.toTable))

suite "tsymex_rfc0005_s8cq_byvalue":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 252

  test "verdicts against Nim":
    pin(sDirect, "dg_r50", true, sxUnknown)
    pin(sDirect, "dg_rx", false, sxUnknown)
    pin(sSm, "sm_r50", false, sxUnsat)
    pin(sSm, "sm_rx", true, sxSat)
    pin(sBig, "bg_r50", true, sxUnknown)
    pin(sBig, "bg_rx", false, sxUnknown)
    pin(sInner, "in_r50", true, sxUnknown)
    pin(sInner, "in_rx", false, sxUnknown)
    pin(sOuter, "ou_r50", true, sxUnknown)
    pin(sOuter, "ou_rx", false, sxUnknown)
    pin(sVc, "vc_rx1", true, sxUnknown)
    pin(sVc, "vc_rx", false, sxUnknown)
