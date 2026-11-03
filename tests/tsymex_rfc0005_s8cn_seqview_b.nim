## RFC-0005 slice S8cn, item 5 -- a proc value's view and its Table, and a seq's
## element passed with its seq.
##
## `let f = rab; f(v, t, k)` is the direct call (a `let` is written once), and
## `f(s[i], s)` has one location through two formals, as an `mpairs` view and
## its Table have. Both were declined. Every label is run natively too.
##
## The rest are wrong verdicts this slice found next to them, each pinned with
## its native run: a raise out of a callee lost the view's write when the Table
## went by value; a local or a loop in the callee holding the container's memory
## (Nim's cursor inference and `lent`); a key added under a view, which may
## rehash the Table and leave the view on the old slots.
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview`, `tsymex_rfc0005_s8cn_seqview_c`,
## `tsymex_rfc0005_s8cn_seqview_d`, `tsymex_rfc0005_s8cn_seqview_e`,
## `tsymex_rfc0005_s8cn_seqview_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 94 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template decidedN(fn: typed; lbl: static string; want: typed) =
  ## `fn` over an int: the verdict, each native run's agreement, the witness.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for n in ns:
      if lbl in hits(fn(n)): live = true
    if want == sxUnsat: check not live
    else: check live
    if r.status == sxSat:
      check lbl in hits(fn(r.witness[0]))

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000: return

# ---- A seq's element with its seq --------------------------------------------

proc sq(v: var int; s: seq[int]; i: int): int =
  v += 1
  s[i]
proc sqw(v: var int; s: var seq[int]; i: int): int =
  s[i] = 50
  v
proc sLocR(n: int) =
  guardN()
  var s = @[n]
  for x in mitems(s):
    let r = sq(x, s, 0)
    if r == n + 1: symexTarget("lr_live")
    if r == n: symexTarget("lr_dead")
proc sLocW(n: int) =
  guardN()
  var s = @[n]
  for x in mitems(s):
    let r = sqw(x, s, 0)
    if r == 50: symexTarget("lw_live")
    if r == n and n != 50: symexTarget("lw_dead")
proc sLocP(n: int) =
  guardN()
  var s = @[n]
  for i, x in s.mpairs:
    let r = sq(x, s, i)
    if r == n + 1: symexTarget("lp_live")
    if r == n: symexTarget("lp_dead")
proc sLocIdx(n: int) =
  guardN()
  var s = @[n]
  let r = sq(s[0], s, 0)
  if r == n + 1: symexTarget("li_live")
  if r == n: symexTarget("li_dead")
var gs: seq[int]
proc sGloR(n: int) =
  guardN()
  gs = @[n]
  for i, x in gs.mpairs:
    let r = sq(x, gs, i)
    if r == n + 1: symexTarget("gr_live")
    if r == n: symexTarget("gr_dead")
proc sqvw(v: var int; s: var seq[int]; i: int): int =
  v = 7
  result = s[i]
  s[i] = 9
  result += v * 100
proc sVW(n: int) =
  var s = @[n]
  let r = sqvw(s[0], s, 0)
  if r == 907 and s[0] == 9: symexTarget("vw_live")
  else: symexTarget("vw_dead")

suite "S8cn item 5: a seq's element with its seq":
  test "local, mitems and mpairs and direct":
    decidedN(sLocR, "lr_live", sxSat)
    decidedN(sLocR, "lr_dead", sxUnsat)
    decidedN(sLocW, "lw_live", sxSat)
    decidedN(sLocW, "lw_dead", sxUnsat)
    decidedN(sLocP, "lp_live", sxSat)
    decidedN(sLocP, "lp_dead", sxUnsat)
    decidedN(sLocIdx, "li_live", sxSat)
    decidedN(sLocIdx, "li_dead", sxUnsat)
  test "global":
    decidedN(sGloR, "gr_live", sxSat)
    decidedN(sGloR, "gr_dead", sxUnsat)
  test "both written, in order":
    decidedN(sVW, "vw_live", sxSat)
    decidedN(sVW, "vw_dead", sxUnsat)
