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
## RFC-0005 S8cm: part 3 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview`, `tsymex_rfc0005_s8cn_seqview_b`,
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

template declined(fn: typed; lbl: static string; why: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check why in show(r.errors)

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000: return

# ---- A seq's element with its seq --------------------------------------------

proc sq(v: var int; s: seq[int]; i: int): int =
  v += 1
  s[i]
type H = object
  s: seq[int]
  z: int
proc sqh(v: var int; h: H; i: int): int =
  v += 1
  h.s[i]
proc sHold(n: int) =
  guardN()
  var h = H(s: @[n], z: 0)
  let r = sqh(h.s[0], h, 0)
  if r == n + 1: symexTarget("h_live")
  if r == n: symexTarget("h_dead")
proc sq2(a, b: var int; s: seq[int]): int =
  a = 1
  b = 2
  s[0] * 10 + s[1]
proc sTwo(n: int) =
  var s = @[n, n]
  if sq2(s[0], s[1], s) == 12: symexTarget("two_live")
  else: symexTarget("two_dead")
proc sq2s(a, b: var int; s: seq[int]): int =
  a = 1
  b + s[0] * 10
proc sTwoSame(n: int) =
  var s = @[n]
  if sq2s(s[0], s[0], s) == 11: symexTarget("ts_live")
  else: symexTarget("ts_dead")
proc sSymIx(n: int) =
  guardN()
  let i = if n > 0: 1 else: 0
  var s = @[n, n + 1]
  let r = sq(s[i], s, 0)
  if i == 0 and r == n + 1: symexTarget("si_same_live")
  if i == 1 and r == n: symexTarget("si_other_live")
  if i == 0 and r == n: symexTarget("si_same_dead")
  if i == 1 and r == n + 1: symexTarget("si_other_dead")

suite "S8cn item 5: a seq's element with its seq":
  test "a holder of the seq":
    decidedN(sHold, "h_live", sxSat)
    decidedN(sHold, "h_dead", sxUnsat)
  test "two elements, a computed index":
    decidedN(sTwo, "two_live", sxSat)
    decidedN(sTwo, "two_dead", sxUnsat)
    declined(sTwoSame, "ts_live", "may reach it another way")
    declined(sTwoSame, "ts_dead", "may reach it another way")
    decidedN(sSymIx, "si_same_live", sxSat)
    decidedN(sSymIx, "si_other_live", sxSat)
    decidedN(sSymIx, "si_same_dead", sxUnsat)
    decidedN(sSymIx, "si_other_dead", sxUnsat)
