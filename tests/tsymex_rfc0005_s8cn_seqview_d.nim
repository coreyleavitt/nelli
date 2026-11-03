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
## RFC-0005 S8cm: part 4 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview`, `tsymex_rfc0005_s8cn_seqview_b`,
## `tsymex_rfc0005_s8cn_seqview_c`, `tsymex_rfc0005_s8cn_seqview_e`,
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
var gs: seq[int]
proc inner(v: var int; s: seq[int]): int =
  v = 11
  s[0]
proc outer(v: var int; s: seq[int]): int =
  v = 5
  inner(v, s) + v
proc sPassOn(n: int) =
  var s = @[n]
  if outer(s[0], s) == 22: symexTarget("po_live")
  else: symexTarget("po_dead")
proc viaVar(s: var seq[int]): int =
  sq(s[0], s, 0)
proc sViaVar(n: int) =
  guardN()
  var s = @[n]
  if viaVar(s) == n + 1 and s[0] == n + 1: symexTarget("vv_live")
  else: symexTarget("vv_dead")
proc sqr(v: var int; s: seq[int]) =
  v = 3
  if s[0] == 3: raise newException(ValueError, "x")
proc sRaise(n: int) =
  var s = @[n]
  try:
    sqr(s[0], s)
    symexTarget("rs_dead")
  except ValueError:
    if s[0] == 3: symexTarget("rs_live")
proc sqs(v: var string; s: seq[string]): int =
  v.add "x"
  s[0].len
proc sStr(n: int) =
  var s = @["ab"]
  if sqs(s[0], s) == 3: symexTarget("st_live")
  else: symexTarget("st_dead")
proc sAddr(n: int) =
  guardN()
  var s = @[n]
  let p = addr s
  let r = sq(s[0], s, 0)
  if r == n + 1 and p[][0] == n + 1: symexTarget("ad_live")
  else: symexTarget("ad_dead")
proc sqGrow(v: var int; s: var seq[int]): int =
  v += 1
  s.add 3
  s.len
proc sGrow(n: int) =
  guardN()
  var s = @[n]
  if sqGrow(s[0], s) == 2: symexTarget("gw_any")
proc sqAssign(v: var int; s: var seq[int]) =
  s = @[1]
  v = 2
proc sAssign(n: int) =
  var s = @[n]
  sqAssign(s[0], s)
  if s[0] == 2: symexTarget("as_any")
proc sqChain(v: var int; s: var seq[int]) =
  var c = s
  c[0] = 2
  s = c      # other memory, though its term is a store over the old
  v = 3
proc sChain(n: int) =
  var s = @[n]
  sqChain(s[0], s)
  if s[0] == 2: symexTarget("ch_any")
# By a global's name the walk passes a copy, and the name is withheld.
proc sqG(v: var int; i: int): int =
  v += 1
  gs[i]
proc sGloD(n: int) =
  guardN()
  gs = @[n]
  for i, x in gs.mpairs:
    if sqG(x, i) == n + 1: symexTarget("gd_live")

suite "S8cn item 5: a seq's element with its seq":
  test "passed on, through a var formal, past a raise":
    decidedN(sPassOn, "po_live", sxSat)
    decidedN(sPassOn, "po_dead", sxUnsat)
    decidedN(sViaVar, "vv_live", sxSat)
    decidedN(sViaVar, "vv_dead", sxUnsat)
    decidedN(sRaise, "rs_live", sxSat)
    decidedN(sRaise, "rs_dead", sxUnsat)
  test "a string element, and a seq whose address is taken":
    decidedN(sStr, "st_live", sxSat)
    decidedN(sStr, "st_dead", sxUnsat)
    decidedN(sAddr, "ad_live", sxSat)
    decidedN(sAddr, "ad_dead", sxUnsat)
  test "resized or assigned whole while held: declines":
    declined(sGrow, "gw_any", "resized or assigned whole")
    declined(sAssign, "as_any", "resized or assigned whole")
    declined(sChain, "ch_any", "holding the whole of one")
  test "reached by a global's name: declines":
    declined(sGloD, "gd_live", "reached by a callee both through")
