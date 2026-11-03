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
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview_b`, `tsymex_rfc0005_s8cn_seqview_c`,
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

template decidedT(fn: typed; lbl: static string; want: typed) =
  ## As `decidedN`, over a one-key table.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for n in ns:
      if lbl in hits(fn({"a": n}.toTable)): live = true
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

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

# ---- A proc value ------------------------------------------------------------

proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]
proc wab(v: var int; t: var Table[string, int]; k: string): int =
  t[k] = 50
  v
proc sPV(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = rab
  for k, v in t.mpairs:
    let r = f(v, t, k)
    if r == x + 1: symexTarget("pv_live")
    if r == x: symexTarget("pv_dead")
proc sPVChain(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = wab
  let g = f
  for k, v in t.mpairs:
    let r = g(v, t, k)
    if r == 50: symexTarget("pc_live")
    if r == x and x != 50: symexTarget("pc_dead")
proc tOnly(t: var Table[string, int]; k: string): int =
  t[k] = 7
  t[k]
proc sPVTable(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = tOnly
  if f(t, "a") == 7 and t["a"] == 7: symexTarget("pt_live")
  else: symexTarget("pt_dead")
# Still a proc value used as one.
proc sPVVar(t0: Table[string, int]) =
  guardT()
  var t = t0
  var f = rab
  for k, v in t.mpairs:
    if f(v, t, k) == x + 1: symexTarget("pv2_live")
proc apply(f: proc(v: var int; t: Table[string, int]; k: string): int {.nimcall.};
           t: var Table[string, int]): int =
  for k, v in t.mpairs:
    result = f(v, t, k)
proc sPVParam(t0: Table[string, int]) =
  guardT()
  var t = t0
  if apply(rab, t) == x + 1: symexTarget("pv3_live")

suite "S8cn item 5: a proc value":
  test "a let names its proc: decided":
    decidedT(sPV, "pv_live", sxSat)
    decidedT(sPV, "pv_dead", sxUnsat)
    decidedT(sPVChain, "pc_live", sxSat)
    decidedT(sPVChain, "pc_dead", sxUnsat)
    decidedT(sPVTable, "pt_live", sxSat)
    decidedT(sPVTable, "pt_dead", sxUnsat)
  test "a var or a parameter: the closure path declines a view and its Table":
    declined(sPVVar, "pv2_live", "feUnsupportedOp")
    declined(sPVParam, "pv3_live", "feUnsupportedOp")
