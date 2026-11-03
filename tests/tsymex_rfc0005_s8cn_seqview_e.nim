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
## RFC-0005 S8cm: part 5 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview`, `tsymex_rfc0005_s8cn_seqview_b`,
## `tsymex_rfc0005_s8cn_seqview_c`, `tsymex_rfc0005_s8cn_seqview_d`,
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

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000: return

# ---- A raise out of a callee holding the view --------------------------------

proc wrRaise(v: var int; t: Table[string, int]; k: string) =
  v = 9
  if t[k] == 9: raise newException(ValueError, "x")
proc sWrRaise(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  try:
    for k, v in t.mpairs:
      wrRaise(v, t, k)
    symexTarget("wr_noraise")
  except ValueError:
    if t["a"] == 9: symexTarget("wr_live")
    else: symexTarget("wr_dead")
proc wrOnly(v: var int) =
  v = 9
  raise newException(ValueError, "x")
proc sWrOnly(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  try:
    for k, v in t.mpairs:
      wrOnly(v)
  except ValueError:
    if t["a"] == 9: symexTarget("wo_live")
    else: symexTarget("wo_dead")

# ---- The callee holding the memory -------------------------------------------

proc tc1(v: var int; t: Table[string, int]; k: string): int =
  let c = t   # a cursor: never mutated
  v = 77
  c[k]
proc tc2(v: var int; t: Table[string, int]; k: string): int =
  var c = t   # a copy: mutated below
  v = 77
  result = c[k]
  c[k] = 1
proc sTc1(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if tc1(v, t, k) == 77: symexTarget("tc1_shared")
proc sTc2(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if tc2(v, t, k) == x: symexTarget("tc2_copy")
proc sqc(v: var int; s: seq[int]): int =
  let c = s
  v = 5
  c[0]
proc sCur(n: int) =
  guardN()
  if n == 5: return
  var s = @[n]
  if sqc(s[0], s) == 5: symexTarget("cu_shared")
proc sql(v: var int; s: seq[int]): int =
  for x in s:   # `items` yields `lent`
    v = 5
    result = x
proc sLent(n: int) =
  guardN()
  if n == 5: return
  var s = @[n]
  if sql(s[0], s) == 5: symexTarget("le_new")
proc tv(v: var int; t: Table[string, int]): int =
  for x in t.values:   # `values` too
    v = 5
    result = x
proc sTv(t0: Table[string, int]) =
  guardT()
  if x == 5: return
  var t = t0
  for k, v in t.mpairs:
    if tv(v, t) == 5: symexTarget("tv_new")

suite "S8cn: a raise out of a callee holding the view":
  test "the view's write reaches the Table":
    decidedT(sWrRaise, "wr_noraise", sxUnsat)
    decidedT(sWrRaise, "wr_live", sxSat)
    decidedT(sWrRaise, "wr_dead", sxUnsat)
    decidedT(sWrOnly, "wo_live", sxSat)
    decidedT(sWrOnly, "wo_dead", sxUnsat)

suite "S8cn: the callee holding the memory":
  test "native: a cursor shares, a mutated local copies":
    var shared, copied = false
    for x in ns:
      if x == 77: continue
      if "tc1_shared" in hits(sTc1({"a": x}.toTable)): shared = true
      if "tc2_copy" in hits(sTc2({"a": x}.toTable)): copied = true
    check shared
    check copied
    check "cu_shared" in hits(sCur(1))
    check "le_new" in hits(sLent(1))
    check "tv_new" in hits(sTv({"a": 1}.toTable))
  test "declines":
    declined(sTc1, "tc1_shared", "holding the whole of one")
    declined(sTc2, "tc2_copy", "holding the whole of one")
    declined(sCur, "cu_shared", "holding the whole of one")
    declined(sLent, "le_new", "holding the whole of one")
    declined(sTv, "tv_new", "holding the whole of one")
