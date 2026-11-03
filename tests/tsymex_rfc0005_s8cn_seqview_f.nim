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
## RFC-0005 S8cm: part 6 of 6 of this suite, with
## `tsymex_rfc0005_s8cn_seqview`, `tsymex_rfc0005_s8cn_seqview_b`,
## `tsymex_rfc0005_s8cn_seqview_c`, `tsymex_rfc0005_s8cn_seqview_d`,
## `tsymex_rfc0005_s8cn_seqview_e`. Split so that each part compiles and runs
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

# ---- A key added under the view ----------------------------------------------

proc sRehash(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  for k, v in t.mpairs:
    for key in ["b", "c", "d", "e", "f", "g", "h", "i", "j", "l", "m"]:
      t[key] = 1
    v = 9
    break
  # Natively lost, at this capacity.
  if t["a"] != 9: symexTarget("rh_lost")
proc wrNew(v: var int; t: var Table[string, int]) =
  t["b"] = 1
  v = 9
proc sNewKey(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  for k, v in t.mpairs:
    wrNew(v, t)
    break
  if t["a"] == 9: symexTarget("nk_seen")
proc wrSame(v: var int; t: var Table[string, int]): int =
  t["b"] = 1
  v
proc sNewRead(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    let r = wrSame(v, t)
    if r == x and t["b"] == 1: symexTarget("nr_live")
    if r != x: symexTarget("nr_dead")
    break

proc sPtrGrow(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  for k, v in t.mpairs:
    let p = addr v
    for key in ["b", "c", "d", "e", "f", "g", "h", "i", "j", "l", "m"]:
      t[key] = 1
    p[] = 9
    break
  if t["a"] != 9: symexTarget("pg_lost")

proc sPtrGrow1(t0: Table[string, int]) =
  guardT()
  if x == 9: return
  var t = t0
  for k, v in t.mpairs:
    let p = addr v
    t["b"] = 1
    p[] = 9
    break
  if t["a"] != 9: symexTarget("p1_lost")

suite "S8cn: a key added under the view":
  test "a write past it declines, at any capacity":
    check "rh_lost" in hits(sRehash({"a": 1}.toTable))
    declined(sRehash, "rh_lost", "written after a key was added")
    check "nk_seen" in hits(sNewKey({"a": 1}.toTable))
    declined(sNewKey, "nk_seen", "written after a key was added")
  test "a pointer to the view: declines where the key is added":
    check "pg_lost" in hits(sPtrGrow({"a": 1}.toTable))
    declined(sPtrGrow1, "p1_lost", "while a pointer to the loop variable")
  test "no write past it: decided":
    decidedT(sNewRead, "nr_live", sxSat)
    decidedT(sNewRead, "nr_dead", sxUnsat)

suite "S8cn: walker version":
  test "the floor":
    check parseInt(symexWalkerVersion) >= 251
