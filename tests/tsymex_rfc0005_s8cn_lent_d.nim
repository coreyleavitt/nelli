## RFC-0005 slice S8cn -- a `lent` `for` loop, and a `let` over a container, with
## a write during the variable's life.
##
## The walk binds a loop variable or a `let` to the value read where it stands.
## Natively `items` over a seq or an openArray, and a Table's `values`, yield the
## element's own memory, so a write to the container in the body is seen through
## the variable. `let c = s` shares under `--mm:refc` always and under orc or arc
## when cursor inference proves it, which turns on the whole routine:
## `tsymex_rfc0005_s8cn_lentnative` pins that, on each memory manager. Both are
## declined when the body (a callee, a pointer, a global alias included) may
## write; the exact model is for RFC-0016. The forms Nim copies on every setting
## stay decided: scalar elements through `pairs`, an array's `items`, a Table's
## `pairs`. Every label runs natively.
##
## RFC-0005 S8cm: part 4 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent`,
## `tsymex_rfc0005_s8cn_lent_b`, `tsymex_rfc0005_s8cn_lent_c`,
## `tsymex_rfc0005_s8cn_lent_e`, `tsymex_rfc0005_s8cn_lent_f`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 95 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template declined(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "memory" in show(r.errors)

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let n = t0["a"]
  if n > 1000 or n < -1000 or n == 99: return

template decidedT(fn: typed; lbl: static string; want: typed) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for n in ns:
      if lbl in hits(fn({"a": n}.toTable)): live = true
    if want == sxUnsat: check not live
    else: check live
var gt: Table[string, int]
proc wt() = gt["a"] = 99
proc wtv(t: var Table[string, int]) = t["a"] = 99

# ---- Table ---------------------------------------------------------------------

proc tvDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for v in t.values:
    t["a"] = 99
    if v == 99: symexTarget("tv_new")
    if v == n: symexTarget("tv_old")
proc tvGlobal(t0: Table[string, int]) =
  guardT()
  gt = t0
  for v in gt.values:
    wt()
    if v == 99: symexTarget("tg_new")
    if v == n: symexTarget("tg_old")
proc tvVar(t0: Table[string, int]) =
  guardT()
  var t = t0
  for v in t.values:
    wtv(t)
    if v == 99: symexTarget("tc_new")
    if v == n: symexTarget("tc_old")
proc tvPtr(t0: Table[string, int]) =
  guardT()
  var t = t0
  let p = addr t
  for v in t.values:
    p[]["a"] = 99
    if v == 99: symexTarget("tq_new")
    if v == n: symexTarget("tq_old")
proc tkDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k in t.keys:
    t[k] = 99
    if t[k] == 99: symexTarget("tk_new")
    if t[k] == n: symexTarget("tk_old")
proc tvNoWrite(t0: Table[string, int]) =
  guardT()
  var t = t0
  var c = 0
  for v in t.values:
    c = v
  if c == n: symexTarget("tn_live")
  else: symexTarget("tn_dead")
proc tmDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for v in t.mvalues:
    t["a"] = 99
    if v == 99: symexTarget("tm_live")
    if v == n: symexTarget("tm_dead")

# ---- string --------------------------------------------------------------------

proc strItems(n: int) =
  guardN()
  var st = "ab"
  if n == 0: st[0] = 'c'
  for c in st:
    st[0] = 'z'
    if c == 'z': symexTarget("st_new")

suite "S8cn: a Table's values and keys":
  test "declines":
    declined(tvDirect, "tv_new"); declined(tvDirect, "tv_old")
    declined(tvGlobal, "tg_new"); declined(tvGlobal, "tg_old")
    declined(tvVar, "tc_new"); declined(tvVar, "tc_old")
    declined(tvPtr, "tq_new"); declined(tvPtr, "tq_old")
    declined(tkDirect, "tk_new"); declined(tkDirect, "tk_old")
  test "no write: decided":
    decidedT(tvNoWrite, "tn_live", sxSat); decidedT(tvNoWrite, "tn_dead", sxUnsat)
  test "mvalues: seen, or declined":
    let a = symexFind(tmDirect, tLabel("tm_dead"))
    check a.status != sxSat
    let b = symexFind(tmDirect, tLabel("tm_live"))
    check b.status != sxUnsat

suite "S8cn: a string":
  test "declines":
    check symexFind(strItems, tLabel("st_new")).status == sxUnknown
