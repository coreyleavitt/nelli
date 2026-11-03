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
## RFC-0005 S8cm: part 2 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent`,
## `tsymex_rfc0005_s8cn_lent_c`, `tsymex_rfc0005_s8cn_lent_d`,
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

template decided(fn: typed; lbl: static string; want: typed) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for n in ns:
      if lbl in hits(fn(n)): live = true
    if want == sxUnsat: check not live
    else: check live

template nativeSees(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      if n == 99: continue
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let n = t0["a"]
  if n > 1000 or n < -1000 or n == 99: return

template nativeSeesT(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      let h = hits(fn({"a": n}.toTable))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

var gs: seq[int]
var ga: array[2, int]
# A closure call's decline, with the target in the body.
proc gwBody(a: seq[int]) =
  gs[0] = 99
  if a[0] == 99: symexTarget("cg_new")
  else: symexTarget("cg_old")
proc cGlobal(n: int) =
  guardN()
  gs = @[n]
  var f = gwBody
  f(gs)
proc cLambda(n: int) =
  guardN()
  var s = @[n]
  let f = proc (a: seq[int]) =
    s[0] = 99
    if a[0] == 99: symexTarget("cl_new")
    else: symexTarget("cl_old")
  f(s)
proc tvBody(v: var int; t: Table[string, int]) =
  v = 99
  if t["a"] == 99: symexTarget("cv_new")
  else: symexTarget("cv_old")
proc cVarCall(t0: Table[string, int]) =
  guardT()
  var t = t0
  var f = tvBody
  f(t["a"], t)
# The calling path's branches hold in the body.
proc pcBody(a: int) =
  if a == 77: symexTarget("cp_never")
proc cPcVar(n: int) =
  var f = pcBody
  if n != 77: f(n)
proc cPcLambda(n: int) =
  let f = proc (a: int) =
    if a == 77: symexTarget("cp_never")
  if n != 77: f(n)
proc cPcLive(n: int) =
  var f = pcBody
  if n > 70: f(n)
proc iNoWrite(n: int) =
  guardN()
  var s = @[n]
  var t = 0
  for x in s:
    t = x + 1
  if t == n + 1: symexTarget("nw_live")
  else: symexTarget("nw_dead")
proc iOther(n: int) =
  guardN()
  var s = @[n]
  var o = @[0]
  for x in s:
    o[0] = x
  if o[0] == n: symexTarget("io_live")
  else: symexTarget("io_dead")

# ---- A copy on every setting: scalar `pairs`, array `items` --------------------

proc pSeq(n: int) =
  guardN()
  var s = @[n, n + 1]
  for i, x in s:
    s[1] = 99
    if i == 0 and x == n: symexTarget("ps_live")
    if i == 0 and x == 99: symexTarget("ps_dead")
    if i == 1 and x == 99: symexTarget("ps_next")
proc pArrItems(n: int) =
  guardN()
  var a = [n, n + 1]
  var c = 0
  for x in a:
    a[0] = 99
    a[1] = 99
    if c == 0 and x == n: symexTarget("aa_live")
    if c == 0 and x == 99: symexTarget("aa_dead")
    if c == 1 and x == 99: symexTarget("aa_next")
    inc c
proc pArrGlobal(n: int) =
  guardN()
  ga = [n, n + 1]
  for x in ga:
    ga[0] = 99
    if x == n: symexTarget("ag_live")
    if x == 99: symexTarget("ag_dead")
    break

suite "S8cn: seq `items` with a write in the body":
  test "a target in the body of a declined closure call: never a false sxSat":
    nativeSees(cGlobal, "cg_new", "cg_old")
    nativeSees(cLambda, "cl_new", "cl_old")
    nativeSeesT(cVarCall, "cv_new", "cv_old")
    check symexFind(cGlobal, tLabel("cg_old")).status == sxUnknown
    check symexFind(cLambda, tLabel("cl_old")).status == sxUnknown
    check symexFind(cVarCall, tLabel("cv_old")).status == sxUnknown
  test "a target in a closure body: the calling path's branches hold":
    for n in [-1, 0, 76, 77, 78, 177]:
      check "cp_never" notin hits(cPcVar(n))
      check "cp_never" notin hits(cPcLambda(n))
    check "cp_never" in hits(cPcLive(77))
    check symexFind(cPcVar, tLabel("cp_never")).status == sxUnsat
    check symexFind(cPcLambda, tLabel("cp_never")).status == sxUnsat
    check symexFind(cPcLive, tLabel("cp_never")).status == sxSat
  test "no write to the container: decided":
    decided(iNoWrite, "nw_live", sxSat); decided(iNoWrite, "nw_dead", sxUnsat)
    decided(iOther, "io_live", sxSat); decided(iOther, "io_dead", sxUnsat)

suite "S8cn: what Nim copies on every setting stays decided":
  test "scalar elements":
    decided(pSeq, "ps_live", sxSat); decided(pSeq, "ps_dead", sxUnsat)
    decided(pSeq, "ps_next", sxSat)
    decided(pArrItems, "aa_live", sxSat); decided(pArrItems, "aa_dead", sxUnsat)
    decided(pArrItems, "aa_next", sxSat)
    decided(pArrGlobal, "ag_live", sxSat); decided(pArrGlobal, "ag_dead", sxUnsat)
