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
var gt: Table[string, int]
var gstr: string
var gp: ptr seq[int]
type Obj2 = object
  a: int
  b: seq[int]

proc wr(v: var seq[int]) = v[0] = 99
proc wg() = gs[0] = 99
proc wgDeep() = wg()
proc wp() = gp[][0] = 99
proc wt() = gt["a"] = 99
proc wtv(t: var Table[string, int]) = t["a"] = 99

# ---- seq, `items`: the element's memory ---------------------------------------

proc iDirect(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    s[0] = 99
    if x == 99: symexTarget("id_new")
    if x == n: symexTarget("id_old")
proc iVarCallee(n: int) =
  guardN()
  var s = @[n]
  for x in s:
    wr(s)
    if x == 99: symexTarget("iv_new")
    if x == n: symexTarget("iv_old")
proc iGlobalName(n: int) =
  guardN()
  gs = @[n]
  for x in gs:
    gs[0] = 99
    if x == 99: symexTarget("in_new")
    if x == n: symexTarget("in_old")
proc iGlobalCallee(n: int) =
  guardN()
  gs = @[n]
  for x in gs:
    wgDeep()
    if x == 99: symexTarget("ig_new")
    if x == n: symexTarget("ig_old")
proc iPtrLocal(n: int) =
  guardN()
  var s = @[n]
  let p = addr s
  for x in s:
    p[][0] = 99
    if x == 99: symexTarget("ip_new")
    if x == n: symexTarget("ip_old")
proc iPtrGlobal(n: int) =
  guardN()
  gs = @[n]
  gp = addr gs
  for x in gs:
    wp()
    if x == 99: symexTarget("ipg_new")
    if x == n: symexTarget("ipg_old")
proc iElemPtr(n: int) =
  guardN()
  var s = @[n]
  let p = addr s[0]
  for x in s:
    p[] = 99
    if x == 99: symexTarget("ie_new")
    if x == n: symexTarget("ie_old")
proc iFormal(a: var seq[int]; n: int) =
  for x in a:
    a[0] = 99
    if x == 99: symexTarget("if_new")
    if x == n: symexTarget("if_old")
proc iFormalCall(n: int) =
  guardN()
  var s = @[n]
  iFormal(s, n)
proc oaLoop(a: openArray[int]; n: int) =
  for x in a:
    gs[0] = 99
    if x == 99: symexTarget("oa_new")
    if x == n: symexTarget("oa_old")
proc iOpenArray(n: int) =
  guardN()
  gs = @[n]
  oaLoop(gs, n)
proc twoInBody(a, b: var int) =
  a = 99
  if b == 99: symexTarget("tb_new")
  else: symexTarget("tb_old")
proc iTwoInBody(n: int) =
  guardN()
  var s = @[n]
  twoInBody(s[0], s[0])
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

# ---- Non-scalar elements: declined wherever the body may write -----------------

proc oPairs(n: int) =
  guardN()
  var s = @[Obj2(a: n, b: @[n])]
  for i, x in s:
    s[0].b[0] = 99
    if x.b[0] == 99: symexTarget("op_new")
    if x.b[0] == n: symexTarget("op_old")

# ---- `mitems` and `mpairs`: the memory, by the walk's substitution -------------

proc mDirect(n: int) =
  guardN()
  var s = @[n]
  for x in s.mitems:
    s[0] = 99
    if x == 99: symexTarget("md_live")
    if x == n: symexTarget("md_dead")
proc mPairs(n: int) =
  guardN()
  var s = @[n]
  for i, x in s.mpairs:
    s[0] = 99
    if x == 99: symexTarget("mp_live")
    if x == n: symexTarget("mp_dead")
proc mGlobalCallee(n: int) =
  guardN()
  gs = @[n]
  for x in gs.mitems:
    wg()
    if x == 99: symexTarget("mg_live")
    if x == n: symexTarget("mg_dead")
proc mPtr(n: int) =
  guardN()
  gs = @[n]
  gp = addr gs
  for x in gs.mitems:
    wp()
    if x == 99: symexTarget("mq_live")
    if x == n: symexTarget("mq_dead")

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
proc tpDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.pairs:
    t["a"] = 99
    if v == n: symexTarget("tp_live")
    if v == 99: symexTarget("tp_dead")
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

# ---- `let` over a container: the setting's choice ------------------------------

proc lGlobalCallee(n: int) =
  guardN()
  gs = @[n]
  let c = gs
  wg()
  if c[0] == 99: symexTarget("lg_a")
  if c[0] == n: symexTarget("lg_b")
proc lGlobalName(n: int) =
  guardN()
  gs = @[n]
  let c = gs
  gs[0] = 99
  if c[0] == 99: symexTarget("ln_a")
  if c[0] == n: symexTarget("ln_b")
proc lLocal(n: int) =
  guardN()
  var s = @[n]
  let c = s
  s[0] = 99
  if c[0] == 99: symexTarget("ll_a")
  if c[0] == n: symexTarget("ll_b")
proc lVarCallee(n: int) =
  guardN()
  var s = @[n]
  let c = s
  wr(s)
  if c[0] == 99: symexTarget("lv_a")
  if c[0] == n: symexTarget("lv_b")
proc lPtr(n: int) =
  guardN()
  var s = @[n]
  let p = addr s
  let c = s
  p[][0] = 99
  if c[0] == 99: symexTarget("lp_a")
  if c[0] == n: symexTarget("lp_b")
proc lTable(n: int) =
  guardN()
  gt = {"a": n}.toTable
  let c = gt
  wt()
  if c["a"] == 99: symexTarget("lt_a")
  if c["a"] == n: symexTarget("lt_b")
proc lField(n: int) =
  guardN()
  var o = Obj2(a: 1, b: @[n])
  let c = o.b
  o.b[0] = 99
  if c[0] == 99: symexTarget("lf_a")
  if c[0] == n: symexTarget("lf_b")
proc lString(n: int) =
  guardN()
  gstr = "ab"
  let c = gstr
  gstr[0] = 'z'
  if c[0] == 'z' and n == 0: symexTarget("ls_a")
  if c[0] == 'a' and n == 0: symexTarget("ls_b")
proc lObject(n: int) =
  guardN()
  var o = Obj2(a: 1, b: @[n])
  let c = o
  o.b[0] = 99
  if c.b[0] == 99: symexTarget("lo_a")
  if c.b[0] == n: symexTarget("lo_b")
proc lBefore(n: int) =
  guardN()
  var s = @[n]
  s[0] = n + 1
  let c = s
  if c[0] == n + 1: symexTarget("lb_live")
  else: symexTarget("lb_dead")
proc lFormal(s0: seq[int]) =
  # A formal, so a pointer may reach it; nothing here writes through one, and
  # the target's own runtime call is not a write.
  if s0.len != 1 or s0[0] > 1000 or s0[0] < -1000: return
  let c = s0
  if c[0] == s0[0]: symexTarget("lc_live")
  else: symexTarget("lc_dead")
proc lVar(n: int) =
  guardN()
  var s = @[n]
  var c = s
  s[0] = 99
  if c[0] == n: symexTarget("va_live")
  if c[0] == 99: symexTarget("va_dead")
proc lArr(n: int) =
  guardN()
  var a = [n, 0]
  let c = a
  a[0] = 99
  if c[0] == n: symexTarget("ar_live")
  if c[0] == 99: symexTarget("ar_dead")

suite "S8cn: seq `items` with a write in the body":
  test "native: the element's memory":
    nativeSees(iDirect, "id_new", "id_old")
    nativeSees(iVarCallee, "iv_new", "iv_old")
    nativeSees(iGlobalName, "in_new", "in_old")
    nativeSees(iGlobalCallee, "ig_new", "ig_old")
    nativeSees(iPtrLocal, "ip_new", "ip_old")
    nativeSees(iPtrGlobal, "ipg_new", "ipg_old")
    nativeSees(iElemPtr, "ie_new", "ie_old")
    nativeSees(iFormalCall, "if_new", "if_old")
    nativeSees(iOpenArray, "oa_new", "oa_old")
  test "declines":
    declined(iDirect, "id_new"); declined(iDirect, "id_old")
    declined(iVarCallee, "iv_new"); declined(iVarCallee, "iv_old")
    declined(iGlobalName, "in_new"); declined(iGlobalName, "in_old")
    declined(iGlobalCallee, "ig_new"); declined(iGlobalCallee, "ig_old")
    declined(iPtrLocal, "ip_new"); declined(iPtrLocal, "ip_old")
    declined(iPtrGlobal, "ipg_new"); declined(iPtrGlobal, "ipg_old")
    declined(iElemPtr, "ie_new"); declined(iElemPtr, "ie_old")
    declined(iFormalCall, "if_new"); declined(iFormalCall, "if_old")
    declined(iOpenArray, "oa_new"); declined(iOpenArray, "oa_old")
  test "a target in the body of a declined call declines":
    nativeSees(iTwoInBody, "tb_new", "tb_old")
    check symexFind(iTwoInBody, tLabel("tb_new")).status == sxUnknown
    check symexFind(iTwoInBody, tLabel("tb_old")).status == sxUnknown
  test "a target in the body of a declined closure call: never a false sxSat":
    nativeSees(cGlobal, "cg_new", "cg_old")
    nativeSees(cLambda, "cl_new", "cl_old")
    nativeSeesT(cVarCall, "cv_new", "cv_old")
    for r in [symexFind(cGlobal, tLabel("cg_old")),
              symexFind(cLambda, tLabel("cl_old")),
              symexFind(cVarCall, tLabel("cv_old"))]:
      check r.status == sxUnknown
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
  test "a Table's pairs":
    decidedT(tpDirect, "tp_live", sxSat); decidedT(tpDirect, "tp_dead", sxUnsat)
  test "non-scalar elements decline":
    declined(oPairs, "op_new"); declined(oPairs, "op_old")

suite "S8cn: mitems and mpairs":
  test "the write is seen":
    decided(mDirect, "md_live", sxSat); decided(mDirect, "md_dead", sxUnsat)
    decided(mPairs, "mp_live", sxSat); decided(mPairs, "mp_dead", sxUnsat)
  test "a global's callee and a pointer: seen, or declined":
    nativeSees(mGlobalCallee, "mg_live", "mg_dead")
    nativeSees(mPtr, "mq_live", "mq_dead")
    decided(mGlobalCallee, "mg_live", sxSat); decided(mGlobalCallee, "mg_dead", sxUnsat)
    check symexFind(mPtr, tLabel("mq_live")).status == sxUnknown
    check symexFind(mPtr, tLabel("mq_dead")).status == sxUnknown

suite "S8cn: a Table's values and keys":
  test "native":
    nativeSeesT(tvDirect, "tv_new", "tv_old")
    nativeSeesT(tvGlobal, "tg_new", "tg_old")
    nativeSeesT(tvVar, "tc_new", "tc_old")
    nativeSeesT(tvPtr, "tq_new", "tq_old")
    nativeSeesT(tmDirect, "tm_live", "tm_dead")
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

suite "S8cn: `let` over a container with a write in its life":
  test "declines":
    declined(lGlobalCallee, "lg_a"); declined(lGlobalCallee, "lg_b")
    declined(lGlobalName, "ln_a"); declined(lGlobalName, "ln_b")
    declined(lLocal, "ll_a"); declined(lLocal, "ll_b")
    declined(lVarCallee, "lv_a"); declined(lVarCallee, "lv_b")
    declined(lPtr, "lp_a"); declined(lPtr, "lp_b")
    declined(lTable, "lt_a"); declined(lTable, "lt_b")
    declined(lField, "lf_a"); declined(lField, "lf_b")
    declined(lString, "ls_a"); declined(lString, "ls_b")
    declined(lObject, "lo_a"); declined(lObject, "lo_b")
  test "no write after it, a `var`, an array: decided":
    decided(lBefore, "lb_live", sxSat); decided(lBefore, "lb_dead", sxUnsat)
    decided(lVar, "va_live", sxSat); decided(lVar, "va_dead", sxUnsat)
    check symexFind(lFormal, tLabel("lc_live")).status == sxSat
    check symexFind(lFormal, tLabel("lc_dead")).status == sxUnsat
    decided(lArr, "ar_live", sxSat); decided(lArr, "ar_dead", sxUnsat)
