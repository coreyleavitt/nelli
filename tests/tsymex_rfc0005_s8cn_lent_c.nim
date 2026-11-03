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
## RFC-0005 S8cm: part 3 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent`,
## `tsymex_rfc0005_s8cn_lent_b`, `tsymex_rfc0005_s8cn_lent_d`,
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
var gt: Table[string, int]
var gp: ptr seq[int]
type Obj2 = object
  a: int
  b: seq[int]
proc wg() = gs[0] = 99
proc wp() = gp[][0] = 99
proc wt() = gt["a"] = 99
proc wtv(t: var Table[string, int]) = t["a"] = 99

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
proc tpDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.pairs:
    t["a"] = 99
    if v == n: symexTarget("tp_live")
    if v == 99: symexTarget("tp_dead")
proc tmDirect(t0: Table[string, int]) =
  guardT()
  var t = t0
  for v in t.mvalues:
    t["a"] = 99
    if v == 99: symexTarget("tm_live")
    if v == n: symexTarget("tm_dead")

suite "S8cn: what Nim copies on every setting stays decided":
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
