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
proc sSymIx(n: int) =
  guardN()
  let i = if n > 0: 1 else: 0
  var s = @[n, n + 1]
  let r = sq(s[i], s, 0)
  if i == 0 and r == n + 1: symexTarget("si_same_live")
  if i == 1 and r == n: symexTarget("si_other_live")
  if i == 0 and r == n: symexTarget("si_same_dead")
  if i == 1 and r == n + 1: symexTarget("si_other_dead")
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
# By a global's name the walk passes a copy, and the name is withheld.
proc sqG(v: var int; i: int): int =
  v += 1
  gs[i]
proc sGloD(n: int) =
  guardN()
  gs = @[n]
  for i, x in gs.mpairs:
    if sqG(x, i) == n + 1: symexTarget("gd_live")

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

suite "S8cn item 5: a proc value":
  test "a let names its proc: decided":
    decidedT(sPV, "pv_live", sxSat)
    decidedT(sPV, "pv_dead", sxUnsat)
    decidedT(sPVChain, "pc_live", sxSat)
    decidedT(sPVChain, "pc_dead", sxUnsat)
    decidedT(sPVTable, "pt_live", sxSat)
    decidedT(sPVTable, "pt_dead", sxUnsat)
  test "a var or a parameter: the closure path, which has no Table formal":
    declined(sPVVar, "pv2_live", "seUnsupportedCompoundSortLeaf")
    declined(sPVParam, "pv3_live", "seUnsupportedCompoundSortLeaf")

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
  test "a holder of the seq":
    decidedN(sHold, "h_live", sxSat)
    decidedN(sHold, "h_dead", sxUnsat)
  test "two elements, a computed index":
    decidedN(sTwo, "two_live", sxSat)
    decidedN(sTwo, "two_dead", sxUnsat)
    decidedN(sSymIx, "si_same_live", sxSat)
    decidedN(sSymIx, "si_other_live", sxSat)
    decidedN(sSymIx, "si_same_dead", sxUnsat)
    decidedN(sSymIx, "si_other_dead", sxUnsat)
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
  test "reached by a global's name: declines":
    declined(sGloD, "gd_live", "reached by a callee both through")

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
    check parseInt(symexWalkerVersion) >= 247
