## RFC-0005 batch 9 -- where S8ce, S8ca, S8by and S8cc meet the batches before
## them.
##
## S8ca item 5 gives a proc value's domain a sort for a seq, table, set or
## array. Calls with such an argument used to decline for want of one, and that
## decline was all that stood in front of three aliasing shapes. Each was a
## false verdict once it was lifted, and each now declines where it is met:
##
## 1. A view and its Table in one call through a proc value: no `cViewAliases`
##    entry exists for one, so `markViewAliases` declines the call when it has a
##    `var` or `addr` actual (`closureTakesView`). A false `sxSat`.
## 2. A by-value seq or table whose variable the body also reaches (a capture, a
##    global): Nim passes the seq's memory, so the body's write is seen through
##    the formal. The actual reports its location in `ccTouch`, and
##    `touchMeetsOuter` declines the meeting (`byValueTouch`). A false `sxUnsat`.
## 3. A call returning `var T` as a `var` actual, `f(t["a"], t, "a")`: the
##    callee's write landed in a temporary. A false `sxSat`.
##
## What the lifted limit is for stays exact: a by-value call, a copy passed, a
## `var` Table with the view read after, and (S8cc's index mark through S8ca's
## closure call) an index call evaluated once beside a seq argument.
##
## The step and timeout meetings are pinned where they already were: S8by's skip
## beside batch 8's step 1d in `tsymex_rfc0005_s8bp_isolation` and
## `tsymex_rfc0005_s8by_remainder`, S8ce's fallback beside S8bx's pins in
## `tsymex_rfc0005_s8bx_extractraise`.
##
## `unsafeNew`. S8ca's report has it as a defect (a no-op, so `p` stays
## nil), true at S8ca's own head (8cef160: `p != nil` a false `sxUnsat`, `p == nil`
## a false `sxSat`), whose base has no S8bl. S8bl's decline held on this stack
## until S8cl modelled the allocation, so it is decided here.
##
## Every SUT's native run is checked here, on the input the comment names.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_b9_integration_b`, `tsymex_rfc0005_b9_integration_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 71 s).
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

from ./s8cu_helpers import nativeHits

template verdict(fn: typed; lbl: static string; want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

type Holder = object
  tab: Table[string, int]

var gObj: Holder
var gs: seq[int]
var gt: Table[string, int]
var gCalls: int

# ---- 1. A view and its Table through a proc value ----------------------------

proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]

proc rabVT(v: var int; t: var Table[string, int]; k: string): int =
  t[k] = 50
  v

proc rabH(v: var int; o: Holder; k: string): int =
  v += 1
  o.tab[k]

proc both(v: var int; t: var Table[string, int]; k: string) =
  v = 9
  t[k] = t[k] + 1

proc sVal(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = rab
  for k, v in t.mpairs:
    let r = f(v, t, k)
    if r == x + 1: symexTarget("val_live")
    if r == x: symexTarget("val_dead")

proc sVar(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = rabVT
  for k, v in t.mpairs:
    let r = f(v, t, k)
    if r == 50: symexTarget("var_live")
    if r == x and x != 50: symexTarget("var_dead")

proc sLambda(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = proc (v: var int; t2: Table[string, int]; k: string): int =
    v += 1
    t2[k]
  for k, v in t.mpairs:
    let r = f(v, t, k)
    if r == x + 1: symexTarget("lam_live")
    if r == x: symexTarget("lam_dead")

proc sHolder(t0: Table[string, int]) =
  guardT()
  var o: Holder
  o.tab = t0
  let f = rabH
  for k, v in o.tab.mpairs:
    let r = f(v, o, k)
    if r == x + 1: symexTarget("hold_live")
    if r == x: symexTarget("hold_dead")

proc sGlobalHolder(t0: Table[string, int]) =
  guardT()
  gObj.tab = t0
  let f = rabH
  for k, v in gObj.tab.mpairs:
    let r = f(v, gObj, k)
    if r == x + 1: symexTarget("ghold_live")
    if r == x: symexTarget("ghold_dead")

proc sVoid(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = both
  for k, v in t.mpairs:
    f(v, t, k)
    if t["a"] == 10: symexTarget("void_live")
    if t["a"] == 1 or t["a"] == 9: symexTarget("void_dead")

# ---- 2. A by-value location the body also reaches ----------------------------

proc gWrite(a: seq[int]): int =
  gs[0] = 50
  a[0]

proc gtWrite(a: Table[string, int]): int =
  gt["a"] = 50
  a["a"]

proc gRead(a: seq[int]): int =
  gs[0] + a[0]

proc sCapture(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  var s = s0
  let f = proc (a: seq[int]): int =
    s[0] = 50
    a[0]
  let r = f(s)
  if r == 50: symexTarget("cap_live")
  if r == x: symexTarget("cap_dead")

proc sGlobalSeq(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let f = gWrite
  let r = f(gs)
  if r == 50: symexTarget("gseq_live")
  if r == x: symexTarget("gseq_dead")

proc sGlobalTable(t0: Table[string, int]) =
  guardT()
  if x == 50: return
  gt = t0
  let f = gtWrite
  let r = f(gt)
  if r == 50: symexTarget("gtab_live")
  if r == x: symexTarget("gtab_dead")

proc sReadOnly(s0: seq[int]) =
  ## Reads only, so sharing changes nothing, but the touch does not tell a read
  ## from a write: it declines, as it did at batch 8 for want of a sort.
  ## PRECISION, no worse than batch 8.
  if s0.len != 1: return
  let x = s0[0]
  if x > 1000 or x < -1000: return
  gs = s0
  let f = gRead
  let r = f(gs)
  if r == 2 * x: symexTarget("ro_live")
  if r != 2 * x: symexTarget("ro_dead")

# ---- 3. A call returning `var T` as a `var` actual ---------------------------

proc sVarCall(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = rab
  let r = f(t["a"], t, "a")
  if r == x + 1: symexTarget("vc_live")
  if r == x: symexTarget("vc_dead")

# ---- What the lifted limit is for --------------------------------------------

proc pure(v: int; t: Table[string, int]; k: string): int =
  v + t[k]

proc tOnly(t: var Table[string, int]; k: string) =
  t[k] = 50

proc nextI(): int =
  inc gCalls
  0

proc bumpI(v: var int; s: seq[int]): int =
  v += 1
  s[0]

proc sPure(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = pure
  for k, v in t.mpairs:
    v = 7
    let r = f(v, t, k)
    if r == 14: symexTarget("pure_live")
    if r != 14: symexTarget("pure_dead")

proc sViewAfter(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = tOnly
  for k, v in t.mpairs:
    f(t, k)
    if v == 50: symexTarget("after_live")
    if v == x and x != 50: symexTarget("after_dead")

proc sCopy(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let local = s0
  let f = gWrite
  let r = f(local)
  if r == x: symexTarget("copy_live")
  if r == 50: symexTarget("copy_dead")

proc sIndexOnce(n: int) =
  if n > 1000 or n < -1000: return
  gs = @[n]
  gCalls = 0
  let f = bumpI
  let r = f(gs[nextI()], @[3])
  if gCalls == 1 and gs[0] == n + 1 and r == 3: symexTarget("once_live")
  if gCalls != 1: symexTarget("once_dead")
  if gs[0] != n + 1: symexTarget("once_dead2")

# ---- `unsafeNew` -------------------------------------------------------------

proc sUnsafeNil(k: int) =
  var p: ref int
  unsafeNew(p, 8)
  if p != nil: symexTarget("un_live")
  if p == nil: symexTarget("un_dead")

proc sUnsafeWrite(k: int) =
  var p: ref int
  unsafeNew(p, 8)
  p[] = k
  if p[] == 3: symexTarget("uw_live")
  if p[] != k: symexTarget("uw_dead")

let t5 = {"a": 5}.toTable

suite "batch 9: the native runs":

  test "input {a: 5} or 5":
    check nativeHits(sVal(t5)) == ["val_live"].toHashSet
    check nativeHits(sVar(t5)) == ["var_live"].toHashSet
    check nativeHits(sLambda(t5)) == ["lam_live"].toHashSet
    check nativeHits(sHolder(t5)) == ["hold_live"].toHashSet
    check nativeHits(sGlobalHolder(t5)) == ["ghold_live"].toHashSet
    check nativeHits(sVoid(t5)) == ["void_live"].toHashSet
    check nativeHits(sCapture(@[5])) == ["cap_live"].toHashSet
    check nativeHits(sGlobalSeq(@[5])) == ["gseq_live"].toHashSet
    check nativeHits(sGlobalTable(t5)) == ["gtab_live"].toHashSet
    check nativeHits(sReadOnly(@[5])) == ["ro_live"].toHashSet
    check nativeHits(sVarCall(t5)) == ["vc_live"].toHashSet
    check nativeHits(sPure(t5)) == ["pure_live"].toHashSet
    check nativeHits(sViewAfter(t5)) == ["after_live"].toHashSet
    check nativeHits(sCopy(@[5])) == ["copy_live"].toHashSet
    check nativeHits(sIndexOnce(5)) == ["once_live"].toHashSet
    check nativeHits(sUnsafeNil(5)) == ["un_live"].toHashSet
    check nativeHits(sUnsafeWrite(3)) == ["uw_live"].toHashSet

suite "batch 9: a view and its Table through a proc value":

  test "the Table by value and by var: decided, as the direct call (S8cn)":
    verdict(sVal, "val_live", sxSat)
    verdict(sVal, "val_dead", sxUnsat)
    verdict(sVar, "var_live", sxSat)
    verdict(sVar, "var_dead", sxUnsat)

  test "a lambda":
    verdict(sLambda, "lam_live", sxUnknown)
    verdict(sLambda, "lam_dead", sxUnknown)
