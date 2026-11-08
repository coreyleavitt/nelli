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
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_b9_integration`, `tsymex_rfc0005_b9_integration_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 71 s).
import std/[unittest, strutils, tables, sets]
import nelli
import nelli/symex
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "b9_integration_b")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

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

proc rabH(v: var int; o: Holder; k: string): int =
  v += 1
  o.tab[k]

proc both(v: var int; t: var Table[string, int]; k: string) =
  v = 9
  t[k] = t[k] + 1

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

suite "batch 9: a view and its Table through a proc value":


  test "the Table in a field, of a local and of a global: decided (S8cn)":
    verdict(sHolder, "hold_live", sxSat)
    verdict(sHolder, "hold_dead", sxUnsat)
    verdict(sGlobalHolder, "ghold_live", sxSat)
    verdict(sGlobalHolder, "ghold_dead", sxUnsat)

  test "a void call: decided (S8cn)":
    verdict(sVoid, "void_live", sxSat)
    verdict(sVoid, "void_dead", sxUnsat)

suite "batch 9: a by-value location the body also reaches declines":

  test "a capture":
    pinDecline(sCapture, declKey, ceCaptureByRefUnmodelled, tLabel("cap_live"))
    pinDecline(sCapture, declKey, ceCaptureByRefUnmodelled, tLabel("cap_dead"))

  test "a global seq and a global Table":
    pinDecline(sGlobalSeq, declKey, feUnsupportedOp, tLabel("gseq_live"))
    pinDecline(sGlobalSeq, declKey, feUnsupportedOp, tLabel("gseq_dead"))
    pinDecline(sGlobalTable, declKey, feUnsupportedOp, tLabel("gtab_live"))
    pinDecline(sGlobalTable, declKey, feUnsupportedOp, tLabel("gtab_dead"))
