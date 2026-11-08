## RFC-0005 batch 8 -- where S8bx and S8bt meet the batches before them.
##
## `for k, v in t.mpairs` yields `var V`: `v` IS the slot of `t` at `k`.
##
## 1. S8bx's sync of a view and its Table in a callee ran between the
##    statements of a block, so a callee of one statement (`t[k] = 50`) was
##    never synced: a false `sxSat`. It is now S8bs's address cell sync, which
##    runs after every statement (`AddrCellEntry.slot`, `syncAddrCells`).
## 2. S8bl stored a write through the view into the table, and nothing carried
##    a write through the table to the view: `t[k] = 50; if v == 50` read the
##    value from the head of the iteration, by name, through a `var` formal,
##    through a capture and through a global's name. A false `sxSat` on the
##    negation. Each such statement now reloads the view (`mutViewWriteBack`).
## 3. A callee holding the view that reaches the Table by a global's name or a
##    capture has two copies of one location. The name is withheld (S8an's
##    `cGuardRoots`), and its access declines. It was a false `sxUnsat`.
## 4. A module-level Table through `mpairs`, and a module-level seq through
##    `mitems` / `mpairs` (S8bu spells the element `c[k]`, which an element
##    passed on to a `var` formal aborted the compile on).
##
## A raise inside an own-context solve (S8bp, S8bu) is pinned beside the
## extraction raise it shares a hook with, `tsymex_rfc0005_s8bx_extractraise`.
##
## Every SUT's native run is checked here, on the input the comment names.
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_b8_integration_b`, `tsymex_rfc0005_b8_integration_c`,
## `tsymex_rfc0005_b8_integration_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 73 s).
import std/[unittest, strutils, tables]
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

var gt: Table[string, int]
var gs: seq[int]

# ---- 1. A callee of one statement ------------------------------------------

proc only(v: var int; t: var Table[string, int]; k: string) =
  t[k] = 50

proc sOnly(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    only(v, t, k)
    if t["a"] == 50: symexTarget("only_live")
    if t["a"] == x and x != 50: symexTarget("only_dead")

proc onlyV(v: var int; t: var Table[string, int]; k: string) =
  v = 50

proc sOnlyV(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    onlyV(v, t, k)
    if t["a"] == 50: symexTarget("onlyv_live")
    if t["a"] == x and x != 50: symexTarget("onlyv_dead")

proc readAfterBump(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]

proc raiser(v: var int; t: var Table[string, int]; k: string) =
  v = 9
  if t[k] == 9: raise newException(ValueError, "x")
  t[k] = 10

proc sRaise(t0: Table[string, int]) =
  guardT()
  var t = t0
  try:
    for k, v in t.mpairs:
      raiser(v, t, k)
    if t["a"] == 10: symexTarget("ra_dead")
  except ValueError:
    if t["a"] == 9: symexTarget("ra_live")
    else: symexTarget("ra_dead2")

# Through a proc value: RFC-0005 S8cn, the direct call.
proc sProcVal(t0: Table[string, int]) =
  guardT()
  var t = t0
  let f = readAfterBump
  for k, v in t.mpairs:
    let r = f(v, t, k)
    if r == x: symexTarget("pv_dead")

# ---- 2. A write through the table is seen through the view ------------------

proc sBodyT(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    t[k] = 50
    if v == 50: symexTarget("body_live")
    if v == x and x != 50: symexTarget("body_dead")

proc setT(t: var Table[string, int]; k: string) =
  t[k] = 50

proc sCallT(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    setT(t, k)
    if v == 50: symexTarget("callt_live")
    if v == x and x != 50: symexTarget("callt_dead")

proc setG(k: string) =
  gt[k] = 50

proc sCallG(t0: Table[string, int]) =
  guardT()
  gt = t0
  for k, v in gt.mpairs:
    setG(k)
    if v == 50: symexTarget("callg_live")
    if v == x and x != 50: symexTarget("callg_dead")

proc sCap(t0: Table[string, int]) =
  guardT()
  var t = t0
  proc setC(k: string) =
    t[k] = 50
  for k, v in t.mpairs:
    setC(k)
    if v == 50: symexTarget("cap_live")
    if v == x and x != 50: symexTarget("cap_dead")

proc setThenRaise(t: var Table[string, int]; k: string) =
  t[k] = 50
  raise newException(ValueError, "x")

# A handler reads the view past a raise out of the table write.
proc sHandler(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    try:
      setThenRaise(t, k)
    except ValueError:
      if v == 50: symexTarget("hand_live")
      if v == x and x != 50: symexTarget("hand_dead")

# ---- 3. A callee reaching the Table by another name -------------------------

proc readG(v: var int; k: string): int =
  v += 1
  gt[k]

proc sGlobalDirect(t0: Table[string, int]) =
  guardT()
  gt = t0
  for k, v in gt.mpairs:
    let r = readG(v, k)
    if r == x: symexTarget("gd_dead")

proc writeG(v: var int; k: string): int =
  gt[k] = 50
  v

proc sGlobalDirectW(t0: Table[string, int]) =
  guardT()
  gt = t0
  for k, v in gt.mpairs:
    let r = writeG(v, k)
    if r == x and x != 50: symexTarget("gw_dead")

proc sCaptured(t0: Table[string, int]) =
  guardT()
  var t = t0
  proc inner(v: var int): int =
    v += 1
    t["a"]
  for k, v in t.mpairs:
    let r = inner(v)
    if r == x: symexTarget("cp_dead")

# ---- 4. Module-level containers --------------------------------------------

proc sGlobalPass(t0: Table[string, int]) =
  guardT()
  gt = t0
  for k, v in gt.mpairs:
    let r = readAfterBump(v, gt, k)
    if r == x + 1: symexTarget("gp_live")
    if r == x: symexTarget("gp_dead")

proc sGlobalBody(t0: Table[string, int]) =
  guardT()
  gt = t0
  for k, v in gt.mpairs:
    v = 9
    if gt["a"] == 9: symexTarget("gb_live")
    if gt["a"] == x and x != 9: symexTarget("gb_dead")

proc bump(v: var int) =
  v += 1

proc seqRead(v: var int; s: seq[int]; i: int): int =
  v += 1
  s[i]

proc seqReadG(v: var int; i: int): int =
  v += 1
  gs[i]

proc seqWriteG(v: var int; i: int): int =
  gs[i] = 50
  v

# An element passed on to a `var` formal: the compile aborted on it.
proc sSeqBump(n: int) =
  if n > 1000 or n < -1000: return
  var s = @[n]
  for x in mitems(s):
    bump(x)
  if s[0] == n + 1: symexTarget("sb_live")
  if s[0] == n: symexTarget("sb_dead")

proc sGlobalSeqBump(n: int) =
  if n > 1000 or n < -1000: return
  gs = @[n]
  for x in mitems(gs):
    bump(x)
  if gs[0] == n + 1: symexTarget("gsb_live")
  if gs[0] == n: symexTarget("gsb_dead")

proc sSeqPass(n: int) =
  if n > 1000 or n < -1000: return
  gs = @[n]
  for i, x in gs.mpairs:
    let r = seqRead(x, gs, i)
    if r == n: symexTarget("sp_dead")

proc sSeqDirect(n: int) =
  if n > 1000 or n < -1000: return
  gs = @[n]
  for i, x in gs.mpairs:
    let r = seqReadG(x, i)
    if r == n: symexTarget("sd_dead")

proc sSeqDirectW(n: int) =
  if n > 1000 or n < -1000: return
  gs = @[n]
  for i, x in gs.mpairs:
    let r = seqWriteG(x, i)
    if r == n and n != 50: symexTarget("sw_dead")

let t5 = {"a": 5}.toTable

suite "batch 8: the native runs":

  test "input {a: 5} or 5":
    check "only_live" in nativeHits(sOnly(t5))
    check "only_dead" notin nativeHits(sOnly(t5))
    check "onlyv_live" in nativeHits(sOnlyV(t5))
    check "onlyv_dead" notin nativeHits(sOnlyV(t5))
    check "ra_live" in nativeHits(sRaise(t5))
    check "ra_dead" notin nativeHits(sRaise(t5))
    check "pv_dead" notin nativeHits(sProcVal(t5))
    check "body_live" in nativeHits(sBodyT(t5))
    check "body_dead" notin nativeHits(sBodyT(t5))
    check "callt_live" in nativeHits(sCallT(t5))
    check "callt_dead" notin nativeHits(sCallT(t5))
    check "callg_live" in nativeHits(sCallG(t5))
    check "callg_dead" notin nativeHits(sCallG(t5))
    check "cap_live" in nativeHits(sCap(t5))
    check "cap_dead" notin nativeHits(sCap(t5))
    check "hand_live" in nativeHits(sHandler(t5))
    check "hand_dead" notin nativeHits(sHandler(t5))
    check "gd_dead" notin nativeHits(sGlobalDirect(t5))
    check "gw_dead" notin nativeHits(sGlobalDirectW(t5))
    check "cp_dead" notin nativeHits(sCaptured(t5))
    check "gp_live" in nativeHits(sGlobalPass(t5))
    check "gp_dead" notin nativeHits(sGlobalPass(t5))
    check "gb_live" in nativeHits(sGlobalBody(t5))
    check "gb_dead" notin nativeHits(sGlobalBody(t5))
    check "sb_live" in nativeHits(sSeqBump(5))
    check "sb_dead" notin nativeHits(sSeqBump(5))
    check "gsb_live" in nativeHits(sGlobalSeqBump(5))
    check "gsb_dead" notin nativeHits(sGlobalSeqBump(5))
    check "sp_dead" notin nativeHits(sSeqPass(5))
    check "sd_dead" notin nativeHits(sSeqDirect(5))
    check "sw_dead" notin nativeHits(sSeqDirectW(5))

suite "batch 8: a view and its Table in one callee":

  test "a callee of one statement":
    verdict(sOnly, "only_live", sxSat)
    verdict(sOnly, "only_dead", sxUnsat)
    verdict(sOnlyV, "onlyv_live", sxSat)
    verdict(sOnlyV, "onlyv_dead", sxUnsat)

  test "a raise out of the callee":
    verdict(sRaise, "ra_live", sxSat)
    verdict(sRaise, "ra_dead", sxUnsat)
    verdict(sRaise, "ra_dead2", sxUnsat)

  test "through a proc value: decided (RFC-0005 S8cn)":
    verdict(sProcVal, "pv_dead", sxUnsat)
