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
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_b8_integration`, `tsymex_rfc0005_b8_integration_b`,
## `tsymex_rfc0005_b8_integration_c`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 73 s).
import std/[unittest, strutils, tables]
import nelli
import nelli/symex
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "b8_integration_d")

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

var gt: Table[string, int]
var gs: seq[int]

proc readAfterBump(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]

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

suite "batch 8: module-level containers":

  test "a global Table":
    verdict(sGlobalPass, "gp_live", sxSat)
    verdict(sGlobalPass, "gp_dead", sxUnsat)
    verdict(sGlobalBody, "gb_live", sxSat)
    verdict(sGlobalBody, "gb_dead", sxUnsat)

  test "an element passed on to a var formal":
    verdict(sSeqBump, "sb_live", sxSat)
    verdict(sSeqBump, "sb_dead", sxUnsat)
    verdict(sGlobalSeqBump, "gsb_live", sxSat)
    verdict(sGlobalSeqBump, "gsb_dead", sxUnsat)

  test "a global seq with the element and its seq: decided (RFC-0005 S8cn)":
    verdict(sSeqPass, "sp_dead", sxUnsat)
  test "a global seq by its name with the element: declines":
    pinDecline(sSeqDirect, declKey, feUnsupportedOp, tLabel("sd_dead"))
    pinDecline(sSeqDirectW, declKey, feUnsupportedOp, tLabel("sw_dead"))

suite "batch 8: walker version":

  test "walker version floor >= 241 (batch 8)":
    check parseInt(symexWalkerVersion) >= 241
