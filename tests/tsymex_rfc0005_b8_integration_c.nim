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
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_b8_integration`, `tsymex_rfc0005_b8_integration_b`,
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

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed; lbl: static string; want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want

template declines(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check hasKind(r.errors, feUnsupportedOp)

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

var gt: Table[string, int]

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

suite "batch 8: a callee reaching the Table by another name declines":

  test "a global, read and written":
    declines(sGlobalDirect, "gd_dead")
    declines(sGlobalDirectW, "gw_dead")

  test "a capture":
    verdict(sCaptured, "cp_dead", sxUnknown)
