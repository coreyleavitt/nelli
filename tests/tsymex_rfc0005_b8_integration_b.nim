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
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_b8_integration`, `tsymex_rfc0005_b8_integration_c`,
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

# A key removed under the view declines where it is removed: native reads a
# slot `del` may have refilled.
proc sRemoved(t0: Table[string, int]) =
  guardT()
  var t = t0
  for k, v in t.mpairs:
    t.del(k)
    t["b"] = 1
    if v == x: symexTarget("rem_dead")

suite "batch 8: a table write is seen through the view":

  test "by name":
    verdict(sBodyT, "body_live", sxSat)
    verdict(sBodyT, "body_dead", sxUnsat)

  test "through a var formal":
    verdict(sCallT, "callt_live", sxSat)
    verdict(sCallT, "callt_dead", sxUnsat)

  test "by a global's name":
    verdict(sCallG, "callg_live", sxSat)
    verdict(sCallG, "callg_dead", sxUnsat)

  test "through a capture":
    verdict(sCap, "cap_live", sxSat)
    verdict(sCap, "cap_dead", sxUnsat)

  test "in a handler, past the raise":
    verdict(sHandler, "hand_live", sxSat)
    verdict(sHandler, "hand_dead", sxUnsat)

  test "a removed key declines where it is removed":
    declines(sRemoved, "rem_dead")
