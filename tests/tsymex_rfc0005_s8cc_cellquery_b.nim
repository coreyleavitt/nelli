## RFC-0005 (soundness channels) slice S8cc -- S8br's remainder, item 1.
##
## 1. S8an's `addr` cell at a non-literal array index, holding an
##    input-dependent value (`var j = 1; touchP(addr gArr[j], 0)` with
##    `gArr[1] == k`): the query never finished (past 420 s at S8br's base
##    and head). Every query here runs under an explicit `queryRLimit`, and
##    must DECIDE within it: a bounded decline is not the goal. At the job's
##    base (a25229d) each dead label was `sxUnknown` here (20M units,
##    `beSolverUndef`); batch 7 decides them, S8bu's arithmetic. The RFC's
##    "As landed (S8cc)" note has the measurements.
##
## Items 2 and 3 are `tsymex_rfc0005_s8cc_remainder`.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8cc_cellquery`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 60 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

const cellBudget = SymexSettings(budget: ResourceBudget(queryRLimit: 2_000_000'u))
  ## The decision is pinned by a step budget, not a clock: every query of
  ## these walks decides within 2M Z3 units (at the job's base a dead
  ## label's query spent the 20M it was given and came back `sxUnknown`),
  ## on both pinned Z3 versions.

template verdict(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  ## `want`, with no decline (`hePtrFamily`, a hint, may accompany a `ptr`).
  block:
    let r = symexFind(fn, tLabel(lbl), cellBudget)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.kind == hePtrFamily
    r

template replays(fn: typed, lbl: string) =
  block:
    let r = verdict(fn, lbl, sxSat)
    if r.status == sxSat:
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

var gArr: array[3, int]
var gArr32: array[3, int32]
var gs: seq[int]
proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

proc touchP32(v: ptr int32; k: int32) = v[] = v[] + 5 + k

proc sutCellPick(k: int) =
  ## The index itself depends on the input: a store over a symbolic index.
  if k < 0 or k > 1000: return
  gArr = [10, k, k + 1]
  let j = if k > 500: 1 else: 2
  touchP(addr gArr[j], 0)
  if k > 500 and gArr[1] == k + 5 and gArr[2] == k + 1 and k == 600:
    symexTarget("cp")
  if (k > 500 and gArr[1] != k + 5) or (k <= 500 and gArr[2] != k + 6):
    symexTarget("cp_dead")

proc sutCellInput(k: int) =
  ## The index is the input.
  if k < 0 or k > 2: return
  gArr = [k, k + 1, k + 2]
  touchP(addr gArr[k], 0)
  if gArr[k] == 2 * k + 5 and k == 2: symexTarget("ci")
  if gArr[k] != 2 * k + 5: symexTarget("ci_dead")

proc sutCell32(k: int32) =
  ## A narrower element: its heap is not the Int-sorted `int` one's width.
  if k < 0 or k > 1000: return
  gArr32 = [10'i32, k, 30'i32]
  var j = 1
  touchP32(addr gArr32[j], 0'i32)
  if gArr32[1] == k + 5 and k == 8: symexTarget("c3")
  if gArr32[1] != k + 5: symexTarget("c3_dead")

proc sutCellSeq(k: int) =
  ## A module-level seq's element.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  var j = 1
  touchP(addr gs[j], 0)
  if gs[1] == k + 5 and k == 12: symexTarget("cs")
  if gs[1] != k + 5: symexTarget("cs_dead")

proc sutCellLocal(k: int) =
  ## A local array's element.
  if k < 0 or k > 1000: return
  var a = [10, k, 30]
  var j = 1
  touchP(addr a[j], 0)
  if a[1] == k + 5 and a[0] == 10 and k == 13: symexTarget("co")
  if a[1] != k + 5 or a[0] != 10: symexTarget("co_dead")

suite "S8cc: an address cell at a non-literal index decides":
  test "the index, the element's width and the storage vary":
    replays(sutCellPick, "cp")
    discard verdict(sutCellPick, "cp_dead", sxUnsat)
    replays(sutCellInput, "ci")
    discard verdict(sutCellInput, "ci_dead", sxUnsat)
    replays(sutCell32, "c3")
    discard verdict(sutCell32, "c3_dead", sxUnsat)
    replays(sutCellSeq, "cs")
    discard verdict(sutCellSeq, "cs_dead", sxUnsat)
    replays(sutCellLocal, "co")
    discard verdict(sutCellLocal, "co_dead", sxUnsat)

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 238
