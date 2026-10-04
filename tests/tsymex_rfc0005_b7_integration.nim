## RFC-0005 batch 7 -- where S8bp, S8bu and S8br meet batch 6.
##
## 1. A `var openArray` view (S8bu) is copied into a temporary where the
##    argument stands; Nim passes the storage's address, so a later
##    argument's call that writes the storage is seen by the callee, and
##    the walk's write-back overwrote that write with the stale copy (a
##    false `sxUnsat` at S8bu's tip, 5729b1a). Batch 7 declines it on S8br's
##    frame condition (`laterLeavesLvalue`).
## 2. A module-level seq indexed by a call in a `var` actual (S8br's hoist
##    beside batch 6's entry values and S8bl's constant-guard fold): at
##    S8bu's tip `gw` was a false `sxUnsat` (the copy-out called the index
##    function again); S8br's hoist fixes it on the stack.
## 3. S8br's slow query (an `addr` cell at a non-literal index with an
##    input-dependent value) terminates under S8bu's default bounds, and
##    never as a false `sxSat`. Fixing its cost is S8cc.
import std/[unittest, strutils, times]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.kind == hePtrFamily
    r

template replays(fn: typed, lbl: string) =
  block:
    let r = verdict(fn, lbl, sxSat)
    if r.status == sxSat:
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template declines(fn: typed, lbl, why: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feEvalOrderUnmodelled)
    check why in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

var gArr: array[3, int]
var gW: seq[int]
var gCalls: int

proc nextI(): int =
  inc gCalls
  1

proc touch(v: var int; k: int) = v = v + 5 + k
proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k
proc fill(x: var openArray[int]; k: int) = x[0] = x[0] + k

proc bumpA(): int =
  ## The later argument: writes the viewed storage.
  gArr[0] = 100
  1

proc bumpC(): int =
  ## A later argument that writes something else.
  inc gCalls
  1

# ---- 1. a `var openArray` view a later argument writes ----------------------

proc sutOa(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  fill(gArr, bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("oa")
  if gArr[0] != 101: symexTarget("oa_dead")

proc sutOaSlice(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  fill(toOpenArray(gArr, 0, 1), bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("os")
  if gArr[0] != 101: symexTarget("os_dead")

proc sutOaClosure(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  let f = fill
  f(gArr, bumpA())
  if gArr[0] != 101: symexTarget("oc_dead")

proc sutOaOther(k: int) =
  ## The later argument leaves the storage alone: still modelled.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gCalls = 0
  fill(gArr, bumpC())
  if gArr[0] == k + 1 and gCalls == 1 and k == 4: symexTarget("ot")
  if gArr[0] != k + 1 or gCalls != 1: symexTarget("ot_dead")

# ---- 2. a module-level seq indexed by a call --------------------------------

proc sutGlobalIdxCall(k: int) =
  if k < 0 or k > 1000: return
  gW = @[10, 20, 30]
  gCalls = 0
  touch(gW[nextI()], k)
  if gW[1] == 25 + k and gCalls == 1 and k == 3: symexTarget("gw")
  if gW[1] != 25 + k or gCalls != 1: symexTarget("gw_dead")

proc sutGuardFold(k: int) =
  ## S8bl folds a guard on a value the walk knows; here the guard reads
  ## the count the hoisted index call left.
  if k < 0 or k > 1000: return
  gW = @[10, 20, 30]
  gCalls = 0
  touch(gW[nextI()], 0)
  if gCalls == 1:
    if k == 7: symexTarget("gf")
  else:
    symexTarget("gf_dead")

proc sutGlobalEntry(k: int) =
  ## `gW` read at its entry value (batch 6's `globalEntryVals`): any length.
  if k < 0 or k > 1000: return
  gCalls = 0
  touch(gW[nextI()], k)
  if gCalls != 1: symexTarget("ge_dead")

# ---- 3. S8br's slow `addr` cell ----------------------------------------------

proc sutAddrCell(k: int) =
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  var j = 1
  touchP(addr gArr[j], 0)
  if gArr[1] != k + 5: symexTarget("ac_dead")

suite "RFC-0005 batch 7: integration":

  test "nim":
    gArr = [4, 20, 30]
    fill(gArr, bumpA())
    check gArr == [101, 20, 30]
    gArr = [4, 20, 30]
    fill(toOpenArray(gArr, 0, 1), bumpA())
    check gArr == [101, 20, 30]
    block:
      let f = fill
      gArr = [4, 20, 30]
      f(gArr, bumpA())
      check gArr == [101, 20, 30]
    gArr = [4, 20, 30]
    gCalls = 0
    fill(gArr, bumpC())
    check gArr == [5, 20, 30] and gCalls == 1
    gW = @[10, 20, 30]
    gCalls = 0
    touch(gW[nextI()], 3)
    check gW == @[10, 28, 30] and gCalls == 1
    for k in [0, 7, 1000]:
      gArr = [10, k, 30]
      var j = 1
      touchP(addr gArr[j], 0)
      check gArr[1] == k + 5

  test "a var openArray view a later argument writes declines":
    ## RED at S8bu's tip: `oa`, `os` a false `sxUnsat`, `oa_dead`,
    ## `os_dead` a refuted `sxSat`.
    declines(sutOa, "oa", "copied where it stands")
    declines(sutOa, "oa_dead", "copied where it stands")
    declines(sutOaSlice, "os", "copied where it stands")
    declines(sutOaSlice, "os_dead", "copied where it stands")
    declines(sutOaClosure, "oc_dead", "copied where it stands")

  test "a var openArray view a later argument leaves alone is modelled":
    replays(sutOaOther, "ot")
    discard verdict(sutOaOther, "ot_dead", sxUnsat)

  test "a module-level seq indexed by a call":
    ## RED at S8bu's tip: `gw`, `gf` a false `sxUnsat`, `gw_dead`,
    ## `gf_dead` a refuted `sxSat`.
    replays(sutGlobalIdxCall, "gw")
    discard verdict(sutGlobalIdxCall, "gw_dead", sxUnsat)
    replays(sutGuardFold, "gf")
    discard verdict(sutGuardFold, "gf_dead", sxUnsat)
    let r = symexFind(sutGlobalEntry, tLabel("ge_dead"))
    checkpoint "ge_dead " & $r.status & " " & show(r.errors)
    check r.status notin {sxSat, sxUnsat}
    check r.errors.hasKind(feGlobalHavoc)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "S8br's addr cell at a non-literal index terminates":
    ## Natively `ac_dead` is unreachable. The query may come back exact
    ## (`sxUnsat`, as it does at batch 7) or as a bounded decline; never
    ## `sxSat`, and within the budget S8bu's defaults allow.
    let t0 = epochTime()
    let r = symexFind(sutAddrCell, tLabel("ac_dead"))
    let el = epochTime() - t0
    checkpoint "ac_dead " & $r.status & " " & $el & "s " & show(r.errors)
    check r.status in {sxUnsat, sxUnknown}
    check not r.errors.hasKind(weInternalWalkerFault)
    check el < 300.0

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 237
