## RFC-0016 W3-z R9 -- the whole-run gate's tail walk has its own budget.
##
## After a label `sxSat` the tail walk replays the winner under the witness's
## model pins (`verifyTailDefined`). A branch the pins cannot decide (a global
## havoc, an opaque call's result) is asked in scratch checks, each capped at
## `concreteBranchRLimit` units, and since W3-z R6 it is forked both ways. In a
## nested loop the forks multiplied the capped checks until only `walkRLimit`
## (about 50 capped checks, over 20 minutes) stopped them. Now the tail walk
## stops once it has spent `tailWalkCappedChecks` capped checks' worth of
## units, and fails closed: the `sxSat` stands, untrusted, `ubTailUnverified`.
## A check that spent its cap undecided is not asked again for the same branch.
##
## The pins run under a small `queryRLimit` (500k units per scratch check), so
## a capped check is cheap and the cost shows in units, not in minutes.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import ./s8cu_helpers

var gA: uint64
  ## A module global the SUTs never write: the tail walk reads it as a free
  ## constant (its entry value), which the witness's pins do not fix.

proc setGA(v: uint64) =
  ## Natively reachable state: an earlier call of the program sets it.
  gA = v

const r9CheckRLimit = 500_000'u

const r9Settings = block:
  var s = pinSettingsConst
  s.budget.queryRLimit = r9CheckRLimit
  s

const r9Unbounded = block:
  var s = r9Settings
  s.budget.tailWalkCappedChecks = 0
  s

const r9Budget = 5 * int(r9CheckRLimit)
  ## The tail budget under `r9Settings`: `tailWalkCappedChecks` (default 5)
  ## times the scratch check's rlimit (`queryRLimit` when set).

proc sutNestedCapped(x: int64): int64 =
  ## The label, then a nested loop whose branch reads `gA` cubed: open under
  ## the pins, and each scratch check of it spends its whole cap undecided
  ## (a 64-bit cube root). Both arms are defined.
  if x == 5: symexTarget("hit")
  var i = 0
  while i < 2:
    var j = 0
    while j < 2:
      if gA * gA * gA == 0x123456789ABCDEF'u64 + uint64(i * 2 + j):
        result += 1
      inc j
    inc i
  result += x

proc sutNestedCheap(x: int64): int64 =
  ## The same nested loop, with a branch on `gA` the scratch checks decide
  ## open at once (both ways satisfiable): forked both ways, defined on both.
  if x == 5: symexTarget("hit")
  var i = 0
  while i < 2:
    var j = 0
    while j < 2:
      if gA > uint64(i * 2 + j):
        result += 1
      inc j
    inc i
  result += x

proc tailUnits(log: string): int =
  result = -1
  for line in readFile(log).splitLines:
    let f = line.split('\t')
    if f.len >= 2 and f[1] == "k10b-tail": result = parseInt(f[0])

template withUnitsLog(name: string; body: untyped): int =
  let log = getTempDir() / ("r9_" & name & "_units.log")
  removeFile(log)
  putEnv("NELLI_WALK_UNITS_LOG", log)
  try:
    body
  finally:
    delEnv("NELLI_WALK_UNITS_LOG")
  let t = tailUnits(log)
  removeFile(log)
  t

suite "W3-z R9: the tail walk's own budget":
  test "version floor (the tail walk has its own budget at 343)":
    check parseInt(symexWalkerVersion) >= 343

  test "the default budget: five capped checks, a tenth of walkRLimit":
    let b = ResourceBudget()
    check b.tailWalkCappedChecks == 5
    check uint(b.tailWalkCappedChecks) * defaultConcreteBranchRLimit ==
          b.walkRLimit div 10

  test "(a) capped open branches in a nested loop: the tail stops at its budget, untrusted":
    var r: typeof(symexFind(sutNestedCapped, tLabel("hit"), r9Settings))
    let tail = withUnitsLog("a"):
      r = symexFind(sutNestedCapped, tLabel("hit"), r9Settings)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    checkpoint "tail units: " & $tail & " (budget " & $r9Budget & ")"
    check r.status == sxSat
    check r.witness[0] == 5
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubTailUnverified)}
    # Each check runs under what is left, so the walk overshoots the budget by
    # the walker's own term charges at most.
    check tail >= r9Budget
    check tail < r9Budget + r9Budget div 10

  test "(b) an open branch the checks decide, in the same loop: trusted within budget":
    var r: typeof(symexFind(sutNestedCheap, tLabel("hit"), r9Settings))
    let tail = withUnitsLog("b"):
      r = symexFind(sutNestedCheap, tLabel("hit"), r9Settings)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    checkpoint "tail units: " & $tail
    check r.status == sxSat
    check r.witness[0] == 5
    check r.trusted
    check r.soundness.undefinedKinds == {}
    check tail >= 0 and tail < r9Budget
    # Native agreement: defined whatever an earlier call left in `gA`.
    for g in [0'u64, 2'u64, 9'u64]:
      setGA(g)
      let v = sutNestedCheap(r.witness[0])
      check v >= 5 and v <= 9
    setGA(0)

  test "(c) the budget opted out: only walkRLimit bounds the tail, which spends past it":
    # The knob is the walk's: at `0` the same capped tail runs to its end and
    # both arms are defined, so the verdict is trusted, at a cost above the
    # budget (a capped check asked once per open branch, R9's shortcut).
    var r: typeof(symexFind(sutNestedCapped, tLabel("hit"), r9Unbounded))
    let tail = withUnitsLog("c"):
      r = symexFind(sutNestedCapped, tLabel("hit"), r9Unbounded)
    checkpoint show(r.errors)
    checkpoint "tail units: " & $tail
    check r.status == sxSat
    check r.trusted
    check tail > r9Budget
