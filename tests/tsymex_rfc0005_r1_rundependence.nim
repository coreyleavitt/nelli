## RFC-0005 review, round 1, R1-07 -- run-dependence read at save time.
##
## A verdict some solve of whose run the clock cut off (S8bu), one a call
## declined for want of native stack (S8ca), and one a replay left undecided
## for a reason of the run (WA-7) are the machine's or the moment's, so an
## `sxUnknown` among them is not cached. The save decided that by reading three
## thread-local flags (`symexQueryTimedOut`, `symexNativeStackCut`,
## `replayRunDependent`), which hold whatever the LAST run on the thread set.
## The public `saveSymexVerdict` is handed a status and a `Soundness`, not a
## run, so a save after other work read another run's flags:
##
##   (1) a run-dependent run, then a save of an unrelated verdict: dropped;
##   (2) a run-dependent run, then a clean run, then the first run's verdict
##       saved: stored, and served as if any run would reach it.
##
## The run-dependence now rides the result (`Soundness.runDependence`), set
## where the run ends and where its replays settle, and the save reads the
## soundness it is handed.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/replayproc
import nelli/smt/replayresult
import nelli/smt/soundness

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc r1Forever(n: uint): uint =
  ## As `tsymex_rfc0005_s8ca_stack`'s: only the call, on a new argument, so a
  ## walk with a deep budget inlines it until the stack (or Nim's call depth)
  ## declines. Never run natively.
  result = r1Forever(n + 1)

proc r1ForeverSut(n: uint) =
  if r1Forever(n) > 1_000_000'u:
    symexTarget("r1_forever_never")

proc r1Helper(x: int): int = x + 1

proc r1Shallow(x: int) =
  if r1Helper(x) == 8:
    symexTarget("r1_shallow")

proc r1Unrelated(x: int) =
  if x == 3:
    symexTarget("r1_unrelated")

const deep = SymexSettings(budget: ResourceBudget(maxCallDepth: 100_000,
                                                  maxRecursionDepth: 100_000))

suite "R1-07: a save reads the run-dependence of the verdict it is handed":

  test "a run-dependent run does not drop a later save of another verdict":
    let cut = symexFind(r1ForeverSut, tLabel("r1_forever_never"), deep)
    checkpoint show(cut.errors)
    check cut.status == sxUnknown
    # Nothing about this verdict depends on the run before it.
    let db = inMemoryDatabase()
    saveSymexVerdict(db, r1Unrelated, tLabel("r1_unrelated"),
                     defaultSymexSettings(), sfUnknown,
                     Soundness(runTaint: {scIncomplete}))
    let got = loadSymexVerdict(db, r1Unrelated, tLabel("r1_unrelated"),
                               defaultSymexSettings())
    check got.isSome

  test "a run-dependent verdict saved after a clean run is not stored":
    let cut = symexFind(r1ForeverSut, tLabel("r1_forever_never"), deep)
    checkpoint show(cut.errors)
    check cut.status == sxUnknown
    let clean = symexFind(r1Shallow, tLabel("r1_shallow"))
    check clean.status == sxSat
    let db = inMemoryDatabase()
    saveSymexVerdict(db, r1ForeverSut, tLabel("r1_forever_never"), deep,
                     sfUnknown, cut.soundness)
    check loadSymexVerdict(db, r1ForeverSut, tLabel("r1_forever_never"),
                           deep).isNone

suite "R1-07: the run-dependence rides the result, and the cache":

  test "a run the stack cut carries it; a clean run does not":
    let cut = symexFind(r1ForeverSut, tLabel("r1_forever_never"), deep)
    check rdNativeStack in cut.soundness.runDependence
    let clean = symexFind(r1Shallow, tLabel("r1_shallow"))
    check clean.soundness.runDependence == {}
    # The first result still says what its own run was.
    check rdNativeStack in cut.soundness.runDependence

  test "a stored witness serves back the run-dependence it was saved with":
    let db = inMemoryDatabase()
    let s = Soundness(replay: rsConfirmed,
                      runDependence: {rdQueryTimeout, rdReplay})
    saveSymexWitness(db, r1Unrelated, tLabel("r1_unrelated"),
                     defaultSymexSettings(),
                     SymexFinding(status: sfSat, soundness: s))
    let got = loadSymexWitnesses(db, r1Unrelated, tLabel("r1_unrelated"),
                                 defaultSymexSettings())
    check got.len == 1
    check got.len == 1 and got[0].soundness == s

  test "an rsUnconfirmed witness is stored unless its own replay was the run's":
    let db = inMemoryDatabase()
    saveSymexWitness(db, r1Unrelated, tLabel("r1_unrelated"),
                     defaultSymexSettings(),
                     SymexFinding(status: sfSat, soundness: Soundness(
                       replay: rsUnconfirmed, runDependence: {rdReplay})))
    check loadSymexWitnesses(db, r1Unrelated, tLabel("r1_unrelated"),
                             defaultSymexSettings()).len == 0
    saveSymexWitness(db, r1Unrelated, tLabel("r1_unrelated"),
                     defaultSymexSettings(),
                     SymexFinding(status: sfSat, soundness: Soundness(
                       replay: rsUnconfirmed, runDependence: {rdQueryTimeout})))
    check loadSymexWitnesses(db, r1Unrelated, tLabel("r1_unrelated"),
                             defaultSymexSettings()).len == 1

suite "R1-06: a replay's result is a value":

  test "each replay keeps its own ending, whatever runs after it":
    let hit = replayWitness(r1Unrelated, (3,), tLabel("r1_unrelated"), {})
    let miss = replayWitness(r1Unrelated, (4,), tLabel("r1_unrelated"), {})
    check hit.outcome == roConfirmed
    check miss.outcome == roRefuted
    check hit.detail == "it ran to its end"
    check rdReplay notin hit.runDependence

# ---- Review round 3 -----------------------------------------------------------
#
# * E1. `ReplayResult`'s zero value was `roConfirmed` over a child that
#   finished: a confirmed, host-safe replay that nothing ran. Its zero, and its
#   child's, is now the replay that did not run.
# * SC1. Whether a replay is run-dependent rested on a flag each producer had to
#   set; a lost status or a kill is the host's, whatever the flag says. And a
#   confirmed claim whose child was killed or lost (`witnessUnsafe` for a reason
#   of the run) was cached for good, so one slow host marked the witness
#   unrunnable forever.

suite "R3 E1: a replay result nothing produced is not a confirmation":
  test "the zero ReplayChild is a child that did not run":
    var c: ReplayChild
    check c.ending == reRefused
    check not c.reached

  test "the zero ReplayResult is the decline its child means":
    var r: ReplayResult
    check r.outcome != roConfirmed
    check r.replayStatus != rsConfirmed
    check r.child.ending != reFinished
    check r.outcome == replayResultOf(r.child, lossy = false).outcome
    check ReplayResult().outcome == r.outcome

suite "R3 SC1: an ending of the host's is run-dependent":
  test "a child whose status was lost":
    let r = replayResultOf(ReplayChild(ending: reLost, reached: true,
                                         runDependent: true), false)
    check r.outcome == roConfirmed
    check rdReplay in r.runDependence
  test "a child killed at its bound":
    let r = replayResultOf(ReplayChild(ending: reTimedOut,
                                         runDependent: true), false)
    check rdReplay in r.runDependence
  test "control: a child that exited is the program's":
    let r = replayResultOf(ReplayChild(ending: reExited, code: 3), false)
    check rdReplay notin r.runDependence

suite "R3 SC1: an unsafe witness of the run's is not cached for good":
  test "a confirmed claim whose child was killed or lost":
    check not Soundness(replay: rsConfirmed, witnessUnsafe: true,
                        runDependence: {rdReplay}).cacheable
  test "an unconfirmed one":
    check not Soundness(replay: rsUnconfirmed, witnessUnsafe: true,
                        runDependence: {rdReplay}).cacheable
  test "control: an unsafe witness of the program's is cached":
    check Soundness(replay: rsConfirmed, witnessUnsafe: true).cacheable
    check Soundness(replay: rsConfirmed, witnessUnsafe: true,
                    runDependence: {rdQueryTimeout}).cacheable
  test "control: a safe confirmed claim is cached":
    check Soundness(replay: rsConfirmed, runDependence: {rdReplay}).cacheable
  test "the save drops it":
    let db = inMemoryDatabase()
    saveSymexWitness(db, r1Unrelated, tLabel("r1_unrelated"),
                     defaultSymexSettings(),
                     SymexFinding(status: sfSat, soundness: Soundness(
                       replay: rsConfirmed, witnessUnsafe: true,
                       runDependence: {rdReplay})))
    check loadSymexWitnesses(db, r1Unrelated, tLabel("r1_unrelated"),
                             defaultSymexSettings()).len == 0
