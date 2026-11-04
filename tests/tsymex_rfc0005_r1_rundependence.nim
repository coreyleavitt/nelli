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
