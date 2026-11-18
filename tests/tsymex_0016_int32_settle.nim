## RFC-0016 INT-32 (0005 review R1-33, R1-34, R4-07, R4-10). Replay and
## settle policy, each item through the entry point that serves it:
##
## * `storedGaps`: a record whose gaps metadata is present but malformed is a
##   miss for the whole record. It served the gaps up to the break as if they
##   were all the cold run had.
## * `reSignalled`: a replay child ended by a signal from outside the SUT
##   (`SIGTERM`, `SIGKILL`, ...) is run-dependent, so its verdict is not
##   stored. A fault the SUT raises on itself (`SIGSEGV`, `SIGABRT`, ...) is
##   the program's and still is.
## * `saveSymexRaisedImpl`: of two findings of one raised type it stores the
##   strongest (`claimRank`: trusted first, then host-runnable), with that
##   finding's own gaps and witness. It stored the first.
## * `winnerLossy`: a clean winner is lossy by its own extraction only, never
##   by a sibling hit's (`RawResult.witnessExtraction`).
## * `witnessUnsafe` is rendered by every report format (pin).
## * A witness whose replay always runs past `replayTimeoutMs` leaves a
##   verdict that is stored: the bound is in the key, so a hit does not pay
##   the bound again until the key changes.
## * A lossy winner whose replay no child could run is `rsRefused`: not
##   trusted, and never run in the host, cold or from the cache. It was
##   `rsUnconfirmed`, which a consumer runs.
import std/[unittest, options, strutils, tables, os]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime, canonicalize, soundness, replayproc,
                  replayresult, replay_settle]
import nelli/engine/types
from nelli/smt/admission import cellKey, axConstruct
from ./s8cu_helpers import pinNever

const childReplays = replayForks or replayExecs
  ## A replay child runs, and is a POSIX process the SUT can signal.

when childReplays:
  import std/posix

# =============================================================================
# 1. storedGaps: malformed gaps metadata is a miss
# =============================================================================

proc int32GapsFn(x: int) =
  if x == 42: symexTarget("int32_gaps")

suite "INT-32 (1): a malformed gaps record is a miss for the whole record":
  test "a verdict whose gaps break part-way is not served":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(int32GapsFn, tLabel("int32_gaps"),
                                 defaultSymexSettings())
    # Two gaps declared; the second's class is missing.
    var meta = {"soundness": "4:0:0:1:0:0", "gapsv": "1", "gapsn": "2",
                "gapsc0": "0", "gapsk0": "feOpaqueCallUnmodelled",
                "gapsm0": "first", "gapsk1": "feOpaqueCallUnmodelled",
                "gapsm1": "second"}.toTable
    db.save(key & cacheKeyUnknown, @[], meta, verdictCacheMaxEntries)
    check loadSymexVerdict(db, int32GapsFn, tLabel("int32_gaps"),
                           defaultSymexSettings()).isNone
    # A class out of range is malformed too.
    meta["gapsc1"] = "99"
    db.save(key & cacheKeyUnknown, @[], meta, verdictCacheMaxEntries)
    check loadSymexVerdict(db, int32GapsFn, tLabel("int32_gaps"),
                           defaultSymexSettings()).isNone
    # Whole, it is a hit with both gaps.
    meta["gapsc1"] = "0"
    db.save(key & cacheKeyUnknown, @[], meta, verdictCacheMaxEntries)
    let hit = loadSymexVerdict(db, int32GapsFn, tLabel("int32_gaps"),
                               defaultSymexSettings())
    check hit.isSome
    check hit.get.gaps.len == 2
    pinNever(cellKey(axConstruct, "cache/record/gaps"),
      hit.isSome and hit.get.gaps.len == 2,
      "a gaps record broken part-way is a miss; whole, it serves every gap")

  test "a witness entry whose gaps count is not a number is not served":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(int32GapsFn, tLabel("int32_gaps"),
                                 defaultSymexSettings())
    db.save(key & cacheKeySat, @[], {"soundness": "4:0:0:1:0:0",
            "gapsv": "1", "gapsn": "x"}.toTable, 64)
    check loadSymexWitnesses(db, int32GapsFn, tLabel("int32_gaps"),
                             defaultSymexSettings()).len == 0

  test "control: a record with no gaps metadata is still a hit (pre-S8av)":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(int32GapsFn, tLabel("int32_gaps"),
                                 defaultSymexSettings())
    db.save(key & cacheKeyUnknown, @[], {"soundness": "4:0:0:1:0:0"}.toTable,
            verdictCacheMaxEntries)
    check loadSymexVerdict(db, int32GapsFn, tLabel("int32_gaps"),
                           defaultSymexSettings()).isSome

# =============================================================================
# 3. saveSymexRaisedImpl keeps the strongest finding per type
# =============================================================================

let int32RaisedProg = SymexProgram(body: mkBlock(@[]))
let int32RaisedTarget = tRaisedExn("ValueError")

suite "INT-32 (3): the strongest finding of a raised type is stored":
  test "an untrusted first finding does not displace a trusted second":
    let db = inMemoryDatabase()
    var errors: seq[string]
    let weak = RawResult(status: sxRaised, raisedTypeId: "ValueError",
                         soundness: Soundness(replay: rsUnconfirmed))
    let strong = RawResult(status: sxRaised, raisedTypeId: "ValueError",
                           soundness: Soundness(replay: rsNotNeeded))
    let weakGaps = @[FindingGap(class: dcSubstituted, kind: "weak", msg: "w")]
    let strongGaps = @[FindingGap(class: dcNoAnswer, kind: "strong", msg: "s")]
    let weakWit = @[integerChoice(1, 0, 10, 0)]
    let strongWit = @[integerChoice(7, 0, 10, 0)]
    check saveSymexRaisedImpl(db, int32RaisedProg, int32RaisedTarget,
                              defaultSymexSettings(), @[weak, strong], errors,
                              @[weakGaps, strongGaps], @[weakWit, strongWit])
    check errors.len == 0
    let loaded = loadSymexRaisedImpl(db, int32RaisedProg, int32RaisedTarget,
                                     defaultSymexSettings(), errors)
    check loaded.len == 1
    check loaded[0].raw.soundness.replay == rsNotNeeded
    check loaded[0].gaps == strongGaps
    check loaded[0].choices == strongWit
    pinNever(cellKey(axConstruct, "replay/settle/policy"),
      loaded.len == 1 and loaded[0].raw.soundness.replay == rsNotNeeded and
        loaded[0].choices == strongWit,
      "the strongest raise of a type is stored with its own gaps and witness")

  test "a host-runnable finding outranks an unsafe one; a tie keeps the first":
    let db = inMemoryDatabase()
    var errors: seq[string]
    let unsafe = RawResult(status: sxRaised, raisedTypeId: "ValueError",
                           soundness: Soundness(replay: rsUnconfirmed,
                                                witnessUnsafe: true))
    let runnable = RawResult(status: sxRaised, raisedTypeId: "ValueError",
                             soundness: Soundness(replay: rsUnconfirmed))
    let later = RawResult(status: sxRaised, raisedTypeId: "ValueError",
                          soundness: Soundness(replay: rsUnconfirmed))
    check saveSymexRaisedImpl(db, int32RaisedProg, int32RaisedTarget,
                              defaultSymexSettings(), @[unsafe, runnable, later],
                              errors, @[],
                              @[@[integerChoice(1, 0, 10, 0)],
                                @[integerChoice(2, 0, 10, 0)],
                                @[integerChoice(3, 0, 10, 0)]])
    let loaded = loadSymexRaisedImpl(db, int32RaisedProg, int32RaisedTarget,
                                     defaultSymexSettings(), errors)
    check loaded.len == 1
    check not loaded[0].raw.soundness.witnessUnsafe
    check loaded[0].choices == @[integerChoice(2, 0, 10, 0)]

# =============================================================================
# 4. winnerLossy reads the winner's own extraction
# =============================================================================

suite "INT-32 (4): a sibling's extraction does not make the winner lossy":
  let failed = SymexErrorInfo(kind: feExtractionFailed,
                              severity: severity(feExtractionFailed),
                              msg: "float64 witness at 'y' did not resolve")
  test "a faithful winner beside a sibling's failed extraction":
    let raw = RawResult(status: sxSat, soundness: Soundness(replay: rsNotNeeded),
                        errors: @[failed])
    check not winnerLossy(raw, staticLossy = false)
    check winnerCandidate(raw).errors.len == 0

  test "the winner's own failed extraction":
    let raw = RawResult(status: sxSat, soundness: Soundness(replay: rsNotNeeded),
                        errors: @[failed], witnessExtraction: @[failed])
    check winnerLossy(raw, staticLossy = false)
    check candidateLossy(winnerCandidate(raw))

# =============================================================================
# 5. witnessUnsafe is rendered (pin)
# =============================================================================

suite "INT-32 (5): every report format shows witnessUnsafe":
  test "text, JUnit, JSON and GitHub":
    let f = SymexFinding(status: sfSat, targetDesc: "label(\"u\")",
                         soundness: Soundness(replay: rsConfirmed,
                                              witnessUnsafe: true))
    let r = Report[int](outcome: otPassed, examples: 1, symexFindings: @[f])
    check "witnessUnsafe=true" in renderReport(r, ofText)
    check "witnessUnsafe=true" in renderReport(r, ofJunit)
    check "\"witnessUnsafe\":true" in renderReport(r, ofJson)
    check "witness unsafe" in renderReport(r, ofGithubAnnotation)

# =============================================================================
# 2 and 7: through a real replay
# =============================================================================

var int32Fresh = false
  ## Read by the SUTs below and written by no one: a fresh symbol to the walker
  ## (`dcFreshSymbol`), so the only path to each target is `scSpurious`-tainted
  ## and the replay decides. It really holds false.

when childReplays:
  proc int32Signal(k, sig: int) {.symexOpaque.} =
    if k > 0: discard kill(getpid(), cint(sig))

  proc int32Terminated(k: int) =
    ## The replay's child is ended by `SIGTERM` before the target.
    symexAssume(k > 0 and k < 10)
    int32Signal(k, int(SIGTERM))
    symexTarget("int32_term")

  proc int32Aborted(k: int) =
    ## The replay's child aborts before the target.
    symexAssume(k > 0 and k < 10)
    int32Signal(k, int(SIGABRT))
    symexTarget("int32_abrt")

proc int32Hangs(a: bool; x: int) =
  let o = int32Fresh and (a or not a)
  if not o:
    if x == 42:
      os.sleep(60_000)
      symexTarget("int32_hang")

proc findOf(fs: seq[SymexFinding]; desc: string): SymexFinding =
  for f in fs:
    if f.targetDesc == desc: return f
  raiseAssert "no finding for " & desc

suite "INT-32 (2): a replay ended from outside the SUT is run-dependent":
  test "the signal decides, not the ending alone":
    when childReplays:
      check rdReplay in replayResultOf(
        ReplayChild(ending: reSignalled, code: int(SIGTERM)), false).runDependence
      check rdReplay in replayResultOf(
        ReplayChild(ending: reSignalled, code: int(SIGKILL)), false).runDependence
      check rdReplay notin replayResultOf(
        ReplayChild(ending: reSignalled, code: int(SIGSEGV)), false).runDependence
      check rdReplay notin replayResultOf(
        ReplayChild(ending: reSignalled, code: int(SIGABRT)), false).runDependence

  test "a SUT ended by SIGTERM leaves a verdict that is not stored":
    when childReplays:
      let db = inMemoryDatabase()
      let cold = findOf(symexFindAllWitnesses(int32Terminated, db),
                        "label(\"int32_term\")")
      checkpoint $cold.hints
      check cold.status == sfUnknown
      check rdReplay in cold.soundness.runDependence
      let warm = findOf(symexFindAllWitnesses(int32Terminated, db),
                        "label(\"int32_term\")")
      check not warm.fromCache

  test "control: a SUT that aborts itself is the program's, and stored":
    when childReplays:
      let db = inMemoryDatabase()
      let cold = findOf(symexFindAllWitnesses(int32Aborted, db),
                        "label(\"int32_abrt\")")
      checkpoint $cold.hints
      check cold.status == sfUnknown
      check rdReplay notin cold.soundness.runDependence
      let warm = findOf(symexFindAllWitnesses(int32Aborted, db),
                        "label(\"int32_abrt\")")
      check warm.fromCache

const int32Bound300 = SymexSettings(replayTimeoutMs: 300)
const int32Bound400 = SymexSettings(replayTimeoutMs: 400)

suite "INT-32 (7): a witness that always runs past the bound is stored":
  test "the bound is a fact of the key: a hit does not replay":
    when childReplays:
      let db = inMemoryDatabase()
      let before = replayExecutions()
      let cold = findOf(symexFindAllWitnesses(int32Hangs, db, int32Bound300),
                        "label(\"int32_hang\")")
      checkpoint $cold.hints
      check cold.status == sfUnknown
      check replayExecutions() > before
      check rdReplay notin cold.soundness.runDependence
      let mid = replayExecutions()
      let warm = findOf(symexFindAllWitnesses(int32Hangs, db, int32Bound300),
                        "label(\"int32_hang\")")
      check warm.fromCache
      check replayExecutions() == mid
      pinNever(cellKey(axConstruct, "replay/settle/policy"),
        warm.fromCache and replayExecutions() == mid,
        "a witness killed at replayTimeoutMs is stored; a hit does not replay")
      # A different bound is a different key: decided again.
      let other = findOf(symexFindAllWitnesses(int32Hangs, db, int32Bound400),
                         "label(\"int32_hang\")")
      check not other.fromCache

  test "a timeout a limit or a flood caused stays run-dependent":
    check rdReplay in replayResultOf(
      ReplayChild(ending: reTimedOut, why: "it used the replay's CPU-time " &
                  "limit (2 s) and was stopped"), false).runDependence
    check rdReplay notin replayResultOf(
      ReplayChild(ending: reTimedOut), false).runDependence

# =============================================================================
# 9. a replay no child could run is stored refused, and never run in the host
# =============================================================================

suite "INT-32 (9): a lossy winner whose replay was refused is rsRefused":
  let lossyWinner = RawResult(status: sxSat,
                              soundness: Soundness(replay: rsNotNeeded))
  test "statically refused: rsRefused, not host-runnable, stored":
    let r = replayResultOf(refusedStatically("no child on this platform"),
                           lossy = true)
    let s = settleWinner(lossyWinner, r, "").soundness
    check s.replay == rsRefused
    check not trustedSat(s)
    check not hostRunnable(s)
    check s.cacheable

  test "refused for a reason of the moment: not stored":
    let r = replayResultOf(ReplayChild(ending: reRefused, why: "fork failed",
                                       runDependent: true), lossy = true)
    let s = settleWinner(lossyWinner, r, "").soundness
    check s.replay == rsRefused
    check not s.cacheable

  test "a hit serves rsRefused, so it is not run in the host":
    let db = inMemoryDatabase()
    var errors: seq[string]
    let prog = SymexProgram(body: mkBlock(@[]))
    let f = SymexFinding(status: sfSat, witnessChoices: @[],
                         soundness: Soundness(replay: rsRefused))
    check saveSymexWitnessImpl(db, prog, tLabel("int32_refused"),
                               defaultSymexSettings(), f, errors)
    let loaded = loadSymexWitnessesImpl(db, prog, tLabel("int32_refused"),
                                        defaultSymexSettings(), errors)
    check loaded.len == 1
    check loaded[0].soundness.replay == rsRefused
    check not hostRunnable(loaded[0].soundness)
    pinNever(cellKey(axConstruct, "replay/settle/policy"),
      loaded.len == 1 and not hostRunnable(loaded[0].soundness),
      "a lossy winner no replay child ran is rsRefused, not run in the host")

suite "INT-32: walker version floor":
  test "408":
    check parseInt(symexWalkerVersion) >= 408
