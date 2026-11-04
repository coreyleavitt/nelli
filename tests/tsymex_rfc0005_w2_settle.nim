## RFC-0005 0.9.1 wiring slice W2 -- the replay settle and the verdict cache
## (handoff "2026-11-03 -- Wiring audit", WA-2, WA-7, WA-8, WA-9).
##
## * WA-2. A replay that reaches the target and then ends its child (`quit`, a
##   signal) or runs past its bound is confirmed: the target was reached. Before
##   the fix nothing said how it ended, and two consumers then ran the same
##   witness in the host: `assertCoveredBy`'s splat and `symexForAll`'s seeds.
##   RED: the host died (`quit(3)`), in a process of its own here (`hostRun`).
## * WA-7. A replay outcome that depends on the run (`roTimedOut`, a decline for a
##   reason of the moment, a crash at the replay's memory limit) was cached as a
##   permanent `:unk`. RED: the second run served the cache and replayed nothing.
## * WA-8. The cache key did not cover how replay runs (a forked child, a
##   re-executed one, none) or `--panics:on`, where nothing is replayed.
## * WA-9. A clean winner whose witness is lossy was `trusted()` though no run
##   of the real `fn` had seen it. It is now replayed, and trusted only when the
##   replay confirms it. RED: no replay ran, and `trusted()` held.
##
## The re-execution path (Windows) runs this suite through
## `tsymex_rfc0005_w2_settle_reexec` (`-d:nelliReplayReexec`).
import std/[unittest, strutils, os, osproc, streams, strtabs]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/replayproc

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc msgOf(errs: seq[SymexErrorInfo]; k: SymexErrorKind): string =
  for e in errs:
    if e.kind == k: return e.msg
  ""

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- the SUTs ----------------------------------------------------------------
#
# `gG` is a module-level variable nothing writes: the walker's read of it is a
# fresh symbol (`feGlobalHavoc`), so a path past it is a replay candidate. It
# really holds 0.

var gG: int

proc labelThenQuit(k: int) =
  ## WA-2: reaches the label, then ends the process.
  if k == 123457:
    let a = gG
    symexTarget("t")
    quit(3 + a)

proc labelThenQuitToo(k: int) =
  ## A `testFn` for `labelThenQuit` that is not `labelThenQuit` itself.
  if k == 123457:
    symexTarget("t")
    quit(3)

type
  W2Dist = object
    ## A `seq` of tuples, which no heap cell holds: a `ref` to an object with
    ## one renders lossily (`wfLossy`, RFC-0005 S8h/S8at).
    x: int
    ys: seq[(int, int)]
  W2Box = object
    n: int
    s: W2Dist

proc lossyClean(p: ref W2Box) =
  ## WA-9: a clean path to the label; the witness renders lossily.
  if p != nil and p.n == 5:
    symexTarget("lossy")

proc lossyThenQuit(p: ref W2Box) =
  ## WA-2 with WA-9: a clean winner, lossy, that ends the process past the label.
  if p != nil and p.n == 5:
    symexTarget("lq")
    quit(4)

proc lossyNil(p: ref W2Box) =
  if p == nil or p.n == 5:
    discard p.n

proc w2Spin(v: int) {.symexOpaque.} =
  if v > 5: sleep(3000)

proc sutSpin(v: int) =
  ## WA-7: a replay that runs past a small `replayTimeoutMs`.
  symexAssume(v > 5 and v < 100)
  w2Spin(v)
  symexTarget("big")

proc w2Hog(k: int) {.symexOpaque.} =
  if k > 0:
    var s = newSeq[int](400_000_000)   # 3.2 GB: past the replay's limit
    s[k] = k

proc sutHog(k: int) =
  ## WA-7: a replay that ends at the replay's memory limit.
  symexAssume(k > 0 and k < 10)
  w2Hog(k)
  symexTarget("h")

proc quitBefore(k: int) =
  ## WA-7's control: a replay that ends the same way on every run.
  if gG == 0:
    quit(7)
  symexTarget("q")

proc confirmable(k: int) =
  if gG == 0 and k == 42:
    symexTarget("c")

const tinyReplay = SymexSettings(replayTimeoutMs: 200)
const noReplay = SymexSettings(replay: false)

# ---- runs in a process of their own ------------------------------------------

proc nativeSink(name: string; depth: int) {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    stdout.writeLine "HIT|" & name
    stdout.flushFile()

proc hostMain(mode: string) =
  ## What a test's host does with each witness. Prints `SURVIVED` if it is still
  ## running at the end.
  case mode
  of "native":
    symexCaptureBegin()
    symexHitSink = nativeSink
    labelThenQuit(123457)
  of "nativeLossy":
    symexCaptureBegin()
    symexHitSink = nativeSink
    var b = new W2Box
    b.n = 5
    lossyThenQuit(b)
  of "coveredBy":
    assertCoveredBy(labelThenQuit, tLabel("t"))
  of "coveredByLossy":
    assertCoveredBy(lossyThenQuit, tLabel("lq"))
  of "coveredByTestFn":
    try:
      assertCoveredBy(labelThenQuit, tLabel("t"), labelThenQuitToo)
      stdout.writeLine "COVERED"
    except AssertionDefect as e:
      stdout.writeLine "REFUSED|" & e.msg
  of "forAll":
    let db = inMemoryDatabase()
    for round in 1 .. 2:   # the second round is served from the cache
      let rep = symexForAll(integers(0, 1_000_000_000), labelThenQuit, db)
      var sat = 0
      for f in rep.symexFindings:
        if f.targetDesc == "label(\"t\")" and f.status == sfSat:
          inc sat
          if round == 2: stdout.writeLine "CACHED|" & $f.fromCache
      stdout.writeLine "ROUND|" & $round & "|" & $rep.outcome & "|" & $sat
  else:
    quit(250)
  stdout.writeLine "SURVIVED"
  stdout.flushFile()

if getEnv("W2_HOST").len > 0:
  hostMain(getEnv("W2_HOST"))
  quit(0)

type HostRun = object
  rc: int
  lines: seq[string]

proc hostRun(mode: string): HostRun =
  var env = newStringTable(modeCaseSensitive)
  for name, value in envPairs(): env[name] = value
  env["W2_HOST"] = mode
  let p = startProcess(getAppFilename(), env = env,
                       options = {poStdErrToStdOut})
  var output = ""
  try:
    output = p.outputStream.readAll()
  except IOError:
    discard
  result.rc = p.waitForExit(300_000)
  p.close()
  result.lines = output.splitLines()
  checkpoint mode & " rc=" & $result.rc & ":\n" & output

proc has(h: HostRun; s: string): bool =
  for l in h.lines:
    if l == s: return true
  false

proc startsWith(h: HostRun; s: string): string =
  for l in h.lines:
    if l.startsWith(s): return l
  ""

proc labelFinding(fs: seq[SymexFinding]; label: string): SymexFinding =
  for f in fs:
    if f.targetDesc == "label(\"" & label & "\")": return f
  SymexFinding(targetDesc: "missing", status: sfNotApplicable)

# ---- WA-2 --------------------------------------------------------------------

suite "W2 / WA-2: a witness known to end the process never runs in the host":
  test "native truth: the SUT reaches the label, then exits 3":
    let n = hostRun("native")
    check n.has("HIT|t")
    check n.rc == 3
    check not n.has("SURVIVED")
    let l = hostRun("nativeLossy")
    check l.has("HIT|lq")
    check l.rc == 4

  test "symexFind confirms it: the target was reached":
    let r = symexFind(labelThenQuit, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 123457
    check r.soundness.replay == rsConfirmed
    check trusted(r)
    # How it ended rides on the confirmed result.
    check r.soundness.witnessUnsafe
    check r.errors.hasKind(feReplayCrashed)
    when replayForks:
      check "code 3" in msgOf(r.errors, feReplayCrashed)
    check "after reaching the target" in msgOf(r.errors, feReplayCrashed)

  test "a confirmed replay that finished leaves the witness safe":
    let r = symexFind(confirmable, tLabel("c"))
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check not r.soundness.witnessUnsafe
    check not r.errors.hasKind(feReplayCrashed)

  test "assertCoveredBy does not run it in the host":
    let h = hostRun("coveredBy")
    check h.rc == 0
    check h.has("SURVIVED")

  test "assertCoveredBy with another testFn refuses it rather than run it":
    let h = hostRun("coveredByTestFn")
    check h.rc == 0
    check h.has("SURVIVED")
    check "not run in this process" in h.startsWith("REFUSED|")

  test "a lossy clean winner that ends the process: not run in the host either":
    let h = hostRun("coveredByLossy")
    check h.rc == 0
    check h.has("SURVIVED")

  test "symexForAll does not seed it, cold or from the cache":
    let h = hostRun("forAll")
    check h.rc == 0
    check h.has("SURVIVED")
    check h.has("ROUND|1|otPassed|1")
    check h.has("ROUND|2|otPassed|1")
    check h.has("CACHED|true")

# ---- WA-8 --------------------------------------------------------------------

suite "W2 / WA-8: the cache key covers how the build replays":
  test "fork, re-execution, none and --panics:on are four keys":
    let prog = SymexProgram()
    proc key(mode: string): string =
      symexCacheKey(prog, tLabel("t"), SymexSettings(), "z", "n", "w", "r",
                    replayMode = mode)
    let modes = [replayModeSegment(true, false, false),
                 replayModeSegment(false, true, false),
                 replayModeSegment(false, false, false),
                 replayModeSegment(true, false, true),
                 replayModeSegment(false, true, true)]
    for i in 0 ..< modes.len:
      for j in i + 1 ..< modes.len:
        check modes[i] != modes[j]
        check key(modes[i]) != key(modes[j])

  test "the default is this build's mode":
    when replayForks:
      check replayModeSegment() == "fork"
    elif replayReexecs:
      check replayModeSegment() == "reexec"
    let prog = SymexProgram()
    check symexCacheKey(prog, tLabel("t"), SymexSettings(), "z", "n", "w",
                        "r") ==
          symexCacheKey(prog, tLabel("t"), SymexSettings(), "z", "n", "w",
                        "r", replayMode = replayModeSegment())

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 266

# ---- WA-7 --------------------------------------------------------------------

suite "W2 / WA-7: a run-dependent replay outcome is not cached":
  test "a replay killed at its bound is tried again on the next run":
    let db = inMemoryDatabase()
    let n0 = replayExecutions()
    let f1 = labelFinding(symexFindAllWitnesses(sutSpin, db, tinyReplay), "big")
    check f1.status == sfUnknown
    let n1 = replayExecutions()
    check n1 > n0
    let f2 = labelFinding(symexFindAllWitnesses(sutSpin, db, tinyReplay), "big")
    check f2.status == sfUnknown
    check not f2.fromCache
    check replayExecutions() > n1

  test "a replay ended at the memory limit is tried again on the next run":
    let db = inMemoryDatabase()
    let n0 = replayExecutions()
    let f1 = labelFinding(symexFindAllWitnesses(sutHog, db), "h")
    check f1.status == sfUnknown
    let n1 = replayExecutions()
    check n1 > n0
    let f2 = labelFinding(symexFindAllWitnesses(sutHog, db), "h")
    check f2.status == sfUnknown
    check not f2.fromCache
    check replayExecutions() > n1

  test "control: a replay that crashes the same way every run stays cached":
    let db = inMemoryDatabase()
    let f1 = labelFinding(symexFindAllWitnesses(quitBefore, db), "q")
    check f1.status == sfUnknown
    let n1 = replayExecutions()
    let f2 = labelFinding(symexFindAllWitnesses(quitBefore, db), "q")
    check f2.status == sfUnknown
    check f2.fromCache
    check replayExecutions() == n1

  when replayReexecs:
    test "a decline for a runtime hook set at the time is tried again":
      let db = inMemoryDatabase()
      globalRaiseHook = proc (e: ref Exception): bool {.nimcall.} = true
      let f1 = labelFinding(symexFindAllWitnesses(confirmable, db), "c")
      globalRaiseHook = nil
      check f1.status == sfUnknown
      let n1 = replayExecutions()
      let f2 = labelFinding(symexFindAllWitnesses(confirmable, db), "c")
      check not f2.fromCache
      check f2.status == sfSat
      check replayExecutions() > n1

# ---- WA-9 --------------------------------------------------------------------

suite "W2 / WA-9: a lossy winner is trusted only once replay confirms it":
  test "the clean lossy winner is replayed, and confirmed":
    let n0 = replayExecutions()
    let r = symexFind(lossyClean, tLabel("lossy"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check rfc0005RawStatus == sxSat        # a clean winner, not a candidate
    check replayExecutions() == n0 + 1
    check r.soundness.replay == rsConfirmed
    check not r.soundness.witnessUnsafe
    check trusted(r)

  test "with replay off it cannot be confirmed, so it is not trusted":
    let r = symexFind(lossyClean, tLabel("lossy"), noReplay)
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.replay == rsUnconfirmed
    check not trusted(r)
    check r.errors.hasKind(feReplayDeclined)
    check "lossy" in msgOf(r.errors, feReplayDeclined)

  test "a lossy winner that ends the process is confirmed and unsafe":
    let r = symexFind(lossyThenQuit, tLabel("lq"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.soundness.witnessUnsafe

  test "a lossy winner on an out-of-scope target is not trusted":
    # `tNilAccess` is never replayed (`replayInScope`): no confirmation.
    let r = symexFind(lossyNil, tNilAccess())
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised              # NilAccessDefect, a clean path
    check r.soundness.replay == rsUnconfirmed
    check not trusted(r)
    check r.errors.hasKind(feReplayDeclined)

  test "a faithful clean winner is not replayed":
    let n0 = replayExecutions()
    let r = symexFind(confirmable, tLabel("c"), noReplay)
    check r.status == sxUnknown           # a candidate, with replay off
    let r2 = symexFind(labelThenQuitToo, tLabel("t"))
    check r2.status == sxSat
    check r2.soundness.replay == rsNotNeeded
    check trusted(r2)
    check replayExecutions() == n0
