## RFC-0005 review R2 (SD1/SD2) -- a statement owns only the lowering taint
## it queued, and its taint reaches every path it produced.
##
## R1-04 made `walk` the unit of the pending-lowering-taint discipline: on
## exit it took `stmtStrayTaint + loweringPendingTaint`, cleared the queue,
## and stamped the set on the paths it returned. Two holes:
##   SD1  a `walk` nested inside an expression (a body descended while the
##        calling expression is half lowered) cleared taint the CALLER had
##        queued -- an unwritten global read before the call -- and stamped
##        it only on the nested statement's result, which is empty when the
##        body leaves through `return`/`break`/`continue`.
##   SD2  the stamp never reached paths that left the statement through an
##        exit channel (`returnedPaths`, a loop's `breakPaths` and
##        `continuePaths`).
##
## Review R3 (T1): R2 found a statement's exit entries by per-channel length
## marks. Handler bodies are walked with the handler stack cut back to the
## matched try, so an inner try in one has that try's depth and claimed every
## `caught` entry there, older ones included: the channel shrank under its
## mark and the new entry landed below it, unstamped. The same claim walked
## the earlier catch's continuation through the rest of the arm a second
## time (the source row: a false `sxSat`). Entries now carry the serial they
## were parked at (`parkExit`); a statement stamps, and a try claims, only
## what was parked after it began. The writer pin keeps every channel append
## on `parkExit` and every channel appended to in `exitEntries`.
##
## The shapes the finding named do not reach the hole from source: a closure
## body is walked with the calling expression's queue set aside
## (`takePendingLowerEffects`), and a named callee after its arguments are
## drained. The source rows pin that; the probe rows drive `walk` itself with
## a queue it does not own, as an arm that walks a child before draining
## would. Each source row runs the routine natively (`native`) beside the
## walk's verdict.
import std/[unittest, strutils, os, sets]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import ./s8cu_helpers

var gN: int          # never written: 0 natively, `feGlobalHavoc` to the walk

# The finding's trigger: `gN` is lowered (its decline queued) before the
# closure call's body is walked; the body leaves through `return`.
proc closureReturn(b: byte) =
  let f = proc(x: int): int = return 1
  if b > 3:
    let r = gN + f(1)
    if r == 5: symexTarget("hit")

proc closureReturnRaise(b: byte) =
  let f = proc(x: int): int = return 1
  if b > 3:
    let r = gN + f(1)
    if r == 5: raise newException(ValueError, "x")

# The body falls through instead.
proc closureFall(b: byte) =
  let f = proc(x: int): int = x
  if b > 3:
    let r = gN + f(1)
    if r == 5: symexTarget("hit")

# The global is read after the call.
proc closureAfter(b: byte) =
  let f = proc(x: int): int = return 1
  if b > 3:
    let r = f(1) + gN
    if r == 5: symexTarget("hit")

# The global is the call's argument.
proc closureArg(b: byte) =
  let f = proc(x: int): int = return x + 1
  if b > 3:
    let r = f(gN)
    if r == 5: symexTarget("hit")

# A nested proc the walk descends (an inline call).
proc nestedReturn(b: byte) =
  proc h(x: int): int = return 1
  if b > 3:
    let r = gN + h(1)
    if r == 5: symexTarget("hit")

# The global read inside a body that leaves through `return`.
proc closureBodyGlobal(b: byte) =
  let f = proc(x: int): int =
    if x > 0: return gN + x
    return 0
  if b > 3:
    let r = f(1)
    if r == 5: symexTarget("hit")

# A loop body that leaves through `break` after reading the global.
proc loopBreak(b: byte) =
  var r = 0
  let f = proc(x: int): int = return 1
  for i in 0 ..< 3:
    r = gN + f(i)
    if b > 3: break
  if r == 5: symexTarget("hit")

# ... and through `continue`.
proc loopContinue(b: byte) =
  var r = 0
  let f = proc(x: int): int = return 1
  var i = 0
  while i < 2:
    inc i
    r = gN + f(i)
    if b > 3: continue
  if r == 5: symexTarget("hit")

# T1's shape: two raises caught by one try in separate statements, its
# handler holding an inner try. Each path runs the handler once: `x` is 1.
proc handlerInnerTry(b: byte) =
  var x = 0
  var y = 0
  try:
    if b > 3: raise newException(ValueError, "a")
    raise newException(ValueError, "b")
  except ValueError:
    try: inc y
    except CatchableError: discard
    inc x
  if x == 2: symexTarget("hit")

# Controls: the same shapes over a value the walk knows.
proc closureKnown(b: byte) =
  let f = proc(x: int): int = return 1
  if b > 3:
    let r = int(b) + f(1)
    if r == 5: symexTarget("hit")

proc closureKnownDead(b: byte) =
  let f = proc(x: int): int = return 1
  if b > 3:
    let r = int(b) + f(1)
    if r == 2: symexTarget("hit")

proc clean(r: SymexResult): bool =
  r.status == sxSat and r.soundness.pathTaint == {} and
    r.soundness.replay == rsNotNeeded

template tainted(fn: untyped; tgt: SymexTarget) =
  let r = symexFind(fn, tgt)
  checkpoint show(r.errors)
  checkpoint $r.status & " " & $r.soundness.pathTaint & " " &
    $r.soundness.replay
  check not r.clean
  check not trusted(r) or r.status == sxUnsat

suite "R2 SD1/SD2: lowering taint survives a nested walk and its exits":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 271

  test "SD1: a nested walk keeps the caller's queue; its break path carries it":
    let probe = stmtExitTaintProbe()
    check probe.resultLen == 0
    check probe.pendingAfter == {scSpurious}   # was {}: the caller's, cleared
    check probe.breakTaint == {scSpurious}     # was {}: the stamp landed nowhere

  test "SD2: a statement's stray taint reaches every exit channel":
    let probe = stmtExitTaintProbe()
    check probe.channelTaints.len == 9
    for t in probe.channelTaints: check t == {scSpurious}
    check probe.priorTaint == {}

  test "T1: an inner try in a handler body does not hide the new caught entry":
    let probe = stmtExitTaintProbe()
    check probe.caughtTaints.len == 2
    check {scSpurious} in probe.caughtTaints   # was {} for the new entry
    # The earlier catch's entry stands outside the statement: the inner try
    # no longer claims and re-parks it.
    check {} in probe.caughtTaints

  test "every exit-channel append parks through parkExit, on a listed channel":
    let src = readFile(currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                       "smt" / "runtime.nim")
    var listed, parked: HashSet[string]
    var inIter = false
    var bare: seq[string]
    for raw in src.splitLines():
      if raw.startsWith("iterator exitEntries("): inIter = true; continue
      if inIter:
        if raw.len > 0 and raw[0] != ' ': inIter = false
        else:
          let ix = raw.find(".mitems")
          if ix > 0 and "yield" in raw:
            var j = ix
            while j > 0 and raw[j - 1] in IdentChars: dec j
            listed.incl raw[j ..< ix]
          continue
      let t = raw.strip()
      if t.startsWith("#"): continue
      let ax = t.find(".add ")
      if ax <= 0: continue
      var j = ax
      while j > 0 and t[j - 1] in IdentChars: dec j
      let chan = t[j ..< ax]
      if "parkExit(" in t: parked.incl chan
      else: bare.add t
    check listed.len == 9
    checkpoint "parked on unlisted channels: " & $(parked - listed)
    check parked == listed
    var unparked: seq[string]
    for t in bare:
      for c in listed:
        if t.contains("." & c & ".add ") or t.startsWith(c & ".add "):
          unparked.add t
    checkpoint "appends that skip parkExit: " & $unparked
    check unparked.len == 0

  test "T1 source shape: a handler's inner try leaves earlier catches alone":
    check native(handlerInnerTry(4)) == "ran"
    check native(handlerInnerTry(2)) == "ran"
    decides(handlerInnerTry, sxUnsat)

  test "closure body leaving through return (the finding)":
    check native(closureReturn(4)) == "ran"
    tainted(closureReturn, tLabel("hit"))

  test "closure body leaving through return, raise target":
    closureReturnRaise(4)
    tainted(closureReturnRaise, tRaisedExn("ValueError"))

  test "closure body falling through":
    check native(closureFall(4)) == "ran"
    tainted(closureFall, tLabel("hit"))

  test "global read after the call":
    check native(closureAfter(4)) == "ran"
    tainted(closureAfter, tLabel("hit"))

  test "global as the call's argument":
    check native(closureArg(4)) == "ran"
    tainted(closureArg, tLabel("hit"))

  test "nested proc descended inline":
    check native(nestedReturn(4)) == "ran"
    tainted(nestedReturn, tLabel("hit"))

  test "global read in a body that returns":
    check native(closureBodyGlobal(4)) == "ran"
    tainted(closureBodyGlobal, tLabel("hit"))

  test "loop body leaving through break":
    check native(loopBreak(4)) == "ran"
    tainted(loopBreak, tLabel("hit"))

  test "loop body leaving through continue":
    check native(loopContinue(4)) == "ran"
    tainted(loopContinue, tLabel("hit"))

  test "controls: a known operand decides":
    check native(closureKnown(4)) == "hit"
    decides(closureKnown, sxSat)
    check native(closureKnownDead(2)) == "ran"
    decides(closureKnownDead, sxUnsat)
