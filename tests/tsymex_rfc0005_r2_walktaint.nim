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
## were parked at; a statement stamps, and a try claims, only what was
## parked after it began.
##
## Review R4: the channels are `ExitChannel`s (`nelli/smt/exits`), whose
## storage is private: `park` is the only way on and takes the serial, which
## lives on the entry rather than the shared `Path`. The R3 text scan over
## `runtime.nim` is gone; the module's semantics are pinned directly below.
##
## The shapes the finding named do not reach the hole from source: a closure
## body is walked with the calling expression's queue set aside
## (`takePendingLowerEffects`), and a named callee after its arguments are
## drained. The source rows pin that; the probe rows drive `walk` itself with
## a queue it does not own, as an arm that walks a child before draining
## would. Each source row runs the routine natively (`native`) beside the
## walk's verdict.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/exits
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

type Entry = tuple[depth: int, v: string]

proc vs[T](xs: seq[T]): seq[string] =
  for x in xs: result.add x.v

suite "R4: exit channels (nelli/smt/exits)":

  test "park assigns increasing serials across channels on one clock":
    var clock: ExitClock
    var a, b: ExitChannel[Entry]
    let m0 = clock.mark
    check not clock.parkedSince(m0)
    a.park(clock, (0, "a1"))
    let m1 = clock.mark
    check clock.parkedSince(m0)
    check not clock.parkedSince(m1)
    b.park(clock, (0, "b1"))
    a.park(clock, (0, "a2"))
    check clock.parkedSince(m1)
    # Since m1: b1 and a2, not a1.
    var since: seq[string]
    for e in a.mitemsSince(m1): since.add e.v
    for e in b.mitemsSince(m1): since.add e.v
    check since == @["a2", "b1"]
    check a.contents.vs == @["a1", "a2"]
    check a.len == 2 and b.len == 1

  test "claimAt takes only entries parked after the mark, at the depth":
    var clock: ExitClock
    var ch: ExitChannel[Entry]
    ch.park(clock, (1, "old1"))
    ch.park(clock, (0, "old0"))
    let m = clock.mark
    ch.park(clock, (1, "new1a"))
    ch.park(clock, (0, "new0"))
    ch.park(clock, (1, "new1b"))
    check ch.claimAt(m, 1).vs == @["new1a", "new1b"]
    # Kept entries stay in order.
    check ch.contents.vs == @["old1", "old0", "new0"]
    # A claim at the other depth sees only the new one.
    check ch.claimAt(m, 0).vs == @["new0"]
    check ch.contents.vs == @["old1", "old0"]
    # Nothing is parked after a fresh mark.
    check ch.claimAt(clock.mark, 1).len == 0

  test "kept entries keep their original serial through a claim":
    # T1's shape: an outer scope marks, an inner try claims around an entry
    # it does not own, and the outer scope must still find that entry.
    var clock: ExitClock
    var ch: ExitChannel[Entry]
    ch.park(clock, (0, "earlier"))
    let outer = clock.mark
    ch.park(clock, (0, "outerOwn"))
    let inner = clock.mark
    ch.park(clock, (0, "innerOwn"))
    check ch.claimAt(inner, 0).vs == @["innerOwn"]
    var seen: seq[string]
    for e in ch.mitemsSince(outer): seen.add e.v
    check seen == @["outerOwn"]
    # Re-reading after the claim: the earlier entry is still not "since".
    check ch.claimAt(outer, 0).vs == @["outerOwn"]
    check ch.contents.vs == @["earlier"]

  test "a stamp replaces the item and the entry keeps its serial":
    var clock: ExitClock
    var ch: ExitChannel[Entry]
    ch.park(clock, (0, "before"))
    let m = clock.mark
    ch.park(clock, (0, "after"))
    for e in ch.mitemsSince(m): e.v = e.v & "*"
    check ch.contents.vs == @["before", "after*"]
    # The stamped entry is still parked after `m`.
    check ch.claimAt(m, 0).vs == @["after*"]

  test "the serial is the entry's: one ref parked twice moves neither":
    type R = ref object
      depth: int
      tag: string
    var clock: ExitClock
    var ch: ExitChannel[R]
    let shared = R(depth: 0, tag: "x")
    ch.park(clock, shared)
    let m = clock.mark
    ch.park(clock, shared)
    # Parking the same ref again did not move the first entry past `m`.
    var n = 0
    for e in ch.mitemsSince(m): inc n
    check n == 1
    check ch.claimAt(m, 0).len == 1
    check ch.len == 1

  test "takeAll empties the channel whatever the serials":
    var clock: ExitClock
    var ch: ExitChannel[Entry]
    ch.park(clock, (0, "a"))
    let m = clock.mark
    ch.park(clock, (3, "b"))
    check ch.takeAll().vs == @["a", "b"]
    check ch.len == 0
    check ch.claimAt(m, 3).len == 0
    var items: seq[string]
    for e in ch: items.add e.v
    check items.len == 0
