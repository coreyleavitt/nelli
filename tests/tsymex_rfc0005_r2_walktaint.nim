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
## The walk's initial path is built by one constructor that drains what the
## parameter set-up queued (`initialWalkPath`), pinned by a proc parameter.
##
## Review R5: a channel is bound to its walk's clock when its group is made
## (`newExits`) and parks only on it, and a mark is made only by a clock and
## refused by any other. The channels are grouped by owner, and the stamp,
## the probe and a try's claim walk the groups, so a new channel is reached
## by all three without a list to extend.
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

# A proc-typed parameter: allocating it declines (no lambda the walk built)
# before the walk begins. The target does not read it, but the path the
# walk starts from carries the decline.
proc procParam(f: proc(x: int): int {.closure.}; b: byte) =
  if b > 3: symexTarget("hit")

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
    check parseInt(symexWalkerVersion) >= 272

  test "SD1: a nested walk keeps the caller's queue; its break path carries it":
    let probe = stmtExitTaintProbe()
    check probe.resultLen == 0
    check probe.pendingAfter == {scSpurious}   # was {}: the caller's, cleared
    check probe.breakTaint == {scSpurious}     # was {}: the stamp landed nowhere

  test "SD2: a statement's stray taint reaches every exit channel":
    let probe = stmtExitTaintProbe()
    # The probe parks on every channel the walk's groups hold; a channel
    # added to any group is counted, stamped and checked here unedited.
    check probe.channelsParked >= 9
    check probe.channelTaints.len == probe.channelsParked
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

  test "initial path: a proc parameter's decline reaches the result":
    let r = symexFind(procParam, tLabel("hit"))
    checkpoint show(r.errors)
    checkpoint $r.status & " " & $r.soundness.pathTaint & " " &
      $r.soundness.replay
    check not r.clean
    check r.status == sxUnknown
    check r.errors.named(ceUnsupportedHof)
    # The leak pin stays quiet: the decline was drained onto the initial
    # path, the one every path of the walk derives from. A driver that
    # skips the drain leaves it queued, and the pin fires here.
    check not r.errors.named(weInternalWalkerFault)

  test "controls: a known operand decides":
    check native(closureKnown(4)) == "hit"
    decides(closureKnown, sxSat)
    check native(closureKnownDead(2)) == "ran"
    decides(closureKnownDead, sxUnsat)

type
  Entry = tuple[depth: int, v: string]
  RefEntry = ref object
    depth: int
    tag: string
  One = object
    ch: ExitChannel[Entry]
  Pair = object
    a, b: ExitChannel[Entry]
  Nested = object
    ## A group of groups: the walks reach the inner channels too.
    held: Pair
    loose: ExitChannel[Entry]
  RefOne = object
    ch: ExitChannel[RefEntry]
  NotAGroup = object
    ch: ExitChannel[Entry]
    count: int
  Undepthed = object
    ch: ExitChannel[tuple[depth: int, w: int]]

# The hooks the group walks and `claimAt` reach an item through.
func depthOf(e: Entry): int = e.depth
func depthOf(e: RefEntry): int = e.depth
proc exitPath(e: var Entry): var string = e.v

proc vs[T](xs: seq[T]): seq[string] =
  for x in xs: result.add x.v

suite "R4: exit channels (nelli/smt/exits)":

  test "park assigns increasing serials across channels on one clock":
    let clock = newExitClock()
    var g = clock.newExits(Pair)
    let m0 = clock.mark
    check not clock.parkedSince(m0)
    g.a.park((0, "a1"))
    let m1 = clock.mark
    check clock.parkedSince(m0)
    check not clock.parkedSince(m1)
    g.b.park((0, "b1"))
    g.a.park((0, "a2"))
    check clock.parkedSince(m1)
    # Since m1: b1 and a2, not a1.
    var since: seq[string]
    for e in g.a.mitemsSince(m1): since.add e.v
    for e in g.b.mitemsSince(m1): since.add e.v
    check since == @["a2", "b1"]
    check g.a.contents.vs == @["a1", "a2"]
    check g.a.len == 2 and g.b.len == 1

  test "claimAt takes only entries parked after the mark, at the depth":
    let clock = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((1, "old1"))
    g.ch.park((0, "old0"))
    let m = clock.mark
    g.ch.park((1, "new1a"))
    g.ch.park((0, "new0"))
    g.ch.park((1, "new1b"))
    check g.ch.claimAt(m, 1).vs == @["new1a", "new1b"]
    # Kept entries stay in order.
    check g.ch.contents.vs == @["old1", "old0", "new0"]
    # A claim at the other depth sees only the new one.
    check g.ch.claimAt(m, 0).vs == @["new0"]
    check g.ch.contents.vs == @["old1", "old0"]
    # Nothing is parked after a fresh mark.
    check g.ch.claimAt(clock.mark, 1).len == 0

  test "kept entries keep their original serial through a claim":
    # T1's shape: an outer scope marks, an inner try claims around an entry
    # it does not own, and the outer scope must still find that entry.
    let clock = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((0, "earlier"))
    let outer = clock.mark
    g.ch.park((0, "outerOwn"))
    let inner = clock.mark
    g.ch.park((0, "innerOwn"))
    check g.ch.claimAt(inner, 0).vs == @["innerOwn"]
    var seen: seq[string]
    for e in g.ch.mitemsSince(outer): seen.add e.v
    check seen == @["outerOwn"]
    # Re-reading after the claim: the earlier entry is still not "since".
    check g.ch.claimAt(outer, 0).vs == @["outerOwn"]
    check g.ch.contents.vs == @["earlier"]

  test "a stamp replaces the item and the entry keeps its serial":
    let clock = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((0, "before"))
    let m = clock.mark
    g.ch.park((0, "after"))
    for e in g.ch.mitemsSince(m): e.v = e.v & "*"
    check g.ch.contents.vs == @["before", "after*"]
    # The stamped entry is still parked after `m`.
    check g.ch.claimAt(m, 0).vs == @["after*"]

  test "the serial is the entry's: one ref parked twice moves neither":
    let clock = newExitClock()
    var g = clock.newExits(RefOne)
    let shared = RefEntry(depth: 0, tag: "x")
    g.ch.park(shared)
    let m = clock.mark
    g.ch.park(shared)
    # Parking the same ref again did not move the first entry past `m`.
    var n = 0
    for e in g.ch.mitemsSince(m): inc n
    check n == 1
    check g.ch.claimAt(m, 0).len == 1
    check g.ch.len == 1

  test "takeAll empties the channel whatever the serials":
    let clock = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((0, "a"))
    let m = clock.mark
    g.ch.park((3, "b"))
    check g.ch.takeAll().vs == @["a", "b"]
    check g.ch.len == 0
    check g.ch.claimAt(m, 3).len == 0
    var items: seq[string]
    for e in g.ch: items.add e.v
    check items.len == 0

suite "R5: channels bound to their clock, grouped by owner":

  test "a channel parks only on the clock it was bound to":
    let clock = newExitClock()
    var g = clock.newExits(One)
    # No clock can be passed to `park`: the channel's own is the only one.
    check not compiles(g.ch.park(clock, (0, "x")))
    # A channel bound to no clock cannot be parked on at all.
    var loose: ExitChannel[Entry]
    expect AssertionDefect:
      loose.park((0, "x"))
    check loose.len == 0

  test "a mark is unforgeable: only a clock makes one":
    let clock = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((0, "a"))
    # Its fields are the module's: no serial can be written from outside.
    check not compiles(ExitMark(serial: 0))
    check not compiles(ExitMark(clock: clock, serial: 0))
    check not compiles(clock.mark.serial)
    # A default mark is bound to no clock and claims nothing: it is refused.
    expect AssertionDefect:
      discard g.ch.claimAt(default(ExitMark), 0)
    expect AssertionDefect:
      for e in g.ch.mitemsSince(default(ExitMark)): discard
    expect AssertionDefect:
      discard clock.parkedSince(default(ExitMark))
    check g.ch.contents.vs == @["a"]

  test "a mark of another clock is refused":
    let clock = newExitClock()
    let other = newExitClock()
    var g = clock.newExits(One)
    g.ch.park((0, "a"))
    let foreign = other.mark
    expect AssertionDefect:
      discard g.ch.claimAt(foreign, 0)
    expect AssertionDefect:
      for e in g.ch.mitemsSince(foreign): discard
    expect AssertionDefect:
      discard clock.parkedSince(foreign)
    check g.ch.contents.vs == @["a"]

  test "newExits binds every channel of a nested group to one clock":
    let clock = newExitClock()
    var g = clock.newExits(Nested)
    let m = clock.mark
    g.held.a.park((0, "a"))
    g.loose.park((0, "l"))
    g.held.b.park((0, "b"))
    var seen: seq[string]
    for e in g.held.a.mitemsSince(m): seen.add e.v
    for e in g.held.b.mitemsSince(m): seen.add e.v
    for e in g.loose.mitemsSince(m): seen.add e.v
    check seen == @["a", "b", "l"]

  test "a group holds only channels and groups":
    let clock = newExitClock()
    check not compiles(clock.newExits(NotAGroup))
    check compiles(clock.newExits(Nested))

  test "claimAt requires the item's depth hook":
    let clock = newExitClock()
    var g = clock.newExits(Undepthed)
    let m = clock.mark
    # `Undepthed`'s items have a `depth` field but no `depthOf`: the claim
    # does not fall back on the field.
    check not compiles(g.ch.claimAt(m, 0))
    g.ch.park((depth: 0, w: 1))
    check g.ch.len == 1

  test "parkOnEach and visitSince reach every channel of the group":
    let clock = newExitClock()
    var g = clock.newExits(Nested)
    g.held.a.park((0, "before"))
    let m = clock.mark
    var made = 0
    g.parkOnEach(proc (): string =
      inc made
      "p" & $made)
    check made == 3     # held.a, held.b, loose
    var visited: seq[string]
    g.visitSince(m, proc (p: var string) =
      visited.add p
      p = p & "*")
    check visited == @["p1", "p2", "p3"]
    check g.held.a.contents.vs == @["before", "p1*"]
    check g.held.b.contents.vs == @["p2*"]
    check g.loose.contents.vs == @["p3*"]

  test "a group claim takes each channel's own claim, in field order":
    let clock = newExitClock()
    var g = clock.newExits(Pair)
    g.a.park((1, "oldA"))
    let m = clock.mark
    g.b.park((1, "b1"))
    g.a.park((0, "a0"))
    g.a.park((1, "a1"))
    g.b.park((0, "b0"))
    let claimed = g.claimAt(m, 1)
    check claimed.a.contents.vs == @["a1"]
    check claimed.b.contents.vs == @["b1"]
    # What was not claimed stays, in order, still after the mark.
    check g.a.contents.vs == @["oldA", "a0"]
    check g.b.contents.vs == @["b0"]
    check g.claimAt(m, 0).a.contents.vs == @["a0"]
    check g.a.contents.vs == @["oldA"]
    # The claimed group is bound to no clock: nothing is parked on it.
    var c2 = claimed
    expect AssertionDefect:
      c2.a.park((1, "x"))
