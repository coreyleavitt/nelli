import std/[unittest, sequtils, strutils]
import nelli

# C1: slot -> file:line:col side-table emitted at {.cover.} expansion.
# Unblocks source-mapped coverage-gap reports: an unhit slot can be
# translated back to the source location(s) that hash to it.

proc allRegisteredSources(): seq[string] =
  for slot in 0 ..< coverageEdgeCount:
    result.add edgeSources(slot)

suite "{.cover.} pragma: source-location registration":
  setup:
    setCoverageMode(cmRecording)
  teardown:
    setCoverageMode(cmOff)

  test "if/else arms register distinct source locations against their slots":
    let before = allRegisteredSources()
    proc trivial(x: int): int {.cover.} =
      if x > 0:
        x + 1
      else:
        x - 1
    let after = allRegisteredSources()
    let newLocs = after.filterIt(it notin before)
    check newLocs.len == 2
    check newLocs[0] != newLocs[1]
    for loc in newLocs:
      check "tcovsourcetable" in loc

  test "case arms register a source location per arm":
    let before = allRegisteredSources()
    proc classify(x: int): string {.cover.} =
      case x
      of 0:
        "zero"
      of 1:
        "one"
      else:
        "many"
    let after = allRegisteredSources()
    let newLocs = after.filterIt(it notin before)
    check newLocs.len == 3
    check newLocs.deduplicate().len == 3

  test "while body registers a source location":
    let before = allRegisteredSources()
    proc countdown(x: int): int {.cover.} =
      var n = x
      while n > 0:
        dec n
      n
    let after = allRegisteredSources()
    let newLocs = after.filterIt(it notin before)
    check newLocs.len == 1

  test "uncoveredSources reports only the not-taken arm's location":
    let before = allRegisteredSources()
    proc gate(x: int): int {.cover.} =
      if x > 0:
        x + 1
      else:
        x - 1
    let newLocs = allRegisteredSources().filterIt(it notin before)
    require newLocs.len == 2  # the two arms just registered

    resetCoverage()
    discard gate(5)  # only the "then" arm executes

    let gaps = uncoveredSources()
    let stillGap = newLocs.filterIt(it in gaps)
    let noLongerGap = newLocs.filterIt(it notin gaps)
    check stillGap.len == 1     # the not-taken "else" arm
    check noLongerGap.len == 1  # the taken "then" arm

  test "multiple {.cover.} procs accumulate into one table without clobbering":
    let before = allRegisteredSources()
    proc procA(x: int): int {.cover.} =
      if x > 0: 1 else: 0
    proc procB(x: int): int {.cover.} =
      if x > 0: 1 else: 0
    let newLocs = allRegisteredSources().filterIt(it notin before)
    # Two procs, two arms each; all four locations distinct and present —
    # procB's registration didn't clobber procA's.
    check newLocs.len == 4
    check newLocs.deduplicate().len == 4

  test "collision honesty: a slot with two colliding locations reports both, and is covered iff either was hit":
    # Simulate a bitmap collision directly: two distinct source locations
    # deliberately registered against the SAME slot (this does happen in
    # practice — 8192 slots, AFL convention — but forcing it here is more
    # robust than hunting for a natural collision).
    const slot = 4321
    resetCoverage()
    registerEdgeSource(slot, "fileA.nim:1:1")
    registerEdgeSource(slot, "fileB.nim:2:2")

    let locs = edgeSources(slot)
    check "fileA.nim:1:1" in locs
    check "fileB.nim:2:2" in locs
    check locs.len == 2

    # Neither hit -> the slot (and both its locations) is a gap.
    check "fileA.nim:1:1" in uncoveredSources()
    check "fileB.nim:2:2" in uncoveredSources()

    # Hitting EITHER location's edge marks the whole slot covered — you
    # cannot tell which of the two fired. Neither location appears in the
    # gap report anymore, even though "fileB.nim:2:2" itself was never hit.
    recordEdge(slot)
    check "fileA.nim:1:1" notin uncoveredSources()
    check "fileB.nim:2:2" notin uncoveredSources()

  test "a {.cover.} lambda instruments and registers its arms' source locations":
    let before = allRegisteredSources()
    let f = (proc(x: int): int {.cover.} =
      if x > 0:
        x + 1
      else:
        x - 1)
    let newLocs = allRegisteredSources().filterIt(it notin before)
    check newLocs.len == 2
    check newLocs.deduplicate().len == 2

    resetCoverage()
    check f(5) == 6
    let gaps = uncoveredSources()
    let stillGap = newLocs.filterIt(it in gaps)
    check stillGap.len == 1  # the "else" arm wasn't taken
