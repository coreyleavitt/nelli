## RFC-0016 INT-35 (0005 review R6-03, R5-08): the exit-group guards.
##
## R6-03. `forEachExitGroup` names the groups a walk keeps by hand. A group
## field added to `WalkCtx` or a frame and left out of it would be stamped by
## no statement and claimed by no `try`, and the probe that parks on every
## channel walks the same list, so it would not see the gap either. Now every
## field of `WalkCtx`, `CallFrame`, `LoopFrame` and `CallFrameCtx` that holds
## an exit group (directly, as a frame, or as a seq of frames) must be named
## as walked or as deliberately unwalked, or `runtime.nim` does not compile
## (`collectExitGroupFields`).
##
## R5-08. `mitemsSince` yielded the parked item as `var T`, so any importer
## could change an entry's handler depth after it was parked, and a `try`
## would then claim it at the wrong depth. It is private to `exits`; its one
## reader, `visitSince`, hands out only the path.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/exits
from nelli/smt/admission import cellKey, axConstruct
import ./s8cu_helpers

type ProbeItem = object
  depth: int

suite "INT-35: exit-group guards":

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 413

  test "R6-03: every exit-group field of the walk is accounted for":
    let paths = exitGroupFieldPaths().toHashSet
    for p in ["WalkCtx.topExits", "WalkCtx.callStack", "WalkCtx.loopStack",
              "WalkCtx.frame", "WalkCtx.frameStack", "CallFrame.exits",
              "LoopFrame.exits", "CallFrameCtx.exits"]:
      checkpoint p
      check p in paths

  test "R5-08: a parked entry's item cannot be changed from outside exits":
    var clock = newExitClock()
    var ch: ExitChannel[ProbeItem]
    let ok = not compiles(
      (for it in ch.mitemsSince(clock.mark): it.depth = 3))
    check ok
    pinNever(cellKey(axConstruct, "walk/exits/groups"),
      ok and exitGroupFieldPaths().len >= 8,
      "every exit group of the walk and its frames is named as walked or " &
      "unwalked, and a parked entry's depth is not writable outside exits")
