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
import ./audit_scan_utils
import nelli/smt/replayresult

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

# ---- R6-04: frames are made by their constructors --------------------------
#
# A frame built field by field could leave its exit group at the zero value,
# bound to no clock, and the slip showed only at its first `park`. Each frame
# is now made by `initLoopFrame`/`initCallFrame`/`initCallFrameCtx`, which bind
# the group to the walk's clock. The types live in `walk_types` (RFC-0016
# INT-34 B2), which `runtime` does not re-export, so no module outside the
# runtime family can name them; inside the family, no other construction is
# left.

proc frameConstructions(): seq[string] =
  ## Each `LoopFrame(`/`CallFrame(`/`CallFrameCtx(` construction in the
  ## walker's source (every runtime-family file: the frame types are
  ## `walk_types`'), comments and strings removed, outside the constructors.
  for (f, path) in runtimeFamilySources():
    let code = codeOf(readFile(path)).splitLines
    var inCtor = false
    for i, line in code:
      if line.len > 0 and line[0] notin {' ', '\t'}:
        inCtor = line.startsWith("proc initLoopFrame") or
                 line.startsWith("proc initCallFrame")
      for t in ["LoopFrame(", "CallFrame(", "CallFrameCtx("]:
        var at = line.find(t)
        while at >= 0:
          let prev = if at > 0: line[at - 1] else: ' '
          if prev notin IdentChars and not inCtor:
            result.add f & ":" & $(i + 1) & ": " & line.strip
          at = line.find(t, at + 1)

suite "INT-35 R6-04: frames are built only by their constructors":

  test "no frame is constructed outside its constructor":
    let stray = frameConstructions()
    checkpoint stray.join("\n")
    check stray.len == 0
    check not compiles(LoopFrame())
    check not compiles(CallFrameCtx())
    pinNever(cellKey(axConstruct, "walk/exits/frames"),
      stray.len == 0 and not compiles(LoopFrame()),
      "every walker frame is made by its constructor, which binds its exit " &
      "group to the walk's clock")

suite "INT-35 R5-08: a replay decided without a child leaves no hint":

  test "replayNotRun: no candidate hint, not refused, not run-dependent":
    let r = replayNotRun()
    check r.outcome == roInconclusive
    check candidateHint(r, sxSat, "", "").len == 0
    check candidateHint(r, sxRaised, "E", "").len == 0
    check r.replayStatus != rsRefused
    check not r.endsChild
    check r.runDependence == {}
    # The zero value is a decline (review R3 E1), which does leave one.
    check candidateHint(ReplayResult(), sxSat, "", "").len == 1
