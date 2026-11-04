## RFC-0005 S8ct. What a pin accepts where replay re-executes the binary
## (Windows, and Linux under `-d:nelliReplayReexec`): the outcome a forked
## child gives, or a decline whose message names what the re-executed child
## could not be handed. A forked child copies the whole process, so on Linux
## and macOS these helpers accept only the forked outcome.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/replayproc

export replayForks, replayReexecs

const notMarshallable* = "replay not marshallable"

proc replayedOrNotMarshallable*(got: ReplayResult; want: ReplayOutcome): bool =
  ## `got` is `want`, or (re-exec only) a decline naming why it did not run.
  if got.outcome == want: return true
  when replayReexecs:
    let why = got.detail
    checkpoint "declined: " & why
    got.outcome == roDeclined and notMarshallable in why
  else:
    false

proc declinedNotMarshallable*(errs: seq[SymexErrorInfo]): bool =
  ## A `feReplayDeclined` among `errs` naming what the child could not take.
  for e in errs:
    if e.kind == feReplayDeclined and notMarshallable in e.msg: return true
  false

template decidedOrNotMarshallable*(r, want: untyped): bool =
  ## `r.status` is `want`, or (re-exec only) `sxUnknown` with a decline naming
  ## why the replay that would have decided it did not run.
  when replayReexecs:
    r.status == want or
      (r.status == sxUnknown and declinedNotMarshallable(r.errors))
  else:
    r.status == want
