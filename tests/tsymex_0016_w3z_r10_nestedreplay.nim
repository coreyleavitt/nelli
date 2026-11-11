## RFC-0016 W3-z R10 follow-up. A replay nested in a routine that a re-executed
## replay parses and scans compiles under the default `--maxLoopIterationsVM`.
## A consumer compiles with the default, so the macro work must fit in it.
##
## Re-execution is Windows' replay; Linux runs it under `-d:nelliReplayReexec`
## (this file's `.nim.cfg`). There, `replayWitness(nestingSut, ...)` parses
## `nestingSut`, whose body holds the inner replay's expansion, and reads the
## footprint of everything that expansion calls. R10 grew the expansion (the
## routine table held in a `{.global.}`, the environment codecs) and took
## `tsymex_rfc0005_s2_replay` past the VM's limit. What made it costly:
## * the table's declaration spelled `seq[pointer]`, which inside a routine
##   is a call of every `[]` in scope (32, the Z3 binding's among them), and
##   both the parse and the footprint read each (`replaywire.RoutineSlots`);
## * the parse asks three whole-call-graph collectors of every routine it
##   parses, each from a fresh guard (now kept per body, `CollectorMemo`);
## * `isStdlibDecl` normalised a whole path per symbol, `isRuntimeCode` built a
##   256-entry skip table per routine, `fileDeclaresHook` searched each module
##   five times, and `replayFootprint` kept its visited routines in a list.
import std/unittest
import nelli/symex
import nelli/smt/types
import s8ct_platform

proc innerSut(x: int) =
  if x == 42:
    symexTarget("inner")

proc nestingSut(x: int) =
  symexTarget("outer")
  doAssert replayWitness(innerSut, (42,), tLabel("inner"), {}).outcome ==
           roConfirmed

suite "W3-z R10: a replay nested in a re-executed one":
  test "compiles, and the outer replay runs or declines naming why":
    check replayedOrNotMarshallable(
      replayWitness(nestingSut, (0,), tLabel("outer"), {}), roConfirmed)
    check replayedOrNotMarshallable(
      replayWitness(nestingSut, (0,), tLabel("inner"), {}), roRefuted)
