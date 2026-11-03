## RFC-0005 batch 11 -- what a re-executed replay child starts without. A forked
## child (POSIX) copies the host; a re-executed one (Windows, and Linux under
## `-d:nelliReplayReexec`, `tsymex_rfc0005_b11_hoststate_reexec`) is handed the
## variables its footprint names, and runs none of the host's top-level code.
##
## RED before the fix, re-exec only: both rows confirmed a hit (`sxSat`) that the
## real program, run with the host's state, does not reach.
##
## * A lifetime hook of a type no variable holds. `use7(H7(x: k))` builds a
##   temporary the callee consumes; its `=destroy` reads `gArm7`, which the SUT
##   never names, so the child was not handed it and took the other branch. The
##   footprint read only the types of variables; it now reads the types a body
##   names, a call's result type and a routine's signature too.
## * A runtime hook the host installed (`globalRaiseHook`). The child starts
##   without it, and a proc value cannot be marshalled. A replay now declines,
##   naming the hook, while one is set.
##
## Every row checks a native run of the same SUT, in a process of its own.
import std/[unittest, strutils, os, osproc, streams, strtabs, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/replayproc
import nelli/engine/markers
import s8ct_platform

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

var gG: int        # nothing writes it: a hit through it is replayed

# ---- a hook on a type only a temporary has ------------------------------------

var gArm7: int     # the host sets it; only the hook names it
type H7 = object
  x: int
proc `=destroy`(h: H7) =
  let a = [1, 2]
  if a[gArm7 + 1] == 2: discard
proc use7(h: sink H7) = discard
proc sutTemp(k: int) =
  use7(H7(x: k))
  if gG == 0:
    symexTarget("t")

# ---- a `doAssert` in a hook ----------------------------------------------------
#
# Stopped the compile before the fix ("node has no type", S8cs's hook summary
# classifying a formal whose type is inferred from its default); main 6cbfe8f
# compiled it and declined.

var gArm5: int
type H5 = object
  x: int
proc `=destroy`(h: H5) =
  doAssert gArm5 == 0
proc use5(h: sink H5) = discard
proc sutAssert(k: int) =
  use5(H5(x: k))
  if gG == 0:
    symexTarget("t")

# ---- a raise hook the host installed ------------------------------------------

var gBlock: int    # only the host's raise hook writes it
proc sutRaise(k: int) =
  try:
    raise newException(ValueError, "b11")
  except ValueError:
    discard
  if gBlock == 0:
    symexTarget("t")

proc blockOnRaise(e: ref Exception): bool {.nimcall, gcsafe.} =
  if e.msg == "b11":
    {.cast(gcsafe).}:
      gBlock = 1
  true

proc hostState() =
  gArm7 = 1
  gArm5 = 1
  globalRaiseHook = blockOnRaise

# ---- native runs --------------------------------------------------------------

if existsEnv("B11_NATIVE"):
  hostState()
  symexCaptureBegin()
  try:
    case getEnv("B11_NATIVE")
    of "sutTemp": sutTemp(0)
    of "sutRaise": sutRaise(0)
    of "sutAssert": sutAssert(0)
    else: discard
  except Defect as e:
    echo "RAISED|", e.name
  if "t" in symexCaptureEnd(): echo "HIT|t"
  quit(0)

proc nativeHit(row: string): bool =
  var env = newStringTable(modeCaseSensitive)
  for name, value in envPairs(): env[name] = value
  env["B11_NATIVE"] = row
  let p = startProcess(getAppFilename(), env = env, options = {poStdErrToStdOut})
  let output = p.outputStream.readAll()
  discard p.waitForExit(30_000)
  p.close()
  checkpoint row & " natively: " & output
  "HIT|t" in output.splitLines()

suite "batch 11: host state a re-executed replay child does not have":
  test "a hook on a temporary's type: no confirmation native would not reach":
    check not nativeHit("sutTemp")
    gArm7 = 1
    let r = symexFind(sutTemp, tLabel("t"))
    gArm7 = 0
    checkpoint show(r.errors)
    check r.status == sxUnknown
    when replayReexecs:
      check declinedNotMarshallable(r.errors)
      check "`H7`, a type whose module declares a hook" in show(r.errors)
    else:
      check "feReplayRefuted" in show(r.errors)

  test "a raise hook the host set: no confirmation native would not reach":
    check not nativeHit("sutRaise")
    globalRaiseHook = blockOnRaise
    let r = symexFind(sutRaise, tLabel("t"))
    globalRaiseHook = nil
    gBlock = 0
    checkpoint show(r.errors)
    check r.status == sxUnknown
    when replayReexecs:
      check declinedNotMarshallable(r.errors)
      check "`globalRaiseHook`, a runtime hook the host set" in show(r.errors)
    else:
      check "feReplayRefuted" in show(r.errors)

  test "no hook set: the same SUT replays on either path":
    let r = symexFind(sutRaise, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed

  test "a doAssert in a hook compiles, and no confirmation native would not reach":
    check not nativeHit("sutAssert")
    gArm5 = 1
    let r = symexFind(sutAssert, tLabel("t"))
    gArm5 = 0
    checkpoint show(r.errors)
    check r.status == sxUnknown
    when replayReexecs:
      check declinedNotMarshallable(r.errors)
    else:
      check "feReplayRefuted" in show(r.errors)

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 264
