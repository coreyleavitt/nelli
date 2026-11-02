## RFC-0005 (soundness channels) slice S8bo -- S8be's remainder: the
## threaded replay. An abandoned replay's thread running on while a later
## replay runs, and the replay thread's fidelity to the calling thread (its
## `{.threadvar.}`s, its stack).
##
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is). The interleavings are forced
## by handshakes, not by sleeps: no expectation depends on the load.
import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc drainAbandoned() =
  ## Waits, without a time bound of its own, for every abandoned replay
  ## thread to end: each one below is released by a handshake.
  while replayAbandonedLive() > 0: sleep(1)

# ---- (6) an abandoned replay's late write ------------------------------------
#
# WRONG VERDICT before S8bo: a replay abandoned past `replayTimeoutMs` kept
# running, and a later replay ran concurrently with it. Here the first
# replay (of `sutLateWriter`) blocks until the second (of `sutLateReader`)
# releases it, writes `s8boFlag`, and only then lets the second go on: the
# second read the abandoned replay's write and confirmed a hit no
# single-threaded run of `sutLateReader` makes (the test leaves the flag at
# 0, and nothing but the abandoned thread writes it). A replay that starts
# while an abandoned one still runs is now neither confirmed nor refuted
# (`feReplayTimedOut`).

var s8boFlag = 0
var s8boGo, s8boDone: Channel[int]
s8boGo.open()
s8boDone.open()

proc s8boWaitThenWrite(v: int) {.symexOpaque.} =
  discard s8boGo.recv()
  s8boFlag = 1
  s8boDone.send(1)

proc sutLateWriter(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8boWaitThenWrite(v)
  symexTarget("w")

proc s8boRelease(v: int) {.symexOpaque.} =
  s8boGo.send(1)
  discard s8boDone.recv()

proc sutLateReader(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8boRelease(v)
  if s8boFlag == 1: symexTarget("late")

# ---- (7) the calling thread's `{.threadvar.}`s ---------------------------------
#
# WRONG VERDICT before S8bo (a refuted candidate, `sxUnknown`, where the
# real call reaches the target): the replay ran on a thread of its own,
# where `s8boTv` starts at 0, not at the calling thread's 7. The replay now
# runs with the calling thread's values of the thread variables the routine
# may reach, and hands its writes back.

var s8boTv {.threadvar.}: int
var s8boTvCount {.threadvar.}: int

proc sutTv(v: int) =
  symexAssume(v >= 0 and v < 10)
  if s8boTv == 7 and v == 3: symexTarget("tv")

proc s8boTvBump() =
  s8boTvCount += 1

proc sutTvWrite(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8boTvBump()
  if s8boTv == 7 and v == 4: symexTarget("tvw")

# ---- (7) the calling thread's stack ------------------------------------------
#
# CRASH before S8bo: the replay thread had Nim's 2 MiB thread stack, so a
# routine whose frame holds 3 MiB -- which runs on the calling thread
# (Linux: 8 MiB) -- overflowed it and killed the process. The replay now
# runs on a stack the calling thread's size.

var s8boBig = 0

proc s8boBigFrame(v: int) {.symexOpaque.} =
  var buf: array[3 shl 20, byte]
  buf[v and 1023] = 1
  s8boBig = int(buf[v and 1023]) + int(buf[(v + 1) and 1023])

proc sutBigFrame(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8boBigFrame(v)
  if s8boBig == 1: symexTarget("big")

suite "RFC-0005 S8bo: walker version":
  test "symexWalkerVersion is at least 216":
    check parseInt(symexWalkerVersion) >= 216

suite "RFC-0005 S8bo (6): an abandoned replay's late write":
  test "a replay started while an abandoned one runs is not confirmed":
    s8boFlag = 0
    let a = symexFind(sutLateWriter, tLabel("w"),
                      SymexSettings(replayTimeoutMs: 200))
    checkpoint "writer " & $a.status & " " & show(a.errors)
    check a.status != sxSat
    check a.errors.hasKind(feReplayTimedOut)
    let b = symexFind(sutLateReader, tLabel("late"))
    checkpoint "reader " & $b.status & " " & show(b.errors)
    check b.status != sxSat
    check b.errors.hasKind(feReplayTimedOut)
    check "still running" in show(b.errors)
    drainAbandoned()
  test "once the abandoned replay has ended, a replay confirms again":
    drainAbandoned()
    s8boFlag = 1
    s8boDone.send(1)      # `s8boRelease`'s handshake, answered in advance
    let c = symexFind(sutLateReader, tLabel("late"))
    checkpoint "reader " & $c.status & " " & show(c.errors)
    check c.status == sxSat
    discard s8boGo.tryRecv()

suite "RFC-0005 S8bo (7): the calling thread's `{.threadvar.}`s":
  test "the replay reads the calling thread's value":
    s8boTv = 7
    let r = symexFind(sutTv, tLabel("tv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
  test "the replay's writes are the calling thread's":
    s8boTv = 7
    s8boTvCount = 0
    let r = symexFind(sutTvWrite, tLabel("tvw"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check s8boTvCount == 1

suite "RFC-0005 S8bo (7): the calling thread's stack":
  test "a frame the calling thread holds does not overflow the replay":
    if replayStackSize() < 6 shl 20:
      skip()
    else:
      let r = symexFind(sutBigFrame, tLabel("big"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
