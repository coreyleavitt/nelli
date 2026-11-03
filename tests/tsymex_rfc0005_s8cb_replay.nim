## RFC-0005 (soundness channels) slice S8cb -- the replay's remainder:
## (6) a replay started from a thread with a stack of its own runs on one of
## that size, and (7) one abandoned never-ending replay leaves later replays
## alone unless they may share state with it.
##
## Item 7's replays never end, so no test drains them: the process's exit ends
## their threads. They block on a channel, and take no CPU from the rest of the
## run.
import std/[unittest, strutils, random]
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

# ---- (6) a thread Nim did not start ------------------------------------------
#
# CRASH before S8cb: a thread other than the main one was taken to have Nim's
# 2 MiB stack, whatever it had. A routine whose frame holds 3 MiB, run from a
# 16 MiB thread (which runs it directly), overflowed the replay's stack and
# killed the process.

var s8cbBig = 0

proc s8cbBigFrame(v: int) =
  var buf: array[3 shl 20, byte]
  buf[v and 1023] = 1
  s8cbBig = int(buf[v and 1023]) + int(buf[(v + 1) and 1023])

when defined(linux) and compileOption("threads"):
  import std/posix

  type ForeignResult = object
    size: int
    run: ReplayRun
    big: int

  var foreignOut: ForeignResult
  proc pthreadCreateRaw(t: ptr Pthread; a: ptr Pthread_attr;
                        fn: proc (x: pointer): pointer {.noconv.};
                        arg: pointer): cint
    {.importc: "pthread_create", header: "<pthread.h>".}

  proc foreignBody() =
    {.cast(gcsafe).}:
      foreignOut.size = replayStackSize()
      foreignOut.run = runReplayBounded(proc () {.closure, gcsafe.} =
        {.cast(gcsafe).}:
          s8cbBigFrame(3), 30_000)
      foreignOut.big = s8cbBig

  proc foreignMain(x: pointer): pointer {.noconv.} =
    # Before anything allocates: its own frame must not.
    setupForeignThreadGc()
    foreignBody()

  proc onForeignThread(stack: int) =
    var a: Pthread_attr
    doAssert pthread_attr_init(addr a) == 0
    doAssert pthread_attr_setstacksize(addr a, stack) == 0
    var t: Pthread
    doAssert pthreadCreateRaw(addr t, addr a, foreignMain, nil) == 0
    discard pthread_join(t, nil)
    discard pthread_attr_destroy(addr a)

  proc nimThreadSize(x: ptr int) {.thread.} =
    x[] = replayStackSize()

# ---- (7) a never-ending replay -----------------------------------------------
#
# RED before S8cb: a replay that never ends left every later replay of the
# process `roContended` (`sxUnknown`), whatever it ran. A replay now contends
# only with what it may share.

var s8cbHangCount = 0
var s8cbOnlyForLater = 0
var s8cbNever, s8cbNever2: Channel[int]
s8cbNever.open()
s8cbNever2.open()

proc s8cbHangForever(v: int) {.symexOpaque.} =
  discard s8cbNever.recv()

proc sutHang(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8cbHangForever(v)
  symexTarget("h")

proc s8cbHangWriting(v: int) {.symexOpaque.} =
  s8cbHangCount += 1
  discard s8cbNever2.recv()

proc sutHangWriting(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8cbHangWriting(v)
  symexTarget("h")

var s8cbNever3: Channel[int]
s8cbNever3.open()

proc s8cbHangRandom(v: int) {.symexOpaque.} =
  discard rand(10)
  discard s8cbNever3.recv()

proc sutHangRandom(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8cbHangRandom(v)
  symexTarget("h")

proc s8cbRandom(v: int) {.symexOpaque.} =
  discard rand(5)

proc sutRandom(v: int) =
  symexAssume(v == 3)
  s8cbRandom(v)
  symexTarget("r")

proc sutDisjoint(v: int) =
  if v == 3: symexTarget("d")

proc s8cbLater(v: int) {.symexOpaque.} =
  s8cbOnlyForLater += v

proc sutDisjointGlobal(v: int) =
  symexAssume(v == 3)
  s8cbLater(v)
  symexTarget("dg")

proc s8cbReadCount(v: int) {.symexOpaque.} =
  s8cbHangCount += 1

proc sutSharing(v: int) =
  symexAssume(v == 3)
  s8cbReadCount(v)
  symexTarget("s")

proc s8cbDeep(v: int) {.symexOpaque.} = s8cbReadCount(v)

proc s8cbDeeper(v: int) {.symexOpaque.} = s8cbDeep(v)

proc sutSharingDeep(v: int) =
  symexAssume(v == 3)
  s8cbDeeper(v)
  symexTarget("sd")

var s8cbHook: proc (v: int): int {.nimcall.} = nil

proc s8cbCallHook(v: int) {.symexOpaque.} =
  if s8cbHook != nil: discard s8cbHook(v)

proc sutProcValue(v: int) =
  symexAssume(v == 3)
  s8cbCallHook(v)
  symexTarget("pv")

type
  S8cbBase = ref object of RootObj
  S8cbSub = ref object of S8cbBase

method s8cbM(x: S8cbBase; v: int): int {.base, gcsafe.} = v
method s8cbM(x: S8cbSub; v: int): int {.gcsafe.} = v + 1

proc s8cbCallMethod(v: int) {.symexOpaque.} = discard s8cbM(S8cbSub(), v)

proc sutMethod(v: int) =
  symexAssume(v == 3)
  s8cbCallMethod(v)
  symexTarget("m")

proc s8cbForeignRand(): cint {.importc: "rand", header: "<stdlib.h>".}

proc s8cbCallForeign(v: int) {.symexOpaque.} = discard s8cbForeignRand()

proc sutForeign(v: int) =
  symexAssume(v == 3)
  s8cbCallForeign(v)
  symexTarget("f")

# ---- a thread variable behind a routine of the same signature ----------------
#
# REFUTED before S8cb: `threadvarsReached` keyed its scan by `signatureHash`,
# which is the same for every routine of a module with the same parameter
# types, so it never read `s8cbTvLook`, as it has the signature of `sutTvBehind`.

var s8cbTv {.threadvar.}: int
var s8cbTvOut = 0

proc s8cbTvLook(v: int) {.symexOpaque.} =
  s8cbTvOut = s8cbTv

proc sutTvBehind(v: int) =
  symexAssume(v == 3)
  s8cbTvLook(v)
  if s8cbTvOut == 7: symexTarget("tv")

suite "RFC-0005 S8cb: walker version":
  test "symexWalkerVersion is at least 243":
    check parseInt(symexWalkerVersion) >= 243

when defined(linux) and compileOption("threads"):
  suite "RFC-0005 S8cb (6): the replay's stack on a thread of any size":
    test "a thread Nim did not start":
      onForeignThread(16 shl 20)
      check foreignOut.size >= (15 shl 20)
      check foreignOut.size <= (17 shl 20)
      check foreignOut.run == rrEnded
      check foreignOut.big == 1
    test "and a Nim thread keeps its own":
      var th: Thread[ptr int]
      var size = 0
      createThread(th, nimThreadSize, addr size)
      joinThread(th)
      check size >= (1 shl 20)
      check size <= (3 shl 20)
    test "the main thread keeps RLIMIT_STACK":
      var rl: RLimit
      check getrlimit(RLIMIT_STACK, rl) == 0
      if int(rl.rlim_cur) > 0 and int(rl.rlim_cur) <= (256 shl 20):
        check replayStackSize() == int(rl.rlim_cur)

suite "RFC-0005 S8cb: the thread variables a replay carries":
  test "named behind a routine of the same signature":
    s8cbTv = 7
    let r = symexFind(sutTvBehind, tLabel("tv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

when compileOption("threads"):
  suite "RFC-0005 S8cb (7): a never-ending replay":
    test "it is abandoned":
      let r = symexFind(sutHang, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check r.errors.hasKind(feReplayTimedOut)
      check replayAbandonedLive() >= 1
    test "a later replay of unrelated code proceeds":
      let r = symexFind(sutDisjoint, tLabel("d"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
      check not r.errors.hasKind(feReplayTimedOut)
    test "and of code with a global of its own":
      let r = symexFind(sutDisjointGlobal, tLabel("dg"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
      check not r.errors.hasKind(feReplayTimedOut)
    test "a second never-ending replay":
      let r = symexFind(sutHangWriting, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check r.errors.hasKind(feReplayTimedOut)
      check replayAbandonedLive() >= 2
    test "still leaves unrelated code alone":
      let r = symexFind(sutDisjointGlobal, tLabel("dg"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
    test "but a replay reading what it writes stays contended":
      let r = symexFind(sutSharing, tLabel("s"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check r.errors.hasKind(feReplayTimedOut)
      check "still running" in show(r.errors)
    test "through any depth of calls":
      let r = symexFind(sutSharingDeep, tLabel("sd"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "and through the stdlib's own state":
      let h = symexFind(sutHangRandom, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      check h.errors.hasKind(feReplayTimedOut)
      let r = symexFind(sutRandom, tLabel("r"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "a call through a proc value may share anything":
      let r = symexFind(sutProcValue, tLabel("pv"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "as may a method":
      let r = symexFind(sutMethod, tLabel("m"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "and a foreign routine":
      let r = symexFind(sutForeign, tLabel("f"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "a caller not naming a footprint is contended":
      let r = runReplayBounded(proc () {.closure, gcsafe.} = discard, 5000)
      check r == rrContended
    test "nor does a disjoint footprint":
      let r = runReplayBounded(proc () {.closure, gcsafe.} = discard, 5000,
                               ReplayFootprint(tokens: @["nothing-shared"]))
      check r == rrEnded
