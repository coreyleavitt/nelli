## RFC-0005 S8cp, item 1: what a replay's footprint could not see. An abandoned
## replay contended a later one only if the scan of the two routines' typed ASTs
## found a name in common, and three ways of sharing state name nothing there: a
## C routine of the stdlib, a hook the runtime calls through a variable the
## program set, and a hook the compiler inserts. Each one here is the same shape:
## a replay that never ends leaves its mark first, and a later replay's label is
## reachable only through that mark. No program run without the abandoned thread
## reaches it (the native test), so sxSat there is false; a contended replay
## reports sxUnknown.
##
## Each suite releases its hanging replay and waits for it to end: a replay of an
## open footprint left running would contend every later replay of the process,
## and every pin after it would hold for that reason alone.
import std/[unittest, strutils, os, envvars, math]
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

const envName = "NELLI_S8CP_FOOTPRINT"

# ---- state behind two different C routines ---------------------------------

var neverC: Channel[int]
neverC.open()

proc hangSetEnv(v: int) {.symexOpaque.} =
  putEnv(envName, "1")
  discard neverC.recv()

proc sutHangSetEnv(v: int) =
  symexAssume(v >= 0 and v < 10)
  hangSetEnv(v)
  symexTarget("h")

var envOut = 0

proc readsEnv(v: int) {.symexOpaque.} =
  envOut = getEnv(envName).len

proc sutReadsEnv(v: int) =
  symexAssume(v == 3)
  readsEnv(v)
  if envOut == 1: symexTarget("e")

var sqrtOut = 0.0

proc pureSqrt(v: int) {.symexOpaque.} =
  sqrtOut = sqrt(float(v))

proc sutPureForeign(v: int) =
  symexAssume(v == 3)
  pureSqrt(v)
  symexTarget("p")

# ---- a runtime hook variable the program sets ------------------------------

var neverH: Channel[int]
neverH.open()
var hookMark = 0

proc markingRaiseHook(e: ref Exception): bool {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    hookMark = 7
  true

proc hangRaising(v: int) {.symexOpaque.} =
  try:
    raise newException(ValueError, "x")
  except ValueError:
    discard
  discard neverH.recv()

proc sutHangRaising(v: int) =
  symexAssume(v >= 0 and v < 10)
  hangRaising(v)
  symexTarget("h")

var neverP: Channel[int]
neverP.open()

proc hangPlain(v: int) {.symexOpaque.} =
  discard neverP.recv()

proc sutHangPlain(v: int) =
  symexAssume(v >= 0 and v < 10)
  hangPlain(v)
  symexTarget("h")

var hookOut = 0

proc readsHookMark(v: int) {.symexOpaque.} =
  hookOut = hookMark

proc sutReadsHookMark(v: int) =
  symexAssume(v == 3)
  readsHookMark(v)
  if hookOut == 7: symexTarget("hm")

# ---- a hook the compiler inserts --------------------------------------------

var neverD: Channel[int]
neverD.open()
var destroyMark = 0

type Marks = object
  v: int

proc `=destroy`(m: Marks) =
  {.cast(gcsafe).}:
    destroyMark = 7
    discard neverD.recv()

proc hangDestroying(v: int) {.symexOpaque.} =
  var m = Marks(v: v)
  m.v = v + 1

proc sutHangDestroying(v: int) =
  symexAssume(v >= 0 and v < 10)
  hangDestroying(v)
  symexTarget("h")

type Box = tuple[a: int, ms: seq[Marks]]

var boxOut = 0

proc hangBoxed(v: int) {.symexOpaque.} =
  var b: Box
  b.a = v
  b.ms.setLen(1)
  boxOut = v

proc sutHangBoxed(v: int) =
  symexAssume(v >= 0 and v < 10)
  hangBoxed(v)
  if boxOut == v: symexTarget("h")

var destroyOut = 0

proc readsDestroyMark(v: int) {.symexOpaque.} =
  destroyOut = destroyMark

proc sutReadsDestroyMark(v: int) =
  symexAssume(v == 3)
  readsDestroyMark(v)
  if destroyOut == 7: symexTarget("dm")

suite "RFC-0005 S8cp (1): native":
  test "no label of a reader is reached with no abandoned thread":
    symexCaptureBegin()
    sutReadsEnv(3)
    sutReadsHookMark(3)
    sutReadsDestroyMark(3)
    let hits = symexCaptureEnd()
    checkpoint $hits
    check hits.len == 0
  test "the raise hook writes its mark, and the environment starts without one":
    check getEnv(envName).len == 0
    let prior = globalRaiseHook
    globalRaiseHook = markingRaiseHook
    try:
      raise newException(ValueError, "x")
    except ValueError:
      discard
    globalRaiseHook = prior
    check hookMark == 7
    hookMark = 0

proc released(c: var Channel[int]): bool =
  ## The hanging replays have ended and been reaped, so none of them contends a
  ## later suite's replay. One find may have abandoned several.
  for _ in 0 ..< 500:
    if replayAbandonedLive() == 0:
      # A send past the last receive would leave the next hanger no reason to hang.
      while c.tryRecv().dataAvailable: discard
      return true
    c.send(1)
    sleep(10)
  false

when compileOption("threads"):
  suite "RFC-0005 S8cp (1): state behind two C routines":
    test "the hanging replay is abandoned":
      let r = symexFind(sutHangSetEnv, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      checkpoint $r.status & " " & show(r.errors)
      check r.errors.hasKind(feReplayTimedOut)
      check replayAbandonedLive() >= 1
    test "a replay through another C routine stays contended":
      let r = symexFind(sutReadsEnv, tLabel("e"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "a known-pure C routine is not":
      let r = symexFind(sutPureForeign, tLabel("p"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
    test "released":
      check released(neverC)

  suite "RFC-0005 S8cp (1): a runtime hook variable the program sets":
    test "the hanging replay is abandoned with the hook set":
      globalRaiseHook = markingRaiseHook
      let r = symexFind(sutHangRaising, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      globalRaiseHook = nil
      checkpoint $r.status & " " & show(r.errors)
      check r.errors.hasKind(feReplayTimedOut)
    test "what its hook wrote contends a replay naming the mark":
      let r = symexFind(sutReadsHookMark, tLabel("hm"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "released":
      check released(neverH)
      hookMark = 0
    test "a hook set when the later replay starts contends it":
      globalRaiseHook = markingRaiseHook
      let hung = symexFind(sutHangPlain, tLabel("h"),
                           SymexSettings(replayTimeoutMs: 100))
      checkpoint $hung.status & " " & show(hung.errors)
      check hung.errors.hasKind(feReplayTimedOut)
      let r = symexFind(sutReadsHookMark, tLabel("hm"))
      globalRaiseHook = nil
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
      check released(neverP)

  suite "RFC-0005 S8cp (1): a hook the compiler inserts":
    test "the hanging replay is abandoned in its destructor":
      let r = symexFind(sutHangDestroying, tLabel("h"),
                        SymexSettings(replayTimeoutMs: 100))
      checkpoint $r.status & " " & show(r.errors)
      check r.errors.hasKind(feReplayTimedOut)
    test "what the destructor wrote contends a replay naming the mark":
      let r = symexFind(sutReadsDestroyMark, tLabel("dm"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
    test "released":
      check released(neverD)
      destroyMark = 0
    test "a hook no name in the body leads to: the type behind a tuple's seq":
      let hung = symexFind(sutHangBoxed, tLabel("h"),
                           SymexSettings(replayTimeoutMs: 100))
      checkpoint $hung.status & " " & show(hung.errors)
      check hung.errors.hasKind(feReplayTimedOut)
      let r = symexFind(sutReadsDestroyMark, tLabel("dm"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
      check "still running" in show(r.errors)
      check released(neverD)
      destroyMark = 0

  suite "RFC-0005 S8cp (1): a footprint that stays narrow":
    test "a replay of plain ints is not contended by one of its own kind":
      let hung = symexFind(sutHangPlain, tLabel("h"),
                           SymexSettings(replayTimeoutMs: 100))
      checkpoint $hung.status & " " & show(hung.errors)
      check hung.errors.hasKind(feReplayTimedOut)
      let r = symexFind(sutPureForeign, tLabel("p"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxSat
      check released(neverP)

  suite "RFC-0005 S8cp (1): walker version":
    test "symexWalkerVersion is at least 253":
      check parseInt(symexWalkerVersion) >= 253
