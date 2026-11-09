## RFC-0016 PRC-02 (with INT-13). Windows re-exec replay carries proc values,
## routine-local `{.global.}`s and the runtime hooks it used to decline on.
## Windows has no `fork`, so the replay re-executes the binary; Linux runs that
## path under `-d:nelliReplayReexec` (this file's `.nim.cfg`), so every leg
## exercises the marshalling.
##
## * A proc value crosses by identity: the child is this binary, so it is
##   written as the index of the routine in a table both ends build from the
##   routines the replayed code names. A closure with an environment, and a
##   routine the code does not name, decline, saying which.
## * A `{.global.}` of a routine that a nested routine names is the child's own
##   (it runs the declaring routine), as the routine's own use already was.
## * A `method` declines under a stock Nim: the override that runs depends on
##   the receiver's dynamic type and the scan cannot list overrides. Under the
##   in-house toolchain that emits a per-binary dispatch table
##   (`hasMethodTable`, RFC-0016 PRC-02b) the host asks the
##   table which bodies a dispatcher can run: confirmed when the scan read every
##   one, declined (at run time) naming the override that no scan read.
## * A runtime hook naming a routine the replayed code names is reinstalled in
##   the child (INT-13); any other still declines, naming the hook.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/replayproc
import helpers/prc03_sut     # imports an override module this file cannot see

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

var gG: int         # never written: a path past its read is a replay candidate

# ---- proc values -----------------------------------------------------------

proc dbl(x: int): int = x * 2
proc unnamed(x: int): int = x + 100

var gOut: int
var gClos: proc (v: int): int = dbl
var gNimcall: proc (v: int): int {.nimcall.} = dbl
type Ops = object
  f: proc (v: int): int
var gOps = Ops(f: dbl)
var gNil: proc (v: int): int
var gUnnamed: proc (v: int): int = unnamed
var gEnv: proc (v: int): int

proc runClos(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)    # names the routine the global holds
  gOut = gClos(v)
proc sutClos(v: int) =
  symexAssume(v == 3)
  runClos(v)
  if gOut == 6: symexTarget("t")

proc runNimcall(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)    # names the routine the global holds
  gOut = gNimcall(v)
proc sutNimcall(v: int) =
  symexAssume(v == 3)
  runNimcall(v)
  if gOut == 6: symexTarget("t")

proc runField(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)    # names the routine the global holds
  gOut = gOps.f(v)
proc sutField(v: int) =
  symexAssume(v == 3)
  runField(v)
  if gOut == 6: symexTarget("t")

proc sutNil(v: int) =
  if gG == 0 and gNil == nil and v == 3: symexTarget("t")

proc runUnnamed(v: int) {.symexOpaque.} = gOut = gUnnamed(v)
proc sutUnnamed(v: int) =
  symexAssume(v == 3)
  runUnnamed(v)
  if gOut == 103: symexTarget("t")

proc runEnv(v: int) {.symexOpaque.} = gOut = gEnv(v)
proc sutEnv(v: int) =
  symexAssume(v == 3)
  runEnv(v)
  if gOut == 8: symexTarget("t")

proc mkEnv() =
  var n = 5
  gEnv = proc (v: int): int = v + n

# ---- a method --------------------------------------------------------------

type
  Base = ref object of RootObj
  Sub = ref object of Base

method area(x: Base; v: int): int {.base, gcsafe.} = v
method area(x: Sub; v: int): int {.gcsafe.} = v + 1

proc runMethod(v: int) {.symexOpaque.} =
  let b: Base = Sub()
  gOut = area(b, v)         # dispatched on the receiver's dynamic type
proc sutMethod(v: int) =
  symexAssume(v == 3)
  runMethod(v)
  if gOut == 4: symexTarget("t")

# ---- a {.global.} named by a nested routine ----------------------------------

proc nestedGlobal(v: int) =
  var cnt {.global.} = 0
  proc bump() = inc cnt
  bump()
  if gG == 0 and v == 3 and cnt == 1: symexTarget("t")

# ---- runtime hooks ------------------------------------------------------------

var gSeen: int       # only the host's raise hook writes it
proc namedHook(e: ref Exception): bool {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    gSeen = 1
  true

proc unnamedHook(e: ref Exception): bool {.nimcall, gcsafe.} = true

proc sutHook(v: int) =
  try:
    raise newException(ValueError, "prc02")
  except ValueError:
    discard
  if v == 99: discard namedHook(nil)    # names the routine, never run
  if gG == 0 and v == 3 and gSeen == 1: symexTarget("t")

proc sutUnnamedHook(v: int) =
  try:
    raise newException(ValueError, "prc02")
  except ValueError:
    discard
  if gG == 0 and v == 3: symexTarget("t")

suite "PRC-02: proc values cross to the re-executed child":
  test "a closure-typed global naming a routine":
    # The walker leaves a closure-typed store unproved (no SAT path to
    # settle by replay), so the wire is exercised by the direct form.
    let r = replayWitness(sutClos, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a nimcall-typed global":
    let r = symexFind(sutNimcall, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed

  test "a proc held in a field of a global object":
    # The walker leaves a closure-typed store unproved (no SAT path to
    # settle by replay), so the wire is exercised by the direct form.
    let r = replayWitness(sutField, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a nil proc global replays":
    let r = replayWitness(sutNil, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a proc naming a routine the code does not name declines":
    let r = replayWitness(sutUnnamed, (3,), tLabel("t"), {})
    checkpoint r.detail
    when replayReexecs:
      check r.outcome == roDeclined
      check "replay not marshallable" in r.detail
      check "naming no routine the replayed code names" in r.detail
    else:
      check r.outcome == roConfirmed

  test "a closure with a captured environment declines":
    mkEnv()
    let r = replayWitness(sutEnv, (3,), tLabel("t"), {})
    gEnv = nil
    checkpoint r.detail
    when replayReexecs:
      check r.outcome == roDeclined
      check "a closure with a captured environment" in r.detail
    else:
      check r.outcome == roConfirmed

proc runProcCall(v: int) {.symexOpaque.} =
  gOut = procCall area(Sub(), v)   # a static call: no dispatch
proc sutProcCall(v: int) =
  symexAssume(v == 3)
  runProcCall(v)
  if gOut == 4: symexTarget("t")

suite "PRC-02: a method":
  test "a dynamic call over a visible hierarchy":
    let r = replayWitness(sutMethod, (3,), tLabel("t"), {})
    checkpoint r.detail
    when replayReexecs and not hasMethodTable:
      # Stock Nim: the dispatcher's override set cannot be read, so it declines.
      check r.outcome == roDeclined
      check "`area`, a method on `Base`, whose overrides the scan cannot " &
            "list" in r.detail
      check "a module `sutMethod` cannot see" in r.detail
      check "a Linux or macOS run forks and replays it" in r.detail
    else:
      # RFC-0016 PRC-02b: every body the dispatcher can run was scanned, so the
      # replay is confirmed (the toolchain table says which bodies those are).
      check r.outcome == roConfirmed

  test "procCall of a method is a static call: scanned as a plain routine":
    let r = replayWitness(sutProcCall, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "an override in a module the entry cannot see":
    # The dispatcher runs `Sub`'s override although this file never imports
    # its module; only a fork (which copies the process) reproduces it.
    let r = replayWitness(sutHidden, (3,), tLabel("t"), {})
    checkpoint r.detail
    when replayReexecs and not hasMethodTable:
      check r.outcome == roDeclined
      check "whose overrides the scan cannot list" in r.detail
    elif replayReexecs:
      # RFC-0016 PRC-02b: the table lists the override no scan read, and the
      # decline names it. The run is not run-dependent.
      check r.outcome == roDeclined
      check "an override of `area` for `Sub` the entry could not see" in
            r.detail
    else:
      check r.outcome == roConfirmed

suite "PRC-02: a routine's {.global.}":
  test "named by a routine nested in the one that declares it":
    let r = replayWitness(nestedGlobal, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

# ---- borrowed and system operators in the footprint ------------------------------
# A `{.borrow.}` routine (and the system `==`/`<`/`+` it forwards to) has no body
# whose address the table can take; it must be left out, not crash the build.

type Dist = distinct int
proc `==`(a, b: Dist): bool {.borrow.}
proc `<`(a, b: Dist): bool {.borrow.}
proc `+`(a, b: Dist): Dist {.borrow.}

var gSysOp: proc (c: char): char = strutils.toLowerAscii

proc sutBorrow(v: int) =
  symexAssume(v == 3)
  let a = Dist(v)
  if a + Dist(1) == Dist(4) and a < Dist(10) and v + 1 < 5 and v == 3 and
     gG == 0:
    symexTarget("t")

proc sutSysProcValue(v: int) =
  symexAssume(v == 3)
  if gSysOp('A') == 'a' and gG == 0: symexTarget("t")

suite "INT-13: runtime hooks":
  test "a hook naming a routine the code names is reinstalled":
    globalRaiseHook = namedHook
    gSeen = 0
    let r = replayWitness(sutHook, (3,), tLabel("t"), {})
    globalRaiseHook = nil
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a hook naming another routine declines, naming the hook":
    globalRaiseHook = unnamedHook
    let r = replayWitness(sutUnnamedHook, (3,), tLabel("t"), {})
    globalRaiseHook = nil
    checkpoint r.detail
    when replayReexecs:
      check r.outcome == roDeclined
      check "`globalRaiseHook`, a runtime hook the host set" in r.detail
    else:
      check r.outcome == roConfirmed

  test "no hook set replays":
    let r = replayWitness(sutUnnamedHook, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 308

suite "borrowed and system routines":
  test "borrowed and system operators compile and replay":
    let r = replayWitness(sutBorrow, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a proc value naming a system routine compiles and declines or replays":
    let r = replayWitness(sutSysProcValue, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome in {roConfirmed, roDeclined}

