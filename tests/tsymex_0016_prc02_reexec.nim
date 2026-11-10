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
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/replayproc
from nelli/smt/runtime import hostAdmission
import ./s8cu_helpers except show
import helpers/prc03_sut     # imports an override module this file cannot see
import helpers/r8_hooked     # W3-z R8: a closure environment with a hook

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
    # A symexFind run is decided only on a verified build row, and the Z3 4.13.4 row is Linux c alone (`rowOf`,
    # buildprofile.nim), so cpp under 4.13.4 is `feHostUnadmitted` by design.
    # Not a defect: `replayWitness` does not read the row.
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      let r = symexFind(sutNimcall, tLabel("t"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed
      # RFC-0016 W3-z R7. The opaque body calls through `gNimcall`, which may
      # hold any routine of its type (one with `overflowChecks: off`
      # included), so the walk carries "may be undefined" for the call
      # (W3-z R3). The replayed run is concrete: the global held `dbl` when it
      # started, no code the run executes writes it, and `dbl` is checked, so
      # the call ran no undefined behaviour and the confirmed sxSat is exact.
      discard pinExact(sutNimcall, cellKey(faCallShape, "reexec/procValueGlobal"),
                       tLabel("t"))

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

# ---- RFC-0016 W3-z R7: the callee a replayed run executed ---------------------

{.push overflowChecks: off.}
proc ovfAdd(x: int): int = x + (high(int) - 2)   # unchecked: undefined past high
{.pop.}

var gOvf: proc (v: int): int {.nimcall.} = ovfAdd
proc runOvf(v: int) {.symexOpaque.} =
  gOut = gOvf(v)                  # the opaque body names no routine
proc sutOvf(v: int) =
  symexAssume(v == 3)
  if v == 99: gOut = ovfAdd(v)    # names it (the replay's routine table)
  runOvf(v)
  if gOut < 0: symexTarget("t")

var gClosR7: proc (v: int): int = dbl
proc runClosR7(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOut = gClosR7(v)
proc sutClosR7(v: int) =
  symexAssume(v == 3)
  runClosR7(v)
  if gOut == 6: symexTarget("t")

var gEnvR7: proc (v: int): int
proc runEnvR7(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOut = gEnvR7(v)
proc sutEnvR7(v: int) =
  symexAssume(v == 3)
  runEnvR7(v)
  if gOut == 8: symexTarget("t")
proc mkEnvR7() =
  var n = 5
  gEnvR7 = proc (v: int): int = v + n

var gNilR7: proc (v: int): int {.nimcall.}
proc runNilR7(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOut = gNilR7(v)
proc sutNilR7(v: int) =
  symexAssume(v == 3)
  runNilR7(v)
  if gOut == 6: symexTarget("t")

var gRe: proc (v: int): int {.nimcall.} = dbl
proc runRe(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gRe = ovfAdd                    # reassigned during the run, before the call
  gOut = gRe(v)
proc sutRe(v: int) =
  symexAssume(v == 3)
  runRe(v)
  if gOut < 0: symexTarget("t")

# ---- RFC-0016 W3-z R8 ------------------------------------------------------

var gCapRun: proc (v: int): int
proc runCapRun(v: int) {.symexOpaque.} =
  var n = 5
  gCapRun = proc (w: int): int = w + n   # a checked closure, an int captured
  gOut = gCapRun(v)
proc sutCapRun(v: int) =
  symexAssume(v == 3)
  runCapRun(v)
  if gOut == 8: symexTarget("t")

var gCapHook: proc (v: int): int
proc runCapHook(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOut = gCapHook(v)
proc sutCapHook(v: int) =
  symexAssume(v == 3)
  runCapHook(v)
  if gOut == 4: symexTarget("t")
proc mkCapHook() =
  gCapHook = mkHooked()           # dropping the environment runs a hook

var gOrdA: proc (v: int): int {.nimcall.} = ovfAdd
proc runOrdA(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOrdA = dbl                     # the unchecked start value is replaced
  gOut = gOrdA(v)                 # before the only call
proc sutOrdA(v: int) =
  symexAssume(v == 3)
  if v == 98: gOut = ovfAdd(v)
  runOrdA(v)
  if gOut == 6: symexTarget("t")

var gOrdB: proc (v: int): int {.nimcall.} = dbl
proc runOrdB(v: int) {.symexOpaque.} =
  if v == 99: discard dbl(v)
  gOut = gOrdB(v)                 # the call runs the start value
  gOrdB = ovfAdd                  # the unchecked one is stored after it
proc sutOrdB(v: int) =
  symexAssume(v == 3)
  runOrdB(v)
  if gOut == 6: symexTarget("t")

suite "W3-z R7: the replayed run's proc-value callee":
  test "an overflowChecks: off routine in the global stays undefined":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      let r = symexFind(sutOvf, tLabel("t"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed
      # The run held `ovfAdd`, whose add is undefined past `high(int)`.
      pinUndefined(sutOvf, cellKey(faCallShape, "reexec/procValueGlobalUnchecked"),
                   UbKind(ubSignedOverflow), tLabel("t"))

  test "a closure-typed global holding a routine with no environment":
    # RFC-0016 W3-z R8 (a). The route scan reads a module-level closure
    # variable as a hypothesis (`closureRouteGuard`): what it holds when the
    # run starts has no environment, so dropping it runs no hook, and the
    # read past the call stands. The replay names `dbl`, which is checked.
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      discard pinExact(sutClosR7, cellKey(faCallShape,
                       "reexec/procValueClosureGlobal"), tLabel("t"))

  test "a closure with a captured environment is not cleared":
    mkEnvR7()
    let r = symexFind(sutEnvR7, tLabel("t"))
    gEnvR7 = nil
    checkpoint show(r.errors)
    check not r.trusted

  test "a nil proc value: the call does not return, nothing is cleared":
    let r = symexFind(sutNilR7, tLabel("t"))
    checkpoint show(r.errors)
    check not r.trusted

  test "a proc value reassigned during the run before the call":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      # It held `dbl` when the run started, but the run itself wrote
      # `ovfAdd` into it before the call: the start value is not the callee.
      pinUndefined(sutRe, cellKey(faCallShape, "reexec/procValueReassigned"),
                   UbKind(ubSignedOverflow), tLabel("t"))

  test "the walker's version floor (R7)":
    check parseInt(symexWalkerVersion) >= 344

suite "W3-z R8: a closure global, and the routine a variable holds at its call":
  test "the walker's version floor (R8)":
    check parseInt(symexWalkerVersion) >= 345

  test "a closure with a captured int, built by the run":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      discard pinExact(sutCapRun, cellKey(faCallShape,
                       "reexec/procValueClosureEnv"), tLabel("t"))

  test "a closure whose captured environment runs a hook stays untrusted":
    mkCapHook()
    let r = symexFind(sutCapHook, tLabel("t"))
    gCapHook = nil
    checkpoint show(r.errors)
    check not r.trusted
    # Dropping the environment runs the destructor of `HookedCap`, which the scan
    # never read: the route stays open, and the decline names the variable.
    check r.errors.named(feGlobalRouteUnproved)
    var named = false
    for e in r.errors:
      if e.kind == feGlobalRouteUnproved and "`gCapHook`" in e.msg and
         "environment" in e.msg:
        named = true
    check named

  test "unchecked when the run starts, checked at the call":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      discard pinExact(sutOrdA, cellKey(faCallShape,
                       "reexec/procValueOrderStoredFirst"), tLabel("t"))

  test "checked at the call, unchecked stored after it":
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      discard pinExact(sutOrdB, cellKey(faCallShape,
                       "reexec/procValueOrderStoredAfter"), tLabel("t"))

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
    check parseInt(symexWalkerVersion) >= 310

suite "borrowed and system routines":
  test "borrowed and system operators compile and replay":
    let r = replayWitness(sutBorrow, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome == roConfirmed

  test "a proc value naming a system routine compiles and declines or replays":
    let r = replayWitness(sutSysProcValue, (3,), tLabel("t"), {})
    checkpoint r.detail
    check r.outcome in {roConfirmed, roDeclined}

