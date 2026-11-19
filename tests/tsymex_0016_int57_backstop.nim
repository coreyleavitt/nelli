## RFC-0016 INT-57 (A): the solver stall backstop. A step bound ends a search
## only while Z3 advances its step counter, and Z3 can stop advancing it; the
## pin settings run with no wall clock (`queryTimeoutMs = 0`) so a loaded
## machine cannot turn a pin into a decline, and under them a stalled query
## never returned (`tests/tsymex_0016_int57_strlenstall.nim`, killed at
## 900 s). With no run clock, every step-bounded solve now runs under the
## stall backstop (`stallBackstopMs`), which this file's `.nim.cfg` lowers to
## 2 s so a query Z3 does not answer that fast stands in for one that stalls.
##
## What the backstop must give: the walk returns; the cut solve is a decline
## (`sxUnknown`, untrusted), never a verdict; its error names the backstop,
## not the run clock; and the run is marked run-dependent (`rdQueryTimeout`),
## so its verdict is not cached. A query the step bound decides first keeps
## its exact verdict.
import std/[unittest, strutils, times]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
from ./s8cu_helpers import pinFind

proc sutCubes(x, y, z: int) =
  ## S8bu's cubes query: Z3 does not answer it in 2 s.
  if x > 0 and y > 0 and z > 0 and x < 1000 and y < 1000 and z < 1000:
    if x * x * x + y * y * y == z * z * z: symexTarget("tc")

proc sutManyCubes(x, y, z, w: int) =
  ## Four solves, each one Z3 does not answer in 2 s: a per-solve backstop
  ## would let the walk run four backstops (and a loop of them, without
  ## end); the run's deadline ends it within one.
  if x > 0 and y > 0 and z > 0 and x < 1000 and y < 1000 and z < 1000:
    if x * x * x + y * y * y == z * z * z: symexTarget("tc")
    if w > 0 and w < 1000 and x * x * x + y * y * y == w * w * w:
      symexTarget("tc")
    if x * x * x + z * z * z == y * y * y: symexTarget("tc")
    if y * y * y + z * z * z == x * x * x: symexTarget("tc")

proc sutSliceWide(a: int32) =
  ## INT-74's shape over a 32-bit rendering, which the byte rewrite does not
  ## restate (the 8-bit row is exact since walker 431 and pinned in
  ## `tsymex_0016_int74_renderslice`): no input hits (the first byte is `-`
  ## or a digit, so `acc` is 47 or 50..59), and the sequence solver is left
  ## the `str.at` over `str.from_int` it did not decide for the 8-bit row.
  let t = int(a)
  var acc = 0
  let s = ($t & "ab")[0 .. 1]
  acc = acc + (s.len + ord(s[0]))
  if acc == 13: symexTarget("hit")

proc sutEasy(x: int) =
  if x > 3 and x < 7: symexTarget("easy")

proc mkNoClock(): SymexSettings =
  ## The pin settings' shape: every step bound at its default, no run clock.
  result = defaultSymexSettings()
  result.budget.queryTimeoutMs = 0
const noClock = mkNoClock()

suite "RFC-0016 INT-57 (A): the stall backstop with the wall clock off":
  test "the backstop is this file's 2 s":
    check stallBackstopMs == 2000
    check noClock.budget.queryTimeoutMs == 0'u
    check noClock.budget.queryRLimit != 0'u

  test "a solve past the backstop declines, named, and is not cached":
    let t0 = epochTime()
    let r = symexFind(sutCubes, tLabel("tc"), noClock)
    let secs = epochTime() - t0
    checkpoint $r.status & " in " & $int(secs) & " s; errors " & $r.errors
    check r.status == sxUnknown
    check not r.trusted
    var named = false
    for e in r.errors:
      # the run clock is off: never its wording
      check "no step bound ended the solve" notin e.msg
      if e.kind == beSolverUndef and "solver stall backstop" in e.msg and
         "2000 ms" in e.msg:
        named = true
    check named
    check rdQueryTimeout in r.soundness.runDependence
    # each cut solve takes the backstop's 2 s; the walk is not left running
    check secs < 120.0

  test "the backstop is the run's deadline: many stalled solves end within it":
    let t0 = epochTime()
    let r = symexFind(sutManyCubes, tLabel("tc"), noClock)
    let secs = epochTime() - t0
    checkpoint $r.status & " in " & $secs & " s; errors " & $r.errors
    check r.status == sxUnknown
    check not r.trusted
    check rdQueryTimeout in r.soundness.runDependence
    # the walk stopped, named, when the first solve was cut
    var halted = false
    for e in r.errors:
      if e.kind == beSolverUndef and "solver stall backstop" in e.msg and
         "ended the walk" in e.msg:
        halted = true
    check halted
    # one 2 s deadline for the run, not one per solve (four would be 8 s);
    # the slack is the walk's own work on a loaded host
    check secs < 7.0

  test "a wide rendering's slice is never a wrong verdict, and ends within the backstop":
    let t0 = epochTime()
    let r = symexFind(sutSliceWide, tLabel("hit"), noClock)
    let secs = epochTime() - t0
    checkpoint $r.status & " in " & $secs & " s; errors " & $r.errors
    check r.status in {sxUnknown, sxUnsat}
    if r.status == sxUnknown:
      var named = false
      for e in r.errors:
        if e.kind == beSolverUndef and "solver stall backstop" in e.msg:
          named = true
      check named
      check rdQueryTimeout in r.soundness.runDependence
    check secs < 7.0

  test "a query the step bound decides keeps its exact verdict":
    let r = pinFind(sutEasy, tLabel("easy"), noClock)
    check r.status == sxSat
    check r.trusted
    check r.soundness.runDependence == {}
    check r.witness[0] in 4 .. 6

suite "RFC-0016 INT-57: walker version":
  test "symexWalkerVersion >= 428":
    check parseInt(symexWalkerVersion) >= 428
