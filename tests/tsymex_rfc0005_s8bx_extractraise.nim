## RFC-0005 (soundness channels) slice S8bx, item 1 -- a raise from witness
## extraction inside the walk was lost on the C backend.
##
## Since S1c the target solve and its witness extraction run inside the
## walk. Nim 2.2.10's C backend (goto exceptions) destroys a call's result
## temporary on the raise path without clearing the error flag first, and
## when that temporary holds a Z3 term (a `seq[Path]`, a `SymVal`, a
## `Z3String`), nim-z3's `termDestroy` runs its own `try: ... except
## CatchableError: discard` with the flag still set: its first checked call
## jumps to its handler, which takes the IN-FLIGHT exception as its own,
## clears the flag and pops it. The frame then returns as if nothing was
## raised. Located by instrumenting every `popCurrentException` of a probe
## build: the extraction raise was consumed by `Z3BitVec`'s `=destroy`,
## called from `walkBlock`'s raise path destroying `walk`'s returned
## `seq[Path]` (`result = walk(s, result, w)`). C++ exceptions are native,
## so the same raise reached `runSymex` as `weInternalWalkerFault` there.
##
## The companion `.nim.cfg` sets `-d:symexTestInjectWalkerFault`, under
## which extracting a string parameter named `injectExtractionFault` raises
## out of extraction, and one named `injectSwallowedExtractionFault` raises
## in a callee returning a Z3 term, which the C backend loses inside
## extraction itself. Both must be a named decline on both backends.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc namedFault[T](r: SymexResult[T]; text: string): bool =
  ## The run declines with `weInternalWalkerFault` naming the injected raise.
  if r.status != sxUnknown: return false
  for e in r.errors:
    if e.kind == weInternalWalkerFault and e.severity == sevError and
       text in e.msg:
      return true
  false

# A loop before the target: the raise unwinds through `walkBlock`, whose
# raise path destroys the loop's returned paths. Was a false sxUnsat on C
# with no error at all.
proc afterLoop(injectExtractionFault: string, n: int) =
  var i = 0
  while i < n and i < 4:
    inc i
  if i == 3 and n > 1:
    symexTarget("after_loop")

# S8bl's trigger shape (two iterations of one input table), with the
# extraction raise injected rather than an out-of-range key codepoint.
proc twoIters(t: Table[string, int], injectExtractionFault: string) =
  if t.len > 2: return
  for k, v in t:
    if v < -100 or v > 100: return
  var s = 0
  for k, v in t.pairs:
    s += v
  if "a" in t and t["a"] == 4 and t.len == 1: symexTarget("two_iters")

# No loop: the raise already reached `runSymex` on both backends.
proc flat(injectExtractionFault: string, a, b: int) =
  if a > 3 and b < 2: symexTarget("flat")

# The raise is lost inside extraction (a Z3-term result destroyed on the
# raise path), so extraction itself returns normally on C.
proc swallowedInside(injectSwallowedExtractionFault: string, n: int) =
  if n == 7: symexTarget("swallowed")

# A string parameter that is not an injection name extracts normally.
proc clean(s: string, n: int) =
  var i = 0
  while i < n and i < 4:
    inc i
  if i == 3 and s.len == 2:
    symexTarget("clean")

# RFC-0005 batch 8: the same raise from an own-context solve (S8bp's
# `solveBounded`, S8bu's bounds). The solve sits at the same place in the walk
# as extraction, so the same destructor could lose it, and the query's status
# was whatever the frame held. A parameter's name in the query triggers it.
proc solveAfterLoop(injectSolveFault: int) =
  var i = 0
  while i < injectSolveFault and i < 4:
    inc i
  if i == 3: symexTarget("solve_after_loop")

proc solveFlat(injectSolveFault: int) =
  if injectSolveFault == 7: symexTarget("solve_flat")

proc solveSwallowed(injectSwallowedSolveFault: int) =
  var i = 0
  while i < injectSwallowedSolveFault and i < 4:
    inc i
  if i == 3: symexTarget("solve_swallowed")

# Only the target's query names the parameter: the raise leaves the target
# solve, past the loop's paths, as `afterLoop`'s extraction raise does.
proc solveAtTarget(n, injectSolveFault: int) =
  var i = 0
  while i < n and i < 4:
    inc i
  if i == 3 and n > 1 and injectSolveFault == 1:
    symexTarget("solve_at_target")

proc solveAtTargetTable(t: Table[string, int], injectSolveFault: int) =
  if t.len > 2: return
  for k, v in t:
    if v < -100 or v > 100: return
  var s = 0
  for k, v in t.pairs:
    s += v
  if "a" in t and t["a"] == 4 and t.len == 1 and injectSolveFault == 1:
    symexTarget("solve_at_table")

proc solveSwallowedAtTarget(n, injectSwallowedSolveFault: int) =
  var i = 0
  while i < n and i < 4:
    inc i
  if i == 3 and n > 1 and injectSwallowedSolveFault == 1:
    symexTarget("solve_swallowed_target")

const injected = "S8bx synthetic extraction fault"
const injectedSolve = "batch 8 synthetic solve fault"

suite "S8bx (1): a raise from in-walk witness extraction":

  test "after a loop: a named decline (was a false sxUnsat on C)":
    let r = symexFind(afterLoop, tLabel("after_loop"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check namedFault(r, injected)

  test "two iterations of one table: a named decline (was a false sxUnsat on C)":
    let r = symexFind(twoIters, tLabel("two_iters"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check namedFault(r, injected)

  test "no loop: a named decline":
    let r = symexFind(flat, tLabel("flat"))
    checkpoint $r.status & " " & show(r.errors)
    check namedFault(r, injected)

  test "lost inside extraction: a named decline, never a winner":
    let r = symexFind(swallowedInside, tLabel("swallowed"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxSat
    check namedFault(r, "S8bx synthetic swallowed extraction fault")

  test "a clean string parameter extracts":
    let r = symexFind(clean, tLabel("clean"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 2
      check r.witness[1] == 3

  test "a later run is not declined by an earlier run's fault":
    discard symexFind(afterLoop, tLabel("after_loop"))
    let r = symexFind(clean, tLabel("clean"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

suite "batch 8: a raise from an own-context solve":

  test "after a loop: a named decline":
    let r = symexFind(solveAfterLoop, tLabel("solve_after_loop"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, injectedSolve)

  test "no loop: a named decline":
    let r = symexFind(solveFlat, tLabel("solve_flat"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, injectedSolve)

  test "lost inside the solve: a named decline":
    let r = symexFind(solveSwallowed, tLabel("solve_swallowed"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, "batch 8 synthetic swallowed solve fault")

  test "the target's solve, past a loop: a named decline":
    let r = symexFind(solveAtTarget, tLabel("solve_at_target"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, injectedSolve)

  test "the target's solve, past two iterations of a table: a named decline":
    let r = symexFind(solveAtTargetTable, tLabel("solve_at_table"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, injectedSolve)

  test "lost inside the target's solve: a named decline":
    let r = symexFind(solveSwallowedAtTarget, tLabel("solve_swallowed_target"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check namedFault(r, "batch 8 synthetic swallowed solve fault")

  test "a later run is not declined by an earlier run's fault":
    discard symexFind(solveFlat, tLabel("solve_flat"))
    let r = symexFind(clean, tLabel("clean"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

suite "S8bx: walker version":

  test "walker version floor >= 228 (S8bx)":
    check parseInt(symexWalkerVersion) >= 228
