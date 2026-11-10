## RFC-0016 W3-z P5. A read inside the right operand of a boolean `and`/`or`
## must lower under the left operand's guard. `shortCircuitPartIsPure` used to
## treat an operand that hoisted nothing as pure and joined it flat, so a
## degrade recorded while lowering it (an indeterminate `{.noinit.}` read) or
## a raise it forks (an index fault) was asserted even on paths where the left
## operand short-circuits. Natively the right operand is not evaluated there.
##
## Each "dead" case makes the right operand unreachable (`k > 3 and k < 2`,
## `k > 3 or k < 10`), so no path may carry its side condition.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/[canonicalize, types, replayproc]

proc scrub() {.noinline.} =
  ## Zero the stack where the replay's frames land, so the `{.noinit.}` slot
  ## reads zero natively and the replay confirms (as `tsymex_0016_wa_undefined_e2e`).
  var a {.volatile.}: array[8192, int]
  for i in 0 ..< a.len: a[i] = 0

proc andDeadRead(k: int) =
  ## `k > 3` is false on the else path, so natively `x` is never read there.
  var x {.noinit.}: int
  if k > 3 and x == x: discard
  else: symexTarget("clean")

proc andDeadRead2(k: int) =
  if k > 3: return
  var x {.noinit.}: int
  if k > 3 and x == x: discard
  else: symexTarget("clean")

proc orDeadRead(k: int) =
  ## The left operand always holds, so `x` is never read.
  if k > 3: return
  var x {.noinit.}: int
  if k <= 3 or x == x: symexTarget("clean")

proc andLiveRead(k: int) =
  var x {.noinit.}: int
  if k > 3 and x == x: symexTarget("live")

proc orLiveRead(k: int) =
  var x {.noinit.}: int
  if k > 3 or x != x: discard
  else: symexTarget("live")

proc andDeadIndex(a: seq[int], k: int) =
  if k > 3 and k < 2 and a[k] == 0: discard

proc orDeadIndex(a: seq[int], k: int) =
  if (k > 3 or k < 10) or a[k] == 0: discard

proc andGuardedIndex(a: seq[int], k: int) =
  if k >= 0 and k < a.len and a[k] == 0: symexTarget("hit")

proc andLiveIndex(a: seq[int], k: int) =
  if k > 3 and a[k] == 0: discard

proc orLiveIndex(a: seq[int], k: int) =
  if k < 3 or a[k] == 0: discard

const ind = {UbKind(ubIndeterminateRead)}

suite "W3-z P5: the right operand of and/or is lowered under the left guard":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 316

  when defined(cpp) or replayReexecs:
    test "skipped: the replay stack is not the scrubbed one":
      skip()
  else:
    test "and: a dead right-hand read carries no UB":
      scrub()
      let r = symexFind(andDeadRead, tLabel("clean"))
      check r.status == sxSat
      check r.soundness.undefinedKinds == {}
    test "and: a dead right-hand read carries no UB (left known false)":
      scrub()
      let r = symexFind(andDeadRead2, tLabel("clean"))
      check r.status == sxSat
      check r.soundness.undefinedKinds == {}
    test "or: a dead right-hand read carries no UB":
      scrub()
      let r = symexFind(orDeadRead, tLabel("clean"))
      check r.status == sxSat
      check r.soundness.undefinedKinds == {}
    test "and: a live right-hand read is still UB":
      scrub()
      let r = symexFind(andLiveRead, tLabel("live"))
      check r.status == sxSat
      check r.soundness.undefinedKinds == ind
    test "or: a live right-hand read is still UB":
      scrub()
      let r = symexFind(orLiveRead, tLabel("live"))
      check r.status == sxSat
      check r.soundness.undefinedKinds == ind

  test "and: a dead index is never an IndexDefect":
    check symexFind(andDeadIndex, tRaisedExn("IndexDefect")).status != sxRaised
  test "or: a dead index is never an IndexDefect":
    check symexFind(orDeadIndex, tRaisedExn("IndexDefect")).status != sxRaised
  test "a bounds-guarded index never raises and the target is reachable":
    check symexFind(andGuardedIndex, tRaisedExn("IndexDefect")).status != sxRaised
    check symexFind(andGuardedIndex, tLabel("hit")).status == sxSat
  test "and: a live unguarded index still raises":
    check symexFind(andLiveIndex, tRaisedExn("IndexDefect")).status == sxRaised
  test "or: a live unguarded index still raises":
    check symexFind(orLiveIndex, tRaisedExn("IndexDefect")).status == sxRaised

# ---- a degrade that is not a `{.noinit.}` read: an unwritten module global ----
var p5g = 0
var p5arr: array[4, int]

proc andDeadGlobal(k: int) =
  if k > 3 and p5g == 0: discard
  else: symexTarget("clean")

proc orDeadGlobal(k: int) =
  if k > 3: return
  if k <= 3 or p5g == 0: symexTarget("clean")

proc andDeadGlobalElem(k: int) =
  if k > 3 and p5arr[1] == 0: discard
  else: symexTarget("clean")

proc andLiveGlobal(k: int) =
  if k > 3 and p5g == 0: symexTarget("live")

suite "W3-z P5b: any lowering-time degrade in a dead right operand":
  ## An unwritten module global is read on the right; the degrade it records
  ## (feGlobalHavoc, a spurious-path taint) must reach only the paths where
  ## the left operand lets the read happen; the run-level error list still
  ## names it, because the live branch is walked. Not a `{.noinit.}` read, so the parser
  ## cannot name it by a local's pragma.
  test "and: a dead global read taints nothing":
    let r = symexFind(andDeadGlobal, tLabel("clean"))
    check r.status == sxSat
    check r.soundness.pathTaint == {}
  test "or: a dead global read taints nothing":
    let r = symexFind(orDeadGlobal, tLabel("clean"))
    check r.status == sxSat
    check r.soundness.pathTaint == {}
  test "and: a dead global array element read taints nothing":
    let r = symexFind(andDeadGlobalElem, tLabel("clean"))
    check r.status == sxSat
    check r.soundness.pathTaint == {}
  test "and: a live global read still taints the path":
    let r = symexFind(andLiveGlobal, tLabel("live"))
    check r.status == sxSat
    check scSpurious in r.soundness.pathTaint
