## Issue #163 review finding R28 (Medium -- a narrowing R27 introduced).
##
## R27 fixed a High in R22 by deleting a name-keyed walk-global table and
## instead attaching the assignment target's declared type to the IR at
## parse time (`IRStmt.isAssign.aty`, populated via `classifyType` on the
## target's true `nnkSym`). R27 wired `aty` at the three sites that go
## through the NORMAL assignment dispatch (plain assign, inc/dec, +=/-=/*=).
##
## But three SCAN-IDIOM RECOGNIZERS replace an entire `while` loop with a
## synthesized closed form and call `mkAssign` DIRECTLY, bypassing that
## dispatch entirely:
##   - `tryRecognizeScanIdiom`         (the skip-while-and-clamp shape)
##   - `tryRecognizeScanPairIdiom`     (the early-return-on-match shape)
##   - `tryRecognizeAccumulatingScan`  (the readCString accumulating shape)
##
## Each calls `mkAssign(iNode.strVal, ...)` with NO third argument, so
## `aty` defaults to `nil` and `forkAssignRangeCheck` never runs for the
## closed form's counter write -- even though each recognizer's own type
## gate (`classifyType(iNode).ty.kind != itInt`) happily accepts a ranged
## int counter (`hasRange` is not excluded; a `range[lo..hi]` IS `itInt`).
##
## Under R22's flat name-keyed table these sites WERE covered (name-based
## lookup, oblivious to which parser call site produced the statement) --
## this is a narrowing R27 introduced, not a pre-existing gap.
##
## Trigger (the finding's own example):
##
##     var i: range[0..3] = 0
##     while i < s.len and s[i] != '\0':
##       inc i
##
## A genuine Nim `RangeDefect` at the closed form's final counter write is
## missed -- wrong verdict (sxUnsat/no witness) instead of `sxRaised`.
##
## Loop body spelling note: every idiom below advances its counter with
## the explicit `i = i + 1` form rather than `inc i`. Both spellings are
## accepted by the recognizers' shared `counterAdvancesByOne` predicate,
## but they are NOT semantically identical in real Nim for a `range`-typed
## counter -- confirmed empirically (probe run, not committed): `inc i` on
## a `range[0..3]` at `i == 3` raises `OverflowDefect` (the `inc` magic
## does checked arithmetic in the range's own representation), while
## `i = i + 1` computes in the base `int` type and raises `RangeDefect` on
## the implicit conversion back into `i` -- the SAME defect
## `forkAssignRangeCheck` always routes for a fixed assignment, regardless
## of which of R27's/this finding's call sites produced it. Using the
## `inc`-spelling here would pin a pre-existing (out-of-scope, inherited
## from R27's inc/dec arm) Overflow-vs-Range modeling mismatch instead of
## R28's actual narrowing; the `i = i + 1` spelling isolates R28 cleanly.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation executed for real in Nim, in this file.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

# ---------------------------------------------------------------------------
# Idiom 1 -- tryRecognizeScanIdiom (skip-while-and-clamp)
# ---------------------------------------------------------------------------
#
##     while i < s.len and s[i] != '\0': i = i + 1
#
## Real Nim: `i` is `range[0..3]`. If no NUL appears in the first 4 bytes
## and `s.len > 4`, the assignment raises RangeDefect trying to push `i`
## past 3 (the loop can never reach `i == s.len` for a longer string -- it
## dies first). Any string of length <= 4 with no NUL, or with a NUL
## inside [0,3], leaves `i` in range and does not raise.

proc scanCounterRangeIdiom(s: string) =
  var i: range[0..3] = 0
  while i < s.len and s[i] != '\0':
    i = i + 1
  symexTarget("t")
  discard i

suite "#163 review R28 -- the oracle (idiom 1: skip-while-and-clamp)":

  test "Nim itself raises RangeDefect when the scan runs the counter past the range":
    proc rt(s: string): range[0..3] =
      var i: range[0..3] = 0
      while i < s.len and s[i] != '\0':
        i = i + 1
      i
    expect RangeDefect:
      discard rt("abcde")       # no NUL in 5 bytes -- counter overruns [0,3]
    check rt("ab") == 2         # s.len == 2 -- counter stops at 2, in range
    check rt("a\0bcde") == 1    # NUL at index 1 -- counter stops at 1

suite "#163 review R28 -- idiom 1: the recognized closed form keeps the counter's range":

  test "a genuinely out-of-range scan counter is found as sxRaised(RangeDefect)":
    ## Before the fix: `mkAssign(iNode.strVal, boundIR)` /
    ## `mkAssign(iNode.strVal, mkVar(p))` carry no `aty` -- sxUnsat (nothing
    ## in the path space raises, the RangeDefect fork was never built).
    let r = symexFind(scanCounterRangeIdiom, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(scanCounterRangeIdiom, tLabel("t"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Idiom 2 -- tryRecognizeScanPairIdiom (early-return-on-match)
# ---------------------------------------------------------------------------
#
##     while i < s.len:
##       if s[i] == '\0':
##         return i
##       i = i + 1
##     symexTarget("t")
##     return -1
#
## Real Nim: same overrun mechanism -- if no NUL appears in the first 4
## bytes and `s.len > 4`, the assignment raises RangeDefect before the loop
## can ever reach a longer index or fall through past it.

proc scanPairCounterRange(s: string): int =
  var i: range[0..3] = 0
  while i < s.len:
    if s[i] == '\0':
      return i
    i = i + 1
  symexTarget("t")
  return -1

suite "#163 review R28 -- the oracle (idiom 2: early-return-on-match)":

  test "Nim itself raises RangeDefect when the scan runs the counter past the range":
    proc rt(s: string): int =
      var i: range[0..3] = 0
      while i < s.len:
        if s[i] == '\0':
          return i
        i = i + 1
      return -1
    expect RangeDefect:
      discard rt("abcde")       # no NUL in 5 bytes -- counter overruns [0,3]
    check rt("ab") == -1        # s.len == 2 -- counter stops at 2, in range
    check rt("a\0bc") == 1      # NUL at index 1 -- returns before overrun

suite "#163 review R28 -- idiom 2: the recognized closed form keeps the counter's range":

  test "a genuinely out-of-range scan counter is found as sxRaised(RangeDefect)":
    ## Before the fix: `mkAssign(iNode.strVal, mkVar(p))` (found branch) and
    ## `mkAssign(iNode.strVal, boundIR)` (not-found branch) both carry no
    ## `aty` -- sxUnsat.
    let r = symexFind(scanPairCounterRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(scanPairCounterRange, tLabel("t"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Idiom 3 -- tryRecognizeAccumulatingScan (readCString family)
# ---------------------------------------------------------------------------
#
##     while i < s.len:
##       if s[i] == '\0':
##         return acc
##       acc.add(s[i])
##       i = i + 1
##     symexTarget("t")
##     return acc
#
## Same overrun mechanism again, now with an accumulating string alongside
## the ranged counter.

proc accScanCounterRange(s: string): string =
  var acc = ""
  var i: range[0..3] = 0
  while i < s.len:
    if s[i] == '\0':
      return acc
    acc.add(s[i])
    i = i + 1
  symexTarget("t")
  return acc

suite "#163 review R28 -- the oracle (idiom 3: readCString accumulating scan)":

  test "Nim itself raises RangeDefect when the scan runs the counter past the range":
    proc rt(s: string): string =
      var acc = ""
      var i: range[0..3] = 0
      while i < s.len:
        if s[i] == '\0':
          return acc
        acc.add(s[i])
        i = i + 1
      return acc
    expect RangeDefect:
      discard rt("abcde")        # no NUL in 5 bytes -- counter overruns [0,3]
    check rt("ab") == "ab"       # s.len == 2 -- counter stops at 2, in range
    check rt("a\0bc") == "a"     # NUL at index 1 -- returns before overrun

suite "#163 review R28 -- idiom 3: the recognized closed form keeps the counter's range":

  test "a genuinely out-of-range scan counter is found as sxRaised(RangeDefect)":
    let r = symexFind(accScanCounterRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = symexFind(accScanCounterRange, tLabel("t"))
    check r.status == sxSat


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138":
    check parseInt(symexWalkerVersion) >= 138
