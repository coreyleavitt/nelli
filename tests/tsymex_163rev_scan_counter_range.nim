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
## Loop body spelling note: the R28 idioms below advance their counter
## with `i = i + 1`, which computes in `int` and raises `RangeDefect` on the
## conversion back into `i`. `inc i` is the `Inc` magic and raises
## `OverflowDefect` instead; the closed forms reported `RangeDefect` for it
## until RFC-0016 K9e, whose suites at the end of this file pin both
## spellings (`scanCounterStore`, dsl_parser.nim).
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation executed for real in Nim, in this file.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex
import ./s8cu_helpers

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
    let r = pinFind(scanCounterRangeIdiom, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = pinFind(scanCounterRangeIdiom, tLabel("t"))
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
    let r = pinFind(scanPairCounterRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = pinFind(scanPairCounterRange, tLabel("t"))
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
    let r = pinFind(accScanCounterRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

  test "the in-range survivor path still reaches the label":
    let r = pinFind(accScanCounterRange, tLabel("t"))
    check r.status == sxSat


# ---------------------------------------------------------------------------
# K9e: the `inc` spelling raises OverflowDefect, not RangeDefect
# ---------------------------------------------------------------------------
#
# `inc` (and `+=`) is the `Inc` magic. On a range receiver with overflow
# checks on and a signed base, Nim's C code generator checks the sum against
# the range itself and raises `OverflowDefect` outside it
# (`binaryArithOverflowRaw`); with overflow checks off, or an unsigned base,
# it emits a plain `+=` and nothing is raised (the counter leaves its range).
# Range checks play no part. `i = i + 1` is the conversion of an `int` sum
# into the range: `RangeDefect` under range checks (the idioms above),
# nothing without. Native, Nim 2.2.10, c: a `range[0..3]` counter scanning
# "abcde" raises `OverflowDefect` under `inc`; an `int8`-based one too; with
# overflow checks off the scan ends at `s.len` with no raise. An unsigned
# base cannot be scanned (`i < s.len` does not compile for it), but `inc`,
# `dec` and `+=` on one are plain: `inc` of 10 in a `range[0'u8 .. 10'u8]`
# raises nothing, and the walker claimed `OverflowDefect` for it. The closed
# forms wrote the counter through the assignment's range check and reported
# `RangeDefect` for the `inc` spelling. Every verdict is judged natively
# (`pinFind`); the unchecked shapes decline (the value past the range is not
# modelled), so they claim no raise.

proc scanIncRange(s: string) =
  var i: range[0..3] = 0
  while i < s.len and s[i] != '\0': inc i
  symexTarget("t")
  discard i

proc scanPairIncRange(s: string): int =
  var i: range[0..3] = 0
  while i < s.len:
    if s[i] == '\0':
      return i
    inc i
  symexTarget("t")
  return -1

proc accScanIncRange(s: string): string =
  var acc = ""
  var i: range[0..3] = 0
  while i < s.len:
    if s[i] == '\0':
      return acc
    acc.add(s[i])
    inc i
  symexTarget("t")
  return acc

proc scanIncRangeI8(s: string) =
  var i: range[0'i8..3'i8] = 0
  while i < s.len and s[i] != '\0': inc i
  symexTarget("t")
  discard i

{.push overflowChecks: off.}
proc scanIncRangeOvfOff(s: string) =
  var i: range[0..3] = 0
  while i < s.len and s[i] != '\0': inc i
  symexTarget("t")
  discard i
{.pop.}

{.push rangeChecks: off.}
proc scanAsgRangeRngOff(s: string) =
  var i: range[0..3] = 0
  while i < s.len and s[i] != '\0':
    i = i + 1
  symexTarget("t")
  discard i
{.pop.}

proc incRangeU8(x: range[0'u8..10'u8]) =
  var i = x
  inc i
  symexTarget("u")
  discard i

proc decRangeU8(x: range[0'u8..10'u8]) =
  var i = x
  dec i
  symexTarget("u")
  discard i

proc plusEqRangeU8(x: range[0'u8..10'u8]) =
  var i = x
  i += 1
  symexTarget("u")
  discard i

suite "K9e -- the oracle: which defect a scan counter's step raises":

  test "inc past a signed range raises OverflowDefect, in each idiom":
    proc rt1(s: string): int =
      var i: range[0..3] = 0
      while i < s.len and s[i] != '\0': inc i
      int(i)
    proc rt8(s: string): int =
      var i: range[0'i8..3'i8] = 0
      while i < s.len and s[i] != '\0': inc i
      int(i)
    expect OverflowDefect: discard rt1("abcde")
    expect OverflowDefect: discard rt8("abcde")
    expect OverflowDefect: discard scanPairIncRange("abcde")
    expect OverflowDefect: discard accScanIncRange("abcde")
    check rt1("ab") == 2
    check scanPairIncRange("a\0bc") == 1
    check accScanIncRange("a\0bc") == "a"

  test "unchecked, the counter leaves its range with no raise":
    # Each runs past its range to `s.len` and returns normally.
    scanIncRangeOvfOff("abcde")
    scanAsgRangeRngOff("abcde")
    check true

  test "a uint8-based range: inc, dec and += past it raise nothing":
    # Nim's code generator skips the `Inc` / `Dec` check for an unsigned
    # underlying type: 10 steps to 11, 0 to 255.
    incRangeU8(10)
    decRangeU8(0)
    plusEqRangeU8(10)
    check true

suite "K9e -- the closed forms raise what the step raises":

  test "idiom 1, inc: sxRaised(OverflowDefect)":
    let r = pinFind(scanIncRange, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "idiom 1, inc: no RangeDefect":
    # The run's one raise is the step's: a `RangeDefect` target reports it.
    let r = pinFind(scanIncRange, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "idiom 2, inc: sxRaised(OverflowDefect), no RangeDefect":
    let r = pinFind(scanPairIncRange, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
    let g = pinFind(scanPairIncRange, tRaisedExn("RangeDefect"))
    check g.status == sxRaised
    if g.status == sxRaised:
      check g.raisedTypeId == "OverflowDefect"

  test "idiom 3, inc: sxRaised(OverflowDefect), no RangeDefect":
    let r = pinFind(accScanIncRange, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
    let g = pinFind(accScanIncRange, tRaisedExn("RangeDefect"))
    check g.status == sxRaised
    if g.status == sxRaised:
      check g.raisedTypeId == "OverflowDefect"

  test "an int8-based counter, inc: sxRaised(OverflowDefect)":
    let r = pinFind(scanIncRangeI8, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "the in-range survivor still reaches the label":
    check pinFind(scanIncRange, tLabel("t")).status == sxSat
    check pinFind(scanPairIncRange, tLabel("t")).status == sxSat
    check pinFind(accScanIncRange, tLabel("t")).status == sxSat

  test "overflow checks off, inc: no raise is claimed":
    let o = pinFind(scanIncRangeOvfOff, tRaisedExn("OverflowDefect"))
    checkpoint "OverflowDefect " & $o.status
    check o.status != sxRaised
    let g = pinFind(scanIncRangeOvfOff, tRaisedExn("RangeDefect"))
    checkpoint "RangeDefect " & $g.status
    check g.status != sxRaised

  test "range checks off, i = i + 1: no raise is claimed":
    let o = pinFind(scanAsgRangeRngOff, tRaisedExn("OverflowDefect"))
    checkpoint "OverflowDefect " & $o.status
    check o.status != sxRaised
    let g = pinFind(scanAsgRangeRngOff, tRaisedExn("RangeDefect"))
    checkpoint "RangeDefect " & $g.status
    check g.status != sxRaised

suite "K9e -- a uint-based range's step claims no raise":

  test "inc past the high bound: no OverflowDefect":
    let r = pinFind(incRangeU8, tRaisedExn("OverflowDefect"))
    checkpoint $r.status
    check r.status != sxRaised

  test "dec past the low bound: no OverflowDefect":
    let r = pinFind(decRangeU8, tRaisedExn("OverflowDefect"))
    checkpoint $r.status
    check r.status != sxRaised

  test "+= past the high bound: no OverflowDefect":
    let r = pinFind(plusEqRangeU8, tRaisedExn("OverflowDefect"))
    checkpoint $r.status
    check r.status != sxRaised

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138":
    check parseInt(symexWalkerVersion) >= 138

  test "walker version floor >= 457 (K9e: a scan counter's inc raises OverflowDefect)":
    check parseInt(symexWalkerVersion) >= 457
