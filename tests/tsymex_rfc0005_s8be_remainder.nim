## RFC-0005 (soundness channels) slice S8be -- S8ax's remainder.
##
## Items (1)-(8); (9)-(11) are in `tsymex_rfc0005_s8be_remainder_b`,
## (12)-(13) in `tsymex_rfc0005_s8be_remainder_c`
## (RFC-0005 S8bo split the suite, which took 83 s to compile and run).
##
## Each section below names the wrong verdict, the crash or the decline it
## closes. Every expected value was probed against the real compiler (Nim
## 2.2.10, the debug build the test binary itself is).
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

template verdict(fn: typed, tgt: SymexTarget, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template verdictS(fn: typed, tgt: SymexTarget, want: SymexStatusKind,
                  s: SymexSettings) =
  block:
    let r = symexFind(fn, tgt, s)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template declines(fn: typed, tgt: SymexTarget, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (1) an opaque routine's implicit Defects -------------------------------
#
# WRONG VERDICT before S8be: an opaque routine's body was scanned for its
# explicit raises only, so an index or an overflow check inside it -- an
# `IndexDefect`, an `OverflowDefect` -- was a raise the walk never forked:
# `s8beIdx(7)` raises (probed), and `idx` was a false `sxUnsat`. Likewise a
# `finally` around the call never ran on that exit.

proc s8beIdx(a: int) {.symexOpaque.} =
  let s = [1, 2, 3]
  discard s[a]

proc s8beOvf(a: int) {.symexOpaque.} =
  discard a + 1

proc sutDefIdx(v: int) =
  symexAssume(v > 2 and v < 10)
  s8beIdx(v)

proc sutDefOvf(v: int) =
  symexAssume(v == high(int))
  s8beOvf(v)

proc sutDefFin(v: int) =
  symexAssume(v > 2 and v < 10)
  var ok = false
  try:
    s8beIdx(v)
    ok = true
  finally:
    if not ok and v == 7: symexTarget("fin")

# ---- (2) a replay that does not end ------------------------------------------
#
# HANG before S8be: a candidate's replay ran the real routine on the
# calling thread, with no bound: an opaque body that runs long held the
# run forever. The replay now runs on its own thread, abandoned past
# `replayTimeoutMs` with `feReplayTimedOut`: the candidate is never a
# confirmed `sxSat`.

proc s8beSpin(v: int) {.symexOpaque.} =
  if v > 5: sleep(3000)

proc sutSpin(v: int) =
  symexAssume(v > 5 and v < 100)
  s8beSpin(v)
  symexTarget("big")

proc sutSpinOk(v: int) =
  symexAssume(v >= 0 and v < 5)
  s8beSpin(v)
  if v == 3: symexTarget("three")

# ---- (3) `{.global.}` in a routine -------------------------------------------
#
# WRONG VERDICT before S8be: a `var x {.global.}` inside a proc was walked
# as a local, re-initialised on every call, so `reset` was a false `sxSat`
# and `second` a false `sxUnsat`. Nim initialises it once, at program
# start, and keeps it across calls: the second call reads 2 (probed). The
# walk holds it as a module-level variable, which may hold any value when
# the property runs (an earlier run's calls) -- `feGlobalHavoc`.

proc s8beCounter(): int =
  var n {.global.} = 0
  n += 1
  n

proc sutGlobalPragma(v: int) =
  discard s8beCounter()
  let b = s8beCounter()
  if b == 2 and v == 1: symexTarget("second")
  if b == 1: symexTarget("reset")

# ---- (4) an opaque raise of a subtype ----------------------------------------
#
# DECLINE before S8be: a handler naming a subtype (`S8beErr`) of a type an
# opaque routine's `raises` list allows (`ValueError`) declined the call,
# so `sub` was `sxUnknown`. The raise is now split into the subtypes the handlers name; each is a candidate the
# replay settles (`s8beRaisesSub` raises `S8beErr` on every input, so `sub`
# is confirmed and `base` refuted).

type S8beErr = object of ValueError

proc s8beRaisesSub(a: int) {.symexOpaque, raises: [ValueError].} =
  if a > -1000: raise newException(S8beErr, "sub")

proc sutSub(v: int) =
  symexAssume(v > 0 and v < 10)
  try:
    s8beRaisesSub(v)
  except S8beErr:
    symexTarget("sub")
  except ValueError:
    symexTarget("base")

# ---- (5) `int(high(int32))` --------------------------------------------------
#
# CRASH before S8be: `int(high(int32))` lowers `high(int32)` to a 64-bit
# bit-vector literal, and widening it was a walker fault
# (`weInternalWalkerFault`, "unsupported operand kind for widening"), so
# every target here was `sxUnknown`. `int(high(int32)) + 1 == 2147483648`
# (probed).

proc sutWiden(v: int32) =
  if int(v) == int(high(int32)): symexTarget("w1")
  if int(v) + 1 == 2147483648: symexTarget("w2")

proc sutWiden2(v: int) =
  let h = int(high(int32))
  if h + 1 == 2147483648 and v == 0: symexTarget("w3")
  if v > int(high(int32)): symexTarget("w4")

proc sutWiden3(v: int32) =
  let w = int64(v)
  if w == int64(high(int32)): symexTarget("w5")
  if v == high(int32) and int(v) + 1 > int(high(int32)): symexTarget("w6")

# ---- (6) a recursive frame's return under the depth budget -------------------
#
# SLOW before S8be (146 s): the fresh return a declined recursive frame
# stands for was a 64-bit vector against an Int-sorted argument, every
# query mixing the two theories. It is now Int-sorted, bounded by its
# declared type.

proc s8beSumTo(k: int): int =
  if k <= 0: 0 else: k + s8beSumTo(k - 1)

proc sutSumToNo(n: int) =
  symexAssume(n >= 0 and n <= 5)
  if s8beSumTo(n) == 15: symexTarget("st")
  if s8beSumTo(n) == 16: symexTarget("st_dead")

# ---- (7) a lazy read's check -------------------------------------------------
#
# A checked read (`s[i]`) followed by an operand's call is checked where
# it stands, before the call, and read after it. S8ax got the first pin
# right only through the order of its hoisted statements; it is now the
# placement itself (`splitIndexChecks`). DECLINE before S8be: a container
# the later call shrinks (`feEvalOrderUnmodelled`): `read` was
# `sxUnknown`.

proc s8beBoomD(): int =
  raise newException(AssertionDefect, "d")

proc sutStrIdxD(s: string; i: int) =
  symexAssume(i >= s.len and i < 100)
  let x = int(s[i]) + s8beBoomD()
  discard x

var s8beGs = @[1, 2]
proc s8beShrink(): int =
  s8beGs = @[7]
  0

proc sutSeqShrink(i: int) =
  s8beGs = @[1, 2]
  symexAssume(i >= 0 and i < 2)
  if s8beGs[i] + s8beShrink() == 7: symexTarget("read")

# Nim checks `s8beGs[1]` against the length 2 before the call and reads it
# after the call shrank the seq to one element: freed memory (probed: it
# read 1). The walk declines there rather than read a value.
proc sutSeqShrinkStale(i: int) =
  s8beGs = @[1, 2]
  symexAssume(i >= 0 and i < 2)
  if s8beGs[i] + s8beShrink() != 7: symexTarget("stale")

# ---- (8) a guard condition's order -------------------------------------------
#
# A `while` condition is now lowered under the evaluation-order model the
# rest of the routine has (S8ax (7)) rather than relying on the walker's
# clash decline: Nim hoists the call and reads the global after it
# (probed: `n == 1`). The verdicts were already right before S8be; this
# pins them under the new placement.

var s8beGx = 0
proc s8beBumpG(): int =
  s8beGx += 10
  0

proc sutGuardG(v: int) =
  symexAssume(v >= 0 and v < 5)
  s8beGx = v
  var n = 0
  while s8beGx + s8beBumpG() >= 10 and n < 1:
    inc n
  if n == 1: symexTarget("late")
  if n == 0: symexTarget("early")

suite "RFC-0005 S8be: walker version":
  test "symexWalkerVersion is at least 205":
    check parseInt(symexWalkerVersion) >= 205

suite "RFC-0005 S8be (1): an opaque routine's implicit Defects":
  test "an index check inside it raises":
    verdict(sutDefIdx, tRaisedExn("IndexDefect"), sxRaised)
  test "an overflow check inside it raises":
    verdict(sutDefOvf, tRaisedExn("OverflowDefect"), sxRaised)
  test "a finally around it runs on that exit":
    verdict(sutDefFin, tLabel("fin"), sxSat)

suite "RFC-0005 S8be (2): a replay that does not end":
  test "is abandoned, never confirmed":
    let r = symexFind(sutSpin, tLabel("big"),
                      SymexSettings(replayTimeoutMs: 300))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxSat
    check r.errors.hasKind(feReplayTimedOut)
  test "a replay that ends is confirmed as before":
    # RFC-0005 S8bo: a replay started while the one abandoned above still
    # runs is not confirmed (`roContended`); its 3 s sleep ends first.
    while replayAbandonedLive() > 0: sleep(1)
    let r = symexFind(sutSpinOk, tLabel("three"),
                      SymexSettings(replayTimeoutMs: 300))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feReplayTimedOut)
  test "the timeout enters the cache key only when not the default":
    check ";rpt=" notin canonicalize(SymexSettings())
    check ";rpt=300" in canonicalize(SymexSettings(replayTimeoutMs: 300))

suite "RFC-0005 S8be (3): `{.global.}` in a routine":
  test "is initialised once and kept across calls":
    verdict(sutGlobalPragma, tLabel("second"), sxSat)
    let r = symexFind(sutGlobalPragma, tLabel("reset"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxSat
    check r.errors.hasKind(feGlobalHavoc)

suite "RFC-0005 S8be (4): an opaque raise of a subtype":
  test "an except of the subtype is entered":
    verdict(sutSub, tLabel("sub"), sxSat)
    let r = symexFind(sutSub, tLabel("base"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feReplayRefuted)

suite "RFC-0005 S8be (5): `int(high(int32))`":
  test "a widened value does not wrap at 32 bits":
    verdict(sutWiden, tLabel("w1"), sxSat)
    verdict(sutWiden, tLabel("w2"), sxSat)
    verdict(sutWiden2, tLabel("w3"), sxSat)
    verdict(sutWiden2, tLabel("w4"), sxSat)
    verdict(sutWiden3, tLabel("w5"), sxSat)
    verdict(sutWiden3, tLabel("w6"), sxSat)

suite "RFC-0005 S8be (6): a recursive frame's return":
  test "a declined frame's return is bounded by its type, and fast":
    const s = SymexSettings(budget: ResourceBudget(maxCallDepth: 3,
                                                 maxRecursionDepth: 0))
    let r = symexFind(sutSumToNo, tLabel("st_dead"), s)
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxUnsat, sxUnknown}
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S8be (7): a lazy read's check":
  test "the index check comes before a later operand's call":
    verdict(sutStrIdxD, tRaisedExn("IndexDefect"), sxRaised)
  test "a container a later operand shrinks":
    verdict(sutSeqShrink, tLabel("read"), sxSat)
  test "a read the early check no longer covers declines":
    let r = symexFind(sutSeqShrinkStale, tLabel("stale"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S8be (8): a guard condition's order":
  test "the global is read after the call writes it":
    verdict(sutGuardG, tLabel("late"), sxSat)
    verdict(sutGuardG, tLabel("early"), sxUnsat)

