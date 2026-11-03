## RFC-0005 S8cd -- operations: `len` over a proc value's result (item 1), and
## a string pinned to a long literal under a tight cap (item 6). Item 4 is in
## `tsymex_rfc0005_s8cd_setorder_small` and `_large`.
##
## The "nim" tests run each SUT natively.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with `tsymex_rfc0005_s8cd_ops`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 62 s).

import std/[unittest, strutils, sets, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reached(fn: typed, lbl: string; st: SymexSettings = SymexSettings()) =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feReplayRefuted)

template dead(fn: typed, lbl: string; st: SymexSettings = SymexSettings()) =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnsat

proc mkSeq(k: int): seq[int] =
  if k > 0: @[1, 2] else: @[]
proc badKeyCalled(k: int) =
  # The table's key type has no model: a call allocates it and declines.
  let f = proc(j: int): Table[(int, int), string] =
    if j > 0: result[(1, 2)] = "x"
  if f(k).len == 1: symexTarget("k_badkey")
proc knownFor(k: int) =
  var calls = 0
  let f = proc(j: int): seq[int] =
    inc calls
    mkSeq(j)
  var sum = 0
  for x in f(k): sum += x
  if sum == 3 and calls == 1: symexTarget("k_for")
  if calls > 1: symexTarget("k_for_dead")

suite "S8cd item 1: len over each receiver kind":
  test "a called proc value whose Table key has no model: a decline, never sxUnsat":
    let r = symexFind(badKeyCalled, tLabel("k_badkey"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a for over a call runs the call once":
    reached(knownFor, "k_for")
    dead(knownFor, "k_for_dead")

# --- item 6: a pinned long literal under a tight cap ----------------------------

const cap8 = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))
const cap2 = SymexSettings(budget: ResourceBudget(maxSeqLen: 2))

proc longPinned(s: string) =
  symexAssume(s == "abcdefghijkl")
  if s.rfind("kl") == 10: symexTarget("c_long")
  if s.rfind("kl") == 3: symexTarget("c_long_dead")

proc longPinnedNeedle(s, n: string) =
  symexAssume(s == "abcabcabcabc")
  if s.rfind(n) == 9 and n.len == 3: symexTarget("c_needle")
  if s.rfind(n) >= 0 and n.len > 12: symexTarget("c_needle_dead")

proc longPinnedLen(s, t: string) =
  symexAssume(s == "abcdefghijkl")
  if s.len == 12 and t.len == 1: symexTarget("c_len")
  if t.len == 9 and s.len == 12: symexTarget("c_other_past")

proc pastCap(s, t: string) =
  symexAssume(s == "abc")
  if t.len > 10 and s.rfind("bc") == 1: symexTarget("c_past")

proc withinCap(s, t: string) =
  symexAssume(s == "abc")
  if t.len > 2 and s.rfind("bc") == 1: symexTarget("c_within")

proc pinnedThenLen(s, t: string) =
  symexAssume(s == "abcdefghij" and t.len == 2)
  if s.len == t.len + 8: symexTarget("c_and")

suite "S8cd item 6: a string pinned to a literal under a cap":

  test "nim":
    symexCaptureBegin()
    longPinned("abcdefghijkl")
    longPinnedNeedle("abcabcabcabc", "abc")
    longPinnedLen("abcdefghijkl", "x")
    withinCap("abc", "xyz")
    pinnedThenLen("abcdefghij", "xy")
    check symexCaptureEnd() ==
      toHashSet(["c_long", "c_needle", "c_len", "c_within", "c_and"])

  test "the literal itself is past the cap: decided, not declined":
    reached(longPinned, "c_long", cap8)
    dead(longPinned, "c_long_dead", cap8)
    reached(longPinned, "c_long", cap2)

  test "a symbolic needle over a pinned haystack":
    reached(longPinnedNeedle, "c_needle", cap8)
    dead(longPinnedNeedle, "c_needle_dead", cap8)

  test "a conjunct of the assumption pins it too":
    reached(pinnedThenLen, "c_and", cap8)

  test "another string still takes the cap":
    reached(longPinnedLen, "c_len", cap8)
    let r = symexFind(longPinnedLen, tLabel("c_other_past"), cap2)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check "maxSeqLen" in show(r.errors)

  test "SAT within the cap, and SAT only past it":
    reached(withinCap, "c_within", cap8)
    let r = symexFind(pastCap, tLabel("c_past"), cap8)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check "maxSeqLen" in show(r.errors)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
