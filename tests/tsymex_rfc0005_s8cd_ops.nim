## RFC-0005 S8cd -- operations: `len` over a proc value's result (item 1), and
## a string pinned to a long literal under a tight cap (item 6). Item 4 is in
## `tsymex_rfc0005_s8cd_setorder_small` and `_large`.
##
## The "nim" tests run each SUT natively.
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

template classified(fn: typed, lbl: string) =
  ## The proc value has no known target: a decline naming that, never the
  ## receiver's kind, and never a walker fault.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(ceClosureUnknownCallee) or
          r.errors.hasKind(ceUnsupportedHof)
    check not r.errors.hasKind(weInternalWalkerFault)
    check "unsupported receiver kind" notin show(r.errors)
    check "fixed-width" notin show(r.errors)

# --- item 1: `len` over the receiver kinds the walker builds -----------------

type
  T2 = tuple[a, b: int]
  PF = object
    f: proc(k: int): seq[int]
    xs: seq[int]
    st: string
    tb: Table[string, int]

var gf: proc(k: int): seq[int]

proc viaPtr(p: ptr seq[int]) =
  if p != nil and p[].len == 2: symexTarget("l_ptr")
proc viaRef(p: ref seq[T2]) =
  if p != nil and p[].len == 2: symexTarget("l_ref")
proc viaField(o: ref PF) =
  if o != nil and o.xs.len == 2: symexTarget("l_field")
proc viaStrField(o: ref PF) =
  if o != nil and o.st.len == 2: symexTarget("l_str")
proc viaTabField(o: ref PF) =
  if o != nil and o.tb.len == 2: symexTarget("l_tab")

proc procParam(f: proc(k: int): seq[int]; k: int) =
  if f(k).len == 2: symexTarget("l_pv")
proc procStr(f: proc(k: int): string; k: int) =
  if f(k).len == 2: symexTarget("l_pvs")
proc procTab(f: proc(k: int): Table[string, int]; k: int) =
  if f(k).len == 2: symexTarget("l_pvt")
proc procTup(f: proc(k: int): seq[T2]; k: int) =
  if f(k).len == 2: symexTarget("l_pvtu")
proc heapProc(o: ref PF; k: int) =
  if o != nil and o.f != nil:
    discard
proc globalProc(k: int) =
  if gf(k).len == 2: symexTarget("l_gpv")
proc forOverUnknown(f: proc(k: int): seq[int]; k: int) =
  for x in f(k):
    if x == 1: symexTarget("l_for")

proc mkSeq(k: int): seq[int] =
  if k > 0: @[1, 2] else: @[]
proc mkTab(k: int): Table[string, int] =
  if k > 0:
    result["a"] = 1
    result["b"] = 2
proc mkSet(k: int): HashSet[int] =
  if k > 0:
    result.incl 1
    result.incl 2
proc mkBits(k: int): set[uint8] =
  if k > 0: {1'u8, 2'u8} else: {}

proc knownSeq(k: int) =
  let f = mkSeq
  if f(k).len == 2: symexTarget("k_seq")
  if f(k).len == 1: symexTarget("k_seq_dead")
proc knownTab(k: int) =
  let f = mkTab
  if f(k).len == 2: symexTarget("k_tab")
  if f(k).len == 1: symexTarget("k_tab_dead")
proc knownSet(k: int) =
  let f = mkSet
  if f(k).len == 2: symexTarget("k_set")
proc knownBits(k: int) =
  let f = mkBits
  if f(k).card == 2: symexTarget("k_bits")
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

  test "nim":
    symexCaptureBegin()
    knownSeq(1); knownTab(1); knownSet(1); knownBits(1); knownFor(1); badKeyCalled(1)
    check symexCaptureEnd() ==
      toHashSet(["k_seq", "k_tab", "k_set", "k_bits", "k_for", "k_badkey"])

  test "ptr, ref and heap-field receivers":
    reached(viaPtr, "l_ptr")
    reached(viaRef, "l_ref")
    reached(viaField, "l_field")
    reached(viaStrField, "l_str")
    reached(viaTabField, "l_tab")

  test "a proc value with no target: a classified decline":
    classified(procParam, "l_pv")
    classified(procStr, "l_pvs")
    classified(procTab, "l_pvt")
    classified(procTup, "l_pvtu")
    classified(globalProc, "l_gpv")
    classified(forOverUnknown, "l_for")

  test "a known proc value: each result kind decided":
    reached(knownSeq, "k_seq")
    dead(knownSeq, "k_seq_dead")
    reached(knownTab, "k_tab")
    dead(knownTab, "k_tab_dead")
    reached(knownSet, "k_set")
    reached(knownBits, "k_bits")

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
