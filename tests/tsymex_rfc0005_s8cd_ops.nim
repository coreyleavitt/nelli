## RFC-0005 S8cd -- operations: `len` over a proc value's result (item 1), the
## evaluation order of a set expression (item 4), and a string pinned to a
## long literal under a tight cap (item 6).
##
## The "nim" tests run each SUT natively; item 4's expectations are its
## results (C backend and C++, a set of more than 64 values differs from a
## smaller one).
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
    knownSeq(1); knownTab(1); knownSet(1); knownBits(1); knownFor(1)
    check symexCaptureEnd() == toHashSet(["k_seq", "k_tab", "k_set", "k_bits", "k_for"])

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

  test "a for over a call runs the call once":
    reached(knownFor, "k_for")
    dead(knownFor, "k_for_dead")

# --- item 4: where a set expression is read ----------------------------------

type
  Sm = range[0'u8 .. 7'u8]   # a C integer
  Md = range[0'u8 .. 63'u8]  # the largest C integer
  Mx = range[0'u8 .. 64'u8]  # the smallest array

template orderSuts(T: typedesc; A, B, C, X, tg: untyped) =
  ## Each proc starts `s = {A}`, `k = A`; `ch` writes `s = {B, C}`, `k = B`.
  proc `unionNested tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): set[T] =
      s = {B}
      {C}
    let r = (s + {X}) + ch()
    if A in r and j == 1: symexTarget(astToStr(tg) & "_u_early")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_u_late")
  proc `compareTemp tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(s <= {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_le_early")
    s = {A}
    if not b2(s <= {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_le_late")
  proc `eqLazy tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(s == {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_eq_early")
    s = {A}
    if not b2(s == {A}, ch()) and j == 1: symexTarget(astToStr(tg) & "_eq_late")
  proc `inLazy tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): bool =
      s = {B, C}
      true
    proc b2(a, b: bool): bool = a
    if b2(A in s, ch()) and j == 1: symexTarget(astToStr(tg) & "_in_early")
    s = {A}
    if not b2(A in s, ch()) and j == 1: symexTarget(astToStr(tg) & "_in_late")
  proc `inLit tg`(j: int) =
    # A literal's elements are compared inline, not built (`k` read late).
    var k = A
    proc ch(): bool =
      k = B
      true
    proc b2(a, b: bool): bool = a
    if b2(A in {k, X}, ch()) and j == 1: symexTarget(astToStr(tg) & "_il_early")
    k = A
    if not b2(A in {k, X}, ch()) and j == 1: symexTarget(astToStr(tg) & "_il_late")
  proc `cardInner tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): int =
      s = {B, C}
      1
    proc i2(a, b: int): int = a
    if i2(card(s + {X}), ch()) == 2 and j == 1: symexTarget(astToStr(tg) & "_card_early")
    s = {A}
    if i2(card(s + {X}), ch()) == 3 and j == 1: symexTarget(astToStr(tg) & "_card_late")
  proc `cardBare tg`(j: int) =
    var s: set[T] = {A}
    proc ch(): int =
      s = {B, C}
      1
    proc i2(a, b: int): int = a
    if i2(card(s), ch()) == 1 and j == 1: symexTarget(astToStr(tg) & "_cb_early")
    s = {A}
    if i2(card(s), ch()) == 2 and j == 1: symexTarget(astToStr(tg) & "_cb_late")
  proc `ctorEager tg`(j: int) =
    var k = A
    proc ch(): bool =
      k = B
      true
    proc f2(a: set[T]; b: bool): set[T] = a
    let r = f2({k}, ch())
    if A in r and j == 1: symexTarget(astToStr(tg) & "_ct_early")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_ct_late")
  proc `elemEagerSetLazy tg`(j: int) =
    var s: set[T] = {A}
    var k = A
    proc ch(): bool =
      s = {B, C}
      k = B
      true
    proc f2(a: set[T]; b: bool): set[T] = a
    let r = f2(s + {k}, ch())
    if A in r and j == 1: symexTarget(astToStr(tg) & "_es_a")
    if B in r and j == 1: symexTarget(astToStr(tg) & "_es_b")
    if C in r and j == 1: symexTarget(astToStr(tg) & "_es_c")

orderSuts(Sm, Sm(1), Sm(2), Sm(3), Sm(4), sm)
orderSuts(Md, Md(1), Md(2), Md(3), Md(4), md)
orderSuts(Mx, Mx(1), Mx(2), Mx(3), Mx(4), mx)
orderSuts(uint8, 1'u8, 2'u8, 3'u8, 4'u8, by)

template orderPins(tag: static string; big: static bool;
                   unionN, compareT, eqL, inL, inLt, cardI, cardB, ctor, es: untyped) =
  test "nim: " & tag:
    symexCaptureBegin()
    unionN(1); compareT(1); eqL(1); inL(1); inLt(1); cardI(1); cardB(1); ctor(1); es(1)
    let hit = symexCaptureEnd()
    check (tag & "_u_early" in hit) == big
    check (tag & "_u_late" in hit) == not big
    check (tag & "_le_early" in hit) == big
    check (tag & "_le_late" in hit) == not big
    check tag & "_eq_early" notin hit
    check tag & "_eq_late" in hit
    check tag & "_in_early" notin hit
    check tag & "_in_late" in hit
    check tag & "_il_early" notin hit
    check tag & "_il_late" in hit
    check (tag & "_card_early" in hit) == big
    check (tag & "_card_late" in hit) == not big
    check tag & "_cb_early" notin hit
    check tag & "_cb_late" in hit
    check tag & "_ct_early" in hit
    check tag & "_ct_late" notin hit
    check (tag & "_es_a" in hit) == true
    check (tag & "_es_b" in hit) == not big
    check (tag & "_es_c" in hit) == not big

  test "walker agrees: " & tag:
    template early(c: bool; fn: typed; lbl: string) =
      if c: reached(fn, lbl) else: dead(fn, lbl)
    early(big, unionN, tag & "_u_early")
    early(not big, unionN, tag & "_u_late")
    early(big, compareT, tag & "_le_early")
    early(not big, compareT, tag & "_le_late")
    early(false, eqL, tag & "_eq_early")
    early(true, eqL, tag & "_eq_late")
    early(false, inL, tag & "_in_early")
    early(true, inL, tag & "_in_late")
    early(false, inLt, tag & "_il_early")
    early(true, inLt, tag & "_il_late")
    early(big, cardI, tag & "_card_early")
    early(not big, cardI, tag & "_card_late")
    early(false, cardB, tag & "_cb_early")
    early(true, cardB, tag & "_cb_late")
    early(true, ctor, tag & "_ct_early")
    early(false, ctor, tag & "_ct_late")
    early(true, es, tag & "_es_a")
    early(not big, es, tag & "_es_b")
    early(not big, es, tag & "_es_c")

suite "S8cd item 4: where Nim reads a set expression":
  orderPins("sm", false, unionNestedsm, compareTempsm, eqLazysm, inLazysm, inLitsm,
            cardInnersm, cardBaresm, ctorEagersm, elemEagerSetLazysm)
  orderPins("md", false, unionNestedmd, compareTempmd, eqLazymd, inLazymd, inLitmd,
            cardInnermd, cardBaremd, ctorEagermd, elemEagerSetLazymd)
  orderPins("mx", true, unionNestedmx, compareTempmx, eqLazymx, inLazymx, inLitmx,
            cardInnermx, cardBaremx, ctorEagermx, elemEagerSetLazymx)
  orderPins("by", true, unionNestedby, compareTempby, eqLazyby, inLazyby, inLitby,
            cardInnerby, cardBareby, ctorEagerby, elemEagerSetLazyby)

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
    check parseInt(symexWalkerVersion) >= 244
