## RFC-0005 (soundness channels) slice S8be -- S8ax's remainder.
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

# ---- (9) a returned tuple of closures ----------------------------------------
#
# DECLINE before S8be (`ceUnsupportedHof`): a routine returning a tuple of
# closures sharing one capture. A closure called through a tuple field
# (`t.f()`) did not compile ("cannot resolve callee `t.f`").

proc s8bePair(start: int): (proc(): int, proc(): int) =
  var c = start
  result = (proc(): int =
              c += 1
              c,
            proc(): int = c)

proc sutCloTuple(v: int) =
  symexAssume(v > -100 and v < 100)
  let (inc1, get1) = s8bePair(v)
  discard inc1()
  if get1() == v + 1: symexTarget("ok")
  if get1() != v + 1: symexTarget("bad")

proc s8beTriple(start: int): tuple[n: int, f: proc(): int] =
  var c = start
  (n: start * 2, f: proc(): int =
                      c += 3
                      c)

proc sutCloNamed(v: int) =
  symexAssume(v > -100 and v < 100)
  let t = s8beTriple(v)
  let a = t.f()
  discard t.f()
  if a == v + 3 and t.f() == v + 9 and t.n == 2 * v: symexTarget("ok")
  if a != v + 3 or t.n != 2 * v: symexTarget("bad")

# ---- (10) an opaque routine applying a closure -------------------------------
#
# WRONG VERDICT before S8be: an opaque routine handed a closure kept the
# closure's captures unchanged, so `x == v + 1` after it applied the
# closure was a false `sxUnsat`.

proc s8beApplyOpaque(f: proc(): int) {.symexOpaque.} =
  discard f()

proc sutOpaqueClo(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  s8beApplyOpaque(f)
  if x == v + 1: symexTarget("moved")

# ---- (11) the call cache under capture cells ---------------------------------
#
# A routine reading a capture or a global is cached keyed by their values
# as it found them; one that writes one is not cached. Before S8be such a
# frame bypassed the cache (cost, not soundness); these pins guard the
# staleness the key must rule out.

proc s8beFib(k: int): int =
  if k < 2: k else: s8beFib(k - 1) + s8beFib(k - 2)

proc sutCacheCap(n: int) =
  symexAssume(n >= 0 and n <= 6)
  var c = 0
  let bump = proc() = c += 1
  bump()
  if s8beFib(n) + c == 9: symexTarget("hit")

proc sutCapStale(v: int) =
  symexAssume(v >= 0 and v < 10)
  var c = v
  proc rd(): int = c * 2
  let a = rd()
  c = c + 1
  let b = rd()
  if b == a + 2: symexTarget("ok")
  if b != a + 2: symexTarget("bad")

var s8beG = 0
proc s8beRdG(k: int): int = s8beG + k

proc sutGlobStale(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8beG = v
  let a = s8beRdG(1)
  s8beG = v + 5
  let b = s8beRdG(1)
  if b == a + 5: symexTarget("ok")
  if b != a + 5: symexTarget("bad")

var s8beCnt = 0
proc s8beTick(k: int): int =
  s8beCnt += 1
  k

proc sutGlobWrite(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8beCnt = 0
  discard s8beTick(1)
  discard s8beTick(1)
  if s8beCnt == 2: symexTarget("ok")
  if s8beCnt != 2: symexTarget("bad")

# ---- (12) an element's address as a value; a case object's address ----------
#
# DECLINE before S8be: `addr s[i]` of a seq whose pointer is compared,
# stored, returned, or whose index variable is reassigned while it lives
# (`feUnsupportedExprKind`, `heUnsafeCast`); `addr o` of a case object
# (`feUnsupportedOp`); `addr o.a` of an arm field (`heUnsafeCast`). The
# element's cell is identified by the seq and the index as `addr`
# evaluated it, and dies when the seq is resized (Nim may move it).

proc sutElemPtrCompare(v: int) =
  var s = @[1, v, 3]
  let p = addr s[1]
  let q = addr s[1]
  let r = addr s[0]
  if p == q and p != r: symexTarget("ok")
  if p != q or p == r: symexTarget("bad")

proc s8beRetP(p: ptr int): ptr int = p

proc sutElemPtrReturned(v: int) =
  var s = @[1, v, 3]
  let p = s8beRetP(addr s[1])
  p[] = 9
  if s[1] == 9: symexTarget("ok")
  if s[1] != 9: symexTarget("bad")

type S8bePBox = object
  p: ptr int

proc sutElemPtrStored(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  b.p[] = 9
  if s[1] == 9: symexTarget("ok")
  if s[1] != 9: symexTarget("bad")

proc sutElemPtrIdxMoved(v: int) =
  var s = @[1, v, 3]
  var i = 1
  let p = addr s[i]
  i = 2
  p[] = 9
  if s[1] == 9 and s[2] == 3: symexTarget("ok")
  if s[1] != 9 or s[2] != 3: symexTarget("bad")

proc sutElemPtrIdxMovedCmp(v: int) =
  var s = @[1, v, 3]
  var i = 1
  let p = addr s[i]
  i = 2
  let q = addr s[i]
  if p != q: symexTarget("ok")
  if p == q: symexTarget("bad")

proc sutElemPtrWriteBack(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  s[1] = 4
  if b.p[] == 4: symexTarget("ok")
  if b.p[] != 4: symexTarget("bad")

proc s8beRetElem(s: var seq[int]; i: int): ptr int = addr s[i]

proc sutElemPtrFromCallee(v: int) =
  var s = @[1, v, 3]
  let p = s8beRetElem(s, 2)
  p[] = 9
  if s[2] == 9: symexTarget("ok")
  if s[2] != 9: symexTarget("bad")

proc sutElemPtrResized(v: int) =
  var s = @[1, v, 3]
  var b = S8bePBox(p: addr s[1])
  s.add 4
  b.p[] = 9
  if s[1] == 9: symexTarget("ok")

proc sutElemPtrOob(i: int) =
  var s = @[1, 2, 3]
  symexAssume(i >= 3 and i < 10)
  var b = S8bePBox(p: addr s[i])
  discard b

type
  S8beK = enum kA, kB
  S8beV = object
    case k: S8beK
    of kA: a: int
    of kB: b: int

proc s8beSetV(p: ptr S8beV) =
  p.a = 7

proc sutVariantAddrCall(v: int) =
  var o = S8beV(k: kA, a: v)
  s8beSetV(addr o)
  if o.a == 7: symexTarget("ok")
  if o.a != 7: symexTarget("bad")

proc sutVariantFieldAddr(v: int) =
  var o = S8beV(k: kA, a: v)
  let p = addr o.a
  p[] = 5
  if o.a == 5: symexTarget("ok")
  if o.a != 5: symexTarget("bad")

proc sutVariantFieldRearm(v: int) =
  var o = S8beV(k: kA, a: v)
  let p = addr o.a
  o = S8beV(k: kB, b: 3)
  if p[] == 3: symexTarget("ok")

# ---- (13) the call-depth decline names its budget ----------------------------

proc s8beDown(k: int): bool =
  if k <= 0: true else: s8beDown(k - 1)

proc sutDownFree(n: int) =
  if s8beDown(n) and n == 50: symexTarget("dd")

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

suite "RFC-0005 S8be (9): a returned tuple of closures":
  test "an unnamed tuple":
    verdict(sutCloTuple, tLabel("ok"), sxSat)
    verdict(sutCloTuple, tLabel("bad"), sxUnsat)
  test "a named tuple, the closure called through its field":
    verdict(sutCloNamed, tLabel("ok"), sxSat)
    verdict(sutCloNamed, tLabel("bad"), sxUnsat)

suite "RFC-0005 S8be (10): an opaque routine applying a closure":
  test "the closure's captures are havocked":
    verdict(sutOpaqueClo, tLabel("moved"), sxSat)

suite "RFC-0005 S8be (11): the call cache under capture cells":
  test "a recursion under a frame with a capture cell":
    verdictS(sutCacheCap, tLabel("hit"), sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 8,
                                                  maxRecursionDepth: 0)))
  test "a capture read after a write is read again":
    verdict(sutCapStale, tLabel("ok"), sxSat)
    verdict(sutCapStale, tLabel("bad"), sxUnsat)
  test "a global read after a write is read again":
    verdict(sutGlobStale, tLabel("ok"), sxSat)
    verdict(sutGlobStale, tLabel("bad"), sxUnsat)
  test "a call writing a global is walked each time":
    verdict(sutGlobWrite, tLabel("ok"), sxSat)
    verdict(sutGlobWrite, tLabel("bad"), sxUnsat)

suite "RFC-0005 S8be (12): an element's address as a value":
  test "compared":
    verdict(sutElemPtrCompare, tLabel("ok"), sxSat)
    verdict(sutElemPtrCompare, tLabel("bad"), sxUnsat)
  test "returned through a callee":
    verdict(sutElemPtrReturned, tLabel("ok"), sxSat)
    verdict(sutElemPtrReturned, tLabel("bad"), sxUnsat)
  test "stored in an object":
    verdict(sutElemPtrStored, tLabel("ok"), sxSat)
    verdict(sutElemPtrStored, tLabel("bad"), sxUnsat)
  test "a write by name seen through the pointer":
    verdict(sutElemPtrWriteBack, tLabel("ok"), sxSat)
    verdict(sutElemPtrWriteBack, tLabel("bad"), sxUnsat)
  test "the index variable reassigned while the pointer lives":
    verdict(sutElemPtrIdxMoved, tLabel("ok"), sxSat)
    verdict(sutElemPtrIdxMoved, tLabel("bad"), sxUnsat)
    verdict(sutElemPtrIdxMovedCmp, tLabel("ok"), sxSat)
    verdict(sutElemPtrIdxMovedCmp, tLabel("bad"), sxUnsat)
  test "taken by a callee of its var formal":
    verdict(sutElemPtrFromCallee, tLabel("ok"), sxSat)
    verdict(sutElemPtrFromCallee, tLabel("bad"), sxUnsat)
  test "used after a resize declines":
    declines(sutElemPtrResized, tLabel("ok"), feUnsupportedOp, "S8be")
  test "the index is checked where `addr` takes it":
    verdict(sutElemPtrOob, tRaisedExn("IndexDefect"), sxRaised)

suite "RFC-0005 S8be (12): a case object's address":
  test "passed to a routine writing an arm field":
    verdict(sutVariantAddrCall, tLabel("ok"), sxSat)
    verdict(sutVariantAddrCall, tLabel("bad"), sxUnsat)
  test "an arm field's address":
    verdict(sutVariantFieldAddr, tLabel("ok"), sxSat)
    verdict(sutVariantFieldAddr, tLabel("bad"), sxUnsat)
  test "an arm field's pointer after the object changes arm declines":
    declines(sutVariantFieldRearm, tLabel("ok"), feUnsupportedOp, "another arm")

suite "RFC-0005 S8be (13): the call-depth decline":
  test "names the budget":
    let r = symexFind(sutDownFree, tLabel("dd"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check "maxCallDepth" in show(r.errors)
