## RFC-0016 INT-92 (soundness): INT-86's optimiser class across a call. A
## nil read whose value nothing live consumes was claimed a crash when the
## dead end is a call: `discard rd(nil)` (`rd(p: ref B): int = p.n`), an
## unused `let x = rd(nil)`, and `noReadL(p.n)` (a by-value argument the
## callee never names) were each `sxRaised(NilAccessDefect)`, the label
## behind them refuted. Natively each faults at `-O0` and returns at `-O2`:
## the call is inlined and the load is dead. A nil read is C undefined
## behaviour, which reliably faults only when its value is live.
##
## Native truth (pinned toolchain, gcc and g++, c and cpp; the default build
## and `-d:release`), each run on a nil `ref`:
##
## ====================================  =========  ===========
## form                                  default    -d:release
## ====================================  =========  ===========
## `discard rd(p)` (`= p.n`)             SIGSEGV    returns
## `discard rdAsgn(p)` (`result = p.n`)  SIGSEGV    returns
## `discard rdRet(p)` (`return p.n`)     SIGSEGV    returns
## `discard rdChain(p)` (`= p.q.n`)      SIGSEGV    returns
## `discard rdEffect(p)` (a store, then  SIGSEGV    returns
## `result = p.n`)
## unused `let x = rd(p)`                SIGSEGV    returns
## `noReadL(p.n)`                        SIGSEGV    returns
## `if rd(p) > 0: ...` (used result)     SIGSEGV    SIGSEGV
## `discard rdUse(p)` (reads `result`)   SIGSEGV    SIGSEGV
## `discard ctl(p)` (`if p.n > 0:` a     SIGSEGV    SIGSEGV
## store)
## `useArg(p.n)` (the formal is stored)  SIGSEGV    SIGSEGV
## ====================================  =========  ===========
##
## The walker claims a nil fault only for a read whose value is live; a
## read it can prove dead is the optimiser's, and a nil on it declines
## (`feUnsupportedOp`), as INT-86's dead locals do. The callee of a call
## whose result nothing reads is registered under `#resultdead`; if its body
## never reads `result`, a `result = E` (or `return E`, or the expression
## body) of a pure `E` through a `ref`/`ptr` is that dead read. A by-value
## actual whose formal the callee never names is one too.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  B = object
    n: int
    q: ref B

var sideSink: int

proc rd(p: ref B): int = p.n
proc rdAsgn(p: ref B): int =
  result = p.n
proc rdRet(p: ref B): int =
  return p.n
proc rdChain(p: ref B): int = p.q.n
proc rdEffect(p: ref B): int =
  sideSink = 3
  result = p.n
proc rdUse(p: ref B): int =
  result = p.n
  if result > 5: sideSink = 1
proc ctl(p: ref B): int =
  if p.n > 0: sideSink = 1
  0
proc noReadL(x: int) = discard
proc useArg(x: int) = sideSink = x

# -- dead: the optimiser's ---------------------------------------------------

proc discardRd(p: ref B) =
  if p == nil:
    discard rd(p)
    symexTarget("after")

proc discardRdAsgn(p: ref B) =
  if p == nil:
    discard rdAsgn(p)
    symexTarget("after")

proc discardRdRet(p: ref B) =
  if p == nil:
    discard rdRet(p)
    symexTarget("after")

proc discardRdChain(p: ref B) =
  if p == nil:
    discard rdChain(p)
    symexTarget("after")

proc discardRdEffect(p: ref B) =
  if p == nil:
    discard rdEffect(p)
    symexTarget("after")

proc deadRd(p: ref B) =
  if p == nil:
    let x = rd(p)
    symexTarget("after")

proc noReadArg(p: ref B) =
  if p == nil:
    noReadL(p.n)
    symexTarget("after")

# -- live: faults under every build ------------------------------------------

proc usedRd(p: ref B) =
  if p == nil:
    if rd(p) > 0: sideSink = 2
    symexTarget("after")

proc discardRdUse(p: ref B) =
  if p == nil:
    discard rdUse(p)
    symexTarget("after")

proc discardCtl(p: ref B) =
  if p == nil:
    discard ctl(p)
    symexTarget("after")

proc useArgRead(p: ref B) =
  if p == nil:
    useArg(p.n)
    symexTarget("after")

# -- non-nil controls ----------------------------------------------------------

proc discardRdSome(p: ref B) =
  if p != nil:
    discard rd(p)
    symexTarget("after")

proc noReadArgSome(p: ref B) =
  if p != nil:
    noReadL(p.n)
    symexTarget("after")

proc rdEffectSink(p: ref B) =
  if p != nil:
    discard rdEffect(p)
    if sideSink == 3: symexTarget("stored")

crashForms:
  case crashForm()
  of "discardRd": discardRd(nil)
  of "discardRdAsgn": discardRdAsgn(nil)
  of "discardRdRet": discardRdRet(nil)
  of "discardRdChain": discardRdChain(nil)
  of "discardRdEffect": discardRdEffect(nil)
  of "deadRd": deadRd(nil)
  of "noReadArg": noReadArg(nil)
  of "usedRd": usedRd(nil)
  of "discardRdUse": discardRdUse(nil)
  of "discardCtl": discardCtl(nil)
  of "useArgRead": useArgRead(nil)
  else: discard

template keyOf(form: static string): CellKey =
  cellKey(faGeneric, "k9d/tsymex_0016_int92_deadcallnil/" & form & "/tNilAccess()")

template declines(fn: untyped) =
  let a = symexFind(fn, tNilAccess())
  let b = symexFind(fn, tLabel("after"))
  checkpoint astToStr(fn) & ": " & $a.status & " " & $b.status
  check a.status == sxUnknown
  check a.errors.named(feUnsupportedOp)
  check b.status == sxUnknown
  check b.errors.named(feUnsupportedOp)

suite "INT-92: a nil read a call leaves dead is the optimiser's":
  test "natively, in this (unoptimised) build, each crashes":
    # Under `-d:release` each returns instead (the table in the header).
    pinCrashSelf(keyOf("discardRd"), "discardRd", ceSegv)
    pinCrashSelf(keyOf("discardRdAsgn"), "discardRdAsgn", ceSegv)
    pinCrashSelf(keyOf("discardRdRet"), "discardRdRet", ceSegv)
    pinCrashSelf(keyOf("discardRdChain"), "discardRdChain", ceSegv)
    pinCrashSelf(keyOf("discardRdEffect"), "discardRdEffect", ceSegv)
    pinCrashSelf(keyOf("deadRd"), "deadRd", ceSegv)
    pinCrashSelf(keyOf("noReadArg"), "noReadArg", ceSegv)

  test "the walker claims neither side: the nil path declines":
    declines(discardRd)
    declines(discardRdAsgn)
    declines(discardRdRet)
    declines(discardRdChain)
    declines(discardRdEffect)
    declines(deadRd)
    declines(noReadArg)

suite "INT-92: a nil read whose value is live faults":
  test "natively: each crashes under every build":
    pinCrashSelf(keyOf("usedRd"), "usedRd", ceSegv)
    pinCrashSelf(keyOf("discardRdUse"), "discardRdUse", ceSegv)
    pinCrashSelf(keyOf("discardCtl"), "discardCtl", ceSegv)
    pinCrashSelf(keyOf("useArgRead"), "useArgRead", ceSegv)

  test "the walker claims the nil access, before the label":
    check symexFind(usedRd, tNilAccess()).status == sxRaised
    check symexFind(discardRdUse, tNilAccess()).status == sxRaised
    check symexFind(discardCtl, tNilAccess()).status == sxRaised
    check symexFind(useArgRead, tNilAccess()).status == sxRaised
    check symexFind(usedRd, tLabel("after")).status == sxRaised
    check symexFind(discardRdUse, tLabel("after")).status == sxRaised
    check symexFind(discardCtl, tLabel("after")).status == sxRaised
    check symexFind(useArgRead, tLabel("after")).status == sxRaised

suite "INT-92: off the nil path nothing changes":
  test "the label and the callee's effect are reached":
    check pinFind(discardRdSome, tLabel("after")).status == sxSat
    check pinFind(noReadArgSome, tLabel("after")).status == sxSat
    check pinFind(rdEffectSink, tLabel("stored")).status == sxSat

suite "INT-92: the walker's version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 452
