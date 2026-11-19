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
##
## The remaining shapes (second table; same toolchains and builds): a dead
## value through a local, a dead result forwarded through a further call, a
## formal the callee uses only in a dead way, a field of an object `result`.
##
## ==========================================  =========  ===========
## form                                        default    -d:release
## ==========================================  =========  ===========
## `discard rdLocal(p)` (`let v = p.n;         SIGSEGV    returns
## result = v`)
## `discard rdLocalRet(p)` (`let v = p.n; v`)  SIGSEGV    returns
## `localUnused(p)` (`let v = p.n` unused)     SIGSEGV    returns
## `discard outerRd(p)` (`= rd(p)`)            SIGSEGV    returns
## `discard outerRdAsgn(p)` (`result =         SIGSEGV    returns
## rd(p)`)
## `discard outerLocal(p)` (`let v = rd(p);    SIGSEGV    returns
## result = v`)
## unused `let x = outerRd(p)`                 SIGSEGV    returns
## `discFormal(p.n)` (`discard x`)             SIGSEGV    returns
## `letFormal(p.n)` (`let y = x` unused)       SIGSEGV    returns
## `discard mkR(p)` (`result.a = p.n`)         SIGSEGV    returns
## `mkR2(p).b == 1` (`result.a = p.n;          SIGSEGV    returns
## result.b = 1`)
## `outerRd(p) > 0` (used)                     SIGSEGV    SIGSEGV
## `rdLocal(p) > 0` (used)                     SIGSEGV    SIGSEGV
## `discard rdLocalUse(p)` (branches on `v`)   SIGSEGV    SIGSEGV
## `letFormalUse(p.n)` (`y` is stored)         SIGSEGV    SIGSEGV
## `discard mkRUse(p)` (branches on            SIGSEGV    SIGSEGV
## `result.a`)
## `mkR(p).a == 1` (the field read)            SIGSEGV    SIGSEGV
## ==========================================  =========  ===========
##
## One summary covers them (`onlyDeadUses`): a value is dead when every
## place it reaches is: a `discard`, a local whose own uses are dead, a
## by-value formal its callee uses only so, or a part of `result` the caller
## does not read (the whole, or the other fields of an object result:
## `#resultdead:<fields read>`); a call forwarded into such a result is a
## call of whose value the same part is read.
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

type
  R = object
    a: int
    b: int

# INT-92 (remaining shapes): a dead value through a local, a forwarded call,
# a formal named only in a dead way, a field of an object `result`.
proc rdLocal(p: ref B): int =
  let v = p.n
  result = v
proc rdLocalRet(p: ref B): int =
  let v = p.n
  v
proc localUnused(p: ref B) =
  let v = p.n
proc outerRd(p: ref B): int = rd(p)
proc outerRdAsgn(p: ref B): int =
  result = rd(p)
proc outerLocal(p: ref B): int =
  let v = rd(p)
  result = v
proc discFormal(x: int) = discard x
proc letFormal(x: int) =
  let y = x
proc mkR(p: ref B): R =
  result.a = p.n
proc mkR2(p: ref B): R =
  result.a = p.n
  result.b = 1
proc rdLocalUse(p: ref B): int =
  let v = p.n
  if v > 5: sideSink = 1
  result = v
proc letFormalUse(x: int) =
  let y = x
  sideSink = y
proc mkRUse(p: ref B): R =
  result.a = p.n
  if result.a > 5: sideSink = 1

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

proc discardRdLocal(p: ref B) =
  if p == nil:
    discard rdLocal(p)
    symexTarget("after")

proc discardRdLocalRet(p: ref B) =
  if p == nil:
    discard rdLocalRet(p)
    symexTarget("after")

proc localUnusedCall(p: ref B) =
  if p == nil:
    localUnused(p)
    symexTarget("after")

proc discardOuterRd(p: ref B) =
  if p == nil:
    discard outerRd(p)
    symexTarget("after")

proc discardOuterRdAsgn(p: ref B) =
  if p == nil:
    discard outerRdAsgn(p)
    symexTarget("after")

proc discardOuterLocal(p: ref B) =
  if p == nil:
    discard outerLocal(p)
    symexTarget("after")

proc deadOuterRd(p: ref B) =
  if p == nil:
    let x = outerRd(p)
    symexTarget("after")

proc discFormalArg(p: ref B) =
  if p == nil:
    discFormal(p.n)
    symexTarget("after")

proc letFormalArg(p: ref B) =
  if p == nil:
    letFormal(p.n)
    symexTarget("after")

proc discardMkR(p: ref B) =
  if p == nil:
    discard mkR(p)
    symexTarget("after")

proc mkR2OtherField(p: ref B) =
  if p == nil:
    if mkR2(p).b == 1: sideSink = 2
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

proc usedOuterRd(p: ref B) =
  if p == nil:
    if outerRd(p) > 0: sideSink = 2
    symexTarget("after")

proc usedRdLocal(p: ref B) =
  if p == nil:
    if rdLocal(p) > 0: sideSink = 2
    symexTarget("after")

proc discardRdLocalUse(p: ref B) =
  if p == nil:
    discard rdLocalUse(p)
    symexTarget("after")

proc letFormalUseArg(p: ref B) =
  if p == nil:
    letFormalUse(p.n)
    symexTarget("after")

proc discardMkRUse(p: ref B) =
  if p == nil:
    discard mkRUse(p)
    symexTarget("after")

proc mkRField(p: ref B) =
  if p == nil:
    if mkR(p).a == 1: sideSink = 2
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

proc outerLocalSome(p: ref B) =
  if p != nil:
    if outerLocal(p) == 7: symexTarget("seven")

proc mkR2Some(p: ref B) =
  if p != nil:
    if mkR2(p).b == 1: symexTarget("after")

proc mkRFieldSome(p: ref B) =
  if p != nil:
    if mkR(p).a == 7: symexTarget("seven")

proc letFormalSome(p: ref B) =
  if p != nil:
    letFormal(p.n)
    symexTarget("after")

proc discardOuterRdSome(p: ref B) =
  if p != nil:
    discard outerRd(p)
    symexTarget("after")

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
  of "discardRdLocal": discardRdLocal(nil)
  of "discardRdLocalRet": discardRdLocalRet(nil)
  of "localUnusedCall": localUnusedCall(nil)
  of "discardOuterRd": discardOuterRd(nil)
  of "discardOuterRdAsgn": discardOuterRdAsgn(nil)
  of "discardOuterLocal": discardOuterLocal(nil)
  of "deadOuterRd": deadOuterRd(nil)
  of "discFormalArg": discFormalArg(nil)
  of "letFormalArg": letFormalArg(nil)
  of "discardMkR": discardMkR(nil)
  of "mkR2OtherField": mkR2OtherField(nil)
  of "usedOuterRd": usedOuterRd(nil)
  of "usedRdLocal": usedRdLocal(nil)
  of "discardRdLocalUse": discardRdLocalUse(nil)
  of "letFormalUseArg": letFormalUseArg(nil)
  of "discardMkRUse": discardMkRUse(nil)
  of "mkRField": mkRField(nil)
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

suite "INT-92: a dead value through a local, a call, a formal or a field":
  test "natively, in this (unoptimised) build, each crashes":
    # Under `-d:release` each returns instead (the second table).
    pinCrashSelf(keyOf("discardRdLocal"), "discardRdLocal", ceSegv)
    pinCrashSelf(keyOf("discardRdLocalRet"), "discardRdLocalRet", ceSegv)
    pinCrashSelf(keyOf("localUnusedCall"), "localUnusedCall", ceSegv)
    pinCrashSelf(keyOf("discardOuterRd"), "discardOuterRd", ceSegv)
    pinCrashSelf(keyOf("discardOuterRdAsgn"), "discardOuterRdAsgn", ceSegv)
    pinCrashSelf(keyOf("discardOuterLocal"), "discardOuterLocal", ceSegv)
    pinCrashSelf(keyOf("deadOuterRd"), "deadOuterRd", ceSegv)
    pinCrashSelf(keyOf("discFormalArg"), "discFormalArg", ceSegv)
    pinCrashSelf(keyOf("letFormalArg"), "letFormalArg", ceSegv)
    pinCrashSelf(keyOf("discardMkR"), "discardMkR", ceSegv)
    pinCrashSelf(keyOf("mkR2OtherField"), "mkR2OtherField", ceSegv)

  test "the walker claims neither side: the nil path declines":
    declines(discardRdLocal)
    declines(discardRdLocalRet)
    declines(localUnusedCall)
    declines(discardOuterRd)
    declines(discardOuterRdAsgn)
    declines(discardOuterLocal)
    declines(deadOuterRd)
    declines(discFormalArg)
    declines(letFormalArg)
    declines(discardMkR)
    declines(mkR2OtherField)

  test "natively, a live one crashes under every build":
    pinCrashSelf(keyOf("usedOuterRd"), "usedOuterRd", ceSegv)
    pinCrashSelf(keyOf("usedRdLocal"), "usedRdLocal", ceSegv)
    pinCrashSelf(keyOf("discardRdLocalUse"), "discardRdLocalUse", ceSegv)
    pinCrashSelf(keyOf("letFormalUseArg"), "letFormalUseArg", ceSegv)
    pinCrashSelf(keyOf("discardMkRUse"), "discardMkRUse", ceSegv)
    pinCrashSelf(keyOf("mkRField"), "mkRField", ceSegv)

  test "the walker claims a live one, before the label":
    for r in [symexFind(usedOuterRd, tNilAccess()),
              symexFind(usedRdLocal, tNilAccess()),
              symexFind(discardRdLocalUse, tNilAccess()),
              symexFind(letFormalUseArg, tNilAccess()),
              symexFind(discardMkRUse, tNilAccess()),
              symexFind(mkRField, tNilAccess()),
              symexFind(usedOuterRd, tLabel("after")),
              symexFind(usedRdLocal, tLabel("after")),
              symexFind(discardRdLocalUse, tLabel("after")),
              symexFind(letFormalUseArg, tLabel("after")),
              symexFind(discardMkRUse, tLabel("after")),
              symexFind(mkRField, tLabel("after"))]:
      check r.status == sxRaised

  test "off the nil path the values and the label are the ordinary ones":
    check pinFind(outerLocalSome, tLabel("seven")).status == sxSat
    check pinFind(mkR2Some, tLabel("after")).status == sxSat
    check pinFind(mkRFieldSome, tLabel("seven")).status == sxSat
    check pinFind(letFormalSome, tLabel("after")).status == sxSat
    check pinFind(discardOuterRdSome, tLabel("after")).status == sxSat

suite "INT-92: the walker's version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 453
