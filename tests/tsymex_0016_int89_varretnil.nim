## RFC-0016 INT-89 (soundness): what a discarded view costs natively.
##
## 1. A `var T` (or `lent T`) result naming a location through a nil `ref` is
##    an address, not a read. `proc varN(p: ref B): var int = p.n` is emitted
##    as `result = &(*p).n;` (address arithmetic, no load), and the caller's
##    `discard varN(p)` as `T = varN(p); (void)(*T);`, which the C compiler
##    drops. So `discard varN(nil)` returns and the label after it is reached
##    (pinned toolchain, gcc and g++, c and cpp; the default build,
##    `-d:release`, `-d:danger`, `--opt:none`). The walker walked the
##    callee's `result = p.n` as a read: `sxRaised(NilAccessDefect)`, the
##    label refuted. Only the callee's own reads count:
##      * an array index check in the address (`p.arr[i]`) runs under every
##        checked build and reads the index only: `IndexDefect` out of range,
##        nothing in range, whatever `p` is;
##      * a pointer the address is computed from (`p.q.n` loads `p.q`) is
##        loaded in the callee at `-O0` (SIGSEGV through a nil `p`) and dead
##        once the call is inlined at `-O2` (`-d:release` returns): the C
##        compiler's, so a nil there declines;
##      * a copy of the result (`result = varN(p)`) loads it and faults, as
##        the walker says.
## 2. `discard p.arr[i]` through a nil `ref`, the index a variable, emits
##    `if ((NU)(i) > 2) raiseIndexError2(i, 2); (void)((*p).arr[i]);`: the
##    check runs (against the array's static length) and the read is dropped.
##    In range it returns, out of range (`5`, `-1`) it raises `IndexDefect`,
##    in both cases with no nil access (c and cpp, default, `-d:release`,
##    `--opt:none`); under `-d:danger` there is no check and it returns. An
##    unused `let x = p.arr[i]` runs the same check, then its load is the
##    optimiser's (`-O0` faults, `-O2` returns): out of range raises, in range
##    declines.
## Found probing INT-86's class (K9d-12).
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  B = object
    n: int
    q: ref B
  A = object
    arr: array[3, int]

proc varN(p: ref B): var int = p.n
proc lentN(p: ref B): lent int = p.n
proc varQ(p: ref B): var int = p.q.n
proc varA(p: ref A; i: int): var int = p.arr[i]

proc discardVar(p: ref B) =
  if p == nil:
    discard varN(p)
    symexTarget("after")

proc discardLent(p: ref B) =
  if p == nil:
    discard lentN(p)
    symexTarget("after")

proc keptVar(p: ref B): int =
  if p == nil:
    result = varN(p)
    symexTarget("after")

proc discardVarLoad(p: ref B) =
  if p == nil:
    discard varQ(p)
    symexTarget("after")

proc discardVarIdx(p: ref A; i: int) =
  if p == nil:
    discard varA(p, i)
    symexTarget("after")

proc discardArrIdx(p: ref A; i: int) =
  if p == nil:
    discard p.arr[i]
    symexTarget("after")

proc deadArrIdx(p: ref A; i: int) =
  if p == nil:
    let x = p.arr[i]
    symexTarget("after")

proc deadArrIdxIn(p: ref A; i: int) =
  if p == nil and i >= 0 and i <= 2:
    let x = p.arr[i]
    symexTarget("after")

crashForms:
  case crashForm()
  of "keptVar": discard keptVar(nil)
  of "discardVarLoad": discardVarLoad(nil)
  of "deadArrIdx": deadArrIdx(nil, 1)
  else: discard

template keyOf(form: static string): CellKey =
  cellKey(faGeneric, "k9d/tsymex_0016_int89_varretnil/" & form & "/tNilAccess()")

suite "INT-89: a `var` result through nil is an address":
  test "natively: the discarded call returns and reaches the label":
    check nativeRun(discardVar(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardLent(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardVarIdx(nil, 1)).hitsTarget(tLabel("after"))

  test "natively: a copy of the result faults (the control)":
    pinCrashSelf(keyOf("keptVar"), "keptVar", ceSegv)

  test "the walker reaches the label and claims no nil access":
    check pinFind(discardVar, tLabel("after")).status == sxSat
    check pinFind(discardVar, tNilAccess()).status == sxUnsat

  test "a `lent` result of the same shape still declines (the by-value rule)":
    let a = symexFind(discardLent, tLabel("after"))
    checkpoint $a.status
    check a.status == sxUnknown
    check a.errors.named(feUnsupportedOp)

  test "the copied result is still a nil-access claim":
    check symexFind(keptVar, tNilAccess()).status == sxRaised
    check symexFind(keptVar, tLabel("after")).status == sxRaised

  test "an index check in the address runs, and reads the index only":
    check pinFind(discardVarIdx, tLabel("after")).status == sxSat
    check pinFind(discardVarIdx, tRaisedExn("IndexDefect")).status == sxRaised
    # The only raise on the nil path is the index check's.
    let n = symexFind(discardVarIdx, tNilAccess())
    check n.status == sxRaised
    check n.raisedTypeId.endsWith("IndexDefect")

  test "a pointer the address loads is the optimiser's: the nil path declines":
    # Natively, in this (unoptimised) build, it crashes; `-d:release`
    # returns (the probe table in the header).
    pinCrashSelf(keyOf("discardVarLoad"), "discardVarLoad", ceSegv)
    let a = symexFind(discardVarLoad, tLabel("after"))
    let b = symexFind(discardVarLoad, tNilAccess())
    checkpoint $a.status & " " & $b.status
    check a.status == sxUnknown
    check a.errors.named(feUnsupportedOp)
    check b.status == sxUnknown
    check b.errors.named(feUnsupportedOp)

suite "INT-89: a discarded array element at a variable index through nil":
  test "natively: in range it returns, out of range it raises IndexDefect":
    check nativeRun(discardArrIdx(nil, 1)).hitsTarget(tLabel("after"))
    check nativeRun(discardArrIdx(nil, 5)).hitsTarget(tRaisedExn("IndexDefect"))
    check nativeRun(discardArrIdx(nil, -1)).hitsTarget(tRaisedExn("IndexDefect"))

  test "the walker runs the index check and claims no nil access":
    check pinFind(discardArrIdx, tLabel("after")).status == sxSat
    check pinFind(discardArrIdx, tRaisedExn("IndexDefect")).status == sxRaised
    # The only raise on the nil path is the index check's.
    let n = symexFind(discardArrIdx, tNilAccess())
    check n.status == sxRaised
    check n.raisedTypeId.endsWith("IndexDefect")

  test "an unused local runs the check, then its load is the optimiser's":
    pinCrashSelf(keyOf("deadArrIdx"), "deadArrIdx", ceSegv)
    check nativeRun(deadArrIdx(nil, 5)).hitsTarget(tRaisedExn("IndexDefect"))
    check pinFind(deadArrIdx, tRaisedExn("IndexDefect")).status == sxRaised
    # In range, the nil path declines; the raise either search reports is
    # the out-of-range index's, never a nil access.
    let a = symexFind(deadArrIdx, tLabel("after"))
    let b = symexFind(deadArrIdx, tNilAccess())
    checkpoint $a.status & " " & $b.status
    for r in [a, b]:
      check r.status == sxRaised
      check r.raisedTypeId.endsWith("IndexDefect")
    let c = symexFind(deadArrIdxIn, tLabel("after"))
    let d = symexFind(deadArrIdxIn, tNilAccess())
    checkpoint $c.status & " " & $d.status
    for r in [c, d]:
      check r.status == sxUnknown
      check r.errors.named(feUnsupportedOp)

suite "INT-89: the walker's version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 449
