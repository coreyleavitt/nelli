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
##
## 3. (INT-89's remnants, walker 450) A view handed on WITHOUT the hidden
##    address wrapper. `lent` is emitted as `var` is (`NI* lentN(...)`
##    returns `&(*p).n`; a 64-word object's `lent` too: an address, never a
##    copy). Natively, through a nil `ref` (gcc and g++, c and cpp; the
##    default build, `-d:release`, `-d:danger`):
##      * returns at every level: `discard fwdV(nil)` and `discard
##        fwdL(nil)` (a view of a view), `discard lentN(nil)`,
##        `noRead(varN(nil))` and `discard noReadRet(varN(nil))` (a `var`
##        formal takes the address), `let a = addr varN(nil)`, `discard
##        addr varN(nil)`, `discard unsafeAddr lentN(nil)`;
##      * faults at every level: `varN(nil).inc`, `varN(nil) = 3`,
##        `swap(varN(nil), y)`, a used `doRead(varN(nil))`, a used
##        `lentN(nil)`;
##      * the optimiser's (faults at `-O0`, returns at `-O2`): an unused
##        `let x = varN(nil)` / `lentN(nil)`, `discard doRead(varN(nil))`
##        (the callee's read is dead once inlined), `noReadL(lentN(nil))`.
##    The walker: a view of a view and a discarded `lent` are the address
##    (`#viewaddr`); a dead local's copy is the optimiser's (`#viewdead`, a
##    nil on the location declines); a view handed to a `var` formal is its
##    address, then the call declines (the write-back is not modelled), so
##    the callee's read or not is never claimed; the rest decline by name.
## 4. MSVC: whether `cl` at `/Od` (Nim's default build under `--cc:vcc`)
##    also drops `(void)((*p).n);` and `(void)(*T1_);` is asked of this
##    binary on the `fuzzer-msvc` walker leg (a form run in a child that must
##    return); no local route runs `cl`.
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
proc fwdV(p: ref B): var int = varN(p)
proc fwdL(p: ref B): lent int = lentN(p)
proc noRead(x: var int) = discard
proc doRead(x: var int): int = x
proc noReadRet(x: var int): var int = x
proc noReadL(x: int) = discard

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

proc discardFwd(p: ref B) =
  if p == nil:
    discard fwdV(p)
    symexTarget("after")

proc discardFwdL(p: ref B) =
  if p == nil:
    discard fwdL(p)
    symexTarget("after")

proc varArgNoRead(p: ref B) =
  if p == nil:
    noRead(varN(p))
    symexTarget("after")

proc varArgNoReadRet(p: ref B) =
  if p == nil:
    discard noReadRet(varN(p))
    symexTarget("after")

proc varArgRead(p: ref B) =
  if p == nil:
    if doRead(varN(p)) == 7: symexTarget("seven")
    symexTarget("after")

proc varArgReadDiscard(p: ref B) =
  if p == nil:
    discard doRead(varN(p))
    symexTarget("after")

proc addrOfVar(p: ref B) =
  if p == nil:
    let a = addr varN(p)
    symexTarget("after")

proc incVar(p: ref B) =
  if p == nil:
    varN(p).inc
    symexTarget("after")

proc storeVar(p: ref B) =
  if p == nil:
    varN(p) = 3
    symexTarget("after")

proc usedLent(p: ref B) =
  if p == nil:
    if lentN(p) == 7: symexTarget("seven")
    symexTarget("after")

proc lentByValue(p: ref B) =
  if p == nil:
    noReadL(lentN(p))
    symexTarget("after")

proc deadVar(p: ref B) =
  if p == nil:
    let x = varN(p)
    symexTarget("after")

proc deadLent(p: ref B) =
  if p == nil:
    let x = lentN(p)
    symexTarget("after")

proc deadVarSome(p: ref B) =
  if p != nil:
    let x = varN(p)
    symexTarget("after")

proc discardLentSome(p: ref B) =
  if p != nil:
    discard lentN(p)
    symexTarget("after")

# MSVC `/Od` probe forms (every one returns on gcc and g++ at every level).
proc msvcField(p: ref B) = discard p.n
proc msvcDeref(p: ref B) = discard p[]

crashForms:
  case crashForm()
  of "keptVar": discard keptVar(nil)
  of "discardVarLoad": discardVarLoad(nil)
  of "deadArrIdx": deadArrIdx(nil, 1)
  of "varArgRead": varArgRead(nil)
  of "varArgReadDiscard": varArgReadDiscard(nil)
  of "incVar": incVar(nil)
  of "storeVar": storeVar(nil)
  of "usedLent": usedLent(nil)
  of "lentByValue": lentByValue(nil)
  of "deadVar": deadVar(nil)
  of "deadLent": deadLent(nil)
  of "msvcField": msvcField(nil)
  of "msvcDeref": msvcDeref(nil)
  of "msvcVar": discardVar(nil)
  of "msvcLent": discardLent(nil)
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

  test "a `lent` result of the same shape is an address too":
    check pinFind(discardLent, tLabel("after")).status == sxSat
    check pinFind(discardLent, tNilAccess()).status == sxUnsat
    check pinFind(discardLentSome, tLabel("after")).status == sxSat

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

template declines(f: untyped) =
  ## Both the label and the nil access: a named decline, recorded through
  ## `pinDecline` (K9b: a kind-naming decline is never a local template).
  pinDecline(f, keyOf(astToStr(f)), feUnsupportedOp, tLabel("after"))
  pinDecline(f, keyOf(astToStr(f)), feUnsupportedOp, tNilAccess())

suite "INT-89: a view handed on without the address wrapper":
  test "natively: an address handed on reads nothing":
    check nativeRun(discardFwd(nil)).hitsTarget(tLabel("after"))
    check nativeRun(discardFwdL(nil)).hitsTarget(tLabel("after"))
    check nativeRun(varArgNoRead(nil)).hitsTarget(tLabel("after"))
    check nativeRun(varArgNoReadRet(nil)).hitsTarget(tLabel("after"))
    check nativeRun(addrOfVar(nil)).hitsTarget(tLabel("after"))

  test "a view of a view is the address":
    check pinFind(discardFwd, tLabel("after")).status == sxSat
    check pinFind(discardFwd, tNilAccess()).status == sxUnsat
    check pinFind(discardFwdL, tLabel("after")).status == sxSat
    check pinFind(discardFwdL, tNilAccess()).status == sxUnsat

  test "a view handed to a `var` formal is its address; the call declines":
    # Natively the callee's own read decides: none returns at every level, a
    # used one faults at every level, a discarded one is the optimiser's.
    pinCrashSelf(keyOf("varArgRead"), "varArgRead", ceSegv)
    pinCrashSelf(keyOf("varArgReadDiscard"), "varArgReadDiscard", ceSegv)
    declines(varArgNoRead)
    declines(varArgNoReadRet)
    declines(varArgRead)
    declines(varArgReadDiscard)

  test "a dead local's copy of a view is the optimiser's: nil declines":
    pinCrashSelf(keyOf("deadVar"), "deadVar", ceSegv)
    pinCrashSelf(keyOf("deadLent"), "deadLent", ceSegv)
    declines(deadVar)
    declines(deadLent)
    check pinFind(deadVarSome, tLabel("after")).status == sxSat

  test "a write, a used `lent` and the rest decline or claim, never falsely":
    pinCrashSelf(keyOf("incVar"), "incVar", ceSegv)
    pinCrashSelf(keyOf("storeVar"), "storeVar", ceSegv)
    pinCrashSelf(keyOf("usedLent"), "usedLent", ceSegv)
    pinCrashSelf(keyOf("lentByValue"), "lentByValue", ceSegv)
    declines(incVar)
    declines(usedLent)
    declines(lentByValue)
    let s = symexFind(storeVar, tNilAccess())
    checkpoint $s.status & " " & show(s.errors)
    # A store through a view call is not modelled: a named decline.
    check s.status == sxUnknown
    check s.errors.named(feUnsupportedStmtKind)
    let a = symexFind(addrOfVar, tLabel("after"))
    checkpoint $a.status & " " & show(a.errors)
    check a.status == sxUnknown

suite "INT-89: the C compiler drops a discarded read at the build's level":
  # The INT-86 table's never-read class rests on the C compiler dropping
  # `(void)((*p).n);` and `(void)(*T1_);`. Established on gcc and g++; on the
  # `fuzzer-msvc` walker leg this asks `cl` at `/Od` (Nim's default build
  # under `--cc:vcc` passes no `/O`). A fault there makes the class
  # compiler-dependent.
  test "each discarded read through nil returns in a child":
    for form in ["msvcField", "msvcDeref", "msvcVar", "msvcLent"]:
      let r = runCrashForm(form)
      checkpoint form & ": rc=" & $r.rc & " timedOut=" & $r.timedOut &
                 "\n" & r.output
      check not r.timedOut
      check r.rc == 0
      check "NELLI_CRASH_FORM_RETURNED" in r.output

suite "INT-89: the walker's version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 450
