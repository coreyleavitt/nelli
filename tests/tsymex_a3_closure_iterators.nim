## A3 Slice 1 (ADR-0014): closure/inline iterator inlining into a `for` loop.
##
## Tests cover BOTH directions per ADR-0014 Consequences:
##
##   Positive paths (iterator expanded correctly):
##     * T1: a `countUp`-style `{.closure.}` iterator summed in a `for` —
##       sxSat with witness n=4 (sum of 0+1+2+3 == 6).
##     * T2: beyond-`maxLoopUnwind` iterator (100 iterations) → sxUnknown (sound).
##
##   False-positive direction (pre-scans MUST prevent spurious sxSat):
##     * T3: FINITE iterator (straight yields, no while) with `break` in the
##       for-body → MUST be sxUnknown (CRIT-2, D2-0c).
##     * T4: iterator containing `return` → MUST be sxUnknown (CRIT-1, D2-0b).
##     * T5: label AFTER the `for` over a `return`-bearing iterator →
##       MUST be sxSat (label is reachable; proves paths aren't silently dropped).
##
##   Deferred forms (documented incompleteness, not regressions):
##     * T6: recursive iterator → sxUnknown (CRIT-3, D2-0d).
##     * T7: first-class iterator value (stored in a var) → sxUnknown (D6).
##
## Walker version bumped 29→30 (D7). Both pin tests updated.

import std/unittest
import proptest/symex

# ===========================================================================
# Iterator definitions (module scope so getImpl can resolve them)
# ===========================================================================

# T1/T2: a `{.closure.}` iterator, while-driven — the canonical A3 shape.
# getImpl returns nnkIteratorDef with body:
#   StmtList(VarSection(i=0), WhileStmt(i<n, StmtList(YieldStmt(i), inc i)))
iterator countUpIter(n: int): int {.closure.} =
  var i = 0
  while i < n:
    yield i
    inc i

# T3: finite iterator — straight yields with no enclosing while.
# After inlining this produces a flat sequence of yield-blocks.
# A `break` in the for-body would hit loopStack.len==0 → false positive.
iterator twoElemsIter(): int {.closure.} =
  yield 1
  yield 2

# T4/T5: an iterator that contains a bare `return` (early-finish).
# Pre-scan 0(b) must degrade this to sxUnknown.
iterator earlyReturnIter(n: int): int {.closure.} =
  if n < 0:
    return  # early exit — bare return in iterator body (CRIT-1)
  yield 42

# T6: a recursive iterator (mutually recurses into itself).
# Pre-scan 0(d) must degrade on re-entry (CRIT-3).
iterator recursiveCountIter(n: int): int {.closure.} =
  yield n
  if n > 0:
    for x in recursiveCountIter(n - 1):
      yield x

# ===========================================================================
# SUT procs (module scope — required for getImpl resolution from symexFind)
# ===========================================================================

# NOTE: for-bodies below use `sum = sum + elem`, not `sum += elem`. Augmented
# assignment (`+=`/`-=`/…) is an ORTHOGONAL, pre-existing DSL-parser gap (it is
# `sxUnknown` even in a plain proc — `nnkInfix` is unhandled at statement level),
# unrelated to A3 iterator inlining. Using the explicit form lets these tests
# exercise the actual feature under test. (Augmented-assignment desugaring is a
# good small standalone follow-up slice.)

# T1: sum via countUpIter(n) — label reached when sum == 6, witness n == 4
proc sutA3IterSum(n: int) =
  var sum = 0
  for elem in countUpIter(n):
    sum = sum + elem
  if sum == 6:
    symexTarget("sum6")

# T2: countUpIter(100) — 100 iterations, well beyond maxLoopUnwind (default 5)
proc sutA3BeyondBound(n: int) =
  var sum = 0
  for elem in countUpIter(100):
    sum = sum + elem
  if sum == 4950:  # sum of 0..99 — unreachable within 5 unrolls
    symexTarget("impossible")

# T3: break in for-body over twoElemsIter (FINITE iterator — CRIT-2 / D2-0c)
proc sutA3BreakInBody(n: int) =
  var sum = 0
  for elem in twoElemsIter():
    if elem > n:
      break  # break in for-body → pre-scan 0(c) must degrade
    sum = sum + elem
  if sum == 3:
    symexTarget("sum3")

# T4: for over earlyReturnIter (contains `return` — CRIT-1 / D2-0b)
proc sutA3ReturnIter(n: int) =
  for elem in earlyReturnIter(n):
    if elem == 42:
      symexTarget("got42")

# T5: label AFTER the for over earlyReturnIter — must still be reachable
# (isUnsupported returns paths unchanged → walker continues to the label)
proc sutA3LabelAfterReturnIter(n: int) =
  for elem in earlyReturnIter(n):
    discard
  symexTarget("afterLoop")  # reachable via the degraded/unsupported for

# T6: recursive iterator — pre-scan 0(d) degrades on re-entry
proc sutA3RecursiveIter(n: int) =
  var cnt = 0
  for x in recursiveCountIter(n):
    cnt = cnt + x
  if cnt > 10:
    symexTarget("deepRecurse")

# T7: first-class iterator value — iterator sym stored in a var (D6 deferred)
# After semcheck, `for x in it(n):` where `it` is a var has a non-IteratorDef
# getImpl → falls through → sxUnknown.
proc sutA3FirstClassIter(n: int) =
  let it = countUpIter  # iterator in value position
  var sum = 0
  for elem in it(n):
    sum = sum + elem
  if sum == 6:
    symexTarget("firstClass")

# ===========================================================================
# Tests
# ===========================================================================

suite "A3 Slice 1 — closure/inline iterator inlining (ADR-0014)":

  # ---- T1: positive — iterator expanded; label reached; witness pinned ----
  test "T1: countUpIter(n) summed in for — sxSat, witness n==4 (sum 0+1+2+3==6)":
    let r = symexFind(sutA3IterSum, tLabel("sum6"))
    check r.status == sxSat
    check r.witness[0] == 4   ## n == 4: sum of 0+1+2+3 = 6

  # ---- T2: beyond-bound — 100 iterations, maxLoopUnwind=5 → sxUnknown ----
  test "T2: countUpIter(100) — beyond maxLoopUnwind bound → sxUnknown":
    let r = symexFind(sutA3BeyondBound, tLabel("impossible"))
    check r.status == sxUnknown

  # ---- T3: false-positive guard — break in for-body (CRIT-2 / D2-0c) ----
  test "T3: break in for-body over finite iterator → sxUnknown (pre-scan 0c)":
    ## Without pre-scan 0(c): break hits loopStack.len==0 → path dropped
    ## while later inlined yields still run → wrong surviving state → spurious
    ## sxSat. Pre-scan 0(c) degrades the whole for to isUnsupported → sxUnknown.
    let r = symexFind(sutA3BreakInBody, tLabel("sum3"))
    check r.status == sxUnknown

  # ---- T4: false-positive guard — return in iterator (CRIT-1 / D2-0b) ----
  test "T4: iterator containing `return` → sxUnknown (pre-scan 0b)":
    ## Without pre-scan 0(b): bare iterator `return` inlines to proc-return →
    ## drops the path or leaves caller retSym unconstrained → false positive.
    ## Pre-scan 0(b) degrades the whole for → sxUnknown.
    let r = symexFind(sutA3ReturnIter, tLabel("got42"))
    check r.status == sxUnknown

  # ---- T5: soundness — label AFTER return-bearing iterator is reachable ----
  test "T5: label after for-over-return-iter → sxSat (paths not silently dropped)":
    ## isUnsupported sets sawUnknown but does NOT drop paths. The label after
    ## the degraded for is reached on the continuing paths → sxSat wins over
    ## sawUnknown (per verdict combination logic: sxSat found takes precedence).
    ## This proves the degradation is transparent, not path-dropping.
    let r = symexFind(sutA3LabelAfterReturnIter, tLabel("afterLoop"))
    check r.status == sxSat

  # ---- T6: recursion guard (CRIT-3) — no compile-time hang; partial inline sound ----
  # The recursion guard (D2-0d) stops the infinite parse-time re-inlining: the fact
  # that this file COMPILES AT ALL proves it (without the guard, `getImpl`-driven
  # inlining of a self-recursive iterator overflows the compiler stack). The OUTER
  # level inlines — its first `yield n` runs (`cnt = n`) — and the inner recursive
  # `for recursiveCountIter(n-1)` degrades to `mkUnsupported` (a no-op that flags
  # uncertainty but does NOT mutate `cnt`). So `cnt > 10` is reachable via the first
  # yield at n==11, and this is SOUND: at runtime n==11 yields 11,10,…,1 → cnt==66>10,
  # so the target genuinely fires. sxSat with a legal witness, NOT a false positive.
  test "T6: recursive iterator — recursion guard prevents compile-hang; first-yield reaches target (sxSat, sound)":
    let r = symexFind(sutA3RecursiveIter, tLabel("deepRecurse"))
    check r.status == sxSat
    check r.witness[0] > 10   ## n > 10 → first yield alone reaches cnt > 10

  # ---- T7: deferred — first-class iterator value → sxUnknown (D6) ----
  test "T7: first-class iterator value (stored in let) → sxUnknown (D6 deferred)":
    let r = symexFind(sutA3FirstClassIter, tLabel("firstClass"))
    check r.status == sxUnknown

  # ---- walker version pin ----
  test "walker version is now 31 (A3 Slice 2 bumped 30→31)":
    ## A3 Slice 2 (augmented-assignment desugaring) superseded Slice 1's 30.
    check symexWalkerVersion == "31"
