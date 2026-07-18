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
##     * T5: label AFTER the `for` over a `return`-bearing iterator → the
##       degraded `for` does not DROP the path (`paths.len` is preserved), but
##       (SND-1, walker v38) it now taints the path `uncertain`, so a target
##       reached afterward correctly degrades to `sxUnknown` — see the T5 test
##       comment for the full soundness rationale.
##
##   Deferred forms (documented incompleteness, not regressions):
##     * T6: recursive iterator → sxUnknown (CRIT-3, D2-0d; also SND-1-tainted
##       post-drop, walker v38 — see the T6 test comment).
##     * T7: first-class iterator value (stored in a var) → sxUnknown (D6).
##
## Walker version bumped 29→30 (D7). Both pin tests updated.
## Walker version bumped 30→31 (A3-S2 augmented-assign). Pin tests updated.
## Walker version bumped 37→38 (SND-1: isUnsupported taints Path.uncertain).
## T5/T6 verdicts flip sxSat→sxUnknown (RFC-chapulin-hardening Cluster 1) — see
## their test comments; this is a soundness correction, not a regression.
## Walker version bumped 31→32 (A3-S2a tuple-yield). Pin tests updated.

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

# T8 (A3-S2a): iterator yielding EXPLICIT tuple constructors (index, value).
# Semcheck wraps `yield (i, i*2)` as nnkHiddenSubConv[nnkEmpty, nnkTupleConstr[…]].
# The A3-S2a path peels the HiddenSubConv and emits one `let` per loop var.
iterator pairsIter(n: int): (int, int) {.closure.} =
  var i = 0
  while i < n:
    yield (i, i * 2)
    inc i

# T9: iterator yielding a tuple VARIABLE (not an explicit constructor).
# `yield tupleVarSentinel` produces nnkSym in the typed AST (not nnkTupleConstr),
# so the A3-S2a degrade fires: tupleConstr == nil → mkUnsupported → sxUnknown.
# The module-level sentinel avoids nnkTupleConstr in the iterator body itself
# (nnkTupleConstr in a var-section RHS would cause a compile-time parseExpr error
# since the symex engine has no nnkTupleConstr expression handler).
let tupleVarSentinel: (int, int) = (0, 0)

iterator tupleVarIter(): (int, int) {.closure.} =
  yield tupleVarSentinel  # nnkSym — NOT an explicit tuple constructor

# T10: 3-element tuple iterator, verifying A3-S2a generalises to N > 2.
# `yield (i, i*2, i*3)` → nnkHiddenSubConv[nnkEmpty, nnkTupleConstr[3 elems]];
# `for a, b, c in tripleIter(n):` has 3 nnkSym loop vars in the ForStmt.
iterator tripleIter(n: int): (int, int, int) {.closure.} =
  var i = 0
  while i < n:
    yield (i, i * 2, i * 3)
    inc i

# ===========================================================================
# SUT procs (module scope — required for getImpl resolution from symexFind)
# ===========================================================================

# NOTE: for-bodies below use `sum += elem` where the augmented-assignment walker
# (v31) is available, and explicit `sum = sum + elem` elsewhere. A3-S2a tests
# (T8, T10) use `+=` since walker v31 desugars it; T1/T2 keep the explicit form
# to preserve their characterisation as pure A3-S1 tests.

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

# T8 (A3-S2a positive): pairsIter yields (idx, val) pairs; for-body accumulates val.
# `yield (i, i*2)` is an explicit TupleConstr, so the tuple-yield path fires.
# pairsIter(3) yields (0,0), (1,2), (2,4) → sum of vals = 0+2+4 = 6.
# Walker v32: `sum += v` uses augmented-assign desugaring (v31 feature).
proc sutA3TupleYieldSum(n: int) =
  var sum = 0
  for i, v in pairsIter(n):
    sum += v
  if sum == 6:
    symexTarget("pairSum6")

# T9 (A3-S2a non-constructor yield degrade): tupleVarIter yields a tuple sym.
# `yield tupleVarSentinel` → nnkSym in the typed AST — NOT nnkTupleConstr.
# The degrade fires (tupleConstr == nil → mkUnsupported) → sxUnknown.
proc sutA3TupleVarYield(n: int) =
  for a, b in tupleVarIter():
    if a + b == n:
      symexTarget("tupleVarReach")

# T10 (A3-S2a 3-var): tripleIter yields (i, i*2, i*3); for-body accumulates last.
# Verifies multi-var support generalises to N=3, not just N=2.
# tripleIter(3) yields (0,0,0),(1,2,3),(2,4,6) → sum of z values = 0+3+6 = 9.
proc sutA3TripleYield(n: int) =
  var sum = 0
  for x, y, z in tripleIter(n):
    sum += z
  if sum == 9:
    symexTarget("tripleSum9")

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
  # SND-1 (RFC-chapulin-hardening Cluster 1, walker v38) update: `isUnsupported`
  # still does NOT drop the path (it is not halt-the-path, unlike `isUnsafeCast`),
  # but it now TAINTS every surviving path `uncertain = true` before continuing.
  # The label after the degraded `for` IS still reached on the continuing path
  # (the degrade remains transparent, not path-dropping — `paths.len` is
  # preserved), but the `isTargetLabel` chokepoint now demotes any sxSat found
  # on an `uncertain` path to `sxUnknown` — this is a GENERAL walker-level fix
  # (not per-site), so this SUT (which happens not to depend on anything the
  # degraded `for` would have mutated) is intentionally treated the same as any
  # other post-drop target: `sxUnknown`, not a distinguishable "reached but
  # tainted" status. (Pre-SND-1 this test asserted `sxSat` — that assertion
  # encoded exactly the unsoundness SND-1 closes: an unrelated downstream
  # target on a path that dropped a mutation is not distinguishable, in
  # general, from one that DOES depend on the dropped mutation, so the walker
  # must conservatively degrade both alike.)
  test "T5: label after for-over-return-iter → sxUnknown (SND-1: post-drop path is tainted uncertain)":
    let r = symexFind(sutA3LabelAfterReturnIter, tLabel("afterLoop"))
    check r.status == sxUnknown

  # ---- T6: recursion guard (CRIT-3) — no compile-time hang; degraded inner for is tainted ----
  # The recursion guard (D2-0d) stops the infinite parse-time re-inlining: the fact
  # that this file COMPILES AT ALL proves it (without the guard, `getImpl`-driven
  # inlining of a self-recursive iterator overflows the compiler stack). The OUTER
  # level inlines — its first `yield n` runs (`cnt = n`) — and the inner recursive
  # `for recursiveCountIter(n-1)` degrades to `mkUnsupported`.
  #
  # SND-1 update: the pre-SND-1 comment here argued this was "sound" because the
  # dropped inner `for` is a "no-op that does NOT mutate `cnt`" — but that is
  # exactly the unsound assumption SND-1 closes. The dropped inner `for` WOULD, if
  # modeled, have added further (non-negative, in THIS particular SUT) contributions
  # to `cnt` — the walker cannot verify that domain fact in general (a bare
  # `mkUnsupported` carries no such guarantee), so treating the pre-drop `cnt` as
  # trustworthy for a POST-drop target was only accidentally correct here, not sound
  # by construction. Post-SND-1 the degraded inner `for` taints the path uncertain,
  # and `cnt > 10` (checked strictly after it) now correctly degrades to `sxUnknown`.
  test "T6: recursive iterator — degraded inner for taints the path → sxUnknown (SND-1)":
    let r = symexFind(sutA3RecursiveIter, tLabel("deepRecurse"))
    check r.status == sxUnknown

  # ---- T7: deferred — first-class iterator value → sxUnknown (D6) ----
  test "T7: first-class iterator value (stored in let) → sxUnknown (D6 deferred)":
    let r = symexFind(sutA3FirstClassIter, tLabel("firstClass"))
    check r.status == sxUnknown

  # ---- T8 (A3-S2a positive): explicit tuple-yield inlined; witness pinned ----
  test "T8: pairsIter tuple-yield — sxSat, witness n==3 (sum of vals 0+2+4==6)":
    ## A3-S2a: `yield (i, i*2)` is nnkTupleConstr (after peeling nnkHiddenSubConv).
    ## Each loop var binds to the corresponding element: `let i = elem0; let v = elem1`.
    ## pairsIter(3) yields (0,0),(1,2),(2,4) → val-sum = 0+2+4 = 6 → witness n=3.
    let r = symexFind(sutA3TupleYieldSum, tLabel("pairSum6"))
    check r.status == sxSat
    check r.witness[0] == 3   ## n == 3: pairSum(3) = 0+2+4 = 6

  # ---- T9 (A3-S2a degrade): tuple VARIABLE yield → sxUnknown ----
  test "T9: tuple-var yield (not constructor) in multi-var for → sxUnknown":
    ## `yield p` where p: (int, int) is a variable → typed AST yields nnkSym,
    ## not nnkTupleConstr. tupleConstr == nil → mkUnsupported → sxUnknown.
    ## Sound by Invariant 3: we cannot safely destructure an indirect tuple.
    ## (True arity-mismatch between loop-var count and yield tuple arity is
    ## prevented by Nim's own type checker; the safety check in parseIterBodyStmt
    ## is defense-in-depth for future or implementation-internal mismatches.)
    let r = symexFind(sutA3TupleVarYield, tLabel("tupleVarReach"))
    check r.status == sxUnknown

  # ---- T10 (A3-S2a 3-var): 3-element tuple destructuring — positive ----
  test "T10: tripleIter 3-var tuple-yield — sxSat, witness n==3 (sum z 0+3+6==9)":
    ## Verifies A3-S2a generalises to N=3 loop vars, not just N=2.
    ## tripleIter(3): (0,0,0),(1,2,3),(2,4,6) → z-sum = 0+3+6 = 9 → witness n=3.
    let r = symexFind(sutA3TripleYield, tLabel("tripleSum9"))
    check r.status == sxSat
    check r.witness[0] == 3   ## n == 3: tripleSum(3) z-vals = 0+3+6 = 9

  # ---- walker version pin ----
  test "walker version is now 38 (SND-1 uncertain-taint producer, 37→38)":
    ## SND-1 bumps 37→38 (isUnsupported taints Path.uncertain). A7-S3 adds
    ## parse-time literal decode (runeLen/runes) and seZ3StringIncomplete
    ## degrade for symbolic strings (ADR-0017 Path B, closes Phase-16 RFC).
    check symexWalkerVersion == "38"
