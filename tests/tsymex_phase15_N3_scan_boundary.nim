## RFC-parser-normalization (#146), Cluster N, slice N3 — routine-shaped
## node set reconciliation. Two divergent inline vocabularies in
## `dsl_parser.nim` (a 7-elem closure-call-detect family and a 6-elem
## scanner-scope-boundary family, neither matching `std/macros.RoutineNodes`)
## are collapsed onto two named, audited consts:
##
##   `routineShapedForClosureDetect* = RoutineNodes - {nnkDo, nnkLambda}`
##   `nestedRoutineScanBoundary*     = RoutineNodes - {nnkDo}`
##
## both defined in `src/nelli/smt/dsl_parser.nim` immediately above
## `resolveRoutineImpl`. This file characterizes `nestedRoutineScanBoundary`
## — the set consumed by the A3 (ADR-0014) shallow pre-scans
## (`hasYieldShallow`/`hasReturnShallow`/`hasKindShallow`/
## `substIteratorParams`) to decide where a nested routine's own scope
## begins, so a `yield`/`return`/`break`/`continue`/param-name occurring
## INSIDE a nested routine is never misattributed to the OUTER iterator or
## for-body being characterized.
##
## ----------------------------------------------------------------------------
## Probe findings that decided the N3 design (2026-08-13; probes NOT
## committed — gitignored `scratchpad/`, matching the RFC-146/N2 convention)
## ----------------------------------------------------------------------------
## (a) `method` definitions are Nim TOP-LEVEL-ONLY: nesting one inside a
##     proc body is a compile error, "'method' is only allowed at top
##     level" (`scratchpad/probe_n3_nested_method.nim`).
## (b) `converter` definitions are equally top-level-only: "'converter' is
##     only allowed at top level" (`scratchpad/probe_n3_nested_converter.nim`).
##     Consequence for (a)/(b): a `nnkMethodDef`/`nnkConverterDef` node can
##     NEVER appear nested inside a body one of these scanners descends
##     into — the pre-N3 6-elem set's omission of both was a real
##     vocabulary inconsistency but never a reachable defect. Adding them
##     to `nestedRoutineScanBoundary` (this slice) is behavior-identical
##     hardening: there is no Nim program on which the addition changes
##     which node the scan stops at, because the scan can never reach one
##     of these two node kinds in the first place. NOT independently
##     end-to-end testable for exactly this reason — there is no legal Nim
##     program that would exercise the pre-N3 gap.
## (c) `do:`-notation is parser-level sugar already rewritten to `nnkLambda`
##     BEFORE semcheck produces any typed impl tree — `getImpl`, and so
##     every one of these scanners, can never observe an `nnkDo` node
##     (`scratchpad/probe_n3_do_shape.nim`: the typed `treeRepr` of a
##     `do:`-block call argument is `Lambda`, never `Do`; confirmed
##     separately that `yield`/`break` cannot legally cross into a `do:`
##     block's own scope either — `scratchpad/probe_n3_do_yield.nim` /
##     `probe_n3_do_break.nim`). `nnkDo` is excluded from
##     `nestedRoutineScanBoundary` for definitional precision (it is what
##     `RoutineNodes` names for do-notation) but a `do:` block's own body
##     is ALREADY correctly excluded from descent via `nnkLambda`, which
##     both the pre-N3 and post-N3 sets contain.
## (d) `case n.kind of aNamedConstSet: ...` (a `set[NimNodeKind]` CONST used
##     directly as case-branch labels, not spelled out inline) is legal Nim
##     (`scratchpad/probe_n3_case_constset.nim`) — this is what let three of
##     the four consumers (`hasYieldShallow`/`hasReturnShallow`/
##     `hasKindShallow`, all `case`-based) migrate onto
##     `nestedRoutineScanBoundary` with NO restructuring; only
##     `substIteratorParams`'s `if n.kind in {...}:` form needed the const
##     name substituted directly, already the same shape it had before.
##
## ----------------------------------------------------------------------------
## What is, and is not, diagnostically testable end-to-end (important:
## read before extending this file)
## ----------------------------------------------------------------------------
## `nnkLambda` (a `let`/`var`-bound closure VALUE, Phase 15 Cluster C's
## explicitly-supported expression-position form) is the ONLY
## `nestedRoutineScanBoundary` member that can be embedded inside a scanned
## body AND still leave the surrounding program A3-inlineable, because a
## raw NESTED `nnkProcDef`/`nnkFuncDef`/`nnkIteratorDef` STATEMENT inside an
## iterator's own body is excluded from the walker's "supported fragment"
## independently of N3 — probe-verified
## (`scratchpad/probe_n3_nested_def_isolation.nim`): an iterator containing
## an UNUSED, `return`-free, otherwise-inert nested `proc` statement already
## degrades the enclosing `for` to `sxUnknown`, with no `yield`/`return`
## anywhere for `hasYieldShallow`/`hasReturnShallow` to misattribute. That
## degrade is orthogonal to, and pre-dates, this slice — it is the generic
## statement dispatcher declining an unrecognised statement kind, not a
## `nestedRoutineScanBoundary` gap — so it is out of N3's scope and NOT
## fixed here. The two tests below are consequently the diagnostic ones N3
## actually admits: both use a nested LAMBDA (not a nested proc/func/
## iterator statement) to prove `hasReturnShallow` and `hasKindShallow`
## (via `hasBreakContinueShallow`) correctly stop descent at the boundary.
## `hasYieldShallow`'s boundary is UNTESTABLE by construction for a
## different reason than the proc/func/iterator case: `yield` is illegal
## anywhere but directly in an iterator's own top-level flow (probe (c)
## above already establishes this for `do:` blocks; the same restriction
## applies uniformly to every nested-routine form), so there is no legal
## Nim program in which a nested routine's yield could be misattributed to
## its enclosing iterator in the first place. `substIteratorParams` is not
## independently exercised either (constructing a diagnostic collision
## requires reasoning about the IR environment's scoping model beyond this
## slice's remit) — it consumes the SAME `nestedRoutineScanBoundary` value
## as the two consumers characterized below, not a per-consumer copy, so
## their pass is direct evidence for its correctness too.
##
## Both tests below are CHARACTERIZATIONS of pre-existing, correct
## behavior (the `nnkLambda` member was already present in the pre-N3
## 6-elem literal) — they pin that N3's re-spelling onto
## `nestedRoutineScanBoundary` preserves it, not new coverage of a
## previously-broken path.
##
## No `symexWalkerVersion` bump (N3 is behavior-identical — RFC Cluster N
## acceptance). The floor pin matches N2's.

import std/[unittest, strutils]
import nelli/symex

# ===========================================================================
# Iterator/proc definitions (module scope so getImpl can resolve them)
# ===========================================================================

# hasReturnShallow pin: the iterator's OWN body contains a `let`-bound
# LAMBDA whose body contains a `return`. If `nestedRoutineScanBoundary`
# did not stop descent at `nnkLambda`, `hasReturnShallow` would find that
# `return`, misattribute it to `iterLambdaReturn` itself, and pre-scan 0(b)
# would degrade the WHOLE `for` to `sxUnknown` (ADR-0014 D2-0b, CRIT-1)
# exactly as it does for a genuine top-level iterator `return` (contrast
# test below, mirroring `tsymex_a3_closure_iterators.nim` T4).
iterator iterLambdaReturn(n: int): int {.closure.} =
  let doubleOrZero = proc (x: int): int =
    if x < 0:
      return 0
    x * 2
  var i = 0
  while i < n:
    yield doubleOrZero(i)
    inc i

# Contrast baseline: a genuine top-level `return` in the iterator's OWN
# flow — MUST still degrade (proves the mechanism is not vacuously
# "always sxSat"; mirrors T4 of tsymex_a3_closure_iterators.nim).
iterator iterTopLevelReturn(n: int): int {.closure.} =
  if n < 0:
    return
  yield 42

# hasKindShallow (via hasBreakContinueShallow) pin: `hasBreakContinueShallow`
# scans the FOR-LOOP's CALLER body (`bodyNode`, the code written inside
# `for elem in ...:`), not the iterator's own body. Here the caller body
# contains a `let`-bound LAMBDA with its OWN `while true: break` — a break
# that targets the LAMBDA's own loop, not the enclosing `for`. If
# `nestedRoutineScanBoundary` did not stop descent at `nnkLambda`, this
# scan would find that break, misattribute it to the for-body, and pre-scan
# 0(c) would degrade the finite (straight-yield) iterator to `sxUnknown`
# (ADR-0014 D2-0c, CRIT-2) exactly as it does for a genuine for-body break
# (contrast test below, mirroring T3).
iterator twoElemsIterN3(): int {.closure.} =
  yield 1
  yield 2

# ===========================================================================
# SUT procs
# ===========================================================================

# T-lambda-return: nested lambda's `return` must not leak into the
# iterator's own hasReturnShallow scan.
# iterLambdaReturn(3): doubleOrZero(0)=0, doubleOrZero(1)=2, doubleOrZero(2)=4
# -> sum = 6.
proc sutLambdaReturnBoundary(n: int) =
  var sum = 0
  for elem in iterLambdaReturn(n):
    sum = sum + elem
  if sum == 6:
    symexTarget("lambdaReturnSum6")

# T-toplevel-return (contrast): a real iterator-level return still degrades.
proc sutTopLevelReturnDegrades(n: int) =
  for elem in iterTopLevelReturn(n):
    if elem == 42:
      symexTarget("topLevelReturnGot42")

# T-lambda-break: nested lambda's OWN break must not leak into the
# for-body's hasBreakContinueShallow scan. `helper()` always returns 99
# (its own `while true: break` fires immediately), so `(helper() - 99)`
# contributes 0 every iteration: twoElemsIterN3() sums 1 + 2 = 3.
proc sutLambdaBreakBoundary(n: int) =
  var sum = 0
  for elem in twoElemsIterN3():
    let helper = proc (): int =
      while true:
        break
      99
    sum = sum + elem + (helper() - 99)
  if sum == 3:
    symexTarget("lambdaBreakSum3")

# T-toplevel-break (contrast): a real for-body-level break still degrades
# the finite iterator (mirrors T3 of tsymex_a3_closure_iterators.nim).
proc sutTopLevelBreakDegrades(n: int) =
  var sum = 0
  for elem in twoElemsIterN3():
    if elem > n:
      break
    sum = sum + elem
  if sum == 3:
    symexTarget("topLevelBreakSum3")

# ===========================================================================
# Tests
# ===========================================================================

suite "symex N3 — nestedRoutineScanBoundary characterization (RFC-parser-normalization #146/#148/#150)":

  test "hasReturnShallow: nested lambda's return does not leak — sxSat, witness n==3":
    let r = symexFind(sutLambdaReturnBoundary, tLabel("lambdaReturnSum6"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "hasReturnShallow contrast: a real top-level iterator return still degrades — sxUnknown":
    let r = symexFind(sutTopLevelReturnDegrades, tLabel("topLevelReturnGot42"))
    check r.status == sxUnknown

  test "hasKindShallow/hasBreakContinueShallow: nested lambda's own break does not leak — sxSat":
    let r = symexFind(sutLambdaBreakBoundary, tLabel("lambdaBreakSum3"))
    check r.status == sxSat

  test "hasBreakContinueShallow contrast: a real for-body break still degrades — sxUnknown":
    let r = symexFind(sutTopLevelBreakDegrades, tLabel("topLevelBreakSum3"))
    check r.status == sxUnknown

  test "walker version floor: symexWalkerVersion >= 71 (N3 is behavior-identical, no bump)":
    check parseInt(symexWalkerVersion) >= 71
