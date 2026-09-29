## Augmented-assignment desugaring (walker v31).
##
## `<simpleVar> <op>= <rhs>` with `<op>=` ∈ {+=, -=, *=} now desugars to
## the same IR as the explicit `<var> = <var> <op> <rhs>` form.  Previously
## these fell through to `isUnsupported` → `sxUnknown`.
##
## Scope (SIMPLE-VARIABLE LHS ONLY — see dsl_parser.nim `of nnkInfix:`):
##   * Covered: plain `var` / `let` / local-sym LHS.
##   * Degraded (sound): field LHS (`obj.f += y`), index LHS (`a[i] += y`),
##     any `op=` not in {+=, -=, *=}. Invariant 3 — never a wrong verdict.
##
## Tests (RED→GREEN order):
##   1. `+=` gives same verdict AND same witness as explicit `s = s + x`.
##   2. `-=` gives sxSat.
##   3. `*=` gives sxSat.
##   4. Iterator integration: `for elem in iter(): sum += elem` → sxSat
##      (the motivating case; requires A3-S1 iterator inlining + += together).
##   5. Degradation (Invariant 3): field-LHS `obj.val += b` → sxUnknown.

import std/unittest
import nelli/symex

# ===========================================================================
# SUT procs — explicit form (baseline for cross-checking)
# ===========================================================================

proc sutPlusExplicit(s, x: int) =
  var acc = s
  acc = acc + x
  if acc == 7:
    symexTarget("sum7")

proc sutMinusExplicit(s, x: int) =
  var acc = s
  acc = acc - x
  if acc == 3:
    symexTarget("diff3")

proc sutMulExplicit(s, x: int) =
  var acc = s
  acc = acc * x
  if acc == 12:
    symexTarget("prod12")

# ===========================================================================
# SUT procs — augmented form (under test)
# ===========================================================================

proc sutPlusAug(s, x: int) =
  var acc = s
  acc += x
  if acc == 7:
    symexTarget("sum7")

proc sutMinusAug(s, x: int) =
  var acc = s
  acc -= x
  if acc == 3:
    symexTarget("diff3")

proc sutMulAug(s, x: int) =
  var acc = s
  acc *= x
  if acc == 12:
    symexTarget("prod12")

# ===========================================================================
# Iterator integration: sum += elem in for-body (the motivating pattern)
# ===========================================================================

## NOTE: re-uses the countUpIter shape from A3 Slice 1 to confirm += works
## INSIDE an inlined iterator body (A3-S1 inlining + augmented-assign together).
iterator augCountUp(n: int): int {.closure.} =
  var i = 0
  while i < n:
    yield i
    inc i

proc sutIterSumAug(n: int) =
  var sum = 0
  for elem in augCountUp(n):
    sum += elem   ## formerly sxUnknown; now desugared to sum = sum + elem
  if sum == 6:    ## 0+1+2+3 = 6 when n = 4
    symexTarget("sum6")

# ===========================================================================
# Degradation: field-LHS augmented assign (Invariant 3)
# ===========================================================================

## AugPoint is a plain value type (itTuple in symex). Used for the
## field-LHS degradation test — passed in as a parameter so no
## unsupported nnkObjConstr appears in the SUT body.
type AugPoint = object
  x, y: int

proc sutFieldAugModelled(p: AugPoint, b: int) =
  ## RFC-0005 S8p: a value-object field `+=` is modelled (rebuilt-root
  ## assignment), so a label it guards is decided.
  ## Both operands are bounded first, so neither `+` can overflow (an
  ## unbounded `q.x += b` rightly reports its OverflowDefect, sxRaised).
  if b > 0 and b < 1000 and p.x > 0 and p.x < 1000:
    var q = p
    q.x += b
    if q.x == p.x + b + 1:
      symexTarget("field_aug_dead")

proc sutFieldAugDegrades(p: AugPoint, b: int) =
  var q = [p.x, p.y]  ## an array copy of the struct param
  q[0] += b    ## array-element LHS → non-nnkSym after unwrap → mkUnsupported → sawUnknown
  ## No symexTarget: target not reached + sawUnknown=true → sxUnknown

# ===========================================================================
# Tests
# ===========================================================================

suite "Augmented-assignment desugaring (walker v31)":

  # ---- 1. += gives same verdict AND witness as explicit form ------------------
  test "+= gives same verdict (sxSat) as explicit s = s + x":
    let rExpl = symexFind(sutPlusExplicit, tLabel("sum7"))
    let rAug  = symexFind(sutPlusAug, tLabel("sum7"))
    check rExpl.status == sxSat
    check rAug.status  == sxSat

  test "+= produces same witness as explicit form":
    ## Desugared IR is byte-identical to the explicit form, so Z3 should
    ## produce the same satisfying assignment.  If the two witnesses ever
    ## diverge it means the IR differs — a regression in the desugaring.
    let rExpl = symexFind(sutPlusExplicit, tLabel("sum7"))
    let rAug  = symexFind(sutPlusAug, tLabel("sum7"))
    check rAug.witness == rExpl.witness

  test "+= witness satisfies s + x == 7":
    let r = symexFind(sutPlusAug, tLabel("sum7"))
    check r.status == sxSat
    let s = r.witness[0]; let x = r.witness[1]
    check s + x == 7

  # ---- 2. -= gives sxSat for acc - x == 3 ------------------------------------
  test "-= gives sxSat for acc - x == 3":
    let r = symexFind(sutMinusAug, tLabel("diff3"))
    check r.status == sxSat
    let s = r.witness[0]; let x = r.witness[1]
    check s - x == 3

  # ---- 3. *= gives sxSat for acc * x == 12 -----------------------------------
  test "*= gives sxSat for acc * x == 12":
    let r = symexFind(sutMulAug, tLabel("prod12"))
    check r.status == sxSat
    let s = r.witness[0]; let x = r.witness[1]
    check s * x == 12

  # ---- 4. Iterator integration ------------------------------------------------
  test "iterator integration: sum += elem in for-body → sxSat, witness n==4":
    ## augCountUp(4) yields 0,1,2,3; sum = 0+1+2+3 = 6.
    ## Requires A3-S1 iterator inlining (v30) + += desugaring (v31) together.
    let r = symexFind(sutIterSumAug, tLabel("sum6"))
    check r.status == sxSat
    check r.witness[0] == 4

  # ---- 5. Degradation (Invariant 3) ------------------------------------------
  test "field-LHS augmented assign on a value object is modelled (RFC-0005 S8p) → sxUnsat":
    ## Real Nim: q.x == p.x + b after the `+=`, never p.x + b + 1.
    let r = symexFind(sutFieldAugModelled, tLabel("field_aug_dead"))
    check r.status == sxUnsat

  test "positional-element augmented assign degrades soundly → sxUnknown":
    ## `q[0] += b` on an array: the LHS (after unwrapping hidden-deref
    ## wrappers) is nnkBracketExpr, NOT nnkSym, and not a value field chain
    ## (RFC-0005 S8p's field route; S8s added a tuple element, not an array
    ## one). The nnkInfix arm degrades to
    ## mkUnsupported → sawUnknown=true.
    ## With no symexTarget in the proc and sawUnknown=true, the verdict is
    ## sxUnknown (not sxSat — which would be wrong — and not sxUnsat — which
    ## would be unsound because we can't prove the label is unreachable).
    let r = symexFind(sutFieldAugDegrades, tLabel("never_label"))
    check r.status == sxUnknown
