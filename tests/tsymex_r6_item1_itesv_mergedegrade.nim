## Item 1 (round-6 re-review, walker v114) -- `iteSV`'s composite-merge arms
## (`svString`/`svTable`/`svSet`/`svVariant`/`svMultiVariant`/`svUninterpRef`,
## plus `svSeq`'s genuine-non-placeholder branch) used to be
## `allocDegrade(...); t` -- returning ONE OPERAND'S CONCRETE VALUE
## unconditionally, ignoring both `cond` and the accumulator `e`. Every
## caller's index-ite-fold (`res = arrElems[0]; for k: res = iteSV(cond_k,
## arrElems[k], res)`) is a LEFT FOLD that always returns `t` at every step,
## so the fold's final value was structurally the LAST array element,
## independent of the symbolic index -- a silent wrong-value substitution.
##
## ---- Verification summary (adversarial, container-run) ----------------------
## The expression-level `iekIndex` call site (`lower()`, runtime.nim) is DEAD
## CODE: `mkIndex` (the only constructor for an `iekIndex` IRExpr) has zero
## callers anywhere in the parser -- `nnkBracketExpr` on an `itArray` receiver
## ALWAYS A-normalises to the `isIndex` STATEMENT via `mkIndexStmt`
## (dsl_parser.nim, `of itArray:`), so no real SUT can ever reach it. The one
## LIVE route is the walk-level `isIndex` fold, which calls `iteSV` directly
## with no intervening `lower()`/`lowerBoolInExpr` wrapper -- so the
## `loweringDidDegrade` taint `allocDegrade` deposits is not drained onto the
## surviving path's `uncertain` flag inside `isIndex` itself; it is drained by
## whatever `lower()`/`lowerBoolInExpr` call runs NEXT on that SAME path.
## Every adversarial shape constructed this round -- a single symbolic-index
## read over a local `array[3, string]` literal, and two sibling paths
## (produced by an EARLIER, already-resolved branch) sharing one subsequent
## `isIndex` + comparison pair -- reached `isTargetLabel` with `uncertain ==
## true` and reported a correctly-classified `sxUnknown`, never a fabricated
## `sxSat`. The reason: `isIf`'s own body-walk descends ONE OUTER PATH AT A
## TIME (`walk(br.body, @[armPath], w)`, runtime.nim), so the walker never
## actually batches multiple live siblings through a shared `isIndex`+
## consumer pair in practice, even though nothing in the STATEMENT-level
## `isIndex`/`isLet` handlers themselves would prevent that batching from one
## day mattering (e.g. a HOF/closure fold merging several call-return paths).
##
## Verdict: ROUTE (a) -- sound today, but via a caller-shape coincidence (the
## taint racing whatever lowering call happens to run next), not by
## construction. Fixed regardless, per the review brief: the composite arms
## now return a genuinely FRESH, unconstrained placeholder of the operand's
## own kind instead of the collapsed concrete value, so soundness no longer
## depends on that race. This file pins the classified-`sxUnknown` shape (the
## correct, sound-by-construction outcome) as a permanent regression guard --
## a future edit that reintroduces "return `t`" or breaks the taint mechanism
## must fail one of these tests.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

suite "symex item1 -- iteSV composite-merge degrade, single path":
  test "symbolic index over array[3, string] local literal -- classified sxUnknown, never a fabricated sxSat":
    proc pickString(i: int) =
      let arr = ["zero", "one", "two"]
      if i >= 0 and i < 3:
        if arr[i] == "two":
          symexTarget("item1_pick_string_hit")
    let r = symexFind(pickString, tLabel("item1_pick_string_hit"))
    check r.status == sxUnknown
    var sawClassified = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "iteSV" in e.msg and "string" in e.msg:
        sawClassified = true
    check sawClassified

suite "symex item1 -- iteSV composite-merge degrade, two sibling paths merged before a shared isIndex":
  ## Reproduces the specific shape the verification round constructed to
  ## probe for a cross-path `loweringDidDegrade` leak: two live paths
  ## (produced by an earlier, unrelated branch) share ONE subsequent
  ## `isIndex` statement over a composite-typed array, with the vulnerable
  ## array placed in EACH branch in turn (both orderings) to rule out an
  ## order-dependent escape.
  test "vulnerable array in the else branch":
    proc probeElse(flag: bool, i: int) =
      var arr: array[3, string]
      if flag:
        arr = ["aaa", "bbb", "ccc"]
      else:
        arr = ["zero", "one", "two"]
      let v = arr[i]
      if i >= 0 and i < 3:
        if v == "two":
          symexTarget("item1_probe_else_hit")
    let r = symexFind(probeElse, tLabel("item1_probe_else_hit"))
    check r.status == sxUnknown

  test "vulnerable array in the then branch":
    proc probeThen(flag: bool, i: int) =
      var arr: array[3, string]
      if flag:
        arr = ["zero", "one", "two"]
      else:
        arr = ["aaa", "bbb", "ccc"]
      let v = arr[i]
      if i >= 0 and i < 3:
        if v == "two":
          symexTarget("item1_probe_then_hit")
    let r = symexFind(probeThen, tLabel("item1_probe_then_hit"))
    check r.status == sxUnknown

suite "symex item1 -- ordinary (non-composite) symbolic array indexing is unaffected":
  test "array[5, int] symbolic index -- still finds a real, correct witness (positive control)":
    proc symbolicIdx(arr: array[5, int], i: int) =
      if i >= 0 and i < 5:
        if arr[i] == 42:
          symexTarget("item1_control_found")
    let r = symexFind(symbolicIdx, tLabel("item1_control_found"))
    check r.status == sxSat
    let i = r.witness[1]
    check i >= 0 and i < 5
    check r.witness[0][i] == 42

suite "symex item1 -- walker version pin":
  test "walker version floor >= 114 (item 1: iteSV composite-merge degrade fixed)":
    check parseInt(symexWalkerVersion) >= 114
