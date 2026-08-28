## iteSV composite-merge degrade (round-6 re-review items 1-2, walker
## v114/v115). `iteSV`'s composite-merge arms (`svString`/`svTable`/
## `svSet`/`svVariant`/`svMultiVariant`/`svUninterpRef`, plus `svSeq`'s
## genuine-non-placeholder branch) used to be `allocDegrade(...); t` --
## returning ONE OPERAND'S CONCRETE VALUE unconditionally, ignoring both
## `cond` and the accumulator `e`. Every caller's index-ite-fold
## (`res = arrElems[0]; for k: res = iteSV(cond_k, arrElems[k], res)`) is a
## LEFT FOLD that always returns `t` at every step, so the fold's final
## value was structurally the LAST array element, independent of the
## symbolic index -- a silent wrong-value substitution.
##
## Renamed from `tsymex_r6_item1_itesv_mergedegrade.nim` (item 5, walker
## v115): a within-round ordinal ("item1") is ambiguous once a later round
## reuses the same numbering; topic names are this suite's convention.
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
##
## Closing slice (walker v115) additions:
##   - `svSeq`'s GENUINE (non-placeholder) merge arm was re-opened: it still
##     fell through to a collapsed `t` after v114 (its own docstring falsely
##     claimed closure). `array[3, seq[int]]` PARAMETER probes below pin the
##     fix (parameter allocation, not a seq/array literal, so every element
##     is a real, backed, non-placeholder `svSeq` -- exactly the branch that
##     was still broken).
##   - `tyOf`'s `svVariant`/`svMultiVariant` arms dropped the SymVal's own
##     (fully-preserved) plain-field names/types when reconstructing a
##     degrade-placeholder's type, so a later plain-field read crashed with a
##     parser-blame `ValueError` instead of an honest classified decline. An
##     `array[2, Variant]` PARAMETER probe below, followed by a plain-field
##     read, pins the fix.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

suite "symex iteSV mergedegrade -- composite-merge degrade, single path":
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

suite "symex iteSV mergedegrade -- two sibling paths merged before a shared isIndex":
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

suite "symex iteSV mergedegrade -- ordinary (non-composite) symbolic array indexing is unaffected":
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

suite "symex iteSV mergedegrade -- svSeq genuine (non-placeholder) merge, walker v115":
  ## `array[3, seq[int]]` as a PARAMETER (not a literal): `allocateSym`'s
  ## `itArray` arm recurses into `itSeq` for each element, and `seq[int]`'s
  ## `itInt` elem type IS backed, so all three elements are GENUINE (never
  ## `isUnsupportedFieldPlaceholder`) `svSeq` values -- exactly the branch
  ## re-opened this round.
  test "symbolic index over array[3, seq[int]] param -- classified sxUnknown, never a fabricated sxSat":
    proc pickSeqElem(arr: array[3, seq[int]], i: int) =
      if i >= 0 and i < 3:
        let v = arr[i]
        if v.len == 7:
          symexTarget("seqmerge_pick_hit")
    let r = symexFind(pickSeqElem, tLabel("seqmerge_pick_hit"))
    check r.status == sxUnknown
    var sawClassified = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "iteSV" in e.msg and "seq" in e.msg:
        sawClassified = true
    check sawClassified

  test "two sibling array[3, seq[int]] params merged before a shared isIndex -- vulnerable array first":
    proc probeSeqFirst(flag: bool, a: array[3, seq[int]], b: array[3, seq[int]], i: int) =
      var arr: array[3, seq[int]]
      if flag:
        arr = a
      else:
        arr = b
      if i >= 0 and i < 3:
        let v = arr[i]
        if v.len == 7:
          symexTarget("seqmerge_sibling_first_hit")
    let r = symexFind(probeSeqFirst, tLabel("seqmerge_sibling_first_hit"))
    check r.status == sxUnknown

  test "two sibling array[3, seq[int]] params merged before a shared isIndex -- vulnerable array second":
    proc probeSeqSecond(flag: bool, a: array[3, seq[int]], b: array[3, seq[int]], i: int) =
      var arr: array[3, seq[int]]
      if flag:
        arr = b
      else:
        arr = a
      if i >= 0 and i < 3:
        let v = arr[i]
        if v.len == 7:
          symexTarget("seqmerge_sibling_second_hit")
    let r = symexFind(probeSeqSecond, tLabel("seqmerge_sibling_second_hit"))
    check r.status == sxUnknown

suite "symex iteSV mergedegrade -- tyOf plain-field threading for merge-degraded variants, walker v115":
  test "array[2, Variant] param symbolic-index merge, then a plain-field read -- classified decline, never the parser-blame raise":
    type
      Mv2Kind = enum mv2A, mv2B
      Mv2Shape = object
        label: int          ## plain (shared, always-present) field
        case kind: Mv2Kind
        of mv2A: aval: int
        of mv2B: bval: int
    proc probeVariantMergeThenPlainRead(arr: array[2, Mv2Shape], i: int) =
      if i >= 0 and i < 2:
        let v = arr[i]
        if v.label == 99:
          symexTarget("item2_variant_plain_read_hit")
    let r = symexFind(probeVariantMergeThenPlainRead, tLabel("item2_variant_plain_read_hit"))
    check r.status == sxUnknown
    for e in r.errors:
      check "A-normalised" notin e.msg
      check e.kind != weInternalWalkerFault
    var sawClassified = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "iteSV" in e.msg and "variant" in e.msg:
        sawClassified = true
    check sawClassified

suite "symex iteSV mergedegrade -- walker version pin":
  test "walker version floor >= 115 (item 1 re-opened + item 2: iteSV/tyOf merge-degrade fixes)":
    check parseInt(symexWalkerVersion) >= 115
