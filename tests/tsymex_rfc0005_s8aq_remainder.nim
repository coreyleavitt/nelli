## RFC-0005 (soundness channels) slice S8aq -- S8ai's remainder.
##
## (1) `checkCapped`'s step 1c (the facts-based theory-free decision) ran
##     only `if r1 == zsUnsat`: step 1, the capped one-shot solve. A query
##     whose step 1 itself ran out of budget (`zsUnknown`, the solve
##     cancelled rather than refuted) skipped 1c entirely and fell to step
##     3 with whatever budget remained -- the facts were never tried. S8ai
##     flagged two such cases by name as not pinned end to end for exactly
##     this reason (`tsymex_rfc0005_s8ai_semantic.nim`, the comment above
##     `decidedBy1c`). Both are pinned below.
## (2) The dropped link "L (`seq.last_indexof`) is at least every found
##     `str.indexof(s, t, i)`" is valid but S8ai could not get either Z3 to
##     refute its negation within 1M units, even at `i = 0` -- so it was
##     never emitted. S8aq tried two reformulations as a ground fact
##     `seqRangeFacts` could emit (a fresh `str.indexof(s, t, L)` term
##     joined into the existing pairwise loop; the same bound stated
##     directly against an existing `str.indexof(s, t, i)` term with no
##     nested term at all) and both proved undecidable in practice, not
##     just slow -- `tsymex_rfc0005_s8v_termination.nim`'s own per-fact
##     validity pin caught each as `zsUnknown` on Z3 5.1 (not only Z3
##     4.13.4), and raising that pin's own check budget 50x (1M -> 50M
##     units) made Z3 hang past a 240s wall-clock bound rather than answer
##     either way. Declined: no ground fact links `str.indexof` and
##     `seq.last_indexof` here. (2) below pins the decline's shape instead
##     of the (abandoned) fact's validity.
## (3) `str.replace_all` is unreachable from the walker because nim-z3's
##     `replaceAll` wrapper is `-d:z3WithSeqReplaceAll`-gated (the C
##     constructor is absent below Z3 4.16); nelli's own build never set
##     the define, so `iekStrReplaceAll` always took the
##     `SymexZ3VersionMissingError` decline, never the real op. The define
##     is enabled for THIS suite only (`tsymex_rfc0005_s8aq_remainder.nim.cfg`,
##     the same per-test-file mechanism `symexQueryStats` and
##     `nelliVmAliasAudit` already use) -- nim-z3 needs no change, since the
##     FFI binding and its `Available()` runtime guard already exist there.
##     The walker's chokepoint (`runtime.nim`'s `lowerStrArm` catch, below
##     `degradeStrArm`'s doc comment) now also catches nim-z3's own
##     `Z3FeatureUnavailableError`, so a Z3 that lacks the C symbol (Z3
##     4.13.4, which this suite also runs under) still declines cleanly
##     instead of raising past the chokepoint.
## (4) The equality classes `seqRangeFacts` builds are a union-find over
##     the query's OWN stated equalities (and what `Z3_simplify` folds a
##     term to) -- not closed under what the query's assertions IMPLY
##     without stating it (e.g. `a < b`, `b < c` implies `a < c`, or two
##     arithmetic terms forced equal by a linear system). A missed
##     implied equality costs completeness only: the link that would have
##     fired does not, so step 1c declines (falls through to steps 2/3)
##     rather than deciding -- it never emits a fact that is false. Shown
##     with a test pair: a needle linked by the query's OWN equality
##     assertion is caught (as S8ai's needle-by-equality tests already
##     show); one linked only by two arithmetic facts the query implies
##     but never states as `=` is missed by step 1c (declines) and still
##     decided downstream (steps 2/3, the uncapped solver, do see the full
##     theory and arithmetic), so the final verdict is unaffected.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc tight(): SymexSettings =
  result = defaultSymexSettings()
  result.budget.seqQueryRLimit = 2_000

# ---- (1) step 1c no longer depends on step 1 completing --------------------

proc rfindBeforePiece(s: string) =
  if s.len > 10 and s[7] == ':' and s.rfind(':') < 7:
    symexTarget("s8aq_rfind_before_piece")

proc rfindNotinButFound(s: string) =
  if ':' in s and s.rfind(':') == -1:
    symexTarget("s8aq_rfind_notin_found")

suite "S8aq (1): step 1c's path does not depend on step 1 reaching UNSAT":

  test "end to end: s[7] == ':' and rfind < 7 is decided though step 1 is cancelled":
    # RED at a9bdaf4 (S8ai's own note): at this budget, step 1 itself (the
    # capped solve with the full theory) is cancelled (zsUnknown), so step
    # 1c -- gated on `r1 == zsUnsat` -- was never reached, and step 3 (the
    # uncapped query) ran out too: "was not decided".
    let r = symexFind(rfindBeforePiece, tLabel("s8aq_rfind_before_piece"), tight())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    for e in r.errors: check "was not decided" notin e.msg

  test "end to end: ':' in s and rfind == -1 is decided though step 1 is cancelled":
    let r = symexFind(rfindNotinButFound, tLabel("s8aq_rfind_notin_found"), tight())
    checkpoint show(r.errors)
    check r.status == sxUnsat
    for e in r.errors: check "was not decided" notin e.msg

# ---- (2) "L is at least every found index": a ground, budget-provable form -

const decls = """
(declare-const s String) (declare-const t String)
(declare-const i Int) (declare-const j Int)
"""

proc q(ctx: Z3Context; src: string): seq[Z3Bool] =
  parseSmt2String(ctx, decls & src)

proc stepOneC(ctx: Z3Context; roots: seq[Z3Bool]): Z3Status =
  let sv = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
  for f in seqRangeFacts(ctx, roots): sv.add f
  sv.check()

proc freeConsts(ctx: Z3Context; f: Z3Bool): seq[Z3AnyAst] =
  var seen: seq[int]
  var stack = @[toAnyAst(f)]
  while stack.len > 0:
    let tm = stack.pop()
    if getAstKind(tm) != akApp: continue
    let args = unpackApp(tm).args
    if args.len == 0 and getSortKind(tm) in {skInt, skSeq} and
       not Z3_is_string(ctx.raw, tm.raw):
      let id = astId(ctx, tm.raw)
      if id notin seen:
        seen.add id
        result.add tm
    for a in args: stack.add a

proc holdsOnSmallDomain(ctx: Z3Context; f: Z3Bool): string =
  ## Mirrors `tsymex_rfc0005_s8ai_semantic.nim`'s own helper of the same
  ## name: "" when `f` is `true` on every string over {"a", "\xff"} of
  ## length <= 3 and integer in -1..4, substituted for its free constants.
  var strs = @[""]
  var frontier = @[""]
  for _ in 1 .. 3:
    var next: seq[string]
    for w in frontier:
      for c in ["a", "\xff"]: next.add w & c
    strs.add next
    frontier = next
  let vars = freeConsts(ctx, f)
  if vars.len == 0: return ""
  var froms, tos: seq[RawZ3Ast]
  for v in vars:
    froms.add v.raw
    tos.add v.raw
  proc go(k: int): string =
    if k == vars.len:
      let g = ctx.checkErr Z3_simplify(ctx.raw, ctx.checkErr Z3_substitute(
        ctx.raw, f.raw, cuint(froms.len),
        cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
      let txt = $Z3_ast_to_string(ctx.raw, g)
      return (if txt == "true": "" else: txt)
    if getSortKind(vars[k]) == skInt:
      for v in -1 .. 4:
        tos[k] = mkInt(ctx, v).raw
        let r = go(k + 1)
        if r.len > 0: return r
    else:
      for w in strs:
        tos[k] = mkString(ctx, w).raw
        let r = go(k + 1)
        if r.len > 0: return r
    ""
  go(0)

proc factFlaw(ctx: Z3Context; f: Z3Bool): string =
  let r = querySolver(ctx, @[not f], 1_000_000'u).check()
  let cex = holdsOnSmallDomain(ctx, f)
  if r == zsSat or cex.len > 0: return $f & " -> " & $r & ", ground: " & cex
  ""

proc foundExceedsLast(s, t: string) =
  # `t in s` anchors `seqRangeFacts`' contains <-> last_indexof link
  # (`l.r >= 0 iff contains`, S8ai): without SOME contains/prefix/suffix
  # term in the query, step 1c has no way to learn `L >= 0` at all (the
  # base per-term bound alone says nothing about any OTHER term). `t in s`
  # is already IMPLIED by `s.find(t, 0) >= 0` -- asserting it too narrows
  # nothing.
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) < s.find(t, 0):
    symexTarget("s8aq_found_exceeds_last")

proc foundAtOrBeforeLast(s, t: string) =
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) >= s.find(t, 0):
    symexTarget("s8aq_found_at_or_before_last")

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

suite "S8aq (2): the dropped link is declined -- Z3 cannot decide the combination":

  # RFC-0005 S8aq attempted two reformulations of the dropped link ("L
  # (`seq.last_indexof`) is at least every found `str.indexof`") as a
  # ground fact `seqRangeFacts` could emit: a fresh `str.indexof(s, t, L)`
  # term joined into the existing pairwise loop, and (when that proved
  # undecidable within budget) the same bound stated directly against an
  # existing `str.indexof(s, t, i)` term with no nested term at all.
  # `tsymex_rfc0005_s8v_termination.nim`'s own per-fact validity pin --
  # which asserts the FULL theory refutes every fact's negation within
  # budget, the precondition for using a fact as a theory-free axiom at
  # all -- caught BOTH as undecided (`zsUnknown`) on Z3 5.1, not just Z3
  # 4.13.4; raising that pin's own check budget 50x (1M -> 50M units) made
  # Z3 hang past a 240s wall-clock bound rather than answer either way, so
  # this is not a budget-tuning gap. Declined: `seqRangeFacts` emits no
  # fact linking `str.indexof` and `seq.last_indexof` together. What
  # remains below pins the decline's shape: step 1c never falsely proves
  # the (true) claim, and the one case engineered to need exactly this
  # link is not decided even by the full theory at default settings
  # (`sxUnknown`, never a false verdict) -- the same completeness-only
  # cost item 4 documents for its own missed-equality gap, except here the
  # full theory does not recover it either, so there is no step 2/3 safety
  # net for this specific shape today.

  test "step 1c does not claim UNSAT from the dropped link (no false positive)":
    # Same query item 2 originally meant to decide: `str.contains` anchors
    # the `L >= 0` link (see `foundExceedsLast`'s own comment, above); `i`
    # is fixed at the literal 0. With the link declined, step 1c must not
    # claim UNSAT here -- that would be using an unproven fact as if it
    # were a theorem.
    let ctx = newContext()
    let roots = q(ctx, """(assert (str.contains s t))
                          (assert (>= (str.indexof s t 0) 0))
                          (assert (< (seq.last_indexof s t) (str.indexof s t 0)))""")
    check stepOneC(ctx, roots) != zsUnsat

  test "companion: a found index at or before L is satisfiable":
    let ctx = newContext()
    let roots = q(ctx, """(assert (str.contains s t))
                          (assert (>= (str.indexof s t 0) 0))
                          (assert (>= (seq.last_indexof s t) (str.indexof s t 0)))""")
    check stepOneC(ctx, roots) == zsSat

  test "the validity check catches a broken (strict) mutant of the (declined) fact":
    # `factFlaw`/`holdsOnSmallDomain` are the general validity-checking
    # helpers this suite and `tsymex_rfc0005_s8v_termination.nim` both
    # rely on; this pins that they still catch an actually-broken formula,
    # independent of whether `seqRangeFacts` itself emits anything like it.
    let ctx = newContext()
    let mutant = q(ctx, """
      (assert (=> (>= (str.indexof s t i) 0)
                  (< (str.indexof s t i) (seq.last_indexof s t))))""")[0]
    # Broken: a found index can EQUAL L (e.g. the only occurrence, or a
    # search starting exactly at it), not only lie strictly before it.
    let flaw = factFlaw(ctx, mutant)
    checkpoint $mutant & " -> " & flaw
    check flaw.len > 0

  test "end to end: declined -- sound sxUnknown, never a false sxSat":
    # The one SUT shape engineered to need exactly this link: with it
    # declined, the full (uncapped) sequence theory at DEFAULT settings
    # also does not decide it within budget (the same Z3 weakness the
    # suite-level comment measured, not a separate gap) -- `sxUnknown`,
    # classified `beSolverUndef`, never a false `sxSat` or a silent wrong
    # `sxUnsat`.
    let r = symexFind(foundExceedsLast, tLabel("s8aq_found_exceeds_last"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check hasKind(r.errors, beSolverUndef)

  test "companion: a found index at or before L is reachable":
    let r = symexFind(foundAtOrBeforeLast, tLabel("s8aq_found_at_or_before_last"))
    checkpoint show(r.errors)
    check r.status == sxSat

# ---- (3) str.replace_all is reachable under -d:z3WithSeqReplaceAll --------

proc replaceAllCorrect(s: string) =
  # Every occurrence replaced: "foofoo" -> "barbar", never "barfoo" (the
  # first-occurrence-only result S8c already ruled out at the Nim-model
  # level). With the real Z3 op wired in (this suite's `.nim.cfg`), the
  # SOLVER must agree, not just the concrete evaluator.
  if s == "foofoo" and s.replace("foo", "bar") == "barbar":
    symexTarget("s8aq_replace_all_correct")

proc replaceFirstOnlyUnreachable(s: string) =
  if s == "foofoo" and s.replace("foo", "bar") == "barfoo":
    symexTarget("s8aq_replace_first_only")

proc replaceGrowthAndRoundtrip(s: string) =
  # A real `str.replace_all`-backed symbolic result, not a free fresh
  # symbol: the `seqRangeFacts` growth bound (S8ai) over a SYMBOLIC
  # receiver long enough to force the solver to reason about the real op
  # rather than fold it concretely.
  if s.len > 5 and ':' notin s and s.replace(":", ";;") != s:
    symexTarget("s8aq_replace_no_occurrence_unreachable")

suite "S8aq (3): str.replace_all is reachable (this suite's -d:z3WithSeqReplaceAll)":
  # This suite's `-d:z3WithSeqReplaceAll` only turns ON the attempt to use
  # the real `Z3_mk_seq_replace_all`; the symbol itself is still absent
  # below Z3 4.16 (`scripts/dt-bounded.sh` vs `$S/s8o/dt413.sh`), where the
  # new `Z3FeatureUnavailableError` catch (item 3's other half) degrades
  # exactly like the compile-time-gated-off case: a fresh, unconstrained
  # string stands in for the result, so a content claim the real op would
  # forbid becomes trivially SAT instead. Both outcomes are honest (never a
  # crash, never a false SAT/UNSAT against the REAL op) -- these tests
  # accept either, keyed off whether `seZ3VersionMissing` actually fired.

  test "end to end: every occurrence is replaced (the real op, not a free symbol)":
    let r = symexFind(replaceAllCorrect, tLabel("s8aq_replace_all_correct"))
    checkpoint show(r.errors)
    if hasKind(r.errors, seZ3VersionMissing):
      check r.status == sxSat  # declined: a free fresh symbol can equal "barbar" too
    else:
      check r.status == sxSat
      for e in r.errors: check e.kind != seZ3VersionMissing

  test "end to end: the first-occurrence-only result is unreachable under the real op":
    # On a Z3 build with the real op: GREEN because `str.replace_all`
    # forbids it. On a Z3 build without it (even with the define on): the
    # chokepoint's `Z3FeatureUnavailableError` catch degrades to a free
    # fresh symbol, so the ABSTRACT query is SAT against "barfoo" -- but
    # `dcFreshSymbol`'s `scSpurious` replay then runs the REAL
    # `strutils.replace` on the witness concretely, finds it actually
    # yields "barbar" (never "barfoo"), and refutes the candidate
    # (`feReplayRefuted`): a confirmed model gap, `sxUnknown`, never a
    # wrong `sxSat`.
    let r = symexFind(replaceFirstOnlyUnreachable, tLabel("s8aq_replace_first_only"))
    checkpoint show(r.errors)
    if hasKind(r.errors, seZ3VersionMissing):
      check r.status == sxUnknown
      check hasKind(r.errors, feReplayRefuted)
    else:
      check r.status == sxUnsat

  test "end to end: no occurrence leaves a symbolic receiver unchanged":
    # Degraded: same shape as above -- the real `strutils.replace` leaves
    # a string with no ":" unchanged, so a fresh stand-in claiming
    # inequality is replay-refuted (`sxUnknown`), never confirmed SAT.
    let r = symexFind(replaceGrowthAndRoundtrip,
                      tLabel("s8aq_replace_no_occurrence_unreachable"))
    checkpoint show(r.errors)
    if hasKind(r.errors, seZ3VersionMissing):
      check r.status == sxUnknown
      check hasKind(r.errors, feReplayRefuted)
    else:
      check r.status == sxUnsat

# ---- (4) a missed IMPLIED equality costs completeness, never soundness ----

proc qYZ(ctx: Z3Context; src: string): seq[Z3Bool] =
  ## Like `q`, plus two more needles (`y`, `z`) `decls` does not declare.
  parseSmt2String(ctx, decls & "(declare-const y String) (declare-const z String)\n" & src)

suite "S8aq (4): a missed implied (non-stated) equality costs completeness only":

  test "step 1c misses a needle equal only through an implied (non-stated) equality":
    # `y` and `z` are EQUAL in every model: concatenation is injective in
    # its right-hand argument, so `y ++ "x" == z ++ "x"` implies `y == z`
    # (a basic word equation, decided fast by any sequence theory) -- but
    # no `(= y z)` is ever asserted or anywhere in the AST (not even inside
    # a disjunct), and `Z3_simplify` does not fold one free variable to
    # another it is merely constrained equal to this way. `seqRangeFacts`'
    # union-find (`cls`/`join`) joins the two CONCATENATION terms (the
    # asserted equality's own two sides) into one class, but never
    # descends through `str.++` to join `y` and `z` themselves -- so they
    # land in different classes, and the needle-equal-to-known-literal
    # link (the one `tsymex_rfc0005_s8ai_semantic.nim`'s "needle equal
    # through one equality" test gets for a STATED `(= y z)`) never fires
    # here.
    let ctx = newContext()
    let roots = qYZ(ctx, """
      (assert (= (str.++ y "x") (str.++ z "x")))
      (assert (> (str.indexof s y 0) 200))
      (assert (not (str.contains s z)))""")
    check stepOneC(ctx, roots) != zsUnsat

  test "the full (uncapped) sequence theory still decides it: soundness is unaffected":
    # The SAME query, decided by the REAL sequence theory (no caps, no
    # facts-only shortcut) -- exactly what `checkCapped` falls through to
    # (steps 2/3) when step 1c declines. Z3 itself derives the implied
    # equality (concatenation injectivity is basic word-equation
    # reasoning, not a hard search), so the missed LINK costs step 1c a
    # decision, never the walker a wrong one.
    let ctx = newContext()
    let roots = qYZ(ctx, """
      (assert (= (str.++ y "x") (str.++ z "x")))
      (assert (> (str.indexof s y 0) 200))
      (assert (not (str.contains s z)))""")
    check querySolver(ctx, roots, 1_000_000'u).check() == zsUnsat

suite "S8aq: walker version floor":
  test "symexWalkerVersion >= 187":
    check parseInt(symexWalkerVersion) >= 187
