## RFC-0005 (soundness channels) slice S8ag -- S8y's remainder: the
## one-character `str.indexof` split.
##
## `s.find(c, i)` with a one-character literal needle -- what every closed
## form of the scan idiom finds (Q1's `tryRecognizeScanIdiom`, B3's
## `tryRecognizeScanPairIdiom`, B4's `tryRecognizeAccumulatingScan`) --
## lowered to Z3's `str.indexof(s, c, i)`. On `tsymex_r6_n36_raise_degrade`'s
## readCString pair loop the five-deep chains of those terms ran out of the
## tainted 20M budget in every context measured. It now lowers to a fresh
## Int `ix` with the split axioms (`indexSplitAxioms`):
##   ix = -1, or s = pre ++ x ++ c ++ post, len(pre) = i, ix = i + len(x),
##            c notin x
##   ix = -1 implies i < 0, or i > len(s), or c notin s[i ..]
## (`c notin t` as the regex membership `t in (allchar & ~c)*`; the
## differential in (1) checks that form)
## and, between two splits of one haystack, the chain fact
## (`indexSplitChain`): with both found and the second starting at the
## first's match plus one, its prefix is the first's prefix through the
## match. A query asserts the axioms of each split it reaches
## (`indexSplitRoots`, through `globalRoots`).
##
## Pinned here:
##   (1) the equivalence, by a randomized differential check against Z3's
##       own `str.indexof` on small strings, which a deliberately broken
##       axiom fails; and the chain fact's validity the same way;
##   (2) each closed form of the idiom (Q1, B3, B4) lowers through the
##       split and keeps its verdict and a replaying witness;
##   (3) step 1c still links a split's Int as the `str.indexof` it stands
##       for (S8ae's `find > 200 and notin` refutation);
##   (4) N36-1's pair loop at the default budget: no target-hit solve runs
##       out, and the verdict stays `sxUnknown` -- never `sxUnsat`. Pinned
##       where that loop already runs, so it is not walked twice:
##       `tsymex_r6_n36_raise_degrade` (N36-1, N36-1-noblock) and
##       `tsymex_rfc0005_s1c_verdict` (its N36 test), by `budgetOut`,
##       `slowSat` and `rlimit` units;
##   (5) a tainted hit whose model search ran out its first half before the
##       uncapped search found a model (S8y's "step 1 out, step 3 SAT") is
##       under the same scoped decline as a budget-out: the rule itself by
##       `classifyTargetSolve`, the walk by which kind of costly hit Z3
##       gives (a slow SAT on 5.1, a budget-out on 4.13.4).
import std/[unittest, strutils, random, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: openArray[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & ": " & e.msg & "\n"

proc sidx(ctx: Z3Context; s, t: Z3String; i: Z3Int): Z3Int =
  ## Z3's own `str.indexof`, the reference.
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_index(ctx.raw, s.raw, t.raw, i.raw))

proc freshSplit(ctx: Z3Context; tag: string; s, c: Z3String;
                start: Z3Int): IndexSplit =
  IndexSplit(ix: mkIntVar(ctx, tag), s: s, c: c, start: start,
             pre: mkStringVar(ctx, tag & "_pre"),
             x: mkStringVar(ctx, tag & "_x"),
             post: mkStringVar(ctx, tag & "_post"))

proc lit(ctx: Z3Context; s: string): Z3String = mkString(ctx, s)

type AxiomBuilder = proc (sp: IndexSplit): seq[Z3Bool]

proc landed(sp: IndexSplit): seq[Z3Bool] =
  let ax = indexSplitAxioms(sp)
  @[ax.found, ax.notFound]

proc dropNotInGap(sp: IndexSplit): seq[Z3Bool] =
  ## Mutant: the found arm without `c notin x`, so `ix` may be a later
  ## occurrence than the first.
  let ctx = sp.s.ctx
  let found = (sp.ix >= mkInt(ctx, 0)) and
    (sp.s == concat(sp.pre, concat(sp.x, concat(sp.c, sp.post)))) and
    (len(sp.pre) == sp.start) and (sp.ix == sp.start + len(sp.x))
  @[(sp.ix == mkInt(ctx, -1)) or found, indexSplitAxioms(sp).notFound]

proc startAtLenFound(sp: IndexSplit): seq[Z3Bool] =
  ## Mutant: the not-found arm's range off by one (`start >= len(s)`
  ## counted as out of range is right; `start >= len(s) - 1` is not): a
  ## needle in the last position may be reported absent.
  let ctx = sp.s.ctx
  let lenS = len(sp.s)
  @[indexSplitAxioms(sp).found,
    implies(sp.ix == mkInt(ctx, -1),
      (sp.start < mkInt(ctx, 0)) or (sp.start >= lenS - mkInt(ctx, 1)) or
      (not contains(substr(sp.s, sp.start, lenS - sp.start), sp.c)))]

proc differential(build: AxiomBuilder; rounds: int; seed: int64): string =
  ## "" when, on `rounds` random instances -- `s` over {'a', ':', '\0',
  ## '\xff'} of length 0..5, needle ':' or '\0', start in -2 .. len(s) + 2
  ## -- the axioms under `s` and `start` fixed are SAT, and `ix` differs
  ## from Z3's `str.indexof` in no model (`ix != indexof` is UNSAT). Else
  ## the first instance that disagrees.
  var r = initRand(seed)
  const alphabet = ['a', ':', '\0', '\xff']
  for round in 0 ..< rounds:
    let ctx = newContext()
    var s = ""
    for _ in 0 ..< r.rand(0 .. 5): s.add alphabet[r.rand(0 .. 3)]
    let c = if r.rand(0 .. 1) == 0: ":" else: "\0"
    let start = r.rand(-2 .. s.len + 2)
    let sv = mkStringVar(ctx, "s")
    let iv = mkIntVar(ctx, "i")
    let sp = freshSplit(ctx, "ix", sv, lit(ctx, c), iv)
    let pins = @[sv == lit(ctx, s), iv == mkInt(ctx, start)]
    let what = "s=" & s.escape & " c=" & c.escape & " start=" & $start
    let sat = newSolver(ctx)
    for a in build(sp): sat.add a
    for p in pins: sat.add p
    if sat.check() != zsSat: return what & ": axioms UNSAT"
    let differ = newSolver(ctx)
    for a in build(sp): differ.add a
    for p in pins: differ.add p
    differ.add sp.ix != sidx(ctx, sv, lit(ctx, c), iv)
    let st = differ.check()
    if st != zsUnsat:
      return what & ": ix != str.indexof is " & $st
  ""

suite "S8ag (1): the split is str.indexof, for a one-character needle":

  test "randomized differential against Z3's str.indexof":
    check differential(landed, 300, 0x5a6) == ""

  test "the check catches a found arm without `c notin x`":
    check differential(dropNotInGap, 300, 0x5a6) != ""

  test "the check catches an off-by-one not-found range":
    check differential(startAtLenFound, 300, 0x5a6) != ""

  test "start = len(s), start > len(s) and start < 0 are -1, as Z3's":
    ## The boundary cases by name, beside the random sweep.
    for (s, start, want) in [("ab:", 3, -1), ("ab:", 2, 2), ("ab:", 4, -1),
                             ("ab:", -1, -1), ("", 0, -1), (":", 0, 0)]:
      let ctx = newContext()
      let sv = mkStringVar(ctx, "s")
      let sp = freshSplit(ctx, "ix", sv, lit(ctx, ":"), mkInt(ctx, start))
      let solver = newSolver(ctx)
      for a in landed(sp): solver.add a
      solver.add sv == lit(ctx, s)
      solver.add sp.ix != mkInt(ctx, want)
      check solver.check() == zsUnsat

  test "the chain fact holds on every random two-scan instance":
    ## Two splits of one haystack, the second starting one past the first's
    ## value (readCString's next key): the chain fact's negation is UNSAT
    ## under both splits' axioms and the haystack fixed.
    var r = initRand(0x5a7)
    const alphabet = ['a', ':', '\0']
    for round in 0 ..< 150:
      let ctx = newContext()
      var s = ""
      for _ in 0 ..< r.rand(0 .. 6): s.add alphabet[r.rand(0 .. 2)]
      let sv = mkStringVar(ctx, "s")
      let c = lit(ctx, "\0")
      let a = freshSplit(ctx, "a", sv, c, mkInt(ctx, r.rand(0 .. 2)))
      let b = freshSplit(ctx, "b", sv, c, a.ix + mkInt(ctx, 1))
      let solver = newSolver(ctx)
      for x in landed(a) & landed(b): solver.add x
      solver.add sv == lit(ctx, s)
      solver.add not indexSplitChain(a, b)
      let st = solver.check()
      checkpoint "s=" & s.escape
      check st == zsUnsat

# ---- (2) the three closed forms of the scan idiom ---------------------------

proc q1ScanTo(s: string) =
  ## Q1 (`tryRecognizeScanIdiom`): the bounded forward scan to a literal.
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 3 and s.len > 5:
    symexTarget("s8ag_q1")

proc b3FirstColon(s: string): int =
  ## B3 (`tryRecognizeScanPairIdiom`): the early-return scan.
  var i = 0
  while i < s.len:
    if s[i] == ':':
      return i
    inc i
  -1

proc b3Caller(s: string) =
  if b3FirstColon(s) == 2:
    symexTarget("s8ag_b3")

type ScanErrorS8ag = object of CatchableError

proc b4ReadCString(s: string, offset: int): (string, int) =
  ## B4 (`tryRecognizeAccumulatingScan`): the readCString scan.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanErrorS8ag, "unterminated")

proc b4Caller(s: string) =
  let (k, p) = b4ReadCString(s, 0)
  let (v, _) = b4ReadCString(s, p)
  if k == "ab" and v.len == 1:
    symexTarget("s8ag_b4")

suite "S8ag (2): each closed form of the idiom lowers through the split":

  test "Q1: the scan's find is a split; sxSat, the witness has ':' at 3":
    let r = symexFind(q1ScanTo, tLabel("s8ag_q1"))
    checkpoint show(r.errors)
    check indexSplits.len > 0
    check r.status == sxSat
    if r.status == sxSat:
      let s = r.witness[0]
      check s.len > 5 and s.find(':') == 3

  test "B3: the early-return scan's find is a split; sxSat":
    let r = symexFind(b3Caller, tLabel("s8ag_b3"))
    checkpoint show(r.errors)
    check indexSplits.len > 0
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].find(':') == 2

  test "B4: two chained readCStrings are splits with a chain; sxSat":
    let r = symexFind(b4Caller, tLabel("s8ag_b4"))
    checkpoint show(r.errors)
    check indexSplits.len >= 2
    check r.status == sxSat
    if r.status == sxSat:
      let s = r.witness[0]
      let k = s.find('\0')
      check k == 2 and s[0 ..< 2] == "ab"
      check s.find('\0', k + 1) == k + 2

suite "S8ag (3): step 1c links a split's Int as its str.indexof":

  test "find > 200 and notin: refuted theory-free through the split":
    ## S8ae's `s.find(':') > 200 and ':' notin s`, with the find a split.
    ## Theory-free, `contains` is uninterpreted, so only `seqRangeFacts`'
    ## link (`indexof >= 0` implies `contains`) refutes it.
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let colon = oneCharLiteral(fromCode(ctx, mkInt(ctx, 58)))
    check colon.isSome
    let ix = lowerIndexSplit(s, colon.get, mkInt(ctx, 0))
    var roots = @[ix > mkInt(ctx, 200), not contains(s, colon.get)]
    roots.add indexSplitRoots(ctx, roots)
    check roots.len > 2
    let tf = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
    check tf.check() == zsSat
    let linked = querySolver(ctx, roots, 1_000_000'u, seqTheory = false)
    for f in seqRangeFacts(ctx, roots): linked.add f
    check linked.check() == zsUnsat

  test "a split registered in another context is not linked":
    let other = newContext()
    discard lowerIndexSplit(mkStringVar(other, "s"), mkString(other, ":"),
                            mkInt(other, 0))
    let ctx = newContext()
    check indexSplitRoots(ctx, @[mkBool(ctx, true)]).len == 0
    check registeredIndexSplit(ctx, mkIntVar(ctx, "__s8ag_ix1").raw) == -1

  test "a needle of two characters, or a computed one, is not split":
    let ctx = newContext()
    check oneCharLiteral(mkString(ctx, "ab")).isNone
    check oneCharLiteral(mkString(ctx, "")).isNone
    check oneCharLiteral(mkStringVar(ctx, "t")).isNone
    check oneCharLiteral(mkString(ctx, "\xff")).isSome

proc pairLoopS8ag(s: string) =
  ## N36-1's shape (as `tsymex_rfc0005_s8y_budget_decline`'s pair loop):
  ## the two-hop local counter makes every hit past the loop tainted.
  block:
    var localOffset = 0
    var i = localOffset
    var pairs: seq[(string, string)] = @[]
    while i < s.len:
      let (key, p1) = b4ReadCString(s, i)
      if key.len == 0:
        break
      let (val, p2) = b4ReadCString(s, p1)
      pairs.add((key, val))
      i = p2
  symexTarget("s8ag_pair_after")

const midTainted = SymexSettings(
  budget: ResourceBudget(seqQueryRLimit: 400_000))
  ## At 400k a pair-loop hit is costly on both Z3 versions, and shallow
  ## enough that deeper hits follow it: on Z3 5.1 it is a slow SAT (step 1
  ## out, step 3 SAT; 0 budget-outs, 7 declines), on 4.13.4 a budget-out
  ## (3 declines). Which one depends on the Z3 build and even the
  ## process's earlier contexts, so the walk is pinned on what both share,
  ## and the slow-SAT classification itself by `classifyTargetSolve`.

suite "S8ag (5): a tainted SAT after half its budget bounds later hits":

  test "classifyTargetSolve: a SAT after half the budget is slow":
    check classifyTargetSolve(sxSat, 500, 1000) == tscSlowSat
    check classifyTargetSolve(sxSat, 999, 1000) == tscSlowSat
    check classifyTargetSolve(sxSat, 499, 1000) == tscCheap
    check classifyTargetSolve(sxUnknown, 1000, 1000) == tscBudgetOut
    check classifyTargetSolve(sxUnknown, 999, 1000) == tscCheap
    # An UNSAT is no candidate and bounds nothing, however costly.
    check classifyTargetSolve(sxUnsat, 1000, 1000) == tscCheap
    # An unbounded solve is never costly.
    check classifyTargetSolve(sxSat, 10_000_000, 0) == tscCheap
    check classifyTargetSolve(sxUnknown, 10_000_000, 0) == tscCheap

  test "a costly tainted hit bounds the deeper ones; with no budget-out it was a slow SAT":
    symexTargetSolveStats = default(typeof(symexTargetSolveStats))
    let r = symexFind(pairLoopS8ag, tLabel("s8ag_pair_after"), midTainted)
    let st = symexTargetSolveStats
    checkpoint show(r.errors)
    checkpoint "stats=" & $st
    check st.budgetOut + st.slowSat >= 1
    check st.declined >= 1
    # Before S8ag a decline needed a budget-out; now a slow SAT alone
    # gives one (Z3 5.1 at this budget).
    if st.budgetOut == 0:
      check st.slowSat >= 1
    check st.slowSat <= 1
    # Each target-hit solve is bounded by the budget, so the walk's total
    # is too, and in practice far below (solved hits) x 400k.
    check st.units < 8 * 400_000
    check r.status == sxUnknown

  test "the declines are classified beSolverUndef, never sxUnsat":
    let r = symexFind(pairLoopS8ag, tLabel("s8ag_pair_after"), midTainted)
    var declined = false
    for e in r.errors:
      if e.kind == beSolverUndef and "not solved (RFC-0005 S8y)" in e.msg:
        declined = true
    checkpoint show(r.errors)
    check declined
    check r.status != sxUnsat

suite "S8ag: walker version floor":
  test "symexWalkerVersion >= 182":
    check parseInt(symexWalkerVersion) >= 182
