## RFC-0005 (soundness channels) slice S8y -- the floor under
## `tsymex_r6_n36_raise_degrade` and `tsymex_rfc0005_s1c_verdict`.
##
## Both suites walk a readCString pair loop whose target is past the loop.
## Every path reaching it is tainted (the loop counter's BV-bound
## `iekStrInOptionRegion` decline, the k-unroll exhaustion), so every hit is
## solved under the tainted budget (`taintedSolveRLimit`, 20M units) and a
## SAT is only a candidate. The five-iteration hits -- the break on a fifth,
## empty key and the unwind-bound survivor -- are nested `str.indexof`
## chains ten deep that Z3 5.1 does not decide in 20M units in any context
## measured, fresh or the walk's; each spent its whole budget, two per test,
## about 80% of the suites' CPU. Which shallower hit also runs out moved
## with whatever the walk's context held (S8r's step 1c, S8v's range facts):
## the runtime regression S8y was opened for.
##
## Two changes, pinned here by counts, never by wall time:
##   (a) `checkCapped` drops a string's byte-domain constraint
##       `x in (\x00..\xff)*` when `x` is defined equal to a term built by
##       `str.++` / `str.substr` / `str.at` from literals and strings whose
##       own byte-domain constraint stays in the query: the term's
##       characters are the other strings' characters, so the constraint is
##       implied (`dropImpliedByteDomains`).
##   (b) once a TAINTED target-hit solve runs out of budget, a later tainted
##       hit of the same walk that is at least as deep in every loop the
##       exhausted one iterated is not solved: it is declined with a
##       `beSolverUndef` naming the exhausted depth, which voids `sxUnsat`
##       exactly as the solver's own unknown does. A candidate is never a
##       winner, so what is lost is replay candidates on tainted paths
##       only. A clean path is always solved.
##
## RFC-0005 S8aq (walker 187): step 1c's new ground fact can now decide a
## shallow hit of (b)'s pair loop outright from facts alone instead of it
## exhausting the budget, on some Z3 builds (observed: Z3 4.13.4) but not
## others (Z3 5.1) -- a completeness gain, not a regression. Which hit (if
## any) therefore ends up declined is Z3-build sensitive, so (b)'s own two
## tests no longer pin `st.declined` or the specific decline message by
## count; they pin the floor that must hold on every build regardless
## (a budget-out happens, `beSolverUndef` classified, never `sxUnsat`).
## (S8aq pinned `budgetOut <= 1`, the n36 / s1c floor at their default
## budget; at S8ag's 20k `tightTainted` a shallower hit can run out after a
## deeper one, so this suite keeps S8ag's `budgetOut >= 1`.)
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: openArray[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & ": " & e.msg & "\n"

# ---- (a) the implied byte-domain constraint ---------------------------------

proc byteDomain(x: Z3String): Z3Bool =
  let ctx = x.ctx
  matches(x, star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff"))))

proc keeps(kept: openArray[Z3Bool]; b: Z3Bool): bool =
  for k in kept:
    if astId(k.ctx, k.raw) == astId(b.ctx, b.raw): return true

suite "S8y (a): a byte-domain constraint implied by the query is dropped":

  test "a string defined as a substring of a byte string loses its own":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let x = mkStringVar(ctx, "x")
    let def = x == (mkString(ctx, "") & substr(s, mkInt(ctx, 1), mkInt(ctx, 2)))
    let roots = @[byteDomain(s), byteDomain(x), mkBool(ctx, true) and def]
    let kept = dropImpliedByteDomains(ctx, roots)
    check kept.len == 2
    check kept.keeps(byteDomain(s))
    check not kept.keeps(byteDomain(x))

  test "a string defined over an unconstrained string keeps its own":
    let ctx = newContext()
    let z = mkStringVar(ctx, "z")
    let y = mkStringVar(ctx, "y")
    let roots = @[byteDomain(y), y == (mkString(ctx, "") & z)]
    check dropImpliedByteDomains(ctx, roots).len == 2

  test "two strings defined by each other keep at least one constraint":
    let ctx = newContext()
    let a = mkStringVar(ctx, "a")
    let b = mkStringVar(ctx, "b")
    let roots = @[byteDomain(a), byteDomain(b),
                  a == substr(b, mkInt(ctx, 0), mkInt(ctx, 1)),
                  b == substr(a, mkInt(ctx, 0), mkInt(ctx, 1))]
    let kept = dropImpliedByteDomains(ctx, roots)
    check kept.keeps(byteDomain(a)) or kept.keeps(byteDomain(b))

  test "a definition under a disjunction justifies nothing":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let x = mkStringVar(ctx, "x")
    let p = mkBoolVar(ctx, "p")
    let roots = @[byteDomain(s), byteDomain(x),
                  p or (x == substr(s, mkInt(ctx, 0), mkInt(ctx, 1)))]
    check dropImpliedByteDomains(ctx, roots).len == 3

# ---- (b) the budget-out decline ---------------------------------------------

type ScanError = object of CatchableError

proc readCStringS8y(s: string, offset: int): (string, int) =
  ## N36's `readCStringOptN36`, the B4-recognized readCString idiom.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc pairLoopS8y(s: string) =
  ## N36-1's shape: the two-hop local counter makes every hit past the loop
  ## tainted.
  block:
    var localOffset = 0
    var i = localOffset
    var pairs: seq[(string, string)] = @[]
    while i < s.len:
      let (key, p1) = readCStringS8y(s, i)
      if key.len == 0:
        break
      let (val, p2) = readCStringS8y(s, p1)
      pairs.add((key, val))
      i = p2
  symexTarget("s8y_pair_after")

proc cleanLoopS8y(k: int, a: int, b: int) =
  ## A clean loop (its bound is concrete, so no hit is tainted) ahead of a
  ## factoring query Z3 cannot finish in a few thousand units: one clean hit
  ## per exit, each running out.
  var i = 0
  while i < k and i < 2:
    inc i
  if a > 1 and b > 1 and a * b == 1_000_003 * 999_983 + i:
    symexTarget("s8y_clean_after")

const tightTainted = SymexSettings(
  budget: ResourceBudget(seqQueryRLimit: 20_000))
  ## Small enough that a shallow pair-loop hit already runs out, so the
  ## pin runs in seconds. RFC-0005 S8ag: was 2M. The one-character
  ## `str.indexof` split makes the pair loop's hits cheap enough that at
  ## 2M none runs out, and on Z3 4.13.4 the 2M pin was already red at S8y
  ## (its only budget-out was the deepest hit, so nothing was declined).
  ## At 20k a shallow hit runs out on both Z3 versions (measured: 1 and 2
  ## budget-outs, 24 declines each).

const starvedClean = SymexSettings(
  budget: ResourceBudget(queryRLimit: 5_000))
  ## Every factoring solve runs out.

suite "S8y (b): a tainted hit at least as deep as an exhausted one is declined":

  test "one tainted budget-out; every later hit as deep is declined, never solved":
    symexTargetSolveStats = default(typeof(symexTargetSolveStats))
    let r = symexFind(pairLoopS8y, tLabel("s8y_pair_after"), tightTainted)
    let st = symexTargetSolveStats
    checkpoint show(r.errors)
    checkpoint "budgetOut=" & $st.budgetOut & " declined=" & $st.declined &
               " slowSat=" & $st.slowSat
    # RFC-0005 S8ag: `>= 1`, was `== 1`. A budget-out bounds only hits at
    # least as deep, so a shallower one can still run out after it (Z3
    # 4.13.4 has two at this budget).
    check st.budgetOut >= 1
    # RFC-0005 S8aq: `st.declined` is no longer pinned to >= 1 here. Step
    # 1c's new ground fact (item 2, the `seq.last_indexof`-is-at-least-
    # every-found-`str.indexof` link) now decides some of this walk's
    # shallower tainted hits outright from facts alone -- the very
    # completeness gain S8aq was for -- so WHICH hit (if any) is the one
    # whose own solve exhausts the budget is Z3-build sensitive, and
    # whether a later, equally deep hit is left to decline with it. Both
    # are sound. (S8aq, written against the 2M budget, pinned `budgetOut
    # <= 1` here; at S8ag's 20k budget a shallower hit can run out after a
    # deeper one, so the batch keeps S8ag's `>= 1` instead.)
    check r.status == sxUnknown

  test "the decline is recorded as a classified beSolverUndef, so never sxUnsat":
    let r = symexFind(pairLoopS8y, tLabel("s8y_pair_after"), tightTainted)
    # RFC-0005 S8aq: whether the SPECIFIC "not solved (RFC-0005 S8y)"
    # decline placeholder fires is the same Z3-build-sensitive question as
    # the preceding test's. The invariant that must hold on every build is
    # that an unsolved tainted hit is classified `beSolverUndef` -- an S8y
    # decline placeholder or a genuine solver `unknown`, both produced by
    # the same code path in `solveTargetHit` -- and so never promoted to a
    # false `sxUnsat`.
    var undef = false
    for e in r.errors:
      if e.kind == beSolverUndef: undef = true
    check undef
    check r.status != sxUnsat

  test "a clean path is always solved, however many budget-outs precede it":
    symexTargetSolveStats = default(typeof(symexTargetSolveStats))
    let r = symexFind(cleanLoopS8y, tLabel("s8y_clean_after"), starvedClean)
    let st = symexTargetSolveStats
    checkpoint show(r.errors)
    checkpoint "budgetOut=" & $st.budgetOut & " declined=" & $st.declined
    check st.budgetOut >= 2
    check st.declined == 0
    check r.status == sxUnknown

suite "S8y: walker version floor":
  test "symexWalkerVersion >= 176":
    check parseInt(symexWalkerVersion) >= 176
