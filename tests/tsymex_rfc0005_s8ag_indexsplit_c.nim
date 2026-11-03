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
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8ag_indexsplit`, `tsymex_rfc0005_s8ag_indexsplit_b`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 65 s).
import std/[unittest, strutils, random, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc show(errs: openArray[SymexErrorInfo]): string =
  for e in errs: result.add $e.kind & ": " & e.msg & "\n"

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
  test "symexWalkerVersion >= 183":
    check parseInt(symexWalkerVersion) >= 183
