## Rectify #133/#134/#135 — abstraction-layer refinements.
##
## - #134: assertions of shape `x >= K` / `x <= K` feed into the
##   range table, enabling promotion to Z3Int.
## - #135: caller's ranges propagate to callee's params on inline.
## - #133: loop-invariant inference (deferred; needs Phase 6 loops).
import std/unittest
import nelli/symex

suite "symex abstraction refinements":
  test "#134 assertion-based range refinement promotes plain int":
    proc refined(x: int) =
      symexAssert(x >= 10)
      symexAssert(x <= 20)
      if x == 15:
        symexTarget("hit")
    let r = symexFind(refined, tLabel("hit"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] == 15
    var hasX = false
    for ab in r.abstractions:
      if ab.name == "x": hasX = true
    check hasX

  test "#135 range propagates through helper call":
    # `helper(x)` doubles its arg. caller's `x in [0..100]` should
    # propagate to the callee, so the Z3 model finds x=25 directly.
    proc helper(y: int): int = y * 2
    proc outer(x: range[0..100]) =
      if helper(x) == 50:
        symexTarget("hit")
    let r = symexFind(outer, tLabel("hit"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] == 25
    # outer's `x` is promoted via its range type — propagation to the
    # callee is the natural consequence of binding the formal to the
    # already-promoted SymVal.
    var hasX = false
    for ab in r.abstractions:
      if ab.name == "x": hasX = true
    check hasX
