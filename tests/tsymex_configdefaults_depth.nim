## RFC-0010 B4 round 2 -- an explicit finite `maxCallDepth` completes cleanly.
## Split from `tsymex_configdefaults` (RFC-0005 batch 8): this one test took 60
## to 150 s on the Windows runners, and the rest of that file about 14 s.
import std/unittest
import nelli/symex

proc runawayRecursion(n: int): int =
  if n > 0:
    result = runawayRecursion(n - 1) + 1
  else:
    result = 0

proc runawayRecursionSut(n: int) =
  if runawayRecursion(n) > 1_000_000:
    symexTarget("runaway_recursion_never")

suite "RFC-0010 B4 -- the default budget actually bounds a runaway search":

  test "an explicit finite maxCallDepth also completes cleanly (round 2 crash pin)":
    # Round 2: two independent reviewers reproduced a SIGSEGV (native stack
    # exhausted in under a second) against this EXACT SUT -- ordinary linear
    # countdown recursion, unconstrained `n` -- under `maxCallDepth: 0`.
    # Disabling the cap let the walker recurse natively without bound;
    # `w.activeCalls` does not cycle-break this shape because `f(n-1)` hashes
    # to a distinct Z3 AST at every level. This pins that an explicit FINITE
    # bound -- the honest way to ask for deeper analysis -- still completes
    # cleanly (no hang, no crash).
    #
    # The bound deliberately is NOT a "large-looking" round number. A direct
    # probe (throwaway, deleted after use) against this exact SUT found
    # unconstrained linear recursion safe through a cap of 85 and SIGSEGV by
    # 88 on this engine's Linux/podman debug build (8MB `ulimit -s`) -- i.e.
    # `maxCallDepth: 1000` ITSELF crashes here, because the cap bounds NATIVE
    # recursion depth and this walker's per-level native stack cost is large.
    # 50 sits with a wide, verified margin below that ceiling. Deliberately
    # never pass `maxCallDepth: 0` (or a naively "large" bound) in this
    # suite: that is the crash, and it would take this entire test binary
    # down with it, not just this one query.
    let r = symexFind(runawayRecursionSut, tLabel("runaway_recursion_never"),
        SymexSettings(budget: ResourceBudget(maxCallDepth: 50)))
    check r.status == sxUnknown
