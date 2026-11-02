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
    # The bound was sized by a probe on the c backend (safe through 85
    # levels on an 8 MB stack, SIGSEGV by 88), and on cpp, whose levels
    # cost more, these same 50 levels ran off the 8 MB stack: the binary
    # died with rc=139 here. RFC-0005 S8ca: a call is no longer inlined
    # when the native stack left is under one more level's need, so this
    # declines in-band on both backends, and so does any larger bound
    # (`tsymex_rfc0005_s8ca_stack`). `maxCallDepth: 0` still exhausts on
    # the first call, by design (above).
    let r = symexFind(runawayRecursionSut, tLabel("runaway_recursion_never"),
        SymexSettings(budget: ResourceBudget(maxCallDepth: 50)))
    check r.status == sxUnknown
