import std/unittest
import nelli/symex

# Phase 15 — Cluster L cycle L2: untyped template parameters (verification).

# sub-test 1: untyped-param template that expands to supported nodes.
template assertPositive(x: untyped) =
  if x <= 0: discard
proc l2ok(n: int) =
  assertPositive(n)
  if n > 0: symexTarget("positive")

# sub-test 2: an untyped-param template whose expansion CONSTRAINS the path.
# `requireEq` expands to `if n != k: return`, so the early return must be
# faithfully walked — if the template body were skipped, the contradiction
# below would look reachable (sxSat); honoring it yields sxUnsat.
template requireEq(x: untyped, k: int) =
  if x != k: return
proc l2constrained(n: int) =
  requireEq(n, 5)                       # expands to: if n != 5: return
  if n == 6: symexTarget("contradiction")   # n==5 ∧ n==6 ⇒ unreachable

suite "symex Phase 15 — L2 untyped template params":

  test "untyped-template SUT body parses without unknown residuals -> sxSat":
    let r = symexFind(l2ok, tLabel("positive"))
    check r.status == sxSat

  test "untyped-template expansion is faithfully walked (constraint honored)":
    # If the `if n != 5: return` from the template were dropped, n==6 would be
    # reachable (sxSat). Honoring it makes n==5 ∧ n==6 unsatisfiable -> sxUnsat.
    let r = symexFind(l2constrained, tLabel("contradiction"))
    check r.status == sxUnsat
