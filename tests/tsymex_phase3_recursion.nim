## Phase 3 — bounded recursion via `maxCallDepth`.
##
## A recursive helper is inlined repeatedly until the call stack
## reaches `maxCallDepth` (default 3). Calls beyond that depth flag
## the *path* as uncertain (a fresh unconstrained symbol replaces the
## return value); any target reached only on uncertain paths
## degrades the verdict from `sxSat` to `sxUnknown`.
from ./s8cu_helpers import named
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc fib(n: int): int =
  if n <= 1:
    return n
  return fib(n - 1) + fib(n - 2)

proc fibTarget(x: int) =
  if fib(x) == 2:
    symexTarget("hit")

suite "symex Phase 3 — bounded recursion":
  test "depth-3 recursion completes; witness reaches the target":
    let r = pinFind(fibTarget, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 3

  test "depth-overflow target → sxUnknown (uncertain witness rejected)":
    # fib(7) = 13 — the only x satisfying fib(x) == 13. Reaching it
    # needs depth ≫ 3 (the default cap). With per-path uncertainty
    # tracking we report `sxUnknown` rather than emitting a fake
    # witness via the bailed-call's unconstrained retSym.
    proc fibDeep(x: int) =
      if fib(x) == 13:
        symexTarget("deep")
    let r = pinFind(fibDeep, tLabel("deep"))
    check r.status == sxUnknown
    check r.errors.named(beBudgetExhaustedUnmodelled)

  test "custom maxCallDepth=1 — even shallow recursion bails":
    # With maxCallDepth=1, fib's first internal recursion is already
    # at depth 2 → bails → uncertain. Even fib(3) ≡ 2 becomes
    # unreachable on certain paths.
    proc settings1(): SymexSettings =
      result = defaultSymexSettings()
      result.budget.maxCallDepth = 1
    let r = pinFind(fibTarget, tLabel("hit"), settings1())
    check r.status == sxUnknown
    check r.errors.named(beBudgetExhaustedUnmodelled)
