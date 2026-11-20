## RFC-0016 0.10.0 review D3c-2: the lower hooks of `walk_state.nim`.
##
## `runtime.nim` fills `lowerHooks` once, at module init. Every field must be
## non-nil after `import nelli/smt/runtime`, so the slices that switch the
## include files over to the hooks find them ready; a field added to
## `LowerHooks` and not filled fails here, not as a nil call mid-walk.
import std/unittest
import nelli/smt/runtime
import nelli/smt/[walk_state, walk_path, lower_expr, walk_solve]   ## R2-3: the leaves are no longer re-exported by the facade

suite "RFC-0016 D3c-2: lowerHooks":
  test "every hook is filled at module init":
    var n = 0
    for name, f in fieldPairs(lowerHooks):
      checkpoint name
      check not f.isNil
      inc n
    # The exact inventory: lower, lowerClosureCall, currentFrameId,
    # registerCapCell, depositStrIndexOob, (INT-87, 9e37524b)
    # depositUndefinedOob (INT-87, 9e37524b). Each is filled in
    # `runtime.nim`'s `lowerHooks = LowerHooks(...)`; a seventh must be named
    # here.
    check n == 6

  test "every walk_path hook is filled at module init":
    # INT-34 B3b. `walk_path` declares its own typed `PathHooks` (it can name
    # `Path`, which `walk_state` cannot); the same rule holds: no field nil.
    var n = 0
    for name, f in fieldPairs(pathHooks):
      checkpoint name
      check not f.isNil
      inc n
    check n == 1   # noteUbAtFork; a second must be named here

  test "every lower_expr hook is filled at module init":
    # INT-34 B4. `lower_expr` declares its own typed `LowerExprHooks`, the
    # `PathHooks` pattern; the same rule holds: no field nil.
    var n = 0
    for name, f in fieldPairs(lowerExprHooks):
      checkpoint name
      check not f.isNil
      inc n
    check n == 1   # lowerHofCall; a second must be named here

  test "walk_solve declares no hook table":
    # INT-34 B5. Region R2 (`trySolve`, `pathInfeasible`, the witness) calls
    # nothing above it, so `walk_solve` has no typed hooks to fill. A hook
    # added there is declared as `walkSolveHooks` (the `PathHooks` pattern)
    # and replaces this test with the fill check above.
    check not declared(walkSolveHooks)
    check not declared(WalkSolveHooks)
