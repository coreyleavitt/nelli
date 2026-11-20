## RFC-0016 0.10.0 review D3c-2: the lower hooks of `walk_state.nim`.
##
## `runtime.nim` fills `lowerHooks` once, at module init. Every field must be
## non-nil after `import nelli/smt/runtime`, so the slices that switch the
## include files over to the hooks find them ready; a field added to
## `LowerHooks` and not filled fails here, not as a nil call mid-walk.
import std/unittest
import nelli/smt/runtime
import nelli/smt/[walk_state]   ## R2-3: the leaves are no longer re-exported by the facade

suite "RFC-0016 D3c-2: lowerHooks":
  test "every hook is filled at module init":
    var n = 0
    for name, f in fieldPairs(lowerHooks):
      checkpoint name
      check not f.isNil
      inc n
    # The exact inventory: lower, lowerClosureCall, currentFrameId,
    # registerCapCell, depositStrIndexOob, (INT-87, 9e37524b)
    # depositUndefinedOob and (INT-34 B3) noteUbAtFork, which the fork
    # templates of the `walk_path` leaf call on the rare path. Each is filled
    # in `runtime.nim`'s `lowerHooks = LowerHooks(...)`; an eighth must be
    # named here.
    check n == 7

