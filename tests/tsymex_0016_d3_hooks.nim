## RFC-0016 0.10.0 review D3c-2: the lower hooks of `walk_state.nim`.
##
## `runtime.nim` fills `lowerHooks` once, at module init. Every field must be
## non-nil after `import nelli/smt/runtime`, so the slices that switch the
## include files over to the hooks find them ready; a field added to
## `LowerHooks` and not filled fails here, not as a nil call mid-walk.
import std/unittest
import nelli/smt/runtime

suite "RFC-0016 D3c-2: lowerHooks":
  test "every hook is filled at module init":
    var n = 0
    for name, f in fieldPairs(lowerHooks):
      checkpoint name
      check not f.isNil
      inc n
    check n == 8

