## Phase 3 — stdlib model registry stub exists and is importable.
##
## The registry is empty in Phase 3; Phase 5+ will populate it with
## models for `seq`, `Table`, `HashSet`. The Phase-3 contract is
## just: the module is reachable and `getStdlibModel` returns the
## unregistered sentinel.
import std/unittest
import nelli/symex

suite "symex Phase 3 — stdlib model registry":
  test "registry stub returns unregistered for any callee":
    let m = getStdlibModel("len")
    check m.kind == smkUnregistered
    let m2 = getStdlibModel("anyUnknownCallee")
    check m2.kind == smkUnregistered
