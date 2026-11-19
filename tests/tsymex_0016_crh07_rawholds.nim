## RFC-0016 CRH-07, the class: a raw Z3 handle held without a reference.
##
## `tsymex_0016_crh07_substowned` pins the first instance (`checkExact`'s
## unowned `Z3_substitute` results). The audit that followed walked every raw
## handle `src/nelli` stores (`tests/0016-allowlist/rawhold.txt`, enforced by
## `tsymex_0016_crh07_rawhold_census`) and found the instances pinned here,
## each reachable from a walk.
##
## 1. `xs.map(f)` over a symbolic-length seq built a `Z3FuncDecl` around the
##    closure's cached decl (`currentClosureSyms`) by object construction, so
##    no reference was taken, and the value's `=destroy` released the cache's
##    own reference. Once the mapped term died the decl was freed while still
##    cached; the next path to reach the same lambda site handed the freed
##    decl to `Z3_mk_map`. RED under the ASan libz3: heap-use-after-free.
##
## GREEN: each SUT runs to a verdict with no sanitizer report. In
## `scripts/asan-slice.sh`'s core set, which is where a regression shows: a
## stock libz3 reads the freed node silently.
import std/[unittest, sequtils, strutils]
import nelli/symex
import nelli/smt/canonicalize
from ./s8cu_helpers import pinFind

proc mapOnTwoPaths(xs: seq[int]; b: bool) =
  # Both paths lower the same lambda site, so the second takes the cached decl.
  var k = 0
  if b: k = 1
  let ys = xs.map(proc(x: int): int = x * 2)
  if ys.len > k:
    symexTarget("crh07_map_two")

proc mapTwiceInOnePath(xs: seq[int]) =
  for i in 0 ..< 2:
    let ys = xs.map(proc(x: int): int = x * 2)
    if ys.len > i:
      symexTarget("crh07_map_loop")

suite "RFC-0016 CRH-07: raw Z3 handles are owned":
  test "native agrees":
    check @[1, 2].map(proc(x: int): int = x * 2) == @[2, 4]

  test "map over a symbolic-length seq, the lambda site reached twice":
    # The map's function symbol is unconstrained (`ceUnsupportedHof`), so the
    # verdict is `sxUnknown`; what is pinned is a verdict and no stale decl.
    for i in 0 ..< 3:
      check pinFind(mapOnTwoPaths, tLabel("crh07_map_two")).status in
        {sxSat, sxUnknown}
      check pinFind(mapTwiceInOnePath, tLabel("crh07_map_loop")).status in
        {sxSat, sxUnknown}

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 372
