## RFC-0016 W1-d1a / W1-d2, the checks-off BUILD half of the `low(T) div -1`
## row of `tsymex_0016_w1d1a_intminmod`. Built with `--overflowChecks:off` (its
## `.nim.cfg`): the C division is undefined, so the path halts through
## `haltUndefined` as `ubSignedOverflow`, and the default settings already
## follow the build.
import std/unittest
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutDivUnchecked(x: int) =
  if x == low(int):
    let q = x div -1
    if q == 0: symexTarget("hit")

suite "W1-d1a low(T) div -1, checks-off build":
  test "checks off: the path halts":
    let r = symexFind(sutDivUnchecked, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(ubSignedOverflow)
    check not r.errors.named(ubIntMinModMinusOne)
    check not r.errors.named(feCheckOption)
