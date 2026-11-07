## RFC-0016 WA-A (P3). A consumer that imports nelli under a check `push`
## changes what nelli's own modules read: `buildSemantics` is a constant of
## `buildprofile.nim`, evaluated where that module is first compiled. This
## default (checks-on) build imports nelli under `push overflowChecks: off`.
import std/[unittest, strutils]
{.push overflowChecks: off.}
import nelli
import nelli/symex
{.pop.}

suite "WA-A import under a push":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 285

  test "the profile reads the push as the build, and the walker follows it":
    # Documented in `buildprofile.nim`: there is no decline for this, only the
    # advice to import nelli before the push.
    check coOverflow notin buildSemantics.checks
    check buildWraps()
    check acOverflow notin defaultSymexSettings().arithChecks
