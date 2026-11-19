## RFC-0016 int6-w2: a stdlib routine declared inside a stdlib body that
## pushes check options is placed under that push.
##
## int6-a5 and int6-u decline a routine declared inside a body that pushes
## (`check_options.positionUnreadable`): it compiles under that push where it
## stands. Both reads, the definition text's (`pushingHost`) and the typed
## body's (`typedPushingHost`), were skipped for a stdlib routine, which was
## then read under its module's checks alone.
##
## No stdlib routine of 2.2.10 is declared so (a scan of its `lib/` text finds
## no routine nested in a routine whose body names a check option), so the
## skip lost nothing on the pinned toolchain; the typed read now holds for a
## stdlib routine too, sound by construction rather than by that census. The
## fixture is a module the scan classifies as the stdlib by its path
## (`tests/m6lib/lib/std/`), as `tsymex_0016_int6m6_stdbodypush`'s is.

import std/[unittest, macros, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/check_options
import ./m6lib/lib/std/s0016_w2_stdnest

proc nestedWhy(n: NimNode): string =
  ## `routineChecks(...).why` of the first routine declared inside `n`.
  for c in n:
    if c.kind == nnkProcDef: return routineChecks(c).why
    let r = nestedWhy(c)
    if r.len > 0: return r

macro innerWhy(host: typed): string =
  newLit(nestedWhy(host.getImpl[6]))

suite "int6-w2: a stdlib routine declared inside a pushing stdlib body":
  test "natively it compiles under the push":
    check stdNestHost(300) == 300

  test "its position is read as the push's: it declines":
    let why = innerWhy(stdNestHost)
    checkpoint why
    check "declared inside `stdNestHost`" in why

suite "int6-w2: walker version":
  test "walker version floor >= 483":
    check parseInt(symexWalkerVersion) >= 483
