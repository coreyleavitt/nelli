## RFC-0016 code-review M1. `symexFind` expands, in the caller's module, to a
## `SymexResult` construction. That expansion must not name the deprecated
## `fromCache` field, or every user call site warns and a consumer building
## with `--warningAsError:Deprecated` cannot compile. The pragma below turns
## the warning into an error for THIS module only (a global
## `--warningAsError:Deprecated` would also trip nelli's own internals), so
## this file compiling is the assertion.
import std/unittest
import nelli/symex

{.warningAsError[Deprecated]: on.}

proc trivial(x: int) =
  if x == 7: symexTarget("seven")

suite "symexFind expansion is deprecation-clean":
  test "sat, and a no-target decline, both expand without a deprecated name":
    let r = symexFind(trivial, tLabel("seven"))
    check r.status == sxSat
    let u = symexFind(trivial, tLabel("not-a-marker"))
    check u.status != sxSat
