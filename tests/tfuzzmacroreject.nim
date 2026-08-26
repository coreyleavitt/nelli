## RFC-fuzzer-nextgen E1 stage 2, C6: compile-time capture checks on the
## `fuzz(...)` macro. Two shapes must fail to compile, naming the offending
## identifier — the established `check not compiles(...)` idiom (see e.g.
## `tests/tderive.nim`, `tests/tsymex_phase15_N1_resolution_gates.nim`):
## since `fuzz` is a MACRO, writing the offending call directly inside
## `compiles(...)`'s argument defers its expansion (and our `error(...)`
## calls) into `compiles`'s isolated check — no separate not-yet-called proc
## wrapper needed (a regular `proc` body is compiled eagerly at its
## definition, which would fire the error outside of `compiles`'s catch).
##
## (a) a free reference to a local (not module-scope-reconstructible)
##     identifier; (b) a captured initializer calling a best-effort-
##     denylisted impure stdlib proc. A normal `fuzz(...)` call must still
##     `compiles`.

import std/[unittest, os]
import nelli

proc branchyProp(n: int) {.cover.} =
  if n mod 2 == 0:
    if n > 100: discard else: discard
  else:
    if n < -50: discard else: discard

suite "fuzz: call-site macro compile-time capture checks (RFC-fuzzer-nextgen E1 C6)":
  test "a normal fuzz(...) built purely from module-scope constructors compiles":
    check compiles(fuzz(integers(-10, 10), branchyProp, FuzzSettings(maxIterations: 5, seed: 1)))

  test "closing over a local let fails to compile, naming it (free-identifier check, C6a)":
    let localSeed = 5
    check not compiles(fuzz(integers(-localSeed, localSeed), branchyProp,
                             FuzzSettings(maxIterations: 5, seed: 1)))

  test "a strategy initializer calling getEnv fails to compile, naming it (impurity denylist, C6b)":
    check not compiles(fuzz(integers(0, len(getEnv("HOME"))), branchyProp,
                             FuzzSettings(maxIterations: 5, seed: 1)))
