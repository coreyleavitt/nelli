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
##
## R8 (finding, closed here): (b) above only checked the TOP LEVEL of the
## captured expression — a denylisted call hidden one or more named-proc
## hops away (`proc seedFromEnv(): int = len(getEnv("HOME"))`, then
## `fuzz(integers(0, seedFromEnv()), ...)`) compiled clean. The RFC's own
## resolution ("checked through called procs, not just the top-level call")
## already called this in scope; `checkCallee`/`checkCalleeBody`
## (`fuzzmacro.nim`) now follow a named proc/func/method/converter into its
## own body via `getImpl`, bounded by depth + a visited set. The tests below
## prove: one-hop and two-hop impurity are now rejected; a self- or
## mutually-recursive helper does not hang the compiler; ordinary valid
## captures (a pure helper, a const, a call to a proc with no accessible
## body) still compile — false positives are worse than the residual false
## negative this closes.

import std/[unittest, os]
import nelli

proc branchyProp(n: int) {.cover.} =
  if n mod 2 == 0:
    if n > 100: discard else: discard
  else:
    if n < -50: discard else: discard

proc twoParamProp(x, y: int) {.cover.} =
  ## A genuinely multi-parameter property — two NAMES sharing one
  ## `nnkIdentDefs` group (`proc(x, y: int)`), not the tuple idiom
  ## (`proc(t: tuple[a, b: int])`, see `dictComboGate` in
  ## tests/tfuzzhavoc.nim). `countFormalParams` must count parameter NAMES,
  ## not `IdentDefs` groups, or this shape would be wrongly accepted as
  ## arity 1 (RFC-z3-optional R1-4).
  discard x + y

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

  test "a genuine multi-parameter property fails to compile (R1-4: arity check, not a silent mis-dispatch)":
    check not compiles(fuzz(integers(-10, 10), twoParamProp,
                             FuzzSettings(maxIterations: 5, seed: 1)))

## --- R8: impurity reached through a named-proc hop, not just the top level --

proc seedFromEnv(): int =
  ## Wraps a denylisted call ONE hop below the capture's own top level — the
  ## exact shape R8 reproduced as compiling clean before this fix.
  len(getEnv("HOME"))

proc innerSeedForOuter(): int =
  len(getEnv("HOME"))

proc outerSeed(): int =
  ## Two hops below the capture: `outerSeed` (hop 1) calls `innerSeed`
  ## (hop 2), which is the one that actually reaches `getEnv`.
  innerSeedForOuter()

proc selfRecursiveHelper(n: int): int =
  ## Pure (no denylisted call anywhere in its call graph) but calls itself —
  ## proves the traversal's cycle guard (`visited`) terminates rather than
  ## hanging the compiler, and that a legitimately-recursive pure helper is
  ## still accepted.
  if n <= 0: 0 else: n + selfRecursiveHelper(n - 1)

proc mutuallyRecursiveA(n: int): int
proc mutuallyRecursiveB(n: int): int = (if n <= 0: 0 else: mutuallyRecursiveA(n - 1))
proc mutuallyRecursiveA(n: int): int = (if n <= 0: 0 else: mutuallyRecursiveB(n - 1))

proc pureDoubler(n: int): int =
  ## Ordinary pure module-scope helper — must never be flagged.
  n * 2

const seedConst = 42

proc cAbs(x: cint): cint {.importc: "abs", header: "<stdlib.h>".}
  ## No accessible Nim body (`getImpl` yields an empty body) — the
  ## "unavailable body" case `checkCallee` must silently allow, not flag.

suite "fuzz: R8 — impurity check follows named-proc calls into their bodies":
  test "impurity one named-proc hop away fails to compile, naming the denylisted call":
    check not compiles(fuzz(integers(0, seedFromEnv()), branchyProp,
                             FuzzSettings(maxIterations: 5, seed: 1)))

  test "impurity two named-proc hops away also fails to compile":
    check not compiles(fuzz(integers(0, outerSeed()), branchyProp,
                             FuzzSettings(maxIterations: 5, seed: 1)))

  test "a self-recursive pure helper in the capture compiles without hanging (cycle safety)":
    check compiles(fuzz(integers(0, selfRecursiveHelper(3)), branchyProp,
                         FuzzSettings(maxIterations: 5, seed: 1)))

  test "a mutually-recursive pair of pure helpers in the capture compiles without hanging (cycle safety)":
    check compiles(fuzz(integers(0, mutuallyRecursiveA(3)), branchyProp,
                         FuzzSettings(maxIterations: 5, seed: 1)))

  test "a module-scope pure helper call in the capture still compiles (no false positive)":
    check compiles(fuzz(integers(0, pureDoubler(5)), branchyProp,
                         FuzzSettings(maxIterations: 5, seed: 1)))

  test "a const initializer still compiles (no false positive)":
    check compiles(fuzz(integers(0, seedConst), branchyProp,
                         FuzzSettings(maxIterations: 5, seed: 1)))

  test "a call to a proc with no accessible Nim body (FFI/importc) still compiles (no false positive)":
    check compiles(fuzz(integers(0, cAbs(5).int), branchyProp,
                         FuzzSettings(maxIterations: 5, seed: 1)))
