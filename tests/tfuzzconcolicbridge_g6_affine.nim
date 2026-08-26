## RFC-fuzzer-nextgen G6 C3 — the HEADLINE: the real concolic bridge, wired
## through the `fuzz(...)` macro, breaks a gate THROUGH an affine `.map()`.
##
## `tfuzzconcolicbridge_real.nim` (G3 C4) already proved the bridge reaches
## a gate on a DIRECT draw (`integers(0, 0xFFFFFFFF)`, no combinator). This
## is the case G6 exists for: `integers(0, 1000).map(x => x*2 + 1)` — under
## the PRE-G6 minimal classifier (`cbDrawLinked` positional, ignoring the
## `.map()` entirely) Z3 would solve for the WRONG equation (`draw == 501`,
## never satisfiable within the drawn value's own path — the property sees
## `mapped`, not `draw`), so concolic could never break the gate: it always
## fell back to concretizing on this shape. G6's AST classifier recognizes
## the affine body, composes `identity ∘ affine(2,1)`, and the macro flattens
## that straight into a `cbTransformLinked` binding — Z3 solves the INVERSE
## (`draw = (501-1)/2 = 250`) and the gate breaks.
##
## Deliberately just `import nelli` (mirrors `tfuzzconcolicbridge_real.nim`).
import std/unittest
import nelli

proc mappedGate(mapped: int) {.cover.} =
  if mapped == 501:
    discard "gate"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G6 — real concolic bridge breaks a gate THROUGH an affine map":

  test "stalled campaign with the real bridge wired breaks the mapped==501 gate through .map(x*2+1)":
    let report = fuzz(integers(0, 1000).map(proc(x: int): int = x * 2 + 1), mappedGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60, stallRounds: 1))
    check report.coverageHits == 2   # BOTH edges — including the mapped-gate edge

  test "the identical campaign with stallRounds left at 0 (the default) never reaches the gate":
    let report = fuzz(integers(0, 1000).map(proc(x: int): int = x * 2 + 1), mappedGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.coverageHits == 1   # only the ordinary (miss) edge
