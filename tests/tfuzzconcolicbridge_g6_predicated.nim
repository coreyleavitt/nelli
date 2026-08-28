## RFC-fuzzer-nextgen G6 C4 — a 2-combinator chain (filter THEN map) through
## the real `fuzz(...)` macro: `integers(0,1000).filter(x => x > 500)
## .map(x => x + 1)`. Composes to `predicated(affine(1,1), [x > 500])` —
## proves (a) `filter`'s predicate classifies correctly even though Nim's
## typed AST rewrites `x > 500` to `500 < x` (`predicateOf`'s operand-order
## handling), (b) the chain composition (`compose(predicated, affine)`)
## carries the conjunct through a SUBSEQUENT map, matching G6 C1's pure-
## algebra proof end to end through the real bridge.
##
## RFC-z3-optional: the assist is opt-in, so this file now carries the extra
## `import nelli/concolic` and drives the campaign through `fuzzConcolic`.
import std/[unittest, tables]
import nelli
import nelli/concolic

proc chainedGate(mapped: int) {.cover.} =
  if mapped == 601:   # x + 1 == 601 => x == 600, which satisfies x > 500
    discard "gate"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G6 — real concolic bridge through a filter-then-map chain":

  test "stalled campaign breaks the mapped==601 gate through filter(x>500).map(x+1)":
    let report = fuzzConcolic(
      integers(0, 1000).filter(proc(x: int): bool = x > 500).map(proc(x: int): int = x + 1),
      chainedGate,
      FuzzSettings(seed: 7'u64, maxIterations: 60))
    check report.coverageHits == 2
    # RFC-z3-optional: `coverageHits == 2` alone does not say the SOLVER got
    # there. These two do, and they are the same discriminating pair
    # `tfuzzconcolicbridge_real.nim` uses.
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic > 0
    check report.stats.provenanceCounts[pvConcolic] > 0

  test "the identical campaign with no assist (plain fuzz) never reaches the gate":
    let report = fuzz(
      integers(0, 1000).filter(proc(x: int): bool = x > 500).map(proc(x: int): int = x + 1),
      chainedGate,
      FuzzSettings(seed: 7'u64, maxIterations: 60))
    check report.coverageHits == 1
    check report.stats.provenanceCounts[pvConcolic] == 0
