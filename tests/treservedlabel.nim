import std/[unittest, times, strutils]
import nelli
import zerofill  # RFC-0010 A1 pin; removed by A3

# #107 — the engine reserves the `__` label prefix for its own
# scores (`__coverage__` is the first; future engine-internal
# objectives may follow). User `target()` calls with a `__`-prefixed
# label must raise — otherwise a user could silently overwrite an
# engine-injected score and corrupt the Pareto front.

suite "target() reserved-label namespace":
  test "target() with __-prefixed label raises ValueError":
    proc prop(x: int) =
      target(float(x), "__custom__")
      ensure true
    let r = forAll(integers(0, 10), prop,
                   zeroFilled(Settings(maxExamples: 1, maxRejections: 100,
                                       seed: 1, flakyRetries: 1, maxShrinks: 10,
                                       useSA: false, targetedSAIters: 0,
                                       deadline: initDuration(seconds = 1))))
    # The user's `target()` call inside the property raises ValueError;
    # the engine treats it as a falsification with that exception name.
    check r.outcome == otFalsified
    check "ValueError" in r.message
    check "__" in r.message

  test "ordinary labels and empty label are still accepted":
    proc prop(x: int) =
      target(float(x), "score")
      target(float(x), "")     # default unlabeled objective still works
      ensure true
    let r = forAll(integers(0, 10), prop,
                   zeroFilled(Settings(maxExamples: 3, maxRejections: 100,
                                       seed: 1, flakyRetries: 1, maxShrinks: 10,
                                       useSA: false, targetedSAIters: 0,
                                       deadline: initDuration(seconds = 1))))
    check r.outcome == otPassed
