import std/[unittest, strutils, tables]
import nelli

# A property that itself calls `forAll` (the natural shape of
# metamorphic relations or parametric law tests) must not have its
# note/event/target context clobbered by the inner run. The fix is
# pure: the engine pushes/pops a per-example frame, so the inner's
# state is a separate stack entry.

suite "nested forAll: per-example context stacking":
  test "outer note() survives a nested forAll inside the property":
    # If notes leaked between frames, the outer Report's notes after
    # falsification would be the *inner* run's notes (or empty).
    # Correct behaviour: outer Report carries the outer note() calls;
    # inner Report carries the inner ones.
    proc outerProp(x: int) =
      note("outer-x", x)
      # nested forAll: a trivial passing inner property
      proc innerProp(y: int) =
        note("inner-y", y)
        ensure true
      let innerR = forAll(integers(0, 5), innerProp,
                          Settings(maxExamples: 3, seed: 9,
                                   flakyRetries: 0, maxShrinks: 5,
                                   maxRejections: 10))
      doAssert innerR.outcome == otPassed
      ensure x < 50    # outer fails when x reaches 50
    let r = forAll(integers(0, 100), outerProp,
                   Settings(maxExamples: 200, seed: 1,
                            flakyRetries: 0, maxShrinks: 100,
                            maxRejections: 200))
    check r.outcome == otFalsified
    # Outer note must be present and not contaminated by inner notes.
    var sawOuterX = false
    var sawInnerY = false
    for (label, _) in r.notes:
      if label == "outer-x": sawOuterX = true
      if label == "inner-y": sawInnerY = true
    check sawOuterX
    check not sawInnerY    # inner notes belong to the inner Report only

  test "outer event() accumulates independently of nested forAll":
    var innerObserved = 0
    proc outerProp(x: int) =
      event("outer-tag")
      proc innerProp(y: int) =
        event("inner-tag")
        ensure true
      let ir = forAll(integers(0, 3), innerProp,
                      Settings(maxExamples: 4, seed: 2,
                               flakyRetries: 0, maxShrinks: 5,
                               maxRejections: 10))
      innerObserved = ir.events.categorical.getOrDefault("inner-tag")
      ensure true
    let r = forAll(integers(0, 9), outerProp,
                   Settings(maxExamples: 5, seed: 3,
                            flakyRetries: 0, maxShrinks: 5,
                            maxRejections: 20))
    check r.outcome == otPassed
    # Outer's events: only outer-tag (counted once per outer example).
    check r.events.categorical["outer-tag"] == 5
    check "inner-tag" notin r.events.categorical
    # Inner Report's events: only inner-tag (4 per inner-forAll call).
    check innerObserved == 4

  test "outer target() scores aren't wiped by nested forAll":
    # If the inner forAll cleared the outer frame's scores between
    # examples, the outer Pareto front would be empty even when the
    # outer property called target().
    proc innerProp(y: int) = (ensure true)
    var outerTargetCalls = 0
    proc outerProp(x: int) =
      target(float(x), "outer-score")
      inc outerTargetCalls
      let _ = forAll(integers(0, 2), innerProp,
                     Settings(maxExamples: 2, seed: 1,
                              flakyRetries: 0, maxShrinks: 2,
                              maxRejections: 5))
      ensure true
    let r = forAll(integers(0, 9), outerProp,
                   Settings(maxExamples: 10, seed: 4,
                            flakyRetries: 0, maxShrinks: 5,
                            maxRejections: 20, useSA: false,
                            targetedSAIters: 0))
    check r.outcome == otPassed
    check outerTargetCalls >= 10  # at least one per random-phase example
    # The outer Pareto front must have at least one entry (the random
    # phase populated it from outer-score targets).
    check r.paretoFront.len >= 1
