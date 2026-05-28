import std/[unittest, algorithm, sequtils]
import proptest

# Metamorphic testing: when there's no obvious oracle for a function's
# output, *relations* between outputs under input transformations
# often are easy to state. Classic examples: sort(reverse(xs)) ==
# sort(xs); compile(rename(ast)) ≅ compile(ast); f(perturb(x)) ≈ f(x).
#
# `metamorphic(s, prop, transform, relation)` formalizes the pattern:
# for each generated x, check that relation(prop(x), prop(transform(x)))
# holds.

suite "metamorphic":
  test "relation that always holds → otPassed":
    # Trivial: identity transform, equality relation. The property
    # value is unchanged because the input is unchanged.
    let r = metamorphic(
      integers(0, 100),
      proc(x: int): int = x * 2,
      proc(x: int): int = x,                # identity transform
      proc(a, b: int): bool = a == b,
      Settings(maxExamples: 50, seed: 1,
               flakyRetries: 0, maxShrinks: 50,
               maxRejections: 100))
    check r.outcome == otPassed

  test "real example: sort(reverse(xs)) == sort(xs)":
    proc sortProp(xs: seq[int]): seq[int] =
      result = xs
      result.sort()
    proc reverseTransform(xs: seq[int]): seq[int] =
      result = xs
      result.reverse()
    let r = metamorphic(
      lists(integers(0, 9), maxLen = 8),
      sortProp,
      reverseTransform,
      proc(a, b: seq[int]): bool = a == b,
      Settings(maxExamples: 100, seed: 1,
               flakyRetries: 0, maxShrinks: 50,
               maxRejections: 100))
    check r.outcome == otPassed

  test "broken metamorphic relation falsifies with a counterexample":
    # `sum` is NOT invariant under "append the input to itself" — the
    # transformed sum is exactly 2× the original. Use the wrong
    # relation (equality) and expect falsification.
    proc sumProp(xs: seq[int]): int =
      for x in xs: result += x
    proc doubleTransform(xs: seq[int]): seq[int] = xs & xs
    let r = metamorphic(
      lists(integers(1, 10), minLen = 1, maxLen = 5),
      sumProp,
      doubleTransform,
      proc(a, b: int): bool = a == b,    # broken relation
      Settings(maxExamples: 100, seed: 1,
               flakyRetries: 0, maxShrinks: 50,
               maxRejections: 100))
    check r.outcome == otFalsified
    check r.counterexample.isSome

suite "unchangedUnder (eq specialization)":
  test "sort is unchanged under reverse":
    proc sortProp(xs: seq[int]): seq[int] =
      result = xs
      result.sort()
    proc reverseTransform(xs: seq[int]): seq[int] =
      result = xs
      result.reverse()
    let r = unchangedUnder(
      lists(integers(0, 9), maxLen = 8),
      sortProp,
      reverseTransform,
      Settings(maxExamples: 50, seed: 2,
               flakyRetries: 0, maxShrinks: 30, maxRejections: 100))
    check r.outcome == otPassed

suite "metamorphics (fan-out form)":
  test "fan-out over multiple transforms all check":
    # sort is invariant under reverse AND under rotation by k.
    proc sortProp(xs: seq[int]): seq[int] =
      result = xs
      result.sort()
    let revT: proc(xs: seq[int]): seq[int] {.closure.} =
      proc(xs: seq[int]): seq[int] =
        result = xs
        result.reverse()
    let rot1T: proc(xs: seq[int]): seq[int] {.closure.} =
      proc(xs: seq[int]): seq[int] =
        if xs.len == 0: return @[]
        result = xs[1 .. ^1] & @[xs[0]]
    let r = metamorphics(
      lists(integers(0, 9), maxLen = 6),
      sortProp,
      @[revT, rot1T],
      proc(a, b: seq[int]): bool = a == b,
      Settings(maxExamples: 50, seed: 3,
               flakyRetries: 0, maxShrinks: 30, maxRejections: 100))
    check r.outcome == otPassed

  test "if ANY transform breaks the relation, metamorphics falsifies":
    proc sortProp(xs: seq[int]): seq[int] =
      result = xs
      result.sort()
    let revT: proc(xs: seq[int]): seq[int] {.closure.} =
      proc(xs: seq[int]): seq[int] =
        result = xs
        result.reverse()
    let badT: proc(xs: seq[int]): seq[int] {.closure.} =
      proc(xs: seq[int]): seq[int] = xs & @[999]
    let r = metamorphics(
      lists(integers(0, 9), minLen = 1, maxLen = 4),
      sortProp,
      @[revT, badT],
      proc(a, b: seq[int]): bool = a == b,
      Settings(maxExamples: 30, seed: 4,
               flakyRetries: 0, maxShrinks: 30, maxRejections: 100))
    check r.outcome == otFalsified
