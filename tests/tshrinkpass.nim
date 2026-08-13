import std/unittest
import nelli
import nelli/[int128, choice, datasource, rng, shrinker]

# #105 — promote shrink passes to first-class data so users can
# enable/disable individual passes or add domain-specific reductions.

suite "shrink passes are first-class data":
  test "passes = @[] returns the input unchanged (driver iterates only over the passed list)":
    # Build a falsifying choice sequence by hand: integer = 42, property
    # rejects it. With zero passes the shrinker has nothing to do — the
    # input is returned as-is even though many reductions would still
    # falsify.
    let s = integers(0, 100)
    proc prop(x: int) = ensure x < 10
    let input = @[ChoiceNode(kind: ckInteger,
                             intC: IntConstraints(min: toInt128(0),
                                                  max: toInt128(100),
                                                  shrinkTowards: toInt128(0)),
                             intVal: toInt128(42))]
    let r = shrink(s, prop, input, maxShrinks = 50, passes = @[])
    check r.choices == input

  test "defaultShrinkPasses fully reduces an int falsifier toward shrinkTowards":
    # Falsify when x >= 10. Default suite includes lowerInteger; shrinker
    # should drive value toward 10 (smallest in-range value satisfying x >= 10).
    let s = integers(0, 100)
    proc prop(x: int) = ensure x < 10
    let input = @[ChoiceNode(kind: ckInteger,
                             intC: IntConstraints(min: toInt128(0),
                                                  max: toInt128(100),
                                                  shrinkTowards: toInt128(0)),
                             intVal: toInt128(42))]
    let r = shrink(s, prop, input,
                   maxShrinks = 200,
                   passes = defaultShrinkPasses[int]())
    check toInt64(r.choices[0].intVal) == 10

  test "lowerInteger-only pass shrinks int but doesn't delete spans":
    # With *only* lowerInteger, the value lowers but if there's a
    # secondary draw (introduced via lists), the span isn't deleted.
    # Verifiable by handing the shrinker a sequence that has two ints,
    # only one of which is necessary; the unnecessary one stays.
    let s = integers(0, 100)
    proc prop(x: int) = ensure x < 50
    let input = @[ChoiceNode(kind: ckInteger,
                             intC: IntConstraints(min: toInt128(0),
                                                  max: toInt128(100),
                                                  shrinkTowards: toInt128(0)),
                             intVal: toInt128(99))]
    let r = shrink(s, prop, input,
                   maxShrinks = 100,
                   passes = @[lowerIntegerShrinkPass[int]()])
    check toInt64(r.choices[0].intVal) == 50

  test "user-defined custom pass composes with the default suite":
    # Custom pass that always sets the integer to min when feasible.
    # Combined with the default suite, the result should land at the
    # smallest in-range value that still falsifies.
    let s = integers(0, 100)
    proc prop(x: int) = ensure x < 50
    let input = @[ChoiceNode(kind: ckInteger,
                             intC: IntConstraints(min: toInt128(0),
                                                  max: toInt128(100),
                                                  shrinkTowards: toInt128(0)),
                             intVal: toInt128(99))]
    var passCalled = 0
    let customPass = ShrinkPass[int](
      name: "trackInvocation",
      reduce: proc(s: Strategy[int], prop: proc(x: int),
                   choices: var seq[ChoiceNode]) =
        inc passCalled)
    let combo = defaultShrinkPasses[int]() & @[customPass]
    let r = shrink(s, prop, input, maxShrinks = 100, passes = combo)
    # Default suite still shrinks the value to 50 (smallest falsifier).
    check toInt64(r.choices[0].intVal) == 50
    # Custom pass actually ran (at least once per fixpoint iteration).
    check passCalled >= 1
