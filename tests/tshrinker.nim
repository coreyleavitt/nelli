import std/unittest
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "shrinker: lexicographic lowering":
  test "shrinker minimizes a failing integer toward shrinkTowards":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check r.outcome == otFalsified
    check r.counterexample.get == 50  # the minimum value that still fails

  test "shrinker minimizes a failing negative integer toward shrinkTowards":
    # shrinkTowards defaults to 0; a falsifying x = -47 should shrink to
    # x = -1 (the value closest to 0 that still violates `x >= 0`).
    let r = forAll(integers(-100, 100), proc(x: int) = ensure x >= 0)
    check r.outcome == otFalsified
    check r.counterexample.get == -1

  test "shrinker minimizes from low(int) toward 0 without int64 distance overflow":
    # `failSide - passSide` (or its reverse) overflows int64 when
    # `passSide = 0, failSide = low(int64)`. Hand-craft the starting node so
    # the shrinker enters that path: cur = low(int64), target = 0.
    let strat = newStrategy(proc(src: var DataSource): int =
      toInt64(src.drawInteger(toInt128(low(int64)),
                              toInt128(high(int64)),
                              toInt128(0))).int)
    proc prop(x: int) = ensure x > -1_000_000_000
    let initial = @[integerChoice(low(int64),
                                  low(int64), high(int64), 0)]
    let shrunk = shrink(strat, prop, initial)
    # Pre-fix: bisect exits with zero iterations; example stays at low(int).
    # Post-fix: bisect converges and the shrunk example is at or just below
    # the boundary.
    check shrunk.example.get <= -1_000_000_000
    check shrunk.example.get > low(int) div 2

  test "shrinker leaves a passing run alone":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check r.outcome == otPassed

suite "shrinker: deletion (lists)":
  test "shrinker minimizes a failing list to the smallest counterexample":
    let r = forAll(lists(integers(0, 9), maxLen = 20),
                   proc(xs: seq[int]) = ensure xs.len < 3)
    check r.outcome == otFalsified
    check r.counterexample.get == @[0, 0, 0]  # min length × min elements

suite "shrinker: float bounds invariant":
  test "shrinker keeps stored floatVal within floatC.min/max when shrinking to the floor":
    # Property fails at *every* value in `[1.0, 10.0]` (min is itself
    # falsifying). The shrinker used to write `floatVal = 0.0` into the
    # choice node — outside the [1.0, 10.0] constraint — relying on replay's
    # `coerceFloat` to clamp it back to 1.0. That makes `repro()` lie and
    # violates the IR's per-node invariant. Stored value must be in range.
    proc prop(x: float) = (ensure false)
    let r = forAll(floats(1.0, 10.0, allowNan = false), prop)
    check r.outcome == otFalsified
    check r.counterexample.get == 1.0  # shrunk to the floor
    for n in r.choices:
      if n.kind == ckFloat:
        check n.floatVal >= n.floatC.min
        check n.floatVal <= n.floatC.max

suite "shrinker: lowerFloatAt honors smallestNonzeroMagnitude":
  test "stored value satisfies permits even when interpolation lands in the forbidden window":
    # Strategy with `smallestNonzeroMagnitude = 2.0`: nonzero values with
    # `|v| < 2.0` are not admissible. lowerFloatAt interpolating between
    # floor=0.0 and cur=5.0 will visit mid=2.5, 1.25, ... — 1.25 violates
    # the constraint. The shrunk node's stored value must satisfy permits.
    let strat = newStrategy(proc(src: var DataSource): float =
      src.drawFloat(1.0, 10.0, false, 3.0))
    proc prop(x: float) = (ensure false)
    let initial = @[floatChoice(5.0, 1.0, 10.0,
                                allowNan = false,
                                smallestNonzeroMagnitude = 3.0)]
    let shrunk = shrink(strat, prop, initial)
    for n in shrunk.choices:
      if n.kind == ckFloat:
        check n.floatC.permits(n.floatVal)

suite "shrinker: float values":
  test "float shrink minimizes a failing float toward the boundary":
    proc prop(x: float) = ensure x < 50.0
    let r = forAll(floats(-1e9, 1e9, allowNan = false), prop)
    check r.outcome == otFalsified
    # Float shrinks from above toward 0; smallest value still falsifying is 50.0.
    check r.counterexample.get >= 50.0
    check r.counterexample.get <= 50.0001

suite "shrinker: bool / bytes / string values":
  test "shrink lowers an unforced true bool to false when still falsifying":
    proc prop(t: (bool, int)) = (ensure false)
    let strat = map(booleans(), integers(0, 10))
    # Hand-crafted starting sequence: bool=true, int=5 — both above the
    # zero/false target, so a working shrinker must reduce them.
    let initial = @[booleanChoice(true, 0.5),
                    integerChoice(5, 0, 10, 0)]
    let shrunk = shrink(strat, prop, initial)
    check shrunk.example.get[0] == false
    check shrunk.example.get[1] == 0

  test "shrink reduces a bytes value toward empty (the zero form)":
    let bytesS = newStrategy(proc(src: var DataSource): seq[byte] =
      src.drawBytes(0, 16))
    proc prop(b: seq[byte]) = (ensure false)
    let initial = @[bytesChoice(@[5'u8, 3, 7], minSize = 0, maxSize = 16)]
    let shrunk = shrink(bytesS, prop, initial)
    check shrunk.example.get == newSeq[byte]()

  test "shrink reduces a string value toward empty":
    let iv = intervals([(0x61'i32, 0x7a'i32)])
    let strS = newStrategy(proc(src: var DataSource): string =
      src.drawString(iv, 0, 10))
    proc prop(s: string) = (ensure false)
    let initial = @[stringChoice("hello", iv, minSize = 0, maxSize = 10)]
    let shrunk = shrink(strS, prop, initial)
    check shrunk.example.get == ""

suite "shrinker: string complexity counts codepoints":
  # Iterate over bytes mis-counts multi-byte UTF-8 (each byte adds to both
  # the length and the sum). Two-rune `"éé"` should be strictly simpler than
  # three-rune `"aaa"` even though `"éé".len == 4` (bytes) > `"aaa".len == 3`.
  test "fewer codepoints sorts as simpler regardless of byte width":
    let iv = intervals([(0x20'i32, 0xD7FF'i32),
                        (0xE000'i32, 0x10FFFF'i32)])
    let ee = @[stringChoice("éé", iv, 0, 10)]
    let aaa = @[stringChoice("aaa", iv, 0, 10)]
    check sortKeyLess(ee, aaa)
    check not sortKeyLess(aaa, ee)

suite "shrinker: float complexity uses magnitude":
  # Shortlex over float-bearing sequences must treat `±x` as equally complex
  # (they're equally far from zero) and `0.0` as strictly simpler than any
  # nonzero magnitude. A signed-bit-pattern complexity would invert this.
  test "0.0 is strictly simpler than ±1.0; ±1.0 are tied":
    let zero = @[floatChoice(0.0, -10.0, 10.0, true, 0.0)]
    let posOne = @[floatChoice(1.0, -10.0, 10.0, true, 0.0)]
    let negOne = @[floatChoice(-1.0, -10.0, 10.0, true, 0.0)]
    check sortKeyLess(zero, posOne)
    check sortKeyLess(zero, negOne)
    check not sortKeyLess(posOne, zero)
    check not sortKeyLess(negOne, zero)
    check not sortKeyLess(posOne, negOne)
    check not sortKeyLess(negOne, posOne)

suite "shrinker: shortlex ordering (#34)":
  test "shorter sequences are smaller than longer":
    let a = @[integerChoice(0, 0, 100, 0)]
    let b = @[integerChoice(0, 0, 100, 0), booleanChoice(false, 0.5)]
    check sortKeyLess(a, b)
    check not sortKeyLess(b, a)

  test "equal-length sequences use lex order by per-node complexity":
    let a = @[integerChoice(1, 0, 100, 0)]
    let b = @[integerChoice(5, 0, 100, 0)]
    check sortKeyLess(a, b)
    check not sortKeyLess(b, a)
    check not sortKeyLess(a, a)  # not strict for equal
