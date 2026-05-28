import std/unittest
import std/[math, sets]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "ChoiceNode: integer":
  test "constructing an integer choice exposes its kind, value, and constraints":
    let n = integerChoice(value = 42, min = 0, max = 100, shrinkTowards = 0)
    check n.kind == ckInteger
    check n.intVal == toInt128(42)
    check n.intC.min == toInt128(0)
    check n.intC.max == toInt128(100)
    check n.intC.shrinkTowards == toInt128(0)
    check not n.wasForced

suite "IntConstraints: permits":
  test "permits values within [min,max] and rejects those outside":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100),
                           shrinkTowards: toInt128(0))
    check c.permits(toInt128(0))     # lower bound inclusive
    check c.permits(toInt128(100))   # upper bound inclusive
    check c.permits(toInt128(42))
    check not c.permits(toInt128(-1))
    check not c.permits(toInt128(101))

  test "constructor clamps shrinkTowards into [min,max]":
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = -100).intC.shrinkTowards == toInt128(0)
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = 100).intC.shrinkTowards == toInt128(10)
    check integerChoice(value = 5, min = 0, max = 10,
                        shrinkTowards = 3).intC.shrinkTowards == toInt128(3)

suite "ChoiceInt: full integer-type coverage":
  test "represents and orders the full uint64 range int64 cannot hold":
    let maxU = toInt128(high(uint64))
    let aboveI64 = toInt128(uint64(high(int64)) + 1'u64)  # 2^63, beyond int64
    check toInt128(high(int64)) < aboveI64                # ordering across boundary
    check aboveI64 < maxU
    let c = IntConstraints(min: toInt128(0'u64), max: maxU,
                           shrinkTowards: toInt128(0))
    check c.permits(maxU)
    check c.permits(aboveI64)
    check not c.permits(toInt128(-1))

suite "BoolConstraints: permits":
  test "boundary guarantee: p=0 only false, p=1 only true, otherwise both":
    check BoolConstraints(p: 0.0).permits(false)
    check not BoolConstraints(p: 0.0).permits(true)
    check BoolConstraints(p: 1.0).permits(true)
    check not BoolConstraints(p: 1.0).permits(false)
    check BoolConstraints(p: 0.5).permits(true)
    check BoolConstraints(p: 0.5).permits(false)

suite "FloatConstraints: permits":
  test "respects range, NaN policy, and smallest-nonzero-magnitude":
    let c = FloatConstraints(min: -1e9, max: 1e9, allowNan: false,
                             smallestNonzeroMagnitude: 1e-6)
    check c.permits(0.0)
    check c.permits(-0.0)            # signed zero is always legal
    check c.permits(3.14)
    check not c.permits(1e-9)        # nonzero but below smallest magnitude
    check not c.permits(2e9)         # above max
    check not c.permits(NaN)         # NaN disallowed here
    let withNan = FloatConstraints(min: -1e9, max: 1e9, allowNan: true,
                                   smallestNonzeroMagnitude: 1e-6)
    check withNan.permits(NaN)

suite "BytesConstraints: permits":
  test "respects byte-length bounds":
    let c = BytesConstraints(minSize: 2, maxSize: 4)
    check c.permits(@[1'u8, 2])
    check c.permits(@[1'u8, 2, 3, 4])
    check not c.permits(@[1'u8])
    check not c.permits(@[1'u8, 2, 3, 4, 5])

suite "StringConstraints: permits":
  test "respects codepoint-length bounds and allowed codepoint intervals":
    let lower = intervals([(0x61'i32, 0x7a'i32)])  # 'a'..'z'
    let c = StringConstraints(intervals: lower, minSize: 1, maxSize: 5)
    check c.permits("abc")
    check not c.permits("")        # 0 codepoints, below minSize
    check not c.permits("abcdef")  # 6 codepoints, above maxSize
    check not c.permits("aZc")     # 'Z' outside the allowed interval

suite "intervals() input validation":
  test "rejects inverted ranges (lo > hi)":
    # An inverted range underflows `hi - lo + 1` in the uniform-pick path of
    # `drawCodepoint`, silently producing wildly-wrong codepoints. Catch it
    # at construction.
    expect ValueError:
      discard intervals([(0x7a'i32, 0x61'i32)])  # 'z'..'a'
    discard intervals([(0x61'i32, 0x7a'i32)])    # valid

suite "ChoiceNode constructors validate value against constraints":
  # The IR invariant — `node.value` satisfies `node.constraints` — is what
  # makes `repro()` honest and the engine's replay defensible. Constructors
  # are the first line of defense.
  test "integerChoice rejects an out-of-range value":
    expect ValueError:
      discard integerChoice(value = 200, min = 0, max = 100, shrinkTowards = 0)
    expect ValueError:
      discard integerChoice(value = -5, min = 0, max = 100, shrinkTowards = 0)
    # in-range still works
    discard integerChoice(value = 42, min = 0, max = 100, shrinkTowards = 0)

  test "floatChoice rejects NaN when not allowed and out-of-range values":
    expect ValueError:
      discard floatChoice(value = NaN, min = -1.0, max = 1.0,
                          allowNan = false, smallestNonzeroMagnitude = 0.0)
    expect ValueError:
      discard floatChoice(value = 5.0, min = -1.0, max = 1.0,
                          allowNan = false, smallestNonzeroMagnitude = 0.0)
    # legal cases
    discard floatChoice(value = 0.5, min = -1.0, max = 1.0,
                        allowNan = false, smallestNonzeroMagnitude = 0.0)
    discard floatChoice(value = NaN, min = -1.0, max = 1.0,
                        allowNan = true, smallestNonzeroMagnitude = 0.0)

  test "bytesChoice rejects length outside [minSize, maxSize]":
    expect ValueError:
      discard bytesChoice(@[1'u8], minSize = 2, maxSize = 4)
    expect ValueError:
      discard bytesChoice(@[1'u8, 2, 3, 4, 5], minSize = 0, maxSize = 4)
    discard bytesChoice(@[1'u8, 2, 3], minSize = 0, maxSize = 4)

  test "stringChoice rejects out-of-interval codepoints and bad lengths":
    let lower = intervals([(0x61'i32, 0x7a'i32)])  # 'a'..'z'
    expect ValueError:
      discard stringChoice("aZc", lower, minSize = 0, maxSize = 5)
    expect ValueError:
      discard stringChoice("abcdef", lower, minSize = 0, maxSize = 5)
    discard stringChoice("abc", lower, minSize = 0, maxSize = 5)

suite "ChoiceNode: equality":
  test "integer nodes compare by value, constraints, and forced flag":
    let a = integerChoice(value = 5, min = 0, max = 10, shrinkTowards = 0)
    check a == integerChoice(value = 5, min = 0, max = 10, shrinkTowards = 0)
    check a != integerChoice(value = 6, min = 0, max = 10, shrinkTowards = 0)
    check a != integerChoice(value = 5, min = 0, max = 20, shrinkTowards = 0)
    check a != integerChoice(value = 5, min = 0, max = 10, shrinkTowards = 0,
                             forced = true)

  test "float nodes compare bitwise: NaN equals NaN, +0 differs from -0":
    proc f(v: float64): ChoiceNode =
      floatChoice(value = v, min = -1e9, max = 1e9, allowNan = true,
                  smallestNonzeroMagnitude = 1e-300)
    check f(1.5) == f(1.5)
    check f(NaN) == f(NaN)     # same bits → equal (semantic == would say false)
    check f(0.0) != f(-0.0)    # distinct bit patterns → not equal

  test "boolean, bytes, and string nodes compare by value and constraints":
    check booleanChoice(true, p = 0.5) == booleanChoice(true, p = 0.5)
    check booleanChoice(true, p = 0.5) != booleanChoice(false, p = 0.5)
    check booleanChoice(true, p = 0.5) != booleanChoice(true, p = 0.25)

    check bytesChoice(@[1'u8, 2], minSize = 0, maxSize = 8) ==
          bytesChoice(@[1'u8, 2], minSize = 0, maxSize = 8)
    check bytesChoice(@[1'u8, 2], minSize = 0, maxSize = 8) !=
          bytesChoice(@[1'u8, 3], minSize = 0, maxSize = 8)

    let iv = intervals([(0x61'i32, 0x7a'i32)])
    check stringChoice("ab", iv, minSize = 0, maxSize = 8) ==
          stringChoice("ab", iv, minSize = 0, maxSize = 8)
    check stringChoice("ab", iv, minSize = 0, maxSize = 8) !=
          stringChoice("ac", iv, minSize = 0, maxSize = 8)

suite "ChoiceNode: hash":
  test "hash is consistent with equality and usable for dedup":
    # equal nodes hash equal — including bitwise-equal NaN floats
    check hash(integerChoice(5, 0, 10, 0)) == hash(integerChoice(5, 0, 10, 0))
    check hash(floatChoice(NaN, -1e9, 1e9, true, 1e-300)) ==
          hash(floatChoice(NaN, -1e9, 1e9, true, 1e-300))
    # works as a set element (the dedup case the novelty tree needs)
    var seen = initHashSet[ChoiceNode]()
    seen.incl integerChoice(5, 0, 10, 0)
    check integerChoice(5, 0, 10, 0) in seen     # equal draw recognised
    check integerChoice(6, 0, 10, 0) notin seen  # different draw not recognised
