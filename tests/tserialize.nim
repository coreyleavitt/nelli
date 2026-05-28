import std/unittest
import std/[math, strutils]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker, db]

suite "choice sequence serialization":
  test "round-trips a single integer node":
    let s = @[integerChoice(42, 0, 100, 0)]
    check fromBytes(toBytes(s)) == s

  test "round-trips an empty sequence":
    var s: seq[ChoiceNode] = @[]
    check fromBytes(toBytes(s)) == s
    check toBytes(s).len == 8  # just the 8-byte count header

  test "round-trips a mixed sequence of all five kinds losslessly":
    let iv = intervals([(0x20'i32, 0xFFFF'i32)])  # wide enough for "naïve"
    let s = @[
      integerChoice(uint64(high(int64)) + 5'u64, 0'u64, high(uint64), 0'u64),
      floatChoice(NaN, -1e9, 1e9, allowNan = true, smallestNonzeroMagnitude = 1e-300),
      floatChoice(-0.0, -1e9, 1e9, allowNan = false,
                  smallestNonzeroMagnitude = 1e-300, forced = true),
      booleanChoice(true, p = 0.25),
      bytesChoice(@[0'u8, 255, 7], minSize = 1, maxSize = 16),
      stringChoice("naïve", iv, minSize = 0, maxSize = 32),  # multi-byte utf8
    ]
    check fromBytes(toBytes(s)) == s

suite "choice sequence corruption handling":
  test "fromBytes on a malformed buffer raises DbCorrupt, not IndexDefect":
    # Hand-craft a buffer that claims `nNodes = 5` but ends after just one
    # node; the second-node read must fail with a clean DbCorrupt rather
    # than an opaque IndexDefect.
    let good = toBytes(@[integerChoice(1, 0, 10, 0)])
    var bad: seq[byte]
    # Replace the leading u64 length with `5` to claim more nodes than exist.
    for i in 0 ..< 8: bad.add 0'u8
    bad[0] = 5'u8
    # Append just one valid node's worth of bytes from `good` (skip its
    # length prefix).
    for i in 8 ..< good.len: bad.add good[i]
    expect DbCorrupt:
      discard fromBytes(bad)

suite "choice sequence rendering":
  test "renders nodes in a readable form":
    check $integerChoice(42, 0, 100, 0) == "int(42)"
    check $integerChoice(-5, -10, 0, 0) == "int(-5)"
    check $booleanChoice(true, p = 0.5, forced = true) == "bool!(true)"
    check "1.5" in $floatChoice(1.5, -1e9, 1e9, true, 1e-300)
    check "ab" in $stringChoice("ab", intervals([(0x61'i32, 0x7a'i32)]), 0, 8)
