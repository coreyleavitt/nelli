import std/unittest
import nelli
import nelli/[int128, choice, serialize, rng, datasource, shrinker]

suite "SplitMix64":
  test "the same seed produces the same sequence":
    var a = initSplitMix64(12345)
    var b = initSplitMix64(12345)
    for _ in 0 ..< 5:
      check a.next == b.next

  test "a value copy is an independent, identical stream":
    var a = initSplitMix64(7)
    var b = a                     # copy
    check a.next == b.next        # copy reproduces the same stream
    discard b.next                # advance only b
    var fresh = initSplitMix64(7)
    discard fresh.next            # align: a and fresh have each consumed one
    check a.next == fresh.next    # a is unaffected by b's advance

  test "different seeds diverge":
    var r1 = initSplitMix64(1)
    var r2 = initSplitMix64(2)
    check r1.next != r2.next
