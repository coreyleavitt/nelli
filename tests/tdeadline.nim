import std/[unittest, times, hashes, os, strutils]
import nelli

suite "Settings.derandomize":
  test "derandomize=true derives the seed from testId, ignoring `seed`":
    # Hermetic CI mode: a single global `seed` is fragile (one collision
    # affects everyone); deriving from `testId` makes every test
    # independently reproducible, while still bit-for-bit deterministic
    # across hosts.
    let s = integers(0, 1_000_000)
    let r1 = forAll(s, proc(x: int) = (ensure true),
                    Settings(maxExamples: 50,
                             testId: "derandomize-test-A",
                             derandomize: true,
                             seed: 1, flakyRetries: 0,
                             maxShrinks: 50, maxRejections: 100))
    let r2 = forAll(s, proc(x: int) = (ensure true),
                    Settings(maxExamples: 50,
                             testId: "derandomize-test-A",
                             derandomize: true,
                             seed: 99999,   # different `seed`, same testId
                             flakyRetries: 0,
                             maxShrinks: 50, maxRejections: 100))
    check r1.seed == r2.seed     # same testId → same effective seed
    check r1.seed == cast[uint64](hash("derandomize-test-A"))

    let r3 = forAll(s, proc(x: int) = (ensure true),
                    Settings(maxExamples: 50,
                             testId: "derandomize-test-B",  # different testId
                             derandomize: true,
                             seed: 1, flakyRetries: 0,
                             maxShrinks: 50, maxRejections: 100))
    check r3.seed != r1.seed     # different testId → different seed

  test "derandomize=true with empty testId raises ValueError (loud > silent)":
    expect ValueError:
      discard forAll(integers(0, 100),
                     proc(x: int) = (ensure true),
                     Settings(maxExamples: 5,
                              derandomize: true,    # but no testId
                              flakyRetries: 0,
                              maxShrinks: 10, maxRejections: 10))

suite "Settings.deadline":
  test "a property invocation that exceeds the deadline falsifies":
    # Sleep longer than the deadline → DeadlineExceeded fires inside the
    # engine's timed call → counted as a falsification, like any other
    # property violation. The user's property body is *not* interrupted
    # (we don't preempt threads); we check after each invocation returns.
    proc slowProp(x: int) =
      sleep(40)            # ms; deadline is 5ms
      ensure true
    let r = forAll(integers(0, 5), slowProp,
                   Settings(maxExamples: 5,
                            deadline: initDuration(milliseconds = 5),
                            flakyRetries: 0,
                            maxShrinks: 20, maxRejections: 10,
                            seed: 1))
    check r.outcome == otFalsified
    check "deadline" in r.message.toLowerAscii

  test "deadline-exceeding input gets shrunk":
    # Sleep proportional to list length: any list with >= 1 element will
    # take ~30ms, well past the 5ms deadline. The shrinker should pull
    # the falsifying example down to the shortest deadline-violating
    # list — len == 1.
    proc slow(xs: seq[int]) =
      sleep(30 * xs.len)
      ensure true
    let r = forAll(lists(integers(0, 9), maxLen = 8),
                   slow,
                   Settings(maxExamples: 5,
                            deadline: initDuration(milliseconds = 5),
                            flakyRetries: 0,
                            maxShrinks: 50, maxRejections: 10,
                            seed: 7))
    check r.outcome == otFalsified
    # Shrinker minimizes magnitude; minimal slow input has len 1.
    check r.counterexample.get.len == 1
