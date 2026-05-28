import std/[unittest, tables]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "targeted PBT":
  test "target() captures a score and a passing property still passes":
    proc prop(x: int) =
      target(float(x))
      ensure x >= 0
    let r = forAll(integers(0, 100), prop)
    check r.outcome == otPassed

  test "simulated-annealing escape uncovers falsifications greedy misses":
    # Deceptive landscape: a tall local peak at x=0 where greedy + the
    # shrinkTowards-biased random phase get stuck, separated by a wide flat
    # zero-score moat from a narrow global peak at |x| in [1550, 1560].
    # Greedy's ±{1, 10, 100, 1000} delta set can't cross the moat (any single
    # step from the local peak lands in the zero region, which is strictly
    # worse than the local-peak height). SA's heavy-tailed Cauchy proposals
    # can cross. We measure SA's contribution **differentially**: same seed,
    # one run with SA disabled, one with SA enabled — SA-enabled finds
    # falsifications that no-SA does not.
    proc score(x: int): float =
      let a = abs(x)
      if a <= 5: 100.0 - a.float * 5.0
      elif a >= 1550 and a <= 1560: 250.0
      else: 0.0
    proc prop(x: int) =
      target(score(x))
      ensure score(x) < 200.0
    var saExclusive = 0
    for seed in 1'u64 .. 8'u64:
      let noSA = forAll(integers(-2000, 2000), prop,
                        Settings(maxExamples: 30, maxRejections: 1000,
                                 seed: seed, flakyRetries: 0, maxShrinks: 50,
                                 useSA: false))
      let withSA = forAll(integers(-2000, 2000), prop,
                          Settings(maxExamples: 30, maxRejections: 1000,
                                   seed: seed, flakyRetries: 0, maxShrinks: 50,
                                   useSA: true))
      if withSA.outcome == otFalsified and noSA.outcome != otFalsified:
        inc saExclusive
    check saExclusive >= 1

  test "multi-objective target() builds a Pareto front of non-dominated examples":
    # Two conflicting objectives over a 2-d input. There is no single best
    # (x, y): a high "lo" requires small x, while "hi" rewards large x.
    # The engine must surface multiple non-dominated examples — the Pareto
    # front — rather than collapsing to one.
    proc prop(t: (int, int)) =
      target(-float(t[0]), "lo")  # maximize → push x toward 0
      target(float(t[0]),  "hi")  # maximize → push x toward 1000
      ensure true               # never falsifies; only the front matters
    let r = forAll(tuples2(integers(0, 1000), integers(0, 1000)), prop,
                   Settings(maxExamples: 40, maxRejections: 1000, seed: 1,
                            flakyRetries: 0, maxShrinks: 50, useSA: true))
    check r.outcome == otPassed
    check r.paretoFront.len >= 2
    # No member of the front should dominate any other.
    for i, a in r.paretoFront:
      for j, b in r.paretoFront:
        if i != j:
          check not dominates(a.scores, b.scores)
    # Both labels appear in front members' score maps.
    var sawLo, sawHi = false
    for e in r.paretoFront:
      if e.scores.hasKey("lo"): sawLo = true
      if e.scores.hasKey("hi"): sawHi = true
    check sawLo and sawHi

  test "SA over a wide integer range doesn't crash on Cauchy tail samples":
    # Cauchy proposals scaled to a wide range regularly return float values
    # whose magnitude exceeds int64; both the float-to-int conversion
    # (saturates to int64.min in release; raises in some configurations) and
    # the subsequent `baseVal + d` int64 addition can overflow. Doing the
    # candidate arithmetic in float space and clamping to `[lo.float, hi.float]`
    # before casting eliminates both. We exercise the full int64 range to
    # force the issue.
    proc prop(x: int) =
      target(float(x))
      ensure true
    let r = forAll(integers(low(int), high(int)), prop,
                   Settings(maxExamples: 8, maxRejections: 1000, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            useSA: true, targetedSAIters: 400))
    check r.outcome == otPassed

  test "NaN passed to target() is coerced to NegInf and doesn't poison the front":
    # A NaN score evades both `dominates` and the cap-eviction sum (NaN < x
    # is always false), so it would otherwise fill the front with garbage.
    # The engine must coerce NaN to NegInf so the entry sorts as "worst".
    proc prop(x: int) =
      target(if x == 0: NaN else: float(x))  # NaN on x=0, positive elsewhere
      ensure true
    let r = forAll(integers(0, 100), prop,
                   Settings(maxExamples: 40, maxRejections: 1000, seed: 1,
                            flakyRetries: 0, maxShrinks: 50,
                            useSA: true, targetedSAIters: 50))
    check r.outcome == otPassed
    # Every score on the front must be a real number (no NaN survivors).
    for e in r.paretoFront:
      for v in e.scores.values:
        check v == v  # NaN != NaN; this rejects any NaN that survived

  test "target() guides toward a narrow falsifying region":
    # Property holds unless x+y > 1900 (~0.5% of the joint range);
    # with target(x+y), hill-climb pushes toward the boundary.
    proc prop(t: (int, int)) =
      target(float(t[0] + t[1]))
      ensure t[0] + t[1] <= 1900
    let r = forAll(tuples2(integers(0, 1000), integers(0, 1000)), prop,
                   Settings(maxExamples: 80, maxRejections: 1000, seed: 1))
    check r.outcome == otFalsified
    check r.counterexample[0] + r.counterexample[1] > 1900
