import std/[unittest, tables]
import nelli
import nelli/[int128, choice, serialize, rng, datasource, shrinker]
import zerofill  # RFC-0010 A1 pin; removed by A3

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
                        zeroFilled(Settings(maxExamples: 30, maxRejections: 1000,
                                            seed: seed, flakyRetries: 0, maxShrinks: 50,
                                            useSA: false, targetedSAIters: 200)))
      let withSA = forAll(integers(-2000, 2000), prop,
                          zeroFilled(Settings(maxExamples: 30, maxRejections: 1000,
                                              seed: seed, flakyRetries: 0, maxShrinks: 50,
                                              useSA: true, targetedSAIters: 200)))
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
    let r = forAll(map(integers(0, 1000), integers(0, 1000)), prop,
                   zeroFilled(Settings(maxExamples: 40, maxRejections: 1000, seed: 1,
                                       flakyRetries: 0, maxShrinks: 50, useSA: true,
                                       targetedSAIters: 200)))
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
                   zeroFilled(Settings(maxExamples: 8, maxRejections: 1000, seed: 1,
                                       flakyRetries: 0, maxShrinks: 50,
                                       useSA: true, targetedSAIters: 400)))
    check r.outcome == otPassed

  test "clampToInt64 never wraps via the 2^63.0 float-rounding edge":
    # `float(high(int64))` rounds *up* to `2^63.0`; the obvious clamp lets
    # that edge value pass through, and `int64(2^63.0)` then wraps to
    # `low(int64)` on x86 (UB by spec). Engine hill-climb and SA both relied
    # on this; the safe-clamp helper snaps the upper bound below the float
    # edge so the cast is guaranteed in-range.
    check clampToInt64( 1e30, 0'i64, high(int64)) >= 0
    check clampToInt64( 1e30, 0'i64, high(int64)) <= high(int64)
    check clampToInt64(-1e30, low(int64), high(int64)) >= low(int64)
    check clampToInt64(-1e30, low(int64), high(int64)) <= high(int64)
    # In-range values pass through unchanged.
    check clampToInt64(42.0, 0'i64, 100'i64) == 42'i64
    # NaN input is benign — clamps to lo (per Nim's clamp NaN semantics).
    check clampToInt64(NaN, 0'i64, 100'i64) in 0'i64 .. 100'i64
    # Singleton range at the top of int64 must still return `high(int64)`,
    # not `high(int64) - 2047` from an inverted-edge float clamp.
    check clampToInt64(1e30, high(int64), high(int64)) == high(int64)
    check clampToInt64(0.0, high(int64), high(int64)) == high(int64)

  test "targetedSAIters: 0 disables the SA phase (no special 'default' magic)":
    # Previously `targetedSAIters: 0` was reinterpreted as 200 (the baked-in
    # default) so consumers couldn't actually request 0 SA iters. That is
    # surprising — `useSA: false` is the only off-switch we want, and the
    # iter count should mean what it says. Same scenario as the SA-escape
    # test, but with explicit 0; we expect *no* SA-exclusive falsifications.
    proc score(x: int): float =
      let a = abs(x)
      if a <= 5: 100.0 - a.float * 5.0
      elif a >= 1550 and a <= 1560: 250.0
      else: 0.0
    proc prop(x: int) =
      target(score(x))
      ensure score(x) < 200.0
    var saHits = 0
    for seed in 1'u64 .. 8'u64:
      let r = forAll(integers(-2000, 2000), prop,
                     zeroFilled(Settings(maxExamples: 30, maxRejections: 1000,
                                         seed: seed, flakyRetries: 0, maxShrinks: 50,
                                         useSA: true, targetedSAIters: 0)))
      if r.outcome == otFalsified: inc saHits
    # With 0 SA iters and the same trap landscape, only random+greedy runs.
    # Random+greedy alone misses the global peak; SA-via-iters=0 has nothing
    # to add. We expect ≤ 1 falsification across all seeds (a generous slack
    # for any random luck).
    check saHits <= 1

  test "±Inf in target() is coerced to finite sentinels so SA stays well-defined":
    # `+Inf` as a reference point makes augmented-Tchebycheff compute
    # `Inf − Inf = NaN` for every candidate, killing SA acceptance. NaN was
    # handled in mediums round 1; ±Inf gets the same treatment now, but
    # *toward the meaningful magnitude*: +Inf → very large finite, -Inf →
    # very small finite. SA continues working and the front still ranks.
    proc prop(x: int) =
      target(if x mod 2 == 0: Inf else: float(x))
      ensure true
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 30, maxRejections: 1000, seed: 1,
                                       flakyRetries: 0, maxShrinks: 50,
                                       useSA: true, targetedSAIters: 50)))
    check r.outcome == otPassed
    for e in r.paretoFront:
      for v in e.scores.values:
        check v == v                       # not NaN
        check v < Inf and v > NegInf       # not ±Inf either

  test "all-NaN scores don't poison the SA aggregator for the rest of the run":
    # When `target()` only ever gets NaN, the previous fix coerced to NegInf;
    # `bumpedRef(NegInf, 1.0) = NegInf` then made augmentedTchebycheff return
    # NaN, killing SA acceptance for the whole run. The current behavior
    # coerces NaN to a finite sentinel so refPoint stays finite and SA's
    # acceptance probabilities remain well-defined.
    proc prop(x: int) =
      target(NaN)
      ensure true
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 30, maxRejections: 1000, seed: 1,
                                       flakyRetries: 0, maxShrinks: 50,
                                       useSA: true, targetedSAIters: 50)))
    check r.outcome == otPassed
    # Every front score must be finite — no NegInf, no NaN.
    for e in r.paretoFront:
      for v in e.scores.values:
        check v == v                    # not NaN
        check v != NegInf and v != Inf  # finite

  test "NaN passed to target() is coerced to a finite sentinel and doesn't poison the front":
    # A NaN score evades both `dominates` and the cap-eviction sum (NaN < x
    # is always false), so it would otherwise fill the front with garbage.
    # The engine coerces NaN to a finite sentinel so the entry sorts as
    # "worst" via dominance while keeping the SA aggregator finite.
    proc prop(x: int) =
      target(if x == 0: NaN else: float(x))  # NaN on x=0, positive elsewhere
      ensure true
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 40, maxRejections: 1000, seed: 1,
                                       flakyRetries: 0, maxShrinks: 50,
                                       useSA: true, targetedSAIters: 50)))
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
    let r = forAll(map(integers(0, 1000), integers(0, 1000)), prop,
                   zeroFilled(Settings(maxExamples: 80, maxRejections: 1000, seed: 1)))
    check r.outcome == otFalsified
    check r.counterexample.get[0] + r.counterexample.get[1] > 1900
