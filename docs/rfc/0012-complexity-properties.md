# RFC — complexity as a property

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. Small, cheap, and reuses machinery that already exists. Not yet
  designed.
- Category: core
- Size: S
- Value: med
- **Depends on:**
  - RFC-0008 (assurance-record) — soft. A complexity verdict is evidence and
    belongs in the record; it does not need it to ship.

## §0 — Thesis

nelli can check what your code computes. It cannot check what it costs.

That gap covers a well-populated bug class that ordinary properties are blind
to by construction — because these are bugs where **every output is correct**:

- hash-collision denial of service (correct lookups, quadratic time)
- a parser that is linear on well-formed input and quadratic on adversarial
  input
- catastrophic regex backtracking
- an accidental `O(n²)` from a `seq.delete` inside a loop, which passes every
  correctness property forever

## §1 — Why this is nearly free

`target(score)` is already a hill-climber with a simulated-annealing escape
over a user-supplied objective, with a Pareto front that persists across runs
(`engine/targeting.nim`). It was built to find inputs that maximize a number.

Point that number at **runtime** and it is a SlowFuzz-style algorithmic-
complexity attack search. The search machinery, the persistence, the shrinker,
and the report all already exist. What is missing is the objective and the
verdict.

## §2 — Scope

Two related facilities, and the RFC should be clear they are different claims:

1. **Complexity attack search.** `target(elapsed)` with the ergonomics and the
   noise handling made explicit — repeated timing, outlier rejection, a
   defensible measure. Finds the input that makes it slow. This is a *search*,
   and reports like one.

2. **Trend falsification.** `complexity(f, expected = onLogN)` — generate
   inputs of geometrically growing size, measure, fit, and falsify when the
   observed trend exceeds the expected class with statistical confidence. This
   is a *claim about an algorithm*, and it is the one that belongs in the
   assurance record.

## §3 — Open questions for the design phase

- **Wall-clock is a terrible measure** and a flaky one. Operation counting via
  the existing `{.cover.}` instrumentation is deterministic and reproducible,
  but counts edges rather than work. Allocation counts are a third option.
  **Which measure the RFC picks determines whether it produces a stable
  verdict or a flaky test**, and it is the central question.
- **Fitting a trend is statistics, not a predicate.** How much confidence, at
  what sample sizes, and what does the failure message say? "Observed
  `n^1.94`, expected `n·log n`, over sizes 64…8192" is actionable; "complexity
  check failed" is not.
- **What is "input size"?** Not derivable in general. A user-supplied size
  function is the honest answer; whether it can be derived for built-in
  containers is worth checking.
- **CI stability.** A timing-based property on shared CI runners is a
  flakiness generator. Does trend falsification run by default, or only under
  an explicit opt-in / a dedicated budget?

## §4 — First slice

Trend falsification against a *known-quadratic* function and a *known-linear*
one: the quadratic must falsify an `O(n)` claim, the linear must not. Two
functions, one verdict each, using whichever measure §3 settles on. That is
the whole load-bearing property, and it is small.

## §5 — Why it belongs on the board

It is the cheapest genuinely-differentiating item on the post-0005 survey:
weeks rather than quarters, built almost entirely on `target()`, and it covers
a bug class no property-based testing library addresses. It is also the
clearest demonstration that the targeted-search machinery generalizes beyond
the use case it was built for.
