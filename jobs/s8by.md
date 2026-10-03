# Job: S8by -- new slice (S8bp's remainder; all PRECISION)

**Setup**
- Create branch `rfc-0005-s8by` from origin/rfc-0005-s8bp at 79037e4 (base 14d7e81, walker 219).
- Provisional walker: **231**.
- Read first: WORKER-BRIEF.md, WORKER-LOCAL.md, and the "As landed (S8bp)" notes.
- In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8by"
title = "S8bp's remainder: isolate concolic scratch solves, skip redundant 1b/1c after a facts-first SAT, term-order-stable wall time in translated contexts, mergeMemberships under disjunction/ite"
state = "pending"
```
- Flip the row to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **Isolate the concolic scratch solves.**
   - The calls are `concreteBranchOutcome`, `concretelyInfeasible`, and `runConcolicCollectImpl`'s concrete-inputs check.
   - Give each its own context, as S8bp did for `checkCapped`, so their spend and outcome depend only on the query.
   - Pin it: an outcome that changes with unrelated context content must now be stable.
2. **Skip the redundant (1b)/(1c) after a facts-first SAT.**
   - Reuse the known SAT (and its model where it is valid), so the extra spend is gone.
   - Show `lastNl`'s spend dropping by about 607k units, with verdicts unchanged.
3. **Wall time per unit follows term order.** `r4_strip`'s budget-out step 3 took 135 s against 58.5 s in the walk context.
   - Make the translated context's term order deterministic and close to the walk's. For example, translate in the walk's assertion order, or canonicalize term order before translating.
   - Get r4_strip back to at most 190 s on Z3 5.1.
   - Report the before and after times for r4_strip, B1-1 and lastNl.
4. **`mergeMemberships` reads only top-level conjuncts.**
   - Extend it to memberships under a disjunction or an `ite`, for example `a or not s.contains(re"b")`.
   - Pin with native Nim.

## Verification
- **Suites:** yours, the s8bp and s8bm suites, B1-1, r4_strip, s8ay, s8ar, s8bj_*, s8bb_*, CR2, phase13_rlimit, and every concolic suite (`command grep -l concolic tests/`).
- **Configurations:** Z3 5.1 and 4.13.4, plus one cpp run.

Push, and report DONE to `worker-reports/s8by.md`.
