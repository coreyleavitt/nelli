# Job: S8cc -- new slice (S8br's remainder)

## Setup
- Branch: create `rfc-0005-s8cc` from origin/rfc-0005-s8br at a25229d (base fa8edd8, walker 229).
- Provisional walker: **235**.
- Before starting, read WORKER-BRIEF.md, WORKER-LOCAL.md, and the "As landed (S8br)" notes.
- In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8cc"
title = "S8br's remainder: address cell at a non-literal array index with an input-dependent value runs past 420s, write summary over-approximates a global a later callee names, unnameable index call declines"
state = "pending"
```
- Flip the row to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **HANG: a query that never finishes.** An address cell at a non-literal array index, holding an input-dependent value, produces a query that runs past 420 s, both at base and at head.
   - Your base does NOT have S8bu's default query bound (250M / 10 min); that lands in batch 7. So set an explicit `queryRLimit` in your RED test, and bound every run with dt-bounded.
   - Find the encoding cause. Likely suspects are an array-theory store chain over a symbolic index, or a missing frame or extensionality fact. Make the query decide (SAT or UNSAT) well within budget.
   - A bounded decline is NOT the goal. A decline is acceptable only for a residual you prove hard, and then the report must include measurements.
   - Pin the query's decision time.
2. **The write summary over-approximates a global that a later callee names.** Make the summary precise, so a later callee that only names the global doesn't count as a write.
3. **An index call the walker cannot name declines.** Bind the call's result once into a temp, as S8br item 1 does for named calls, so the unnameable case decides too.

## Verification
- Suites: yours, s8br (2), s8bk (3), s8bs (4), s8be, s8ax, s8bh, s7_closure, CR2, and every `addr` / array-index grep hit.
- Run on Z3 5.1 and 4.13.4, plus one cpp run.
- Push, then report DONE to `worker-reports/s8cc.md`.
