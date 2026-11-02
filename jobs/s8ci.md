# Job: S8ci -- new slice (S8by's item 3 reopened, and the costs its term order introduced; PRECISION)

Use opus. S8by's report shows item 3 was not achieved: the 190 s ceiling meant "back to S8bm", and it was met only because the host changed.

## Setup
- Branch: create `rfc-0005-s8ci` from origin/rfc-0005-soundness-channels at 136ad60, then merge origin/rfc-0005-s8by at 2cb85f5, reusing `s8by-work/trial-merge.diff`. Check the timeout at the concolic sites while resolving: `queryTimeoutMsCur` against `settings.budget.queryTimeoutMs`. If batch 8 has landed by then, base on its head instead; the coordinator will say.
- Walker number is assigned at integration; use the next free one above 241 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8by.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8ci"
title = "S8by's item 3 reopened: a translated term order that earns its cost, r4_strip back to S8bm, configdefaults and s8ai_semantic under 60 s, wide factoring decided again"
state = "pending"
```

## Scope (do all of it; defer nothing)
Measure everything side by side on one host, S8bm 14d7e81 and S8bp 79037e4 against the head, with at least two pairs each. A figure from a different host or a different load does not count.
1. **Find an order that is worth keeping, or remove it.** At S8by's head, `queryTermOrder` gains 4-7% on r4_strip, more than doubles `lastNl`'s spend against the skip alone (498,821 to 1,026,624), and may cost the items below. Compare at least: the current order, the walk's assertion order, and S8bp's root-by-root translation. Keep the one with the best result across r4_strip, B1-1, lastNl, configdefaults and wide factoring. If none beats no reordering, take `queryTermOrder` out. Determinism within one thread history is required of whichever stays.
2. **r4_strip within 10% of S8bm**, side by side, on Z3 5.1.
3. **A behavioural pin for the order.** Item 3 has no behavioural RED today; the test pins the order itself. Pin a spend or verdict difference that fails if the order is reverted. Do not pin wall time.
4. **Trace and fix `tsymex_configdefaults`' rise,** 98 s at S8bp to 127 and 153 s on Windows, after the skip and uncaptured so far. Bring it and `s8ai_semantic` under the 60 s convention on Windows, by speeding them up or by splitting the suite at a meaningful boundary. S8ca is working on configdefaults' cpp segfault; rebase on it if it lands first.
5. **Wide factoring.** Rebuild and confirm or refute that `x * y == 6999433` with `x`, `y` below 200000 went from decided in 5,526,707 units to out of 50M on Z3 5.1. If it is real and caused by the order, it must be decided again. Pin the outcome against native Nim.
6. **State the skip's real saving at the final code.** Report units with the skip on and off, for `lastNl` and B1-1, on both Z3 versions.

## Verification
- Suites: yours, s8by, s8bp, s8bm, B1-1, r4_strip, configdefaults, s8ai_semantic, s8ay, s8ar, s8bj_*, s8bb_*, CR2, phase13_rlimit, and every concolic suite (`command grep -l concolic tests/`).
- Run on Z3 5.1 and 4.13.4, plus cpp for the new suite. All three Windows legs green.
- Report DONE to `worker-reports/s8ci.md`, with per-file Windows times.

## Added after batch 8
Batch 8 split the slow files: `tsymex_configdefaults_depth` (the `maxCallDepth: 50` pin, about 96 s on Windows) from `tsymex_configdefaults`, and `tsymex_rfc0005_s8ai_semantic_b` (52.9 s) from `s8ai_semantic`. Base on batch 8's head, as the coordinator will say. Item 4's target is now `configdefaults_depth`. Find why one test spends 96 s and fix that cause. Do not lower the depth, because the pin exists to prove the bound at that depth.

## Added by batch 9
S8by's `queryTermOrder` moved `ti_tuple`'s SAT search on Z3 4.13.4 from 79,811,644 to 411,783,288 units, so `s8bc_remainder_c`'s `tupleBudget` went from 300M to 600M, costing about +100 s on Linux. UNSAT queries fell (142,112 to 68,137, and 521,055 to 315,601). Take the term order itself: find an order that keeps the UNSAT gains without the SAT cost, or measure why none exists, then lower the budget back if you can.
