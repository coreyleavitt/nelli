# S8bm -- DONE

- **sha:** 14d7e813584ad71fd16367c38baf457f99bc4840 (branch `rfc-0005-s8bm`)
  - a02289e docs(rfc): RFC-0005 S8bm -- add the slice row
  - b63a92a perf(symex): RFC-0005 S8bm -- step 1 searches in a context of its own
  - 14d7e81 docs(rfc): RFC-0005 S8bm -- as landed (row flipped to done)
- **base:** built on 2d47b32 and **rebased onto 621af8f** (batch 3's final head, the heap-cell sort fix), as the coordinator asked. B1-1 was re-measured on both Z3 versions after the rebase, and the whole verification list ran on the rebased code tree.
- **walker:** 209 -> 214 (provisional). The CR2 `==` pin was updated and run (6/0 on both Z3 versions), and `>= 214` is pinned in the S8bm suite.

## Mechanism (item 1)

Z3's search on a walker query follows the **term order of the walk's shared Z3 context** (AST ids, and with them the rewriter's argument order and the solver's tie-breaks), not only the query. The facts-first check is one perturbation among many.

The experiments used local, uncommitted `-d:zz*` toggles in `checkCapped` (saved in `/home/corey/tmp-usage/work/s8bm-work/experiment-toggles.patch`). On Z3 5.1, B1-1's q10 (the target query, identical text at every head) cost the following in step 1:

| Variant | q10 units |
|---|---|
| as is (2d47b32; reproduces the evidence's 3,383,332 total) | 3,365,417 |
| no facts-first, the process's first walk (reproduces 187,401 total) | 172,215 |
| no facts-first, the process's second walk | 11,771,578 |
| no facts-first + ONE unrelated `mkIntVar` before each step 1 | 5,280,185 |
| no facts-first + 50 unrelated constants | 5,728,300 |
| facts-first in its own context (translated), UNSAT returns | 1,223,059 |
| same, never returning (main ctx = a later walk's: probe ran elsewhere) | 11,771,578 |
| step 1 in a fresh context (translated), with or without facts-first | 5,711,742 |
| translation into another context leaves the source's search unchanged | 172,215 / 3,365,417 (unchanged) |

The candidates in the job were checked as follows:
- **Random seed.** Every solver already gets `random_seed = 0`.
- **Solver reuse.** None: every step builds a fresh solver.
- **Push/pop and assertion leaks.** None: the code has no push/pop, and the checks are one-shot.
- **Declaration and term order.** This is the mechanism. A single constant that no query mentions moves the search 30x.

Isolating facts-first alone is not enough. By deciding earlier queries before their step 1 runs, it changes the context's history, and so do its fact terms and the per-thread kind probes.

## Design

- **Item 2: step 1 in a context of its own.** `checkCapped`'s step 1 runs in a fresh context via `ownContextSolver`, which translates the query and caps in, and the model is translated back. Step 1's cost is therefore a function of the query alone.
  - This is translation-safe because the walker builds no recursive function definitions, which a translation would drop.
  - `newContext` makes the new context the thread's current one; the walk context is restored.
  - Overhead is about 3 ms per query on 5.1 and about 13 ms on 4.13.4, measured under load.
- **Spend accounting.** `ownContextUnits` is a thread running total of own-context units.
  - `rlimitCountNow` adds it. This matters because `solveTargetHit` classifies S8y budget-outs and S8ag slow SATs from that reading.
  - The query stats add it to `rlimitDelta`, and `rlimit` stays cumulative.
- **Cheap: character form through a slice.** `byteTestChar` now follows `str.substr` down to the byte leaf, since a substring of a byte leaf has byte characters and `str.at` past its end is `""`. q10's `int2bv(str.to_code(str.at(str.substr(data,4,..),0))) == 42` becomes `str.at(..) == "*"`: 5,711,742 units become 24,467 on 5.1, and 60,895 on 4.13.4 (fresh context).
- **Test switch.** `symexFactsFirstOff` is a stats-build-only threadvar, so the suite can walk with and without facts-first. It follows the `symexQueryStatsPaused` precedent.

## RED / GREEN observed

1. **Same query with and without facts-first** (q10 decisions and conflicts equal, units within 25%).
   - RED at 2d47b32: 80,799 vs 32,250 decisions (3,365,417 vs 11,771,578 units).
   - GREEN: 191 vs 191 on 5.1 and 2,092 vs 2,092 on 4.13.4; units 28,573 vs 24,693 (5.1) and 63,126 vs 61,109 (4.13.4).
2. **B1-1 under the ceiling, byte test in character form.**
   - RED (step 1 isolated, no char form): 5,737,434 (5.1) and 1,268,400 (4.13.4), with `str.to_code` still in the query.
   - GREEN: 46,533 and 79,494.
3. **A target hit's spend counts step 1.**
   - RED at the commit without the `rlimitCountNow` accounting: the hit read 20,237 units for a query that spent 5,719,478.
   - GREEN at head. No existing suite caught this, which is why the test was added.
4. **s8ac's "per-query deltas sum to no more than the last".**
   - RED on 4.13.4 (359,236 > 358,768) while the stats `rlimit` added only the query's own units.
   - GREEN once `rlimit` read as `rlimitCountNow` does (19/0 on both versions).

## B1-1 before and after (whole walk, `rlimitDelta` sum)

| | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| before (2d47b32 = 621af8f for this code) | 3,383,332 | 7,766,466 (in the s8ba suite, per 2d47b32); 25,652,149 as a process's only walk (q10 unknown at 20M) |
| after (rebased), first walk | 46,533 | 79,494 |
| after, second walk, facts-first off | 40,250 | 78,667 |
| after, third walk | 46,529 | 79,510 |

**Item 3.** The ceilings are back to **100,000 (5.1) and 160,000 (4.13.4)**, about 2x the measurements, in both `s8ba_remainder` and `s8bm_stability`. Batch 3 had 7M/16M, and S8ba had 1M/3M.

**Item 4.** S8ay's two join-walk `< factsFirstRLimit` (1M) pins pass on both Z3 versions.

**Item 5: victims.**
- Swept the git history since the S8aw+S8ay merge for loosened pins. The only unit ceiling that was loosened is B1-1's (f09a07a split it into 1M/3M; 2d47b32 raised it to 7M/16M), and it is restored.
- S8ay's `endsWithRun` length bound (8b2508f, for 4.13.4) was re-probed unbounded at head. It is still `sxUnknown` on 4.13.4 (11.2M units in one query), which is a different mechanism, so the bound stays (listed below).
- Every `units|rlimit` suite was run on both Z3 versions; table below.

## Suites (ok/failed, c backend; identical on Z3 5.1 and 4.13.4; 64 runs + the cpp run)

| suite | 5.1 | 4.13.4 |
|---|---|---|
| s8bm_stability | 4/0 (cpp 4/0) | 4/0 |
| phase15_CR2_cachekey (214) | 6/0 | 6/0 |
| s8ba_remainder | 32/0 | 32/0 |
| s8ay_remainder | 40/0 | 40/0 |
| s8aw_remainder | 31/0 | 31/0 |
| s8au_remainder | 35/0 | 35/0 |
| s8ag_indexsplit | 15/0 | 15/0 |
| s8aj_remainder | 21/0 | 21/0 |
| s1c_verdict | 24/0 | 24/0 |
| s8y_budget_decline | 8/0 | 8/0 |
| g1b_concolic | 15/0 | 15/0 |
| g2_flip | 8/0 | 8/0 |
| phase13_rlimit | 1/0 | 1/0 |
| r4_strip | 5/0 | 5/0 |
| r6_b5_chained | 9/0 | 9/0 |
| r6_n36_raise_degrade | 8/0 | 8/0 |
| s1b_kinds | 18/0 | 18/0 |
| s8ac_remainder | 19/0 | 19/0 |
| s8ad_remainder | 13/0 | 13/0 |
| s8ae_remainder | 16/0 | 16/0 |
| s8aq_remainder | 13/0 | 13/0 |
| s8av_remainder | 19/0 | 19/0 |
| s8ax_remainder | 52/0 | 52/0 |
| s8bd_remainder | 23/0 | 23/0 |
| s8k_bounds | 19/0 | 19/0 |
| s8o_termination | 14/0 | 14/0 |
| s8q_termination | 10/0 | 10/0 |
| s8r_theoryfree | 3/0 | 3/0 |
| s8t_termination | 20/0 | 20/0 |
| s8v_termination | 7/0 | 7/0 |
| snd3_6_equality_loop | 3/0 | 3/0 |
| snd3_loopdegrade | 7/0 | 7/0 |

Notes on the runs:
- **Code tree.** All 64 runs except s8ac (and S8bm's later 4th test) ran at 15d48fc. The final code tree (5c60184 = b63a92a) differs from it only in the stats-build `rlimit` field and the added test, and s8ac plus the S8bm suite (c on both versions, cpp) were re-run on it.
- **S8bm suite time.** The test binary runs in 2.4 s (5.1 c), 3.8 s (4.13.4 c) and 4.4 s (5.1 cpp), at load average about 16. Wall time including compile is 63-73 s.
- **Performance, no regression** (wall times include compile, concurrent load):

| suite | Z3 | 621af8f | S8bm head |
|---|---|---|---|
| r4_strip | 5.1 | 364 s | 280 s |
| s8ae_remainder | 4.13.4 | 172 s | 156 s |

## Soundness bugs found

None in the walker's verdicts. One accounting defect introduced and fixed within the slice: isolating step 1 hid its units from `solveTargetHit`'s budget classification. It is pinned (RED 3 above).

## Windows CI

The legs for 14d7e81 are listed below. Stale runs for the superseded WIP shas were cancelled.

| leg | run id | result |
|---|---|---|
| symex-mingw | 37083269401 | success |
| fuzzer-mingw | 37083269389 | success |
| fuzzer-msvc | 37083269446 | success |

## Different mechanisms, reported and not fixed here (also in the RFC's "As landed (S8bm)")

- **PRECISION: the steps after step 1 still search in the walk's context.** The facts-first check, (1b) and (1c) are theory-free and small. (2), the uncapped (3), and a query with no string leaf (`plain`) are full-theory searches whose cost can still move with what the walk did before. A query that reaches them near its budget can therefore decline in one walk and not another. They remain deterministic for a given SUT and Z3 build.
- **PRECISION: the per-thread kind probes run in a process's first walk context** (`seqCapKinds`, `byteDomainKinds`, `intDivDeclKinds`, `theoryFreeSimple`'s check). That walk's context therefore differs from a later one's. With step 1 isolated, this reaches only the steps above.
- **PRECISION: unbounded `s.endsWith(re"b+") and not s.contains(re"b")` is `sxUnknown` on Z3 4.13.4** (11,234,660 units in its second query, `beSolverUndef`). S8ay's pin keeps `s.len <= 8`.

## Tree state

- Worktree `/home/corey/tmp-usage/work/wt/s8bm` is clean at 14d7e81.
- The extra verification worktrees (`wt/s8bm-v51`, `wt/s8bm-v413`, `wt/s8bm-base`) have been removed.
- Probes and logs are in `/home/corey/tmp-usage/work/s8bm-work/`.
