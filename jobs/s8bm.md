# Job: S8bm -- new slice (performance and stability: facts-first perturbs step 1)

Create branch `rfc-0005-s8bm` from origin/rfc-0005-batch3 at 2d47b32 (walker 209).
Provisional walker: **214**. Read WORKER-BRIEF.md first, then:
- the S8ay "As landed" notes (facts-first, `factsFirstRLimit`);
- the S8ba notes (B1-1, `nimLenFacts`);
- the comment above the B1-1 pin in `tests/tsymex_rfc0005_s8ba_remainder.nim`.

In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8bm"
title = "Facts-first check perturbs the step-1 search: B1-1 q10 cost unstable (187k without facts-first vs 3.38M); restore tight unit ceilings"
state = "pending"
```
Flip it to `done` at the end.

## Evidence (`jobs/s8bm-evidence/` on this branch)

The B1-1 walk at d42204d on Z3 5.1. Almost all of its cost is q10's step-1 search.

| Variant | Units |
|---|---|
| As is | 3,383,332 |
| Facts-first without `nimLenFacts` | 1,963,139 |
| Facts-first solver built but never checked | 738,048 |
| Facts-first on the full theory | 1,715,154 |
| Facts-first removed | 187,401 |
| The facts-first check itself | about 12k |

By commit:

| Commit | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| Channel f488986 | 1.96M | 5.53M |
| S8ba chain head 77e57a7 | 380,570 | 2.29M |

The jump comes in with the S8aw + S8ay merge (8889263).

The q10 step-1 query text is IDENTICAL at the two heads (`q10-chaind.txt` vs `q10-headd.txt`). So the cost comes from Z3 state and search variance, not from query bloat.

The probe scripts are `b11*.sh` and `b11dump.py`. They used temporary `-d:zz*` toggles in `runtime.nim` that are not on the branch; recreate them locally.

## Scope (do all of it; defer nothing)
1. **Find the mechanism.** Find out why building or checking the facts-first solver changes step 1's cost. Candidates:
   - a shared Z3 context with global state: the random seed, the term-id / hash-cons order, or the arith solver's internal state;
   - a solver reused across the two;
   - assertions or push/pop leaking from one to the other;
   - declaration order.

   Prove it with targeted experiments.
2. **Fix it** so step 1's search is independent of whether facts-first ran. Options:
   - run facts-first in an isolated context;
   - give step 1 a fresh solver with a fixed seed;
   - control the declaration order.

   Make step 1 deterministic and cheap on B1-1.
3. **Restore tight B1-1 ceilings.** The S8ba-era figures were about 380k on 5.1 and 2.3M on 4.13.4. Use measured figures with headroom.
4. **Keep the facts-first budget.** S8ay's join walks must stay under `factsFirstRLimit` (the 1M pins).
5. **Check for other victims.** Look for other unit-ceiling pins or timing-sensitive pins affected by the same mechanism, and restore any that were loosened.

**Test file:** `tests/tsymex_rfc0005_s8bm_stability.nim`. It must include:
- a determinism test: the same query, with and without a preceding facts-first, costs about the same;
- a pin for the restored ceiling.

**Verification:**
- Suites: yours, s8ba, s8ay, s8aw, s8au, s8ag_indexsplit, s8aj, s1c_verdict, s8y_budget_decline, CR2, plus every suite asserting rlimit or units (find them with `command grep -l 'units\|rlimit' tests/tsymex_*`).
- Run them on Z3 5.1 and 4.13.4, plus one cpp run.

Push, then report DONE to `worker-reports/s8bm.md`, including the measurements before and after.
