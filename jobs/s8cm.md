# Job: S8cm -- new slice (corpus compile time on Windows)

**HELD: do not start until the coordinator releases it after batch 9 lands.** The files it splits are moving until then.

## Setup
- Branch: `rfc-0005-s8cm`, from the base the coordinator names on release.
- Tests and CI only, so no walker change.
- Read WORKER-BRIEF.md and WORKER-LOCAL.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cm"
title = "Corpus files over 60 s compile plus run on Windows, and shard budgets"
state = "pending"
```

## Scope (do all of it; defer nothing)
1. S8ca's run found 21 files over 60 s compile plus run on Windows, most of it compile time. Use a current run's per-file times to list them afresh. Measure on Windows, compare at least two runs, and bring each file under 60 s, by splitting at a meaningful boundary or by removing what makes it compile slowly. Keep every test and verdict.
2. Find what makes those compiles slow. For example, `s8ar_remainder` runs 5.4 s and takes 110 s in all. If the cause is shared, such as SUT count or a macro's cost per SUT, fix the cause rather than splitting around it.
3. Check the shard budgets. A shard at 38.9 of 40 minutes fails on a slow runner with every suite passing, as 1c9bc98's shard 0 did. Rebalance by measured time, so that no shard's typical time is above 30 minutes.

## Verification
- Every test count is unchanged in total, compared against the base by a script.
- `nelli.nimble` registers any new file.
- All three Windows legs green.
- Report DONE to `worker-reports/s8cm.md`, with per-file Windows times.
