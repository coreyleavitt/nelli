# Job: S8cj -- new slice (S8by's process-level findings; PRECISION)

Use opus. This is a diagnosis first: find the cause before choosing a fix.

## Setup
- Branch: create `rfc-0005-s8cj` from origin/rfc-0005-soundness-channels at 136ad60, then merge origin/rfc-0005-s8by at 2cb85f5, reusing `s8by-work/trial-merge.diff`. If batch 8 has landed by then, base on its head instead; the coordinator will say.
- Walker number is assigned at integration; use the next free one above 241 locally, and update the CR2 pin to match. If the slice changes no walker semantics, leave the walker alone and say so.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md, worker-reports/s8by.md and `raw/cpa0.txt`, `raw/cpa1.txt`, `raw/cp7h413.txt` first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cj"
title = "S8by's process-level findings: a thread's spend on a query follows what earlier threads ran; Z3 5.1's internal check on wide factoring"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **A fresh thread's spend follows what earlier threads ran.** On Z3 5.1 one factoring solve took 72,124 units on non-main threads until a thread ran it beside 3,000 unrelated constants, then 5,854,994 on that thread and every later one. The main thread did not move. 4.13.4 moves similarly, 26,695 to 911,593.
   - Identify the state that carries over, down to the Z3 mechanism, and reduce it to a small C-API-level reproducer if the cause is in Z3.
   - Then make a query's spend independent of that history. If nothing the engine can do from outside Z3 achieves that, write down exactly what remains true.
   - Correct the "function of the query alone" claims from S8bm and S8bp to match what you find, in the code comments and the RFC.
   - Check whether any existing pin depends on suite order for this reason, and fix each one you find.
2. **`Failed to verify: m_cache.mk_unique(p) == p` on Z3 5.1.** Seen on wide factoring with `x`, `y` below 200000.
   - Reduce it to a small SMT-LIB file and record it in the report, with the Z3 version, so it can be filed upstream. Do not file it yourself.
   - Establish whether a verdict reached after this check can be trusted. If not, the engine must decline on that query, which is a soundness fix; say so at the top of the report.
   - The message must not reach a user's output as unexplained noise. Route it or document it.

## Verification
- Suites: yours, s8by, s8bp, s8bm, r4_strip, CR2, phase13_rlimit, s8bb_constructs, and any suite you changed.
- Run on Z3 5.1 and 4.13.4, plus cpp for the new suite. All three Windows legs green.
- Report DONE to `worker-reports/s8cj.md`, with per-file Windows times.
