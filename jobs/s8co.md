# Job: S8co -- new slice (S8cf's remainder; item 1 is a crash)

## Setup
- Branch: create `rfc-0005-s8co` from origin/rfc-0005-soundness-channels at afce42a, then merge origin/rfc-0005-s8cf at a0824d0. If batch 9 or 10 has landed by then, the coordinator will name the base.
- Walker number is assigned at integration; use the next free one above 246 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8cf.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8co"
title = "S8cf's remainder: the regexRecDefConds segfault, older PCRE builds by differential leg, auto-possession and skip-arg limit declines, group repeats on the JIT, SKIP:NAME counts, (*ANY) under the JIT scan, multi-item POSIX classes on 8.37, replace and count gaps, unbounded refutation past the safe length"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native PCRE)
1. **CRASH: a `v == f` Int definition in `regexRecDefConds` segfaults at `byteLeafIds` dec_ref.** S8cf only avoided it. Find the cause: a wrong refcount here can hide a use-after-free, so check under valgrind or an ASan build whether it is S8cf's construction or something in the hooks. Re-test with nim-z3 cc5ffc9 (S8ce), which changes every hook. Fix it, then use the definition if it is the better encoding.
2. **PCRE 8.44 and 8.39 stay declined because no CI leg runs them.** Adding the 32 regex suites per build costs far too much. So build a differential-only check instead: S8bt's and S8cf's harnesses run against those two builds, on Linux, without the walker suites. Measure it.
   - Under 5 minutes of CI per build: add it to a Linux job and allowlist the build.
   - Over 5 minutes: keep them declined, and report the cost.
   - Either way, model 8.39 JIT's 113 prefix-scan differences or decline them precisely.
3. **Auto-possession comparing a property or XCLASS with another item** declines. Model it.
4. **A kept `ignore_skip_arg` under a limit** declines (model -8 against native -1 on abab at LIMIT_MATCH=5). Model it.
5. **`detect_repeat` group repeats on the JIT** stay unread (400 calls skipped). Read them.
6. **SKIP:NAME.** A count past 100 is unmodelled, and languages decline past 7. Extend both, bounded by measured cost.
7. **Symbolic `(*ANY)` under the JIT's scan** stays unknown, with 72+ real differences when lifted. Model the scan.
8. **Multi-item POSIX classes on 8.37** decline. Model them.
9. **`replace`'s unmarked SKIP:NAME** has no sure bytes, and `first` is not computed in UTF. Add both. **`count`** of a `set[char]` and overlapping counts stay unregistered: register them, native-checked.
10. **An unbounded no-match refutation past `limitReach`'s safe length is now unknown** (`altPlus` moved from `sxUnsat`). That is correct where the limit can change the outcome. Decide the patterns where it cannot: where no input length can reach a limit before the match fails, the refutation holds at every length. Prove that per pattern, pin it, and keep `altPlus`'s decline if it really can reach one.

## Verification
- Suites: yours, s8cf_* (all), s8bt_* (all), s8bj_* (all), s8bb_* (all), s5_str, emit_roundtrip, CR2.
- Run on Z3 5.1, 4.13.4 and the 8.37+JIT runner, plus cpp for the new suites. All three Windows legs green.
- Report DONE to `worker-reports/s8co.md`, with per-file Windows times.
