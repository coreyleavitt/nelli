# Job: S8br -- new slice (S8bk's remainder; all PRECISION)

Create branch `rfc-0005-s8br` from origin/rfc-0005-soundness-channels at **fa8edd8**: batch 5 has landed, and it contains S8bk 9ce7fdb plus the newSeq unification and the late-address rule on closureCallIR. Walker there is 223. (Rebased from the original S8bk base.)
Provisional walker: **229** (must be above 223).

Read WORKER-BRIEF.md and the "As landed (S8bk)" notes first.

In your first commit, add this row before the S11 row:
```
[[slice]]
id = "S8br"
title = "S8bk's remainder: index call inside a var actual's lvalue (evaluate once, read late), checks no snapshot carries (frame-condition the later call), S8bk suite compile time"
state = "pending"
```
Flip it to `done` at the end.

## Scope (do all of it; defer nothing; pin each item RED first)
1. **An index call in a `var` actual's lvalue.** `touch(gArr[nextI()], f())` declines with `unsupported nnkAsgn shape`, because copy-out would call `nextI` again.
   - Model Nim's behaviour: evaluate `nextI()` ONCE, where the argument stands, into a temporary, and do the check there.
   - Read the element late, at the call. Write back through the same temporary index.
   - Pin it against a native run.
2. **A check that no snapshot carries.** `touch(gH.s[gi], f())` declines whenever `f` may write, even when `f` leaves `gH` and `gi` alone.
   - Use the callee's write set or frame condition. S8as/S8ax have summaries and capture/global write tracking.
   - Decline only when the later call may actually write a location the check read.
   - Pin both twins: the call leaves those locations alone, and the call writes them.
3. **Compile time.** The S8bk suite takes 57-103 s to compile on c and 184 s on cpp. Split it so each file stays under 60 s per backend including compile.

## Integration note
S8bn, running separately on S8bh's base, applies S8bk's late-address rule to S8bh's proc-value indirect-call path. You do not need those forms.

## Verification
- Suites: yours, s8bk, s8ax, s8ba, s8bd, s8bf_alias, s8as, CR2, letaudit, and every suite that `command grep -l 'feEvalOrderUnmodelled'` lists.
- Run them on Z3 5.1 and 4.13.4, plus one cpp run.

Push, then report DONE to `worker-reports/s8br.md`.
