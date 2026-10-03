# Batch-5 gate at fa8edd82d10e7c850a0fa8ca4878f50b40ab6682

## Step 0: dependency parity (PASS)
- fa8edd8's `milpa.lock` pins nim-z3 at commit ae509f0eea606bd085064ce1f1ab107c2cdd5806 (identity dag-sha256:3864c15d...).
- The gate worktree's `_deps/z3` HEAD is ae509f0eea606bd085064ce1f1ab107c2cdd5806, with a clean tree. softlink is at 872042789d93942e2258d08ff167f44ebc5c8104.
- Every worktree on this host was audited, about 20 of them: both earlier gate worktrees, and every slice and base worktree. Every `_deps/z3` copy is at ae509f0, so the batch-3 and batch-4 gates and every slice run here used the locked nim-z3.
- The only modification found was S8bu's own worktree: a `when defined(s8buDump)` debug hook in `solver.nim`. It does nothing unless that flag is set, and S8bu is told to revert it before verification.

## Sweep
- `scripts/sweep.sh -j 4`, c backend, 900s timeout, wall time 4965s.
- The worktree was a fresh one, verified at exactly fa8edd8 and clean, with the pause flag set throughout.

```
backend=c jobs=4 timeout=900s
pass=591 fail=0 (of which timeout-killed=0) skip=0 total=591
unregistered=0 missing=0 stale_skiplist=0  (see /home/corey/tmp-usage/work/b5-gate.log.drift)
warn_tests=548 warn_total=11016  (see /home/corey/tmp-usage/work/b5-gate.log.warnings) -- trend only, never zero; the gate is scripts/sweep-diff.sh's warnings delta against a baseline, not this total
```

## Timed single runs
These ran alone after the sweep, with the slices still paused. Wall time includes compile.

```
r6b6_413 rc=0 ok=8 failed=0 wall=77.4s
s8bb_constructs_51 rc=0 ok=7 failed=0 wall=34.5s
s8bb_constructs_413 rc=0 ok=7 failed=0 wall=36.6s
```

- `r6b6_413` is `dt413.sh c tests/tsymex_r6_b6_optionregion.nim 900`.
- `s8bb_constructs_51` and `s8bb_constructs_413` are `tests/tsymex_rfc0005_s8bb_constructs.nim` on Z3 5.1 and 4.13.4.
