# Batch-6 gate at 80c2904418a68ef236122034598eda4b2f852485, with the n45 fix at 8a2eb51

## Step 0: dependency parity (PASS)
- 80c2904's `milpa.lock` pins nim-z3 at ae509f0eea606bd085064ce1f1ab107c2cdd5806 and softlink at 872042789d93942e2258d08ff167f44ebc5c8104.
- The gate worktree `wt/b6gate` was created fresh, with `_deps/z3` at ae509f0 and a clean tree.
- Every other worktree on this host was re-audited: each `_deps/z3` copy is at ae509f0 and clean.

## Sweep at 80c2904
- `scripts/sweep.sh -j 4`, c backend, 900s timeout, wall time 10354s.
- The worktree was a fresh one at exactly 80c2904, not edited during the sweep. The pause flag was set throughout.
- Wall time is about 2x batch 5's 4965s. That is not interpreted here; slice agents were paused for tests but still compiling and editing, with load average around 9-11.

```
backend=c jobs=4 timeout=900s
pass=607 fail=1 (of which timeout-killed=0) skip=0 total=608
unregistered=0 missing=0 stale_skiplist=0  (see /home/corey/tmp-usage/work/b6-gate.log.drift)
warn_tests=565 warn_total=12303  (see /home/corey/tmp-usage/work/b6-gate.log.warnings) -- trend only, never zero; the gate is scripts/sweep-diff.sh's warnings delta against a baseline, not this total

## failing
1 c tests/tprobe_n45stats.nim 21
```

### The one failure: tprobe_n45stats (a stale test, fixed in 8a2eb51)
Re-run in the 80c2904 gate tree after the sweep had passed it, to capture its output (`batch6-gate.n45-80c2904.log`):
```
STATUS=sxSat
  TOTAL queries=2 asserts=3 rlimit=16749 drlimit=9246
  [OK] sat query records nonzero rlimit
STATUS=sxUnsat
  TOTAL queries=0 asserts=0 rlimit=0 drlimit=0
    /work/tests/tprobe_n45stats.nim(46, 31): Check failed: symexQueryStats.len > 0
    symexQueryStats.len was 0
  [FAILED] unsat query records stats too
  [OK] assertion count tracks path-condition growth
```
- S8bl folds `a != a` to false, so Z3 is never called. The coordinator confirmed this and fixed the test in 8a2eb51, a test-only change of 1 file.

## Fixed probe at 8a2eb5101e9cd530f191b9f89a1256f0e43b1057
This run used a fresh worktree `wt/b6fix` with deps at ae509f0, and ran `scripts/dt-bounded.sh c tests/tprobe_n45stats.nim 600` (`batch6-gate.n45-8a2eb51.log`): rc=0 in 51.3s.
```
STATUS=sxSat
  TOTAL queries=2 asserts=3 rlimit=16749 drlimit=9246
  [OK] sat query records nonzero rlimit
STATUS=sxUnsat
  TOTAL queries=1 asserts=2 rlimit=59 drlimit=31
  [OK] unsat query records stats too
  [OK] assertion count tracks path-condition growth
```

## Timed single runs at 80c2904
These ran alone after the sweep, with the slices paused. Wall time includes compile.

```
r6b6_413 rc=0 ok=8 failed=0 wall=35.5s
s8bb_constructs_51 rc=0 ok=7 failed=0 wall=38.8s
s8bb_constructs_413 rc=0 ok=7 failed=0 wall=47.6s
```
