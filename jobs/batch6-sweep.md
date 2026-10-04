# Job: batch6-sweep -- gate sweep for batch 6

**Target:** branch `rfc-0005-batch6` at EXACTLY **80c2904** (80c2904418a68ef236122034598eda4b2f852485). The branch is based on fa8edd8 and is at walker 230.

## Step 0 (mandatory): dependency parity
The coordinator found that its own checkout's `_deps/z3` was STALE. It pointed at a nim-z3 build older than the locked one, so local runs since S8at's lock bump used the wrong nim-z3.

Check yours before sweeping:
- `milpa.lock` pins nim-z3 at commit **ae509f0** (identity dag-sha256:3864c15d...).
- The sweep worktree's `_deps/z3` must be exactly that tree. Check the git sha of `/home/corey/tmp-usage/work/deps/nim-z3`, or diff it against a fresh clone at ae509f0.

If yours differs:
1. Fix it.
2. Report which nim-z3 sha the batch-3 and batch-4 gate sweeps, and the slices you have run so far, actually used.
3. Tell every running slice agent to re-copy `_deps/z3` and re-run its suites.

Put the result of this check at the top of the report.

## Sweep
- Make a fresh worktree at 80c2904, with the deps copied as real directories.
- Set `PAUSE_SLICE_TESTS`.
- Run `scripts/sweep.sh -j 4 <log>`.
- Push the log, `.summary`, `.drift` and `.warnings` to `worker-sls2` as `worker-reports/batch6-gate.*`.
- Also report `tsymex_r6_b6_optionregion`'s wall time on Z3 4.13.4, and the wall time of `s8bb_constructs`.
- Clear the pause flag when the sweep is done.
