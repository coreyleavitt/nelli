# Job: batch9-sweep -- gate sweep for batch 9

**Target:** branch `rfc-0005-batch9` at EXACTLY **e497dcf**. Resolve the full sha with `git rev-parse origin/rfc-0005-batch9` and confirm it starts with e497dcf. The branch is based on afce42a and is at walker 245.

## Step 0 (mandatory): dependency parity
Batch 9 changes the lock. `milpa.lock` now pins nim-z3 at commit **cc5ffc9** (cc5ffc9a742c3251a16c95f1d3b98d4b93f05a91, identity dag-sha256:9a033bebe5b01bc9633d0e12c9c68b8f2e358dd0cc7917d98226b0ab26eb68d8, ref "main"). Earlier gates used ae509f0, so this sweep is the first full one on the new hooks.

- The sweep worktree's `_deps/z3` must be exactly that tree. Diff it against a fresh clone at cc5ffc9.
- Do not change the deps of a running slice worktree for this.

If yours differs, fix it for the sweep before starting. Put the result of this check at the top of the report.

## Sweep
- Make a fresh worktree at e497dcf, with the deps copied as real directories.
- Set `PAUSE_SLICE_TESTS`.
- Run `scripts/sweep.sh -j 4 <log>`.
- Push the log, `.summary`, `.drift` and `.warnings` to `worker-sls2` as `worker-reports/batch9-gate.*`.
- Also report `tsymex_r6_b6_optionregion`'s wall time on Z3 4.13.4, and the wall time of `s8bb_constructs`.
- Clear the pause flag when the sweep is done.
