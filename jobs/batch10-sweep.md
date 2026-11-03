# Job: batch10-sweep -- gate sweep for batch 10

**Target:** branch `rfc-0005-batch10` at EXACTLY **cecbe04**. Resolve the full sha with `git rev-parse origin/rfc-0005-batch10` and confirm it starts with cecbe04. The branch is based on e497dcf and is at walker 252.

## Step 0 (mandatory): dependency parity
`milpa.lock` is unchanged from batch 9. It pins nim-z3 at commit **cc5ffc9** (cc5ffc9a742c3251a16c95f1d3b98d4b93f05a91, identity dag-sha256:9a033bebe5b01bc9633d0e12c9c68b8f2e358dd0cc7917d98226b0ab26eb68d8, ref "main").

- The sweep worktree's `_deps/z3` must be exactly that tree. Diff it against a fresh clone at cc5ffc9.
- Do not change the deps of a running slice worktree for this.

If yours differs, fix it for the sweep before starting. Put the result of this check at the top of the report.

## Sweep
- Make a fresh worktree at cecbe04, with the deps copied as real directories.
- Set `PAUSE_SLICE_TESTS`.
- Run `scripts/sweep.sh -j 4 <log>`.
- Push the log, `.summary`, `.drift` and `.warnings` to `worker-sls2` as `worker-reports/batch10-gate.*`.
- Also report `tsymex_r6_b6_optionregion`'s wall time on Z3 4.13.4, and the wall time of `s8bb_constructs`.
- Clear the pause flag when the sweep is done.
