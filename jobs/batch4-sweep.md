# Job: batch-4 full sweep (PRIORITY: set the pause flag)

Certify **8165899f5be6693f3abf5ff9dd50e6cf08d106d6**, the head of `rfc-0005-batch4`. It holds S8bb, S8bc, S8be and S8bh on 621af8f, at walker 217.

1. Set the pause flag and wait for in-flight slice runs to drain.
2. Create a gate worktree pinned to EXACTLY 8165899. You may re-pin the batch-3 gate worktree instead: `git fetch; git checkout --detach 8165899`. Copy the deps in.
3. Run `scripts/sweep.sh -j 4 /home/corey/tmp-usage/work/b4-gate.log`. Use -j 6 if the box is quiet.
4. Also run `tests/tsymex_r6_b6_optionregion.nim` on Z3 4.13.4 with the 900 s cap, and report its rc and wall time. The integrator skipped it.
5. Push the log, its `.summary`, `.drift` and `.warnings`, and the 4.13.4 r6_b6 result to `worker-sls2` as `worker-reports/batch4-gate.*`.
6. Clear the pause flag and message the coordinator.

Do not interpret or diff the results.
