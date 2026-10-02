# Job: batch-3 full sweep (PRIORITY: set the pause flag)

The final head of `rfc-0005-batch3` is now **621af8f5230508938b6603cd50711dd0c57bf49e**. It supersedes 2d47b32.
- It fixes the heap-sort defect in `src/nelli/smt/runtime_heap.nim`.
- The integrator ran the targeted suites at this head and they are green on both Z3 versions.

Steps:
1. Set the pause flag, then wait for in-flight slice runs to drain.
2. Re-pin the gate worktree to EXACTLY 621af8f (`git fetch; git checkout --detach 621af8f`), keeping the deps copied in.
3. Run `scripts/sweep.sh -j 4 /home/corey/tmp-usage/work/b3-gate.log`. Use -j 6 if the box is quiet.
4. Push the log plus its `.summary`, `.drift` and `.warnings` siblings to `worker-sls2` as `worker-reports/batch3-gate.*`.
5. Clear the pause flag and message the coordinator.

Do not interpret or diff the log; the coordinator does that.
