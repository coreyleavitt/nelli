# Job: batch-3 full sweep (PRIORITY: set the pause flag)

The final head of `rfc-0005-batch3` is **2d47b32a36a9dd0648547a669cbfa0fc991b67c0**.
- It differs from d42204d in test files only; `src/` is unchanged.
- Your targeted results at d42204d therefore stand.
- The three suites that failed have been re-pinned. They pass at this head on both Z3 versions; the batch-3 integrator verified that.

Steps:
1. Re-pin the gate worktree to EXACTLY 2d47b32, keeping the deps copied in.
2. Run `scripts/sweep.sh -j 4 /home/corey/tmp-usage/work/b3-gate.log`. Use -j 6 if the box is otherwise quiet.
3. Push the log and its `.summary`, `.drift` and `.warnings` files to `worker-sls2` as `worker-reports/batch3-gate.*`.
4. Message the coordinator.

Do not interpret or diff the log; the coordinator does that against its baseline.
