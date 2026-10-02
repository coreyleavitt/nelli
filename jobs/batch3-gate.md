# Job: batch-3 gate (PRIORITY: set ~/work/PAUSE_SLICE_TESTS while this runs)

Certify `rfc-0005-batch3` at EXACTLY d42204d7522b0bf1ed2d44c0a0b59e91543878c6. That is RFC-0005 batch 3 (S8ax + S8ba + S8bd + S8bf on f488986, walker 209).

1. **Gate worktree.** Create a worktree at that sha (`~/work/wt/b3gate`) and copy the deps in as real directories (see WORKER-BRIEF). Never edit it while the gate runs.
2. **Targeted runs.** Run each suite below on BOTH Z3 5.1 (`scripts/dt-bounded.sh c`) and Z3 4.13.4 (`~/work/dt413.sh c`). Record the OK and FAILED counts and rc for each. The batch-3 integrator already ran the other 52 suites green on both versions.
   - Never run the same file twice at once.
   - If anything fails, include the failing `[FAILED]` lines and the assertion output.
3. **Full sweep.** Run it from the same worktree: `scripts/sweep.sh -j 4 ~/work/b3-gate.log`. If the slice agents are paused and the box is otherwise idle, use -j 6.
4. **Push results to `worker-sls2`:**
   - `worker-reports/batch3-gate.log`, plus `.summary`, `.drift` and `.warnings` (the files sweep.sh writes next to the log);
   - `worker-reports/batch3-targeted.md`, the targeted table.
   - Then message the coordinator.

The coordinator diffs the log against its baseline and watches the Windows legs. You do not need to touch CI.

## Targeted suites (tests/tsymex_<name>.nim)
rfc0005_s8ax_remainder
rfc0005_s8ba_remainder
rfc0005_s8bd_remainder
rfc0005_s8bf_alias
rfc0005_s8as_remainder
rfc0005_s8au_remainder
rfc0005_s8an_remainder
rfc0005_s8ac_remainder
rfc0005_s8aq_remainder
rfc0005_s8aw_remainder
rfc0005_s8aa_remainder
rfc0005_s8i_models
rfc0005_s8_scope
rfc0005_s8m_exits
rfc0005_s8ab_letaudit
rectify_effects
rfc0005_s9_vetoes
phase15_S6b_regex
r6_heap_raise_totality
r6_n16_closure_zerodefault
rfc0005_s7_closure
snd1b_closure_uncertain_axiom
phase16_R16_5_overflow_thru_closure
r9_recursive
z3_infra
r6_b1_stringbacked
r6_b7r_bytescan
r6_lows_collectors
r6_n27_placeholder_read_audit
r6_r4_collector_scoping
rfc0005_s0_exhibit
rfc0005_s1c_verdict
rfc0005_s1_lattice
rfc0005_s6a_budget
rfc0005_s6b_ops
rfc0005_s8ag_indexsplit
rfc0005_s8ap_remainder
rfc0005_s8c_resolution
rfc0005_s8o_termination

Some names above are approximate. Resolve each one with `ls tests/ | command grep -i <name>`. If a name matches several files, run them all. If it matches none, report it as such.
