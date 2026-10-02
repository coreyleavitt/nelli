# Batch-3 gate: targeted suites at d42204d7522b0bf1ed2d44c0a0b59e91543878c6

Worker sls2. Worktree pinned at d42204d (walker 209). c backend, 900s timeout per run, 4 files in parallel. Each file ran on Z3 5.1.0.0 (`scripts/dt-bounded.sh`) and then Z3 4.13.4.0 (`dt413.sh`).

**Result: 36 of 39 suites pass on both versions. 3 suites FAIL, identically on both versions (6 of 78 runs).** Per the coordinator's instruction, the full sweep was NOT run at this sha.

Name resolution:
- `r9_recursive` resolved to `tsymex_phase15_r9_recursive`.
- `z3_infra` resolved to `tsymex_phase15_z3_infra`.
- All other names matched `tests/tsymex_<name>.nim` exactly. None matched zero files or several files.

## Failures

### 1. tsymex_rfc0005_s8bd_remainder: 22 OK, 1 FAILED (both Z3)
```
  [OK] a generic callee
    /work/tests/tsymex_rfc0005_s8bd_remainder.nim(450, 19): Check failed: r.status == sxUnknown
    r.status was sxUnsat
    sxUnknown was sxUnknown
    /work/tests/tsymex_rfc0005_s8bd_remainder.nim(451, 26): Check failed: r.errors.hasKind(heUnsafeCast)
  [FAILED] a generic callee's escaping pointer is not a local cell

[Suite] S8bd: walker version
```
Z3 4.13.4 fails the same test, `a generic callee's escaping pointer is not a local cell`.

### 2. tsymex_rfc0005_s8au_remainder: 34 OK, 1 FAILED (both Z3)
```
  [OK] vpi
    /work/tests/tsymex_rfc0005_s8au_remainder.nim(58, 19): Check failed: r`gensym547.status == sxUnknown
    r`gensym547.status was sxSat
    sxUnknown was sxUnknown
    /work/tests/tsymex_rfc0005_s8au_remainder.nim(59, 26): Check failed: r`gensym547.errors.hasKind(heUnsafeCast)
    /work/tests/tsymex_rfc0005_s8au_remainder.nim(60, 17): Check failed: "addr" in show(r`gensym547.errors)
  [FAILED] vpr
  [OK] nim

```
Z3 4.13.4 fails the same test, `vpr`. This suite was 35/35 at f488986 in the setup smoke run, so batch 3 introduced the failure. Together with #1, it looks like a lost heUnsafeCast decline on an escaping pointer or `addr`, which yields a definite verdict where a decline is expected. That would be a possible SOUNDNESS issue.

### 3. tsymex_rfc0005_s8ba_remainder: 31 OK, 1 FAILED (both Z3)
```
Z3 5.1:
  TOTAL queries=11 asserts=87 rlimit=3489374 drlimit=3383328
    /work/tests/tsymex_rfc0005_s8ba_remainder.nim(520, 33): Check failed: units <= 1000000
    units was 3383328
Z3 4.13.4:
  q10 sat asserts=11 rlimit=7767889 drlimit=7750197 conflicts=4549 decisions=476791 props=725556 memMB=17.51
  TOTAL queries=11 asserts=87 rlimit=7877281 drlimit=7766466
    /work/tests/tsymex_rfc0005_s8ba_remainder.nim(521, 22): Check failed: units <= 3000000
    units was 7766466
```

## Table

| Suite | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| tsymex_rfc0005_s8ax_remainder | PASS 52 OK / 0 FAILED, 114.1s | PASS 52 OK / 0 FAILED, 125.5s |
| tsymex_rfc0005_s8ba_remainder | **FAIL rc=1** 31 OK / 1 FAILED, 70.7s | **FAIL rc=1** 31 OK / 1 FAILED, 71.9s |
| tsymex_rfc0005_s8bd_remainder | **FAIL rc=1** 22 OK / 1 FAILED, 60.3s | **FAIL rc=1** 22 OK / 1 FAILED, 59.2s |
| tsymex_rfc0005_s8bf_alias | PASS 13 OK / 0 FAILED, 56.8s | PASS 13 OK / 0 FAILED, 56.5s |
| tsymex_rfc0005_s8as_remainder | PASS 33 OK / 0 FAILED, 70.5s | PASS 33 OK / 0 FAILED, 66.6s |
| tsymex_rfc0005_s8au_remainder | **FAIL rc=1** 34 OK / 1 FAILED, 65.4s | **FAIL rc=1** 34 OK / 1 FAILED, 60.8s |
| tsymex_rfc0005_s8an_remainder | PASS 25 OK / 0 FAILED, 73.4s | PASS 25 OK / 0 FAILED, 68.3s |
| tsymex_rfc0005_s8ac_remainder | PASS 19 OK / 0 FAILED, 50.1s | PASS 19 OK / 0 FAILED, 51.5s |
| tsymex_rfc0005_s8aq_remainder | PASS 13 OK / 0 FAILED, 35.8s | PASS 13 OK / 0 FAILED, 32.6s |
| tsymex_rfc0005_s8aw_remainder | PASS 31 OK / 0 FAILED, 44.5s | PASS 31 OK / 0 FAILED, 46.1s |
| tsymex_rfc0005_s8aa_remainder | PASS 24 OK / 0 FAILED, 45.0s | PASS 24 OK / 0 FAILED, 44.3s |
| tsymex_rfc0005_s8i_models | PASS 39 OK / 0 FAILED, 40.6s | PASS 39 OK / 0 FAILED, 39.6s |
| tsymex_rfc0005_s8_scope | PASS 28 OK / 0 FAILED, 36.2s | PASS 28 OK / 0 FAILED, 38.6s |
| tsymex_rfc0005_s8m_exits | PASS 32 OK / 0 FAILED, 42.9s | PASS 32 OK / 0 FAILED, 46.9s |
| tsymex_rfc0005_s8ab_letaudit | PASS 28 OK / 0 FAILED, 57.8s | PASS 28 OK / 0 FAILED, 70.1s |
| tsymex_rectify_effects | PASS 5 OK / 0 FAILED, 46.7s | PASS 5 OK / 0 FAILED, 48.9s |
| tsymex_rfc0005_s9_vetoes | PASS 19 OK / 0 FAILED, 42.0s | PASS 19 OK / 0 FAILED, 49.2s |
| tsymex_phase15_S6b_regex | PASS 5 OK / 0 FAILED, 34.5s | PASS 5 OK / 0 FAILED, 43.3s |
| tsymex_r6_heap_raise_totality | PASS 9 OK / 0 FAILED, 47.1s | PASS 9 OK / 0 FAILED, 38.5s |
| tsymex_r6_n16_closure_zerodefault | PASS 10 OK / 0 FAILED, 43.6s | PASS 10 OK / 0 FAILED, 35.2s |
| tsymex_rfc0005_s7_closure | PASS 37 OK / 0 FAILED, 52.7s | PASS 37 OK / 0 FAILED, 39.7s |
| tsymex_snd1b_closure_uncertain_axiom | PASS 4 OK / 0 FAILED, 50.8s | PASS 4 OK / 0 FAILED, 35.3s |
| tsymex_phase16_R16_5_overflow_thru_closure | PASS 3 OK / 0 FAILED, 30.8s | PASS 3 OK / 0 FAILED, 34.5s |
| tsymex_r6_b1_stringbacked | PASS 7 OK / 0 FAILED, 37.8s | PASS 7 OK / 0 FAILED, 49.2s |
| tsymex_r6_b7r_bytescan | PASS 26 OK / 0 FAILED, 42.3s | PASS 26 OK / 0 FAILED, 39.1s |
| tsymex_r6_lows_collectors | PASS 5 OK / 0 FAILED, 36.1s | PASS 5 OK / 0 FAILED, 32.0s |
| tsymex_r6_n27_placeholder_read_audit | PASS 4 OK / 0 FAILED, 5.4s | PASS 4 OK / 0 FAILED, 6.4s |
| tsymex_r6_r4_collector_scoping | PASS 7 OK / 0 FAILED, 36.3s | PASS 7 OK / 0 FAILED, 35.2s |
| tsymex_rfc0005_s0_exhibit | PASS 10 OK / 0 FAILED, 34.3s | PASS 10 OK / 0 FAILED, 36.8s |
| tsymex_rfc0005_s1c_verdict | PASS 24 OK / 0 FAILED, 41.0s | PASS 24 OK / 0 FAILED, 42.4s |
| tsymex_rfc0005_s1_lattice | PASS 23 OK / 0 FAILED, 31.6s | PASS 23 OK / 0 FAILED, 32.2s |
| tsymex_rfc0005_s6a_budget | PASS 31 OK / 0 FAILED, 35.4s | PASS 31 OK / 0 FAILED, 47.0s |
| tsymex_rfc0005_s6b_ops | PASS 43 OK / 0 FAILED, 56.8s | PASS 43 OK / 0 FAILED, 50.5s |
| tsymex_rfc0005_s8ag_indexsplit | PASS 15 OK / 0 FAILED, 64.6s | PASS 15 OK / 0 FAILED, 61.7s |
| tsymex_rfc0005_s8ap_remainder | PASS 36 OK / 0 FAILED, 72.1s | PASS 36 OK / 0 FAILED, 75.7s |
| tsymex_rfc0005_s8c_resolution | PASS 25 OK / 0 FAILED, 51.3s | PASS 25 OK / 0 FAILED, 46.3s |
| tsymex_rfc0005_s8o_termination | PASS 14 OK / 0 FAILED, 36.4s | PASS 14 OK / 0 FAILED, 36.2s |
| tsymex_phase15_r9_recursive | PASS 3 OK / 0 FAILED, 39.6s | PASS 3 OK / 0 FAILED, 32.2s |
| tsymex_phase15_z3_infra | PASS 11 OK / 0 FAILED, 14.4s | PASS 11 OK / 0 FAILED, 12.2s |
