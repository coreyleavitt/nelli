# S8by -- DONE

- **sha:** 2cb85f545cd153bf3754d3e05d8a9c81eee793bc (branch `rfc-0005-s8by`, pushed). Windows CI ran on 90a33fe; 2cb85f5 only adds to `docs/rfc/`, which the workflows skip.
- **base:** origin/rfc-0005-s8bp at 79037e4 (walker 219).
- **walker:** 219 -> 231 (provisional, kept as instructed). The CR2 `==` pin passes 6/0 on 5.1, 4.13.4 and cpp; `>= 231` is pinned in the S8by suite.

## For the coordinator to decide

1. **`r4_strip` meets the 190 s ceiling only because the host changed.** It ran 140-146 s, but S8bp also meets it here at 147-155 s. The term order saves 4-7% against S8bp, and the slice stays 16-24% above S8bm (114-126 s). If the ceiling meant parity with S8bm, item 3 is not achieved.
2. **`tsymex_configdefaults` is past the 60 s convention and the slice makes it worse.** Windows run time: 98 s at S8bp, 127 and 153 s on this slice's code. `s8ai_semantic` is also over at 60.4 s, down from 94.1 s at S8bp. Both were over before this slice.
3. **Item 2's 607k drop does not survive at the head.** See "Before and after": the drop is 607,363 at cbfef23, but only 79,560 against S8bp at the head, because the term order moves `lastNl`'s search.
4. **A new process-level effect limits what "a function of the query alone" means.** See "Different mechanisms". It also touches S8bm's and S8bp's claims.
5. **Integration needs care at the concolic sites.** A trial merge onto `rfc-0005-soundness-channels` (136ad60) conflicts in 5 files, 4 of the hunks in `runtime.nim` at the scratch solves. I took S8by's call sites. On that base `ownContextCheck` already uses `solveBounded`, and the timeout now comes from `queryTimeoutMsCur`, not `settings.budget.queryTimeoutMs`. Those are the same value only if the run state was reset with the same settings, so please check that when stacking. My resolution is in `s8by-work/trial-merge.diff`.

## Corrections to what I inherited

- **Item 1's RED was false.** The committed pin compared contexts with and without 300 unrelated constants, and its 72,162 vs 72,126 was the process's first solve of the query. Alternating them in the walk's context gives the same spend. I replaced the pin (1751c88).
- **The S8bp suite failed on Windows at every sha from cbfef23 to 6da4370.** symex-mingw shard 0, `tsymex_rfc0005_s8bp_isolation`, "the three walks reached every step": item 2 had removed (1b) and (1c) from its walks. Fixed in 7a26444.
- **The term-order comments overstated it.** They said wall time only and quoted a walk's 478 s vs 712 s. It moves units too, and the whole binary gains 4-7%. Corrected in d6c7cc7, whose commit message has two slips I cannot amend without a force-push: it says 479 s for 478 s and "idle-enough" for a host at load 21-28.
- **The progress note on non-determinism did not reproduce.** It said wide factoring is not deterministic in-process (4,255,870 vs 5,214,991). My repeats at the head gave identical units for each query on one thread history (`raw/cp5-*`, `raw/cp6-51.raw`).

## Design

1. **Concolic scratch solves.** `concreteBranchOutcome`, `concretelyInfeasible` and the concrete-inputs check go through `concreteScratchCheck`: `ownContextSolver` under `concreteBranchRLimit`, with the units added to `ownContextUnits`.
2. **Skip after a facts-first SAT.** (1c) is the facts-first query under a larger budget and (1b) a subset of it, so neither runs. (1c)'s capped half is also skipped when the model makes every root, fact and cap evaluate true. That half can only decline, so a wrong evaluation cannot change a verdict into a false claim.
3. **Term order.** `queryTermOrder` lists the query's terms: roots in order, arguments last to first, children first. `ownContextSolver` translates them as one vector.
4. **`mergeMemberships`.** A membership under a disjunction, `ite` branch, `not` or implication merges with those of the same string that hold where it is read: `x in (A & I)` where asserted, `not (x in (comp(A) & I))` where denied. A literal read both ways is left alone.

## RED and GREEN

Observed by me in this session:

| Item | RED | GREEN |
|---|---|---|
| 1 (new pin, item 1 reverted in an experiment tree) | 5.1: spend 5,854,996 against 876,296 by context shape, and `none(bool)` vs `some(true)` under a 3M bound. 4.13.4: 911,593 against 23,956, same outcome split under 400k (`v/red1e`, 11/1 on both) | 12/0 on both (`v/g1e`) |
| S8bp pin | 4.13.4: 7/1, "seen was {3, plain, factsFirst, 2, 1}" (`v/red-s8bp`) | 9/0 on both (`v/g-s8bp`) |

Inherited from the previous agent's logs, which I read but did not re-run:

| Item | RED | GREEN |
|---|---|---|
| 2 | 5.1: 1b and 1c present, 1,106,184 units (`raw/red-item2-51.log`) | now 12/0 at the head |
| 3 | compile error only, `queryTermOrder` undeclared (`raw/red3-51.raw`). **There is no behavioural RED and no wall-time pin**: the test pins the order itself | now 12/0 at the head |
| 4 | 4.13.4: `sxUnknown` at 8.5M (or) and 10.4M (ite) (`raw/red-item4-413.log`) | now 12/0 at the head |

## Soundness bugs found

None. No false claim was observed in any item. I reviewed the `mergeMemberships` rewrite by reading it and found no wrong polarity, and its SAT witnesses are checked natively in the suite. That review is reading, not proof.

## Before and after

Units, whole walk:

| Build | `lastNl` 5.1 | `lastNl` 4.13.4 | B1-1 5.1 | B1-1 4.13.4 |
|---|---|---|---|---|
| S8bp 79037e4 | 1,106,184 | 1,499,189 | 47,637 | 80,626 |
| skip only, cbfef23 | 498,821 | 786,466 | 47,637 | 80,626 |
| head code, skip disabled | 2,433,310 | 2,356,421 | 47,601 | 80,546 |
| head code | 1,026,624 | 1,219,607 | 47,601 | 80,546 |

Verdicts are unchanged (`sxSat` in every cell).

Walk seconds, wall, Z3 5.1, two walks each, load 21-29: B1-1 0.348 and 0.245 at S8bp, 0.335 and 0.295 at the head; `lastNl` 0.569 and 0.538 at S8bp, 0.462 and 0.408 at the head.

`r4_strip` binary on Z3 5.1, side by side, 12 cores, load 21-28 with other agents running, pause flag absent; wall s (CPU s):

| Pair | S8bm 14d7e81 | S8bp 79037e4 | head code |
|---|---|---|---|
| a | 125.8 (111.6) | | 146.4 (131.1) |
| b | | 154.7 (143.0) | 143.7 (133.2) |
| c | 113.7 (103.3) | | 141.2 (128.0) |
| d | | 146.5 (129.2) | 140.0 (121.5) |

The binaries are from 6da4370 or later; the code diff since then is comments only, apart from the S8by and S8bp test files.

One possible cost of the order, from an inherited log on an earlier tree I did not rebuild: on 5.1, `x * y == 6999433` with `x`, `y` below 200000 was decided in 5,526,707 units (`raw/conc4-51.raw`), and at the head it runs out of 50M (`raw/cp6-51.raw`).

## Suites

Run at 7a26444, except where noted. 7a26444 to 90a33fe changes only comments in `src/`, plus the S8by test file, which was re-run at the final code.

**Final code, `s8by_remainder` and CR2:**

| suite | 5.1 | 4.13.4 | cpp 5.1 |
|---|---|---|---|
| s8by_remainder | 12/0 | 12/0 | 12/0 |
| phase15_CR2_cachekey | 6/0 | 6/0 | |

**The list at 7a26444** (48 suites, 697 tests, ok/failed). The job's named suites plus every `command grep -l concolic tests/` file. `s8by_remainder` is left out here because it changed after this run.

| suite | 5.1 | 4.13.4 | cpp 5.1 |
|---|---|---|---|
| 163audit_w10 | 5/0 | 5/0 |  |
| 163rev_concolic_diagnostics | 25/0 | 25/0 |  |
| 163rev_concolic_flip_width | 13/0 | 13/0 |  |
| 163rev_concolic_modes | 19/0 | 19/0 |  |
| g1b_concolic | 15/0 | 15/0 | 15/0 |
| g2_flip | 8/0 | 8/0 |  |
| g3fix_walkergap | 1/0 | 1/0 |  |
| g4_cmpwalk | 1/0 | 1/0 |  |
| g6_transform_binding | 6/0 | 6/0 |  |
| phase13_rlimit | 1/0 | 1/0 |  |
| phase15_CR2_cachekey | 6/0 | 6/0 | 6/0 |
| phase15_S6b_regex | 5/0 | 5/0 |  |
| r11_range_invariant_audit | 7/0 | 7/0 |  |
| r4_strip | 5/0 | 5/0 |  |
| r6_b1_stringbacked | 7/0 | 7/0 |  |
| r6_n36_raise_class_audit | 14/0 | 14/0 |  |
| s1c_verdict | 24/0 | 24/0 |  |
| s5_str | 35/0 | 35/0 |  |
| s7_closure | 37/0 | 37/0 |  |
| s8ab_letaudit | 28/0 | 28/0 |  |
| s8ar_remainder | 50/0 | 50/0 |  |
| s8ay_remainder | 40/0 | 40/0 |  |
| s8ba_remainder | 32/0 | 32/0 |  |
| s8bm_stability | 4/0 | 4/0 | 4/0 |
| s8bp_isolation | 9/0 | 9/0 | 9/0 |
| s8i_models | 39/0 | 39/0 |  |
| s8j_exits | 45/0 | 45/0 |  |
| s8l_exits | 50/0 | 50/0 |  |
| s8n_precision | 19/0 | 19/0 |  |
| s8o_termination | 14/0 | 14/0 |  |
| tentrypointwiring | 2/0 | 2/0 |  |
| tfuzzcampaignstats | 13/0 | 13/0 |  |
| tfuzzcmplog | 9/0 | 9/0 |  |
| tfuzzcmplogshm | 3/0 | 3/0 |  |
| tfuzzconcolicassist | 4/0 | 4/0 |  |
| tfuzzconcolicbridge | 13/0 | 13/0 |  |
| tfuzzconcolicbridge_g6_affine | 2/0 | 2/0 |  |
| tfuzzconcolicbridge_g6_predicated | 2/0 | 2/0 |  |
| tfuzzconcolicbridge_real | 3/0 | 3/0 |  |
| tfuzzconcolicdegrade | 5/0 | 5/0 |  |
| tfuzzconcolicmismatch | 4/0 | 4/0 |  |
| tfuzzconfigdefaults | 19/0 | 19/0 |  |
| tfuzzi2s | 21/0 | 21/0 |  |
| tfuzzpackaging | 8/0 | 8/0 |  |
| tfuzzprocessisolation | 6/0 | 6/0 |  |
| tfuzzwinjoblimits | 0/0 | 0/0 |  |
| tfuzzwinshm | 7/0 | 7/0 |  |

**`s8bj_*` and `s8bb_*` are not on this base.** I ran them on the uncommitted trial merge with 136ad60 in `wt/s8by-noi2`, walker left at 237, using the S8by test file as of 7a26444:

| suite | 5.1 | 4.13.4 |
|---|---|---|
| phase15_CR2_cachekey | 6/0 | 6/0 |
| s8bb_captures | 13/0 | 13/0 |
| s8bb_capvalues | 1/0 | 1/0 |
| s8bb_capvalues_lf | 1/0 | 1/0 |
| s8bb_capvalues_plus | 1/0 | 1/0 |
| s8bb_constructs | 7/0 | 7/0 |
| s8bb_exhaustive | 2/0 | 2/0 |
| s8bb_remainder | 21/0 | 21/0 |
| s8bb_replace | 7/0 | 7/0 |
| s8bb_selection | 4/0 | 4/0 |
| s8bj_entries | 1/0 | 1/0 |
| s8bj_entries_multiline | 1/0 | 1/0 |
| s8bj_entries_utf | 1/0 | 1/0 |
| s8bj_entries_utf_b | 1/0 | 1/0 |
| s8bj_entries_utf_c | 1/0 | 1/0 |
| s8bj_langs | 2/0 | 2/0 |
| s8bj_langs_b | 2/0 | 2/0 |
| s8bj_replace | 2/0 | 2/0 |
| s8bj_replace_lemmas | 5/0 | 5/0 |
| s8bj_startopt | 3/0 | 3/0 |
| s8bj_syntax | 4/0 | 4/0 |
| s8bj_verbs | 2/0 | 2/0 |
| s8bj_walker | 11/0 | 11/0 |
| s8bp_isolation | 9/0 | 9/0 |
| s8by_remainder | 12/0 | 12/0 |

**Not run:** the rest of the `tsymex_*` corpus on Linux. Windows `symex-mingw` ran it on 4.13.4 and passed. It has not been run on 5.1 at this slice, and the term order can move any query's model.

## Windows CI

| leg | sha | run id | result |
|---|---|---|---|
| symex-mingw | 90a33fe | 41424831915 | success |
| fuzzer-mingw | 90a33fe | 41424831874 | success |
| fuzzer-msvc | 90a33fe | 41424831908 | success |
| symex-mingw | 7a26444 | 41410310683 | success |
| fuzzer-mingw | 7a26444 | 41410310790 | success |
| fuzzer-msvc | 7a26444 | 41410310718 | success |

Earlier symex-mingw runs failed on the S8bp pin above: 37164716372, 37175138852, 37179609247, 37183503171.

Shard times at 90a33fe (budget 40 min): 26.8, 30.8, 31.3, 23.6, 29.5, 30.8, 22.6, 29.3 min.

## Different mechanisms, reported and not fixed here (also in the RFC's "As landed (S8by)")

- **PRECISION: a fresh thread's spend on a query follows what earlier threads of the process ran,** in a context of its own too. On Z3 5.1, one factoring branch solve took 72,124 units on non-main threads until a thread ran it beside 3,000 unrelated constants, then 5,854,994 on that thread and every later one, whatever its context held (`raw/cpa1.txt`). The main thread stayed at 72,124 through the same sequence, and `lastNl`'s walk on it stayed at 1,026,624 (`raw/cpa0.txt`, `raw/cpa1.txt`). 4.13.4 moves similarly, 26,695 to 911,593 (`raw/cp7h413.txt`). Cause not identified. I marked this PRECISION because a bound that runs out gives an undecided result, not a claim, but the first S8by pin was fooled by it, and the S8bm and S8bp units claims hold only within one such history.
- **PRECISION: Z3 5.1 prints an internal check on wide factoring:** `Failed to verify: m_cache.mk_unique(p) == p`, with a request to file an issue. Seen with `x`, `y` below 200000 for two of the three products tried. The solve continues and runs out of 50M; 4.13.4 decides the first of those queries in 191,361 units.
- **PRECISION: `r4_strip` stays above S8bm.** The order closes about a quarter of S8bp's gap.
- **PRECISION: `tsymex_configdefaults` runs longer.** On Linux side by side (4.13.4, CPU s): 31 and 32 at S8bp against 38 and 40 at the head; 25 and 29 with the skip alone against 32 and 36 at the head in that pair. So the rise comes after the skip. I did not attribute it further.

## Tree state

- `wt/s8by` is clean at 2cb85f5, and the branch is pushed. The commits since 6da4370 are not squashed, since no force-push is allowed; earlier ones carry `wip` prefixes.
- `wt/s8by-noi2`: mid-merge and uncommitted, detached at 136ad60. Do not commit from it.
- `wt/s8by-exp`: detached at 7a26444, with item 1 reverted in `runtime.nim` and the 1751c88 test file copied in. Its earlier toggles are saved in `s8by-work/exp.diff`. `s8by-noi2`'s are in `s8by-work/noi2.diff`.
- `merge.autostash` and `rerere` are on in this clone. The trial merge recorded rerere preimages in the shared repo, and no autostash entry was created.
- Logs: `s8by-work/v/<tag>/`, `raw/`, `ci/`. Windows times as TSV: `s8by-work/s8by-win-times.tsv`.

## Per-file Windows times (symex-mingw 41424831915, 90a33fe, c, Z3 4.13.4)

`run` is the log's `wall=` for the test itself; `total` is from the `==>` line to the `<==` line, so it includes compiling. Every suite below has rc=0. **Over 60 s by run:** `tsymex_configdefaults` 153.0, `tsymex_rfc0005_s8ai_semantic` 60.4. **Over 60 s by total:** 16 files.

Largest rises in run time from S8bp's run 37126510248, shown as S8bp / 7a26444 / 90a33fe: `configdefaults` 98.4 / 127.5 / 153.0; `163rev_degrade_classification` 30.4 / 45.6 / 45.3; `s8ax_remainder` 37.6 / 42.8 / 46.8; `s8ae_remainder` 36.6 / 34.5 / 42.8; `r1_draingap` 9.6 / 15.0 / 15.1; `s8y_budget_decline` 9.2 / 13.2 / 13.2. Same-code runs can differ by about 20% (`configdefaults` 127.5 vs 153.0). All 421 corpus files together: 808.5 s at S8bp, 847.1 and 879.8 s here.

The 9 `scan-tail` suites do not print these lines, so these are whole-job times, setup included, in minutes: nulwitness 1, b7r2_pathscope 1.4, a6r_callwitness 1, g8_multi_param 2.2, b6_optionregion 1.9, g10_smoke 1, b7r_bytescan 1.4, b5_chained 1, bug2_scopeddecline 1.

| suite | shard | run s | total s |
|---|---|---|---|
| tsymex_configdefaults | 5 | 153.0 | 188 |
| tsymex_rfc0005_s8ai_semantic | 3 | 60.4 | 86 |
| tsymex_rfc0005_s8s_precision | 2 | 57.0 | 120 |
| tsymex_rfc0005_s8ax_remainder | 0 | 46.8 | 127 |
| tsymex_163rev_degrade_classification | 7 | 45.3 | 77 |
| tsymex_rfc0005_s8ae_remainder | 1 | 42.8 | 76 |
| tsymex_rfc0005_s8ay_remainder | 1 | 24.9 | 98 |
| tsymex_rfc0005_s8ag_indexsplit | 2 | 23.1 | 55 |
| tsymex_r6_n36_raise_degrade | 7 | 20.4 | 53 |
| tsymex_retest_c6_tuple_chain | 2 | 19.1 | 48 |
| tsymex_r1_draingap | 3 | 15.1 | 43 |
| tsymex_rfc0005_s8y_budget_decline | 1 | 13.2 | 45 |
| tsymex_rfc0005_s8as_remainder | 3 | 11.8 | 60 |
| tsymex_rfc0005_s1c_verdict | 4 | 10.5 | 44 |
| tsymex_rfc0005_s8w_remainder | 6 | 10.3 | 41 |
| tsymex_r14_case2_degrade | 5 | 10.3 | 40 |
| tsymex_rfc0005_s8au_remainder | 5 | 10.0 | 63 |
| tsymex_rfc0005_s8t_termination | 3 | 9.5 | 41 |
| tsymex_r4_strip | 3 | 9.2 | 35 |
| tsymex_phase15_A1_loopguard | 2 | 9.1 | 41 |
| tsymex_rfc0005_s8ar_remainder | 2 | 8.9 | 110 |
| tsymex_retest_c5b_unknown_errors | 1 | 8.6 | 39 |
| tsymex_snd3_loopdegrade | 0 | 7.3 | 36 |
| tsymex_g2_flip | 7 | 7.2 | 41 |
| tsymex_rfc0005_s8p_precision | 7 | 7.1 | 61 |
| tsymex_r6_n21_pairloop_member | 0 | 7.1 | 40 |
| tsymex_rfc0005_s8ad_remainder | 0 | 7.0 | 43 |
| tsymex_rfc0005_s8aw_remainder | 7 | 6.3 | 49 |
| tsymex_phase6_break | 4 | 5.4 | 36 |
| tsymex_rfc0005_s8an_remainder | 6 | 5.3 | 65 |
| tsymex_phase15_C4_hof | 7 | 5.3 | 38 |
| tsymex_rfc0005_s8aa_remainder | 5 | 5.0 | 50 |
| tsymex_rfc0005_s8bp_isolation | 0 | 5.0 | 36 |
| tsymex_phase15_N2_kindgate_audit | 3 | 5.0 | 8 |
| tsymex_rfc0005_s8z_remainder | 2 | 4.6 | 85 |
| tsymex_rfc0005_s8ba_remainder | 4 | 4.6 | 65 |
| tsymex_rfc0005_s8ac_remainder | 7 | 4.6 | 59 |
| tsymex_rfc0005_s8at_remainder | 4 | 4.3 | 109 |
| tsymex_rfc0005_s8ap_remainder | 0 | 4.3 | 65 |
| tsymex_rfc0005_s8by_remainder | 1 | 4.3 | 39 |
| tsymex_phase3_recursion | 1 | 4.3 | 36 |
| tsymex_phase15_A1_arithmetic | 4 | 4.3 | 35 |
| tsymex_rfc0005_s8aj_remainder | 4 | 4.1 | 56 |
| tsymex_rfc0005_s8k_bounds | 2 | 4.1 | 40 |
| tsymex_rfc0005_s3_monotonicity | 6 | 3.8 | 35 |
| tsymex_rfc0005_s8m_exits | 4 | 3.6 | 55 |
| tsymex_r14_continue_guard | 6 | 3.6 | 30 |
| tsymex_r6_r5_pairloop_counter | 3 | 3.4 | 29 |
| tsymex_r6_a4_construct_interactions | 5 | 3.1 | 36 |
| tsymex_rfc0005_s8bd_remainder | 5 | 3.0 | 57 |
| tsymex_q1_scanlift | 1 | 3.0 | 38 |
| tsymex_phase15_F7_float_extract | 6 | 2.6 | 27 |
| tsymex_rfc0005_s11_surface | 2 | 2.5 | 55 |
| tsymex_r1b_shortcircuit_oob | 7 | 2.4 | 39 |
| tsymex_rfc0005_s6a_budget | 1 | 2.4 | 38 |
| tsymex_r6_b1_stringbacked | 0 | 2.4 | 31 |
| tsymex_rfc0005_s5_str | 0 | 2.2 | 39 |
| tsymex_rfc0005_s8l_exits | 3 | 2.0 | 46 |
| tsymex_rfc0005_s8am_remainder | 5 | 1.8 | 47 |
| tsymex_rfc0005_s8u_precision | 4 | 1.7 | 57 |
| tsymex_rfc0005_s8_scope | 4 | 1.7 | 41 |
| tsymex_rfc0005_s7_closure | 3 | 1.6 | 32 |
| tsymex_161_overflow_obligation | 0 | 1.5 | 38 |
| tsymex_a3_closure_iterators | 5 | 1.5 | 35 |
| tsymex_r6_b4_readcstring | 3 | 1.5 | 28 |
| tsymex_rfc0005_s8n_precision | 5 | 1.4 | 42 |
| tsymex_rfc0005_s8i_models | 0 | 1.4 | 38 |
| tsymex_r6_n37_raise_residue | 0 | 1.4 | 32 |
| tsymex_r2_scanbound | 0 | 1.4 | 29 |
| tsymex_rfc0005_s4_alloc | 7 | 1.3 | 34 |
| tsymex_rfc0005_s8f_witness | 5 | 1.2 | 45 |
| tsymex_r6_r2_zerodefault_result | 0 | 1.2 | 37 |
| tsymex_phase15_F8_smoke | 7 | 1.1 | 41 |
| tsymex_rfc0005_s8g_models | 6 | 1.1 | 33 |
| tsymex_rfc0005_s8v_termination | 5 | 1.1 | 31 |
| tsymex_phase7_assertcovered | 0 | 1.0 | 41 |
| tsymex_rfc0005_s6b_ops | 2 | 1.0 | 40 |
| tsymex_a7_rune | 7 | 1.0 | 37 |
| tsymex_phase15_A1_callarg | 0 | 1.0 | 34 |
| tsymex_r6_r4_collector_scoping | 2 | 1.0 | 34 |
| tsymex_rfc0005_s8bm_stability | 7 | 1.0 | 31 |
| tsymex_r6_n10_coverage_matrix | 3 | 1.0 | 30 |
| tsymex_rfc0005_s8bf_alias | 6 | 0.9 | 37 |
| tsymex_r6_b3_scanpair | 2 | 0.9 | 32 |
| tsymex_r6_n20_boundedloop | 7 | 0.9 | 32 |
| tsymex_augmented_assign | 3 | 0.9 | 28 |
| tsymex_rfc0005_s8e_scoping | 4 | 0.8 | 50 |
| tsymex_rfc0005_s8j_exits | 1 | 0.8 | 40 |
| tsymex_r6_n14_seqops | 5 | 0.8 | 40 |
| tsymex_phase15_F6_float_math | 5 | 0.8 | 37 |
| tsymex_r6_lows_collectors | 1 | 0.8 | 35 |
| tsymex_r6_r3_svint_overflow | 1 | 0.8 | 34 |
| tsymex_m6_probeproto_strproto | 2 | 0.8 | 34 |
| tsymex_163rev_assign_sites | 3 | 0.8 | 34 |
| tsymex_phase15_A2a_atomicir_audit | 4 | 0.8 | 33 |
| tsymex_rfc0005_s8q_termination | 0 | 0.8 | 30 |
| tsymex_rfc0005_s1b_kinds | 3 | 0.8 | 27 |
| tsymex_phase6_for | 6 | 0.8 | 24 |
| tsymex_rfc0005_s10_replay_verdict | 1 | 0.7 | 42 |
| tsymex_phase15_rereview_drains | 7 | 0.7 | 38 |
| tsymex_phase15_A1_boolean | 7 | 0.7 | 35 |
| tsymex_163rev_intoffset_range | 2 | 0.7 | 32 |
| tsymex_phase15_N3_scan_boundary | 4 | 0.7 | 32 |
| tsymex_163rev_frontier_default | 6 | 0.7 | 25 |
| tsymex_rfc0005_s8c_resolution | 2 | 0.6 | 41 |
| tsymex_163rev_concolic_diagnostics | 4 | 0.6 | 36 |
| tsymex_g1b_concolic | 6 | 0.6 | 31 |
| tsymex_snd3_6_equality_loop | 7 | 0.6 | 30 |
| tsymex_rfc0005_s8b_substitutions | 3 | 0.6 | 28 |
| tsymex_163rev_scan_counter_range | 6 | 0.6 | 27 |
| tsymex_rfc0005_s8h_refwitness | 7 | 0.5 | 42 |
| tsymex_p2b_refobjconstr_expr | 5 | 0.5 | 37 |
| tsymex_r6_r1_placeholder_totality | 7 | 0.5 | 36 |
| tsymex_r6_a3_variantconstruct_sym | 4 | 0.5 | 35 |
| tsymex_phase15_cr9_lowerInExpr | 2 | 0.5 | 34 |
| tsymex_163audit_w9 | 6 | 0.5 | 33 |
| tsymex_r5_bv32_width | 4 | 0.5 | 32 |
| tsymex_r4_slice_binding | 2 | 0.5 | 32 |
| tsymex_phase15_A2b_bitwise | 0 | 0.5 | 28 |
| tsymex_r6_n42_deref_taint | 3 | 0.5 | 28 |
| tsymex_phase15_A1_bitwise | 6 | 0.5 | 26 |
| tsymex_rfc0005_s8o_termination | 6 | 0.5 | 25 |
| tsymex_phase15_C1_canonical_kind | 1 | 0.4 | 44 |
| tsymex_162_range_base_width | 1 | 0.4 | 43 |
| tsymex_h_verification | 7 | 0.4 | 37 |
| tsymex_rfc0005_s8aq_remainder | 1 | 0.4 | 37 |
| tsymex_phase15_A1_assertarg | 5 | 0.4 | 36 |
| tsymex_r6_b2_intwidth | 1 | 0.4 | 35 |
| tsymex_r6_n39_variant_field_alloc | 1 | 0.4 | 35 |
| tsymex_r6_lows_declines | 2 | 0.4 | 35 |
| tsymex_r4_seq_slice | 1 | 0.4 | 35 |
| tsymex_r6_itesv_mergedegrade | 7 | 0.4 | 34 |
| tsymex_phase16_CR1a_bitwise_svint | 4 | 0.4 | 34 |
| tsymex_phase15_A1_comparison | 1 | 0.4 | 34 |
| tsymex_rfc0005_s9_vetoes | 3 | 0.4 | 31 |
| tsymex_h_witness | 0 | 0.4 | 31 |
| tsymex_g1a_mode | 5 | 0.4 | 31 |
| tsymex_phase16_R16_4_overflow | 0 | 0.4 | 31 |
| tsymex_phase15_M2_parsebiggestint | 0 | 0.4 | 30 |
| tsymex_phase6_while | 7 | 0.4 | 30 |
| tsymex_retest_c3_bitwise_guard | 0 | 0.4 | 29 |
| tsymex_phase15_A1_unary | 3 | 0.4 | 27 |
| tsymex_163rev_concolic_modes | 6 | 0.4 | 27 |
| tsymex_phase15_CR3_CR4_CR6_float | 1 | 0.3 | 39 |
| tsymex_phase15_C6_smoke | 1 | 0.3 | 39 |
| tsymex_163audit_w10 | 5 | 0.3 | 39 |
| tsymex_tot1_totality_corpus | 2 | 0.3 | 38 |
| tsymex_rfc0005_s8ao_remainder | 7 | 0.3 | 36 |
| tsymex_163rev_enum_positions | 4 | 0.3 | 36 |
| tsymex_phase15_A2a_guardcond_pin | 7 | 0.3 | 36 |
| tsymex_163rev_concolic_flip_width | 5 | 0.3 | 35 |
| tsymex_phase15_N0_kindgate_widen | 1 | 0.3 | 35 |
| tsymex_h_containers | 4 | 0.3 | 34 |
| tsymex_phase15_M1_seq_fixedwidth | 7 | 0.3 | 34 |
| tsymex_phase11_walker | 4 | 0.3 | 34 |
| tsymex_cr9c_intrep | 2 | 0.3 | 34 |
| tsymex_phase15_F3_float_arith | 0 | 0.3 | 33 |
| tsymex_r6_n49_dottedfield_mutation | 5 | 0.3 | 32 |
| tsymex_a2_refvariant_fields | 4 | 0.3 | 32 |
| tsymex_r6_n31_block_counter | 5 | 0.3 | 32 |
| tsymex_phase16_CR1b_tail_local | 5 | 0.3 | 30 |
| tsymex_phase14_frontier_pruning | 2 | 0.3 | 30 |
| tsymex_phase15_r11b_smoke | 0 | 0.3 | 30 |
| tsymex_r6_b0_scanlift_bound | 7 | 0.3 | 30 |
| tsymex_retest_c11_stack | 7 | 0.3 | 30 |
| tsymex_phase15_r4_deref_write | 0 | 0.3 | 29 |
| tsymex_phase16_D1c_shortcircuit | 0 | 0.3 | 29 |
| tsymex_163rev_inert_exclusions | 0 | 0.3 | 29 |
| tsymex_phase15_CR21_parseintraise_arg | 0 | 0.3 | 29 |
| tsymex_phase15_S7b_smoke | 3 | 0.3 | 27 |
| tsymex_cr22_label_assert_coexist | 6 | 0.3 | 27 |
| tsymex_r6_a2_retbind_variant | 3 | 0.3 | 26 |
| tsymex_rfc0005_s1_lattice | 0 | 0.3 | 26 |
| tsymex_phase15_F5_probeproto | 3 | 0.3 | 26 |
| tsymex_phase16_R16_2b_shortcircuit_conv | 6 | 0.3 | 25 |
| tsymex_r6_n28_shadow_collision | 3 | 0.3 | 24 |
| tsymex_r11_range_invariant_audit | 4 | 0.3 | 4 |
| tsymex_phase15_A2a_chokepoint_audit | 6 | 0.3 | 3 |
| tsymex_r6_n36_raise_class_audit | 6 | 0.3 | 3 |
| tsymex_163_opaque_transparent | 2 | 0.2 | 48 |
| tsymex_rfc0005_s2_replay | 5 | 0.2 | 40 |
| tsymex_CR2c_witnessreader_catchall | 1 | 0.2 | 39 |
| tsymex_163rev_int_literal_width | 1 | 0.2 | 38 |
| tsymex_163audit_range_elem | 4 | 0.2 | 38 |
| tsymex_phase15_CR1_CR5_closure_heap | 2 | 0.2 | 37 |
| tsymex_163audit_wave2 | 7 | 0.2 | 36 |
| tsymex_phase15_E7_smoke | 4 | 0.2 | 36 |
| tsymex_r6_n43_parity | 4 | 0.2 | 35 |
| tsymex_phase15_A2a_atomize | 5 | 0.2 | 35 |
| tsymex_p2a_objconstr_expr | 4 | 0.2 | 35 |
| tsymex_163rev_enum_domain | 1 | 0.2 | 34 |
| tsymex_phase16_R16_2_rangedefect | 5 | 0.2 | 34 |
| tsymex_phase15_S2_strlit | 4 | 0.2 | 34 |
| tsymex_CR2a_expr_catchall | 7 | 0.2 | 34 |
| tsymex_phase15_S6b_regex | 1 | 0.2 | 33 |
| tsymex_r6_n29_seqlit_sortmismatch | 4 | 0.2 | 33 |
| tsymex_phase16_m3_rfind | 1 | 0.2 | 33 |
| tsymex_163rev_enum_field_witness | 2 | 0.2 | 33 |
| tsymex_phase15_S8_concat | 4 | 0.2 | 33 |
| tsymex_phase15_S5_strops | 7 | 0.2 | 33 |
| tsymex_phase12_witnesses | 7 | 0.2 | 33 |
| tsymex_r6_a1_variantlit | 2 | 0.2 | 33 |
| tsymex_rfc0005_s0_exhibit | 7 | 0.2 | 33 |
| tsymex_r6_n40_alloc_totality | 2 | 0.2 | 33 |
| tsymex_phase15_S3_strindex | 5 | 0.2 | 32 |
| tsymex_r6_n13_reassign_seqarm | 4 | 0.2 | 32 |
| tsymex_phase16_m4_str_add_ampeq | 2 | 0.2 | 32 |
| tsymex_uninit_var | 4 | 0.2 | 32 |
| tsymex_phase15_F9a_array_float | 0 | 0.2 | 32 |
| tsymex_phase16_R16_3_divzero | 7 | 0.2 | 32 |
| tsymex_163rev_assign_rangedefect | 1 | 0.2 | 32 |
| tsymex_phase15_S10a_strconv | 1 | 0.2 | 32 |
| tsymex_163rev_assign_scope | 2 | 0.2 | 32 |
| tsymex_phase16_R16_5_overflow_thru_closure | 1 | 0.2 | 32 |
| tsymex_phase15_r7_alias_chain | 3 | 0.2 | 32 |
| tsymex_phase15_S9_caseconv | 5 | 0.2 | 32 |
| tsymex_163rev_inert_argfork | 7 | 0.2 | 32 |
| tsymex_163audit_range_domain | 3 | 0.2 | 32 |
| tsymex_r7_caseexpr | 5 | 0.2 | 31 |
| tsymex_phase15_S7a_bytes | 2 | 0.2 | 31 |
| tsymex_rfc0005_s8w2_hotfix | 7 | 0.2 | 31 |
| tsymex_a9_casefold | 2 | 0.2 | 31 |
| tsymex_phase15_g5_distinct_borrow | 0 | 0.2 | 31 |
| tsymex_phase5_seq | 2 | 0.2 | 30 |
| tsymex_snd4_strindex_oob | 1 | 0.2 | 30 |
| tsymex_r5_neg_bool_conv | 7 | 0.2 | 30 |
| tsymex_rfc0005_s8r_theoryfree | 1 | 0.2 | 30 |
| tsymex_r6_lows_blockparse | 0 | 0.2 | 29 |
| tsymex_phase15_C5_closure_eq | 0 | 0.2 | 29 |
| tsymex_a7_runes_iter | 0 | 0.2 | 29 |
| tsymex_phase1_arith | 6 | 0.2 | 29 |
| tsymex_163rev_table_elem | 0 | 0.2 | 29 |
| tsymex_rfc0005_s8d_typeheads | 3 | 0.2 | 28 |
| tsymex_163rev_armfield_write | 0 | 0.2 | 28 |
| tsymex_phase16_m5_ifexpr_minmax | 3 | 0.2 | 28 |
| tsymex_phase16_A5_float_classify | 3 | 0.2 | 28 |
| tsymex_r5_tuple_return | 0 | 0.2 | 28 |
| tsymex_h_stepC_heapidentity | 6 | 0.2 | 27 |
| tsymex_163rev_enum_ordinal | 3 | 0.2 | 27 |
| tsymex_phase15_fieldcontainer | 3 | 0.2 | 26 |
| tsymex_rectify_mutation | 3 | 0.2 | 26 |
| tsymex_p1_tupleconstr_expr | 3 | 0.2 | 26 |
| tsymex_rfc0005_s8av_remainder | 6 | 0.2 | 26 |
| tsymex_phase15_S4_strpred | 6 | 0.2 | 26 |
| tsymex_163rev_variant_armfield | 3 | 0.2 | 26 |
| tsymex_retest_char_needle | 3 | 0.2 | 25 |
| tsymex_r6_heap_raise_totality | 6 | 0.2 | 25 |
| tsymex_g6_transform_binding | 3 | 0.2 | 25 |
| tsymex_r6_n16_closure_zerodefault | 6 | 0.2 | 25 |
| tsymex_r6_n9_variant_budget | 6 | 0.2 | 24 |
| tsymex_discard_raise | 3 | 0.2 | 24 |
| tsymex_r5_discard | 6 | 0.2 | 23 |
| tsymex_r6_n27_placeholder_read_audit | 2 | 0.2 | 3 |
| tsymex_phase13_layer1_wire | 1 | 0.1 | 37 |
| tsymex_phase15_F5hang_derefwrite | 4 | 0.1 | 35 |
| tsymex_r6_n27_hof_placeholder | 1 | 0.1 | 35 |
| tsymex_a8_radix | 1 | 0.1 | 34 |
| tsymex_phase1_let | 2 | 0.1 | 34 |
| tsymex_r6_a0_lowhigh | 1 | 0.1 | 34 |
| tsymex_phase15_r10_budget | 6 | 0.1 | 34 |
| tsymex_163rev_transparent_guard | 1 | 0.1 | 34 |
| tsymex_phase14_b67_label_filter | 4 | 0.1 | 33 |
| tsymex_phase14_nonenum_disc | 7 | 0.1 | 33 |
| tsymex_phase15_F1_typebridge | 6 | 0.1 | 33 |
| tsymex_phase15_r12_bumps | 1 | 0.1 | 33 |
| tsymex_phase15_E3_try | 7 | 0.1 | 33 |
| tsymex_163rev_range_bounds | 5 | 0.1 | 33 |
| tsymex_phase15_r5_nil | 1 | 0.1 | 33 |
| tsymex_phase15_r11_unsafecast | 7 | 0.1 | 33 |
| tsymex_phase2_bv_arith | 4 | 0.1 | 33 |
| tsymex_phase15_r8_ptr | 4 | 0.1 | 32 |
| tsymex_phase14_symbolic_disc_reassign | 1 | 0.1 | 32 |
| tsymex_phase12_derandomize | 5 | 0.1 | 32 |
| tsymex_r6_d2_recursive_budget | 4 | 0.1 | 32 |
| tsymex_g4_cmpwalk | 1 | 0.1 | 32 |
| tsymex_163rev_parser_gaps | 4 | 0.1 | 32 |
| tsymex_rfc0005_s8az_remainder | 2 | 0.1 | 32 |
| tsymex_rectify_effects | 1 | 0.1 | 32 |
| tsymex_snd1_uncertain_taint | 4 | 0.1 | 32 |
| tsymex_phase14_else_arms | 1 | 0.1 | 32 |
| tsymex_phase4_array | 4 | 0.1 | 32 |
| tsymex_phase15_G1a_instkey | 4 | 0.1 | 32 |
| tsymex_phase15_S10b_strconv | 2 | 0.1 | 31 |
| tsymex_163rev_enum_valueshapes | 5 | 0.1 | 31 |
| tsymex_inv_structured_kinds | 1 | 0.1 | 31 |
| tsymex_phase14_multivariant_walker | 5 | 0.1 | 31 |
| tsymex_phase15_R1a_ir | 4 | 0.1 | 31 |
| tsymex_phase15_F2_float_literals | 7 | 0.1 | 31 |
| tsymex_phase3_inline | 7 | 0.1 | 31 |
| tsymex_phase15_C1_ir | 2 | 0.1 | 31 |
| tsymex_phase15_E1_ir | 4 | 0.1 | 31 |
| tsymex_phase15_S11_mutation | 3 | 0.1 | 31 |
| tsymex_phase15_r6_refobj | 2 | 0.1 | 31 |
| tsymex_phase15_F4_float_compare | 1 | 0.1 | 31 |
| tsymex_phase15_z4_walkctx | 2 | 0.1 | 31 |
| tsymex_phase15_z3c_classify | 1 | 0.1 | 31 |
| tsymex_phase15_E8_getcurrentexn | 5 | 0.1 | 31 |
| tsymex_phase15_r3_deref_read | 7 | 0.1 | 31 |
| tsymex_phase15_g6_concept_constraint | 1 | 0.1 | 31 |
| tsymex_phase15_g4_distinct_sort | 7 | 0.1 | 31 |
| tsymex_phase4_tuple | 7 | 0.1 | 31 |
| tsymex_phase6_case | 5 | 0.1 | 31 |
| tsymex_phase15_F5_float_conv | 2 | 0.1 | 31 |
| tsymex_phase15_CR11_CR18_splitcap | 4 | 0.1 | 31 |
| tsymex_phase15_C2b_closure_call | 5 | 0.1 | 31 |
| tsymex_phase15_F9b_seq_float | 1 | 0.1 | 31 |
| tsymex_rectify_nested_arrays | 4 | 0.1 | 30 |
| tsymex_phase15_r1_refsort | 5 | 0.1 | 30 |
| tsymex_snd1b_closure_uncertain_axiom | 5 | 0.1 | 30 |
| tsymex_phase15_l1_boundary | 4 | 0.1 | 30 |
| tsymex_163rev_seqelem_promoted_int | 7 | 0.1 | 30 |
| tsymex_phase15_l2_untyped_template | 5 | 0.1 | 30 |
| tsymex_phase15_F9c_variant_float | 2 | 0.1 | 30 |
| tsymex_q1_sibling_collision | 2 | 0.1 | 30 |
| tsymex_phase15_G1c_instcap | 5 | 0.1 | 30 |
| tsymex_163rev_transparent_result | 2 | 0.1 | 30 |
| tsymex_phase15_E5_finally | 2 | 0.1 | 30 |
| tsymex_phase15_E4a_userexn | 1 | 0.1 | 30 |
| tsymex_phase15_r1b_callheap | 5 | 0.1 | 30 |
| tsymex_phase2_fallback | 5 | 0.1 | 30 |
| tsymex_rectify_abstraction | 7 | 0.1 | 30 |
| tsymex_phase15_g7_static_param | 2 | 0.1 | 30 |
| tsymex_phase15_r8b_varref | 5 | 0.1 | 30 |
| tsymex_phase14_c4_z3error | 7 | 0.1 | 30 |
| tsymex_rectify_refs | 5 | 0.1 | 30 |
| tsymex_r5_const_fold | 5 | 0.1 | 30 |
| tsymex_phase15_N1_resolution_gates | 2 | 0.1 | 30 |
| tsymex_phase1_assert | 7 | 0.1 | 30 |
| tsymex_phase4_nested | 5 | 0.1 | 30 |
| tsymex_phase16_R16_6_diagnostics_channel | 2 | 0.1 | 29 |
| tsymex_funcdef_callee | 4 | 0.1 | 29 |
| tsymex_phase14_var_param | 2 | 0.1 | 29 |
| tsymex_rectify_generics | 2 | 0.1 | 29 |
| tsymex_phase16_D1a_defect_routeraise | 7 | 0.1 | 29 |
| tsymex_phase15_r13_closure_ref | 2 | 0.1 | 29 |
| tsymex_phase14_multivariant_witness | 6 | 0.1 | 28 |
| tsymex_CR2b_paramtype_catchall | 0 | 0.1 | 28 |
| tsymex_phase12_sugar | 6 | 0.1 | 28 |
| tsymex_phase3_mutual | 0 | 0.1 | 28 |
| tsymex_g3fix_walkergap | 0 | 0.1 | 28 |
| tsymex_phase15_E4_hierarchy | 0 | 0.1 | 28 |
| tsymex_rectify_cardinality | 0 | 0.1 | 28 |
| tsymex_phase15_l3_quote_do | 6 | 0.1 | 27 |
| tsymex_phase14_disc_promotion | 0 | 0.1 | 27 |
| tsymex_phase15_S1_typebridge | 0 | 0.1 | 27 |
| tsymex_phase1_bool | 0 | 0.1 | 27 |
| tsymex_phase5_hashset | 0 | 0.1 | 27 |
| tsymex_phase14_arm_field_zero_init | 0 | 0.1 | 27 |
| tsymex_a6_symlen_hof | 6 | 0.1 | 27 |
| tsymex_phase15_C3_proc_as_value | 6 | 0.1 | 26 |
| tsymex_phase2_abstraction | 3 | 0.1 | 26 |
| tsymex_phase15_CR15_enum_ordinal | 6 | 0.1 | 26 |
| tsymex_phase14_var_param_downstream | 3 | 0.1 | 25 |
| tsymex_phase5_table | 3 | 0.1 | 25 |
| tsymex_phase15_E2b_raise | 6 | 0.1 | 25 |
| tsymex_163rev_nested_clamp | 3 | 0.1 | 25 |
| tsymex_phase3_summarization | 3 | 0.1 | 25 |
| tsymex_snd2_assume | 6 | 0.1 | 24 |
| tsymex_phase15_r13_ptr_finally | 3 | 0.1 | 24 |
| tsymex_phase15_r9_recursive | 6 | 0.1 | 24 |
| tsymex_r6_a6_exported_field_names | 6 | 0.1 | 24 |
| tsymex_phase2_overflow | 6 | 0.1 | 24 |
| tsymex_phase15_r2_new | 6 | 0.1 | 24 |
| tsymex_phase15_E6_defect | 3 | 0.1 | 24 |
| tsymex_phase15_g3_type_subst | 6 | 0.1 | 24 |
| tsymex_phase15_C2_staticparams | 3 | 0.1 | 24 |
| tsymex_retest_pred_succ | 6 | 0.1 | 23 |
| tsymex_phase15_E_roundtrip | 3 | 0.1 | 23 |
| tsymex_r8_omitted_field_degrade | 6 | 0.1 | 23 |
| tsymex_rectify_variants | 6 | 0.1 | 23 |
| tsymex_phase11_fielddefect | 3 | 0.1 | 23 |
| tsymex_phase13_rlimit | 3 | 0.1 | 23 |
| tsymex_phase4_oob | 6 | 0.1 | 22 |
| tsymex_r6_degrade_pairing_audit | 5 | 0.1 | 3 |
| tsymex_rfc0005_s8ab_letaudit | 6 | 0.0 | 66 |
| tsymex_phase14_c1_fromcache | 5 | 0.0 | 30 |
| tsymex_retest_defect_net | 4 | 0.0 | 30 |
| tsymex_phase15_E2a_cascade | 5 | 0.0 | 30 |
| tsymex_retest_infix_degrade | 5 | 0.0 | 29 |
| tsymex_phase15_CR14_exn_missing | 5 | 0.0 | 29 |
| tsymex_phase15_C2a_closure_capture | 4 | 0.0 | 27 |
| tsymex_phase16_CR1c_internal_fault | 6 | 0.0 | 23 |
| tsymex_phase13_macro | 2 | 0.0 | 13 |
| tsymex_phase13_satsuffix | 4 | 0.0 | 13 |
| tsymex_phase13_verdict_primitives | 7 | 0.0 | 12 |
| tsymex_phase13_unknown_roundtrip | 5 | 0.0 | 12 |
| tsymex_phase5_models | 1 | 0.0 | 11 |
| tsymex_phase13_acceptunknown_guard | 0 | 0.0 | 11 |
| tsymex_phase12_renderchoices | 2 | 0.0 | 11 |
| tsymex_phase14_b3_trace_equivalence | 2 | 0.0 | 11 |
| tsymex_phase12_forall | 6 | 0.0 | 11 |
| tsymex_phase13_unsat_roundtrip | 6 | 0.0 | 10 |
| tsymex_phase3_stdlib | 2 | 0.0 | 10 |
| tsymex_phase15_H1_path_heap_fields | 3 | 0.0 | 9 |
| tsymex_phase15_z3_infra | 0 | 0.0 | 8 |
| tsymex_163rev_disc_domain | 0 | 0.0 | 8 |
| tsymex_phase12_pipeline | 1 | 0.0 | 7 |
| tsymex_r6_r6_emit_roundtrip | 4 | 0.0 | 7 |
| tsymex_phase15_z1_canary | 7 | 0.0 | 7 |
| tsymex_phase15_S6a_regex_parser | 0 | 0.0 | 6 |
| tsymex_phase15_CR10_regex_overflow | 3 | 0.0 | 6 |
| tsymex_phase12_seedphase | 4 | 0.0 | 5 |
| tsymex_phase14_c2_dberrors | 6 | 0.0 | 5 |
| tsymex_canonicalize | 4 | 0.0 | 5 |
| tsymex_phase14_multivariant_typebridge | 4 | 0.0 | 5 |
| tsymex_phase1_dsl | 1 | 0.0 | 4 |
| tsymex_phase14_strategy_digest | 0 | 0.0 | 4 |
| tsymex_phase16_R16_1_arithcheck_foundation | 4 | 0.0 | 4 |
| tsymex_phase15_z0_carryover | 6 | 0.0 | 4 |
| tsymex_g6_algebra | 2 | 0.0 | 4 |
| tsymex_phase15_CR2_cachekey | 7 | 0.0 | 3 |
| tsymex_rfc0005_s8x_vm_alias | 0 | 0.0 | 3 |
| tsymex_phase12_sink | 5 | 0.0 | 3 |
| tsymex_phase12_phase_closure | 0 | 0.0 | 3 |
| tsymex_phase14_b2_forcephases | 1 | 0.0 | 3 |
| tsymex_h_stepA_nominalid | 5 | 0.0 | 3 |
| tsymex_phase12_notapplicable | 7 | 0.0 | 3 |
| tsymex_phase12_scan | 3 | 0.0 | 3 |
| tsymex_typebridge_variants | 3 | 0.0 | 2 |
| tsymex_phase14_multivariant_ir | 3 | 0.0 | 2 |
| tsymex_phase14_b5_replaymiss | 3 | 0.0 | 2 |
