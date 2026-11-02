# S8ca report: DONE

- **Branch:** rfc-0005-s8ca, pushed.
- **Head:** 8cef160 (docs). The last commit Windows ran is 5c4350c; the last commit touching `src` is a22362c.
- **Base:** 5729b1a (S8bu; code 8815a81, walker 225).
- **Walker:** 233 (provisional, kept as the coordinator instructed). The CR2 `==` pin is updated and passes; every S8ca suite has a `>= 233` floor pin.
- **Resumed:** the previous agent stopped at a22362c on 2026-10-04. Items 1-8 were on the branch and Windows was green, but item 9, the sweeps, the RFC note, the row flip and this report were missing. Everything under "Suites" and "Windows" was run on 2026-11-02; nothing relies on the October logs except where marked.

## Audit of a22362c against the job

| requirement | state at a22362c | now |
|---|---|---|
| items 1-8 | code and suites present | re-verified below; item 4b's literal `pb[].x` was not pinned (only `grb.x`), now pinned |
| item 9 | a loaded, truncated timing, no split | measured idle; three files split |
| sweep c 5.1 | 8 logs from October, 2 from an older tree | 148 suites |
| sweep c 4.13.4, cpp | none | 148 suites each |
| RFC note, row flip, report | missing | done |

## Commits (5729b1a..head)

| commit | item | change |
|---|---|---|
| 5ed0aa9 | docs | adds the slice row |
| 7440d2b | 1 | native stack check; walker 233 |
| 37c4ec3 | 2 | in-place write log for views; `swap` modelled |
| d310138, 0effdcc, 0302e64, a22362c | 3-8, Windows fixes | WIP commits |
| d34b972 | 9 | splits `s8bu_paths` and `s8ca_strings` |
| ab58942 | 4b, 9 | pins `pb[].x`; splits `s8ca_closures` |
| 1c9bc98, 5c4350c | 60 s rule | trims the Windows run of `s8ca_stack` |
| 8cef160 | docs | RFC "As landed (S8ca)"; the row flipped to done |

Four WIP commits say they are "rewritten into per-item commits before delivery". I did not do that: it needs a force-push, which my rules forbid. See "For the coordinator".

## RED and GREEN

**RED observed today, using the final suites on the pre-fix trees** (logs in `s8ca-work/red2/`). Items 3-8 ran on wt/s8ca-red at 37c4ec3. Items 1-2 ran on wt/s8ca-base at 5729b1a.

| item | RED observed |
|---|---|
| 1 | `configdefaults` on cpp: the binary dies after 23 OK, in the round-2 pin. The nim wrapper reports rc=1; S8bu recorded rc=139 from the binary. |
| 2 | `s8ca_views` 3 OK / 4 failed: `ls`, `li`, `lp` sxUnsat and their `_dead` targets sxSat, swapped (`swap` a no-op). |
| 3 | `s8ca_calls`: `ed`, `eo`, `el`, `ev`, `ec` and their dead targets sxUnknown. |
| 4 | `s8ca_closures` failed its verdict test; `s8ca_closures_heap`: `hc`, `hp`, `pl`, `pg`, `pv` sxUnknown (`ceCaptureByRefUnmodelled`). `pc` (the body alone reaches the object) already decided at 37c4ec3. |
| 5 | `s8ca_procvals`: both verdict tests failed. |
| 6 | `s8ca_strings` does not compile (`dsl_parser.nim(5553)`: field `size` on `itString`). Finer variants with the failing line removed are in the October logs only: `s8ca-work/it6/red.tsymex_rfc0005_s8ca_strings_red2.51.c.log` (1 OK / 4 failed). |
| 7 | `s8ca_resize` 3 OK / 3 failed. |
| 8 | `s8ca_derefmut` does not compile (`expectKind` through the inlined system `add`). October's finer variant `it6/red.tsymex_rfc0005_s8ca_derefmut_red2.51.c.log` also fails to compile. |

**GREEN:** all of the above pass at the head on all three configs; see "Suites". The October RED for `s8ca_stack` (`logs/stack_red_c*.log`) is that run's evidence only; I did not repeat it, since the suite does not compile without `nativestack`.

## Soundness bugs found and fixed

1. **`viewFollows` was structural.** `swap(gps[], other)` with `other = newSeq(2)` gave `vw` sxUnsat and `vw_dead` sxSat in a defined program.
2. **`swap` was a silent no-op,** which gave clean false sxUnsat verdicts. Its bodiless magic was registered with an empty body.
3. **A shadowed element cell clobbered the element** after a callee's store: `let q = addr s[0]; onlyP(q, k)` then `s[0] != k` was a false sxSat.

## Design per item

1. `nativestack.nim` reads the stack's bounds from the OS, re-reading when the stack pointer leaves them (a new fiber). Each call frame records its stack pointer, so a level's cost is measured. A call is not inlined when the stack left is under the reserve plus twice the largest level seen. It declines in-band as `beBudgetExhaustedUnmodelled`, naming the native stack, and is not cached. Windows: a 1 MB main thread could overflow the same way before this; on CI the solve runs on a 16 MB fiber and the image reserves 8 MB, and all are measured by the same check.
2. Element write-backs are marked `dwInPlace` and logged in `Path.inPlaceSteps`. A view anchored by `ViewMark` follows only a chain of such steps. Any other write declines, whatever its terms.
3. The `addr s[i]` actual is the element's own cell (`sharesElemCell`).
4. (a) A captured address-taken variable binds to its cell (`linkCapAddrCells`, `capCellOf`). (b) A heap lvalue goes by reference (`VarLoc` mode `ref`, `byRefSub`).
5. A seq, table or set contributes each leaf's sort to the application's domain.
6. `iekStrSetAt` for character writes, `iekStrChars` / `iekStrFromChars` for `openArray[char]`, and `StrBuf` to tell whether a by-value copy shares memory.
7. As probed natively: `IndexDefect` iff the length is not 0 and a bound is out of range; a negative view enters no loop and every index raises. A resizing `mitems` body meets Nim's `AssertionDefect` at the end of the iteration; an element used after the resize declines (`miElemGuards`).
8. `p[].add`, `del`, `insert`, `incl` read through the pointer, apply the bare arm's mutation, and store back. A sharing view declines.
9. See "Compile time".

## Compile time (item 9)

**Idle measurement** (2026-11-02, host otherwise idle, 12 cores, my two compiles at once, load 2-8; `s8ca-work/ctime_final.txt`). Compile user seconds:

| file | c | cpp |
|---|---|---|
| one-SUT floor (import of `nelli/symex`) | 23.8 | 29.5 |
| s8bu_byvalseq | 25.2 | 31.8 |
| s8bu_calls | 29.5 | 35.3 |
| s8bu_mitems | 27.9 | 33.8 |
| s8bu_paths | 25.9 | 31.6 |
| s8bu_term | 25.3 | 32.4 |
| s8bu_varviews | 29.1 | 39.7 |
| s8bu_views | 33.2 | 33.7 |
| s8ca_calls | 28.8 | 38.0 |
| s8ca_closures | 28.1 | 32.5 |
| s8ca_closures_heap | 28.2 | 38.2 |
| s8ca_derefmut | 32.0 | 40.4 |
| s8ca_procvals | 29.7 | 42.1 |
| s8ca_resize | 35.9 | 43.1 |
| s8ca_stack | 33.3 | 39.4 |
| s8ca_strings | 35.8 | 42.2 |
| s8ca_strings_byvalue | 32.3 | 38.5 |
| s8ca_views | 33.5 | 31.6 |

Every file is under 60 s on both backends.

**The splits were not needed by this measurement.** I split `s8bu_paths`, `s8ca_strings` and `s8ca_closures` earlier, on readings of 60-62 s c taken while other slices ran (load about 20, `ctime_quiet.txt`; the name is wrong, that slot was not quiet). The idle numbers came later and show those readings were load. I kept the splits: they do no harm and take per-file Windows time down, but they are not what the job's test required.

## Suites

Logs are in `s8ca-work/gate/`, run from wt/s8ca-gate at ab58942 (clean; `src` identical to a22362c and the head), at most 2 runs at once.

**What ran** (`gate.list`, 148 suites): every suite the job names (`s8ca_*`, `s8bu_*`, `s8bs_*`, configdefaults, s8ax, s8bh, s8be, s7_closure, letaudit, n27, emit_roundtrip, augmented_assign, CR2); every `command grep -lE 'openArray|closure|addr ' tests/*.nim` hit, including non-symex ones; the previous agent's list; and S8bu's 62-suite list. `tests/s8bs_suts.nim` is a grep hit but an include, not a suite.

**Totals (ok/failed):** c 5.1 2075/0, c 4.13.4 2075/0, cpp 5.1 2050/0.

**Changes after that sweep:** only `s8ca_stack` (1c9bc98, 5c4350c; tests only). At 5c4350c it passes 9/0 on all three configs, run from wt/s8ca (`s8ca-work/post/stack*.log`). It shows 10/0 in the table because a duplicated pin was then removed. The docs commit changes no code.

**The one suite that is not green:** `r6_n43_parity` on cpp does not compile (`std::atomic` deleted `operator=`, in generated `runtime.nim` code). The same error occurs at the base 5729b1a (`s8ca-work/post/base.tsymex_r6_n43_parity.51.cpp.log`), so it is pre-existing and not S8ca's. It accounts for the whole 25-test difference on cpp.

`tfuzzwinjoblimits` shows 0/0 with rc=0 on all three: it runs no tests on Linux.

| suite | c 5.1 | c 4.13.4 | cpp 5.1 |
|---|---|---|---|
| tdbbackends | 6/0 | 6/0 | 6/0 |
| tdbcorpuslog | 26/0 | 26/0 | 26/0 |
| tfuzzcheckpointmgr | 11/0 | 11/0 | 11/0 |
| tfuzzconcolicbridge | 13/0 | 13/0 | 13/0 |
| tfuzzconcolicdegrade | 5/0 | 5/0 | 5/0 |
| tfuzzcorpus_nilguard | 1/0 | 1/0 | 1/0 |
| tfuzzcovdump | 4/0 | 4/0 | 4/0 |
| tfuzzcrashrecorder | 10/0 | 10/0 | 10/0 |
| tfuzzdroppedseed | 6/0 | 6/0 | 6/0 |
| tfuzzforkworker | 5/0 | 5/0 | 5/0 |
| tfuzzmacro | 8/0 | 8/0 | 8/0 |
| tfuzzprimarymeta | 15/0 | 15/0 | 15/0 |
| tfuzzprocessisolation | 6/0 | 6/0 | 6/0 |
| tfuzzrefactordeterminism | 2/0 | 2/0 | 2/0 |
| tfuzzsectionsize | 7/0 | 7/0 | 7/0 |
| tfuzzwinjoblimits | 0/0 | 0/0 | 0/0 |
| tfuzzwinworker | 2/0 | 2/0 | 2/0 |
| tfuzzworkerlifecycle | 3/0 | 3/0 | 3/0 |
| tfuzzworkerprocess | 18/0 | 18/0 | 18/0 |
| tfuzzworkerspawnfailshm | 2/0 | 2/0 | 2/0 |
| tmetamorphic | 6/0 | 6/0 | 6/0 |
| tmutation | 4/0 | 4/0 | 4/0 |
| 163rev_inert_exclusions | 15/0 | 15/0 | 15/0 |
| 163rev_int_literal_width | 27/0 | 27/0 | 27/0 |
| CR2a_expr_catchall | 7/0 | 7/0 | 7/0 |
| CR2b_paramtype_catchall | 4/0 | 4/0 | 4/0 |
| CR2c_witnessreader_catchall | 17/0 | 17/0 | 17/0 |
| a3_closure_iterators | 11/0 | 11/0 | 11/0 |
| a6_symlen_hof | 3/0 | 3/0 | 3/0 |
| a7_runes_iter | 6/0 | 6/0 | 6/0 |
| augmented_assign | 8/0 | 8/0 | 8/0 |
| configdefaults | 24/0 | 24/0 | 24/0 |
| g1b_concolic | 15/0 | 15/0 | 15/0 |
| g4_cmpwalk | 1/0 | 1/0 | 1/0 |
| g6_algebra | 13/0 | 13/0 | 13/0 |
| h_stepC_heapidentity | 10/0 | 10/0 | 10/0 |
| phase12_phase_closure | 1/0 | 1/0 | 1/0 |
| phase14_multivariant_witness | 2/0 | 2/0 | 2/0 |
| phase15_A2a_atomicir_audit | 9/0 | 9/0 | 9/0 |
| phase15_C1_ir | 7/0 | 7/0 | 7/0 |
| phase15_C2a_closure_capture | 3/0 | 3/0 | 3/0 |
| phase15_C2b_closure_call | 3/0 | 3/0 | 3/0 |
| phase15_C4_hof | 5/0 | 5/0 | 5/0 |
| phase15_C5_closure_eq | 5/0 | 5/0 | 5/0 |
| phase15_C6_smoke | 9/0 | 9/0 | 9/0 |
| phase15_CR1_CR5_closure_heap | 5/0 | 5/0 | 5/0 |
| phase15_CR21_parseintraise_arg | 3/0 | 3/0 | 3/0 |
| phase15_CR2_cachekey | 6/0 | 6/0 | 6/0 |
| phase15_F2_float_literals | 5/0 | 5/0 | 5/0 |
| phase15_H1_path_heap_fields | 2/0 | 2/0 | 2/0 |
| phase15_N1_resolution_gates | 32/0 | 32/0 | 32/0 |
| phase15_N2_kindgate_audit | 5/0 | 5/0 | 5/0 |
| phase15_N3_scan_boundary | 5/0 | 5/0 | 5/0 |
| phase15_S11_mutation | 5/0 | 5/0 | 5/0 |
| phase15_cr9_lowerInExpr | 6/0 | 6/0 | 6/0 |
| phase15_g4_distinct_sort | 4/0 | 4/0 | 4/0 |
| phase15_g5_distinct_borrow | 3/0 | 3/0 | 3/0 |
| phase15_r11_unsafecast | 4/0 | 4/0 | 4/0 |
| phase15_r11b_smoke | 11/0 | 11/0 | 11/0 |
| phase15_r13_closure_ref | 1/0 | 1/0 | 1/0 |
| phase15_r7_alias_chain | 9/0 | 9/0 | 9/0 |
| phase15_rereview_drains | 15/0 | 15/0 | 15/0 |
| phase16_R16_1_arithcheck_foundation | 22/0 | 22/0 | 22/0 |
| phase16_R16_5_overflow_thru_closure | 3/0 | 3/0 | 3/0 |
| r11_range_invariant_audit | 7/0 | 7/0 | 7/0 |
| r6_a6r_callwitness | 12/0 | 12/0 | 12/0 |
| r6_b5_chained | 9/0 | 9/0 | 9/0 |
| r6_itesv_mergedegrade | 11/0 | 11/0 | 11/0 |
| r6_lows_declines | 15/0 | 15/0 | 15/0 |
| r6_n13_reassign_seqarm | 7/0 | 7/0 | 7/0 |
| r6_n14_seqops | 25/0 | 25/0 | 25/0 |
| r6_n16_closure_zerodefault | 10/0 | 10/0 | 10/0 |
| r6_n27_hof_placeholder | 6/0 | 6/0 | 6/0 |
| r6_n27_placeholder_read_audit | 4/0 | 4/0 | 4/0 |
| r6_n29_seqlit_sortmismatch | 7/0 | 7/0 | 7/0 |
| r6_n36_raise_class_audit | 14/0 | 14/0 | 14/0 |
| r6_n36_raise_degrade | 8/0 | 8/0 | 8/0 |
| r6_n37_raise_residue | 11/0 | 11/0 | 11/0 |
| r6_n40_alloc_totality | 10/0 | 10/0 | 10/0 |
| r6_n43_parity | 25/0 | 25/0 | 0/0 rc=1 |
| r6_r4_collector_scoping | 7/0 | 7/0 | 7/0 |
| r6_r6_emit_roundtrip | 104/0 | 104/0 | 104/0 |
| rectify_refs | 1/0 | 1/0 | 1/0 |
| rfc0005_s0_exhibit | 10/0 | 10/0 | 10/0 |
| rfc0005_s11_surface | 34/0 | 34/0 | 34/0 |
| rfc0005_s1_lattice | 23/0 | 23/0 | 23/0 |
| rfc0005_s1b_kinds | 18/0 | 18/0 | 18/0 |
| rfc0005_s1c_verdict | 24/0 | 24/0 | 24/0 |
| rfc0005_s2_replay | 15/0 | 15/0 | 15/0 |
| rfc0005_s4_alloc | 20/0 | 20/0 | 20/0 |
| rfc0005_s5_str | 35/0 | 35/0 | 35/0 |
| rfc0005_s6a_budget | 31/0 | 31/0 | 31/0 |
| rfc0005_s6b_ops | 44/0 | 44/0 | 44/0 |
| rfc0005_s7_closure | 37/0 | 37/0 | 37/0 |
| rfc0005_s8_scope | 28/0 | 28/0 | 28/0 |
| rfc0005_s8ab_letaudit | 28/0 | 28/0 | 28/0 |
| rfc0005_s8ac_remainder | 19/0 | 19/0 | 19/0 |
| rfc0005_s8ad_remainder | 13/0 | 13/0 | 13/0 |
| rfc0005_s8ag_indexsplit | 15/0 | 15/0 | 15/0 |
| rfc0005_s8an_remainder | 25/0 | 25/0 | 25/0 |
| rfc0005_s8ao_remainder | 11/0 | 11/0 | 11/0 |
| rfc0005_s8ap_remainder | 36/0 | 36/0 | 36/0 |
| rfc0005_s8as_remainder | 33/0 | 33/0 | 33/0 |
| rfc0005_s8au_remainder | 35/0 | 35/0 | 35/0 |
| rfc0005_s8av_remainder | 19/0 | 19/0 | 19/0 |
| rfc0005_s8ax_remainder | 53/0 | 53/0 | 53/0 |
| rfc0005_s8ba_remainder | 32/0 | 32/0 | 32/0 |
| rfc0005_s8bb_constructs | 7/0 | 7/0 | 7/0 |
| rfc0005_s8bb_remainder | 21/0 | 21/0 | 21/0 |
| rfc0005_s8bc_remainder | 74/0 | 74/0 | 74/0 |
| rfc0005_s8bd_remainder | 23/0 | 23/0 | 23/0 |
| rfc0005_s8be_remainder | 34/0 | 34/0 | 34/0 |
| rfc0005_s8bf_alias | 13/0 | 13/0 | 13/0 |
| rfc0005_s8bh_remainder | 35/0 | 35/0 | 35/0 |
| rfc0005_s8bs_addrglobal | 14/0 | 14/0 | 14/0 |
| rfc0005_s8bs_byref | 7/0 | 7/0 | 7/0 |
| rfc0005_s8bs_byvalue | 3/0 | 3/0 | 3/0 |
| rfc0005_s8bs_iterparams | 4/0 | 4/0 | 4/0 |
| rfc0005_s8bu_byvalseq | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_calls | 8/0 | 8/0 | 8/0 |
| rfc0005_s8bu_mitems | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_paths | 4/0 | 4/0 | 4/0 |
| rfc0005_s8bu_term | 10/0 | 10/0 | 10/0 |
| rfc0005_s8bu_varviews | 5/0 | 5/0 | 5/0 |
| rfc0005_s8bu_views | 5/0 | 5/0 | 5/0 |
| rfc0005_s8c_resolution | 25/0 | 25/0 | 25/0 |
| rfc0005_s8ca_calls | 4/0 | 4/0 | 4/0 |
| rfc0005_s8ca_closures | 3/0 | 3/0 | 3/0 |
| rfc0005_s8ca_closures_heap | 4/0 | 4/0 | 4/0 |
| rfc0005_s8ca_derefmut | 5/0 | 5/0 | 5/0 |
| rfc0005_s8ca_procvals | 4/0 | 4/0 | 4/0 |
| rfc0005_s8ca_resize | 6/0 | 6/0 | 6/0 |
| rfc0005_s8ca_stack | 10/0 | 10/0 | 10/0 |
| rfc0005_s8ca_strings | 4/0 | 4/0 | 4/0 |
| rfc0005_s8ca_strings_byvalue | 3/0 | 3/0 | 3/0 |
| rfc0005_s8ca_views | 7/0 | 7/0 | 7/0 |
| rfc0005_s8e_scoping | 36/0 | 36/0 | 36/0 |
| rfc0005_s8i_models | 39/0 | 39/0 | 39/0 |
| rfc0005_s8m_exits | 32/0 | 32/0 | 32/0 |
| rfc0005_s8n_precision | 19/0 | 19/0 | 19/0 |
| rfc0005_s8p_precision | 30/0 | 30/0 | 30/0 |
| rfc0005_s8s_precision | 29/0 | 29/0 | 29/0 |
| rfc0005_s8x_vm_alias | 7/0 | 7/0 | 7/0 |
| rfc0005_s8y_budget_decline | 8/0 | 8/0 | 8/0 |
| rfc0005_s8z_remainder | 37/0 | 37/0 | 37/0 |
| rfc0005_s9_vetoes | 19/0 | 19/0 | 19/0 |
| snd1b_closure_uncertain_axiom | 4/0 | 4/0 | 4/0 |
| tot1_totality_corpus | 21/0 | 21/0 | 21/0 |

## Windows

**DONE sha: 5c4350c, all three legs green.** The head 8cef160 is docs-only, so `paths-ignore` skips it and no Windows run exists for it; it changes only `docs/rfc/0005-branch-scoped-degrade.md`.

| head | symex-mingw | fuzzer-mingw | fuzzer-msvc |
|---|---|---|---|
| a22362c | 37184719336 success | 37184719342 success | 37184719355 success |
| ab58942 | 41412488094 success | 41412488021 success | 41412488010 success |
| 1c9bc98 | 41430194830 FAILED (shard 0 budget only), rerun cancelled | 41430194842 success | 41430194896 success |
| 5c4350c | **41436653107 success** | **41436653116 success** | **41436653094 success** |

At 1c9bc98 every suite passed. Shard 0 failed only on its budget, 40.5 min against 40. The same 57 suites took 23.5 min at ab58942 and 38.9 min at 5c4350c, so that is runner speed. I cancelled its rerun because 5c4350c superseded it.

### Per-file Windows times (symex-mingw 41436653107, at 5c4350c)

S8bu and S8ca files, all within 60 s. Times come from each suite's `==>` / `<==` log timestamps; "run" is the suite's reported `wall`.

| file | compile + run (s) | run (s) |
|---|---|---|
| s8bu_calls | 51.8 | 1.3 |
| s8ca_resize | 47.4 | 3.2 |
| s8ca_stack | 47.0 | 9.1 |
| s8bu_varviews | 45.1 | 0.7 |
| s8ca_views | 43.7 | 0.6 |
| s8bu_mitems | 42.5 | 1.5 |
| s8ca_derefmut | 42.5 | 0.9 |
| s8bu_views | 42.5 | 1.3 |
| s8bu_paths | 40.9 | 1.4 |
| s8ca_closures | 38.3 | 0.2 |
| s8ca_closures_heap | 37.9 | 0.7 |
| s8ca_strings | 37.8 | 8.6 |
| s8bu_byvalseq | 36.9 | 1.4 |
| s8bu_term | 33.5 | 5.4 |
| s8ca_calls | 32.3 | 0.7 |
| s8ca_strings_byvalue | 30.8 | 0.4 |
| s8ca_procvals | 29.7 | 1.3 |

Over 60 s in the whole corpus, none of them S8ca's or S8bu's, against S8bu's run 37147844306 at 8815a81:

| suite | 5c4350c total (run) | 8815a81 (S8bu) total (run) |
|---|---|---|
| configdefaults | 137.4 (98.7) | 134.0 (96.4) |
| rfc0005_s8ax_remainder | 123.7 (19.9) | 142.2 (20.6) |
| rfc0005_s8ar_remainder | 110.7 (5.4) | 111.9 (5.3) |
| rfc0005_s8at_remainder | 108.5 (2.7) | 121.2 (3.1) |
| rfc0005_s8bh_remainder | 103.0 (5.4) | 100.7 (4.9) |
| rfc0005_s8s_precision | 94.0 (24.5) | 95.7 (25.1) |
| rfc0005_s8z_remainder | 88.0 (2.2) | 86.3 (2.7) |
| rfc0005_s8ai_semantic | 86.4 (59) | 88.0 (59.9) |
| rfc0005_s8bb_captures | 84.2 (24) | 78.6 (23.4) |
| rfc0005_s8bc_remainder | 81.8 (6.9) | 82.0 (6.5) |
| rfc0005_s8ap_remainder | 78.7 (1.9) | 79.2 (1.8) |
| rfc0005_s8ay_remainder | 76.2 (8.5) | 92.1 (8.5) |
| rfc0005_s8ba_remainder | 72.5 (6.5) | 75.0 (6.4) |
| rfc0005_s8be_remainder | 71.4 (8.4) | 73.1 (8.2) |
| rfc0005_s8ae_remainder | 70.7 (36.1) | 71.0 (35.5) |
| rfc0005_s8au_remainder | 66.5 (9.5) | 73.5 (13.2) |
| rfc0005_s8bb_constructs | 64.4 (56.4) | 67.7 (57.4) |
| rfc0005_s8bb_replace | 64.1 (15.2) | 60.3 (14) |
| rfc0005_s8ab_letaudit | 63.5 (0) | 55.6 (0) |
| rfc0005_s8p_precision | 62.1 (3.2) | 60.3 (3.1) |
| rfc0005_s8u_precision | 60.3 (0.9) | 58.0 (0.9) |

19 of the 21 were over at 8815a81. `s8ab_letaudit` and `s8u_precision` crossed 60 s here; S8ca's own src growth may contribute, but single-run noise is of that size (the same file differs by up to 2x between runs here, e.g. `s8bu_calls` 31.7 s at ab58942 and 51.8 s at 5c4350c). All 451 files: `s8ca-work/win_times.tsv`.

## Different mechanisms, reported and not fixed here

These are also committed in the RFC under "As landed (S8ca)". I observed each one today with a probe at the head's `src` (`s8ca-work/probes/`, logs `s8ca-work/red2/probe.*`), except the two pinned declines, which the suites pin.

- **SOUNDNESS: `unsafeNew(p, n)` is dropped.** `var p: ref int; unsafeNew(p, 8); p[] = k; if p[] == 3: target` is sxRaised, for both a live and a dead target. Natively nothing raises and the live label is hit. The October notes also record a false sxUnsat from it, on a SUT I did not reproduce.
- **PRECISION: `wasMoved(x)` stops the compile.** `parseCalleeImpl`'s `expectKind` fails (nnkSym for nnkIdentDefs) rather than declining. It is a hard compile error for any SUT that uses it.
- **PRECISION: `setLen` declines** (`feUnsupportedStmtKind`, `nnkWhenStmt` in its system body). A `mitems` body that resizes with `setLen` therefore declines, while `add` and `pop` decide. Item 7's pins use those two.
- **PRECISION: a by-value copy of a string of unknown provenance** (`newString`, an opaque call) declines, because the walk cannot place its memory. Pinned as `bu`.
- **PRECISION: a `mitems` element used after a resize** declines, because its address may be stale (undefined natively). Pinned as `mu`.
- **PRECISION: `tsymex_r6_n43_parity` does not compile on cpp,** as above.

## For the coordinator

1. **WIP commits.** d310138, 0effdcc, 0302e64 and a22362c mix items 3-8, and their messages promise a rewrite into per-item commits. That needs a force-push, so I left them. Decide whether the integrator squashes or rewrites them. `s8ca-work/split/` holds the previous agent's hunk assignment, which I did not use or check.
2. **Integration has moved.** `origin/rfc-0005-soundness-channels` is at walker 237 and 148 commits past where the main clone last was, and this branch is not rebased on it. It already contains S8bu. Walker 233 stays provisional, as instructed.
3. **Splits.** The three splits were made on loaded readings, and idle measurement says the job's 60 s test did not require them. Windows times favour keeping them. Say if you want them undone.
4. **Corpus over 60 s on Windows.** 21 files, listed above, and shard 0 ran 38.9 min of its 40 min budget at 5c4350c. Integration has 12 shards rather than this branch's 8.

## Notes

- **Cap overrun:** one RED run (`closures_heap`, about 60 s) ran alongside the two gate runs just after I restarted the gate, so 3 runs at once, over my cap of 2.
- **Extra worktrees:** wt/s8ca-base (5729b1a) and wt/s8ca-gate (ab58942) are mine and can be removed. wt/s8ca-red had `s8ca_calls`, `_strings`, `_resize`, `_derefmut` and `_closures_heap` overwritten with the final suites; its old variants are in `s8ca-work/red-old/`.
- **Pushes:** I pushed d34b972, ab58942, 1c9bc98, 5c4350c and 8cef160 before the new push rule arrived. No runs of this branch are queued or in progress.
