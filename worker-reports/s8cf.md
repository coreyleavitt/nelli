# S8cf: DONE

- **sha:** `a0824d0b58b347e5f28fdafe6c5bcf271e77417c`, branch `rfc-0005-s8cf`, pushed
- **base:** `136ad60` with S8bt (`a0c5a7f`) merged as `d08fe84`
- **walker:** 242, provisional; the coordinator assigns the number

## Decisions for the coordinator
1. **Item 12:** keep 8.44 and 8.39 declined, or pay for more library legs. Today they stay declined, and 8.39 JIT's 113 differences stay declined. Windows legs took 6-38 minutes in S8bt's runs (fuzzer-mingw 6-11, fuzzer-msvc 33-38, symex-mingw 35-38), and the 32 regex suites alone would take far more than 5 minutes per added leg.
2. **Walker number:** 242 is provisional. It appears in `canonicalize.nim` and in the CR2 pin.
3. **Base choice:** batch 8 was not on the channel when this slice started, so the base stands. Channel tip `afce42a` has since moved past it, so expect a merge at integration.

## What the local gates certify
- **Full gates ran at `f8a70ba`, not the final sha.** `f8a70ba..a0824d0` touches only `nelli.nimble` and `tests/tsymex_rfc0005_s8cf_jitutf*.nim`.
- **Rerun at `a0824d0`:** those six test files on all three runners and on cpp. Their rows below are from that run.
- **cpp at `f8a70ba`:** the other eight new suites.
- **Windows at `a0824d0`:** all three legs green.

## Rule slip
`PAUSE_SLICE_TESTS` was up from 07:48. I started test runs without checking it until about 08:05: at least the 4.13.4 point suite and the JIT utf suite, and possibly the earlier point runs after 07:48. The gates themselves check the flag before each test.

## Soundness bugs found
- **Items 1, 2 (fixed, RED then GREEN):** see below. `(a|a)*[bc]` at a^30 gave five false `sxUnsat`, `missOnLong` a false `sxSat`, and the JIT stack limit a false `sxUnsat`.
- **My own fix, caught before landing:** the first pinned-subject fix dropped roots by fresh name and gave a false `sxSat` on `cf_branches_no` (RED observed on Z3 4.13.4). It was never committed. `pointCheck` now drops a definition only when its value is stated and no remaining root names its fresh terms. `cf_branches_no` is pinned `sxUnsat`.
- **Latent, avoided:** a `v == f` Int definition in `regexRecDefConds` segfaulted at `byteLeafIds` dec_ref. S8cf uses an inline term instead; the crash itself is not fixed.

## Items: design, RED and GREEN
| Item | Suite | RED observed | GREEN and design |
|---|---|---|---|
| 1, 2 limits, JIT stack | `s8cf_limits`, `s8cf_reach` | On `90f8b4d`: the false verdicts above | `pcre_select.limitReach` (`reachLenCap` 4096, `reachCallBudget` 5M, `reachDepthBudget` 900); `RegexLimitSite`; `checkCapped` wraps `checkExact`: SAT past safe re-solved with length guards, else unknown; UNSAT must survive `limitWorldRefuted` |
| 3 JIT LIMIT count | `s8cf_jitlimit` | Prior decline | `jitCost`; 424350 calls on JIT, 0 differ, 400 skipped (`detect_repeat` group repeats keep `jitCountUnread`) |
| 4 limit gaps | `s8cf_limitgaps` | Prior declines | `buildNfa(..., concrete = true)`, `possCps`/`possWhole`/`possCrlf`; 2380 calls, 621 stops, 12 unread, 0 differ |
| 5 SKIP:NAME past 7 | `s8cf_skipcount` | On `f5d9d9a`: subjects unmodelled | `concreteCall`, `execArgCap` 100; 1600 compared |
| 6 JIT UTF scan | `s8cf_jitutf`, `_b` to `_f` | On `f977620`: decline | The U+0080..U+00BF decline was over-cautious and is removed; JIT: 239976 calls, 153 scanned patterns, 0 mid-character, 15984 language runs, 34 observable scans, 0 differ. `(*ANY)` under the scan keeps its decline (72+ real differences when lifted); pinned calls read at points |
| 7 classes on 8.37 | `s8cf_classes` | On the `f977620` tree: 133 declined vs 18 | `parsePcre(p, extended, pre845)`, `classPre845`; JIT 65272 calls, 8.45 72436 calls, 0 differ; evidence in `tests/s8cf_harness/class_probe.nim` |
| 8, 9, 10 point route | `s8cf_point` | Unknown at 20M/40M units | `pointCheck`, `RegexPointSite`, `concreteEntry`, `pointTable`; step 65k-95k units, past cap pinned about 3k, symbolic 287k-377k, pinned subject under 1k on Z3 4.13.4. Regex cap stays 40k |
| 11 replace facts | `s8cf_replace` | On the pre-item commit, via `s8cf-work/rp_red.sh`: all unknown | `ReplaceFacts.pairs` (`maxPairs` 64), `.utf`, `searchMoves`, `nonEmptyAttempt`; 8895 fact calls, 0 differ. `iekStrCount` lowers `strutils.count` (char or literal non-empty sub) |
| 12 library builds | none | not applicable | Cost reported above; no code |

**Job assumption that was incomplete:** the job listed two limit outcomes. There is a third: on 8.45 with an 8 MB stack, `(a|b)*c` takes SIGSEGV near 8000 bytes and `(a)*c` near 16000. `limitReach` covers it by treating those lengths as past safe, so the design did not change and this is not a BLOCKER.

**Suites repinned because the slice moved them:** `emit_roundtrip`, `s5_str`, `s8bt_replace_facts`, `s8bt_limit_langs`, `s8bt_utf` (now `parsePcre(p, false, pcreOlderThan(8, 45))`). `altPlus` moved to unknown (unbounded refutation), `altPlusBounded` stays `sxUnsat`.

## Different mechanisms, reported and not fixed here
Also committed in the RFC under "As landed (S8cf)".

**SOUNDNESS (held as unknown, no wrong verdict):**
- A value past `limitReach`'s safe length is `zsUnknown`, including an unbounded no-match refutation.
- SIGSEGV past the stack is the library's own behaviour; no verdict models the crash.

**PRECISION:**
- Auto-possession comparing a property or XCLASS with another item declines.
- A kept `ignore_skip_arg` under a limit declines (model -8 against native -1 on abab at LIMIT_MATCH=5).
- `detect_repeat` group repeats stay unread on the JIT.
- SKIP:NAME's count past 100 is unmodelled; languages decline past 7, and the walker reads those calls at points.
- Symbolic `(*ANY)` under the JIT's scan stays unknown.
- Multi-item POSIX classes on 8.37 decline.
- `replace`'s unmarked SKIP:NAME has no sure bytes; `first` is not computed in UTF.
- `count` of `set[char]` and overlapping counts stay unregistered.

## Windows at `a0824d0`
| Leg | Run | Result |
|---|---|---|
| fuzzer-mingw | 41479023735 | success |
| symex-mingw | 41479023244 | success, 530 suites, none failed |
| fuzzer-msvc | 41479023346 | success |

Per-file times come from the symex-mingw log. The full 530-suite table is in `$W/s8cf-work/win_times.txt`. Run is the suite's own wall time; total includes compile, measured from the log timestamps.

| New suite | Run (s) | Compile + run (s) |
|---|---|---|
| s8cf_jitutf_d | 54.4s | 69.7 |
| s8cf_classes | 23.6s | 66.9 |
| s8cf_jitlimit | 26.6s | 66.8 |
| s8cf_replace | 7.8s | 55.3 |
| s8cf_jitutf_b | 35.8s | 51.5 |
| s8cf_skipcount | 9.1s | 50.1 |
| s8cf_reach | 44.1s | 49.2 |
| s8cf_limitgaps | 0.4s | 42.2 |
| s8cf_jitutf | 0.3s | 41.3 |
| s8cf_jitutf_f | 24.9s | 40.5 |
| s8cf_jitutf_e | 23.4s | 39.9 |
| s8cf_point | 7.2s | 33.2 |
| s8cf_jitutf_c | 21s | 31.4 |
| s8cf_limits | 1.5s | 26.5 |

**60 s check:**
- Every S8cf suite runs under 60 s. The slowest is `jitutf_d` at 54.4 s.
- Three exceed 60 s only with compile: `jitutf_d` 69.7, `classes` 66.9, `jitlimit` 66.8. Compile-dominated suites over 60 s are common in this corpus; I did not split those three.
- Over 60 s of run time, not from this slice: `configdefaults` 105.6 and `s8ai_semantic` 79.7. A sibling run on the same base (`s8bz`, 41430099964) shows 108.0 and 79.7, and neither suite uses a regex.

## Per-suite gates
Each cell is rc / seconds, with P=2 under shared load. Every suite passed. The summaries also hold one empty-name entry per gate (rc=1, no test ran): a blank line in my suite list, omitted here.

| Suite | Z3 5.1 | Z3 4.13.4 | 8.37+JIT |
|---|---|---|---|
| tbiasthreading | 0 / 4 | 0 / 4 | 0 / 4 |
| tcoverage | 0 / 4 | 0 / 4 | 0 / 4 |
| tdb | 0 / 5 | 0 / 4 | 0 / 4 |
| tdbcorpuslog | 0 / 5 | 0 / 4 | 0 / 4 |
| tdsl | 0 / 5 | 0 / 5 | 0 / 4 |
| tfrequency | 0 / 4 | 0 / 5 | 0 / 4 |
| tfuzzconcolicdegrade | 0 / 25 | 0 / 24 | 0 / 24 |
| tfuzzcorpusstore | 0 / 3 | 0 / 3 | 0 / 3 |
| tfuzzcovshm | 0 / 3 | 0 / 3 | 0 / 3 |
| tfuzzfrontier | 0 / 4 | 0 / 4 | 0 / 4 |
| tfuzzmacro | 0 / 4 | 0 / 4 | 0 / 3 |
| tfuzzoperatorselector | 0 / 2 | 0 / 3 | 0 / 2 |
| tlaws | 0 / 5 | 0 / 3 | 0 / 3 |
| tnested | 0 / 5 | 0 / 4 | 0 / 3 |
| treporter | 0 / 5 | 0 / 4 | 0 / 4 |
| treservedlabel | 0 / 4 | 0 / 4 | 0 / 4 |
| tstrategy | 0 / 6 | 0 / 3 | 0 / 3 |
| tsymbolic | 0 / 6 | 0 / 4 | 0 / 3 |
| tsymex_163_opaque_transparent | 0 / 24 | 0 / 21 | 0 / 20 |
| tsymex_163rev_enum_field_witness | 0 / 27 | 0 / 21 | 0 / 21 |
| tsymex_canonicalize | 0 / 6 | 0 / 5 | 0 / 3 |
| tsymex_g1b_concolic | 0 / 29 | 0 / 23 | 0 / 22 |
| tsymex_g2_flip | 0 / 42 | 0 / 30 | 0 / 35 |
| tsymex_phase11_walker | 0 / 28 | 0 / 22 | 0 / 20 |
| tsymex_phase12_notapplicable | 0 / 5 | 0 / 5 | 0 / 2 |
| tsymex_phase12_phase_closure | 0 / 4 | 0 / 5 | 0 / 3 |
| tsymex_phase13_layer1_wire | 0 / 29 | 0 / 22 | 0 / 21 |
| tsymex_phase13_rlimit | 0 / 27 | 0 / 22 | 0 / 20 |
| tsymex_phase15_A2b_bitwise | 0 / 28 | 0 / 23 | 0 / 20 |
| tsymex_phase15_C1_canonical_kind | 0 / 30 | 0 / 24 | 0 / 22 |
| tsymex_phase15_CR2_cachekey | 0 / 4 | 0 / 4 | 0 / 2 |
| tsymex_phase15_N0_kindgate_widen | 0 / 28 | 0 / 22 | 0 / 22 |
| tsymex_phase15_N2_kindgate_audit | 0 / 5 | 0 / 6 | 0 / 4 |
| tsymex_phase15_S6a_regex_parser | 0 / 8 | 0 / 7 | 0 / 4 |
| tsymex_phase15_S6b_regex | 0 / 28 | 0 / 22 | 0 / 20 |
| tsymex_phase15_S7b_smoke | 0 / 28 | 0 / 22 | 0 / 20 |
| tsymex_phase15_z3_infra | 0 / 10 | 0 / 8 | 0 / 7 |
| tsymex_r6_lows_declines | 0 / 27 | 0 / 23 | 0 / 21 |
| tsymex_r6_n27_placeholder_read_audit | 0 / 4 | 0 / 5 | 0 / 2 |
| tsymex_r6_n28_shadow_collision | 0 / 29 | 0 / 22 | 0 / 20 |
| tsymex_r6_n31_block_counter | 0 / 26 | 0 / 23 | 0 / 20 |
| tsymex_r6_n36_raise_class_audit | 0 / 5 | 0 / 5 | 0 / 3 |
| tsymex_r6_n42_deref_taint | 0 / 29 | 0 / 23 | 0 / 21 |
| tsymex_r6_n43_parity | 0 / 31 | 0 / 23 | 0 / 21 |
| tsymex_r6_r4_collector_scoping | 0 / 28 | 0 / 21 | 0 / 21 |
| tsymex_r6_r6_emit_roundtrip | 0 / 7 | 0 / 5 | 0 / 5 |
| tsymex_rectify_effects | 0 / 28 | 0 / 20 | 0 / 20 |
| tsymex_rectify_variants | 0 / 27 | 0 / 20 | 0 / 20 |
| s0_exhibit | 0 / 30 | 0 / 20 | 0 / 21 |
| s10_replay_verdict | 0 / 32 | 0 / 23 | 0 / 23 |
| s11_surface | 0 / 36 | 0 / 30 | 0 / 27 |
| s1b_kinds | 0 / 29 | 0 / 22 | 0 / 21 |
| s1c_verdict | 0 / 32 | 0 / 26 | 0 / 24 |
| s2_replay | 0 / 32 | 0 / 23 | 0 / 24 |
| s3_monotonicity | 0 / 30 | 0 / 25 | 0 / 24 |
| s4_alloc | 0 / 27 | 0 / 21 | 0 / 21 |
| s5_str | 0 / 31 | 0 / 24 | 0 / 24 |
| s6a_budget | 0 / 29 | 0 / 23 | 0 / 22 |
| s6b_ops | 0 / 31 | 0 / 24 | 0 / 24 |
| s7_closure | 0 / 30 | 0 / 23 | 0 / 23 |
| s8ab_letaudit | 0 / 50 | 0 / 38 | 0 / 37 |
| s8ag_indexsplit | 0 / 38 | 0 / 30 | 0 / 27 |
| s8am_remainder | 0 / 31 | 0 / 24 | 0 / 25 |
| s8an_remainder | 0 / 50 | 0 / 38 | 0 / 38 |
| s8ao_remainder | 0 / 30 | 0 / 23 | 0 / 22 |
| s8ap_remainder | 0 / 43 | 0 / 33 | 0 / 32 |
| s8aw_remainder | 0 / 33 | 0 / 26 | 0 / 25 |
| s8ay_remainder | 0 / 47 | 0 / 37 | 0 / 37 |
| s8b_substitutions | 0 / 29 | 0 / 21 | 0 / 22 |
| s8bb_captures | 0 / 47 | 0 / 39 | 0 / 37 |
| s8bb_capvalues | 0 / 15 | 0 / 13 | 0 / 12 |
| s8bb_capvalues_lf | 0 / 17 | 0 / 18 | 0 / 13 |
| s8bb_capvalues_plus | 0 / 16 | 0 / 18 | 0 / 12 |
| s8bb_constructs | 0 / 16 | 0 / 12 | 0 / 13 |
| s8bb_exhaustive | 0 / 21 | 0 / 9 | 0 / 16 |
| s8bb_remainder | 0 / 49 | 0 / 31 | 0 / 39 |
| s8bb_replace | 0 / 36 | 0 / 45 | 0 / 27 |
| s8bb_selection | 0 / 25 | 0 / 16 | 0 / 18 |
| s8bj_entries | 0 / 23 | 0 / 22 | 0 / 16 |
| s8bj_entries_multiline | 0 / 22 | 0 / 21 | 0 / 17 |
| s8bj_entries_utf | 0 / 13 | 0 / 8 | 0 / 8 |
| s8bj_entries_utf_b | 0 / 14 | 0 / 13 | 0 / 12 |
| s8bj_entries_utf_c | 0 / 19 | 0 / 17 | 0 / 13 |
| s8bj_langs | 0 / 9 | 0 / 7 | 0 / 7 |
| s8bj_langs_b | 0 / 9 | 0 / 7 | 0 / 6 |
| s8bj_replace | 0 / 9 | 0 / 8 | 0 / 8 |
| s8bj_replace_lemmas | 0 / 29 | 0 / 21 | 0 / 21 |
| s8bj_startopt | 0 / 7 | 0 / 4 | 0 / 4 |
| s8bj_syntax | 0 / 4 | 0 / 4 | 0 / 3 |
| s8bj_verbs | 0 / 17 | 0 / 12 | 0 / 12 |
| s8bj_walker | 0 / 39 | 0 / 24 | 0 / 30 |
| s8bt_caps | 0 / 19 | 0 / 16 | 0 / 15 |
| s8bt_caps_b | 0 / 18 | 0 / 15 | 0 / 14 |
| s8bt_caps_c | 0 / 32 | 0 / 22 | 0 / 23 |
| s8bt_jit | 0 / 15 | 0 / 11 | 0 / 11 |
| s8bt_jit_langs | 0 / 9 | 0 / 7 | 0 / 7 |
| s8bt_jit_langs_b | 0 / 9 | 0 / 6 | 0 / 6 |
| s8bt_jit_langs_c | 0 / 10 | 0 / 7 | 0 / 7 |
| s8bt_jit_langs_d | 0 / 12 | 0 / 7 | 0 / 7 |
| s8bt_jit_langs_e | 0 / 10 | 0 / 7 | 0 / 6 |
| s8bt_jit_langs_f | 0 / 10 | 0 / 8 | 0 / 8 |
| s8bt_jit_replace | 0 / 11 | 0 / 9 | 0 / 9 |
| s8bt_jit_replace_b | 0 / 10 | 0 / 7 | 0 / 8 |
| s8bt_jit_replace_c | 0 / 10 | 0 / 7 | 0 / 8 |
| s8bt_libversion | 0 / 27 | 0 / 21 | 0 / 20 |
| s8bt_limit | 0 / 13 | 0 / 9 | 0 / 8 |
| s8bt_limit_b | 0 / 10 | 0 / 8 | 0 / 8 |
| s8bt_limit_c | 0 / 12 | 0 / 10 | 0 / 9 |
| s8bt_limit_d | 0 / 12 | 0 / 9 | 0 / 8 |
| s8bt_limit_langs | 0 / 35 | 0 / 27 | 0 / 26 |
| s8bt_replace_facts | 0 / 7 | 0 / 5 | 0 / 5 |
| s8bt_replace_lemmas | 0 / 77 | 0 / 29 | 0 / 63 |
| s8bt_skipname | 0 / 10 | 0 / 8 | 0 / 8 |
| s8bt_skipname_b | 0 / 11 | 0 / 8 | 0 / 8 |
| s8bt_skipname_c | 0 / 11 | 0 / 8 | 0 / 8 |
| s8bt_skipname_d | 0 / 10 | 0 / 8 | 0 / 8 |
| s8bt_skipname_e | 0 / 9 | 0 / 8 | 0 / 8 |
| s8bt_skipname_f | 0 / 14 | 0 / 9 | 0 / 8 |
| s8bt_skipname_langs | 0 / 20 | 0 / 14 | 0 / 14 |
| s8bt_utf | 0 / 7 | 0 / 6 | 0 / 6 |
| s8bt_utf_any | 0 / 10 | 0 / 9 | 0 / 10 |
| s8bt_utf_any_b | 0 / 10 | 0 / 8 | 0 / 8 |
| s8bt_utf_any_c | 0 / 19 | 0 / 15 | 0 / 18 |
| s8bt_utf_any_d | 0 / 16 | 0 / 15 | 0 / 15 |
| s8bt_utf_any_e | 0 / 11 | 0 / 17 | 0 / 13 |
| s8bt_utf_b | 0 / 6 | 0 / 5 | 0 / 7 |
| s8bt_utf_c | 0 / 4 | 0 / 5 | 0 / 5 |
| s8bt_utf_d | 0 / 5 | 0 / 5 | 0 / 5 |
| s8bt_utf_e | 0 / 5 | 0 / 5 | 0 / 6 |
| s8cf_classes | 0 / 25 | 0 / 25 | 0 / 28 |
| s8cf_jitlimit | 0 / 21 | 0 / 20 | 0 / 29 |
| s8cf_jitutf | 0 / 20 | 0 / 19 | 0 / 18 |
| s8cf_jitutf_b | 0 / 12 | 0 / 12 | 0 / 12 |
| s8cf_jitutf_c | 0 / 11 | 0 / 10 | 0 / 11 |
| s8cf_jitutf_d | 0 / 13 | 0 / 14 | 0 / 14 |
| s8cf_jitutf_e | 0 / 10 | 0 / 11 | 0 / 11 |
| s8cf_jitutf_f | 0 / 9 | 0 / 9 | 0 / 10 |
| s8cf_limitgaps | 0 / 20 | 0 / 20 | 0 / 29 |
| s8cf_limits | 0 / 23 | 0 / 23 | 0 / 30 |
| s8cf_point | 0 / 23 | 0 / 24 | 0 / 24 |
| s8cf_reach | 0 / 26 | 0 / 28 | 0 / 21 |
| s8cf_replace | 0 / 21 | 0 / 23 | 0 / 23 |
| s8cf_skipcount | 0 / 20 | 0 / 21 | 0 / 22 |
| s8l_exits | 0 / 29 | 0 / 30 | 0 / 30 |
| s8m_exits | 0 / 27 | 0 / 27 | 0 / 27 |
| s8o_termination | 0 / 20 | 0 / 20 | 0 / 21 |
| s8p_precision | 0 / 28 | 0 / 29 | 0 / 29 |
| s8s_precision | 0 / 48 | 0 / 49 | 0 / 48 |
| tsymex_snd1_uncertain_taint | 0 / 22 | 0 / 21 | 0 / 20 |
| tsymex_snd3_loopdegrade | 0 / 22 | 0 / 22 | 0 / 23 |
| tsymex_typebridge_variants | 0 / 3 | 0 / 2 | 0 / 2 |

cpp: `limits`, `reach`, `jitlimit`, `limitgaps`, `skipcount`, `classes`, `point`, `replace` rc=0 at `f8a70ba`; `jitutf` and `_b` to `_f` rc=0 at `a0824d0`.
