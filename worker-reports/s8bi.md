# S8bi -- DONE

- **sha:** `e5df2072630b84adb6af8de39106cd7845de3008` (`rfc-0005-s8bi`, force-pushed over the WIP `719f2dc`)
- **base:** `9e15103` (`rfc-0005-s8bb`); `d0eb17b` (the S8bi row, pending) sits between the base and the commit.
- **walker:** 210. The CR2 pin is `== "210"`, and the new suite has a `>= 210` floor.
- **Windows:** all green on e5df207: symex-mingw 37083401315 (the new suite ran 7.3 s wall there, Z3 4.13.4; `s6b_ops` rc=0), fuzzer-mingw 37083401314, fuzzer-msvc 37083401328. Earlier, on WIP 719f2dc: symex-mingw 37065686296 failed (`s6b_ops`, fixed here), fuzzer-mingw 37065686291 passed, fuzzer-msvc 37065686271 passed.

## RED and GREEN

All pins are in `tests/tsymex_rfc0005_s8bi_remainder.nim` (45 checks, registered in `nelli.nimble`).
- **RED at 9e15103.** The previous session observed this by running the suite on an export of the base; the details are in its handoff note.
  - Item 1: false sxSat (closure raise, and a borrowed `div` behind `or`); sxUnknown (`(*UTF8)` behind `and` in an if and a while guard, and `re(p)` behind `and`).
  - Item 2: false sxUnsat (`ord(s[i]) + f(x)`, `10 div i + f(x)`, the closure's own trap fact, a three-term expression, `s[i] == chr(f(x))`).
  - Item 3: compile abort, "node has no type" at `dsl_typebridge.nim:838`. This came from a separate probe, because the abort stops the whole file from compiling at base.
  - Item 4: `feUnsupportedExprKind nnkCurly` on every pin.
  - Item 5: the scan flags `regex_parser.run` and both `regexReplaceRec` definitions.
- **GREEN at e5df207.** 45/45 on c with Z3 5.1 and 4.13.4, and on cpp. The controls are green on both trees, including a raise after the call still carrying the call's facts (sxUnsat).
- **RED/GREEN observed in this session.** `symex-mingw` run 37065686296, on the WIP sha, failed `tsymex_rfc0005_s6b_ops`: "feUnsupportedOpHavoc sites match the S6b audit", `sites.len was 14` against the pinned 13.
  - Cause: the new `newSeqUninit` degrade is a fourteenth `feUnsupportedOpHavoc` site.
  - Audit: it meets the kind's rule (operands lowered first, a fresh symbol per evaluation via `freshDegradeName`, no fork, write or raise dropped), so it is `dcFreshSymbol`.
  - Fix: the count is 14, and the site is documented in the test and in `types.nim`.
  - GREEN locally on head under both Z3 versions (44/44), and on symex-mingw 37083401315.

## Soundness bugs found (wrong verdicts at base)

1. False sxSat: a closure call, a `map`/`filter` over a closure, a borrowed `+ - * div mod`, or a regex call behind a `while` guard's short circuit was lowered, and its raise forked, even when the short circuit skipped it. An undecided regex there also tainted the skipping path (sxUnknown).
2. False sxUnsat: a closure call's exit facts ("the body did not raise", value-bearing exit coverage) were on every raise of the expression, including those evaluated before the call.
3. False sxUnsat (found in this slice): an inline `s[i]` (kept inline for CR-17(a)) was evaluated after a later operand's hoisted `let`s, so `s[i] == chr(f(x))` raised the closure's `ValueError` where Nim raises `IndexDefect`.
4. Crash: `newSeq[T](n)` aborted the compile.
5. Decline: set literals in `in`/`notin`.
6. Latent: `run` and both `regexReplaceRec` definitions were recursive without fuel. Z3 can unfold these without spending `rlimit`. No wrong verdict was found through them.

## Design per item

1. **`rhsHasInlineDefectFork`.** It returns true for `iekClosureCall`, `iekHofCall`, a borrowed `bAdd/bSub/bMul/bDiv/bMod`, `iekSeqNew`, and every regex call except capture-group reads (`regexCallForks`). The lowering decides which patterns raise; a valid pattern pays only the guarded form.
2. **Closure exit facts as stages.** `applyClosureGround` logs `rskClosureExit` in `w.raiseOrder` after the call's raise entries. `drainScalarRaiseForks` strips the drained path's tail (`lastDrainedClosureExitPc`) and re-adds each fact at its logged position. `drainClosureRaises` routes from the survivor it is given, and `ClosureRaise.priorExitPc` is removed. If the tail does not match, the old behaviour is kept and a closure raise records `weInternalWalkerFault`. In the 86-suite logs, the grep for "closure raise drained on a path" found nothing.
3. **`keepInlineRaiseOrder` (`dsl_parser`).** An evaluation-only `let` of an inline raising first operand goes before the second operand's hoisted `let`s, at all six operand-pair sites. The `parseAtomicOperand` calls stay on separate lines, because the A2a chokepoint audit counts marker lines.
4. **`iekSeqNew`** (`snArg`, `snElemTy`, `snZeroed`, `snOfCap`), wired through every IR-kind site and the emit-roundtrip gate (two fixtures).
   - The parser intercepts it before `ensureProcRegistered`. The statement `newSeq(s, n)` goes through the assignment path.
   - Lowering: `RangeDefect` on `n < 0`; a `const_array` of `default(T)`; length 0 for `newSeqOfCap`; a free array plus `feUnsupportedOpHavoc` for `newSeqUninit`; an unbacked element type is `seNestedSeqUnsupported`.
5. **`parseSetLitMember`.** Membership in a literal of constants is an OR of equalities and `>=`/`<=` range checks, with the key read once. There is no range check on the key, because Nim's membership never raises. A byte range over an inline `s[i]` is expanded to equalities, because CR-17 declines ordering on `s[i]`.
6. **Fuel.** Each recursive definition takes `fuel: Z3Int`, has a `fuel <= 0` base case, and passes `fuel - 1` on each recursive call, starting from `len + 1`. The suite scans `src/**/*.nim` (comments stripped) for every `defineRecFun[` and forbids the raw API. Fixture self-tests prove that the scan rejects a fuel-less definition and accepts a fueled one.

## Verification (86 suites; c backend; 900 s bound; per-check diff on `[OK]`/`[FAILED]` lines by name)

| Tree | Z3 5.1 | Z3 4.13.4 |
|---|---|---|
| head e5df207 | 86 suites, 1495/1495 | 86 suites, 1495/1495 |
| base 9e15103 | 85 suites (new suite absent), 1448/1448 | 85 suites, 1448/1448 |

- **rc and hangs:** rc=0 everywhere, with no HUNG.
- **Head vs base:** the only differences are the new suite (+45) and `tsymex_r6_r6_emit_roundtrip` (+2: `iekSeqNew (newSeqOfCap)` and `iekSeqNew (newSeqUninit)`).
- **Z3 5.1 vs 4.13.4:** no differences on either tree.
- **"closure raise drained on a path":** no hits in any of the 344 logs.
- **Tree state during the pass:** the head runs began on `719f2dc` and continued on the same tree after the s6b audit fix was committed (16:10). That fix touched one test count and comments only. `s6b_ops` ran after the fix (44/44).
- **cpp:** `tsymex_rfc0005_s8bi_remainder` passed 45/45 in 100.4 s wall, compilation included.
- **Run-only timings** (built binary, real / user, Z3 5.1, load average about 15, other agents' containers running): cpp 10.2 / 7.0 s; c 13.7 / 8.3 s. Both are under the 60 s per-backend limit. c compile+run took 86.9 s at the same load.

Per suite (passed/total, wall time including compilation):

| Suite | head 5.1 | head 4.13.4 | base 5.1 | base 4.13.4 |
|---|---|---|---|---|
| `rfc0005_s8bi_remainder` | 45/45 38s | 45/45 40s | absent | absent |
| `rfc0005_s8bb_remainder` | 21/21 35s | 21/21 38s | 21/21 36s | 21/21 51s |
| `rfc0005_s8ay_remainder` | 38/38 63s | 38/38 71s | 38/38 65s | 38/38 69s |
| `rfc0005_s8aw_remainder` | 31/31 51s | 31/31 52s | 31/31 34s | 31/31 38s |
| `rfc0005_s8bb_replace` | 7/7 38s | 7/7 61s | 7/7 40s | 7/7 60s |
| `rfc0005_s7_closure` | 37/37 44s | 37/37 44s | 37/37 43s | 37/37 32s |
| `phase15_C2a_closure_capture` | 3/3 41s | 3/3 29s | 3/3 26s | 3/3 25s |
| `phase15_C2b_closure_call` | 3/3 27s | 3/3 25s | 3/3 33s | 3/3 26s |
| `phase15_C5_closure_eq` | 5/5 26s | 5/5 31s | 5/5 26s | 5/5 27s |
| `phase15_CR1_CR5_closure_heap` | 5/5 28s | 5/5 29s | 5/5 27s | 5/5 29s |
| `phase15_A2a_atomicir_audit` | 9/9 36s | 9/9 33s | 9/9 30s | 9/9 29s |
| `phase15_A2a_atomize` | 4/4 30s | 4/4 28s | 4/4 26s | 4/4 27s |
| `phase15_A2a_chokepoint_audit` | 3/3 10s | 3/3 7s | 3/3 8s | 3/3 9s |
| `phase15_A2a_guardcond_pin` | 2/2 29s | 2/2 23s | 2/2 24s | 2/2 23s |
| `phase15_CR2_cachekey` | 6/6 5s | 6/6 5s | 6/6 4s | 6/6 5s |
| `163rev_enum_valueshapes` | 9/9 25s | 9/9 26s | 9/9 26s | 9/9 29s |
| `163rev_transparent_result` | 4/4 24s | 4/4 32s | 4/4 29s | 4/4 32s |
| `a3_closure_iterators` | 11/11 34s | 11/11 32s | 11/11 34s | 11/11 34s |
| `h_verification` | 18/18 34s | 18/18 29s | 18/18 32s | 18/18 27s |
| `h_witness` | 11/11 28s | 11/11 26s | 11/11 27s | 11/11 23s |
| `phase12_phase_closure` | 1/1 4s | 1/1 5s | 1/1 5s | 1/1 8s |
| `phase12_witnesses` | 10/10 26s | 10/10 23s | 10/10 23s | 10/10 25s |
| `phase14_b2_forcephases` | 3/3 4s | 3/3 6s | 3/3 3s | 3/3 5s |
| `phase15_C1_ir` | 7/7 25s | 7/7 20s | 7/7 21s | 7/7 19s |
| `phase15_CR10_regex_overflow` | 5/5 7s | 5/5 7s | 5/5 7s | 5/5 6s |
| `phase15_N2_kindgate_audit` | 5/5 4s | 5/5 5s | 5/5 4s | 5/5 5s |
| `phase15_r13_closure_ref` | 1/1 20s | 1/1 25s | 1/1 20s | 1/1 28s |
| `phase15_S6a_regex_parser` | 21/21 9s | 21/21 6s | 21/21 13s | 21/21 11s |
| `phase15_S6b_regex` | 5/5 29s | 5/5 25s | 5/5 29s | 5/5 25s |
| `phase16_R16_1_arithcheck_foundation` | 22/22 10s | 22/22 9s | 22/22 8s | 22/22 5s |
| `phase16_R16_5_overflow_thru_closure` | 3/3 22s | 3/3 22s | 3/3 22s | 3/3 22s |
| `r14_case2_degrade` | 2/2 27s | 2/2 31s | 2/2 27s | 2/2 28s |
| `r14_continue_guard` | 10/10 22s | 10/10 23s | 10/10 23s | 10/10 20s |
| `r6_b1_stringbacked` | 7/7 23s | 7/7 23s | 7/7 23s | 7/7 22s |
| `r6_b4_readcstring` | 13/13 24s | 13/13 22s | 13/13 24s | 13/13 25s |
| `r6_b7r_bytescan` | 26/26 30s | 26/26 31s | 26/26 28s | 26/26 34s |
| `r6_itesv_mergedegrade` | 11/11 31s | 11/11 34s | 11/11 27s | 11/11 57s |
| `r6_lows_declines` | 15/15 41s | 15/15 78s | 15/15 64s | 15/15 104s |
| `r6_n14_seqops` | 25/25 122s | 25/25 65s | 25/25 96s | 25/25 64s |
| `r6_n16_closure_zerodefault` | 10/10 63s | 10/10 44s | 10/10 49s | 10/10 45s |
| `r6_n49_dottedfield_mutation` | 8/8 42s | 8/8 48s | 8/8 41s | 8/8 55s |
| `r6_nulwitness` | 14/14 55s | 14/14 55s | 14/14 65s | 14/14 56s |
| `r6_r2_zerodefault_result` | 25/25 62s | 25/25 64s | 25/25 63s | 25/25 44s |
| `r6_r6_emit_roundtrip` | 102/102 19s | 102/102 15s | 100/100 12s | 100/100 15s |
| `rectify_mutation` | 6/6 38s | 6/6 45s | 6/6 37s | 6/6 61s |
| `rfc0005_s0_exhibit` | 10/10 47s | 10/10 63s | 10/10 66s | 10/10 71s |
| `rfc0005_s10_replay_verdict` | 31/31 71s | 31/31 66s | 31/31 77s | 31/31 84s |
| `rfc0005_s11_surface` | 34/34 92s | 34/34 106s | 34/34 102s | 34/34 122s |
| `rfc0005_s1c_verdict` | 24/24 91s | 24/24 120s | 24/24 110s | 24/24 89s |
| `rfc0005_s1_lattice` | 23/23 49s | 23/23 63s | 23/23 49s | 23/23 57s |
| `rfc0005_s2_replay` | 15/15 52s | 15/15 75s | 15/15 49s | 15/15 74s |
| `rfc0005_s3_monotonicity` | 27/27 53s | 27/27 77s | 27/27 65s | 27/27 69s |
| `rfc0005_s4_alloc` | 20/20 55s | 20/20 62s | 20/20 53s | 20/20 63s |
| `rfc0005_s5_str` | 35/35 55s | 35/35 57s | 35/35 56s | 35/35 56s |
| `rfc0005_s6a_budget` | 31/31 50s | 31/31 48s | 31/31 44s | 31/31 40s |
| `rfc0005_s6b_ops` | 44/44 49s | 44/44 52s | 44/44 48s | 44/44 55s |
| `rfc0005_s8aa_remainder` | 24/24 71s | 24/24 59s | 24/24 64s | 24/24 59s |
| `rfc0005_s8ab_letaudit` | 28/28 78s | 28/28 82s | 28/28 71s | 28/28 92s |
| `rfc0005_s8ae_remainder` | 16/16 104s | 16/16 142s | 16/16 220s | 16/16 134s |
| `rfc0005_s8ag_indexsplit` | 15/15 85s | 15/15 68s | 15/15 77s | 15/15 71s |
| `rfc0005_s8ai_semantic` | 25/25 241s | 25/25 256s | 25/25 257s | 25/25 249s |
| `rfc0005_s8am_remainder` | 29/29 85s | 29/29 96s | 29/29 75s | 29/29 106s |
| `rfc0005_s8ap_remainder` | 36/36 128s | 36/36 132s | 36/36 123s | 36/36 131s |
| `rfc0005_s8aq_remainder` | 13/13 70s | 13/13 64s | 13/13 71s | 13/13 78s |
| `rfc0005_s8bb_captures` | 13/13 135s | 13/13 135s | 13/13 133s | 13/13 133s |
| `rfc0005_s8bb_capvalues` | 1/1 40s | 1/1 57s | 1/1 40s | 1/1 53s |
| `rfc0005_s8bb_capvalues_lf` | 1/1 55s | 1/1 116s | 1/1 54s | 1/1 126s |
| `rfc0005_s8bb_capvalues_plus` | 1/1 42s | 1/1 98s | 1/1 42s | 1/1 88s |
| `rfc0005_s8bb_constructs` | 7/7 69s | 7/7 75s | 7/7 69s | 7/7 73s |
| `rfc0005_s8bb_exhaustive` | 2/2 52s | 2/2 32s | 2/2 55s | 2/2 30s |
| `rfc0005_s8bb_selection` | 4/4 69s | 4/4 39s | 4/4 49s | 4/4 68s |
| `rfc0005_s8b_substitutions` | 26/26 46s | 26/26 74s | 26/26 74s | 26/26 68s |
| `rfc0005_s8g_models` | 38/38 77s | 38/38 58s | 38/38 69s | 38/38 66s |
| `rfc0005_s8i_models` | 39/39 58s | 39/39 74s | 39/39 73s | 39/39 67s |
| `rfc0005_s8j_exits` | 45/45 70s | 45/45 68s | 45/45 61s | 45/45 71s |
| `rfc0005_s8k_bounds` | 19/19 84s | 19/19 54s | 19/19 81s | 19/19 56s |
| `rfc0005_s8m_exits` | 32/32 64s | 32/32 72s | 32/32 76s | 32/32 75s |
| `rfc0005_s8_scope` | 28/28 62s | 28/28 64s | 28/28 61s | 28/28 52s |
| `rfc0005_s8s_precision` | 29/29 92s | 29/29 144s | 29/29 92s | 29/29 143s |
| `rfc0005_s8v_termination` | 7/7 57s | 7/7 67s | 7/7 77s | 7/7 59s |
| `rfc0005_s8w2_hotfix` | 4/4 57s | 4/4 61s | 4/4 58s | 4/4 56s |
| `rfc0005_s8w_remainder` | 23/23 83s | 23/23 87s | 23/23 92s | 23/23 86s |
| `rfc0005_s8x_vm_alias` | 7/7 10s | 7/7 17s | 7/7 18s | 7/7 9s |
| `rfc0005_s8z_remainder` | 37/37 113s | 37/37 127s | 37/37 110s | 37/37 140s |
| `rfc0005_s9_vetoes` | 19/19 61s | 19/19 82s | 19/19 68s | 19/19 87s |
| `snd1b_closure_uncertain_axiom` | 4/4 48s | 4/4 74s | 4/4 65s | 4/4 68s |

## Different mechanisms, reported and not fixed here (also in the RFC under "As landed (S8bi)")

- **SOUNDNESS:** a huge `n` in `newSeq` is modelled as succeeding, where Nim runs out of memory or aborts.
- **PRECISION:** set-typed values, `set[T]` params and builtin-set `incl`/`excl` are unclassified.
- **PRECISION:** `let r = re"(ab"` declines as `feUnsupportedExprKind nnkCallStrLit`, although Nim always raises `RegexError` there.
- **PRECISION:** `newSeqUninit` taints the whole path even when no element is read.
- **PRECISION:** set literals with non-constant elements still decline.

## Notes

- The harness lives outside the repo, under `/home/corey/tmp-usage/work/s8bi-work/`:
  - `runone.sh` and `pass.sh` (restart-safe, at most 3 runs at once, honours the pause flag);
  - `diff.sh` (the per-check diff and the walker-fault grep);
  - `table.md`;
  - per-run logs in `results/<tree>.<z3>/`.
- The pass honoured the pause flag three times (about 15:32-15:49, briefly at 16:11, and 16:30-17:45), with no runs started while it was set.
