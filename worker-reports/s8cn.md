# S8cn report

**DONE: bb1031cae56b0a8374b78e724357fb4c3631efbb** on `rfc-0005-s8cn`
Base afce42a, merged with batch 9 (e497dcf). Walker **251, provisional**. Numbers 252, 253 and 256 are now on other origin branches, so the merge must set the final number. The CR2 pin and the seqview floor move with it.

## Soundness bugs

All were confirmed against native execution. Probes and logs are in `reports-out/`.

### Release blockers sent to the coordinator; all fixed

| # | Shape | e497dcf | 6cbfe8f | Probe |
|---|---|---|---|---|
| 1 | `lent` loop or cursor over memory the body may write | false verdict | better than channel | `s8cn_release_blocker_probe.nim` |
| 2 | `gWrite(gs)`, `gtWrite(gt)`: global by value, callee writes it | clean false | sxUnknown (weInternalWalkerFault) | `s8cn_release_blocker_probe2.nim` |
| 2 | `rab(t["a"], t, "a")` | false | false | `s8cn_release_blocker_probe2.nim` |
| 3 | `cg_old`, `cl_old`, `cv_old`: target in a declined closure call's body | false sxSat | sxUnknown | `s8cn_release_blocker_probe4.nim` |

Accepted split: S8cn owns the ds, dt and dv forms. S8cq owns `inner(s)` and `outerR(gs)`, which are not fixed here.

On blocker 1, `ll_*` and `lg_*` depend on the memory-manager setting. `tk_*` is correct natively, so it is not a false verdict on the default setting.

### Old bugs, also on 6cbfe8f; fixed

- **Caller's branches missing in a closure body:** `if n != 77: f(n)` with `a == 77` in the body gave false sxSat for a var proc value, the `n > 100` form and a lambda. The direct call was already sxUnsat. Probe: `s8cn_release_blocker_probe3.nim`.
- **`tw_copy`:** `two(s[0], s[0])` with a target in the callee's body gave false sxSat on both shas. Probe: `s8cn_callee_target_probe.nim`.
- **`tw_copy` label wording (coordinator's question):** describe it as "a target in a callee body reached ahead of the call's own decline", an old false sxSat and not a channel regression. It now declines.

### Fixed earlier in the slice

- `hp_live` / `hp_dead`: a pointer to the view.
- `wr_live`: a raise lost a view write on a by-value Table.
- `tc1_shared` / `tc1_copy`: a cursor in a callee.
- `rh_lost`: a key added, then a write.
- Retraction: `ba_dead` was not a bug. `x = 3` is a live witness; my native run only tried `x = 5`.

### `closureCallIR` check (coordinator's question)

Its declines do stand in the preamble, but the bug arrived another way. A closure body descends from a fresh path, with no taint and an empty pc, so neither the pending decline nor the caller's branches reached a target in it.

### The 6cbfe8f fault (coordinator's question)

The fault is broader than `dSeq`. A callee writing an element of a global seq the caller assigned hit `weInternalWalkerFault` in all four shapes tried: no argument, a by-value global, another argument and a `var` global (`s8cn_6cb_fault_probe.nim` and its log). Earlier observation: `gRead(gs)`, `gs = s0` then read, a literal, an int global and a Table assign are not absorbed and were sxSat clean. Main's sxUnknown on these shapes comes from that fault, so it is partly incidental.

## Design

- **Lent and let:** `lentLoopDecline`, `letCursorDecline` and the write-reach helpers in `dsl_parser`.
  - Declined: seq and openArray `items`, Table `values` and `keys`, non-scalar `pairs` or array `items`, and a `let` over a seq, string, Table, set or holder that is read and may be written after.
  - Decided: scalar `pairs`, array `items`, scalar Table `pairs`, `mitems` and `mpairs` by substitution, an unused loop variable, `var c = s`, an array `let`, and no write at all.
- **By value:** `byValueTouch`, checked at the top of the argument loop and before `userCallStmt`; it sees through conversions and `toOpenArray`. A `var`-returning call as a `var` actual declines.
- **Declines before the call:** all seven in `userCallStmt` moved from write-backs to the preamble.
- **Closure body:** starts tainted with the call's pending decline and the caller's taint (`carriedDegrade`), and a hit is solved under `closureBodyCallerPc`.
- **Step 1e:** runs after S8by's facts-first SAT too, and each probe keeps to the caller's budget. This fixed a batch 9 merge interaction.
- **`let` proc values:** resolved to direct calls (`devirtProcLets`), except one variable passed twice, which stays a closure call and is decided (S8bh).

## RED and GREEN

- **Lent suite:** RED on e497dcf in `gate/lent_red_chan.log`; GREEN at bb1031c.
- **Closure pins:** RED through probes 3 and 4 on e497dcf, plus probe 3 on 6cbfe8f; GREEN at bb1031c.
- **`s8cn_probe`:** RED in `g52` at 8162a86; GREEN at abd5436 and bb1031c.
- **Native grid (9 settings):** `lentnative` was green on all nine with `s8cn-work/nat.sh` at an earlier sha. The file is unchanged since fd2aabf. At bb1031c it ran only in the gate and on Windows, so the grid was **not** re-run there.

## Gates at bb1031c

Gate `g54` ran from a worktree detached at bb1031c, under machine load shared with other slices. Results: Z3 5.1 c 85/85, Z3 4.13.4 c 85/85, cpp 8/8. `s8cn_step1d` ran alone on 5.1.

This is the slice's own list, not the full corpus. The full corpus ran only on Windows: all 550 files, 22 of 22 symex-mingw jobs green.

**Windows at bb1031c, all success (observed):**

- symex-mingw: 41549687189
- fuzzer-mingw: 41549686845
- fuzzer-msvc: 41549686840

Each cell below is rc / seconds, including compile. The Windows column is run wall time from the corpus log.

| Suite | Z3 5.1 c | Z3 4.13.4 c | Z3 5.1 cpp | Windows wall |
|---|---|---|---|---|
| phase15_CR2_cachekey | 0 / 5s | 0 / 7s | - | 0s |
| phase15_N2_kindgate_audit | 0 / 7s | 0 / 10s | - | 7.5s |
| r6_n36_raise_class_audit | 0 / 5s | 0 / 8s | - | 0.5s |
| r6_r6_emit_roundtrip | 0 / 12s | 0 / 14s | - | 0s |
| rfc0005_b8_integration | 0 / 70s | 0 / 89s | - | 10.7s |
| rfc0005_b9_integration | 0 / 68s | 0 / 81s | 0 / 63s | 11.1s |
| rfc0005_s1b_kinds | 0 / 44s | 0 / 64s | - | 0.9s |
| rfc0005_s7_closure | 0 / 55s | 0 / 61s | - | 2.2s |
| rfc0005_s8bb_replace | 0 / 72s | 0 / 121s | - | 38.8s |
| rfc0005_s8bc_remainder_c | 0 / 104s | 0 / 289s | - | 69.8s |
| rfc0005_s8bh_remainder | 0 / 97s | 0 / 109s | - | 2.5s |
| rfc0005_s8bl_borrow | 0 / 57s | 0 / 50s | - | 0.2s |
| rfc0005_s8bl_gaps | 0 / 89s | 0 / 75s | - | 18.1s |
| rfc0005_s8bl_magics | 0 / 68s | 0 / 52s | - | 0.4s |
| rfc0005_s8bl_magicscan | 0 / 66s | 0 / 52s | - | 0.1s |
| rfc0005_s8bl_pairloop | 0 / 72s | 0 / 52s | - | 6.8s |
| rfc0005_s8bl_seqops | 0 / 66s | 0 / 51s | - | 0.7s |
| rfc0005_s8bl_setlen | 0 / 77s | 0 / 50s | - | 2.4s |
| rfc0005_s8bp_isolation | 0 / 60s | 0 / 65s | - | 5.4s |
| rfc0005_s8bs_addrglobal | 0 / 77s | 0 / 54s | - | 0.7s |
| rfc0005_s8bs_byref | 0 / 81s | 0 / 55s | - | 0.7s |
| rfc0005_s8bs_byvalue | 0 / 69s | 0 / 47s | - | 0.6s |
| rfc0005_s8bs_iterparams | 0 / 71s | 0 / 56s | - | 1.2s |
| rfc0005_s8bt_caps | 0 / 38s | 0 / 24s | - | 18.5s |
| rfc0005_s8bt_caps_b | 0 / 36s | 0 / 27s | - | 9.9s |
| rfc0005_s8bt_caps_c | 0 / 61s | 0 / 35s | - | 2.9s |
| rfc0005_s8bt_jit | 0 / 28s | 0 / 18s | - | 48.3s |
| rfc0005_s8bt_jit_langs | 0 / 19s | 0 / 12s | - | 23.4s |
| rfc0005_s8bt_jit_langs_b | 0 / 16s | 0 / 10s | - | 11.2s |
| rfc0005_s8bt_jit_langs_c | 0 / 16s | 0 / 12s | - | 15.8s |
| rfc0005_s8bt_jit_langs_d | 0 / 18s | 0 / 12s | - | 26s |
| rfc0005_s8bt_jit_langs_e | 0 / 14s | 0 / 9s | - | 16.4s |
| rfc0005_s8bt_jit_langs_f | 0 / 20s | 0 / 14s | - | 21.5s |
| rfc0005_s8bt_jit_replace | 0 / 21s | 0 / 16s | - | 13.5s |
| rfc0005_s8bt_jit_replace_b | 0 / 21s | 0 / 15s | - | 8.6s |
| rfc0005_s8bt_jit_replace_c | 0 / 19s | 0 / 13s | - | 8.7s |
| rfc0005_s8bt_libversion | 0 / 50s | 0 / 39s | - | 0.3s |
| rfc0005_s8bt_limit | 0 / 21s | 0 / 18s | - | 21.6s |
| rfc0005_s8bt_limit_b | 0 / 19s | 0 / 13s | - | 21.1s |
| rfc0005_s8bt_limit_c | 0 / 18s | 0 / 14s | - | 25.2s |
| rfc0005_s8bt_limit_d | 0 / 18s | 0 / 13s | - | 14.4s |
| rfc0005_s8bt_limit_langs | 0 / 68s | 0 / 52s | - | 10s |
| rfc0005_s8bt_replace_facts | 0 / 13s | 0 / 8s | - | 9.4s |
| rfc0005_s8bt_replace_lemmas | 0 / 77s | 0 / 57s | - | 8.2s |
| rfc0005_s8bt_skipname | 0 / 17s | 0 / 14s | - | 19.9s |
| rfc0005_s8bt_skipname_b | 0 / 19s | 0 / 15s | - | 24.9s |
| rfc0005_s8bt_skipname_c | 0 / 18s | 0 / 14s | - | 29.2s |
| rfc0005_s8bt_skipname_d | 0 / 17s | 0 / 13s | - | 30.1s |
| rfc0005_s8bt_skipname_e | 0 / 20s | 0 / 14s | - | 18.7s |
| rfc0005_s8bt_skipname_f | 0 / 22s | 0 / 16s | - | 33.9s |
| rfc0005_s8bt_skipname_langs | 0 / 31s | 0 / 21s | - | 50.3s |
| rfc0005_s8bt_utf | 0 / 12s | 0 / 10s | - | 16s |
| rfc0005_s8bt_utf_any | 0 / 24s | 0 / 15s | - | 17s |
| rfc0005_s8bt_utf_any_b | 0 / 16s | 0 / 15s | - | 12.1s |
| rfc0005_s8bt_utf_any_c | 0 / 32s | 0 / 29s | - | 44.1s |
| rfc0005_s8bt_utf_any_d | 0 / 30s | 0 / 24s | - | 22.5s |
| rfc0005_s8bt_utf_any_e | 0 / 34s | 0 / 33s | - | 14.6s |
| rfc0005_s8bt_utf_b | 0 / 12s | 0 / 8s | - | 10.8s |
| rfc0005_s8bt_utf_c | 0 / 12s | 0 / 10s | - | 13.1s |
| rfc0005_s8bt_utf_d | 0 / 12s | 0 / 9s | - | 11.8s |
| rfc0005_s8bt_utf_e | 0 / 11s | 0 / 9s | - | 8.9s |
| rfc0005_s8bx_extractraise | 0 / 64s | 0 / 68s | - | 12.4s |
| rfc0005_s8bx_iterchange | 0 / 56s | 0 / 61s | - | 2.8s |
| rfc0005_s8bx_mpairs | 0 / 67s | 0 / 74s | - | 10.3s |
| rfc0005_s8bx_setlenstr | 0 / 62s | 0 / 62s | - | 1.9s |
| rfc0005_s8bx_witnessdrift | 0 / 55s | 0 / 51s | - | 0.1s |
| rfc0005_s8ca_calls | 0 / 69s | 0 / 49s | - | 1.2s |
| rfc0005_s8ca_closures | 0 / 61s | 0 / 46s | - | 0.2s |
| rfc0005_s8ca_closures_heap | 0 / 67s | 0 / 57s | - | 0.8s |
| rfc0005_s8ca_derefmut | 0 / 73s | 0 / 51s | - | 0.9s |
| rfc0005_s8ca_procvals | 0 / 74s | 0 / 47s | - | 2.2s |
| rfc0005_s8ca_resize | 0 / 73s | 0 / 47s | - | 1.6s |
| rfc0005_s8ca_stack | 0 / 84s | 0 / 49s | - | 14.3s |
| rfc0005_s8ca_strings | 0 / 77s | 0 / 47s | - | 13.3s |
| rfc0005_s8ca_strings_byvalue | 0 / 57s | 0 / 30s | - | 0.6s |
| rfc0005_s8ca_views | 0 / 63s | 0 / 39s | - | 1s |
| rfc0005_s8cn_lent | 0 / 82s | 0 / 115s | 0 / 85s | 6.3s |
| rfc0005_s8cn_lentnative | 0 / 5s | 0 / 5s | 0 / 5s | 0s |
| rfc0005_s8cn_probe | 0 / 111s | 0 / 104s | 0 / 92s | 0.2s |
| rfc0005_s8cn_seqview | 0 / 104s | 0 / 98s | 0 / 81s | 13.4s |
| rfc0005_s8cn_step1d | 0 / 182s | 0 / 157s | - | 68.9s |
| rfc0005_s8cn_views | 0 / 114s | 0 / 127s | 0 / 84s | 52.1s |
| rfc0005_s8cn_views_b | 0 / 116s | 0 / 131s | 0 / 96s | 53.4s |
| rfc0005_s8cn_views_c | 0 / 124s | 0 / 122s | 0 / 103s | 121.1s |
| rfc0005_s8k_bounds | 0 / 81s | 0 / 62s | - | 3.9s |

The Windows wall time for some files reads 0 or 0.2 s (`s8cn_probe`, `lentnative`) although their tests ran; `s8cn_probe`'s five `[OK]` lines are in the log. Treat those two figures as unreliable.

**Slowest symex-mingw files:**

- rfc0005_s8cn_views_c: 121 s
- configdefaults_depth: 87 s
- rfc0005_s8bc_remainder_c: 70 s
- rfc0005_s8cn_step1d: 69 s
- rfc0005_s8cn_views_b: 53 s
- rfc0005_s8cn_views: 52 s
- rfc0005_s8bt_skipname_langs: 50 s
- rfc0005_s8bj_verbs: 50 s

**Open liveness note:** `s8cn_views_c` is now the slowest file in the corpus, at about 121 s against the 240 s kill. Most of that is one test, "the callee removes a symbolic key". The unsplit file was killed at 240 s at abd5436.

## Different mechanisms (also in the RFC)

SOUNDNESS, not fixed here: `inner(s)` and `outerR(gs)`, owned by S8cq.

Not mine: PCRE limits and regex (S8cf), product overflow and `var openArray` copy (S8cg), `tsymex_configdefaults_depth` (S8ci).

## Declines for RFC-0016 (all PRECISION)

- A lent loop with a possible write, and a `let` cursor.
- A Table `keys` loop that writes the Table, even with no key added. `ti_grow` at `a == 0` is now sxUnknown, moved from S8bl's sxSat pin.
- A by-value actual reached by name, reads included. The b9 `sReadOnly` pin is now feUnsupportedOp.
- Non-scalar `pairs` and array `items`.
- A `let` over a formal with any ptr or ref write (no type filter).
- A `var`, parameter or computed proc value with a view and Table (`closureTakesView`).
- By global name (`sqG`, `gw`).
- `f(s[i], s[0], s)` and `f(s[0], s[0], s)`.
- A pointer plus a Table call.
- A mutated local copy.
- `t.clear` and `t.pop`.
- `Table[string, VObj]`.
- A non-scalar by-value view.
- A pointer plus 11 inserts, which exceeded 1400 s (liveness); the pin uses one insert.
- `nl2_other_live` and `nl2_same_dead`, repinned to sxUnknown.
- Two-entry `del`, which depends on the hash.

## Pins moved

- `s8k_bounds`: `needs130` under a small budget is now sxSat with a correct witness, because step 1e's first candidate answers by evaluation. The decline moved to `needs130Mixed`.
- `s8bc_remainder_c`: `ti_grow`, as listed above.
- `s1b_kinds`: `carriedDegrade` added to the allowed routines. It records nothing itself; the taint it carries was recorded where it arose. This is the pin a reviewer should look at first.
- b9: val, var, hold, ghold and void are decided by devirt; gseq, gtab and ro are declines.

## Process slips

- Three earlier slips, recorded in the progress file: two process-rule slips and one main-baseline probe launched while `PAUSE_SLICE_TESTS` existed.
- **My gate list missed corpus suites:** Windows at abd5436 caught failures in six suites the local gate had not run (`s8k_bounds`, `s8bh_remainder`, `s1b_kinds`, `N2_kindgate_audit`, `r6_emit_roundtrip`, `s8bc_remainder_c`), plus `s8cn_probe` and `s8cn_views`, which the gate does run. All came from this slice and are fixed.
- **Self-caught:** an RFC edit slice nearly deleted 12.5k lines; restored before commit, no impact.
- **Stale comment:** the walker note still names `checkCappedSteps`, removed by batch 9. I left it so as not to move the certified sha.

## Decisions needed

1. The final walker number at merge.
2. Whether to accept the repinned `ti_grow` decline.
3. Whether to accept `carriedDegrade` in the `s1b_kinds` allowed routines.
