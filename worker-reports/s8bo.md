# S8bo -- DONE (item 5 escalated as a BLOCKER, implemented on the base as the job directs)

- **sha:** 10262dd (branch `rfc-0005-s8bo`; history `ebb9b8a` docs-open, `dcafb30` fix, `46efe0a` test, `10262dd` docs)
- **base:** ef08ada (origin/rfc-0005-s8be, walker 205; base S8ax)
- **walker:** 216 (CR2 `== "216"` updated and run; `>= 216` floor in each of the three S8bo suites)
- **Verified tree:** the source (`src/`) at 10262dd is byte-identical to 7a88288, where the full verification list ran. The later commits only split S8be part b into b and c (re-run on all three configurations) and edit the RFC.

## Scratch-clobber incident
- **What came from the clobbered shared-scratchpad script:** my first Z3 5.1 C verification batch. It was run by `runall.sh` in the shared session scratchpad, started at bc2d08d, with logs in `scratchpad/r51/`. Its process vanished partway, and another agent's script of the same name overwrote `runall.sh` (timestamp 03:31). I discarded all 49 partial results it had written, including an N2_kindgate failure. That failure was real, and fixed in 7a88288.
- **Other files there:** three per-test logs (`s8be.log`, `s6b.log`, `nil.log`). They came from direct `scripts/dt-bounded.sh` runs, not a scratchpad script, and were read the moment each run ended. Their suites were re-run anyway.
- **Re-run:** every suite in the verification list was re-run, before this report, from my own runner `/home/corey/tmp-usage/work/s8bo-work/runall.sh`. That covers Z3 5.1 c, Z3 4.13.4 c and Z3 5.1 cpp, with logs in `s8bo-work/{r51,r413,rcpp,bc51,bc413,bccpp}`. This DONE rests only on those re-run results.

## RED and GREEN observed
Every pin was run RED on the pre-change code (ef08ada, or the stashed source) before the change. GREEN was observed on Z3 5.1 c, then all suites on both Z3 versions plus cpp.

**1 -- isNil and magics (`tsymex_rfc0005_s8bo_nil`)**
- RED, `r.isNil` on `ref object` and `ref int` parameters: `sxUnsat`, errors `[]`. Same for a `ptr` and a local `ref` (probe).
- RED, `pointer(p) == nil`: `weInternalWalkerFault` "coerceIntLit: composite prototype".
- RED, `cast[pointer](r) == nil`: `feUnsupportedExprKind`.
- RED, `ashr(-1, 1) == -1`: `sxUnsat`, errors `[]`.
- RED, `wasMoved(x)` and `move(x)`: compile failure, "Expected nnkIdentDefs, got nnkSym".
- GREEN: all 13 OK.

**2 -- plain-object cell (`_cells`)**
- RED, all 6 pins (stored, stored-read, passed, whole `p[]` write, whole `p[]` read, ref-object whole): `sxUnknown` with `seUnsupportedCompoundSortLeaf`.
- GREEN: `sxSat` / `sxUnsat` as pinned.

**3 -- whole seq assignment**
- RED: a callee repeating the held value, and `s = t` after `let t = s`, both gave a confirmed `sxSat` through the dangling pointer.
- GREEN: both decline (`feUnsupportedOp`, "freed").

**4 -- arm-field pointer as a value**
- RED: stored, passed to a keeper, and same-arm reassignment all gave `sxUnknown` (`feUnsupportedExprKind` / `heUnsafeCast`).
- GREEN: `sxSat` / `sxUnsat`. A rearm declines ("changed arm"), and the wrong arm at `addr` is `sxRaised FieldDefect`.

**5 -- seq of objects**
- RED: `feUnsupportedExprKind` on the `addr`.
- GREEN: the element cell declines with `seNestedSeqUnsupported`, "elements the walk does not hold".

**6 -- abandoned replay (`_replay`)**
- RED: the reader's replay, run while the abandoned writer was released mid-run, gave `sxSat` with no `feReplayTimedOut`.
- GREEN: not `sxSat`; `feReplayTimedOut` "still running". After the drain, the replay confirms `sxSat` again.

**7 -- threadvar**
- RED: `sxUnknown` (`feReplayRefuted`), and the write was not handed back (`s8boTvCount` was 0).
- GREEN: `sxSat`, and `s8boTvCount == 1`.

**7 -- stack**
- RED: the process died (SIGSEGV) on a 3 MiB frame in the replay.
- GREEN: `sxSat`. The pin is skipped when the calling thread's stack is under 6 MiB, as on Windows.

**Found during verification**
- RED: `tsymex_phase15_N2_kindgate_audit` flagged the new threadvar scan's bare routine-kind gate (also red on Windows at bc2d08d).
- GREEN: it now resolves through `resolveRoutineImpl`.
- RED: S6b's unsafe-cast pin went `sxUnsat` (Windows run at 1eba21e too), because an arm field's pointer is no longer an unsafe cast.
- GREEN: the pin moved to `cast[ptr int](n)`.

## Soundness bugs found (all fixed here)
1. `isNil` was a false `sxUnsat` with errors empty. The cause was a general one: any bodiless `{.magic.}` was walked as an empty body and became a constant. `ashr` was a second false `sxUnsat`.
2. A whole seq assignment of an equal value term left its element cells live. A read through the dangling pointer was a confirmed `sxSat` on memory Nim had freed (UB).
3. An abandoned replay's late write could confirm a later replay: a confirmation no single-threaded run of the routine makes.
4. Crashes: `pointer(p) == nil` was a walker fault; `wasMoved` / `move` failed the compile; a global of a type whose record holds a `when` (system `Channel`) named in an opaque routine failed the compile; a replay of a routine with a large frame killed the process.

## Design per item
1. **isNil and magics.**
   - `isNil(x)` lowers through `parseNilCompare`, factored out of the R5 `== nil` arm. `nilSideCore` strips a conversion or cast to `pointer` of a ref/ptr.
   - A proc value declines (`ceUnsupportedHof`), exactly as `== nil` does.
   - Guard: in `ensureProcRegistered`, a `{.magic.}` with a stub body (`stubBody`: empty, or only comments and `runnableExamples`) declines with `feUnsupportedOp` "compiler magic ... has no symbolic model". A routine with non-`IdentDefs` formals (a generated hook) declines too.
2. **Plain-object cells.** `objectSlots`, `objectCellValue` and `objectCellStore` generalise S8be's variant cell to `fieldSplitObject` (an object with named fields). A whole `p[]` read or write of such a pointee uses them too.
3. **Whole seq assignment.** `syncElemCells` kills a root's cells on `lastWriteTo`, whatever value is written.
4. **Arm-field pointers.**
   - `armFieldCellOf` / `lowerArmFieldCell` in the parser produce `isNew.nAddrField`, which `walkFieldCell` handles. `ElemCell` gains `field` / `tags`.
   - The arm is checked at the `addr` (a `FieldDefect` fork).
   - In `syncElemCells` and `syncElemCellsFromHeap`, a different discriminator term kills the cell. Otherwise the side that changed wins: `armFieldValue` / `withArmField`, with a clash decline if both changed.
5. **Seq-of-object element cells.** `elemCellOf` accepts a seq of named-field objects; `walkElemCell` declines on a placeholder or unbacked seq with `seNestedSeqUnsupported`.
6. **Abandoned replays.**
   - `runReplayBounded` returns `ReplayRun`. Abandoned jobs are kept under a lock, and reaped (joined and freed) once they are seen to end.
   - A replay started while one is still live is `rrContended`, giving `roContended`: a `feReplayTimedOut` hint, never confirmed or refuted.
   - `replayAbandonedLive()` is exported.
7. **Replay fidelity.**
   - `replayThreadMain` runs the body via `runOnStack`, sized by `callerStackSize`:
     - Linux main thread: `RLIMIT_STACK`, on a ucontext coroutine over an mmap'd stack with a guard page;
     - Windows: `GetCurrentThreadStackLimits`, on a fiber;
     - anywhere else: Nim's thread stack.
   - `threadvarsReached` collects the threadvars named in the routine's body or any routine it names, transitively. They are copied into the replay thread and handed back afterwards.
   - If any code cannot be read (a method, a foreign routine, a proc-value call), no threadvar is copied: that gives a fresh thread's state rather than a mixed one.
8. **Suite split.**
   - S8be is split into three files: `_remainder` (items 1-8), `_b` (9-11) and `_c` (12-13).
   - S8bo's pins are in three files: `_nil`, `_cells` and `_replay`.
   - All are registered in `nelli.nimble`; the Windows corpus is derived from it.

## Item 5 escalation (BLOCKER for the batch-4 integrator)
- **Wrong assumption:** the job expected element cells over seqs of objects. This base has no representation of a seq of objects: it is a placeholder with `seqLen == 0`, and every element access declines `seNestedSeqUnsupported`. So the leaf split *is* needed, and it is S8bc's.
- **Evidence:**
  - `types.nim:4231`: `isBackedSeqElemTy` excludes `itTuple`.
  - `runtime.nim:316`: the placeholder seq is forced `seqLen == 0`.
  - A probe gave every access to `@[P(..), P(..)]` the result `seNestedSeqUnsupported`.
- **What I did, as the job directs:** implemented on the base. The parser and cell side are live: the cell value is `objectCellValue`. The cell declines where no element is held.
- **For the integrator, on the leaf-split base:**
  - remove `walkElemCell`'s placeholder / `isBackedSeqElemTy` decline;
  - give `seqElemAt` and `withElem` (used by `syncElemCells` and `syncElemCellsFromHeap`) the leaf-split object element read and write;
  - make `sameSeqLen` compare the leaf-split length term.
  - `objectCellStore` / `objectCellValue` already handle the object.

## Item 8 timing
- I measured serially at load 10-16 on 8 cores (other agents' containers were running alongside), so the 60 s budget cannot be measured on this box now.
- The floor is a one-test `symexFind` file: 57 s (c) and 76 s (cpp).
- Serial wall times, c / cpp:

| File | c | cpp |
|---|---|---|
| s8bo_nil | 52 s | 89 s |
| s8bo_cells | 69 s | 65 s |
| s8bo_replay | 53 s | 58 s |
| s8be_remainder | 72 s | 61 s |

- `s8be_remainder_b` took 96 / 125 s before I split out `_c`. In the concurrent batch run, `_b` and `_c` each took about 100 s.
- Every file is now within about 20 s of the compile floor; the floor itself is load-dominated.

## Per-suite results
- **Totals across 113 files:** Z3 5.1 c 1674 OK, 0 failed; Z3 4.13.4 c 1674 OK, 0 failed; Z3 5.1 cpp 1673 OK, 0 failed.
- **The one non-zero exit:** `tsymex_configdefaults` on cpp. It exits 1 inside its 24th test ("an explicit finite maxCallDepth also completes cleanly"). The same happens on ef08ada (re-run there): pre-existing, reported below.

| Suite | Z3 5.1 (c) | Z3 4.13.4 (c) | Z3 5.1 (cpp) |
|---|---|---|---|
| tsymex_rfc0005_s8bo_nil | 13 OK / 0 fail | 13 OK / 0 fail | 13 OK / 0 fail |
| tsymex_rfc0005_s8bo_cells | 16 OK / 0 fail | 16 OK / 0 fail | 16 OK / 0 fail |
| tsymex_rfc0005_s8bo_replay | 6 OK / 0 fail | 6 OK / 0 fail | 6 OK / 0 fail |
| tsymex_rfc0005_s8be_remainder | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_rfc0005_s8be_remainder_b | 8 OK / 0 fail | 8 OK / 0 fail | 8 OK / 0 fail |
| tsymex_rfc0005_s8be_remainder_c | 13 OK / 0 fail | 13 OK / 0 fail | 13 OK / 0 fail |
| tsymex_rfc0005_s8ax_remainder | 53 OK / 0 fail | 53 OK / 0 fail | 53 OK / 0 fail |
| tsymex_rfc0005_s2_replay | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_rfc0005_s1_lattice | 23 OK / 0 fail | 23 OK / 0 fail | 23 OK / 0 fail |
| tsymex_phase15_CR2_cachekey | 6 OK / 0 fail | 6 OK / 0 fail | 6 OK / 0 fail |
| tsymex_rfc0005_s8ab_letaudit | 28 OK / 0 fail | 28 OK / 0 fail | 28 OK / 0 fail |
| tsymex_r6_n27_hof_placeholder | 6 OK / 0 fail | 6 OK / 0 fail | 6 OK / 0 fail |
| tsymex_r6_n27_placeholder_read_audit | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_phase15_N2_kindgate_audit | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_configdefaults | 24 OK / 0 fail | 24 OK / 0 fail | 23 OK / 0 fail (exit 1) |
| tsymex_163rev_inert_exclusions | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_rfc0005_s6b_ops | 43 OK / 0 fail | 43 OK / 0 fail | 43 OK / 0 fail |
| tsymex_163audit_w10 | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_163_opaque_transparent | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_163rev_armfield_write | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_163rev_concolic_diagnostics | 25 OK / 0 fail | 25 OK / 0 fail | 25 OK / 0 fail |
| tsymex_163rev_concolic_flip_width | 13 OK / 0 fail | 13 OK / 0 fail | 13 OK / 0 fail |
| tsymex_163rev_concolic_modes | 19 OK / 0 fail | 19 OK / 0 fail | 19 OK / 0 fail |
| tsymex_163rev_degrade_classification | 8 OK / 0 fail | 8 OK / 0 fail | 8 OK / 0 fail |
| tsymex_163rev_inert_argfork | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_163rev_parser_gaps | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_163rev_transparent_guard | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_163rev_transparent_result | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_163rev_variant_armfield | 6 OK / 0 fail | 6 OK / 0 fail | 6 OK / 0 fail |
| tsymex_a2_refvariant_fields | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_a3_closure_iterators | 11 OK / 0 fail | 11 OK / 0 fail | 11 OK / 0 fail |
| tsymex_a6_symlen_hof | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_augmented_assign | 8 OK / 0 fail | 8 OK / 0 fail | 8 OK / 0 fail |
| tsymex_CR2b_paramtype_catchall | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_g1b_concolic | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_g3fix_walkergap | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_g4_cmpwalk | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_g6_algebra | 13 OK / 0 fail | 13 OK / 0 fail | 13 OK / 0 fail |
| tsymex_h_stepC_heapidentity | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_phase12_phase_closure | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_phase12_sink | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_phase12_witnesses | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_phase14_c2_dberrors | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_phase15_A2a_atomicir_audit | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_phase15_C1_ir | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_phase15_C2a_closure_capture | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_phase15_C2b_closure_call | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_phase15_C4_hof | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_phase15_C5_closure_eq | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_phase15_C6_smoke | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_phase15_CR1_CR5_closure_heap | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_phase15_CR21_parseintraise_arg | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_phase15_cr9_lowerInExpr | 6 OK / 0 fail | 6 OK / 0 fail | 6 OK / 0 fail |
| tsymex_phase15_g4_distinct_sort | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_phase15_N1_resolution_gates | 32 OK / 0 fail | 32 OK / 0 fail | 32 OK / 0 fail |
| tsymex_phase15_N3_scan_boundary | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_phase15_r11b_smoke | 11 OK / 0 fail | 11 OK / 0 fail | 11 OK / 0 fail |
| tsymex_phase15_r11_unsafecast | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_phase15_r12_bumps | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_phase15_r13_closure_ref | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_phase15_r1_refsort | 2 OK / 0 fail | 2 OK / 0 fail | 2 OK / 0 fail |
| tsymex_phase15_r5_nil | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_phase15_rereview_drains | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_phase16_R16_1_arithcheck_foundation | 22 OK / 0 fail | 22 OK / 0 fail | 22 OK / 0 fail |
| tsymex_phase16_R16_5_overflow_thru_closure | 3 OK / 0 fail | 3 OK / 0 fail | 3 OK / 0 fail |
| tsymex_q1_sibling_collision | 2 OK / 0 fail | 2 OK / 0 fail | 2 OK / 0 fail |
| tsymex_r11_range_invariant_audit | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_r1b_shortcircuit_oob | 19 OK / 0 fail | 19 OK / 0 fail | 19 OK / 0 fail |
| tsymex_r6_a6r_callwitness | 12 OK / 0 fail | 12 OK / 0 fail | 12 OK / 0 fail |
| tsymex_r6_b5_chained | 9 OK / 0 fail | 9 OK / 0 fail | 9 OK / 0 fail |
| tsymex_r6_itesv_mergedegrade | 11 OK / 0 fail | 11 OK / 0 fail | 11 OK / 0 fail |
| tsymex_r6_lows_declines | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_r6_n13_reassign_seqarm | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_r6_n16_closure_zerodefault | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_r6_n29_seqlit_sortmismatch | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_r6_n36_raise_class_audit | 14 OK / 0 fail | 14 OK / 0 fail | 14 OK / 0 fail |
| tsymex_r6_n36_raise_degrade | 8 OK / 0 fail | 8 OK / 0 fail | 8 OK / 0 fail |
| tsymex_r6_n37_raise_residue | 11 OK / 0 fail | 11 OK / 0 fail | 11 OK / 0 fail |
| tsymex_r6_n40_alloc_totality | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_r6_n42_deref_taint | 15 OK / 0 fail | 15 OK / 0 fail | 15 OK / 0 fail |
| tsymex_r6_n43_parity | 25 OK / 0 fail | 25 OK / 0 fail | 25 OK / 0 fail |
| tsymex_r6_r4_collector_scoping | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_r6_r6_emit_roundtrip | 100 OK / 0 fail | 100 OK / 0 fail | 100 OK / 0 fail |
| tsymex_rectify_effects | 5 OK / 0 fail | 5 OK / 0 fail | 5 OK / 0 fail |
| tsymex_rectify_refs | 1 OK / 0 fail | 1 OK / 0 fail | 1 OK / 0 fail |
| tsymex_rfc0005_s0_exhibit | 10 OK / 0 fail | 10 OK / 0 fail | 10 OK / 0 fail |
| tsymex_rfc0005_s10_replay_verdict | 31 OK / 0 fail | 31 OK / 0 fail | 31 OK / 0 fail |
| tsymex_rfc0005_s11_surface | 34 OK / 0 fail | 34 OK / 0 fail | 34 OK / 0 fail |
| tsymex_rfc0005_s1b_kinds | 18 OK / 0 fail | 18 OK / 0 fail | 18 OK / 0 fail |
| tsymex_rfc0005_s1c_verdict | 24 OK / 0 fail | 24 OK / 0 fail | 24 OK / 0 fail |
| tsymex_rfc0005_s4_alloc | 20 OK / 0 fail | 20 OK / 0 fail | 20 OK / 0 fail |
| tsymex_rfc0005_s5_str | 35 OK / 0 fail | 35 OK / 0 fail | 35 OK / 0 fail |
| tsymex_rfc0005_s6a_budget | 31 OK / 0 fail | 31 OK / 0 fail | 31 OK / 0 fail |
| tsymex_rfc0005_s7_closure | 37 OK / 0 fail | 37 OK / 0 fail | 37 OK / 0 fail |
| tsymex_rfc0005_s8am_remainder | 29 OK / 0 fail | 29 OK / 0 fail | 29 OK / 0 fail |
| tsymex_rfc0005_s8an_remainder | 25 OK / 0 fail | 25 OK / 0 fail | 25 OK / 0 fail |
| tsymex_rfc0005_s8ao_remainder | 11 OK / 0 fail | 11 OK / 0 fail | 11 OK / 0 fail |
| tsymex_rfc0005_s8ap_remainder | 36 OK / 0 fail | 36 OK / 0 fail | 36 OK / 0 fail |
| tsymex_rfc0005_s8as_remainder | 33 OK / 0 fail | 33 OK / 0 fail | 33 OK / 0 fail |
| tsymex_rfc0005_s8b_substitutions | 26 OK / 0 fail | 26 OK / 0 fail | 26 OK / 0 fail |
| tsymex_rfc0005_s8e_scoping | 36 OK / 0 fail | 36 OK / 0 fail | 36 OK / 0 fail |
| tsymex_rfc0005_s8i_models | 39 OK / 0 fail | 39 OK / 0 fail | 39 OK / 0 fail |
| tsymex_rfc0005_s8m_exits | 32 OK / 0 fail | 32 OK / 0 fail | 32 OK / 0 fail |
| tsymex_rfc0005_s8n_precision | 19 OK / 0 fail | 19 OK / 0 fail | 19 OK / 0 fail |
| tsymex_rfc0005_s8p_precision | 30 OK / 0 fail | 30 OK / 0 fail | 30 OK / 0 fail |
| tsymex_rfc0005_s8_scope | 28 OK / 0 fail | 28 OK / 0 fail | 28 OK / 0 fail |
| tsymex_rfc0005_s8s_precision | 29 OK / 0 fail | 29 OK / 0 fail | 29 OK / 0 fail |
| tsymex_rfc0005_s8z_remainder | 37 OK / 0 fail | 37 OK / 0 fail | 37 OK / 0 fail |
| tsymex_rfc0005_s9_vetoes | 19 OK / 0 fail | 19 OK / 0 fail | 19 OK / 0 fail |
| tsymex_snd1b_closure_uncertain_axiom | 4 OK / 0 fail | 4 OK / 0 fail | 4 OK / 0 fail |
| tsymex_snd3_loopdegrade | 7 OK / 0 fail | 7 OK / 0 fail | 7 OK / 0 fail |
| tsymex_snd4_strindex_oob | 8 OK / 0 fail | 8 OK / 0 fail | 8 OK / 0 fail |
| tsymex_tot1_totality_corpus | 21 OK / 0 fail | 21 OK / 0 fail | 21 OK / 0 fail |

## Windows run ids
- **At 4246218**, whose non-docs tree is identical to 10262dd: symex-mingw 37147033113 **success**, fuzzer-mingw 37147032998 **success**, fuzzer-msvc 37147033026 **success**.
- **10262dd itself** differs from 4246218 only under `docs/`, which the workflows' `paths-ignore` skips, so it triggered no run.
- **Earlier reds, both fixed:**
  - bc2d08d / 260aabe symex-mingw (37090077918, 37089934402): the N2 kind-gate audit on the threadvar scan; fixed in 7a88288, which went green (37108464930).
  - 1eba21e symex-mingw (37088866148): S6b's unsafe-cast pin before it was moved.

## Different mechanisms, reported and not fixed here (also in the RFC under "As landed (S8bo)")
- A seq of objects has no element representation on this base; its element cells decline (item 5 escalation). PRECISION.
- `newSeq[T](n)` in a callee fails the whole compile ("node has no type", `classifyType` in `parseCalleeImpl`). Confirmed present on ef08ada. PRECISION (compile failure, no wrong verdict).
- A positional tuple's address cell keeps one heap of its whole value, so a field access through the pointer declines. PRECISION.
- An arm field of a multi-axis case object (`itMultiVariant`) has no field cell; an escaping pointer to one stays `heUnsafeCast`. PRECISION.
- A whole `p[]` read of a plain object does not assert its fields' declared ranges. This is an over-approximation, and replay checks it. PRECISION.
- Every unmodelled magic declines (`swap`, `ashr`, `wasMoved`, `move`, `+%`, ...). PRECISION.
- Replay stack fidelity covers the Linux main thread and Windows. A non-main calling thread on Linux, and other OSes, use Nim's 2 MiB thread stack. PRECISION.
- One abandoned replay that never ends leaves every later replay in the process `roContended`. PRECISION.
- `tsymex_configdefaults` dies under cpp in its round-2 `maxCallDepth` crash pin (the walker's recursion exhausts the native stack). Present on ef08ada. PRECISION.
