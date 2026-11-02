# S8cb -- DONE

- **sha:** 28ab1a7ec0f1d5f136723289be13c304dca7c583 (branch `rfc-0005-s8cb`, origin matches)
- **base:** 136ad60; merge 72b2c2b stacks S8bo (10262dd). Commits on the merge: deea994, bdafb39, a3298b7, a09d879, cb70b96, 01c3132, 28ab1a7.
- **walker:** 243, provisional (S8bz holds 241, S8cf holds 242); renumber at integration if the order changes.
- **Verified tree:** `src/` is unchanged from a09d879 to 28ab1a7. The Linux sweeps ran at a09d879. Later commits touch only the RFC, `nelli.nimble`, four moved pins and the tostr/order split, and each of those suites was re-run on all three configurations (see the table).

## RED and GREEN observed
- RED evidence, run on the pre-change runner or code: `s8cb-work/red-magics.txt`, `red-tostr.txt`, `red-cells.txt`, `red-replay6.txt` (SIGSEGV on a foreign thread), `red-replay7.txt` (disjoint-global replay gave a contended sxUnknown).
- Items 1 and 4 were already exact. They are pinned, with no RED to observe.
- GREEN observed on Z3 5.1 c, Z3 4.13.4 c and Z3 5.1 cpp (table below). The only failures are n42 and n43 on cpp, described under the table.

## Soundness bugs fixed
1. `$char` and `$enum` decimal of an ordinal: false sxUnsat.
2. Negative `$x` had no sign: false sxUnsat; and `$x == ""`: false sxSat.
3. `ensureMove` with a zero result: false sxUnsat and false sxRaised.
4. `threadvarsReached` was keyed by signatureHash, which is the same across routines with the same parameter types. A thread variable behind a same-signature routine was not carried in, so replay refuted a real hit. The key is now routineKey (strVal#symBodyHash).
5. Crash: a 3 MiB frame on a 16 MiB foreign thread made replay SIGSEGV.

Also made exact: the bool-ordering fresh symbol, and string ordering is now modelled.

## Design per item
1. **`newSeq[T](n)` in a callee:** already exact; pinned.
2. **`addr t[i]` on a positional tuple, and tuple or plain-object fields:** a field cell (`fieldCellOf`, `walkFieldCell`, `tupleFieldIx`, `armFieldTags`, `armFieldValue`, `withArmField`). Nested `addr t[1][0]` is not separately pinned and is not claimed.
3. **Multi-axis arm fields:** `fieldMemorySame` kills only when the declaring axis's discriminator changes. Added `multiVariantCellValue` and `multiVariantCellStore`; `addr o` takes the whole object. `sameSymVal` gained an svMultiVariant arm (it previously always reported "changed").
4. **`p[]` range facts:** already asserted; pinned.
5. **Magics modelled:** parseToStr, parseUnsignedOp, parseExitCall, ashr, ord(bool), chr, ensureMove, plain `=dup`, `=sink` statement, quit expression, `@` of openArray, high/low of a value, bool and string order, debugEcho.
   **Declined, with reasons:**
   - `=destroy`, `=trace`, shallowCopy: S8bl table.
   - deepCopy: needs `--deepcopy:on`.
   - `<` and `<=` on pointers: no address order; cast.
   - finished: ADR-0014 D6.
   - GC_ref and GC_unref under ORC: casts.
   - cstring: isNil and `$`.
   - Compile-time magics: folded.
   - `=dup` of an object or tuple: user hook.
   - repr other than modelled: the stdlib body does not end within budget.
   - `$float`: iekStrUnsupported. Holey enum invalid value: also declined.
   - math.toInt: not a magic, not modelled.
6. **Stack size:** `callerStackSize` and `threadStackSize` use pthread_getattr_np on Linux, pthread_get_stacksize_np on macOS, and pthread_attr_get_np on FreeBSD, NetBSD and DragonFly. The main thread keeps RLIMIT_STACK. OpenBSD has no makecontext and stays at 2 MiB. Pinned on Linux with a raw 16 MiB pthread_create. **The other platforms were only checked with `--os:<x> --compileOnly`: Nim level, the C was never compiled, and nothing was run on those hosts.**
7. **Replay footprint:** macro-time `ReplayFootprint` (`replayFootprint`, `routineFootprint`, `scanFootprint`, `isRuntimeCode`, memo `routineFootprints`), `runReplayBounded(body, timeoutMs, footprint = open)` and `reapAbandoned(fp)`. The footprint is open on a method, program proc value, foreign routine or emit, or capturing nested routine. The scan stops at lib/system*, sysatomics and nelli markers. A never-ending replay is pinned with a channel recv; the abandoned thread runs until process exit.
   **Residual SOUNDNESS:** a compiler-inserted hook (`=destroy` naming a variable) is unseen; state shared behind two different C routines is unseen; a runtime hook variable set by the program is unseen.

## Pins moved
- Bool-order fresh vehicle in s2, s10, s11, s8az: now an unwritten module `var` (feGlobalHavoc).
- s7: now a multi-axis result with a `HashSet[string]` arm.
- s6b: bool pins now exact; site count 15 to 14.
- s8bo_nil: ashr now sxSat; the guard pin moved to `isNil(cstring)`.
- 163audit_w10: the degrade moved to `$float(x)`.
- n27: count 120 to 119 (stacking S8bo replaced the marked line in storeSeqElem with withElem).
- N2 kind gate: `userRoutineSymKinds` exported.

## Windows
All three legs succeeded at 28ab1a7 (observed):
- symex-mingw 41483312401
- fuzzer-mingw 41483312581
- fuzzer-msvc 41483312525

Earlier tips:
- cb70b96: symex-mingw 41469522004 failed on stale pins (s11_surface, s8az_remainder, 163audit_w10, n27), which the Linux sweep list did not contain. Its fuzzers 41469521593 and 41469521887 succeeded.
- 01c3132: 41476086885, 41476086835 and 41476087010 all succeeded, but s8cb_tostr took 65 s, which led to the split.

Per-file times from the 28ab1a7 symex-mingw log, for every test file this branch changes. All are under 60 s. Times with a decimal come from the earlier extract; whole seconds come from the log timestamps.

| file | s |
|---|---|
| tsymex_rfc0005_s8cb_cells | 54.8 |
| tsymex_rfc0005_s8cb_magics | 44.3 |
| tsymex_rfc0005_s8cb_order | 50.6 |
| tsymex_rfc0005_s8cb_tostr | 38.3 |
| tsymex_rfc0005_s8cb_replay | 47 |
| tsymex_rfc0005_s10_replay_verdict | 37.2 |
| tsymex_rfc0005_s11_surface | 51.7 |
| tsymex_rfc0005_s2_replay | 49.6 |
| tsymex_rfc0005_s6b_ops | 50.5 |
| tsymex_rfc0005_s7_closure | 49.3 |
| tsymex_rfc0005_s8bo_nil | 49.7 |
| tsymex_rfc0005_s8az_remainder | 41 |
| tsymex_163audit_w10 | 46 |
| tsymex_r6_n27_placeholder_read_audit | 3 |

**Over 60 s:** 39 of the 486 files in that log, none of them changed by this branch. They include `tsymex_rfc0005_s8bo_cells` at 61.2 s (60.8 s on the prior run), which is S8bo's file, stacked here and not split. The largest is `tsymex_configdefaults` at 152 s. I did not compare these with a base run, so I cannot say whether this branch slowed any of them.

## Linux suites
The sweeps cover a 94-suite list (`s8cb-work/v2.txt`), not the whole test tree; the full tree ran only on Windows.

Sweep totals at a09d879:
- Z3 5.1 c: 94 rc=0, 1484 OK, 0 failed.
- Z3 4.13.4 c: 94 rc=0, 1484 OK, 0 failed.
- Z3 5.1 cpp: 92 rc=0, 1444 OK, 2 nonzero.

**The 2 cpp failures:** `tsymex_r6_n42_deref_taint` and `tsymex_r6_n43_parity` are compile errors (readCellField `f = F(i)` on `std::atomic<NI8>`, deleted operator=). The same failure was observed at 136ad60 and 72b2c2b, so it is pre-existing.

Cells are OK/failed followed by seconds. The rows marked "later" ran after a09d879 at their own commit, and their logs record no seconds. `s8cb_tostr` had 57 OK in one file before the split.

| suite | 5.1 c ok/fail s | 4.13.4 c ok/fail s | 5.1 cpp ok/fail s |
|---|---|---|---|
| tconfigdefaults | 21/0 5 | 21/0 5 | 21/0 5 |
| tentrypointwiring | 2/0 4 | 2/0 4 | 2/0 3 |
| tsymex_163_opaque_transparent | 15/0 26 | 15/0 26 | 15/0 30 |
| tsymex_163rev_concolic_modes | 19/0 27 | 19/0 28 | 19/0 32 |
| tsymex_163rev_inert_argfork | 9/0 24 | 9/0 22 | 9/0 30 |
| tsymex_163rev_inert_exclusions | 15/0 24 | 15/0 23 | 15/0 30 |
| tsymex_163rev_int_literal_width | 27/0 27 | 27/0 22 | 27/0 32 |
| tsymex_163rev_parser_gaps | 10/0 27 | 10/0 21 | 10/0 29 |
| tsymex_163rev_scan_counter_range | 10/0 25 | 10/0 21 | 10/0 31 |
| tsymex_163rev_transparent_guard | 9/0 24 | 9/0 21 | 9/0 31 |
| tsymex_163rev_transparent_result | 4/0 24 | 4/0 26 | 4/0 28 |
| tsymex_CR2a_expr_catchall | 7/0 25 | 7/0 23 | 7/0 30 |
| tsymex_CR2b_paramtype_catchall | 4/0 23 | 4/0 20 | 4/0 27 |
| tsymex_CR2c_witnessreader_catchall | 17/0 25 | 17/0 23 | 17/0 30 |
| tsymex_configdefaults | 24/0 64 | 24/0 59 | 24/0 70 |
| tsymex_g2_flip | 8/0 42 | 8/0 31 | 8/0 43 |
| tsymex_g3fix_walkergap | 1/0 24 | 1/0 26 | 1/0 27 |
| tsymex_g4_cmpwalk | 1/0 25 | 1/0 25 | 1/0 28 |
| tsymex_g6_transform_binding | 6/0 27 | 6/0 26 | 6/0 29 |
| tsymex_h_verification | 18/0 29 | 18/0 28 | 18/0 35 |
| tsymex_phase12_witnesses | 10/0 27 | 10/0 26 | 10/0 33 |
| tsymex_phase14_multivariant_ir | 2/0 4 | 2/0 4 | 2/0 4 |
| tsymex_phase14_multivariant_typebridge | 4/0 4 | 4/0 4 | 4/0 4 |
| tsymex_phase14_multivariant_walker | 2/0 24 | 2/0 23 | 2/0 31 |
| tsymex_phase14_multivariant_witness | 2/0 25 | 2/0 23 | 2/0 31 |
| tsymex_phase15_CR21_parseintraise_arg | 3/0 25 | 3/0 26 | 3/0 31 |
| tsymex_phase15_CR2_cachekey | 6/0 3 | 6/0 3 | 6/0 4 |
| tsymex_phase15_N2_kindgate_audit | 5/0 5 | 5/0 6 | 5/0 6 |
| tsymex_phase15_g5_distinct_borrow | 3/0 24 | 3/0 28 | 3/0 30 |
| tsymex_phase15_r11_unsafecast | 4/0 26 | 4/0 28 | 4/0 30 |
| tsymex_phase15_r11b_smoke | 11/0 27 | 11/0 29 | 11/0 31 |
| tsymex_phase15_r8_ptr | 5/0 25 | 5/0 30 | 5/0 32 |
| tsymex_phase16_m5_ifexpr_minmax | 10/0 26 | 10/0 29 | 10/0 32 |
| tsymex_phase7_assertcovered | 22/0 32 | 22/0 33 | 22/0 35 |
| tsymex_r2_scanbound | 3/0 25 | 3/0 27 | 3/0 31 |
| tsymex_r5_bv32_width | 8/0 25 | 8/0 28 | 8/0 30 |
| tsymex_r6_a0_lowhigh | 10/0 25 | 10/0 27 | 10/0 31 |
| tsymex_r6_a1_variantlit | 8/0 25 | 8/0 29 | 8/0 32 |
| tsymex_r6_d2_recursive_budget | 7/0 25 | 7/0 29 | 7/0 30 |
| tsymex_r6_heap_raise_totality | 9/0 27 | 9/0 29 | 9/0 32 |
| tsymex_r6_n36_raise_class_audit | 14/0 5 | 14/0 6 | 14/0 6 |
| tsymex_r6_n40_alloc_totality | 10/0 26 | 10/0 27 | 10/0 30 |
| tsymex_r6_n42_deref_taint | 15/0 28 | 15/0 29 | compile error |
| tsymex_r6_n43_parity | 25/0 29 | 25/0 29 | compile error |
| tsymex_r6_n49_dottedfield_mutation | 8/0 26 | 8/0 28 | 8/0 32 |
| tsymex_r6_r6_emit_roundtrip | 111/0 8 | 111/0 9 | 111/0 10 |
| tsymex_rectify_effects | 5/0 26 | 5/0 28 | 5/0 29 |
| tsymex_rfc0005_b7_integration | 6/0 29 | 6/0 32 | 6/0 35 |
| tsymex_rfc0005_s10_replay_verdict | 31/0 29 | 31/0 33 | 31/0 35 |
| tsymex_rfc0005_s1_lattice | 23/0 24 | 23/0 27 | 23/0 28 |
| tsymex_rfc0005_s2_replay | 16/0 30 | 16/0 34 | 16/0 36 |
| tsymex_rfc0005_s3_monotonicity | 27/0 32 | 27/0 35 | 27/0 37 |
| tsymex_rfc0005_s6b_ops | 44/0 30 | 44/0 30 | 44/0 34 |
| tsymex_rfc0005_s7_closure | 37/0 30 | 37/0 34 | 37/0 32 |
| tsymex_rfc0005_s8_scope | 28/0 29 | 28/0 28 | 28/0 32 |
| tsymex_rfc0005_s8ab_letaudit | 28/0 50 | 28/0 53 | 28/0 53 |
| tsymex_rfc0005_s8an_remainder | 25/0 44 | 25/0 46 | 25/0 50 |
| tsymex_rfc0005_s8au_remainder | 35/0 45 | 35/0 56 | 35/0 49 |
| tsymex_rfc0005_s8ax_remainder | 53/0 65 | 53/0 81 | 53/0 66 |
| tsymex_rfc0005_s8b_substitutions | 26/0 26 | 26/0 26 | 26/0 30 |
| tsymex_rfc0005_s8bc_remainder_a | 27/0 35 | 27/0 45 | 27/0 37 |
| tsymex_rfc0005_s8bc_remainder_b | 18/0 36 | 18/0 49 | 18/0 40 |
| tsymex_rfc0005_s8bc_remainder_c | 29/0 59 | 29/0 81 | 29/0 63 |
| tsymex_rfc0005_s8bd_remainder | 23/0 35 | 23/0 48 | 23/0 41 |
| tsymex_rfc0005_s8be_remainder | 15/0 35 | 15/0 47 | 15/0 37 |
| tsymex_rfc0005_s8be_remainder_b | 8/0 31 | 8/0 44 | 8/0 34 |
| tsymex_rfc0005_s8be_remainder_c | 13/0 31 | 13/0 45 | 13/0 36 |
| tsymex_rfc0005_s8bg_remainder | 14/0 28 | 14/0 42 | 14/0 35 |
| tsymex_rfc0005_s8bh_remainder | 35/0 54 | 35/0 55 | 35/0 56 |
| tsymex_rfc0005_s8bj_startopt | 3/0 8 | 3/0 8 | 3/0 6 |
| tsymex_rfc0005_s8bl_borrow | 4/0 23 | 4/0 27 | 4/0 29 |
| tsymex_rfc0005_s8bl_gaps | 11/0 38 | 11/0 37 | 11/0 41 |
| tsymex_rfc0005_s8bl_magics | 8/0 30 | 8/0 32 | 8/0 31 |
| tsymex_rfc0005_s8bl_magicscan | 3/0 23 | 3/0 29 | 3/0 29 |
| tsymex_rfc0005_s8bl_pairloop | 2/0 29 | 2/0 30 | 2/0 33 |
| tsymex_rfc0005_s8bl_seqops | 4/0 25 | 4/0 27 | 4/0 29 |
| tsymex_rfc0005_s8bl_setlen | 7/0 29 | 7/0 30 | 7/0 34 |
| tsymex_rfc0005_s8bn_remainder | 37/0 57 | 37/0 57 | 37/0 56 |
| tsymex_rfc0005_s8bo_cells | 22/0 35 | 22/0 34 | 22/0 38 |
| tsymex_rfc0005_s8bo_nil | 13/0 29 | 13/0 28 | 13/0 34 |
| tsymex_rfc0005_s8bo_replay | 6/0 29 | 6/0 28 | 6/0 34 |
| tsymex_rfc0005_s8br_framecond | 3/0 27 | 3/0 29 | 3/0 34 |
| tsymex_rfc0005_s8br_remainder | 5/0 31 | 5/0 33 | 5/0 36 |
| tsymex_rfc0005_s8bs_addrglobal | 14/0 31 | 14/0 32 | 14/0 35 |
| tsymex_rfc0005_s8bs_byref | 7/0 32 | 7/0 32 | 7/0 35 |
| tsymex_rfc0005_s8bs_byvalue | 3/0 29 | 3/0 29 | 3/0 33 |
| tsymex_rfc0005_s8bs_iterparams | 4/0 29 | 4/0 32 | 4/0 34 |
| tsymex_rfc0005_s8bw_remainder | 22/0 42 | 22/0 43 | 22/0 47 |
| tsymex_rfc0005_s8cb_cells | 43/0 34 | 43/0 33 | 43/0 36 |
| tsymex_rfc0005_s8cb_magics | 47/0 33 | 47/0 34 | 47/0 35 |
| tsymex_rfc0005_s8cb_replay | 18/0 29 | 18/0 31 | 18/0 32 |
| tsymex_rfc0005_s8cb_tostr (later) | 29/0 | 29/0 | 29/0 |
| tsymex_tot1_totality_corpus | 21/0 25 | 21/0 25 | 21/0 31 |
| ttarget | 10/0 17 | 10/0 16 | 10/0 17 |
| tsymex_rfc0005_s8cb_order (later) | 29/0 | 29/0 | 29/0 |
| tsymex_r6_n27_placeholder_read_audit (later) | 4/0 | 4/0 | 4/0 |
| tsymex_163audit_w10 (later) | 5/0 | 5/0 | 5/0 |
| tsymex_rfc0005_s11_surface (later) | 34/0 | 34/0 | 34/0 |
| tsymex_rfc0005_s8az_remainder (later) | 7/0 | 7/0 | 7/0 |

## Different mechanisms, reported and not fixed here
Also committed in the RFC under "As landed (S8cb)".
- **SOUNDNESS:** `{.cast(uncheckedAssign).}: o.k = v` gives a false sxRaised (the pragma is dropped).
- **SOUNDNESS:** replay of an unmodelled path that calls the real `quit` ends the process (existing).
- **PRECISION:** `s[1].b = 7` and `s[1][0] = x` give "unsupported nnkAsgn shape" (S8bz owns pointers into a seq of aggregates).
- **PRECISION:** whole-tuple `==` declines at eqBV.
- **PRECISION:** a local `let b = addr o.y` alias declines on whole assignment.
- **PRECISION:** a type section in a routine body declines.
- **PRECISION:** a parameter pragma `x {.inject.}: int` fails to compile in collectStringBackedByteSeqParamsImpl.
- **PRECISION:** the n42 and n43 cpp compile failure, pre-existing at 136ad60.

## Notes for integration
- rc=139 was seen once in probe p7 (top-level `let ra = symexFind(...)` plus an unused proc with `=sink`, `=dup` and `quit`). A rerun did not reproduce it, and I did not investigate further. The cause is unknown.
- The S8bw row is still `state="pending"` on this base; S8bz flips it. The S8cb row is flipped to `state="done"`.
- S8bz builds on the field cell type, so the two need coordinating at integration.
