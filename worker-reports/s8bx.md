# S8bx -- DONE

- **sha:** de6c67ff7aa98641cf36f6aea4010854cfe4dd9c (branch `rfc-0005-s8bx`)
- **base:** 1f38a13 (origin/rfc-0005-s8bl; S8bl base 22b67c7)
- **walker:** 213 -> 228 (provisional). CR2 `== "228"` updated and run; floor `>= 228` in `tests/tsymex_rfc0005_s8bx_extractraise.nim`.

History (no WIP):
- 7083952 docs(rfc): 0005 S8bx -- add the slice row (S8bl's remainder)
- 8da129b fix(symex): RFC-0005 S8bx -- a raise inside in-walk witness extraction reaches the run boundary
- d4ab108 fix(symex): RFC-0005 S8bx -- one classifier for the seq witness reader and the renderability predicate
- 371bf84 fix(symex): RFC-0005 S8bx -- an mpairs view passed with its Table is one location
- 7409455 fix(symex): RFC-0005 S8bx -- a key removed while iterating a Table, the length kept, declines
- 1b8d279 feat(symex): RFC-0005 S8bx -- a string's setLen over a symbolic string decides
- de6c67f docs(rfc): RFC-0005 S8bx -- as landed, slice row done

## Soundness bugs found
1. **A raise inside in-walk witness extraction was lost on the C backend.** The result was a false sxUnsat with no error, or a false sxSat from a half-extracted witness.
   - Mechanism: Nim 2.2.10's C backend (goto exceptions) destroys a call's result temporary on the raise path without saving or clearing the error flag (`T = f(); if (*nimErr_) {eqdestroy(T); goto}`). This happens when an existing variable is reassigned from a call.
   - nim-z3's `termDestroy` (`_deps/z3/src/z3/lifecycle.nim`) wraps its body in `try ... except CatchableError/Exception: discard`. Entered with the flag still set, it takes the in-flight exception as its own, clears the flag and pops it.
   - Located by instrumenting `popCurrentException` in the generated C: the raise was consumed by a `Z3BitVec` `=destroy` from `walkBlock`'s raise path, destroying `walk`'s returned `seq[Path]`.
   - C++ is unaffected.
2. **An `mpairs` / `mvalues` view passed to a call together with its Table** gave verdicts swapped against native runs. S8bl had reported this as PRECISION.
3. **A key removed from a Table while iterating it, with the length kept,** followed the loop-entry enumeration, untainted for a 1-entry table. The result was a false sxUnsat (`new_key_visited`) and a false sxSat whose witness did not replay (`new_key_skipped`). S8bl had reported this as PRECISION.

## RED / GREEN (observed by running)
- **Item 1** (`tsymex_rfc0005_s8bx_extractraise` + `.nim.cfg` `-d:symexTestInjectWalkerFault`):
  - RED on c at the base: `afterLoop` and `twoIters` were a false sxUnsat with no error; `swallowedInside` was a false sxSat. cpp already named each one.
  - GREEN 7/7 on c and cpp (Z3 5.1), and on c (Z3 4.13.4). cpp was rerun at the final head: 7/0.
  - S8bl's natural trigger (key-byte constraint disabled in a probe) is now a named decline on c.
- **Item 2** (`tsymex_rfc0005_s8bx_witnessdrift`): RED was a compile crash ("seq witness reader for seq[Widget{...}] not yet implemented"). GREEN 3/3.
- **Item 3** (`tsymex_rfc0005_s8bx_mpairs`): RED 7/8 FAILED at the pre-fix source, with swapped verdicts (the by-value scalar case passed). GREEN 8/8.
- **Item 4** (`tsymex_rfc0005_s8bx_iterchange`):
  - RED: false sxUnsat (`new_key_visited`, `visited_twice`) and a false sxSat (`new_key_skipped`'s witness did not replay).
  - GREEN 6/6 on both Z3 versions.
  - The two native-evidence tests pass, and pin that the slot walk depends on the hashes.
- **Item 5** (`tsymex_rfc0005_s8bx_setlenstr`): RED on Z3 5.1 AND 4.13.4: `grow_pad_dead` and `grow_pad_live` were both sxUnknown (`beSolverUndef`). GREEN 3/3 on both.

## Design per item
1. **Item 1.**
   - `trySolve` installs `extractionRaiseHook` as `system.localRaiseHook` for the span of `extractWitness`. The hook runs in `raiseExceptionAux` on both backends, before any unwinding.
   - The hook records the first raise (`extractionFault`; excluding nim-z3's `Z3InvalidUsageError`).
   - With a fault recorded:
     - `trySolve` returns sxUnknown with no witness;
     - `shouldStop` ends the walk;
     - `runSymex` forces sxUnknown plus `weInternalWalkerFault` naming the raise.
   - `resetSymexRunState` clears the fault and releases the hook.
   - Audit of the other in-walk callbacks:
     - witness extraction (fixed);
     - `nelliZ3ErrorHandler` (counted at source, S8m);
     - `lowerClosureCall` re-entry (walk discipline, N36);
     - the same-frame try sites in `defaultZero` x4, `symValFromRawAst` and `concreteSeqLen` (generated C checked: out-pointer results, shielded exits);
     - concolic `concreteBranchOutcome` / `loopArmInfeasible` / `checkCapped` (Z3 only);
     - the concolic entry never extracts;
     - the Windows fiber trampoline is top level;
     - the `tagGuard` closure is Z3 only.
2. **Item 2.** One classifier, `seqWitnessReader` / `SeqWitnessReader` in types.nim, now backs both `isRenderableWitnessTy` and `emitTyAndReader`.
   - The type is always rendered.
   - An unreadable reader is `unrenderedReader` (`{.error.}`), which fires only if it is emitted.
   - CR2c restored to its `Widget` element.
3. **Item 3.** The parser marks a call that receives both the view and the table's location.
   - The marking is `IRStmt.cViewAliases`, set by `markViewAliases`.
   - An argument that holds the table, or is part of the view, declines.
   - The walker binds the pair in the callee frame and syncs it after every callee statement (`syncViewAliases`):
     - a changed view is stored into the table;
     - a changed table is read back when the key's presence is a literal true;
     - otherwise it declines.
   - The pair is passed on to nested callees.
   - S8bs's `bindVarLocs` / `syncAddrCells` are not on this base. Reconciliation (in the RFC): replace this local model with address cells when the branches meet; the mpairs suite is the acceptance test.
4. **Item 4.** Not modelled, because the slot walk is hash- and capacity-dependent.
   - Native runs: from `{a}`, del a + add c visits c; from `{f}` it does not; in `{k308, k321}`, re-inserting k308 visits it twice. 622 del-and-re-insert shapes over 2-7 keys changed the visit sequence.
   - Each iteration snapshots the table. A removal since the snapshot (`iekTabRemovedSince` / `presenceRemoved`: only true stores and ite merges count as no removal) declines the path with `feUnsupportedOp`.
   - A value write stays exact.
   - The `feTableIterOrder` taint is unchanged.
5. **Item 5.** The `setLen` string result is a fresh string leaf carrying the byte-domain fact, equal to the prefix or to `s ++ NUL-pad`.
   - `seqLenCaps`' byte-test rewrite then applies, and Z3 decides it on both versions.

## Verification
- **Suites run:**
  - every `command grep -l -E 'Table|mpairs|setLen|witness' tests/tsymex_*.nim` hit;
  - plus the s8bl suites, s8bc_remainder_a/b/c, s11_surface, r6_b6_optionregion, CR2 and my 5 suites.
  - That is 342 files, list in `s8bx-work/sweeplist.txt`.
- **How each was run:**
  - Z3 5.1: compiled and run with `scripts/dt-bounded.sh c`.
  - Z3 4.13.4: the same compiled binary, rerun with `LD_LIBRARY_PATH` pointing at 4.13.4. This was verified with `z3FullVersion()` (4.13.4.0); dt413.sh selects the library the same way.
  - Logs are in `/home/corey/tmp-usage/work/s8bx-work/logs/sweep/`.
- **The one red:**
  - The sweep ran at 6286f64 (pre-squash). One red: `rfc0005_s8m_exits`' sort-check audit (raw `Z3_mk_store`/`Z3_mk_ite` in item 4's kind probes).
  - Fixed to `checkedStore`/`checkedIte`, squashed into 7409455.
  - s8m_exits and iterchange were rerun on both Z3 versions; extractraise was rerun on cpp.
- **Item 1 on cpp:** extractraise 7/0 (Z3 5.1).
- **Totals:** Z3 5.1: 3560 ok / 0 failed. Z3 4.13.4: 3560 ok / 0 failed, over 342 files.
- **Run-only times** (binary only; pause flag absent; load 13-16 on 8 cores):

  | suite | time |
  |---|---|
  | iterchange | 9 s |
  | mpairs | 10 s |
  | witnessdrift | 9 s |
  | setlenstr | 32-45 s |
  | extractraise | 38 s |

  Compile and run together took 190-280 s at that load. All 5 are registered in nelli.nimble.
- **Windows at de6c67f:**
  - fuzzer-mingw 37177992464 success
  - symex-mingw 37177992419 success
  - fuzzer-msvc 37177992416 success
  - Earlier heads were all green: 8da129b (37147535920/37147535838/37147535853), d4ab108, 371bf84, 4d7d472.

## Different mechanisms, reported and not fixed here (also in the RFC "As landed (S8bx)")
- **SOUNDNESS:** any raise inside the walk can be lost on the C backend by item 1's mechanism.
  - About 290 unshielded raise-path destroys were found in the generated runtime.nim.c, many of Z3-term-holding types.
  - Only extraction is observed at the raise.
  - The root fix belongs in nim-z3 `termDestroy` (save and restore the error state, or don't catch) or in the Nim compiler.
- **PRECISION:** in an aliased callee, these decline:
  - a table write at a key whose presence is not literal;
  - a write to both the view and the table in one statement;
  - passing the object that holds the table together with the view.
- **PRECISION:** a key removed while iterating declines rather than being modelled. A ground-key slot walk could be a later refinement, and a callee havoc of the table reads as a removal.
- **Integration:** `iekSeqNewZero` (S8bc) / `iekSeqNew` (S8bi) are not reconciled (batch 5, per the job).

## Per-suite table (both Z3 versions, c)
| suite | Z3 5.1 (c) ok/failed | Z3 4.13.4 (c) ok/failed | note |
|---|---|---|---|
| tsymex_phase15_CR2_cachekey | 6/0 | 6/0 |  |
| tsymex_r6_b6_optionregion | 8/0 | 8/0 |  |
| tsymex_rfc0005_s11_surface | 34/0 | 34/0 |  |
| tsymex_rfc0005_s8bc_remainder_a | 27/0 | 27/0 |  |
| tsymex_rfc0005_s8bc_remainder_b | 18/0 | 18/0 |  |
| tsymex_rfc0005_s8bc_remainder_c | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8bl_borrow | 4/0 | 4/0 |  |
| tsymex_rfc0005_s8bl_magicscan | 3/0 | 3/0 |  |
| tsymex_rfc0005_s8bl_magics | 8/0 | 8/0 |  |
| tsymex_rfc0005_s8bl_gaps | 11/0 | 11/0 |  |
| tsymex_rfc0005_s8bl_pairloop | 2/0 | 2/0 |  |
| tsymex_rfc0005_s8bl_seqops | 4/0 | 4/0 |  |
| tsymex_rfc0005_s8bl_setlen | 7/0 | 7/0 |  |
| tsymex_rfc0005_s8bx_extractraise | 7/0 | 7/0 |  |
| tsymex_rfc0005_s8bx_iterchange | 6/0 | 6/0 | rerun after the audit fix: 6/0 both |
| tsymex_rfc0005_s8bx_mpairs | 8/0 | 8/0 |  |
| tsymex_rfc0005_s8bx_witnessdrift | 3/0 | 3/0 |  |
| tsymex_rfc0005_s8bx_setlenstr | 3/0 | 3/0 |  |
| tsymex_162_range_base_width | 21/0 | 21/0 |  |
| tsymex_161_overflow_obligation | 19/0 | 19/0 |  |
| tsymex_163audit_range_domain | 12/0 | 12/0 |  |
| tsymex_163rev_armfield_write | 4/0 | 4/0 |  |
| tsymex_163audit_range_elem | 11/0 | 11/0 |  |
| tsymex_163rev_assign_scope | 10/0 | 10/0 |  |
| tsymex_163rev_concolic_flip_width | 13/0 | 13/0 |  |
| tsymex_163rev_concolic_diagnostics | 25/0 | 25/0 |  |
| tsymex_163rev_concolic_modes | 19/0 | 19/0 |  |
| tsymex_163rev_enum_domain | 19/0 | 19/0 |  |
| tsymex_163rev_degrade_classification | 8/0 | 8/0 |  |
| tsymex_163rev_enum_field_witness | 12/0 | 12/0 |  |
| tsymex_163rev_enum_ordinal | 14/0 | 14/0 |  |
| tsymex_163rev_enum_positions | 13/0 | 13/0 |  |
| tsymex_163rev_enum_valueshapes | 9/0 | 9/0 |  |
| tsymex_163rev_inert_argfork | 9/0 | 9/0 |  |
| tsymex_163rev_int_literal_width | 27/0 | 27/0 |  |
| tsymex_163rev_intoffset_range | 9/0 | 9/0 |  |
| tsymex_163rev_nested_clamp | 5/0 | 5/0 |  |
| tsymex_163rev_range_bounds | 11/0 | 11/0 |  |
| tsymex_163rev_scan_counter_range | 10/0 | 10/0 |  |
| tsymex_163rev_table_elem | 6/0 | 6/0 |  |
| tsymex_163rev_transparent_result | 4/0 | 4/0 |  |
| tsymex_163rev_variant_armfield | 6/0 | 6/0 |  |
| tsymex_a2_refvariant_fields | 9/0 | 9/0 |  |
| tsymex_a3_closure_iterators | 11/0 | 11/0 |  |
| tsymex_a7_rune | 12/0 | 12/0 |  |
| tsymex_a7_runes_iter | 6/0 | 6/0 |  |
| tsymex_a8_radix | 6/0 | 6/0 |  |
| tsymex_a9_casefold | 5/0 | 5/0 |  |
| tsymex_canonicalize | 32/0 | 32/0 |  |
| tsymex_cr22_label_assert_coexist | 5/0 | 5/0 |  |
| tsymex_CR2a_expr_catchall | 7/0 | 7/0 |  |
| tsymex_augmented_assign | 8/0 | 8/0 |  |
| tsymex_configdefaults | 24/0 | 24/0 |  |
| tsymex_CR2b_paramtype_catchall | 4/0 | 4/0 |  |
| tsymex_CR2c_witnessreader_catchall | 17/0 | 17/0 |  |
| tsymex_cr9c_intrep | 10/0 | 10/0 |  |
| tsymex_discard_raise | 4/0 | 4/0 |  |
| tsymex_funcdef_callee | 5/0 | 5/0 |  |
| tsymex_g1a_mode | 6/0 | 6/0 |  |
| tsymex_g1b_concolic | 15/0 | 15/0 |  |
| tsymex_h_stepA_nominalid | 3/0 | 3/0 |  |
| tsymex_h_containers | 12/0 | 12/0 |  |
| tsymex_g2_flip | 8/0 | 8/0 |  |
| tsymex_h_stepC_heapidentity | 10/0 | 10/0 |  |
| tsymex_h_verification | 18/0 | 18/0 |  |
| tsymex_h_witness | 11/0 | 11/0 |  |
| tsymex_inv_structured_kinds | 2/0 | 2/0 |  |
| tsymex_p1_tupleconstr_expr | 11/0 | 11/0 |  |
| tsymex_m6_probeproto_strproto | 10/0 | 10/0 |  |
| tsymex_p2a_objconstr_expr | 14/0 | 14/0 |  |
| tsymex_phase11_fielddefect | 5/0 | 5/0 |  |
| tsymex_p2b_refobjconstr_expr | 18/0 | 18/0 |  |
| tsymex_phase11_walker | 11/0 | 11/0 |  |
| tsymex_phase12_renderchoices | 5/0 | 5/0 |  |
| tsymex_phase12_scan | 6/0 | 6/0 |  |
| tsymex_phase12_seedphase | 3/0 | 3/0 |  |
| tsymex_phase12_derandomize | 1/0 | 1/0 |  |
| tsymex_phase12_sugar | 2/0 | 2/0 |  |
| tsymex_phase12_witnesses | 10/0 | 10/0 |  |
| tsymex_phase13_layer1_wire | 3/0 | 3/0 |  |
| tsymex_phase13_macro | 1/0 | 1/0 |  |
| tsymex_phase13_satsuffix | 1/0 | 1/0 |  |
| tsymex_phase13_unsat_roundtrip | 3/0 | 3/0 |  |
| tsymex_phase13_verdict_primitives | 4/0 | 4/0 |  |
| tsymex_phase14_b3_trace_equivalence | 2/0 | 2/0 |  |
| tsymex_phase14_arm_field_zero_init | 1/0 | 1/0 |  |
| tsymex_phase14_multivariant_ir | 2/0 | 2/0 |  |
| tsymex_phase14_c1_fromcache | 2/0 | 2/0 |  |
| tsymex_phase14_else_arms | 1/0 | 1/0 |  |
| tsymex_phase14_multivariant_walker | 2/0 | 2/0 |  |
| tsymex_phase14_strategy_digest | 4/0 | 4/0 |  |
| tsymex_phase14_multivariant_witness | 2/0 | 2/0 |  |
| tsymex_phase14_nonenum_disc | 1/0 | 1/0 |  |
| tsymex_phase14_symbolic_disc_reassign | 1/0 | 1/0 |  |
| tsymex_phase14_var_param | 1/0 | 1/0 |  |
| tsymex_phase14_var_param_downstream | 2/0 | 2/0 |  |
| tsymex_phase15_A1_assertarg | 4/0 | 4/0 |  |
| tsymex_phase15_A1_bitwise | 8/0 | 8/0 |  |
| tsymex_phase15_A1_arithmetic | 6/0 | 6/0 |  |
| tsymex_phase15_A1_boolean | 5/0 | 5/0 |  |
| tsymex_phase15_A1_callarg | 6/0 | 6/0 |  |
| tsymex_phase15_A1_comparison | 5/0 | 5/0 |  |
| tsymex_phase15_A1_unary | 5/0 | 5/0 |  |
| tsymex_phase15_A1_loopguard | 6/0 | 6/0 |  |
| tsymex_phase15_A2a_atomicir_audit | 9/0 | 9/0 |  |
| tsymex_phase15_A2a_chokepoint_audit | 3/0 | 3/0 |  |
| tsymex_phase15_A2a_guardcond_pin | 2/0 | 2/0 |  |
| tsymex_phase15_A2a_atomize | 4/0 | 4/0 |  |
| tsymex_phase15_A2b_bitwise | 6/0 | 6/0 |  |
| tsymex_phase15_C2b_closure_call | 3/0 | 3/0 |  |
| tsymex_phase15_C1_canonical_kind | 11/0 | 11/0 |  |
| tsymex_phase15_C2_staticparams | 3/0 | 3/0 |  |
| tsymex_phase15_C3_proc_as_value | 2/0 | 2/0 |  |
| tsymex_phase15_C4_hof | 5/0 | 5/0 |  |
| tsymex_phase15_C5_closure_eq | 5/0 | 5/0 |  |
| tsymex_phase15_C6_smoke | 9/0 | 9/0 |  |
| tsymex_phase15_CR14_exn_missing | 4/0 | 4/0 |  |
| tsymex_phase15_CR11_CR18_splitcap | 4/0 | 4/0 |  |
| tsymex_phase15_cr9_lowerInExpr | 6/0 | 6/0 |  |
| tsymex_phase15_E2a_cascade | 4/0 | 4/0 |  |
| tsymex_phase15_CR3_CR4_CR6_float | 7/0 | 7/0 |  |
| tsymex_phase15_E4a_userexn | 2/0 | 2/0 |  |
| tsymex_phase15_E2b_raise | 5/0 | 5/0 |  |
| tsymex_phase15_E3_try | 10/0 | 10/0 |  |
| tsymex_phase15_E4_hierarchy | 4/0 | 4/0 |  |
| tsymex_phase15_E5_finally | 6/0 | 6/0 |  |
| tsymex_phase15_E6_defect | 4/0 | 4/0 |  |
| tsymex_phase15_E7_smoke | 12/0 | 12/0 |  |
| tsymex_phase15_E8_getcurrentexn | 4/0 | 4/0 |  |
| tsymex_phase15_E_roundtrip | 7/0 | 7/0 |  |
| tsymex_phase15_F1_typebridge | 2/0 | 2/0 |  |
| tsymex_phase15_F5_float_conv | 3/0 | 3/0 |  |
| tsymex_phase15_F5hang_derefwrite | 2/0 | 2/0 |  |
| tsymex_phase15_F5_probeproto | 7/0 | 7/0 |  |
| tsymex_phase15_F6_float_math | 15/0 | 15/0 |  |
| tsymex_phase15_F7_float_extract | 7/0 | 7/0 |  |
| tsymex_phase15_F9a_array_float | 3/0 | 3/0 |  |
| tsymex_phase15_F9b_seq_float | 3/0 | 3/0 |  |
| tsymex_phase15_F8_smoke | 4/0 | 4/0 |  |
| tsymex_phase15_F9c_variant_float | 3/0 | 3/0 |  |
| tsymex_phase15_fieldcontainer | 5/0 | 5/0 |  |
| tsymex_phase15_g10_smoke | 7/0 | 7/0 |  |
| tsymex_phase15_G1a_instkey | 4/0 | 4/0 |  |
| tsymex_phase15_g3_type_subst | 2/0 | 2/0 |  |
| tsymex_phase15_g4_distinct_sort | 4/0 | 4/0 |  |
| tsymex_phase15_g6_concept_constraint | 3/0 | 3/0 |  |
| tsymex_phase15_g5_distinct_borrow | 3/0 | 3/0 |  |
| tsymex_phase15_g7_static_param | 2/0 | 2/0 |  |
| tsymex_phase15_g8_multi_param | 3/0 | 3/0 |  |
| tsymex_phase15_M1_seq_fixedwidth | 13/0 | 13/0 |  |
| tsymex_phase15_M2_parsebiggestint | 8/0 | 8/0 |  |
| tsymex_phase15_N2_kindgate_audit | 5/0 | 5/0 |  |
| tsymex_phase15_N0_kindgate_widen | 5/0 | 5/0 |  |
| tsymex_phase15_N1_resolution_gates | 32/0 | 32/0 |  |
| tsymex_phase15_N3_scan_boundary | 5/0 | 5/0 |  |
| tsymex_phase15_r13_ptr_finally | 1/0 | 1/0 |  |
| tsymex_phase15_r12_bumps | 3/0 | 3/0 |  |
| tsymex_phase15_R1a_ir | 9/0 | 9/0 |  |
| tsymex_phase15_r1_refsort | 2/0 | 2/0 |  |
| tsymex_phase15_r3_deref_read | 4/0 | 4/0 |  |
| tsymex_phase15_r5_nil | 5/0 | 5/0 |  |
| tsymex_phase15_r6_refobj | 5/0 | 5/0 |  |
| tsymex_phase15_r8_ptr | 5/0 | 5/0 |  |
| tsymex_phase15_rereview_drains | 15/0 | 15/0 |  |
| tsymex_phase15_S10a_strconv | 4/0 | 4/0 |  |
| tsymex_phase15_S10b_strconv | 4/0 | 4/0 |  |
| tsymex_phase15_S11_mutation | 5/0 | 5/0 |  |
| tsymex_phase15_S1_typebridge | 2/0 | 2/0 |  |
| tsymex_phase15_S2_strlit | 6/0 | 6/0 |  |
| tsymex_phase15_S3_strindex | 7/0 | 7/0 |  |
| tsymex_phase15_S4_strpred | 8/0 | 8/0 |  |
| tsymex_phase15_S5_strops | 7/0 | 7/0 |  |
| tsymex_phase15_S6b_regex | 5/0 | 5/0 |  |
| tsymex_phase15_S7a_bytes | 4/0 | 4/0 |  |
| tsymex_phase15_S8_concat | 5/0 | 5/0 |  |
| tsymex_phase15_S7b_smoke | 8/0 | 8/0 |  |
| tsymex_phase15_S9_caseconv | 5/0 | 5/0 |  |
| tsymex_phase15_z3c_classify | 2/0 | 2/0 |  |
| tsymex_phase16_A5_float_classify | 10/0 | 10/0 |  |
| tsymex_phase16_CR1a_bitwise_svint | 7/0 | 7/0 |  |
| tsymex_phase16_CR1b_tail_local | 3/0 | 3/0 |  |
| tsymex_phase16_D1a_defect_routeraise | 4/0 | 4/0 |  |
| tsymex_phase16_D1c_shortcircuit | 7/0 | 7/0 |  |
| tsymex_phase16_m3_rfind | 6/0 | 6/0 |  |
| tsymex_phase16_m4_str_add_ampeq | 12/0 | 12/0 |  |
| tsymex_phase16_m5_ifexpr_minmax | 10/0 | 10/0 |  |
| tsymex_phase16_R16_3_divzero | 7/0 | 7/0 |  |
| tsymex_phase16_R16_2_rangedefect | 10/0 | 10/0 |  |
| tsymex_phase16_R16_5_overflow_thru_closure | 3/0 | 3/0 |  |
| tsymex_phase16_R16_6_diagnostics_channel | 2/0 | 2/0 |  |
| tsymex_phase1_arith | 7/0 | 7/0 |  |
| tsymex_phase1_assert | 3/0 | 3/0 |  |
| tsymex_phase1_let | 1/0 | 1/0 |  |
| tsymex_phase1_bool | 1/0 | 1/0 |  |
| tsymex_phase2_abstraction | 5/0 | 5/0 |  |
| tsymex_phase2_fallback | 2/0 | 2/0 |  |
| tsymex_phase2_bv_arith | 4/0 | 4/0 |  |
| tsymex_phase2_overflow | 4/0 | 4/0 |  |
| tsymex_phase3_inline | 4/0 | 4/0 |  |
| tsymex_phase3_recursion | 3/0 | 3/0 |  |
| tsymex_phase3_stdlib | 1/0 | 1/0 |  |
| tsymex_phase3_summarization | 1/0 | 1/0 |  |
| tsymex_phase4_array | 3/0 | 3/0 |  |
| tsymex_phase4_nested | 1/0 | 1/0 |  |
| tsymex_phase4_oob | 1/0 | 1/0 |  |
| tsymex_phase4_tuple | 4/0 | 4/0 |  |
| tsymex_phase5_hashset | 1/0 | 1/0 |  |
| tsymex_phase5_models | 5/0 | 5/0 |  |
| tsymex_phase5_seq | 3/0 | 3/0 |  |
| tsymex_phase5_table | 2/0 | 2/0 |  |
| tsymex_phase6_break | 2/0 | 2/0 |  |
| tsymex_phase6_case | 3/0 | 3/0 |  |
| tsymex_phase6_for | 3/0 | 3/0 |  |
| tsymex_phase6_while | 2/0 | 2/0 |  |
| tsymex_phase7_assertcovered | 22/0 | 22/0 | 4.13.4 rerun (sweep filter skipped it) |
| tsymex_r11_range_invariant_audit | 7/0 | 7/0 |  |
| tsymex_q1_scanlift | 13/0 | 13/0 |  |
| tsymex_r14_continue_guard | 10/0 | 10/0 |  |
| tsymex_r1b_shortcircuit_oob | 19/0 | 19/0 |  |
| tsymex_r14_case2_degrade | 2/0 | 2/0 |  |
| tsymex_r2_scanbound | 3/0 | 3/0 |  |
| tsymex_r4_seq_slice | 10/0 | 10/0 |  |
| tsymex_r1_draingap | 11/0 | 11/0 |  |
| tsymex_r4_slice_binding | 6/0 | 6/0 |  |
| tsymex_r5_bv32_width | 8/0 | 8/0 |  |
| tsymex_r5_const_fold | 6/0 | 6/0 |  |
| tsymex_r5_neg_bool_conv | 4/0 | 4/0 |  |
| tsymex_r5_tuple_return | 3/0 | 3/0 |  |
| tsymex_r6_a0_lowhigh | 10/0 | 10/0 |  |
| tsymex_r6_a1_variantlit | 8/0 | 8/0 |  |
| tsymex_r4_strip | 5/0 | 5/0 |  |
| tsymex_r6_a2_retbind_variant | 9/0 | 9/0 |  |
| tsymex_r6_a3_variantconstruct_sym | 12/0 | 12/0 |  |
| tsymex_r6_a4_construct_interactions | 9/0 | 9/0 |  |
| tsymex_r6_a6_exported_field_names | 3/0 | 3/0 |  |
| tsymex_r6_a6r_callwitness | 12/0 | 12/0 |  |
| tsymex_r6_b1_stringbacked | 7/0 | 7/0 |  |
| tsymex_r6_b2_intwidth | 18/0 | 18/0 |  |
| tsymex_r6_b4_readcstring | 13/0 | 13/0 |  |
| tsymex_r6_b5_chained | 9/0 | 9/0 |  |
| tsymex_r6_b7r_bytescan | 26/0 | 26/0 |  |
| tsymex_r6_bug2_scopeddecline | 12/0 | 12/0 |  |
| tsymex_r6_d2_recursive_budget | 7/0 | 7/0 |  |
| tsymex_r6_b7r2_pathscope | 11/0 | 11/0 |  |
| tsymex_r6_heap_raise_totality | 9/0 | 9/0 |  |
| tsymex_r6_itesv_mergedegrade | 11/0 | 11/0 |  |
| tsymex_r6_lows_collectors | 5/0 | 5/0 |  |
| tsymex_r6_lows_declines | 15/0 | 15/0 |  |
| tsymex_r6_n10_coverage_matrix | 22/0 | 22/0 |  |
| tsymex_r6_n16_closure_zerodefault | 10/0 | 10/0 |  |
| tsymex_r6_n14_seqops | 24/0 | 24/0 |  |
| tsymex_r6_n20_boundedloop | 5/0 | 5/0 |  |
| tsymex_r6_n27_placeholder_read_audit | 4/0 | 4/0 |  |
| tsymex_r6_n21_pairloop_member | 14/0 | 14/0 |  |
| tsymex_r6_n27_hof_placeholder | 6/0 | 6/0 |  |
| tsymex_r6_n28_shadow_collision | 5/0 | 5/0 |  |
| tsymex_r6_n36_raise_class_audit | 14/0 | 14/0 |  |
| tsymex_r6_n31_block_counter | 7/0 | 7/0 |  |
| tsymex_r6_n29_seqlit_sortmismatch | 7/0 | 7/0 |  |
| tsymex_r6_n37_raise_residue | 11/0 | 11/0 |  |
| tsymex_r6_n36_raise_degrade | 8/0 | 8/0 |  |
| tsymex_r6_n39_variant_field_alloc | 10/0 | 10/0 |  |
| tsymex_r6_n42_deref_taint | 15/0 | 15/0 |  |
| tsymex_r6_n40_alloc_totality | 10/0 | 10/0 |  |
| tsymex_r6_n43_parity | 25/0 | 25/0 |  |
| tsymex_r6_n9_variant_budget | 7/0 | 7/0 |  |
| tsymex_r6_n49_dottedfield_mutation | 8/0 | 8/0 |  |
| tsymex_r6_nulwitness | 14/0 | 14/0 |  |
| tsymex_r6_r1_placeholder_totality | 14/0 | 14/0 |  |
| tsymex_r6_r2_zerodefault_result | 25/0 | 25/0 |  |
| tsymex_r6_r3_svint_overflow | 9/0 | 9/0 |  |
| tsymex_r6_r6_emit_roundtrip | 105/0 | 105/0 |  |
| tsymex_r6_r5_pairloop_counter | 5/0 | 5/0 |  |
| tsymex_r6_r4_collector_scoping | 7/0 | 7/0 |  |
| tsymex_r8_omitted_field_degrade | 3/0 | 3/0 |  |
| tsymex_rectify_abstraction | 2/0 | 2/0 |  |
| tsymex_rectify_cardinality | 2/0 | 2/0 |  |
| tsymex_rectify_effects | 5/0 | 5/0 |  |
| tsymex_rectify_generics | 1/0 | 1/0 |  |
| tsymex_rectify_mutation | 6/0 | 6/0 |  |
| tsymex_rectify_nested_arrays | 1/0 | 1/0 |  |
| tsymex_rectify_variants | 3/0 | 3/0 |  |
| tsymex_retest_c3_bitwise_guard | 7/0 | 7/0 |  |
| tsymex_retest_char_needle | 6/0 | 6/0 |  |
| tsymex_retest_pred_succ | 5/0 | 5/0 |  |
| tsymex_rfc0005_s0_exhibit | 10/0 | 10/0 |  |
| tsymex_rfc0005_s10_replay_verdict | 31/0 | 31/0 |  |
| tsymex_rfc0005_s1_lattice | 23/0 | 23/0 |  |
| tsymex_rfc0005_s2_replay | 15/0 | 15/0 |  |
| tsymex_rfc0005_s1c_verdict | 24/0 | 24/0 |  |
| tsymex_rfc0005_s3_monotonicity | 27/0 | 27/0 |  |
| tsymex_rfc0005_s4_alloc | 20/0 | 20/0 |  |
| tsymex_rfc0005_s6a_budget | 31/0 | 31/0 |  |
| tsymex_rfc0005_s6b_ops | 43/0 | 43/0 |  |
| tsymex_rfc0005_s7_closure | 37/0 | 37/0 |  |
| tsymex_rfc0005_s8aa_remainder | 24/0 | 24/0 |  |
| tsymex_rfc0005_s8ab_letaudit | 28/0 | 28/0 |  |
| tsymex_rfc0005_s8ac_remainder | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8ad_remainder | 13/0 | 13/0 |  |
| tsymex_rfc0005_s8aj_remainder | 21/0 | 21/0 |  |
| tsymex_rfc0005_s8ag_indexsplit | 15/0 | 15/0 |  |
| tsymex_rfc0005_s8am_remainder | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8ao_remainder | 11/0 | 11/0 |  |
| tsymex_rfc0005_s8an_remainder | 25/0 | 25/0 |  |
| tsymex_rfc0005_s8ae_remainder | 16/0 | 16/0 |  |
| tsymex_rfc0005_s8ap_remainder | 36/0 | 36/0 |  |
| tsymex_rfc0005_s8aq_remainder | 13/0 | 13/0 |  |
| tsymex_rfc0005_s8ar_remainder | 50/0 | 50/0 |  |
| tsymex_rfc0005_s8at_remainder | 67/0 | 67/0 |  |
| tsymex_rfc0005_s8b_substitutions | 26/0 | 26/0 |  |
| tsymex_rfc0005_s8c_resolution | 25/0 | 25/0 |  |
| tsymex_rfc0005_s8d_typeheads | 17/0 | 17/0 |  |
| tsymex_rfc0005_s8e_scoping | 36/0 | 36/0 |  |
| tsymex_rfc0005_s8f_witness | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8g_models | 38/0 | 38/0 |  |
| tsymex_rfc0005_s8h_refwitness | 27/0 | 27/0 |  |
| tsymex_rfc0005_s8j_exits | 45/0 | 45/0 |  |
| tsymex_rfc0005_s8i_models | 39/0 | 39/0 |  |
| tsymex_rfc0005_s8k_bounds | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8m_exits | 32/0 | 32/0 | was 31/1 at 6286f64 (sort-check audit: raw Z3_mk_store/ite in presenceRemoved); fixed in 7409455, rerun |
| tsymex_rfc0005_s8l_exits | 50/0 | 50/0 |  |
| tsymex_rfc0005_s8n_precision | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8o_termination | 14/0 | 14/0 |  |
| tsymex_rfc0005_s8q_termination | 10/0 | 10/0 |  |
| tsymex_rfc0005_s8p_precision | 30/0 | 30/0 |  |
| tsymex_rfc0005_s8r_theoryfree | 3/0 | 3/0 |  |
| tsymex_rfc0005_s8_scope | 28/0 | 28/0 |  |
| tsymex_rfc0005_s8t_termination | 20/0 | 20/0 |  |
| tsymex_rfc0005_s8u_precision | 17/0 | 17/0 |  |
| tsymex_rfc0005_s8s_precision | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8v_termination | 7/0 | 7/0 |  |
| tsymex_rfc0005_s8w2_hotfix | 4/0 | 4/0 |  |
| tsymex_rfc0005_s8x_vm_alias | 7/0 | 7/0 |  |
| tsymex_rfc0005_s9_vetoes | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8w_remainder | 23/0 | 23/0 |  |
| tsymex_rfc0005_s8z_remainder | 37/0 | 37/0 |  |
| tsymex_snd1_uncertain_taint | 5/0 | 5/0 |  |
| tsymex_snd1b_closure_uncertain_axiom | 4/0 | 4/0 |  |
| tsymex_snd3_6_equality_loop | 3/0 | 3/0 |  |
| tsymex_snd4_strindex_oob | 8/0 | 8/0 |  |
| tsymex_snd3_loopdegrade | 7/0 | 7/0 |  |
| tsymex_tot1_totality_corpus | 21/0 | 21/0 |  |
| **total (342 files)** | **3560/0** | **3560/0** | |

## Scratch-clobber incident (verdict: not affected)

The agent confirmed this when the parent session asked, during the slice.
- None of its runners writes to, or references, the shared session scratchpad: `run.sh`, `batch.sh`, `runbin.sh` and `sweep1.sh`, all in `/home/corey/tmp-usage/work/s8bx-work/`.
- Every log and result reported here is under `s8bx-work/logs/`.
