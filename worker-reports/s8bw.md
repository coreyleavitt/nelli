# S8bw -- BLOCKER (two sub-bullets of item 3); everything else landed and verified

Branch `rfc-0005-s8bw`, head **950f8df** (base 22361d7 = S8bn on a28c9c3), walker **227** (provisional).
History: 5fdd9b1 `fix(symex)` (item 1), 0b52bd5 `feat(symex)` (items 2-3), 950f8df `docs(rfc)` (as landed). No WIP commits.

## BLOCKER

**Wrong assumption.** Item 3 assumes substrate that this base does not have.
- *"per-element cells for seqs of aggregates, reusing S8be's"*.
  - S8be (ef08ada), and S8bc's tree-seq backing (22b67c7, `isTreeSeqElemTy`), landed in batch 4 (merge b7808f1 / c87653c, chore d3cb2b1).
  - None of those commits is an ancestor of 22361d7 (`git merge-base --is-ancestor` gives NOT-IN for 22b67c7, ef08ada and d3cb2b1).
  - On this base, a seq of tuples or objects is an unbacked length-0 placeholder: `src/nelli/smt/types.nim:4247` `isBackedSeqElemTy` admits only bool, float, string, ref, ptr and int, and `src/nelli/smt/runtime.nim` `allocateSym` gives such a seq its inert placeholder arm.
  - So there is no element to address, and no S8be cell to reuse.
- *"`Table[K, V]` for an aggregate or non-int `V`"*.
  - This base backs only integer-leaf values: `src/nelli/smt/types.nim:4326` `isBackedTableTy` requires `isContainerIntLeaf`.
  - `string` and `float` values are S8ar's work, and container values are S8at's. Both are batch 2 (f488986), which is not in the base.
  - An aggregate `V` is a scoped decline even on batch 5 (`isTableValTy`, origin/rfc-0005-batch5 types.nim:4589).

**Best read.**
- Both bullets belong on the integrated base (batch 5 or later). Implementing them here would duplicate S8bc, S8be, S8ar and S8at, and would conflict at integration.
- What this base can do is landed:
  - pointers into every table value it backs (all integer widths, char, enum and bool, where it was int64 only);
  - every other bullet of item 3, in full.
- Recommend re-cutting the two bullets as a slice on batch 5. There:
  - the seq bullet extends `ptrVarLeaves` (runtime_heap.nim) with S8bc / S8be element cells, `PtrLeaf.steps` for the witness;
  - the table bullet extends `ptrTabValMatches` to S8ar's string and float values, plus a new leaf-split aggregate value.

**Tree state.**
- Branch pushed at 950f8df, all verification green (below), Windows green on the same code tree.
- The RFC S8bw row is left `state = "pending"` (the slice is not done).
- The "As landed (S8bw)" section is written, and lists both bullets as blocked.

## What landed (the DONE-format detail)

### RED and GREEN observed

Every RED was run on base 22361d7 in a separate worktree, from a copy of the test file.

| Item | Case | RED on base | GREEN |
|---|---|---|---|
| 1 | `gArr[2]` read, `aw` / `oaw` | AssertionDefect at `iekIndex` (`recv.kind == svArray`) | in-band decline |
| 1 | `sqw` | lowering taint leaked to the walk end | in-band decline |
| 1 | `sqp` | KeyError | in-band decline |
| 1 | `sqd` / `sqa` | walker-fault declines | in-band decline |
| 1 | `map` | AssertionDefect (lowerHofCall) | in-band decline |
| 1 | `join` | AssertionDefect (runtime_strings) | in-band decline |
| 1 | `gb` | AssertionDefect (binBV) | in-band decline |
| 1 | `vr` / `vrs` | clean false sxSat (Nim raises FieldDefect) | in-band decline |
| 1 | `lg`, `{.global.}` local | build failure | in-band decline |
| 2 | tf / of / nf / ac / as / ar / vp / ad / ad_let / cw | feGlobalReadUnmodelled, or a walker fault | sxSat, roConfirmed; dead twins sxUnsat; unwritten-part cases decline, named |
| 2 | ptg / pog / pag (S8bn item 4's path on globals) | feGlobalReadUnmodelled | roConfirmed |
| 3 | case-object global or `var` parameter beside a `ptr` parameter | **build failure** (`ptrAimInto` over the discriminator, runtime.nim:21312) | roConfirmed, with the inactive-branch sub-path declined and named |
| 3 | `pce`, heap `else`-branch field through a ptr | **sxRaised, no error: a false miss (SOUNDNESS)** | roConfirmed |
| 3 | `pcm` | no arm check | roConfirmed, inactive sub-path named |
| 3 | `pab` / `pai`, `addr` of a branch field | heUnsafeCast | roConfirmed; FieldDefect clean sxRaised |
| 3 | `gc` / `gcs` / `gcr` / `gc_dead` / `gcf`, generic case object | feUnsupportedParamType | roConfirmed / sxUnsat / FieldDefect sxRaised |
| 3 | `pt32` / `ptb`, ptr into a `Table[string, int32/bool]` value | feUnsupportedOp | roConfirmed |

The suite `tests/tsymex_rfc0005_s8bw_remainder.nim` has 22 tests and is registered in nelli.nimble after s8bn.

### Soundness bugs found
1. **Crash class, item 1.** Any receiver op on a global read before its first write was a walker fault, a KeyError or a leaked taint (listed above). An unbound variant's discriminator reassignment was a clean false sxSat.
2. **Build failure.** A case-object `var` parameter or global beside a `ptr` parameter failed to compile: `ptrAimInto` instantiated `fieldPairs` over the discriminator.
3. **False miss.** A heap case object's `else`-branch field family (`<O>__@-1__<f>`) was silently skipped as a pointer target (`ptrFamilyKey` required a digit), so a write through such a pointer was never seen.
4. **Unchecked arm.** No arm check existed for heap branch-field targets: a `sel` could name the field family of an object whose branch is inactive.

### Item 1 receiver-kind assertion audit (every site checked, and its outcome)
- **Now an in-band decline.**
  - `iekIndex`: recv svArray / arrElems; `degradeAlloc "__indexRecvDegrade"`.
  - `lowerHofCall`: seq svSeq and closure svClosure.
  - `iekStrJoin`: `degradeAlloc "__joinRecvDegrade"`.
  - `isIndexAssign` and `isSeqPop`: KeyError on an unbound receiver.
  - `isVariantReassign`: unbound object, and the multivariant `doAssert`, which now goes to `degradeUnmodelledReassign`.
  - `isVariantReassignSymbolic`: unbound object.
  - `lowerLeafInExpr`: the taint leak; it now returns `(SymVal, Path)` and folds the taint.
- **Kept; every caller checks the kind first:** joinStrSeq, seqElemAt, applyClosureGround, the three table key asserts (`keySV svString`), svTupleEq.
- **Reached only through the untyped stand-in, now typed via `iekVar.vGlobalTy`:** binBV, cmpBV, eqBV, and the walker-fault-kinded declines for the `iekSeqAdd` / `iekSeqDel` receiver and lowerBool / uNot.

### Design
- **Item 2: unwritten leaves.**
  - A read of an unbound typed global gives `globalInitValue`: one constant per leaf of its type, fixed for the run.
  - Each such constant is registered as unwritten (`glUnwritten`).
  - Rebuild copies (`iekVar.vCopy`) observe nothing.
  - The `lower` wrapper observes the outermost read of a chain, plus element reads, pointer derefs, discriminator reassignments and var/addr copy-ins. Any read that mentions an unwritten leaf declines with `feGlobalReadUnmodelled`.
  - For a symbolic index, `unwrittenIndependent` substitutes fresh constants and checks with Z3 that the read cannot depend on an unwritten leaf.
  - `isIndex.ixCheckOnly` marks a partial write's index-check read.
  - The canonical form carries the type, `:copy` and `;check`.
- **Item 3: pointers into case objects.**
  - `ptrVarLeaves` walks svVariant and svMultiVariant values.
    - Plain fields are positional.
    - A branch field is encoded as `ptrArmStep(axis, tag, j)`. One leaf stands for each field name, and a write goes to every tag's copy.
  - `PtrLeaf.steps` names each step for the witness (`f<name>`), and the target codes are unchanged for existing shapes.
  - A target carries `armCond`:
    - by value, from `svPathArmCond` (the discriminator in the branch's tags, or the negated others for `else`);
    - on the heap, from `ptrHeapArmCond` (the discriminator heap from `heapKeyShapes`).
  - At the read and write deref sites, `ptrInactive` is `OR(sel == code AND NOT armCond)`. If that is feasible, the walk forks a `w.degrade(feUnsupportedOp)` path and the main path continues with its negation.
  - **Spec deviation, from a probe on Nim 2.2.10.** Dereferencing a ptr into an inactive branch does NOT raise FieldDefect; it reads the active branch's bytes (the probe printed 2). Only `addr v.b` raises. So FieldDefect is modelled at the `addr`, and the deref declines.
  - `src/nelli/smt/ptraim.nim` adds `ptrAimByName`, a macro over every field of every branch, used under `{.push fieldChecks: off.}`. A pointer can then be aimed at a branch that becomes active only once the SUT runs.
  - The `addr` alias (`addrAliasDecl`) now accepts nnkCheckedFieldExpr and a `var` parameter root. It emits a check-read `discard v.b` (the FieldDefect fork), and only while `rootMutatedIn` finds no assignment to, or address-taking of, the object in scope.
- **Generic case objects.**
  - `userGenericObjectImpl` accepts `case` parts.
  - `classifyGenericInstance` calls `classifyObjectRecordFields` inside the instance frame (monomorphization), and joins a plain parent's fields or a generic case parent.
  - The instance is keyed and named as `G[args]`.
  - `refWitnessTypeNode` names a generic variant instance.
- **Tables.** `ptrTabValMatches` accepts every `isContainerIntLeaf` V of the pointee's width and sign, or bool. Values are read and written through `cellValue` / `cellOf`.

### Verification
Every suite listed was run; nothing was sampled.
- **List:**
  - mine, s8bn, s8bh, s8bf (`tsymex_rfc0005_s8bf_alias`), s8bd, s7_closure, s8i (`tsymex_rfc0005_s8i_models`), h_stepC (`tsymex_h_stepC_heapidentity`) and CR2 (`tsymex_phase15_CR2_cachekey`);
  - all 65 hits of `command grep -l '^var g\|case kind\|of RootObj' tests/tsymex_*.nim`;
  - every other `tsymex_rfc0005_*` suite and every `*audit*` suite, added after Windows caught source-reading audits.
  - s8be and s8ax have no suite on this base (`ls tests | command grep -i` finds nothing).
- **Results:**
  - Z3 5.1, c: 119 suites, 1997 tests, 0 failed. The first 69 ran at 1ed5ee1 and the other 50 at 25e7d1e. The only code change between them is a sort-checked `checkedEq` in place of a raw `Z3_mk_eq`.
  - Z3 4.13.4, c: 119 suites, 1997 tests, 0 failed, at 25e7d1e.
  - cpp, 5.1: the first 9 suites, 218/218.
  - The code tree of 25e7d1e is identical to 950f8df's.
- **Suite run time:** about 1.0 s for c on 5.1 and on 4.13.4, and 1.4 s for cpp, excluding the build. Measured alone, with the pause flag absent.

### Windows runs (head 950f8df), all green
- symex-mingw: 37147388099
- fuzzer-mingw: 37147388087
- fuzzer-msvc: 37147388080

Earlier runs:
- On 25e7d1e (the same code tree), all green: symex-mingw 37142238737, fuzzer-mingw 37142238669, fuzzer-msvc 37142238715.
- On 1ed5ee1, symex-mingw 37135115626 failed 4 suites:
  - `tsymex_rfc0005_s8m_exits`, its raw `Z3_mk_eq` audit;
  - `tsymex_r6_n27_placeholder_read_audit`, its marker count;
  - `tsymex_rfc0005_s8ao_remainder` and `tsymex_rfc0005_s8ap_remainder`, whose generic case object example is now modelled.
  - All four were fixed and repinned (see the RFC).

### Different mechanisms, reported and not fixed here
These are also in the RFC under "As landed (S8bw)".
- **PRECISION (blocked):** a pointer into a seq of aggregates. It needs S8bc's tree-seq backing and S8be's cells, which are not in this base.
- **PRECISION (blocked):** a pointer into a table of `string`, `float` or aggregate values. It needs S8ar and S8at; aggregate values are declined even on batch 5.
- **PRECISION:**
  - A partial write into an unwritten part declines: a symbolic-index write into an array-of-aggregates element, a variant global's partial write, or a `var`/`addr` actual whose part is unwritten.
  - A ptr deref whose candidate target is an unwritten part declines.
- **PRECISION:** `let p = addr gArr[1]` (an array element) stays heUnsafeCast, because S8an's alias takes no index.
- **PRECISION:** a deref that may reach an inactive branch declines that sub-path, since Nim's behaviour there is to read the overlapping bytes.
- **PRECISION:** `{.global.}` and `{.noinit.}` locals decline. S8be models `{.global.}` (`isRoutineGlobal`), and the integration supersedes this parse-time decline.

### Integration flags (for the integrator)
- S8be's `isRoutineGlobal` supersedes the pragma-local decline in dsl_parser's var/let arm.
- The `addrAliasDecl` extension (checked fields, var-param roots) sits on S8an's alias. S8bk's `placeLateAddr` is unaffected.
- `ptrAimInto` now walks fields by name for `f<name>` steps (new module `src/nelli/smt/ptraim.nim`). S8ax's `elemAddrNode` reconciliation (an S8bn note) is untouched.

Per-suite table: 5.1 c / 4.13.4 c / cpp, shown as ok/failed.

| suite | 5.1 c | 4.13.4 c | 5.1 cpp |
|---|---|---|---|
| tsymex_rfc0005_s8bw_remainder | 22/0 | 22/0 | 22/0 |
| tsymex_rfc0005_s8bh_remainder | 32/0 | 32/0 | 32/0 |
| tsymex_rfc0005_s8bn_remainder | 36/0 | 36/0 | 36/0 |
| tsymex_rfc0005_s8bf_alias | 13/0 | 13/0 | 13/0 |
| tsymex_rfc0005_s7_closure | 37/0 | 37/0 | 37/0 |
| tsymex_rfc0005_s8bd_remainder | 23/0 | 23/0 | 23/0 |
| tsymex_phase15_CR2_cachekey | 6/0 | 6/0 | 6/0 |
| tsymex_rfc0005_s8i_models | 39/0 | 39/0 | 39/0 |
| tsymex_h_stepC_heapidentity | 10/0 | 10/0 | 10/0 |
| tsymex_163audit_wave2 | 5/0 | 5/0 |  |
| tsymex_163rev_armfield_write | 4/0 | 4/0 |  |
| tsymex_163rev_degrade_classification | 8/0 | 8/0 |  |
| tsymex_163rev_assign_sites | 33/0 | 33/0 |  |
| tsymex_163rev_enum_positions | 13/0 | 13/0 |  |
| tsymex_h_verification | 18/0 | 18/0 |  |
| tsymex_CR2c_witnessreader_catchall | 17/0 | 17/0 |  |
| tsymex_p2b_refobjconstr_expr | 18/0 | 18/0 |  |
| tsymex_phase11_fielddefect | 5/0 | 5/0 |  |
| tsymex_phase11_walker | 11/0 | 11/0 |  |
| tsymex_phase12_witnesses | 10/0 | 10/0 |  |
| tsymex_phase14_arm_field_zero_init | 1/0 | 1/0 |  |
| tsymex_phase14_multivariant_ir | 2/0 | 2/0 |  |
| tsymex_phase14_disc_promotion | 2/0 | 2/0 |  |
| tsymex_phase14_multivariant_typebridge | 4/0 | 4/0 |  |
| tsymex_phase14_else_arms | 1/0 | 1/0 |  |
| tsymex_phase14_nonenum_disc | 1/0 | 1/0 |  |
| tsymex_phase14_symbolic_disc_reassign | 1/0 | 1/0 |  |
| tsymex_phase15_r6_refobj | 5/0 | 5/0 |  |
| tsymex_phase7_assertcovered | 22/0 | 22/0 |  |
| tsymex_r1_draingap | 11/0 | 11/0 |  |
| tsymex_r6_a1_variantlit | 8/0 | 8/0 |  |
| tsymex_r6_a2_retbind_variant | 9/0 | 9/0 |  |
| tsymex_r6_a3_variantconstruct_sym | 12/0 | 12/0 |  |
| tsymex_r6_a4_construct_interactions | 9/0 | 9/0 |  |
| tsymex_r6_a6_exported_field_names | 3/0 | 3/0 |  |
| tsymex_r6_bug2_scopeddecline | 12/0 | 12/0 |  |
| tsymex_r6_d2_recursive_budget | 7/0 | 7/0 |  |
| tsymex_r6_heap_raise_totality | 9/0 | 9/0 |  |
| tsymex_r6_b7r2_pathscope | 11/0 | 11/0 |  |
| tsymex_r6_itesv_mergedegrade | 11/0 | 11/0 |  |
| tsymex_r6_lows_blockparse | 6/0 | 6/0 |  |
| tsymex_r6_lows_declines | 15/0 | 15/0 |  |
| tsymex_r6_n13_reassign_seqarm | 7/0 | 7/0 |  |
| tsymex_r6_n14_seqops | 24/0 | 24/0 |  |
| tsymex_r6_n27_hof_placeholder | 6/0 | 6/0 |  |
| tsymex_r6_n39_variant_field_alloc | 10/0 | 10/0 |  |
| tsymex_r6_n36_raise_degrade | 8/0 | 8/0 |  |
| tsymex_r6_n40_alloc_totality | 10/0 | 10/0 |  |
| tsymex_r6_n49_dottedfield_mutation | 8/0 | 8/0 |  |
| tsymex_r6_n9_variant_budget | 7/0 | 7/0 |  |
| tsymex_r6_r1_placeholder_totality | 14/0 | 14/0 |  |
| tsymex_rectify_variants | 3/0 | 3/0 |  |
| tsymex_rfc0005_s4_alloc | 20/0 | 20/0 |  |
| tsymex_rfc0005_s3_monotonicity | 27/0 | 27/0 |  |
| tsymex_rfc0005_s6a_budget | 31/0 | 31/0 |  |
| tsymex_rfc0005_s8ac_remainder | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8an_remainder | 25/0 | 25/0 |  |
| tsymex_rfc0005_s8au_remainder | 35/0 | 35/0 |  |
| tsymex_rfc0005_s8ba_remainder | 32/0 | 32/0 |  |
| tsymex_rfc0005_s8e_scoping | 36/0 | 36/0 |  |
| tsymex_rfc0005_s8f_witness | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8g_models | 38/0 | 38/0 |  |
| tsymex_rfc0005_s8h_refwitness | 27/0 | 27/0 |  |
| tsymex_rfc0005_s8j_exits | 45/0 | 45/0 |  |
| tsymex_rfc0005_s8l_exits | 50/0 | 50/0 |  |
| tsymex_rfc0005_s8p_precision | 30/0 | 30/0 |  |
| tsymex_typebridge_variants | 3/0 | 3/0 |  |
| tsymex_rfc0005_s8s_precision | 29/0 | 29/0 |  |
| tsymex_tot1_totality_corpus | 21/0 | 21/0 |  |
| tsymex_163audit_w10 | 5/0 | 5/0 |  |
| tsymex_163audit_range_elem | 11/0 | 11/0 |  |
| tsymex_163audit_range_domain | 12/0 | 12/0 |  |
| tsymex_phase15_A2a_chokepoint_audit | 3/0 | 3/0 |  |
| tsymex_phase15_N2_kindgate_audit | 5/0 | 5/0 |  |
| tsymex_r11_range_invariant_audit | 7/0 | 7/0 |  |
| tsymex_r6_degrade_pairing_audit | 5/0 | 5/0 |  |
| tsymex_r6_n27_placeholder_read_audit | 4/0 | 4/0 |  |
| tsymex_163audit_w9 | 6/0 | 6/0 |  |
| tsymex_phase15_A2a_atomicir_audit | 9/0 | 9/0 |  |
| tsymex_r6_n36_raise_class_audit | 14/0 | 14/0 |  |
| tsymex_rfc0005_s0_exhibit | 10/0 | 10/0 |  |
| tsymex_rfc0005_s10_replay_verdict | 31/0 | 31/0 |  |
| tsymex_rfc0005_s11_surface | 34/0 | 34/0 |  |
| tsymex_rfc0005_s1b_kinds | 18/0 | 18/0 |  |
| tsymex_rfc0005_s1c_verdict | 24/0 | 24/0 |  |
| tsymex_rfc0005_s1_lattice | 23/0 | 23/0 |  |
| tsymex_rfc0005_s2_replay | 16/0 | 16/0 |  |
| tsymex_rfc0005_s6b_ops | 43/0 | 43/0 |  |
| tsymex_rfc0005_s5_str | 35/0 | 35/0 |  |
| tsymex_rfc0005_s8aa_remainder | 24/0 | 24/0 |  |
| tsymex_rfc0005_s8ad_remainder | 13/0 | 13/0 |  |
| tsymex_rfc0005_s8ab_letaudit | 28/0 | 28/0 |  |
| tsymex_rfc0005_s8ag_indexsplit | 15/0 | 15/0 |  |
| tsymex_rfc0005_s8aj_remainder | 21/0 | 21/0 |  |
| tsymex_rfc0005_s8ae_remainder | 16/0 | 16/0 |  |
| tsymex_rfc0005_s8ai_semantic | 25/0 | 25/0 |  |
| tsymex_rfc0005_s8am_remainder | 29/0 | 29/0 |  |
| tsymex_rfc0005_s8ao_remainder | 11/0 | 11/0 |  |
| tsymex_rfc0005_s8aq_remainder | 13/0 | 13/0 |  |
| tsymex_rfc0005_s8ap_remainder | 36/0 | 36/0 |  |
| tsymex_rfc0005_s8b_substitutions | 26/0 | 26/0 |  |
| tsymex_rfc0005_s8c_resolution | 25/0 | 25/0 |  |
| tsymex_rfc0005_s8d_typeheads | 17/0 | 17/0 |  |
| tsymex_rfc0005_s8k_bounds | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8m_exits | 32/0 | 32/0 |  |
| tsymex_rfc0005_s8n_precision | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8o_termination | 14/0 | 14/0 |  |
| tsymex_rfc0005_s8r_theoryfree | 3/0 | 3/0 |  |
| tsymex_rfc0005_s8q_termination | 10/0 | 10/0 |  |
| tsymex_rfc0005_s8_scope | 28/0 | 28/0 |  |
| tsymex_rfc0005_s8t_termination | 20/0 | 20/0 |  |
| tsymex_rfc0005_s8v_termination | 7/0 | 7/0 |  |
| tsymex_rfc0005_s8u_precision | 17/0 | 17/0 |  |
| tsymex_rfc0005_s8x_vm_alias | 7/0 | 7/0 |  |
| tsymex_rfc0005_s8w2_hotfix | 4/0 | 4/0 |  |
| tsymex_rfc0005_s8y_budget_decline | 8/0 | 8/0 |  |
| tsymex_rfc0005_s8w_remainder | 23/0 | 23/0 |  |
| tsymex_rfc0005_s9_vetoes | 19/0 | 19/0 |  |
| tsymex_rfc0005_s8z_remainder | 37/0 | 37/0 |  |

## Scratch-clobber incident (verdict: not affected)

No S8bw script, runner, probe or result ever lived in the shared session scratchpad.

- **Where everything lived:** in `/home/corey/tmp-usage/work/s8bw-work/`:
  - the runner `run.sh`;
  - the suite lists `verify.list`, `verify2.list` and `verifyall.list`;
  - the probe, RED and GREEN logs;
  - the `runs/` results;
  - `win1.log` and the commit message files.

  The probe sources lived in `wt/s8bw/probe/` and the RED copies in the `wt/s8bw-red` worktree; both have been removed.
- **Search:** `grep -rln 'scratchpad\|/tmp/claude'` over `run.sh`, the suite lists, `dt413.sh` and the worktree's `scripts/dt-bounded.sh` matches nothing.
- **Scratchpad contents:** files there named `red1`, `red2`, `red3` and `green4.log` are not S8bw's; `red1` holds S8bl suite logs.
- **Verdict:** no S8bw run needs re-running.
