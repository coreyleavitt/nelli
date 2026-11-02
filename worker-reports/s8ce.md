# DONE: S8ce

- **sha:** 62bed1c on `rfc-0005-s8ce` (tip, docs only). Code and tests are at ab93997, which is the Windows sha. Pushed.
- **base:** de6c67f (base 1f38a13). **walker:** 238, provisional.
- **nim-z3:** cc5ffc9a742c3251a16c95f1d3b98d4b93f05a91 on `origin/rfc-0005-s8ce`, off ae509f0. **Fast-forward nim-z3 main to this sha at integration.** Main is untouched, still ae509f0.
- **Lock:** identity `dag-sha256:9a033bebe5b01bc9633d0e12c9c68b8f2e358dd0cc7917d98226b0ab26eb68d8`, `commit_sha` cc5ffc9, `ref "main"` kept (S8at's shape). `milpa hash` gives this identity for both ref=<sha> and ref=rfc-0005-s8ce, and gives the old lock identity for ae509f0. In a fresh worktree, `milpa fetch` resolved `_deps/z3` to that identity and `milpa verify` reported 2 deps verified. `milpa --frozen fetch` could not be used there: it stopped because softlink's identity was not yet in the store.

## The defect and the generated-C citation
The base-build citations below come from the nimcache kept at `s8ce-work/nc_rs_base`.

Raise-path destroy, `@pnelli@ssmt@sruntime.nim.c:79705-79706` (`walkBlock`, runtime.nim `result = walk(s, result, w)`):
```c
T20_ = walk__OOZsrcZnelliZsmtZruntime_u131901((*s_1), result, w_p2);
if (NIM_UNLIKELY(*nimErr_)) {eqdestroy___OOZsrcZnelliZsmtZruntime_u121942(T20_); goto BeforeRet_;}
```
Where the flag is cleared: `@pz3@sbitvec.nim.c`, the `Z3BitVec` `=destroy` starting at line 359 (`termDestroy` inlined):
```c
T6_ = isNil__OOZ95depsZz3ZsrcZz3Zffi_u124(a_p0.raw);
if (NIM_UNLIKELY(*nimErr_)) goto LA1_;          /* flag already set on entry */
...
LA1_:;
if (isObjDisplayCheck(nimBorrowCurrentException()->Sup.m_type, 2, 3089888768)) {
    *nimErr_ = NIM_FALSE;                       /* the in-flight exception is cleared */
    popCurrentException();
```
Scan of the same test at base and fixed (`s8ce-work/cscan.py`, all modules):
| | base | fixed |
|---|---|---|
| hooks that pop an exception | 50 | 0 |
| nim-z3 hooks reading the error flag | 51 of 51 | 0 of 51 |

The base build has 197 reassigned-temporary sites and 62 merge-label sites unsaved, 259 in all (the job's "~290"; the count is a regex heuristic). Runtime.nim alone has 106 + 43.

**Compiler role.** Nim's unsaved raise-path destroy is what enables this, and the `try` in the hook is what swallows. Pure-Nim reduction, no Z3 (`s8ce-work/probe/purenim.nim`), observed this session: `purenim` and `purenim_init` print `(LOST)` on c, and `caught IOError (OK)` on cpp. `purenim_notry` is OK on both.
```nim
type Obj = object
  p: int
proc mayRaise(x: int) {.raises: [ValueError].} =
  if x == 999: raise newException(ValueError, "x")
proc `=destroy`(o: Obj) {.raises: [].} =
  try: mayRaise(o.p)
  except CatchableError: discard
proc f(n: int): seq[Obj] =
  result = @[Obj(p: n)]
  if n > 0: raise newException(IOError, "boom")
proc g(n: int): seq[Obj] =
  result = @[Obj(p: 1)]
  result = f(n)
try: echo "LOST ", g(1).len
except IOError: echo "OK"
```
This listing is condensed from the file; the file itself is what was run.

## Design, per item
1. **Mechanism pin:** `tests/tsymex_rfc0005_s8ce_hookraise.nim`.
2. **Root fix (nim-z3 27be0a0, cc5ffc9):** every `=destroy` / `=copy` / `=dup` and the refcount helpers have no `try`, call the raw C entry through softlink's `<sym>Ptr()`, and are `{.raises: [], quirky.}`. `quirky` is required: without it, a try-free hook entered with the flag set leaves at its first checked call and leaks its dec_ref and context release (pinned under `-d:z3CtxDestroyCount`). The regression test is `tests/thook_raise_path.nim`, which includes a source audit of every hook.
3. **Lock bump:** as above.
4. **Nelli sites:** `src/nelli` declares no hooks, and neither does softlink. S8bx's extraction hook is **removed** (`extractionRaiseHook`, `extractionFault`, its `shouldStop` arm, `runSymex`'s fallback), because it is redundant: extraction raises now reach `runSymexCaught`, and no walker `try` encloses `trySolve`. S8bx's seven pins are unchanged and green.
5. **Shapes:** `tests/tsymex_rfc0005_s8ce_raiseshapes.nim` with test-only `injectShapeFault`. The inherited version was not RED at base: its raises left the walk with an empty result, so no term was destroyed, and its control was itself wrong (unsatisfiable). I rewrote it so each raise happens with Z3 values live.

**Shape caveat.** The destroy that swallowed was only located for the S8bx case and the probe's two tracebacks, both in `walkBlock`. Most shapes are probably lost at that same site, so `roots` and `conds` are distinct raise origins, and are not shown to be distinct swallow sites. The comment on `injectShapeFault` in runtime.nim implies a helper's local `seq[Z3Bool]` swallows. That is probably wrong, because `Z3Bool` takes a field-wise destroy (see the Z3Ast item below). The comment is harmless to behaviour and I did not churn CI for it. Coverage of all sites rests on the generated-C scan (0 hooks pop), with the shapes as witnesses.

## RED and GREEN observed
On base nim-z3 (ae509f0), C backend, unless stated:
| pin | base hooks, S8bx hook present | hook removed | fixed nim-z3, hook removed |
|---|---|---|---|
| hookraise (6 tests + control) | not re-run in this form | 6 FAILED, control OK | c/cpp/4.13.4: 7 OK |
| raiseshapes: term in loop, solver, roots, conds, `if` condition | FAILED, `sxUnknown` with the raise unreported | same | OK |
| raiseshapes: dispatch, term in callee | FAILED, **false `sxUnsat`** | same | OK |
| raiseshapes: `mpairs` view live | FAILED, `sxUnknown` with the raise unreported | same | OK |
| raiseshapes: concolic walk | FAILED, raise did not reach caller | same | OK |
| raiseshapes: model eval in extraction | OK, masked by S8bx's hook | FAILED, raise unreported | OK |
| S8bx extractraise: afterLoop, twoIters | not re-run | FAILED, **false `sxUnsat`** | OK |
| S8bx extractraise: swallowedInside | not re-run | FAILED, **false `sxSat`** | OK |

- In the "S8bx hook present" run, `raiseshapes` was built before the walker bump, so its walker floor test also failed. That failure is unrelated to the defect.
- On cpp with base nim-z3 and the hook removed: hookraise 7 OK, raiseshapes 13 OK. So the loss is C-only.
- The hookraise RED at the original pin commit is in `logs/hookraise_c_base.log` (6 FAILED, from the earlier session). The table's run is the one observed this session.
- nim-z3's `thook_raise_path` RED at ae509f0 is from the earlier session (`logs/z3t_base_c.log`). Its GREEN was re-observed this session.

## Soundness bugs found
**SOUNDNESS:** any raise crossing a live Z3 value's destroy on the C backend was lost, giving a false `sxUnsat` or `sxSat`, or an `sxUnknown` that hides the fault. Fixed.

## Verification
**Full `tsymex_*` on c, Z3 5.1 and 4.13.4, from worktree `wt/s8ce-gate` at 5bfa104.** Each suite was compiled once and the same binary run on each libz3; `z3FullVersion()` was confirmed to switch between 5.1.0.0 and 4.13.4.0.
- **433 of 434 passed on both versions.**
- The one failure was `tsymex_r6_n36_raise_class_audit`, a count pin that needed the new injection site added. ab93997 fixes it and changes only that test file; re-run at ab93997 it gave 14 OK on c 5.1, c 4.13.4 and cpp 5.1.
- So the gate sha and the final sha differ by that one test plus RFC text. The full set was not re-run at ab93997. The per-suite table is at the end of this report.

**Named suites (`logs/own.summary`, run at 429317c, code identical to ab93997 apart from the n36 pin):**
| suite | backend | Z3 | rc | counts |
|---|---|---|---|---|
| tsymex_configdefaults | c | 51 | 0 | ok=24 failed=0 |
| tsymex_phase15_CR2_cachekey | c | 51 | 0 | ok=6 failed=0 |
| tsymex_phase15_F7_float_extract | c | 51 | 0 | ok=7 failed=0 |
| tsymex_rfc0005_s8bx_extractraise | cpp | 51 | 0 | ok=7 failed=0 |
| tsymex_rfc0005_s8bx_iterchange | c | 51 | 0 | ok=6 failed=0 |
| tsymex_rfc0005_s8bx_iterchange | cpp | 51 | 0 | ok=6 failed=0 |
| tsymex_rfc0005_s8bx_mpairs | c | 51 | 0 | ok=8 failed=0 |
| tsymex_rfc0005_s8bx_mpairs | cpp | 51 | 0 | ok=8 failed=0 |
| tsymex_rfc0005_s8bx_setlenstr | c | 51 | 0 | ok=3 failed=0 |
| tsymex_rfc0005_s8bx_setlenstr | cpp | 51 | 0 | ok=3 failed=0 |
| tsymex_rfc0005_s8bx_witnessdrift | c | 51 | 0 | ok=3 failed=0 |
| tsymex_rfc0005_s8bx_witnessdrift | cpp | 51 | 0 | ok=3 failed=0 |
| tsymex_rfc0005_s8ce_hookraise | c | 413 | 0 | ok=7 failed=0 |
| tsymex_rfc0005_s8ce_hookraise | c | 51 | 0 | ok=7 failed=0 |
| tsymex_rfc0005_s8ce_hookraise | cpp | 51 | 0 | ok=7 failed=0 |
| tsymex_rfc0005_s8ce_raiseshapes | c | 413 | 0 | ok=13 failed=0 |
| tsymex_rfc0005_s8ce_raiseshapes | c | 51 | 0 | ok=13 failed=0 |
| tsymex_rfc0005_s8ce_raiseshapes | cpp | 51 | 0 | ok=13 failed=0 |
| tsymex_rfc0005_s8m_exits | c | 51 | 0 | ok=32 failed=0 |

`tsymex_rfc0005_s8bx_extractraise` on c is covered by the gate; it also passed 7 OK in the hook-removed run.

**nim-z3 suite at cc5ffc9, c and cpp on Z3 5.1 (144 files, `logs/z3suite_fix.summary`):** 140 pass.
- `tffi`, `tversion`, `tmultiversion` fail on 5.1 because they assert a 4.x runtime. All three pass on 4.13.4, c and cpp.
- `tregex_index` hangs on 5.1 at the same test at both ae509f0 and cc5ffc9 (each killed at 1300 s on c). It passes 37/37 in 2 s on 4.13.4, c and cpp.
- `tminimal` passes c and cpp.
- **Not run:** valgrind (not in the image) and `tests/run.sh examples`. The other 140 files were run on 5.1 only.

## Windows (ab93997, all green)
- symex-mingw **41430089289** (18 of 18 jobs), fuzzer-mingw **41430089256**, fuzzer-msvc **41430089284**.
- The tip 62bed1c is docs only and started no runs (5bfa104, also docs only, started none either).
- Earlier symex-mingw runs 41410074619 (429317c) and 41409508233 (8c66166) failed in shard 6. 41410074619 failed on the n36 pin; I did not read the logs of 41409508233.

**Times.** From the logs, `==>` to `<==` is compile + run. "wall" is the run alone.
- New suites: hookraise 3.6 s (wall 0 s); raiseshapes 35.5 s (wall 0.5 s).
- Over 60 s compile + run at ab93997, with de6c67f run 37177992419 for comparison:
| suite | ab93997 s | de6c67f s |
|---|---|---|
| tsymex_161_overflow_obligation | 122.2 | 43.7 |
| tsymex_rfc0005_s8ai_semantic | 108.6 | 111.1 |
| tsymex_rfc0005_s8ar_remainder | 103.6 | 104.6 |
| tsymex_rfc0005_s8at_remainder | 91.0 | 92.7 |
| tsymex_rfc0005_s8an_remainder | 84.4 | 87.5 |
| tsymex_rfc0005_s8ab_letaudit | 83.2 | 86.9 |
| tsymex_rfc0005_s8s_precision | 78.2 | 49.1 |
| tsymex_rfc0005_s8z_remainder | 77.0 | 46.1 |
| tsymex_phase15_A1_callarg | 76.8 | 35.3 |
| tsymex_rfc0005_s8ae_remainder | 61.4 | 67.9 |
- By run wall alone, only `tsymex_rfc0005_s8ai_semantic` is over 60 s (80.7 s).
- Of the four that grew, `tsymex_161` and `A1_callarg` kept the same run wall (1.4 vs 1.5 s, 0.6 vs 0.6 s) and `s8z` barely moved (1.7 vs 1.2 s), so their growth is compile time. `tsymex_161` runs first in its shard. `s8s_precision` run wall went from 13.2 s to 19.1 s, cause not investigated. They also changed shards between the two runs. Median compile + run is 28.0 s against 30.9 s at base.
- The full per-file table is at the end. It has the 425 corpus files. The 9 scan-tail suites run as separate jobs without these markers, so they are not in it.

## Different mechanisms, reported and not fixed here (also in the RFC under "As landed (S8ce)")
- **PRECISION:** ADR-0023's "a lowering-time degrade must never raise" rule and its in-band sinks were written for this hazard. Unchanged; they could be simplified later.
- **PRECISION:** S8m's `z3ApiErrorCount` fallback stays. It also counts API errors caught inside the walk.
- **PRECISION:** nim-z3 leaks with no verdict effect: `Z3FuncDeclOwn`, `Z3FuncInterpOwn` and `Z3RcfNum` hooks never release `ctx`.
- **PRECISION:** `Z3Ast[S: static]`'s custom hooks are not used for `Z3Int` / `Z3Bool`: the generated C has no hook attributed to `ast.nim`, so those values get a field-wise destroy, and by inference never dec_ref. They also never ran the `try`.
- **PRECISION:** nim-z3's tests on Z3 5.1: the three version asserts and the `tregex_index` hang above.
- **Compiler (unmarked in the RFC list; PRECISION for this project, since nothing here is affected now):** a `try` in any other destructor still loses a raise on Nim 2.2.10's C backend. The reduction above is ready for an upstream issue.

## Coordinator decisions
1. Fast-forward nim-z3 main to cc5ffc9 at integration.
2. Whether the gate at 5bfa104 plus the n36 re-run is enough, or you want a re-sweep at ab93997.
3. Whether to require the valgrind leak gate for nim-z3; the image has no valgrind, and this slice changes every hook.
4. Whether to file the upstream Nim issue.

## Per-file Windows times (symex-mingw 41430089289, ab93997)
| suite | compile+run s | run wall s | job |
|---|---|---|---|
| tsymex_161_overflow_obligation | 122.2 | 1.4 | corpus (shard 0) |
| tsymex_162_range_base_width | 37.2 | 0.5 | corpus (shard 1) |
| tsymex_163_opaque_transparent | 34.8 | 0.2 | corpus (shard 2) |
| tsymex_163audit_range_domain | 33.1 | 0.1 | corpus (shard 3) |
| tsymex_163audit_range_elem | 44.3 | 0.1 | corpus (shard 4) |
| tsymex_163audit_w10 | 19.5 | 0.1 | corpus (shard 5) |
| tsymex_163audit_w9 | 39.8 | 0.6 | corpus (shard 6) |
| tsymex_163audit_wave2 | 32.4 | 0.1 | corpus (shard 7) |
| tsymex_163rev_armfield_write | 25.4 | 0.1 | corpus (shard 0) |
| tsymex_163rev_assign_rangedefect | 26.6 | 0.1 | corpus (shard 1) |
| tsymex_163rev_assign_scope | 30.7 | 0.1 | corpus (shard 2) |
| tsymex_163rev_assign_sites | 35.8 | 0.5 | corpus (shard 3) |
| tsymex_163rev_concolic_diagnostics | 32.3 | 0.4 | corpus (shard 4) |
| tsymex_163rev_concolic_flip_width | 18.3 | 0.1 | corpus (shard 5) |
| tsymex_163rev_concolic_modes | 32.9 | 0.2 | corpus (shard 6) |
| tsymex_163rev_degrade_classification | 33.3 | 4.5 | corpus (shard 7) |
| tsymex_163rev_disc_domain | 7.9 | 0 | corpus (shard 0) |
| tsymex_163rev_enum_domain | 27.6 | 0.2 | corpus (shard 1) |
| tsymex_163rev_enum_field_witness | 31.3 | 0.1 | corpus (shard 2) |
| tsymex_163rev_enum_ordinal | 32.2 | 0.1 | corpus (shard 3) |
| tsymex_163rev_enum_positions | 37.3 | 0.2 | corpus (shard 4) |
| tsymex_163rev_enum_valueshapes | 16.5 | 0.1 | corpus (shard 5) |
| tsymex_163rev_frontier_default | 29.2 | 0.6 | corpus (shard 6) |
| tsymex_163rev_inert_argfork | 31.2 | 0.1 | corpus (shard 7) |
| tsymex_163rev_inert_exclusions | 25.9 | 0.2 | corpus (shard 0) |
| tsymex_163rev_int_literal_width | 29.6 | 0.2 | corpus (shard 1) |
| tsymex_163rev_intoffset_range | 30.7 | 0.3 | corpus (shard 2) |
| tsymex_163rev_nested_clamp | 26.3 | 0.1 | corpus (shard 3) |
| tsymex_163rev_parser_gaps | 27.9 | 0.1 | corpus (shard 4) |
| tsymex_163rev_range_bounds | 16.6 | 0.1 | corpus (shard 5) |
| tsymex_163rev_scan_counter_range | 29.8 | 0.3 | corpus (shard 6) |
| tsymex_163rev_seqelem_promoted_int | 28.0 | 0.1 | corpus (shard 7) |
| tsymex_163rev_table_elem | 26.0 | 0.1 | corpus (shard 0) |
| tsymex_163rev_transparent_guard | 25.9 | 0.1 | corpus (shard 1) |
| tsymex_163rev_transparent_result | 28.5 | 0.1 | corpus (shard 2) |
| tsymex_163rev_variant_armfield | 27.2 | 0.1 | corpus (shard 3) |
| tsymex_CR2a_expr_catchall | 29.3 | 0.1 | corpus (shard 7) |
| tsymex_CR2b_paramtype_catchall | 26.3 | 0.1 | corpus (shard 0) |
| tsymex_CR2c_witnessreader_catchall | 33.3 | 0.2 | corpus (shard 1) |
| tsymex_a2_refvariant_fields | 28.2 | 0.2 | corpus (shard 4) |
| tsymex_a3_closure_iterators | 17.4 | 0.4 | corpus (shard 5) |
| tsymex_a6_symlen_hof | 28.7 | 0.1 | corpus (shard 6) |
| tsymex_a7_rune | 32.2 | 0.8 | corpus (shard 7) |
| tsymex_a7_runes_iter | 32.8 | 0.1 | corpus (shard 0) |
| tsymex_a8_radix | 26.5 | 0.1 | corpus (shard 1) |
| tsymex_a9_casefold | 29.5 | 0.1 | corpus (shard 2) |
| tsymex_augmented_assign | 50.2 | 21.3 | corpus (shard 3) |
| tsymex_canonicalize | 4.8 | 0 | corpus (shard 4) |
| tsymex_configdefaults | 51.1 | 33.5 | corpus (shard 5) |
| tsymex_cr22_label_assert_coexist | 28.9 | 0.1 | corpus (shard 6) |
| tsymex_cr9c_intrep | 32.4 | 0.2 | corpus (shard 2) |
| tsymex_discard_raise | 27.1 | 0.1 | corpus (shard 3) |
| tsymex_funcdef_callee | 25.9 | 0.1 | corpus (shard 4) |
| tsymex_g1a_mode | 17.4 | 0.2 | corpus (shard 5) |
| tsymex_g1b_concolic | 33.8 | 0.2 | corpus (shard 6) |
| tsymex_g2_flip | 38.2 | 6.7 | corpus (shard 7) |
| tsymex_g3fix_walkergap | 25.5 | 0.1 | corpus (shard 0) |
| tsymex_g4_cmpwalk | 25.1 | 0.1 | corpus (shard 1) |
| tsymex_g6_algebra | 3.7 | 0 | corpus (shard 2) |
| tsymex_g6_transform_binding | 28.0 | 0.2 | corpus (shard 3) |
| tsymex_h_containers | 30.3 | 0.2 | corpus (shard 4) |
| tsymex_h_stepA_nominalid | 1.6 | 0 | corpus (shard 5) |
| tsymex_h_stepC_heapidentity | 30.4 | 0.1 | corpus (shard 6) |
| tsymex_h_verification | 34.2 | 0.2 | corpus (shard 7) |
| tsymex_h_witness | 28.1 | 0.2 | corpus (shard 0) |
| tsymex_inv_structured_kinds | 24.5 | 0.1 | corpus (shard 1) |
| tsymex_m6_probeproto_strproto | 32.4 | 0.5 | corpus (shard 2) |
| tsymex_p1_tupleconstr_expr | 29.0 | 0.2 | corpus (shard 3) |
| tsymex_p2a_objconstr_expr | 30.4 | 0.1 | corpus (shard 4) |
| tsymex_p2b_refobjconstr_expr | 18.6 | 0.4 | corpus (shard 5) |
| tsymex_phase11_fielddefect | 26.2 | 0.1 | corpus (shard 3) |
| tsymex_phase11_walker | 30.0 | 0.2 | corpus (shard 4) |
| tsymex_phase12_derandomize | 16.3 | 0.1 | corpus (shard 5) |
| tsymex_phase12_forall | 12.1 | 0 | corpus (shard 6) |
| tsymex_phase12_notapplicable | 2.9 | 0 | corpus (shard 7) |
| tsymex_phase12_phase_closure | 3.0 | 0 | corpus (shard 0) |
| tsymex_phase12_pipeline | 5.7 | 0 | corpus (shard 1) |
| tsymex_phase12_renderchoices | 10.8 | 0 | corpus (shard 2) |
| tsymex_phase12_scan | 3.3 | 0 | corpus (shard 3) |
| tsymex_phase12_seedphase | 5.3 | 0 | corpus (shard 4) |
| tsymex_phase12_sink | 1.6 | 0 | corpus (shard 5) |
| tsymex_phase12_sugar | 30.0 | 0 | corpus (shard 6) |
| tsymex_phase12_witnesses | 30.3 | 0.1 | corpus (shard 7) |
| tsymex_phase13_acceptunknown_guard | 10.7 | 0 | corpus (shard 0) |
| tsymex_phase13_layer1_wire | 27.0 | 0.1 | corpus (shard 1) |
| tsymex_phase13_macro | 13.0 | 0 | corpus (shard 2) |
| tsymex_phase13_rlimit | 26.1 | 0 | corpus (shard 3) |
| tsymex_phase13_satsuffix | 12.2 | 0 | corpus (shard 4) |
| tsymex_phase13_unknown_roundtrip | 6.1 | 0 | corpus (shard 5) |
| tsymex_phase13_unsat_roundtrip | 12.1 | 0 | corpus (shard 6) |
| tsymex_phase13_verdict_primitives | 11.9 | 0 | corpus (shard 7) |
| tsymex_phase14_arm_field_zero_init | 25.1 | 0.1 | corpus (shard 0) |
| tsymex_phase14_b2_forcephases | 2.6 | 0 | corpus (shard 1) |
| tsymex_phase14_b3_trace_equivalence | 10.5 | 0 | corpus (shard 2) |
| tsymex_phase14_b5_replaymiss | 2.8 | 0 | corpus (shard 3) |
| tsymex_phase14_b67_label_filter | 27.6 | 0 | corpus (shard 4) |
| tsymex_phase14_c1_fromcache | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase14_c2_dberrors | 2.9 | 0 | corpus (shard 6) |
| tsymex_phase14_c4_z3error | 26.8 | 0 | corpus (shard 7) |
| tsymex_phase14_disc_promotion | 25.5 | 0.1 | corpus (shard 0) |
| tsymex_phase14_else_arms | 24.6 | 0.1 | corpus (shard 1) |
| tsymex_phase14_frontier_pruning | 28.3 | 0.2 | corpus (shard 2) |
| tsymex_phase14_multivariant_ir | 3.0 | 0 | corpus (shard 3) |
| tsymex_phase14_multivariant_typebridge | 3.0 | 0 | corpus (shard 4) |
| tsymex_phase14_multivariant_walker | 15.3 | 0 | corpus (shard 5) |
| tsymex_phase14_multivariant_witness | 32.4 | 0.1 | corpus (shard 6) |
| tsymex_phase14_nonenum_disc | 26.8 | 0 | corpus (shard 7) |
| tsymex_phase14_strategy_digest | 21.1 | 0 | corpus (shard 0) |
| tsymex_phase14_symbolic_disc_reassign | 24.7 | 0.1 | corpus (shard 1) |
| tsymex_phase14_var_param | 27.3 | 0 | corpus (shard 2) |
| tsymex_phase14_var_param_downstream | 27.7 | 0.1 | corpus (shard 3) |
| tsymex_phase15_A1_arithmetic | 31.5 | 4.4 | corpus (shard 4) |
| tsymex_phase15_A1_assertarg | 15.3 | 0.3 | corpus (shard 5) |
| tsymex_phase15_A1_bitwise | 33.5 | 0.3 | corpus (shard 6) |
| tsymex_phase15_A1_boolean | 30.4 | 0.6 | corpus (shard 7) |
| tsymex_phase15_A1_callarg | 76.8 | 0.6 | corpus (shard 0) |
| tsymex_phase15_A1_comparison | 25.8 | 0.3 | corpus (shard 1) |
| tsymex_phase15_A1_loopguard | 32.7 | 3.1 | corpus (shard 2) |
| tsymex_phase15_A1_unary | 29.0 | 0.3 | corpus (shard 3) |
| tsymex_phase15_A2a_atomicir_audit | 29.0 | 0.7 | corpus (shard 4) |
| tsymex_phase15_A2a_atomize | 16.2 | 0.1 | corpus (shard 5) |
| tsymex_phase15_A2a_chokepoint_audit | 5.8 | 0.4 | corpus (shard 6) |
| tsymex_phase15_A2a_guardcond_pin | 26.9 | 0.1 | corpus (shard 7) |
| tsymex_phase15_A2b_bitwise | 46.8 | 0.3 | corpus (shard 0) |
| tsymex_phase15_C1_canonical_kind | 29.1 | 0.3 | corpus (shard 1) |
| tsymex_phase15_C1_ir | 27.7 | 0.1 | corpus (shard 2) |
| tsymex_phase15_C2_staticparams | 26.6 | 0.1 | corpus (shard 3) |
| tsymex_phase15_C2a_closure_capture | 23.6 | 0 | corpus (shard 4) |
| tsymex_phase15_C2b_closure_call | 15.3 | 0.1 | corpus (shard 5) |
| tsymex_phase15_C3_proc_as_value | 30.7 | 0.1 | corpus (shard 6) |
| tsymex_phase15_C4_hof | 32.6 | 2.3 | corpus (shard 7) |
| tsymex_phase15_C5_closure_eq | 40.6 | 0.1 | corpus (shard 0) |
| tsymex_phase15_C6_smoke | 28.0 | 0.3 | corpus (shard 1) |
| tsymex_phase15_CR10_regex_overflow | 6.0 | 0 | corpus (shard 3) |
| tsymex_phase15_CR11_CR18_splitcap | 27.1 | 0 | corpus (shard 4) |
| tsymex_phase15_CR14_exn_missing | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase15_CR15_enum_ordinal | 28.5 | 0 | corpus (shard 6) |
| tsymex_phase15_CR1_CR5_closure_heap | 28.6 | 0.1 | corpus (shard 2) |
| tsymex_phase15_CR21_parseintraise_arg | 41.1 | 0.1 | corpus (shard 0) |
| tsymex_phase15_CR2_cachekey | 3.5 | 0 | corpus (shard 7) |
| tsymex_phase15_CR3_CR4_CR6_float | 28.4 | 0.3 | corpus (shard 1) |
| tsymex_phase15_E1_ir | 26.2 | 0 | corpus (shard 4) |
| tsymex_phase15_E2a_cascade | 15.1 | 0 | corpus (shard 5) |
| tsymex_phase15_E2b_raise | 26.7 | 0.1 | corpus (shard 6) |
| tsymex_phase15_E3_try | 34.4 | 0.1 | corpus (shard 7) |
| tsymex_phase15_E4_hierarchy | 37.3 | 0.1 | corpus (shard 0) |
| tsymex_phase15_E4a_userexn | 24.6 | 0.1 | corpus (shard 1) |
| tsymex_phase15_E5_finally | 30.0 | 0.1 | corpus (shard 2) |
| tsymex_phase15_E6_defect | 27.6 | 0.1 | corpus (shard 3) |
| tsymex_phase15_E7_smoke | 29.8 | 0.1 | corpus (shard 4) |
| tsymex_phase15_E8_getcurrentexn | 15.7 | 0.1 | corpus (shard 5) |
| tsymex_phase15_E_roundtrip | 26.4 | 0.1 | corpus (shard 3) |
| tsymex_phase15_F1_typebridge | 27.5 | 0 | corpus (shard 6) |
| tsymex_phase15_F2_float_literals | 33.4 | 0.1 | corpus (shard 7) |
| tsymex_phase15_F3_float_arith | 26.7 | 0.3 | corpus (shard 0) |
| tsymex_phase15_F4_float_compare | 30.4 | 0.1 | corpus (shard 1) |
| tsymex_phase15_F5_float_conv | 38.5 | 0.1 | corpus (shard 2) |
| tsymex_phase15_F5_probeproto | 39.9 | 0.4 | corpus (shard 3) |
| tsymex_phase15_F5hang_derefwrite | 35.1 | 0.1 | corpus (shard 4) |
| tsymex_phase15_F6_float_math | 18.7 | 0.5 | corpus (shard 5) |
| tsymex_phase15_F7_float_extract | 32.4 | 2.9 | corpus (shard 6) |
| tsymex_phase15_F8_smoke | 38.1 | 1 | corpus (shard 7) |
| tsymex_phase15_F9a_array_float | 25.8 | 0.1 | corpus (shard 0) |
| tsymex_phase15_F9b_seq_float | 26.3 | 0.1 | corpus (shard 1) |
| tsymex_phase15_F9c_variant_float | 35.2 | 0.1 | corpus (shard 2) |
| tsymex_phase15_G1a_instkey | 35.6 | 0.1 | corpus (shard 4) |
| tsymex_phase15_G1c_instcap | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase15_H1_path_heap_fields | 10.0 | 0 | corpus (shard 3) |
| tsymex_phase15_M1_seq_fixedwidth | 31.9 | 0.2 | corpus (shard 7) |
| tsymex_phase15_M2_parsebiggestint | 27.1 | 0.2 | corpus (shard 0) |
| tsymex_phase15_N0_kindgate_widen | 30.0 | 0.3 | corpus (shard 1) |
| tsymex_phase15_N1_resolution_gates | 28.0 | 0 | corpus (shard 2) |
| tsymex_phase15_N2_kindgate_audit | 8.5 | 5.3 | corpus (shard 3) |
| tsymex_phase15_N3_scan_boundary | 27.4 | 0.3 | corpus (shard 4) |
| tsymex_phase15_R1a_ir | 26.8 | 0 | corpus (shard 4) |
| tsymex_phase15_S10a_strconv | 26.0 | 0.2 | corpus (shard 1) |
| tsymex_phase15_S10b_strconv | 29.0 | 0.1 | corpus (shard 2) |
| tsymex_phase15_S11_mutation | 27.6 | 0.1 | corpus (shard 3) |
| tsymex_phase15_S1_typebridge | 25.3 | 0.1 | corpus (shard 0) |
| tsymex_phase15_S2_strlit | 28.1 | 0.1 | corpus (shard 4) |
| tsymex_phase15_S3_strindex | 16.0 | 0.1 | corpus (shard 5) |
| tsymex_phase15_S4_strpred | 30.7 | 0.1 | corpus (shard 6) |
| tsymex_phase15_S5_strops | 30.5 | 0.1 | corpus (shard 7) |
| tsymex_phase15_S6a_regex_parser | 5.7 | 0 | corpus (shard 0) |
| tsymex_phase15_S6b_regex | 26.7 | 0.2 | corpus (shard 1) |
| tsymex_phase15_S7a_bytes | 29.3 | 0.1 | corpus (shard 2) |
| tsymex_phase15_S7b_smoke | 29.1 | 0.2 | corpus (shard 3) |
| tsymex_phase15_S8_concat | 27.7 | 0.1 | corpus (shard 4) |
| tsymex_phase15_S9_caseconv | 16.0 | 0.1 | corpus (shard 5) |
| tsymex_phase15_cr9_lowerInExpr | 31.9 | 0.4 | corpus (shard 2) |
| tsymex_phase15_fieldcontainer | 31.9 | 0.2 | corpus (shard 3) |
| tsymex_phase15_g3_type_subst | 27.8 | 0 | corpus (shard 6) |
| tsymex_phase15_g4_distinct_sort | 28.6 | 0.1 | corpus (shard 7) |
| tsymex_phase15_g5_distinct_borrow | 26.5 | 0.1 | corpus (shard 0) |
| tsymex_phase15_g6_concept_constraint | 29.5 | 0.1 | corpus (shard 1) |
| tsymex_phase15_g7_static_param | 28.3 | 0.1 | corpus (shard 2) |
| tsymex_phase15_l1_boundary | 30.5 | 0 | corpus (shard 4) |
| tsymex_phase15_l2_untyped_template | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase15_l3_quote_do | 28.0 | 0.1 | corpus (shard 6) |
| tsymex_phase15_r10_budget | 29.6 | 0.1 | corpus (shard 6) |
| tsymex_phase15_r11_unsafecast | 28.7 | 0 | corpus (shard 7) |
| tsymex_phase15_r11b_smoke | 27.9 | 0.2 | corpus (shard 0) |
| tsymex_phase15_r12_bumps | 25.3 | 0.1 | corpus (shard 1) |
| tsymex_phase15_r13_closure_ref | 26.9 | 0 | corpus (shard 2) |
| tsymex_phase15_r13_ptr_finally | 26.7 | 0 | corpus (shard 3) |
| tsymex_phase15_r1_refsort | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase15_r1b_callheap | 15.0 | 0 | corpus (shard 5) |
| tsymex_phase15_r2_new | 28.8 | 0.1 | corpus (shard 6) |
| tsymex_phase15_r3_deref_read | 28.5 | 0.1 | corpus (shard 7) |
| tsymex_phase15_r4_deref_write | 27.0 | 0.1 | corpus (shard 0) |
| tsymex_phase15_r5_nil | 26.2 | 0.1 | corpus (shard 1) |
| tsymex_phase15_r6_refobj | 29.1 | 0.1 | corpus (shard 2) |
| tsymex_phase15_r7_alias_chain | 29.8 | 0.1 | corpus (shard 3) |
| tsymex_phase15_r8_ptr | 27.8 | 0.1 | corpus (shard 4) |
| tsymex_phase15_r8b_varref | 14.7 | 0 | corpus (shard 5) |
| tsymex_phase15_r9_recursive | 28.5 | 0.1 | corpus (shard 6) |
| tsymex_phase15_rereview_drains | 34.3 | 0.3 | corpus (shard 7) |
| tsymex_phase15_z0_carryover | 4.9 | 0 | corpus (shard 6) |
| tsymex_phase15_z1_canary | 6.7 | 0 | corpus (shard 7) |
| tsymex_phase15_z3_infra | 8.2 | 0 | corpus (shard 0) |
| tsymex_phase15_z3c_classify | 24.9 | 0.1 | corpus (shard 1) |
| tsymex_phase15_z4_walkctx | 28.0 | 0 | corpus (shard 2) |
| tsymex_phase16_A5_float_classify | 30.2 | 0.2 | corpus (shard 3) |
| tsymex_phase16_CR1a_bitwise_svint | 28.4 | 0.2 | corpus (shard 4) |
| tsymex_phase16_CR1b_tail_local | 15.6 | 0.1 | corpus (shard 5) |
| tsymex_phase16_CR1c_internal_fault | 27.1 | 0 | corpus (shard 6) |
| tsymex_phase16_D1a_defect_routeraise | 27.5 | 0.1 | corpus (shard 7) |
| tsymex_phase16_D1c_shortcircuit | 26.9 | 0.2 | corpus (shard 0) |
| tsymex_phase16_R16_1_arithcheck_foundation | 3.6 | 0 | corpus (shard 4) |
| tsymex_phase16_R16_2_rangedefect | 18.0 | 0.1 | corpus (shard 5) |
| tsymex_phase16_R16_2b_shortcircuit_conv | 29.2 | 0.2 | corpus (shard 6) |
| tsymex_phase16_R16_3_divzero | 30.1 | 0.1 | corpus (shard 7) |
| tsymex_phase16_R16_4_overflow | 28.2 | 0.3 | corpus (shard 0) |
| tsymex_phase16_R16_5_overflow_thru_closure | 25.6 | 0.2 | corpus (shard 1) |
| tsymex_phase16_R16_6_diagnostics_channel | 27.4 | 0.1 | corpus (shard 2) |
| tsymex_phase16_m3_rfind | 26.8 | 0.2 | corpus (shard 1) |
| tsymex_phase16_m4_str_add_ampeq | 31.1 | 0.1 | corpus (shard 2) |
| tsymex_phase16_m5_ifexpr_minmax | 29.4 | 0.2 | corpus (shard 3) |
| tsymex_phase1_arith | 31.3 | 0.1 | corpus (shard 6) |
| tsymex_phase1_assert | 27.1 | 0.1 | corpus (shard 7) |
| tsymex_phase1_bool | 24.8 | 0.1 | corpus (shard 0) |
| tsymex_phase1_dsl | 3.7 | 0 | corpus (shard 1) |
| tsymex_phase1_let | 27.7 | 0 | corpus (shard 2) |
| tsymex_phase2_abstraction | 28.3 | 0.1 | corpus (shard 3) |
| tsymex_phase2_bv_arith | 27.9 | 0.1 | corpus (shard 4) |
| tsymex_phase2_fallback | 22.2 | 0 | corpus (shard 5) |
| tsymex_phase2_overflow | 28.7 | 0.1 | corpus (shard 6) |
| tsymex_phase3_inline | 29.9 | 0.1 | corpus (shard 7) |
| tsymex_phase3_mutual | 24.8 | 0.1 | corpus (shard 0) |
| tsymex_phase3_recursion | 26.5 | 1.1 | corpus (shard 1) |
| tsymex_phase3_stdlib | 10.3 | 0 | corpus (shard 2) |
| tsymex_phase3_summarization | 26.2 | 0 | corpus (shard 3) |
| tsymex_phase4_array | 26.9 | 0.1 | corpus (shard 4) |
| tsymex_phase4_nested | 19.3 | 0 | corpus (shard 5) |
| tsymex_phase4_oob | 26.8 | 0 | corpus (shard 6) |
| tsymex_phase4_tuple | 28.9 | 0.1 | corpus (shard 7) |
| tsymex_phase5_hashset | 24.8 | 0.1 | corpus (shard 0) |
| tsymex_phase5_models | 9.9 | 0 | corpus (shard 1) |
| tsymex_phase5_seq | 29.0 | 0.1 | corpus (shard 2) |
| tsymex_phase5_table | 26.7 | 0 | corpus (shard 3) |
| tsymex_phase6_break | 28.3 | 1.9 | corpus (shard 4) |
| tsymex_phase6_case | 15.5 | 0 | corpus (shard 5) |
| tsymex_phase6_for | 28.7 | 0.5 | corpus (shard 6) |
| tsymex_phase6_while | 27.8 | 0.2 | corpus (shard 7) |
| tsymex_phase7_assertcovered | 37.2 | 0.4 | corpus (shard 0) |
| tsymex_q1_scanlift | 29.3 | 1.2 | corpus (shard 1) |
| tsymex_q1_sibling_collision | 28.2 | 0.1 | corpus (shard 2) |
| tsymex_r11_range_invariant_audit | 3.6 | 0.3 | corpus (shard 4) |
| tsymex_r14_case2_degrade | 19.0 | 4 | corpus (shard 5) |
| tsymex_r14_continue_guard | 31.6 | 1.3 | corpus (shard 6) |
| tsymex_r1_draingap | 50.9 | 20.8 | corpus (shard 3) |
| tsymex_r1b_shortcircuit_oob | 34.9 | 0.9 | corpus (shard 7) |
| tsymex_r2_scanbound | 25.4 | 0.5 | corpus (shard 0) |
| tsymex_r4_seq_slice | 27.9 | 0.3 | corpus (shard 1) |
| tsymex_r4_slice_binding | 29.7 | 0.3 | corpus (shard 2) |
| tsymex_r4_strip | 39.4 | 11.8 | corpus (shard 3) |
| tsymex_r5_bv32_width | 27.4 | 0.2 | corpus (shard 4) |
| tsymex_r5_const_fold | 15.0 | 0.1 | corpus (shard 5) |
| tsymex_r5_discard | 27.1 | 0.1 | corpus (shard 6) |
| tsymex_r5_neg_bool_conv | 27.8 | 0.1 | corpus (shard 7) |
| tsymex_r5_tuple_return | 25.0 | 0.1 | corpus (shard 0) |
| tsymex_r6_a0_lowhigh | 27.5 | 0.1 | corpus (shard 1) |
| tsymex_r6_a1_variantlit | 31.9 | 0.1 | corpus (shard 2) |
| tsymex_r6_a2_retbind_variant | 28.9 | 0.2 | corpus (shard 3) |
| tsymex_r6_a3_variantconstruct_sym | 30.1 | 0.2 | corpus (shard 4) |
| tsymex_r6_a4_construct_interactions | 17.0 | 0.4 | corpus (shard 5) |
| tsymex_r6_a6_exported_field_names | 28.5 | 0.1 | corpus (shard 6) |
| tsymex_r6_b0_scanlift_bound | 27.6 | 0.1 | corpus (shard 7) |
| tsymex_r6_b1_stringbacked | 26.9 | 0.6 | corpus (shard 0) |
| tsymex_r6_b2_intwidth | 27.7 | 0.4 | corpus (shard 1) |
| tsymex_r6_b3_scanpair | 30.3 | 0.4 | corpus (shard 2) |
| tsymex_r6_b4_readcstring | 30.6 | 0.8 | corpus (shard 3) |
| tsymex_r6_d2_recursive_budget | 27.9 | 0.1 | corpus (shard 4) |
| tsymex_r6_degrade_pairing_audit | 1.8 | 0.1 | corpus (shard 5) |
| tsymex_r6_heap_raise_totality | 30.3 | 0.1 | corpus (shard 6) |
| tsymex_r6_itesv_mergedegrade | 31.3 | 0.2 | corpus (shard 7) |
| tsymex_r6_lows_blockparse | 25.9 | 0.1 | corpus (shard 0) |
| tsymex_r6_lows_collectors | 26.5 | 0.3 | corpus (shard 1) |
| tsymex_r6_lows_declines | 34.2 | 0.2 | corpus (shard 2) |
| tsymex_r6_n10_coverage_matrix | 33.8 | 0.6 | corpus (shard 3) |
| tsymex_r6_n13_reassign_seqarm | 28.5 | 0.1 | corpus (shard 4) |
| tsymex_r6_n14_seqops | 19.7 | 0.3 | corpus (shard 5) |
| tsymex_r6_n16_closure_zerodefault | 31.0 | 0.2 | corpus (shard 6) |
| tsymex_r6_n20_boundedloop | 28.8 | 0.3 | corpus (shard 7) |
| tsymex_r6_n21_pairloop_member | 30.3 | 0.3 | corpus (shard 0) |
| tsymex_r6_n27_hof_placeholder | 26.4 | 0.2 | corpus (shard 1) |
| tsymex_r6_n27_placeholder_read_audit | 3.5 | 0.2 | corpus (shard 2) |
| tsymex_r6_n28_shadow_collision | 27.9 | 0.2 | corpus (shard 3) |
| tsymex_r6_n29_seqlit_sortmismatch | 28.6 | 0.1 | corpus (shard 4) |
| tsymex_r6_n31_block_counter | 16.1 | 0.1 | corpus (shard 5) |
| tsymex_r6_n36_raise_class_audit | 4.0 | 0.4 | corpus (shard 6) |
| tsymex_r6_n36_raise_degrade | 47.7 | 17.2 | corpus (shard 7) |
| tsymex_r6_n37_raise_residue | 29.1 | 0.7 | corpus (shard 0) |
| tsymex_r6_n39_variant_field_alloc | 27.8 | 0.2 | corpus (shard 1) |
| tsymex_r6_n40_alloc_totality | 31.1 | 0.1 | corpus (shard 2) |
| tsymex_r6_n42_deref_taint | 30.5 | 0.3 | corpus (shard 3) |
| tsymex_r6_n43_parity | 30.2 | 0.1 | corpus (shard 4) |
| tsymex_r6_n49_dottedfield_mutation | 16.3 | 0.1 | corpus (shard 5) |
| tsymex_r6_n9_variant_budget | 29.3 | 0.1 | corpus (shard 6) |
| tsymex_r6_r1_placeholder_totality | 32.9 | 0.2 | corpus (shard 7) |
| tsymex_r6_r2_zerodefault_result | 33.7 | 0.6 | corpus (shard 0) |
| tsymex_r6_r3_svint_overflow | 27.5 | 0.5 | corpus (shard 1) |
| tsymex_r6_r4_collector_scoping | 31.8 | 0.4 | corpus (shard 2) |
| tsymex_r6_r5_pairloop_counter | 29.2 | 0.2 | corpus (shard 3) |
| tsymex_r6_r6_emit_roundtrip | 7.1 | 0 | corpus (shard 4) |
| tsymex_r7_caseexpr | 15.3 | 0.1 | corpus (shard 5) |
| tsymex_r8_omitted_field_degrade | 28.2 | 0 | corpus (shard 6) |
| tsymex_rectify_abstraction | 27.6 | 0 | corpus (shard 7) |
| tsymex_rectify_cardinality | 24.6 | 0.1 | corpus (shard 0) |
| tsymex_rectify_effects | 25.9 | 0.1 | corpus (shard 1) |
| tsymex_rectify_generics | 28.0 | 0 | corpus (shard 2) |
| tsymex_rectify_mutation | 28.9 | 0.1 | corpus (shard 3) |
| tsymex_rectify_nested_arrays | 25.9 | 0 | corpus (shard 4) |
| tsymex_rectify_refs | 14.9 | 0 | corpus (shard 5) |
| tsymex_rectify_variants | 28.2 | 0.1 | corpus (shard 6) |
| tsymex_retest_c11_stack | 27.2 | 0.1 | corpus (shard 7) |
| tsymex_retest_c3_bitwise_guard | 26.1 | 0.2 | corpus (shard 0) |
| tsymex_retest_c5b_unknown_errors | 27.8 | 3.4 | corpus (shard 1) |
| tsymex_retest_c6_tuple_chain | 39.2 | 11.2 | corpus (shard 2) |
| tsymex_retest_char_needle | 27.3 | 0.1 | corpus (shard 3) |
| tsymex_retest_defect_net | 25.7 | 0 | corpus (shard 4) |
| tsymex_retest_infix_degrade | 14.9 | 0.1 | corpus (shard 5) |
| tsymex_retest_pred_succ | 28.2 | 0.1 | corpus (shard 6) |
| tsymex_rfc0005_s0_exhibit | 29.8 | 0.1 | corpus (shard 7) |
| tsymex_rfc0005_s10_replay_verdict | 34.3 | 0.6 | corpus (shard 1) |
| tsymex_rfc0005_s11_surface | 51.7 | 1 | corpus (shard 2) |
| tsymex_rfc0005_s1_lattice | 23.5 | 0.3 | corpus (shard 0) |
| tsymex_rfc0005_s1b_kinds | 30.1 | 0.8 | corpus (shard 3) |
| tsymex_rfc0005_s1c_verdict | 39.6 | 10.8 | corpus (shard 4) |
| tsymex_rfc0005_s2_replay | 19.9 | 0.1 | corpus (shard 5) |
| tsymex_rfc0005_s3_monotonicity | 40.1 | 1.6 | corpus (shard 6) |
| tsymex_rfc0005_s4_alloc | 30.3 | 0.2 | corpus (shard 7) |
| tsymex_rfc0005_s5_str | 34.4 | 0.5 | corpus (shard 0) |
| tsymex_rfc0005_s6a_budget | 30.5 | 1.7 | corpus (shard 1) |
| tsymex_rfc0005_s6b_ops | 38.9 | 0.8 | corpus (shard 2) |
| tsymex_rfc0005_s7_closure | 35.9 | 1.4 | corpus (shard 3) |
| tsymex_rfc0005_s8_scope | 35.9 | 1.5 | corpus (shard 4) |
| tsymex_rfc0005_s8aa_remainder | 25.2 | 2.7 | corpus (shard 5) |
| tsymex_rfc0005_s8ab_letaudit | 83.2 | 0 | corpus (shard 6) |
| tsymex_rfc0005_s8ac_remainder | 53.4 | 2.7 | corpus (shard 7) |
| tsymex_rfc0005_s8ad_remainder | 39.3 | 5.9 | corpus (shard 0) |
| tsymex_rfc0005_s8ae_remainder | 61.4 | 34.7 | corpus (shard 1) |
| tsymex_rfc0005_s8ag_indexsplit | 46.1 | 15 | corpus (shard 2) |
| tsymex_rfc0005_s8ai_semantic | 108.6 | 80.7 | corpus (shard 3) |
| tsymex_rfc0005_s8aj_remainder | 48.4 | 2.8 | corpus (shard 4) |
| tsymex_rfc0005_s8am_remainder | 22.9 | 0.7 | corpus (shard 5) |
| tsymex_rfc0005_s8an_remainder | 84.4 | 9.2 | corpus (shard 6) |
| tsymex_rfc0005_s8ao_remainder | 33.6 | 0.2 | corpus (shard 7) |
| tsymex_rfc0005_s8ap_remainder | 57.8 | 1.9 | corpus (shard 0) |
| tsymex_rfc0005_s8aq_remainder | 41.5 | 14.6 | corpus (shard 1) |
| tsymex_rfc0005_s8ar_remainder | 103.6 | 3.9 | corpus (shard 2) |
| tsymex_rfc0005_s8at_remainder | 91.0 | 2.4 | corpus (shard 3) |
| tsymex_rfc0005_s8b_substitutions | 32.5 | 0.3 | corpus (shard 4) |
| tsymex_rfc0005_s8bc_remainder_a | 28.6 | 0.6 | corpus (shard 5) |
| tsymex_rfc0005_s8bc_remainder_b | 56.1 | 1.3 | corpus (shard 6) |
| tsymex_rfc0005_s8bc_remainder_c | 57.0 | 3.5 | corpus (shard 7) |
| tsymex_rfc0005_s8bl_borrow | 26.7 | 0.2 | corpus (shard 0) |
| tsymex_rfc0005_s8bl_gaps | 43.4 | 11.9 | corpus (shard 1) |
| tsymex_rfc0005_s8bl_magics | 36.9 | 0.2 | corpus (shard 2) |
| tsymex_rfc0005_s8bl_magicscan | 27.3 | 0.1 | corpus (shard 3) |
| tsymex_rfc0005_s8bl_pairloop | 34.9 | 2.4 | corpus (shard 4) |
| tsymex_rfc0005_s8bl_seqops | 16.6 | 0.3 | corpus (shard 5) |
| tsymex_rfc0005_s8bl_setlen | 42.9 | 2 | corpus (shard 6) |
| tsymex_rfc0005_s8bx_extractraise | 33.7 | 3.9 | corpus (shard 7) |
| tsymex_rfc0005_s8bx_iterchange | 28.4 | 0.9 | corpus (shard 0) |
| tsymex_rfc0005_s8bx_mpairs | 37.9 | 3.3 | corpus (shard 1) |
| tsymex_rfc0005_s8bx_setlenstr | 34.5 | 3 | corpus (shard 2) |
| tsymex_rfc0005_s8bx_witnessdrift | 26.5 | 0 | corpus (shard 3) |
| tsymex_rfc0005_s8c_resolution | 36.3 | 0.3 | corpus (shard 4) |
| tsymex_rfc0005_s8ce_hookraise | 3.6 | 0 | corpus (shard 5) |
| tsymex_rfc0005_s8ce_raiseshapes | 35.5 | 0.5 | corpus (shard 6) |
| tsymex_rfc0005_s8d_typeheads | 33.9 | 0.1 | corpus (shard 7) |
| tsymex_rfc0005_s8e_scoping | 39.5 | 0.6 | corpus (shard 0) |
| tsymex_rfc0005_s8f_witness | 35.9 | 1 | corpus (shard 1) |
| tsymex_rfc0005_s8g_models | 40.5 | 0.7 | corpus (shard 2) |
| tsymex_rfc0005_s8h_refwitness | 37.3 | 0.4 | corpus (shard 3) |
| tsymex_rfc0005_s8i_models | 36.9 | 0.5 | corpus (shard 4) |
| tsymex_rfc0005_s8j_exits | 19.7 | 0.3 | corpus (shard 5) |
| tsymex_rfc0005_s8k_bounds | 36.3 | 3.3 | corpus (shard 6) |
| tsymex_rfc0005_s8l_exits | 54.8 | 1 | corpus (shard 7) |
| tsymex_rfc0005_s8m_exits | 42.5 | 1.3 | corpus (shard 0) |
| tsymex_rfc0005_s8n_precision | 34.1 | 0.7 | corpus (shard 1) |
| tsymex_rfc0005_s8o_termination | 31.3 | 0.4 | corpus (shard 2) |
| tsymex_rfc0005_s8p_precision | 50.2 | 2.7 | corpus (shard 3) |
| tsymex_rfc0005_s8q_termination | 29.0 | 0.3 | corpus (shard 4) |
| tsymex_rfc0005_s8r_theoryfree | 15.1 | 0.1 | corpus (shard 5) |
| tsymex_rfc0005_s8s_precision | 78.2 | 19.1 | corpus (shard 6) |
| tsymex_rfc0005_s8t_termination | 43.4 | 6.7 | corpus (shard 7) |
| tsymex_rfc0005_s8u_precision | 45.0 | 0.9 | corpus (shard 0) |
| tsymex_rfc0005_s8v_termination | 25.1 | 0.2 | corpus (shard 1) |
| tsymex_rfc0005_s8w2_hotfix | 27.3 | 0.1 | corpus (shard 3) |
| tsymex_rfc0005_s8w_remainder | 45.6 | 6.3 | corpus (shard 2) |
| tsymex_rfc0005_s8x_vm_alias | 3.3 | 0 | corpus (shard 4) |
| tsymex_rfc0005_s8y_budget_decline | 18.6 | 3.2 | corpus (shard 5) |
| tsymex_rfc0005_s8z_remainder | 77.0 | 1.7 | corpus (shard 6) |
| tsymex_rfc0005_s9_vetoes | 36.2 | 0.3 | corpus (shard 7) |
| tsymex_snd1_uncertain_taint | 25.9 | 0.1 | corpus (shard 0) |
| tsymex_snd1b_closure_uncertain_axiom | 25.2 | 0.2 | corpus (shard 1) |
| tsymex_snd2_assume | 30.9 | 0.1 | corpus (shard 2) |
| tsymex_snd3_6_equality_loop | 26.1 | 0.2 | corpus (shard 3) |
| tsymex_snd3_loopdegrade | 29.7 | 2 | corpus (shard 4) |
| tsymex_snd4_strindex_oob | 15.5 | 0.1 | corpus (shard 5) |
| tsymex_tot1_totality_corpus | 34.9 | 0.2 | corpus (shard 6) |
| tsymex_typebridge_variants | 3.1 | 0 | corpus (shard 7) |
| tsymex_uninit_var | 26.3 | 0.2 | corpus (shard 0) |

## Per-suite gate table (5bfa104, c; same binary on Z3 5.1 and 4.13.4)
`ok` and `failed` are summed across the two runs.

| suite | compile rc | 5.1 rc | 4.13.4 rc | ok | failed |
|---|---|---|---|---|---|
| tsymex_163audit_range_domain | 0 | 0 | 0 | 24 | 0 |
| tsymex_163audit_range_elem | 0 | 0 | 0 | 22 | 0 |
| tsymex_163audit_w10 | 0 | 0 | 0 | 10 | 0 |
| tsymex_163audit_w9 | 0 | 0 | 0 | 12 | 0 |
| tsymex_163audit_wave2 | 0 | 0 | 0 | 10 | 0 |
| tsymex_163_opaque_transparent | 0 | 0 | 0 | 30 | 0 |
| tsymex_163rev_armfield_write | 0 | 0 | 0 | 8 | 0 |
| tsymex_163rev_assign_rangedefect | 0 | 0 | 0 | 18 | 0 |
| tsymex_163rev_assign_scope | 0 | 0 | 0 | 20 | 0 |
| tsymex_163rev_assign_sites | 0 | 0 | 0 | 66 | 0 |
| tsymex_163rev_concolic_diagnostics | 0 | 0 | 0 | 50 | 0 |
| tsymex_163rev_concolic_flip_width | 0 | 0 | 0 | 26 | 0 |
| tsymex_163rev_concolic_modes | 0 | 0 | 0 | 38 | 0 |
| tsymex_162_range_base_width | 0 | 0 | 0 | 42 | 0 |
| tsymex_163rev_disc_domain | 0 | 0 | 0 | 14 | 0 |
| tsymex_163rev_degrade_classification | 0 | 0 | 0 | 16 | 0 |
| tsymex_163rev_enum_domain | 0 | 0 | 0 | 38 | 0 |
| tsymex_163rev_enum_field_witness | 0 | 0 | 0 | 24 | 0 |
| tsymex_163rev_enum_ordinal | 0 | 0 | 0 | 28 | 0 |
| tsymex_163rev_enum_positions | 0 | 0 | 0 | 26 | 0 |
| tsymex_163rev_enum_valueshapes | 0 | 0 | 0 | 18 | 0 |
| tsymex_163rev_frontier_default | 0 | 0 | 0 | 18 | 0 |
| tsymex_163rev_inert_argfork | 0 | 0 | 0 | 18 | 0 |
| tsymex_163rev_inert_exclusions | 0 | 0 | 0 | 30 | 0 |
| tsymex_163rev_int_literal_width | 0 | 0 | 0 | 54 | 0 |
| tsymex_163rev_intoffset_range | 0 | 0 | 0 | 18 | 0 |
| tsymex_163rev_nested_clamp | 0 | 0 | 0 | 10 | 0 |
| tsymex_163rev_parser_gaps | 0 | 0 | 0 | 20 | 0 |
| tsymex_163rev_range_bounds | 0 | 0 | 0 | 22 | 0 |
| tsymex_163rev_scan_counter_range | 0 | 0 | 0 | 20 | 0 |
| tsymex_163rev_seqelem_promoted_int | 0 | 0 | 0 | 6 | 0 |
| tsymex_163rev_table_elem | 0 | 0 | 0 | 12 | 0 |
| tsymex_161_overflow_obligation | 0 | 0 | 0 | 38 | 0 |
| tsymex_163rev_transparent_result | 0 | 0 | 0 | 8 | 0 |
| tsymex_163rev_variant_armfield | 0 | 0 | 0 | 12 | 0 |
| tsymex_a2_refvariant_fields | 0 | 0 | 0 | 18 | 0 |
| tsymex_a3_closure_iterators | 0 | 0 | 0 | 22 | 0 |
| tsymex_a6_symlen_hof | 0 | 0 | 0 | 6 | 0 |
| tsymex_a7_rune | 0 | 0 | 0 | 24 | 0 |
| tsymex_a7_runes_iter | 0 | 0 | 0 | 12 | 0 |
| tsymex_a8_radix | 0 | 0 | 0 | 12 | 0 |
| tsymex_a9_casefold | 0 | 0 | 0 | 10 | 0 |
| tsymex_canonicalize | 0 | 0 | 0 | 64 | 0 |
| tsymex_augmented_assign | 0 | 0 | 0 | 16 | 0 |
| tsymex_configdefaults | 0 | 0 | 0 | 48 | 0 |
| tsymex_cr22_label_assert_coexist | 0 | 0 | 0 | 10 | 0 |
| tsymex_CR2a_expr_catchall | 0 | 0 | 0 | 14 | 0 |
| tsymex_CR2b_paramtype_catchall | 0 | 0 | 0 | 8 | 0 |
| tsymex_CR2c_witnessreader_catchall | 0 | 0 | 0 | 34 | 0 |
| tsymex_cr9c_intrep | 0 | 0 | 0 | 20 | 0 |
| tsymex_discard_raise | 0 | 0 | 0 | 8 | 0 |
| tsymex_funcdef_callee | 0 | 0 | 0 | 10 | 0 |
| tsymex_g1a_mode | 0 | 0 | 0 | 12 | 0 |
| tsymex_g1b_concolic | 0 | 0 | 0 | 30 | 0 |
| tsymex_163rev_transparent_guard | 0 | 0 | 0 | 18 | 0 |
| tsymex_g3fix_walkergap | 0 | 0 | 0 | 2 | 0 |
| tsymex_g2_flip | 0 | 0 | 0 | 16 | 0 |
| tsymex_g6_algebra | 0 | 0 | 0 | 26 | 0 |
| tsymex_g4_cmpwalk | 0 | 0 | 0 | 2 | 0 |
| tsymex_h_stepA_nominalid | 0 | 0 | 0 | 6 | 0 |
| tsymex_g6_transform_binding | 0 | 0 | 0 | 12 | 0 |
| tsymex_h_containers | 0 | 0 | 0 | 24 | 0 |
| tsymex_h_stepC_heapidentity | 0 | 0 | 0 | 20 | 0 |
| tsymex_h_witness | 0 | 0 | 0 | 22 | 0 |
| tsymex_h_verification | 0 | 0 | 0 | 36 | 0 |
| tsymex_inv_structured_kinds | 0 | 0 | 0 | 4 | 0 |
| tsymex_m6_probeproto_strproto | 0 | 0 | 0 | 20 | 0 |
| tsymex_p1_tupleconstr_expr | 0 | 0 | 0 | 22 | 0 |
| tsymex_p2a_objconstr_expr | 0 | 0 | 0 | 28 | 0 |
| tsymex_phase11_fielddefect | 0 | 0 | 0 | 10 | 0 |
| tsymex_p2b_refobjconstr_expr | 0 | 0 | 0 | 36 | 0 |
| tsymex_phase12_forall | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_notapplicable | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_phase_closure | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase11_walker | 0 | 0 | 0 | 22 | 0 |
| tsymex_phase12_pipeline | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_derandomize | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_scan | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase12_sink | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_seedphase | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase12_renderchoices | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase13_acceptunknown_guard | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase12_sugar | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase12_witnesses | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase13_macro | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase13_layer1_wire | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase13_satsuffix | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase13_unknown_roundtrip | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase13_rlimit | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase13_unsat_roundtrip | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase13_verdict_primitives | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase14_b3_trace_equivalence | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_b5_replaymiss | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_arm_field_zero_init | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase14_b67_label_filter | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_c1_fromcache | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_c2_dberrors | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase14_c4_z3error | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_disc_promotion | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_else_arms | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase14_frontier_pruning | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase14_multivariant_ir | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_multivariant_typebridge | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase14_b2_forcephases | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase14_multivariant_witness | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_nonenum_disc | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase14_strategy_digest | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase14_symbolic_disc_reassign | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase14_var_param_downstream | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase14_var_param | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase15_A1_arithmetic | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_A1_assertarg | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_A1_bitwise | 0 | 0 | 0 | 16 | 0 |
| tsymex_phase15_A1_boolean | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_A1_callarg | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_A1_comparison | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase14_multivariant_walker | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_A1_unary | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_A2a_atomicir_audit | 0 | 0 | 0 | 18 | 0 |
| tsymex_phase15_A2a_chokepoint_audit | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_A2a_atomize | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_A2a_guardcond_pin | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_A2b_bitwise | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_C1_canonical_kind | 0 | 0 | 0 | 22 | 0 |
| tsymex_phase15_A1_loopguard | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_C2a_closure_capture | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_C2_staticparams | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_C3_proc_as_value | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_C4_hof | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_C5_closure_eq | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_C6_smoke | 0 | 0 | 0 | 18 | 0 |
| tsymex_phase15_CR10_regex_overflow | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_CR11_CR18_splitcap | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_CR14_exn_missing | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_CR15_enum_ordinal | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_CR1_CR5_closure_heap | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_CR21_parseintraise_arg | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_CR2_cachekey | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_CR3_CR4_CR6_float | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_cr9_lowerInExpr | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_C2b_closure_call | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_E2a_cascade | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_E2b_raise | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_E3_try | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase15_E4a_userexn | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_E4_hierarchy | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_E5_finally | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_E6_defect | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_E1_ir | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_E7_smoke | 0 | 0 | 0 | 24 | 0 |
| tsymex_phase15_E8_getcurrentexn | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_E_roundtrip | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_F1_typebridge | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_F2_float_literals | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_F3_float_arith | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_F4_float_compare | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_F5_float_conv | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_F5hang_derefwrite | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_F5_probeproto | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_F6_float_math | 0 | 0 | 0 | 30 | 0 |
| tsymex_phase15_F7_float_extract | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_F8_smoke | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_F9a_array_float | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_F9b_seq_float | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_F9c_variant_float | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_fieldcontainer | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_g10_smoke | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_G1a_instkey | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_G1c_instcap | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_g3_type_subst | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_g4_distinct_sort | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_g5_distinct_borrow | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_g6_concept_constraint | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_g7_static_param | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_H1_path_heap_fields | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_g8_multi_param | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_l1_boundary | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_l2_untyped_template | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_l3_quote_do | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_M1_seq_fixedwidth | 0 | 0 | 0 | 26 | 0 |
| tsymex_phase15_C1_ir | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_M2_parsebiggestint | 0 | 0 | 0 | 16 | 0 |
| tsymex_phase15_N0_kindgate_widen | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_N2_kindgate_audit | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_N1_resolution_gates | 0 | 0 | 0 | 64 | 0 |
| tsymex_phase15_N3_scan_boundary | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_r10_budget | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_r11b_smoke | 0 | 0 | 0 | 22 | 0 |
| tsymex_phase15_r11_unsafecast | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_r12_bumps | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_r13_closure_ref | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase15_r13_ptr_finally | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase15_R1a_ir | 0 | 0 | 0 | 18 | 0 |
| tsymex_phase15_r1b_callheap | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_r1_refsort | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_r2_new | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_r3_deref_read | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_r4_deref_write | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_r5_nil | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_r6_refobj | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_r8b_varref | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_r7_alias_chain | 0 | 0 | 0 | 18 | 0 |
| tsymex_phase15_r8_ptr | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_r9_recursive | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase15_rereview_drains | 0 | 0 | 0 | 30 | 0 |
| tsymex_phase15_S10a_strconv | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_S10b_strconv | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_S11_mutation | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_S1_typebridge | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_S2_strlit | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_S3_strindex | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_S6a_regex_parser | 0 | 0 | 0 | 42 | 0 |
| tsymex_phase15_S4_strpred | 0 | 0 | 0 | 16 | 0 |
| tsymex_phase15_S5_strops | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase15_S6b_regex | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_S7a_bytes | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase15_S7b_smoke | 0 | 0 | 0 | 16 | 0 |
| tsymex_phase15_z0_carryover | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase15_S8_concat | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_z1_canary | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase15_z3_infra | 0 | 0 | 0 | 22 | 0 |
| tsymex_phase15_S9_caseconv | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase15_z3c_classify | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase15_z4_walkctx | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase16_A5_float_classify | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase16_CR1a_bitwise_svint | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase16_CR1b_tail_local | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase16_CR1c_internal_fault | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase16_D1a_defect_routeraise | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase16_D1c_shortcircuit | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase16_m3_rfind | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase16_R16_1_arithcheck_foundation | 0 | 0 | 0 | 44 | 0 |
| tsymex_phase16_m4_str_add_ampeq | 0 | 0 | 0 | 24 | 0 |
| tsymex_phase16_m5_ifexpr_minmax | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase16_R16_2b_shortcircuit_conv | 0 | 0 | 0 | 12 | 0 |
| tsymex_phase16_R16_2_rangedefect | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase16_R16_3_divzero | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase16_R16_4_overflow | 0 | 0 | 0 | 20 | 0 |
| tsymex_phase16_R16_5_overflow_thru_closure | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase16_R16_6_diagnostics_channel | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase1_arith | 0 | 0 | 0 | 14 | 0 |
| tsymex_phase1_assert | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase1_dsl | 0 | 0 | 0 | 36 | 0 |
| tsymex_phase1_bool | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase1_let | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase2_abstraction | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase2_bv_arith | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase2_fallback | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase2_overflow | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase3_inline | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase3_stdlib | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase3_mutual | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase3_recursion | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase3_summarization | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase4_array | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase4_nested | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase4_oob | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase4_tuple | 0 | 0 | 0 | 8 | 0 |
| tsymex_phase5_hashset | 0 | 0 | 0 | 2 | 0 |
| tsymex_phase5_models | 0 | 0 | 0 | 10 | 0 |
| tsymex_phase5_seq | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase5_table | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase6_break | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase6_case | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase6_for | 0 | 0 | 0 | 6 | 0 |
| tsymex_phase6_while | 0 | 0 | 0 | 4 | 0 |
| tsymex_phase7_assertcovered | 0 | 0 | 0 | 44 | 0 |
| tsymex_q1_scanlift | 0 | 0 | 0 | 26 | 0 |
| tsymex_q1_sibling_collision | 0 | 0 | 0 | 4 | 0 |
| tsymex_r11_range_invariant_audit | 0 | 0 | 0 | 14 | 0 |
| tsymex_r14_continue_guard | 0 | 0 | 0 | 20 | 0 |
| tsymex_r1b_shortcircuit_oob | 0 | 0 | 0 | 38 | 0 |
| tsymex_r14_case2_degrade | 0 | 0 | 0 | 4 | 0 |
| tsymex_r2_scanbound | 0 | 0 | 0 | 6 | 0 |
| tsymex_r4_seq_slice | 0 | 0 | 0 | 20 | 0 |
| tsymex_r1_draingap | 0 | 0 | 0 | 22 | 0 |
| tsymex_r4_slice_binding | 0 | 0 | 0 | 12 | 0 |
| tsymex_r5_bv32_width | 0 | 0 | 0 | 16 | 0 |
| tsymex_r5_const_fold | 0 | 0 | 0 | 12 | 0 |
| tsymex_r5_discard | 0 | 0 | 0 | 10 | 0 |
| tsymex_r5_neg_bool_conv | 0 | 0 | 0 | 8 | 0 |
| tsymex_r5_tuple_return | 0 | 0 | 0 | 6 | 0 |
| tsymex_r6_a0_lowhigh | 0 | 0 | 0 | 20 | 0 |
| tsymex_r6_a1_variantlit | 0 | 0 | 0 | 16 | 0 |
| tsymex_r6_a2_retbind_variant | 0 | 0 | 0 | 18 | 0 |
| tsymex_r6_a3_variantconstruct_sym | 0 | 0 | 0 | 24 | 0 |
| tsymex_r4_strip | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_a4_construct_interactions | 0 | 0 | 0 | 18 | 0 |
| tsymex_r6_a6_exported_field_names | 0 | 0 | 0 | 6 | 0 |
| tsymex_r6_a6r_callwitness | 0 | 0 | 0 | 24 | 0 |
| tsymex_r6_b0_scanlift_bound | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_b1_stringbacked | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_b2_intwidth | 0 | 0 | 0 | 36 | 0 |
| tsymex_r6_b3_scanpair | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_b4_readcstring | 0 | 0 | 0 | 26 | 0 |
| tsymex_r6_b5_chained | 0 | 0 | 0 | 18 | 0 |
| tsymex_r6_b6_optionregion | 0 | 0 | 0 | 16 | 0 |
| tsymex_r6_bug2_scopeddecline | 0 | 0 | 0 | 24 | 0 |
| tsymex_r6_b7r_bytescan | 0 | 0 | 0 | 52 | 0 |
| tsymex_r6_degrade_pairing_audit | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_d2_recursive_budget | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_heap_raise_totality | 0 | 0 | 0 | 18 | 0 |
| tsymex_r6_b7r2_pathscope | 0 | 0 | 0 | 22 | 0 |
| tsymex_r6_itesv_mergedegrade | 0 | 0 | 0 | 22 | 0 |
| tsymex_r6_lows_blockparse | 0 | 0 | 0 | 12 | 0 |
| tsymex_r6_lows_collectors | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_lows_declines | 0 | 0 | 0 | 30 | 0 |
| tsymex_r6_n10_coverage_matrix | 0 | 0 | 0 | 44 | 0 |
| tsymex_r6_n13_reassign_seqarm | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_n14_seqops | 0 | 0 | 0 | 48 | 0 |
| tsymex_r6_n16_closure_zerodefault | 0 | 0 | 0 | 20 | 0 |
| tsymex_r6_n20_boundedloop | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_n27_placeholder_read_audit | 0 | 0 | 0 | 8 | 0 |
| tsymex_r6_n27_hof_placeholder | 0 | 0 | 0 | 12 | 0 |
| tsymex_r6_n21_pairloop_member | 0 | 0 | 0 | 28 | 0 |
| tsymex_r6_n28_shadow_collision | 0 | 0 | 0 | 10 | 0 |
| tsymex_r6_n36_raise_class_audit | 0 | 1 | 1 | 24 | 4 |
| tsymex_r6_n29_seqlit_sortmismatch | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_n31_block_counter | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_n37_raise_residue | 0 | 0 | 0 | 22 | 0 |
| tsymex_r6_n39_variant_field_alloc | 0 | 0 | 0 | 20 | 0 |
| tsymex_r6_n36_raise_degrade | 0 | 0 | 0 | 16 | 0 |
| tsymex_r6_n40_alloc_totality | 0 | 0 | 0 | 20 | 0 |
| tsymex_r6_n42_deref_taint | 0 | 0 | 0 | 30 | 0 |
| tsymex_r6_n43_parity | 0 | 0 | 0 | 50 | 0 |
| tsymex_r6_n49_dottedfield_mutation | 0 | 0 | 0 | 16 | 0 |
| tsymex_r6_n9_variant_budget | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_nulwitness | 0 | 0 | 0 | 28 | 0 |
| tsymex_r6_r1_placeholder_totality | 0 | 0 | 0 | 28 | 0 |
| tsymex_r6_r2_zerodefault_result | 0 | 0 | 0 | 50 | 0 |
| tsymex_r6_r3_svint_overflow | 0 | 0 | 0 | 18 | 0 |
| tsymex_r6_r6_emit_roundtrip | 0 | 0 | 0 | 210 | 0 |
| tsymex_r6_r4_collector_scoping | 0 | 0 | 0 | 14 | 0 |
| tsymex_r6_r5_pairloop_counter | 0 | 0 | 0 | 10 | 0 |
| tsymex_r7_caseexpr | 0 | 0 | 0 | 10 | 0 |
| tsymex_r8_omitted_field_degrade | 0 | 0 | 0 | 6 | 0 |
| tsymex_rectify_abstraction | 0 | 0 | 0 | 4 | 0 |
| tsymex_rectify_cardinality | 0 | 0 | 0 | 4 | 0 |
| tsymex_rectify_effects | 0 | 0 | 0 | 10 | 0 |
| tsymex_rectify_generics | 0 | 0 | 0 | 2 | 0 |
| tsymex_rectify_mutation | 0 | 0 | 0 | 12 | 0 |
| tsymex_rectify_nested_arrays | 0 | 0 | 0 | 2 | 0 |
| tsymex_rectify_refs | 0 | 0 | 0 | 2 | 0 |
| tsymex_rectify_variants | 0 | 0 | 0 | 6 | 0 |
| tsymex_retest_c11_stack | 0 | 0 | 0 | 6 | 0 |
| tsymex_retest_c3_bitwise_guard | 0 | 0 | 0 | 14 | 0 |
| tsymex_retest_c5b_unknown_errors | 0 | 0 | 0 | 6 | 0 |
| tsymex_retest_char_needle | 0 | 0 | 0 | 12 | 0 |
| tsymex_retest_defect_net | 0 | 0 | 0 | 4 | 0 |
| tsymex_retest_c6_tuple_chain | 0 | 0 | 0 | 10 | 0 |
| tsymex_retest_infix_degrade | 0 | 0 | 0 | 4 | 0 |
| tsymex_retest_pred_succ | 0 | 0 | 0 | 10 | 0 |
| tsymex_rfc0005_s0_exhibit | 0 | 0 | 0 | 20 | 0 |
| tsymex_rfc0005_s10_replay_verdict | 0 | 0 | 0 | 62 | 0 |
| tsymex_rfc0005_s1b_kinds | 0 | 0 | 0 | 36 | 0 |
| tsymex_rfc0005_s11_surface | 0 | 0 | 0 | 68 | 0 |
| tsymex_rfc0005_s1_lattice | 0 | 0 | 0 | 46 | 0 |
| tsymex_rfc0005_s1c_verdict | 0 | 0 | 0 | 48 | 0 |
| tsymex_rfc0005_s2_replay | 0 | 0 | 0 | 30 | 0 |
| tsymex_rfc0005_s4_alloc | 0 | 0 | 0 | 40 | 0 |
| tsymex_rfc0005_s3_monotonicity | 0 | 0 | 0 | 54 | 0 |
| tsymex_rfc0005_s5_str | 0 | 0 | 0 | 70 | 0 |
| tsymex_rfc0005_s6a_budget | 0 | 0 | 0 | 62 | 0 |
| tsymex_rfc0005_s6b_ops | 0 | 0 | 0 | 86 | 0 |
| tsymex_rfc0005_s7_closure | 0 | 0 | 0 | 74 | 0 |
| tsymex_rfc0005_s8aa_remainder | 0 | 0 | 0 | 48 | 0 |
| tsymex_rfc0005_s8ab_letaudit | 0 | 0 | 0 | 56 | 0 |
| tsymex_rfc0005_s8ac_remainder | 0 | 0 | 0 | 38 | 0 |
| tsymex_rfc0005_s8ad_remainder | 0 | 0 | 0 | 26 | 0 |
| tsymex_rfc0005_s8ag_indexsplit | 0 | 0 | 0 | 30 | 0 |
| tsymex_rfc0005_s8aj_remainder | 0 | 0 | 0 | 42 | 0 |
| tsymex_rfc0005_s8am_remainder | 0 | 0 | 0 | 58 | 0 |
| tsymex_rfc0005_s8ae_remainder | 0 | 0 | 0 | 32 | 0 |
| tsymex_rfc0005_s8ao_remainder | 0 | 0 | 0 | 22 | 0 |
| tsymex_rfc0005_s8ai_semantic | 0 | 0 | 0 | 50 | 0 |
| tsymex_rfc0005_s8an_remainder | 0 | 0 | 0 | 50 | 0 |
| tsymex_rfc0005_s8ap_remainder | 0 | 0 | 0 | 72 | 0 |
| tsymex_rfc0005_s8aq_remainder | 0 | 0 | 0 | 26 | 0 |
| tsymex_rfc0005_s8ar_remainder | 0 | 0 | 0 | 100 | 0 |
| tsymex_rfc0005_s8at_remainder | 0 | 0 | 0 | 134 | 0 |
| tsymex_rfc0005_s8bc_remainder_a | 0 | 0 | 0 | 54 | 0 |
| tsymex_rfc0005_s8bc_remainder_b | 0 | 0 | 0 | 36 | 0 |
| tsymex_rfc0005_s8bc_remainder_c | 0 | 0 | 0 | 58 | 0 |
| tsymex_rfc0005_s8bl_borrow | 0 | 0 | 0 | 8 | 0 |
| tsymex_rfc0005_s8bl_magicscan | 0 | 0 | 0 | 6 | 0 |
| tsymex_rfc0005_s8bl_gaps | 0 | 0 | 0 | 22 | 0 |
| tsymex_rfc0005_s8bl_magics | 0 | 0 | 0 | 16 | 0 |
| tsymex_rfc0005_s8bl_pairloop | 0 | 0 | 0 | 4 | 0 |
| tsymex_rfc0005_s8bl_seqops | 0 | 0 | 0 | 8 | 0 |
| tsymex_rfc0005_s8bl_setlen | 0 | 0 | 0 | 14 | 0 |
| tsymex_rfc0005_s8b_substitutions | 0 | 0 | 0 | 52 | 0 |
| tsymex_rfc0005_s8bx_extractraise | 0 | 0 | 0 | 14 | 0 |
| tsymex_rfc0005_s8bx_iterchange | 0 | 0 | 0 | 12 | 0 |
| tsymex_rfc0005_s8bx_mpairs | 0 | 0 | 0 | 16 | 0 |
| tsymex_rfc0005_s8bx_witnessdrift | 0 | 0 | 0 | 6 | 0 |
| tsymex_rfc0005_s8ce_hookraise | 0 | 0 | 0 | 14 | 0 |
| tsymex_rfc0005_s8bx_setlenstr | 0 | 0 | 0 | 6 | 0 |
| tsymex_rfc0005_s8ce_raiseshapes | 0 | 0 | 0 | 26 | 0 |
| tsymex_rfc0005_s8d_typeheads | 0 | 0 | 0 | 34 | 0 |
| tsymex_rfc0005_s8c_resolution | 0 | 0 | 0 | 50 | 0 |
| tsymex_rfc0005_s8e_scoping | 0 | 0 | 0 | 72 | 0 |
| tsymex_rfc0005_s8g_models | 0 | 0 | 0 | 76 | 0 |
| tsymex_rfc0005_s8f_witness | 0 | 0 | 0 | 58 | 0 |
| tsymex_rfc0005_s8h_refwitness | 0 | 0 | 0 | 54 | 0 |
| tsymex_rfc0005_s8i_models | 0 | 0 | 0 | 78 | 0 |
| tsymex_rfc0005_s8j_exits | 0 | 0 | 0 | 90 | 0 |
| tsymex_rfc0005_s8m_exits | 0 | 0 | 0 | 64 | 0 |
| tsymex_rfc0005_s8k_bounds | 0 | 0 | 0 | 38 | 0 |
| tsymex_rfc0005_s8l_exits | 0 | 0 | 0 | 100 | 0 |
| tsymex_rfc0005_s8o_termination | 0 | 0 | 0 | 28 | 0 |
| tsymex_rfc0005_s8n_precision | 0 | 0 | 0 | 38 | 0 |
| tsymex_rfc0005_s8p_precision | 0 | 0 | 0 | 60 | 0 |
| tsymex_rfc0005_s8q_termination | 0 | 0 | 0 | 20 | 0 |
| tsymex_rfc0005_s8r_theoryfree | 0 | 0 | 0 | 6 | 0 |
| tsymex_rfc0005_s8_scope | 0 | 0 | 0 | 56 | 0 |
| tsymex_rfc0005_s8t_termination | 0 | 0 | 0 | 40 | 0 |
| tsymex_rfc0005_s8u_precision | 0 | 0 | 0 | 34 | 0 |
| tsymex_rfc0005_s8s_precision | 0 | 0 | 0 | 58 | 0 |
| tsymex_rfc0005_s8v_termination | 0 | 0 | 0 | 14 | 0 |
| tsymex_rfc0005_s8x_vm_alias | 0 | 0 | 0 | 14 | 0 |
| tsymex_rfc0005_s8w2_hotfix | 0 | 0 | 0 | 8 | 0 |
| tsymex_rfc0005_s8y_budget_decline | 0 | 0 | 0 | 16 | 0 |
| tsymex_rfc0005_s9_vetoes | 0 | 0 | 0 | 38 | 0 |
| tsymex_rfc0005_s8w_remainder | 0 | 0 | 0 | 46 | 0 |
| tsymex_rfc0005_s8z_remainder | 0 | 0 | 0 | 74 | 0 |
| tsymex_snd1b_closure_uncertain_axiom | 0 | 0 | 0 | 8 | 0 |
| tsymex_snd1_uncertain_taint | 0 | 0 | 0 | 10 | 0 |
| tsymex_snd2_assume | 0 | 0 | 0 | 14 | 0 |
| tsymex_snd3_6_equality_loop | 0 | 0 | 0 | 6 | 0 |
| tsymex_snd3_loopdegrade | 0 | 0 | 0 | 14 | 0 |
| tsymex_typebridge_variants | 0 | 0 | 0 | 6 | 0 |
| tsymex_snd4_strindex_oob | 0 | 0 | 0 | 16 | 0 |
| tsymex_tot1_totality_corpus | 0 | 0 | 0 | 42 | 0 |
| tsymex_uninit_var | 0 | 0 | 0 | 10 | 0 |
