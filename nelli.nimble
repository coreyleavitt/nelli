# Package

version       = "0.8.0"
author        = "Corey Leavitt"
description   = "Property-based testing for Nim with internal choice-sequence shrinking (a Hypothesis-style engine)"
license       = "Apache-2.0"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks

task test, "Run the test suite":
  for f in ["tsmoke", "tchoice", "tserialize", "trng", "tdatasource",
            "tstrategy", "tstrategies", "tengine", "tshrinker", "tdsl",
            "tderive", "tdb", "tstateful", "ttarget", "tbias",
            "tdisplay", "tdeadline", "tevents", "texamples", "tbundles",
            "texplain", "tnested", "twiderange", "tdbbackends", "treporter",
            "tfuzzbytes", "tcoverage", "tcoveragemode",
            "tcovguided", "treservedlabel", "tfuzzir", "tfuzzcbuild", "tfuzzcovdump",
            "tfuzzfrontier", "tfuzzprobe", "tfuzzloop", "tfuzzexec", "tfuzzexternal", "tfuzzdiff", "tfuzzdedup", "tfuzzpersist", "tfuzzcovcorpus", "tfuzzprimarymeta", "tfuzzmincover", "tfuzzschedule", "tfuzzseedcov", "tfuzzinterop", "tfuzzpackaging", "tfuzzstopcrash", "tfuzzdroppedseed", "tfuzzsectionsize", "tautolabels",
            "tsymbolic", "tdetect", "trefine", "tdistribution",
            "tbiasthreading", "tfuzzbias", "tshrinkpass", "tbmc",
            "tmining", "tbisim", "tmutation",
            "tlinearisable", "tjsonschema",
            "tlaws", "tmetamorphic", "tparallelcheck", "tpipeline",
            "trequiresinit", "tcombine", "tfrequency",
            "tsymex_phase1_arith", "tsymex_phase1_bool",
            "tsymex_phase1_let", "tsymex_phase1_assert",
            "tsymex_phase1_dsl",
            "tsymex_phase2_bv_arith", "tsymex_phase2_abstraction",
            "tsymex_phase2_fallback", "tsymex_phase2_overflow",
            "tsymex_phase3_inline", "tsymex_phase3_recursion",
            "tsymex_phase3_summarization", "tsymex_phase3_mutual",
            "tsymex_phase3_stdlib",
            "tsymex_phase4_tuple", "tsymex_phase4_nested",
            "tsymex_phase4_array", "tsymex_phase4_oob",
            "tsymex_phase5_seq", "tsymex_phase5_table",
            "tsymex_phase5_hashset", "tsymex_phase5_models",
            "tsymex_rectify_effects", "tsymex_rectify_cardinality",
            "tsymex_rectify_mutation", "tsymex_rectify_nested_arrays",
            "tsymex_rectify_variants", "tsymex_rectify_abstraction",
            "tsymex_rectify_generics", "tsymex_rectify_refs",
            "tsymex_phase6_while", "tsymex_phase6_for",
            "tsymex_phase6_case", "tsymex_phase6_break",
            "tsymex_phase7_assertcovered",
            # RFC-0010 B1: four phase-13 suites that were registered nowhere.
            # They ran in no sweep and no CI leg -- symex-mingw derives its
            # corpus from THIS list -- so nothing had exercised them since they
            # were written. They are also four of the seven files holding the
            # ten SymexSettings const literals round B flips, which is how the
            # gap was found. Expect a surprise on their first Windows run.
            "tsymex_phase13_rlimit",
            "tsymex_phase13_layer1_wire",
            "tsymex_phase13_acceptunknown_guard",
            "tsymex_phase13_unknown_roundtrip",
            # RFC-0010 slice B2 — the symex half of the definition of done.
            # Named tsymex_* WITH the underscore so derive-ci-suites.ps1 picks
            # it up into the symex-mingw corpus.
            "tsymex_configdefaults",
            "tsymex_canonicalize",
            "tsymex_typebridge_variants",
            "tsymex_phase11_walker",
            "tsymex_phase11_fielddefect",
            "tsymex_phase14_multivariant_ir",
            "tsymex_phase14_multivariant_typebridge",
            "tsymex_phase14_multivariant_walker",
            "tsymex_phase14_multivariant_witness",
            "tsymex_phase14_else_arms",
            "tsymex_phase14_nonenum_disc",
            "tsymex_phase14_symbolic_disc_reassign",
            "tsymex_phase14_arm_field_zero_init",
            "tsymex_phase14_disc_promotion",
            "tsymex_phase14_var_param",
            "tsymex_phase14_var_param_downstream",
            "tsymex_phase14_strategy_digest",
            "tsymex_phase14_b2_forcephases",
            "tsymex_phase14_b3_trace_equivalence",
            "tsymex_phase14_b5_replaymiss",
            "tsymex_phase14_b67_label_filter",
            "tsymex_phase14_c1_fromcache",
            "tsymex_phase14_c2_dberrors",
            "tsymex_phase14_frontier_pruning",
            "tsymex_phase14_c4_z3error",
            "tsymex_phase15_z0_carryover",
            "tsymex_phase15_z1_canary",
            "tsymex_phase15_z3_infra",
            "tsymex_phase15_z3c_classify",
            "tsymex_phase15_z4_walkctx",
            "tsymex_phase15_CR2_cachekey",
            "tsymex_phase15_l1_boundary",
            "tsymex_phase15_l2_untyped_template",
            "tsymex_phase15_l3_quote_do",
            "tsymex_phase15_F1_typebridge",
            "tsymex_phase15_F2_float_literals",
            "tsymex_phase15_F3_float_arith",
            "tsymex_phase15_F4_float_compare",
            "tsymex_phase15_F5_float_conv",
            "tsymex_phase15_F6_float_math",
            "tsymex_phase15_F7_float_extract",
            "tsymex_phase15_F8_smoke",
            "tsymex_phase15_F9a_array_float",
            "tsymex_phase15_F9b_seq_float",
            "tsymex_phase15_F9c_variant_float",
            "tsymex_phase15_S1_typebridge",
            "tsymex_phase15_S2_strlit",
            "tsymex_phase15_S3_strindex",
            "tsymex_phase15_S4_strpred",
            "tsymex_phase15_S5_strops",
            "tsymex_phase15_S6a_regex_parser",
            "tsymex_phase15_S6b_regex",
            "tsymex_phase15_S7a_bytes",
            "tsymex_phase15_S7b_smoke",
            "tsymex_phase15_S8_concat",
            "tsymex_phase15_S9_caseconv",
            "tsymex_phase15_S10a_strconv",
            "tsymex_phase15_S10b_strconv",
            "tsymex_phase15_S11_mutation",
            "tsymex_phase15_H1_path_heap_fields",
            "tsymex_phase15_E1_ir",
            "tsymex_phase15_E2a_cascade",
            "tsymex_phase15_E2b_raise",
            "tsymex_phase15_E3_try",
            "tsymex_phase15_E4_hierarchy",
            "tsymex_phase15_E4a_userexn",
            "tsymex_phase15_E5_finally",
            "tsymex_phase15_E6_defect",
            "tsymex_phase15_E7_smoke",
            "tsymex_phase15_E8_getcurrentexn",
            "tsymex_phase15_G1a_instkey",
            "tsymex_phase15_G1c_instcap",
            "tsymex_phase15_g3_type_subst",
            "tsymex_phase15_g4_distinct_sort",
            "tsymex_phase15_g5_distinct_borrow",
            "tsymex_phase15_g6_concept_constraint",
            "tsymex_phase15_g7_static_param",
            "tsymex_phase15_g8_multi_param",
            "tsymex_phase15_g10_smoke",
            "tsymex_phase15_C1_ir",
            "tsymex_phase15_C2a_closure_capture",
            "tsymex_phase15_C2b_closure_call",
            "tsymex_phase15_C3_proc_as_value",
            "tsymex_phase15_C4_hof",
            "tsymex_phase15_C5_closure_eq",
            "tsymex_phase15_C6_smoke",
            "tsymex_phase15_R1a_ir",
            "tsymex_phase15_r1_refsort",
            "tsymex_phase15_r1b_callheap",
            "tsymex_phase15_r2_new",
            "tsymex_phase15_r3_deref_read",
            "tsymex_phase15_r4_deref_write",
            "tsymex_phase15_r5_nil",
            "tsymex_phase15_r6_refobj",
            "tsymex_phase15_r7_alias_chain",
            "tsymex_phase15_r8_ptr",
            "tsymex_phase15_r8b_varref",
            "tsymex_phase15_r9_recursive",
            "tsymex_phase15_r10_budget",
            "tsymex_phase15_r11_unsafecast",
            "tsymex_phase15_r11b_smoke",
            "tsymex_phase15_r12_bumps",
            "tsymex_phase15_r13_closure_ref",
            "tsymex_phase15_r13_ptr_finally",
            "tsymex_tot1_totality_corpus",
            "tsymex_retest_c3_bitwise_guard",
            "tsymex_retest_c5b_unknown_errors",
            "tsymex_retest_c6_tuple_chain",
            "tsymex_retest_c11_stack",
            "tsymex_retest_pred_succ",
            "tsymex_retest_defect_net",
            "tsymex_retest_infix_degrade",
            "tsymex_retest_char_needle",
            "tsymex_r4_slice_binding",
            "tsymex_r4_strip",
            "tsymex_r4_seq_slice",
            "tsymex_r5_discard",
            "tsymex_r5_bv32_width",
            "tsymex_r5_tuple_return",
            "tsymex_r5_neg_bool_conv",
            "tsymex_r5_const_fold",
            "tsymex_r6_b0_scanlift_bound",
            "tsymex_r6_a0_lowhigh",
            "tsymex_r6_a1_variantlit",
            "tsymex_r6_a2_retbind_variant",
            "tsymex_r6_a3_variantconstruct_sym",
            "tsymex_r6_a4_construct_interactions",
            "tsymex_r6_a6_exported_field_names",
            "tsymex_r6_b1_stringbacked",
            "tsymex_r6_b2_intwidth",
            "tsymex_r6_b3_scanpair",
            "tsymex_r6_b4_readcstring",
            "tsymex_r6_b5_chained",
            "tsymex_r6_b6_optionregion",
            "tsymex_r6_nulwitness",
            "tsymex_r6_bug2_scopeddecline",
            "tsymex_r6_a6r_callwitness",
            "tsymex_r6_b7r_bytescan",
            "tsymex_r6_b7r2_pathscope",
            "tsymex_r7_caseexpr",
            "tsymex_r6_r1_placeholder_totality",
            "tsymex_r6_r2_zerodefault_result",
            "tsymex_r6_r3_svint_overflow",
            "tsymex_r6_r4_collector_scoping",
            "tsymex_r6_r5_pairloop_counter",
            "tsymex_r6_n9_variant_budget",
            "tsymex_r6_n10_coverage_matrix",
            "tsymex_r6_r6_emit_roundtrip",
            "tsymex_r6_n21_pairloop_member",
            "tsymex_r6_n16_closure_zerodefault",
            "tsymex_r6_n27_hof_placeholder",
            "tsymex_r6_n27_placeholder_read_audit",
            "tsymex_r6_n28_shadow_collision",
            "tsymex_r6_n13_reassign_seqarm",
            "tsymex_r6_d2_recursive_budget",
            "tsymex_r6_n31_block_counter",
            "tsymex_r6_n36_raise_degrade",
            "tsymex_r6_n36_raise_class_audit",
            "tsymex_r6_n37_raise_residue",
            "tsymex_r6_n29_seqlit_sortmismatch",
            "tsymex_r6_n39_variant_field_alloc",
            "tsymex_r6_n40_alloc_totality",
            "tsymex_r6_n42_deref_taint",
            "tsymex_r6_heap_raise_totality",
            "tsymex_r6_itesv_mergedegrade",
            "tsymex_r6_n43_parity",
            "tsymex_r6_degrade_pairing_audit",
            "tsymex_r6_lows_collectors",
            "tsymex_r6_lows_blockparse",
            "tsymex_r6_lows_declines",
            "tsymex_r6_n14_seqops",
            "tsymex_r6_n20_boundedloop",
            "tsymex_r6_n49_dottedfield_mutation",
            "tsymex_funcdef_callee",
            "tsymex_phase15_N0_kindgate_widen",
            "tsymex_phase15_N1_resolution_gates",
            "tsymex_phase15_N2_kindgate_audit",
            "tsymex_phase15_N3_scan_boundary",
            "tsymex_phase15_C2_staticparams",
            "tsymex_phase15_A1_bitwise",
            "tsymex_phase15_A1_comparison",
            "tsymex_phase15_A1_arithmetic",
            "tsymex_phase15_A1_boolean",
            "tsymex_phase15_A1_loopguard",
            "tsymex_phase15_A1_unary",
            "tsymex_phase15_A1_callarg",
            "tsymex_phase15_A1_assertarg",
            "tsymex_phase15_A2a_chokepoint_audit",
            "tsymex_phase15_A2a_atomicir_audit",
            "tsymex_phase15_A2a_atomize",
            "tsymex_phase15_A2a_guardcond_pin",
            "tsymex_phase15_A2b_bitwise",
            "tsymex_phase15_C1_canonical_kind",
            "tsymex_q1_sibling_collision",
            "tsymex_g1a_mode",
            "tsymex_g1b_concolic",
            "tsymex_g2_flip",
            "tsymex_g3fix_walkergap",
            "tsymex_g4_cmpwalk",
            "tsymex_g6_algebra",
            # Issue #161 (ADR-0001 amendment): promotion must keep the
            # OverflowDefect obligation live. Named tsymex_* so
            # derive-ci-suites.ps1 pulls it into the symex-mingw corpus.
            "tsymex_161_overflow_obligation",
            # Issue #162: a range subtype carries its BASE type, not just its
            # bounds. Same naming reason as #161 above.
            "tsymex_162_range_base_width",
            # Issue #163: an opaque call ahead of the target must not cost
            # the answer -- nelli's own {.cover.}/{.covercmp.} instrumentation
            # is transparent, and an inert opaque call does not taint. Same
            # naming reason as #161 above.
            "tsymex_163_opaque_transparent",
            # The #163 wiring audit over the combined #161-#163 surface.
            # `_range_domain` covers the char-bounded range ALIAS that
            # degraded the whole run and the enum domain constraint the
            # classifier was declining for a reason #162 had retired;
            # `_range_elem` covers seq elements and ref-object fields, which
            # never received their declared bounds (the #162 slice-5 class,
            # one container and one heap hop over); `_wave2` covers the
            # variant-disc else arm, the isIntOffset arms, the obligation
            # operand stamp and the concolic degrade drain.
            "tsymex_163audit_range_domain",
            # #163 review round finding R2: the enum arm's declared domain
            # excluded negative ordinals and truncated its bit width against
            # a sparse enum's large explicit ordinal -- both false sxUnsat.
            "tsymex_163rev_enum_domain",
            "tsymex_163audit_range_elem",
            "tsymex_163audit_wave2",
            "tsymex_163audit_w9",
            "tsymex_163audit_w10",
            # Issue #163 review finding R1 (Critical, soundness regression):
            # the opaqueInert fast path returned paths untouched WITHOUT
            # lowering stmt.cargs, so an inline defect-fork argument
            # (div/mod by zero, parseInt, ...) reaching an inert-classified
            # opaque call lost its raise obligation entirely.
            "tsymex_163rev_inert_argfork",
            "tsymex_g6_transform_binding",
            # W11 (issues #161-163 wiring audit): 88 tsymex_*/t* suites existed
            # on disk but were registered nowhere, so symex-mingw's
            # derive-ci-suites.ps1 corpus (derived from THIS list) never saw
            # them and no sweep ran them either. This block plus the R16/CR2
            # groups below register the ones judged safe; see the audit
            # report for the small remainder left out as hanging or obsolete.
            #
            # Phase 16 R16 (ADR-0011/ADR-0012) — the ArithCheck policy
            # foundation plus its four raise-fork slices: float->int
            # RangeDefect, div/mod-by-zero DivByZeroDefect, signed-overflow
            # OverflowDefect (+ the closure-return sound-witness regression),
            # and the DefectFinding diagnostics channel. This is the
            # machinery issues #161/#162 amend, so it is the closest existing
            # pin to what this branch changed.
            "tsymex_phase16_R16_1_arithcheck_foundation",
            "tsymex_phase16_R16_2_rangedefect",
            "tsymex_phase16_R16_2b_shortcircuit_conv",
            "tsymex_phase16_R16_3_divzero",
            "tsymex_phase16_R16_4_overflow",
            "tsymex_phase16_R16_5_overflow_thru_closure",
            "tsymex_phase16_R16_6_diagnostics_channel",
            # RFC-chapulin-hardening CR-2a/b/c — the three distinct
            # macro-error() catch-all surfaces (parser expression position,
            # param-type classify, post-solve witness-reader codegen), each
            # converted from aborting compilation to a classified sxUnknown
            # degrade.
            "tsymex_CR2a_expr_catchall",
            "tsymex_CR2b_paramtype_catchall",
            "tsymex_CR2c_witnessreader_catchall",
            # Phase 16 Cluster A (ADR-0016/0017) — stdlib coverage: ref-variant
            # field access, closure/inline-iterator inlining, symbolic-length
            # seq map/filter, Rune codepoint model + runes()/runeLen(),
            # toHex/toBin radix formatting, ASCII case-fold.
            "tsymex_a2_refvariant_fields",
            "tsymex_a3_closure_iterators",
            "tsymex_a6_symlen_hof",
            "tsymex_a7_rune",
            "tsymex_a7_runes_iter",
            "tsymex_a8_radix",
            "tsymex_a9_casefold",
            # Standalone regression pins with no sibling cluster.
            "tsymex_augmented_assign",
            "tsymex_cr22_label_assert_coexist",
            "tsymex_cr9c_intrep",
            "tsymex_discard_raise",
            "tsymex_inv_structured_kinds",
            "tsymex_m6_probeproto_strproto",
            "tsymex_uninit_var",
            "tvariantbind",
            "tfuzzcorpus_nilguard",
            "tz3free_probe",
            # Cluster H (ADR-0022) — named ref-object heap identity: Step A
            # (nominalId compile-time helper), Step C (the flagship
            # heap-identity tracer-bullets), containers of refs, recursive
            # heap-snapshot witness fidelity, and closeout edge-case coverage.
            "tsymex_h_containers",
            "tsymex_h_stepA_nominalid",
            "tsymex_h_stepC_heapidentity",
            "tsymex_h_verification",
            "tsymex_h_witness",
            # RFC-chapulin-hardening Cluster 4 (Parser expression coverage,
            # ADR-0021) — P1 tuple-constructor, P2a value-object, P2b
            # ref-object construction in expression position, and R8's
            # telemetry-hygiene follow-up on omitted non-scalar fields.
            "tsymex_p1_tupleconstr_expr",
            "tsymex_p2a_objconstr_expr",
            "tsymex_p2b_refobjconstr_expr",
            "tsymex_r8_omitted_field_degrade",
            # Phase 12 — Layer 1 (symex auto-discovery) / Layer 2
            # (forAllWithSymexSeeds) engine integration cycles.
            "tsymex_phase12_derandomize",
            "tsymex_phase12_forall",
            "tsymex_phase12_notapplicable",
            "tsymex_phase12_phase_closure",
            "tsymex_phase12_pipeline",
            "tsymex_phase12_renderchoices",
            "tsymex_phase12_scan",
            "tsymex_phase12_seedphase",
            "tsymex_phase12_sink",
            "tsymex_phase12_sugar",
            "tsymex_phase12_witnesses",
            # Phase 13 — content-addressed verdict-cache namespace
            # (:sat/:unsat/:unk sibling keys) and its macro forms.
            "tsymex_phase13_macro",
            "tsymex_phase13_satsuffix",
            "tsymex_phase13_unsat_roundtrip",
            "tsymex_phase13_verdict_primitives",
            # Phase 15 code-review findings (CR-*, plus the E-cluster raised-
            # path runtime round-trip, the F5 probeProto/hang regressions,
            # the M1/M2 stdlib widenings, and the rereview drain-
            # consolidation cluster).
            "tsymex_phase15_CR10_regex_overflow",
            "tsymex_phase15_CR11_CR18_splitcap",
            "tsymex_phase15_CR14_exn_missing",
            "tsymex_phase15_CR15_enum_ordinal",
            "tsymex_phase15_CR1_CR5_closure_heap",
            "tsymex_phase15_CR21_parseintraise_arg",
            "tsymex_phase15_CR3_CR4_CR6_float",
            "tsymex_phase15_E_roundtrip",
            "tsymex_phase15_F5_probeproto",
            "tsymex_phase15_F5hang_derefwrite",
            "tsymex_phase15_M1_seq_fixedwidth",
            "tsymex_phase15_M2_parsebiggestint",
            "tsymex_phase15_cr9_lowerInExpr",
            "tsymex_phase15_fieldcontainer",
            "tsymex_phase15_rereview_drains",
            # Phase 16 crash-totality + stdlib slices: classify()/copySign(),
            # bitwise-on-svInt (CR-1a), tail-return-of-local (CR-1b), the
            # last-resort internal-fault catch (CR-1c), unconditional defect
            # routing through routeRaise (D1a), and/or short-circuit modeling
            # (D1c), plus rfind/`.add`&=/if-expression-as-subexpression.
            "tsymex_phase16_A5_float_classify",
            "tsymex_phase16_CR1a_bitwise_svint",
            "tsymex_phase16_CR1b_tail_local",
            "tsymex_phase16_CR1c_internal_fault",
            "tsymex_phase16_D1a_defect_routeraise",
            "tsymex_phase16_D1c_shortcircuit",
            "tsymex_phase16_m3_rfind",
            "tsymex_phase16_m4_str_add_ampeq",
            "tsymex_phase16_m5_ifexpr_minmax",
            # RFC-chapulin-hardening R-series / Cluster 1 (Soundness) findings:
            # the bounded forward scan-to-delimiter idiom (Q1) and its R2/R14
            # loop-invariance/continue-guard hardening, the scalar-raise-fork
            # drain gap (R1) and its short-circuit-OOB sibling (R1B), and the
            # SND-1/1b/2/3/4 soundness fixes (unmodeled-statement taint,
            # closure uncertain-axiom propagation, symexAssume semantics,
            # loop-guard raise-loss on the C backend, string-index OOB).
            "tsymex_q1_scanlift",
            "tsymex_r14_case2_degrade",
            "tsymex_r14_continue_guard",
            "tsymex_r1_draingap",
            "tsymex_r1b_shortcircuit_oob",
            "tsymex_r2_scanbound",
            "tsymex_snd1_uncertain_taint",
            "tsymex_snd1b_closure_uncertain_axiom",
            "tsymex_snd2_assume",
            "tsymex_snd3_loopdegrade",
            "tsymex_snd4_strindex_oob",
            # RFC-fuzzer-nextgen Track E — isolated executor: worker protocol,
            # process/fork workers, orchestrator, lifecycle, breakers, and the
            # Windows arms (the win* suites self-skip off Windows).
            "tfuzzworkerproto", "tfuzzworker", "tfuzzworkerprocess",
            "tfuzzworkerlifecycle", "tfuzzforkworker", "tfuzzexternalworker",
            "tfuzzorchestrator", "tfuzzrespawnstorm", "tfuzzbootstrapbreaker",
            "tfuzzprocessisolation",
            "tfuzzreverify", "tfuzzcrashinfo",
            "tfuzzwinworker", "tfuzzwinshm", "tfuzzwinjoblimits",
            # Track E — coverage transport + corpus/DB channel.
            "tfuzzcovshm", "tfuzzcovreset", "tfuzzcmplog", "tfuzzcmplogshm",
            "tfuzzcmplogprocess", "tfuzzcmplogshmleak", "tfuzzshmhold",
            "tfuzzworkerspawnfailshm",
            "tfuzzdbfunnel", "tfuzzembedguard",
            "tdbcorpuslog", "tdbcleanupsweep",
            # Track G — concolic bridge + cmp-correspondence.
            "tfuzzconcolicbridge", "tfuzzconcolicbridge_real",
            "tfuzzconcolicbridge_g6_affine", "tfuzzconcolicbridge_g6_predicated",
            # RFC-z3-optional S1a — `nelli/concolic`'s opt-in assist builder,
            # exercised through both documented seams.
            "tfuzzconcolicassist", "tfuzzconcolicmismatch", "tfuzzconcolicdegrade",
            "tfuzzsymexmarkers",
            "tfuzzmacro", "tfuzzmacro_astspike", "tfuzzmacroreject", "tfuzzi2s",
            # Track S — scheduling: energy, bandit, havoc, cull, checkpoint.
            "tfuzzbandit", "tfuzzoperatorbandit", "tfuzzhavoc",
            "tfuzzcull", "tfuzzcullpersist", "tfuzzcheckpoint",
            "tfuzzcampaignstats", "tlearnedstate",
            # RFC-fuzzer-nextgen R27: fuzz[T] decomposition into collaborators.
            "tfuzzrefactordeterminism", "tfuzzcheckpointmgr", "tfuzzcorpusstore",
            "tfuzzoperatorselector", "tfuzzcrashrecorder",
            # ADR-0031 — configuration-surface regrouping (finding R11): pins
            # FuzzSettings/OrchestratorPolicy default values across all tracks.
            "tfuzzconfigdefaults",
            # Track U — one engine, two front doors.
            "tengine_crashisolation", "tengine_corpusreplay",
            "tcovsourcetable",
            # RFC-0010 slice A2 — the Z3-free definition of done. Every
            # in-scope surface's documented construction idiom through its
            # real entry point. Also named in fuzzer-msvc/fuzzer-mingw.
            "tconfigdefaults",
            # RFC-0010 stage-4 review — permanent audit that the
            # parseEntryImpl/parseEntryImplValidated wiring split in
            # symex.nim can't silently regress. Z3-free (no `import
            # nelli/symex`, pure text scan), which lets the fuzzer legs run
            # it. Being listed HERE buys no CI coverage on its own — no
            # workflow runs this `test` task — so it is also named in
            # fuzzer-msvc/fuzzer-mingw's discovery pattern, exactly as
            # tconfigdefaults above is. Round 3 caught it born dark: it was
            # registered here, matched no leg, and the comment claimed
            # otherwise. It does NOT reach symex-mingw, whose corpus is
            # derived from `tsymex_*` names only.
            "tentrypointwiring"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
