# Package

version       = "0.9.2"
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
            "tsymex_phase2_overflow_checksoff",
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
            "tsymex_configdefaults_b",
            "tsymex_configdefaults_depth",
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
            "tsymex_r6_n36_raise_degrade_b",
            "tsymex_r6_n36_raise_degrade_c",
            "tsymex_r6_n36_raise_degrade_d",
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
            # Issue #163 review finding R3 (High, soundness regression): a
            # ranged arm-specific field of a ref-to-variant object reached
            # neither its solver-path constraint nor its witness clamp --
            # the one shape #163's own W2/W4 remediation missed.
            "tsymex_163rev_variant_armfield",
            # Issue #163 review finding R17 (High, verified by adversarial
            # verifier): R3's fix was incomplete -- the active-arm override
            # immediately below R3's witness-clamp loops unconditionally
            # overwrote the clamp with a fresh, unclamped heapSelect, so a
            # ranged arm field that was WRITTEN but never read back still
            # reached the caller with an out-of-declared-range witness.
            "tsymex_163rev_armfield_write",
            # Issue #163 review finding R4 (High, soundness regression):
            # extractTableEntries never checked tabValTy.hasRange and never
            # clamped, unlike its three sibling extractors -- a Table value
            # read only on a branch the winning path did not take stayed
            # entirely unconstrained and raised RangeDefect materializing
            # the witness.
            "tsymex_163rev_table_elem",
            # Issue #163 review finding R15 (Critical, soundness regression):
            # the #141 enum-value resolver in the parser's expression `nnkSym`
            # arm embedded an enum CONSTANT's DECLARATION-POSITION loop index
            # instead of its real ordinal -- every non-dense enum comparison
            # (`x == someConstant`) resolved the RHS to the wrong value, and
            # for the last arm this pushed the embedded constant outside the
            # type's own domain, flipping a reachable target to sxUnsat.
            "tsymex_163rev_enum_ordinal",
            # Issue #163 review round 2 findings R18/R19/R23: the structural
            # fix that extracts `enumFieldOrdinals` as the single source of
            # truth both the classifier's enum arm and the parser's `nnkSym`
            # arm now share -- R18 (a tuple/string-valued enum field, e.g.
            # `a = (1, alpha)` -- a tuple-valued enum field -- fell through both loops'
            # guard to the wrong implicit ordinal), R19 (the parser's retired
            # `getType`-direct fallback could only ever embed a
            # positionally-wrong constant, silently), and R23 (an unknown
            # enum-body child kind must not desync the two loops' ordinal
            # tracking -- now a loud macro-time `error`, not a silent guess).
            "tsymex_163rev_enum_valueshapes",
            # Issue #163 review finding R6 (High, verified by count): every
            # mechanism this branch built was pinned only through symexFind
            # (wmExplore) -- wmFollowConcrete, the mode the fuzzer itself
            # walks, had zero coverage. Extends past tsymex_163audit_w10's
            # own concolic pin; also documents (comment-only, no vacuous
            # tests) which mechanisms have no reachable surface in
            # concolicCollect's API today, and a newly-found mode divergence
            # (unsigned/narrow-width param arithmetic loses its wraparound
            # semantics under concolic collection).
            "tsymex_163rev_concolic_modes",
            "tsymex_163rev_concolic_modes_checksoff",
            # Issue #163 review finding R7 (Medium, CONFIRMED with a concrete
            # wrong verdict) -- the statement-position `{.symexTransparent.}`
            # arm deleted the call unconditionally, never consulting the
            # inertness predicate its opaque sibling arm applies to the same
            # argument shapes, so a var/ref-argument transparent callee's
            # mutation vanished and a target reading its effect answered a
            # false `sxUnsat`.
            "tsymex_163rev_transparent_guard",
            # Issue #163 review finding R10 (Medium): the OTHER way a
            # `{.symexTransparent.}` callee can over-claim its promise -- R7
            # covers statement position/non-inert argument; this covers
            # expression position/result used, which fell back to opaque
            # handling and reached the SAME generic `feOpaqueCallUnmodelled`
            # message -- wrongly advising an already-compliant caller to
            # apply the pragma they already applied.
            "tsymex_163rev_transparent_result",
            # Issue #163 review finding R8 (Medium): W4's ref-to-object
            # witness clamp (extractFromSymVal's itTuple pointee arm)
            # iterated only the pointee's OWN immediate fields, but the
            # recursive extraction just above it populates dotted paths
            # arbitrarily deep through nested object/array fields -- a
            # ranged subfield two levels down in an unread ref-object field
            # reconstructed unclamped and raised a real RangeDefect.
            "tsymex_163rev_nested_clamp",
            # Issue #163 review finding R12 (Medium, refactor): the variant
            # discriminator's legal domain was decided independently in the
            # BV-path allocator and the Promoted-Int path -- the same
            # decision W6 had to fix twice. Extracted `discriminatorDomain`
            # (runtime.nim, pure, no Z3 context) and unit-tests it directly.
            "tsymex_163rev_disc_domain",
            # #163 review round findings R21 (Medium) and R20 (Medium, test
            # half): the enum-domain fix (R2) and its default-mode
            # promotion route were pinned only at a top-level enum PARAM.
            # This extends the same domain to an array element, a seq
            # element, and an enum-typed (not range-alias) variant
            # discriminator, and cross-checks a negative-ordinal enum
            # param's Z3Int-promotion route (isOptimised, the default)
            # against isExact.
            "tsymex_163rev_enum_positions",
            # #163 review finding R14a (Low): the range LOWER boundary was
            # never distinguished from a plain non-negative bound, because every
            # existing ranged test starts at 0. Pins a non-zero and a
            # negative lower bound, both edges, both directions.
            "tsymex_163rev_range_bounds",
            # #163 review finding R14 (Low), parts b/c/d: inert-allowlist
            # exclusions beyond var/ref (object/tuple/seq/ptr/pointer/proc/
            # cstring), the wrap-scan's whole-program (not per-variable) ban,
            # and the documented opaque-call-after-target ordering asymmetry.
            "tsymex_163rev_inert_exclusions",
            "tsymex_163rev_inert_exclusions_checksoff",
            # Issue #163 review finding R22 (Medium): the ONLY RangeDefect
            # fork in the whole engine was float->int conversion -- an
            # out-of-range ASSIGNMENT into a `range[lo..hi]`-typed local
            # (`var v: range[1..100]; v = x + y`) forked nothing, so a
            # genuine RangeDefect at that site was invisible to symexFind.
            # Fixes the plain-local-assignment site only (`isAssign`);
            # object-field and seq/array element writes are separate,
            # enumerated remainder -- see the handoff.
            "tsymex_163rev_assign_rangedefect",
            # Issue #163 review finding R27 (High, introduced by R22's own
            # fix): `localRangeTypes` was keyed by bare source-text name on
            # a single WalkCtx-wide table, unscoped like `Env` is scoped --
            # a sibling branch's same-named shadow local silently deleted
            # the tracked entry (a real RangeDefect vanishes), and a stale
            # entry left behind by an inlined callee's popFrame produced a
            # phantom RangeDefect against an unrelated caller variable.
            "tsymex_163rev_assign_scope",
            # Issue #163 review finding R22's own enumerated remainder: four
            # assignment sites R22 deliberately left unmodelled (plain
            # `isAssign` was its whole scope) -- a ref object field write, a
            # variant arm field write, a seq element write, and a var/out
            # param reassignment inside its own callee. Each reuses
            # `forkAssignRangeCheck`/`rangeCondsIfNeeded` unchanged (the
            # RAISE FORK model, never a range CONSTRAINT at the write site).
            "tsymex_163rev_assign_sites",
            # Discovered building R22 site 3 (seq element write): a
            # pre-existing, orthogonal defect -- storeSeqElem's itInt arm
            # never reconciled an svInt-shaped RHS (a range[lo..hi] top-level
            # param promotes to svInt under the engine's default isOptimised
            # semantics) to the seq's BV-backed data array, crashing the
            # walker for any int-family seq element write fed a promoted
            # param, ranged or not.
            "tsymex_163rev_seqelem_promoted_int",
            # Issue #163 review finding R28 (Medium, a narrowing R27
            # introduced): three scan-idiom recognizers (`tryRecognizeScanIdiom`,
            # `tryRecognizeScanPairIdiom`, `tryRecognizeAccumulatingScan`) call
            # `mkAssign` directly for their closed form's counter write,
            # bypassing the normal assignment dispatch R27 taught to carry
            # `aty` -- a ranged scan counter's RangeDefect fork silently never
            # ran. Also fixes a deeper prerequisite gap the RED test surfaced:
            # none of the three could even RECOGNIZE a ranged counter's loop
            # in the first place (Nim wraps it in `nnkHiddenStdConv` at every
            # plain-int use site, which the shape matchers' identity checks
            # did not unwrap).
            "tsymex_163rev_scan_counter_range",
            # Issue #163 review finding W8: `allocateSym`'s two `isIntOffset`
            # arms (bare scan-offset return, traced tuple position) allocate
            # a Z3-Int-sorted `svInt` for a call's fresh return placeholder
            # directly, ignoring `ty.hasRange`/`ft.hasRange` -- unlike the
            # ordinary `itInt` allocation arm beside them (issue #162's fix
            # site), which already asserts a declared range. Reachable only
            # through `calleeIntOffsetReturnPositions` (a callee statically
            # recognized as a B3/B4 scan closed form, called across a real
            # proc boundary); the range assertion this fix adds also turns
            # out to be load-bearing for TERMINATION, not just soundness --
            # without it, Z3 must reason about the full call's Sequence-
            # theory equality to answer an otherwise-trivial out-of-range
            # query, which hangs (confirmed against a worktree pinned to the
            # commit immediately before this fix).
            "tsymex_163rev_intoffset_range",
            # Issue #163 review (second-hand-reported gaps, verified before
            # fixing): (1) `nnkHiddenCallConv` -- `echo(intExpr)` failed to
            # parse at all (no arm for the hidden `$`-conversion Nim inserts
            # for a non-string `varargs[string, `$`]` element); (2)
            # `nnkHiddenSubConv` -- a char-RANGE value compared directly
            # against a char literal (`c > 'm'`) also failed to parse (W3
            # fixed the type side; this is the expression side W3's own
            # comment named as a separate, unrelated gap).
            "tsymex_163rev_parser_gaps",
            # Issue #163 review R11: a permanent source-scanning audit over
            # the two raw range-invariant primitives (`bvRangeConds`,
            # `clampToDeclaredRange`) so a seventh materialization site
            # cannot skip the two-obligation contract (solver-path
            # constraint + witness clamp) silently, mirroring
            # `tsymex_r6_n36_raise_class_audit`'s house scan-and-marker
            # technique.
            "tsymex_r11_range_invariant_audit",
            "tsymex_g6_transform_binding",
            # Issue #163 review round -- R24/R25/R26 (all CONCOLIC-path,
            # opened by R16's own promotion fix): R24, `concolicFlip` read a
            # solved model's value off the wrong, disconnected variable for
            # a BV-bound param; R25, `cbTransformLinked`'s BV branch
            # concretized to a ground literal instead of staying symbolic;
            # R26, a concolic-bound Z3Int param carried no width/signedness
            # stamp, so #161's overflow obligation never fired on a
            # concolic-bound path at any width (fixed at the obligation-log
            # level; confirmed NOT observable through ConcolicCollectResult/
            # ConcolicFlipResult's own public surface -- documented, not a
            # gap this file leaves silent).
            "tsymex_163rev_concolic_flip_width",
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
            "tsymex_phase16_R16_4_overflow_checksoff",
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
            # SND-3-6 split out of tsymex_snd3_loopdegrade in round 10 of the
            # #163 review: it is the only SUT in that file that does not
            # terminate (one Z3 query past a 20M rlimit), and skip-listing the
            # parent to cope would have retired five live soundness pins with
            # it. Registered here so `nimble test` still covers it; skip-listed
            # in scripts/sweep.sh so the gate does not burn a timeout on it.
            "tsymex_snd3_6_equality_loop",
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
            "tfuzzconcolicannotation", "tfuzzconcolicundefined",
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
            "tentrypointwiring",
            # Issue #163 item 1 (rev): an enum-typed OBJECT FIELD's witness
            # reader (`readUInt8`/`readUInt16`) did not compile back into
            # the enum-typed field at all -- `symexFind` could not even be
            # CALLED on a proc taking an object with a plain enum field.
            "tsymex_163rev_enum_field_witness",
            # Issue #163 item 2 (rev): a hidden int-widening conversion
            # (`nnkHiddenStdConv`, e.g. `a: int32` compared against the
            # untyped literal `3_000_000_000`, which Nim itself types
            # `int64`) was blindly unwrapped at its NARROW width, silently
            # wrapping the wider literal into a false `sxSat`.
            "tsymex_163rev_int_literal_width",
            # Issue #163 item 3 (rev): `maxFrontierSize`'s default. Briefly
            # set to `256` on this branch and REVERTED to `0` (unbounded) at
            # `90caaa1` -- the cap's premise was already dead (R22's forks
            # return a single survivor via `routeRaise` and never multiplied
            # the frontier) and its measurement sampled ~20 suites rather
            # than the corpus, which the round-9 gate then caught: A4-3b
            # carries 66 live paths and the prune turned a genuine UNSAT into
            # `sxUnknown`. The suite now pins the default AT 0 and records
            # what a future non-zero default must measure first.
            "tsymex_163rev_frontier_default",
            # Issues #161/#163 handoff follow-up, item 2: the `maxCallDepth`
            # call-inlining bail set `w.sawUnknown` bare, so exceeding an
            # ordinary, actionable recursion-depth budget reported the SAME
            # `weInternalWalkerFault` "the engine has a bug" attribution as a
            # genuine walker fault. Now rides the existing `beBudgetExhausted`
            # kind (a sibling of the `maxLoopUnwind`/`maxFrontierSize` budget
            # family), naming the exhausted budget and the remedy (raise
            # `settings.budget.maxCallDepth`). Item 1 (a module-level global
            # read's raw `KeyError`) landed later in the same round at
            # `7182801`, via the new `feGlobalReadUnmodelled` kind routed
            # through the `loweringDegradeErrors` threadvar sink rather than
            # a raise -- a raw raise there unwinds through nested `walkBlock`
            # frames and is swallowed by the C backend's goto-exception
            # model, which is the N31/N36 false-`sxUnsat` class.
            "tsymex_163rev_degrade_classification",
            "tsymex_163rev_degrade_classification_b",
            "tsymex_163rev_degrade_classification_c",
            "tsymex_163rev_degrade_classification_d",
            # Issue #163 review R26 (continued) + the parse-error gap:
            # `runConcolicCollectImpl` built an obligation log and read
            # `prog.parseErrors`' sibling degrade sinks, but discarded both
            # the obligation log itself and the parse errors before they
            # ever reached `ConcolicCollectResult` -- diagnostics-only,
            # mirroring W10/R9's existing `walkDegradeCount` drain.
            "tsymex_163rev_concolic_diagnostics",
            # N45 investigation instruments, registered in round 10 of the
            # #163 review. Both were previously on disk and registered
            # nowhere, so they ran in no sweep and no CI leg while still
            # counting against the drift report every run. `tn45probe`
            # runs its k=2 B5-4 trip-wire to `sxUnknown` unconditionally in
            # seconds. `tprobe_n45stats` needs `-d:symexQueryStats`, supplied
            # by its sibling `tests/tprobe_n45stats.nim.cfg` (Nim auto-reads
            # `<module>.nim.cfg`), or its whole body compiles to a single
            # `skip()` -- a round-10 liveness finding caught it registered
            # but structurally inert that way.
            "tn45probe",
            "tprobe_n45stats",
            # RFC-0005 (soundness channels) slice S0: characterization pins
            # on TODAY's undifferentiated sxUnknown, run through the real
            # symexFind entry point -- an over-taint-only UNSAT exhibit
            # (flips sxUnsat at S4) plus the cap-veto and closure-veto
            # companions (each a clean-path witness discarded by a blanket
            # veto, flips sxSat at S9). No product code; no walker bump.
            "tsymex_rfc0005_s0_exhibit",
            # RFC-0005 S1: the channel lattice, the Path.taint carrier, the
            # degrade() funnel + Degrade token, RawResult.pathTaint, the
            # .taint/.runTaint writer grep-pin and the lowering pending-taint
            # leak pin. All-⊤ classOf default: no verdict change, no bump.
            "tsymex_rfc0005_s1_lattice",
            # RFC-0005 S1b: every formerly-kindless degrade site mints and
            # records a classified kind (behavioural pins through symexFind,
            # incl. a solver resource-out no longer stamped
            # weInternalWalkerFault) + the structural correspondence pin (a
            # Degrade token exists only inside a recording funnel). All-⊤:
            # no verdict change, no bump.
            "tsymex_rfc0005_s1b_kinds",
            # RFC-0005 S2: the replay substrate -- ReplayOutcome, the
            # target-shaped replayWitness macro, the dcFreshSymbol eligibility
            # gate, witness fidelity / target scope, and the stackable capture
            # context. Not yet wired into the verdict (S10); no walker bump.
            "tsymex_rfc0005_s2_replay",
            # RFC-0005 S1c: the verdict rule -- isTargetLabel/routeRaise solve
            # tainted paths into a candidate pool (never halting the walk),
            # tainted raises are routed, the ordered decideVerdict procedure,
            # the witness-monotonicity pin (tainted arm first), and the
            # N40-4 / concolic pending-taint leak fixes. All-⊤: no status
            # moves; walker 140->141.
            "tsymex_rfc0005_s1c_verdict",
            # RFC-0005 S3: the taint-monotonicity harness -- the
            # `withPoisonedArm` test-support macro + a curated battery
            # (three witness shapes -- sxSat, sxRaised, sxSat behind a loop
            # and a call -- each grafted from >=2 of four live degrade
            # funnels in both discovery orders), the family-2a
            # witness-on-tainted-path classification pins, the family-2b
            # over-taint-only characterization pins for S4/S5/S6 to flip,
            # and an exhaustive `decideVerdict` monotonicity check. No
            # product code; no walker bump.
            "tsymex_rfc0005_s3_monotonicity",
            # RFC-0005 S4: the allocDegrade funnel audited by its true §3.1
            # class -- `liftHeapValue`'s unsupported-pointee read split off
            # `heUnresolvedRef` as `heUnsupportedPointeeRead` (dcFreshSymbol,
            # a per-read fresh name: the introduction invariant),
            # `seUnsupportedCompoundSortLeaf` -> dcSubstituted, every other
            # funnel kind stays ⊤; `checkUnsatOverTaintOnly`; walker 141->142.
            "tsymex_rfc0005_s4_alloc",
            # RFC-0005 S5: the degradeStrArm funnel and the R1 placeholder
            # funnel audited site by site -- bytes/replaceAll/replaceRe/
            # split/join declines -> dcFreshSymbol once each lowers its
            # operands before declining (a dropped operand raise fork was an
            # under-approximation), the parse-time rune-decode sites split off
            # `seZ3StringIncomplete` as `seRuneDecodeSymbolic` (dcSubstituted),
            # seUnsupportedStringOp / seUnsupportedRegex /
            # seNestedSeqUnsupported stay ⊤; walker 142->143.
            "tsymex_rfc0005_s5_str",
            # RFC-0005 S6a: the budget family split and classified --
            # k-unroll survivor keeps `beBudgetExhausted` (dcFabricated, as
            # `beBudgetExhaustedAssumedBound`), frontier prune ->
            # `beBudgetExhaustedPrune` (dcOmitted, a halt), maxCallDepth /
            # variant-ctor bails -> `beBudgetExhaustedUnmodelled`
            # (dcSubstituted), `ceInlineBudgetExceeded` dcSubstituted;
            # verdict-neutral by construction; walker 143->144.
            "tsymex_rfc0005_s6a_budget",
            # RFC-0005 S6b: `feUnsupportedOp` split (fresh sites ->
            # `feUnsupportedOpHavoc` dcFreshSymbol, the boundary abort ->
            # `feUnsupportedOpAborted` dcNoAnswer, the rest dcSubstituted),
            # heap/halt sites dcOmitted, `heNewFieldZeroUnsupported`
            # dcFreshSymbol, `eeUnknownExnType` taints; walker 144->145.
            "tsymex_rfc0005_s6b_ops",
            # RFC-0005 S7: closure / HOF declines taint the path
            # (`closureDegrade`), per-occurrence closure result, closure
            # raises routed, exit coverage, descent isolation, parseInt
            # digits-gate pool deleted; S9 precondition pins; walker
            # 145->146.
            "tsymex_rfc0005_s7_closure",
            # RFC-0005 S10: rule 3 -- witness replay wired into the verdict
            # of symexFind and symexFindAllWitnesses/symexForAll; candidacy
            # unspellable as sat; parseInt's lax raise replay-gated; replay
            # precedes persist; walker 146->147.
            "tsymex_rfc0005_s10_replay_verdict",
            # RFC-0005 S8: DeclineScope on every decline (site-anchored /
            # signature / callee-key / walk-site), the structural totality
            # pin + bucket-4 list, the i3 annotation-violation channel;
            # walker 147->148.
            "tsymex_rfc0005_s8_scope",
            # RFC-0005 S8b: three silent substitutions -- bodiless importc
            # callees take the opaque arm, parseInt follows rawParseInt
            # (`+` sign, int range, `_` continues tainted), exnTypeTable
            # audited against Nim's own hierarchy (+ exception aliases);
            # walker 148->149.
            "tsymex_rfc0005_s8b_substitutions",
            # RFC-0005 S8c -- name-resolved builtins: a builtin model applies
            # only when the resolved callee is the stdlib symbol; a user
            # overload is walked as a user call; markers match by module;
            # walker 149->150.
            "tsymex_rfc0005_s8c_resolution",
            # RFC-0005 S8d -- type heads resolved by symbol: a user type named
            # like a stdlib/builtin type (seq/Table/HashSet/Natural/int8/bool/
            # Rune) is not modelled as it; walker 150->151.
            "tsymex_rfc0005_s8d_typeheads",
            # RFC-0005 S9 -- both blanket vetoes deleted: the parse-time reach
            # join (an unreached decline is a hint), unplaced declines block
            # both directions, dedup on message + anchor, capture by
            # reference (ceCaptureByRefUnmodelled); walker 151->152.
            "tsymex_rfc0005_s9_vetoes",
            # RFC-0005 S8e -- names keyed by symbol: a shadowing local gets its
            # own env slot, case narrowing keys its scrutinee by symbol,
            # generic callees keep node types, witnesses name types by
            # symbol; walker 152->153.
            "tsymex_rfc0005_s8e_scoping",
            # RFC-0005 S8f -- a clean sxSat's witness reproduces: a table's /
            # set's size is tied to its present key terms at every check, and
            # table/set/seq witnesses render len entries; walker 153->154.
            "tsymex_rfc0005_s8f_witness",
            # RFC-0005 S8g -- faithful scalar, string and defect models:
            # float->int never raises, unary-minus overflow, split(s, ""),
            # new(int) zero-init, slice/del defect classes, else-arm
            # discriminator reassignment; walker 154->155.
            "tsymex_rfc0005_s8g_models",
            # RFC-0005 S8h -- ref witnesses that reproduce: built from the
            # model's input heap -- nil, aliasing, recursive cells and cycles,
            # refs in by-value fields; walker 155->156.
            "tsymex_rfc0005_s8h_refwitness",
            # RFC-0005 S8i -- S8g's different-mechanism remainder: low(T)
            # div/mod -1, truncating mod, uint64 -> float, int -> range
            # conversions, declined-construction reassignment, the concolic
            # if-walker's raise drain; walker 156->157.
            "tsymex_rfc0005_s8i_models",
            # RFC-0005 S8j -- S8i's unlowered exits: the SUT's own `return`
            # lowered and drained, an inline `ref <case object>` field,
            # narrowing int conversions (checked into signed/char, truncating
            # into unsigned), one range check per store; walker 157->158.
            "tsymex_rfc0005_s8j_exits",
            # RFC-0005 S8l -- S8j's exit remainder: finally on a return exit,
            # `defer:`, named ref variants and the heap discriminator write's
            # branch check, an inline ref to a multi-variant; walker 158->159.
            "tsymex_rfc0005_s8l_exits",
            "tsymex_rfc0005_s8l_exits_b",
            # RFC-0005 S8m -- S8l's remainder: finally on break/continue,
            # labelled blocks, sort-checked Z3 construction, ref locals and
            # casts, nil ref locals, a closure's bare return; walker 159->160.
            "tsymex_rfc0005_s8m_exits",
            "tsymex_rfc0005_s8m_exits_b",
            "tsymex_rfc0005_s8m_exits_c",
            "tsymex_rfc0005_s8k_bounds",
            # RFC-0005 S8n -- the precision remainder: concolic closure
            # conditions, ref / ptr witnesses in `renderAsChoices`, a callee's
            # unwritten `result`, variant closure results and the variant
            # zero value; walker 161->162.
            "tsymex_rfc0005_s8n_precision",
            # RFC-0005 S8o -- S8k's termination remainder: byte tests matched
            # by decl kind (Z3 4.13.4), byte-vs-byte / byte-vs-input character
            # forms, constant index folding, a bounded concolic pc check, the
            # seq.last_indexof incremental-core guard; walker 162->163.
            "tsymex_rfc0005_s8o_termination",
            # RFC-0005 S8p -- S8n's precision remainder: distinct and
            # multi-variant result binding, the multi-variant zero value, the
            # SUT's unwritten `result`, value field writes, char `add`,
            # structured closure results; walker 163->164.
            "tsymex_rfc0005_s8p_precision",
            "tsymex_rfc0005_s8p_precision_b",
            "tsymex_rfc0005_s8p_precision_c",
            # RFC-0005 S8q -- S8o's termination remainder: a B3 scan-pair
            # offset param allocated as a stamped Int (no bv2int bridge into
            # the string query), a conjunctive symexAssume split per
            # conjunct; walker 164->165.
            "tsymex_rfc0005_s8q_termination",
            # RFC-0005 S8s -- S8p's precision remainder: a `seq[uint8]`
            # element vs a literal, the `else`-arm multi-variant zero value,
            # a callee's `array` result, variant arm field and positional
            # tuple-element writes, n43's cpp build; walker 165->167 (166 is
            # S8r's).
            "tsymex_rfc0005_s8s_precision",
            "tsymex_rfc0005_s8s_precision_b",
            "tsymex_rfc0005_s8s_precision_c",
            "tsymex_rfc0005_s8s_precision_d",
            "tsymex_rfc0005_s8s_precision_e",
            "tsymex_rfc0005_s8s_precision_f",
            "tsymex_rfc0005_s8s_precision_g",
            "tsymex_rfc0005_s8s_precision_h",
            # RFC-0005 S8r -- the symex-mingw shard 2 runner loss: the
            # theory-free check really has no sequence theory on Z3 4.13.4,
            # and a cap-only refutation declines without a string search.
            "tsymex_rfc0005_s8r_theoryfree",
            # RFC-0005 S8t -- S8q's termination remainder: and/or chains
            # lowered with nested guards (linear paths), Q1/B0, pair-loop,
            # B4 and isExact scan offsets allocated as stamped Ints;
            # walker 167->168.
            "tsymex_rfc0005_s8t_termination",
            # RFC-0005 S8u -- S8s's precision remainder: else-covered
            # constructors, local Table / HashSet, `new(result)`, bool
            # multi-variant axes, distinct / container zero values, array
            # element writes; walker 168->169.
            "tsymex_rfc0005_s8u_precision",
            "tsymex_rfc0005_s8u_precision_b",
            "tsymex_rfc0005_s8u_precision_c",
            # RFC-0005 S8w -- S8t's remainder: alternating and/or chains
            # joined (linear paths), Case 2/3 while guards with continue
            # rotated, turned-down B4 offsets stamped and wrapping;
            # walker 169->171.
            "tsymex_rfc0005_s8w_remainder",
            "tsymex_rfc0005_s8w_remainder_b",
            "tsymex_rfc0005_s8w_remainder_b_checksoff",
            # RFC-0005 S8x -- S8t2's remainder: the compile-time VM's `let`
            # aliasing pinned, the parser's two latent value-location lets
            # bound by index / `var`; no walker bump.
            "tsymex_rfc0005_s8x_vm_alias",
            # RFC-0005 S8w2 -- S8w's symex-mingw (Z3 4.13.4) hotfix: a
            # short-circuit join builds the chain's connective, not an
            # `ite`; a literal `shr` on an unstamped Int is Int floor
            # division, not an `int2bv` bridge. Reads query text via its
            # `.nim.cfg` (`-d:symexQueryStats`).
            "tsymex_rfc0005_s8w2_hotfix",
            # RFC-0005 S8aa -- S8w's remainder: unchecked zero divisors
            # trap, the short-circuit join covers strings, seqs, heap
            # cells, refs and multi-path operands, B6 negative starts
            # raise, `len.uint` reinterprets; walker 171->172.
            "tsymex_rfc0005_s8aa_remainder",
            "tsymex_rfc0005_s8aa_remainder_checksoff",
            # RFC-0005 S8v -- S8r's termination remainder: checkCapped's
            # step 1c carries str.len / str.indexof / seq.last_indexof
            # ranges, so a cap-only refutation through them declines without
            # a string search on Z3 4.13.4; walker 172->173.
            "tsymex_rfc0005_s8v_termination",
            # RFC-0005 S8ab -- S8x's remainder: a type-aware typed-AST
            # guard (getImpl + getTypeInst) over the same VM let-aliasing
            # hazard, across all 15 files S8x's own audit covered, in
            # place of S8x's one-file/one-pattern source-text pin; no
            # walker bump. Extended by S8af (same file): Table/`[]`-via-
            # nnkCall aliasing, sameType identity (was repr text), forced
            # generic-instantiation coverage, scan.nim added to scope; no
            # walker bump.
            "tsymex_rfc0005_s8ab_letaudit",
            # RFC-0005 S8ae -- S8v's remainder: step 1c's facts link the
            # sequence functions (indexof / contains / prefixof / slices)
            # and range at / substr / to_code / to_int, so a query refuted
            # only through them is UNSAT, not a cap decline; walker 173->174.
            "tsymex_rfc0005_s8ae_remainder",
            "tsymex_rfc0005_s8ae_remainder_b",
            "tsymex_rfc0005_s8ae_remainder_c",
            # RFC-0005 S8ad -- S8ac's remainder: a borrowed result of a
            # distinct type no parameter carries allocates its sort, a
            # boxed distinct merges with its bare base; linear bounds on
            # Int quotients / remainders and negated bitvectors decide
            # `start div y == start` under the seq theory; walker 174->175.
            # Reads per-query step counts via its `.nim.cfg`
            # (`-d:symexQueryStats`).
            "tsymex_rfc0005_s8ad_remainder",
            # RFC-0005 S8y -- the n36_raise_degrade / s1c_verdict floor:
            # implied byte-domain constraints dropped, and a tainted target
            # hit as deep as one that ran out of budget declined unsolved
            # (beSolverUndef); walker 175->176.
            "tsymex_rfc0005_s8y_budget_decline",
            # RFC-0005 S8z: S8u's remainder -- array low bounds, aliases and
            # symbolic-index writes, an enum zero without ordinal 0, range
            # discriminators, closure results, narrow container cells;
            # walker 176->177.
            "tsymex_rfc0005_s8z_remainder",
            "tsymex_rfc0005_s8z_remainder_b",
            "tsymex_rfc0005_s8z_remainder_c",
            "tsymex_rfc0005_s8z_remainder_d",
            # RFC-0005 S8ac -- S8aa's remainder: var-parameter write-back
            # (var refs, located actuals, raise / cache / outer-except
            # finally), masked shift counts, the linear unchecked div wrap,
            # the join over allocation and table / set / distinct / variant
            # state; walker 177->178. Reads per-query step
            # counts via its `.nim.cfg` (`-d:symexQueryStats`).
            "tsymex_rfc0005_s8ac_remainder",
            "tsymex_rfc0005_s8ac_remainder_b",
            # RFC-0005 S8aj -- S8ad's remainder: uninitialised local
            # arrays, objects, variants and seqs take Nim's zero value (an
            # element write then a read faulted the walker), and an Int
            # merges with a bitvector through reconcileInt; an unchecked
            # sum that wraps decides (divRangeFacts' next window); walker
            # 178->179. Reads per-query step counts via its `.nim.cfg`.
            "tsymex_rfc0005_s8aj_remainder",
            "tsymex_rfc0005_s8aj_remainder_b",
            "tsymex_rfc0005_s8aj_remainder_c",
            "tsymex_rfc0005_s8aj_remainder_c_checksoff",
            # RFC-0005 S8ao -- S8aj's remainder: `add` on a dotted seq
            # field (`o.s.add v`, nested `a.b.s.add v`, a ref object's
            # `p.s.add v`) is modelled through the field path instead of
            # declining (N49); `zeroValueForType` keeps declining for
            # `itUninterp` -- proven the only sound answer, not widened;
            # walker 179->181.
            "tsymex_rfc0005_s8ao_remainder",
            # RFC-0005 S8ai -- S8ae's remainder: step 1c's links follow the
            # query's equality classes; replace_all / in_re / from_int /
            # nonzero-start indexof / word-equation facts; seq.last_indexof
            # queries take step 1c; walker 181->182.
            "tsymex_rfc0005_s8ai_semantic",
            "tsymex_rfc0005_s8ai_semantic_c",
            "tsymex_rfc0005_s8ai_semantic_b",
            "tsymex_rfc0005_s8ai_semantic_b2",
            "tsymex_rfc0005_s8ai_semantic_b3",
            # RFC-0005 S8ag -- S8y's remainder: a one-character literal
            # str.indexof lowers to a fresh Int with split axioms (and
            # chain facts), so N36's five-iteration exits find a model; a
            # tainted SAT after half its budget bounds later hits as a
            # budget-out does; walker 182->190 (batch 1).
            "tsymex_rfc0005_s8ag_indexsplit",
            "tsymex_rfc0005_s8ag_indexsplit_b",
            "tsymex_rfc0005_s8ag_indexsplit_c",
            # RFC-0005 S8am -- S8z's remainder: compound assignment on a
            # seq element; a seq element assignment checks the index bound
            # before the RHS; low/high on an array value; array[bool, T];
            # char/byte/uint8 Table values and HashSet elements are
            # reachable witness parameters; a char witness renders char,
            # not uint8; a non-zero-based array witness renders its
            # declared index range; walker 182->190 (batch 1), render
            # 11->12.
            "tsymex_rfc0005_s8am_remainder",
            # RFC-0005 S8an -- S8ac's remainder: nested procs/funcs (with
            # captures, as values, recursion); `addr x` passed as a `ptr`
            # (a cell for the call; `let p = addr x`); module-level globals
            # threaded through calls; overloads and same-named nested
            # routines keyed apart; walker 182->190 (batch 1).
            "tsymex_rfc0005_s8an_remainder",
            "tsymex_rfc0005_s8an_remainder_b",
            "tsymex_rfc0005_s8an_remainder_b2",
            "tsymex_rfc0005_s8an_remainder_c",
            "tsymex_rfc0005_s8an_remainder_d",
            # RFC-0005 S8ap -- S8ao's remainder: a seq / Table / HashSet
            # field of a ref object is a leaf-split heap cell and a string
            # field is read too (aliasing, nil, witness); del / insert /
            # incl / excl / []= / [i]= on a dotted field and `add` on a
            # dotted string field take the field-write primitive; an
            # itUninterp `var` declines with its own kind; walker
            # 182->190 (batch 1).
            "tsymex_rfc0005_s8ap_remainder",
            "tsymex_rfc0005_s8ap_remainder_b",
            "tsymex_rfc0005_s8ap_remainder_c",
            "tsymex_rfc0005_s8ap_remainder_d",
            # RFC-0005 S8aq -- S8ai's remainder: step 1c no longer depends
            # on step 1 reaching UNSAT (a cancelled step 1 still gets the
            # facts-based decision); the dropped "L is at least every found
            # index" link is reformulated as a ground fact that validates
            # within budget; str.replace_all is reachable under this
            # suite's own `-d:z3WithSeqReplaceAll` (`.nim.cfg`); a missed
            # implied (non-stated) equality is shown to cost completeness
            # only. Walker 182->190 (batch 1).
            "tsymex_rfc0005_s8aq_remainder",
            # RFC-0005 S8aw -- regex `replace(s, re"p", by)` lowered by the
            # walker (a literal, a one-byte class, a class under `+`;
            # every leftmost non-overlapping PCRE match, unrolled per
            # position) instead of the never-built `str.replace_re` gate;
            # other shapes decline naming the construct; the last_indexof /
            # indexof join emitted. Walker 190->202 (batch 2).
            "tsymex_rfc0005_s8aw_remainder",
            # RFC-0005 S8ay -- S8aw's remainder: the std/re entry points'
            # own formulas over a PCRE-faithful reader, re vs rex in the
            # IR, a rejected pattern raises RegexError, exact regex replace
            # past 16 bytes, step 1c's uncapped half first. Walker
            # 190->202 (batch 2).
            "tsymex_rfc0005_s8ay_remainder",
            "tsymex_rfc0005_s8ay_remainder_b",
            "tsymex_rfc0005_s8ay_remainder_c",
            "tsymex_rfc0005_s8ay_remainder_d",
            "tsymex_rfc0005_s8bb_remainder",
            "tsymex_rfc0005_s8bb_remainder_b",
            "tsymex_rfc0005_s8bb_exhaustive",
            "tsymex_rfc0005_s8bb_selection",
            "tsymex_rfc0005_s8bb_selection_b",
            "tsymex_rfc0005_s8bb_constructs",
            "tsymex_rfc0005_s8bb_constructs_b",
            "tsymex_rfc0005_s8bb_constructs_c",
            "tsymex_rfc0005_s8bb_captures",
            "tsymex_rfc0005_s8bb_captures_b",
            "tsymex_rfc0005_s8bb_captures_c",
            "tsymex_rfc0005_s8bb_captures_d",
            "tsymex_rfc0005_s8bb_capvalues",
            "tsymex_rfc0005_s8bb_capvalues_plus",
            "tsymex_rfc0005_s8bb_capvalues_lf",
            "tsymex_rfc0005_s8bb_replace",
            "tsymex_rfc0005_s8bb_replace_b",
            "tsymex_rfc0005_s8bb_replace_c",
            "tsymex_rfc0005_s8bb_replace_d",
            # RFC-0005 S8bi -- S8bb's remainder A: closure/HOF/borrow/regex
            # nodes as raise sites, closure exit facts placed in evaluation
            # order, newSeq / newSeqOfCap / newSeqUninit, set literals in
            # `in`/`notin`, and the recursive-definition fuel scan. Walker 210.
            "tsymex_rfc0005_s8bi_remainder",
            "tsymex_rfc0005_s8bi_remainder_b",
            "tsymex_rfc0005_s8bi_remainder_c",
            # RFC-0005 S8bj -- the reader on verbs, start options, UTF mode,
            # (?m) and (?X) against re(); PCRE's start-of-match data from the
            # tree against pcre_fullinfo; the agenda attempt and search
            # (concrete, languages, Z3 entry formulas, replace) against
            # std/re; Q2/Q7/Q8 decided; walker verdicts, floor >= 211.
            "tsymex_rfc0005_s8bj_syntax",
            "tsymex_rfc0005_s8bj_startopt",
            "tsymex_rfc0005_s8bj_verbs",
            "tsymex_rfc0005_s8bj_langs",
            "tsymex_rfc0005_s8bj_langs_b",
            "tsymex_rfc0005_s8bj_entries",
            "tsymex_rfc0005_s8bj_entries_multiline",
            "tsymex_rfc0005_s8bj_entries_utf",
            "tsymex_rfc0005_s8bj_entries_utf_b",
            "tsymex_rfc0005_s8bj_entries_utf_c",
            "tsymex_rfc0005_s8bj_replace",
            "tsymex_rfc0005_s8bj_replace_lemmas",
            "tsymex_rfc0005_s8bj_walker",
            # RFC-0005 S8bq -- S8bi's remainder: a length above 2^20
            # declines, Regex constructor calls, builtin set[T] values,
            # non-constant set literals, newSeqUninit's unwritten reads.
            # Walker 220.
            "tsymex_rfc0005_s8bq_remainder",
            "tsymex_rfc0005_s8bq_remainder_b",
            "tsymex_rfc0005_s8bq_remainder_c",
            # RFC-0005 batch 6 -- an index assignment, pop or discriminator
            # reassignment on a global the walk has not written reads its
            # entry value (was a false sxUnsat). Walker 230.
            "tsymex_rfc0005_b6_globalrecv",
            # RFC-0005 batch 7 -- a var openArray view a later argument
            # writes declines (was a false sxUnsat); a global seq indexed by
            # a call; S8br's slow addr cell terminates. Walker 237.
            "tsymex_rfc0005_b7_integration",
            "tsymex_rfc0005_b8_integration",
            "tsymex_rfc0005_b8_integration_b",
            "tsymex_rfc0005_b8_integration_c",
            "tsymex_rfc0005_b8_integration_d",
            "tsymex_rfc0005_s8bt_libversion",
            "tsymex_rfc0005_s8bt_jit",
            "tsymex_rfc0005_s8bt_jit_langs",
            "tsymex_rfc0005_s8bt_jit_langs_b",
            "tsymex_rfc0005_s8bt_jit_langs_c",
            "tsymex_rfc0005_s8bt_jit_langs_d",
            "tsymex_rfc0005_s8bt_jit_langs_e",
            "tsymex_rfc0005_s8bt_jit_langs_f",
            "tsymex_rfc0005_s8bt_jit_replace",
            "tsymex_rfc0005_s8bt_jit_replace_b",
            "tsymex_rfc0005_s8bt_jit_replace_c",
            "tsymex_rfc0005_s8bt_skipname",
            "tsymex_rfc0005_s8bt_skipname_b",
            "tsymex_rfc0005_s8bt_skipname_c",
            "tsymex_rfc0005_s8bt_skipname_d",
            "tsymex_rfc0005_s8bt_skipname_e",
            "tsymex_rfc0005_s8bt_skipname_f",
            "tsymex_rfc0005_s8bt_skipname_langs",
            "tsymex_rfc0005_s8bt_limit",
            "tsymex_rfc0005_s8bt_limit_b",
            "tsymex_rfc0005_s8bt_limit_c",
            "tsymex_rfc0005_s8bt_limit_d",
            "tsymex_rfc0005_s8bt_limit_langs",
            "tsymex_rfc0005_s8bt_limit_langs_b",
            "tsymex_rfc0005_s8bt_utf",
            "tsymex_rfc0005_s8bt_utf_b",
            "tsymex_rfc0005_s8bt_utf_c",
            "tsymex_rfc0005_s8bt_utf_d",
            "tsymex_rfc0005_s8bt_utf_e",
            "tsymex_rfc0005_s8bt_utf_any",
            "tsymex_rfc0005_s8bt_utf_any_b",
            "tsymex_rfc0005_s8bt_utf_any_c",
            "tsymex_rfc0005_s8bt_utf_any_d",
            "tsymex_rfc0005_s8bt_utf_any_e",
            "tsymex_rfc0005_s8bt_caps",
            "tsymex_rfc0005_s8bt_caps_b",
            "tsymex_rfc0005_s8bt_caps_c",
            "tsymex_rfc0005_s8bt_replace_lemmas",
            "tsymex_rfc0005_s8bt_replace_lemmas_b",
            "tsymex_rfc0005_s8bt_replace_facts",
            # RFC-0005 S8bv -- S8bq's remainder: iterating a builtin set, enum
            # subranges (no set conversion across domains exists), pigeonhole-
            # hard card queries and newSeqUninit taint precision. Walker 253.
            "tsymex_rfc0005_s8bv_iter_order",
            "tsymex_rfc0005_s8bv_iter_char",
            "tsymex_rfc0005_s8bv_iter_char_b",
            "tsymex_rfc0005_s8bv_iter_char_count",
            "tsymex_rfc0005_s8bv_iter_int8",
            "tsymex_rfc0005_s8bv_iter_forms",
            "tsymex_rfc0005_s8bv_subrange",
            "tsymex_rfc0005_s8bv_subrange_sets",
            "tsymex_rfc0005_s8bv_card_uninit",
            # RFC-0005 S8cf -- S8bt's remainder.
            "tsymex_rfc0005_s8cf_reach",
            "tsymex_rfc0005_s8cf_limits",
            "tsymex_rfc0005_s8cf_point",
            "tsymex_rfc0005_s8cf_point_b",
            "tsymex_rfc0005_s8cf_jitlimit",
            "tsymex_rfc0005_s8cf_jitlimit_b",
            "tsymex_rfc0005_s8cf_skipcount",
            "tsymex_rfc0005_s8cf_limitgaps",
            "tsymex_rfc0005_s8cf_classes",
            "tsymex_rfc0005_s8cf_classes_b",
            "tsymex_rfc0005_s8cf_jitutf",
            "tsymex_rfc0005_s8cf_jitutf_b",
            "tsymex_rfc0005_s8cf_jitutf_c",
            "tsymex_rfc0005_s8cf_jitutf_d",
            "tsymex_rfc0005_s8cf_jitutf_e",
            "tsymex_rfc0005_s8cf_jitutf_f",
            "tsymex_rfc0005_s8cf_replace",
            # RFC-0005 S11 -- the public surface: Soundness / ReplayStatus /
            # trusted() / gaps() on SymexResult and SymexFinding, the bound
            # echo, cached results carrying their stored Soundness, and the
            # render layer incl. the annotation-violation channel; also the
            # gaps() walkthrough. Public imports only. walker 182->190
            # (batch 1).
            "tsymex_rfc0005_s11_surface",
            # RFC-0005 S8ar -- S8ap's remainder: tree-valued heap cells
            # (tuple / object / array / distinct fields), every backed
            # Table key and value type, insert, seq[string] add, dotted
            # chains rooted at a ref field, ref pointees render by name,
            # heap-step depth budget; walker 190->202 (batch 2).
            "tsymex_rfc0005_s8ar_remainder",
            "tsymex_rfc0005_s8ar_remainder_b",
            "tsymex_rfc0005_s8ar_remainder_c",
            "tsymex_rfc0005_s8ar_remainder_d",
            "tsymex_rfc0005_s8ar_remainder_e",
            "tsymex_rfc0005_s8ar_remainder_f",
            "tsymex_rfc0005_s8ar_remainder_g",
            "tsymex_rfc0005_s8ar_remainder_h",
            # RFC-0005 S8at -- S8ar's remainder: a ref to an anonymous
            # tuple, initTable in a SUT, a symbolic index into an array of
            # seqs, by-value case-object fields, distinct over a composite
            # base, Table float keys and container values, KeyError,
            # 2^32-cell key domains; walker 190->202 (batch 2).
            "tsymex_rfc0005_s8at_remainder",
            "tsymex_rfc0005_s8at_remainder_b",
            "tsymex_rfc0005_s8at_remainder_c",
            "tsymex_rfc0005_s8at_remainder_d",
            "tsymex_rfc0005_s8at_remainder_e",
            "tsymex_rfc0005_s8at_remainder_f",
            # RFC-0005 S8as -- S8an's remainder: if-arm pruning in a
            # recursion; opaque-call effect summaries havoc globals; a
            # global's entry value; closure capture/global write-back;
            # more `addr` forms; a path-based alias check; an Int-sorted
            # `int` heap; walker 190->202 (batch 2).
            "tsymex_rfc0005_s8as_remainder",
            "tsymex_rfc0005_s8as_remainder_b",
            "tsymex_rfc0005_s8as_remainder_c",
            # RFC-0005 S8au -- the S8an / S8ag remainder: a var / addr
            # actual reachable through a global or capture declines; var
            # ptr formals modelled; every find / rfind needle splits;
            # consecutive chain facts; the c-notin-t form per Z3 version.
            # Items 1-2 (closed by S8ad) re-pinned. Walker 190->202
            # (batch 2).
            "tsymex_rfc0005_s8au_remainder",
            "tsymex_rfc0005_s8au_remainder_b",
            "tsymex_rfc0005_s8au_remainder_c",
            # RFC-0005 S8av -- S8am's and S11's remainder: the public cache
            # macros (saveSymexWitness/loadSymexWitnesses/saveSymexVerdict/
            # loadSymexVerdict) route dbErrors via recordSymexDbError instead
            # of discarding them; db.nim's F6/secondary/corpus/scheduler
            # wrappers raise DbError on a nil optional closure instead of
            # SIGSEGV-ing; a served sfUnknown/sfUnsat verdict cache hit also
            # serves its stored gaps() (CachedVerdict widened, an entry
            # without gaps metadata degrades to gaps: @[] rather than a
            # miss); S8am's "raise-irrelevant-parameter witness sentinel" is
            # proved to be IndexDefect's own concrete, replayable witness
            # (Phase 15 E6 pre-emption), not a sentinel. Walker 190->202
            # (batch 2).
            "tsymex_rfc0005_s8av_remainder",
            # RFC-0005 S8az -- S8av's own remainder: the :sat witness cache
            # slot (CachedWitness) and each :raised:<type> sentinel
            # (CachedRaised, loadSymexRaisedImpl's new return type) also
            # serve their stored gaps() on a hit now, through the SAME
            # gapsMeta/storedGaps pair CachedVerdict already used; an entry
            # without gaps metadata (pre-S8az, or a third-party writer)
            # still degrades to gaps: @[] rather than a miss. Walker
            # 190->202 (batch 2).
            "tsymex_rfc0005_s8az_remainder",
            # RFC-0005 S8ax -- S8as's remainder: a fact-keyed call cache;
            # adaptive if-arm checks and call depth; per-cell Int heaps;
            # opaque routine summaries; closure environments; evaluation
            # order; `addr` forms; alias precision; walker 202->209
            # (batch 3).
            "tsymex_rfc0005_s8ax_remainder",
            "tsymex_rfc0005_s8ax_remainder2",
            "tsymex_rfc0005_s8ax_remainder3",
            "tsymex_rfc0005_s8ax_remainder_b",
            "tsymex_rfc0005_s8ax_remainder_c",
            "tsymex_rfc0005_s8ax_remainder_d",
            "tsymex_rfc0005_s8ax_remainder_e",
            "tsymex_rfc0005_s8ax_remainder_f",
            "tsymex_rfc0005_s8ax_remainder_g",
            # RFC-0005 S8ba -- S8au's remainder: a declining arm binds its
            # temporary (never read as a global); seq[distinct] modelled;
            # len <= high(int) in step 1c; a heap var/addr actual a global
            # or capture also reaches is passed by reference; split axioms
            # built once, in a fixed order. Walker 202->209 (batch 3).
            "tsymex_rfc0005_s8ba_remainder",
            "tsymex_rfc0005_s8ba_remainder_b",
            "tsymex_rfc0005_s8ba_remainder_c",
            # RFC-0005 S8bd: bit-vector offset links; seq[distinct]
            # witnesses; maxHeapDepth bounds a chain; by-reference
            # elements, call results and generic callees. Walker 202->209
            # (batch 3).
            "tsymex_rfc0005_s8bd_remainder",
            "tsymex_rfc0005_s8bd_remainder_b",
            "tsymex_rfc0005_s8bd_remainder_c",
            # RFC-0005 S8bf: two var / addr heap actuals that may be one
            # cell through different refs are passed by reference. Walker
            # 202->209 (batch 3).
            "tsymex_rfc0005_s8bf_alias",
            # RFC-0005 S8bc -- S8at's remainder: getOrDefault, borrow
            # routines, leaf-split seq elements, array-element insert,
            # newSeq, Table iteration, mgetOrPut, inlined-iterator
            # parameter conversions, seq[char] / seq[enum] witnesses;
            # walker 209->217 (batch 4).
            # RFC-0005 S8bl (item 5): split in three (a / b / c), the
            # single file's compile having taken 77 s on Windows.
            "tsymex_rfc0005_s8bc_remainder_a",
            "tsymex_rfc0005_s8bc_remainder_a2",
            "tsymex_rfc0005_s8bc_remainder_a3",
            "tsymex_rfc0005_s8bc_remainder_b",
            "tsymex_rfc0005_s8bc_remainder_b2",
            "tsymex_rfc0005_s8bc_remainder_b3",
            "tsymex_rfc0005_s8bc_remainder_c",
            "tsymex_rfc0005_s8bc_remainder_c2",
            "tsymex_rfc0005_s8bc_remainder_c3",
            "tsymex_rfc0005_s8bc_remainder_c4",
            # RFC-0005 S8be -- S8ax's remainder: opaque implicit Defects
            # and raise subtypes; a bounded replay; `{.global.}`; int32
            # widening; Int-sorted call returns; tuples of closures; a
            # capture-keyed call cache; element and case-object `addr`
            # cells; walker 209->217 (batch 4).
            "tsymex_rfc0005_s8be_remainder",
            # Split in three by S8bo.
            "tsymex_rfc0005_s8be_remainder_b",
            "tsymex_rfc0005_s8be_remainder_c",
            # RFC-0005 S8bo -- S8be's remainder: isNil and unlowered
            # magics; plain-object, arm-field and seq-of-object address
            # cells, whole seq assignment as a resize; abandoned and
            # threaded replay fidelity.
            "tsymex_rfc0005_s8bo_nil",
            "tsymex_rfc0005_s8bo_cells",
            "tsymex_rfc0005_s8bo_replay",
            "tsymex_rfc0005_s8cb_magics",
            "tsymex_rfc0005_s8cb_tostr",
            "tsymex_rfc0005_s8cb_order",
            "tsymex_rfc0005_s8cb_cells",
            "tsymex_rfc0005_s8cb_replay",
            # RFC-0005 S8cp -- S8cb's remainder: `{.cast(uncheckedAssign).}`.
            # Its item 1 pin (an abandoned replay's footprint) is dropped:
            # S8ct leaves no replay running.
            "tsymex_rfc0005_s8cp_unchecked",
            "tsymex_rfc0005_s8cp_unchecked_zero",
            "tsymex_rfc0005_s8cp_unchecked_decline",
            # RFC-0005 S8bh -- S8bf's remainder: var / addr effects of a
            # call through a proc value; a ptr of unknown origin may address
            # a ref field, a global or a var parameter; ref conversions along
            # a hierarchy keep identity; walker 209->217 (batch 4).
            "tsymex_rfc0005_s8bh_remainder",
            "tsymex_rfc0005_s8bh_remainder_b",
            "tsymex_rfc0005_s8bh_remainder_c",
            "tsymex_rfc0005_s8bh_remainder_d",
            "tsymex_rfc0005_s8bh_remainder_e",
            "tsymex_rfc0005_s8bh_remainder_f",
            # RFC-0005 S8bm: step 1 searches in a context of its own (the
            # same with and without the facts-first check); a slice
            # element's byte test in character form; B1-1's tight unit
            # ceiling. Walker 209->214.
            "tsymex_rfc0005_s8bm_stability",
            # RFC-0005 S8bk (address-of-argument timing), split by S8br
            # into three files so each compiles and runs under 60 s per
            # backend (fixture: tests/s8bk_argtiming_fixture.nim).
            "tsymex_rfc0005_s8bk_argtiming",
            "tsymex_rfc0005_s8bk_argtiming_addr",
            "tsymex_rfc0005_s8bk_argtiming_checks",
            # RFC-0005 S8bg -- S8bd's remainder: a by-reference lvalue
            # reached through a representation-preserving conversion
            # (distinct, range to base) is modelled through; one reached
            # through a cast gets a scoped decline naming the cast instead
            # of a crash; the distinct-bijectivity hint walks the whole
            # distinct chain before judging non-decidability. Walker
            # 209->218.
            "tsymex_rfc0005_s8bg_remainder",
            # RFC-0005 S8bs -- a var, addr or by-pointer actual whose
            # variable is address-taken is bound to its cell; heap lvalues
            # go by reference; by-value seqs share element cells; inlined
            # iterator formals name the caller's locations; walker 222.
            # Split in four by theme (shared SUTs in s8bs_suts.nim).
            "tsymex_rfc0005_s8bs_addrglobal",
            "tsymex_rfc0005_s8bs_byref",
            "tsymex_rfc0005_s8bs_iterparams",
            "tsymex_rfc0005_s8bs_byvalue",
            # RFC-0005 S8bn: S8bh's remainder -- ptr witnesses and targets,
            # proc fields and methods, `of` / `nil`, hierarchies, parameter
            # tags, S8bk's late address. Walker 215 (provisional).
            "tsymex_rfc0005_s8bn_remainder",
            "tsymex_rfc0005_s8bn_remainder_b",
            "tsymex_rfc0005_s8bn_remainder_c",
            "tsymex_rfc0005_s8bn_remainder_d",
            "tsymex_rfc0005_s8bn_remainder_e",
            "tsymex_rfc0005_s8bn_remainder_f",
            # RFC-0005 S8bl -- S8bc's remainder: the system magics with a
            # `var` parameter (swap, wasMoved, move, reset, setLen, add on
            # an element, new on a field) and the guard scan over them,
            # add to a seq of an unbacked element, plain type aliases,
            # mpairs / mvalues, a Table length change while iterating,
            # ref parts and long nested seqs in witnesses; walker
            # 203->213 (provisional).
            "tsymex_rfc0005_s8bl_magics",
            "tsymex_rfc0005_s8bl_setlen",
            "tsymex_rfc0005_s8bl_magicscan",
            "tsymex_rfc0005_s8bl_gaps",
            "tsymex_rfc0005_s8bl_gaps_b",
            "tsymex_rfc0005_s8bl_gaps_c",
            "tsymex_rfc0005_s8bl_gaps_d",
            "tsymex_rfc0005_s8bl_borrow",
            "tsymex_rfc0005_s8bl_seqops",
            "tsymex_rfc0005_s8bl_pairloop",
            # RFC-0005 S8bw: S8bn's remainder -- in-band receiver declines,
            # aggregate globals, pointers into case objects and aggregate
            # containers. Walker 227 (provisional).
            "tsymex_rfc0005_s8bw_remainder",
            "tsymex_rfc0005_s8bw_remainder_b",
            "tsymex_rfc0005_s8bw_remainder_c",
            "tsymex_rfc0005_s8bw_remainder_d",
            "tsymex_rfc0005_s8cd_globals",
            # RFC-0005 S8cs: the stores to a variable the walk does not see
            # (lifetime hooks, code it cannot list) decline a read of it, and
            # an opaque's summary aims a pointer store at every global.
            # Walker 260 (provisional).
            "tsymex_rfc0005_s8cs_routes",
            "tsymex_rfc0005_s8cs_routes_b",
            "tsymex_rfc0005_s8cs_routes_c",
            "tsymex_rfc0005_s8cs_routes2",
            "tsymex_rfc0005_s8cd_globals_b",
            "tsymex_rfc0005_s8cd_ops",
            "tsymex_rfc0005_s8cd_ops_b",
            "tsymex_rfc0005_s8cd_setorder_small",
            "tsymex_rfc0005_s8cd_setorder_md",
            "tsymex_rfc0005_s8cd_setorder_large",
            # RFC-0005 S8bz: S8bw's remainder. Walker 249 (provisional).
            "tsymex_rfc0005_s8bz_written",
            "tsymex_rfc0005_s8bz_written_b",
            "tsymex_rfc0005_s8bz_written_c",
            "tsymex_rfc0005_s8bz_cells",
            "tsymex_rfc0005_s8bz_cells_b",
            "tsymex_rfc0005_s8bz_cells_c",
            "tsymex_rfc0005_s8bz_cells_d",
            "tsymex_rfc0005_s8bz_cells_e",
            "tsymex_rfc0005_s8bz_cells_f",
            "tsymex_rfc0005_s8bz_overlap",
            "tsymex_rfc0005_s8cd_setorder_by",
            # RFC-0005 S8bp: every checkCapped search and the per-thread
            # kind probes in contexts of their own (no step's cost moves
            # with the walk's state; a thread's first walk searches as its
            # second); a membership and a negated one on one string
            # decided as one (the unbounded endsWith run on Z3 4.13.4).
            # Walker 214->219.
            "tsymex_rfc0005_s8bp_isolation",
            # RFC-0005 S8bu -- S8bs's remainder: the signed bv2int bridge's
            # inverse facts and a finite default queryRLimit (no walk runs
            # forever); walker 225.
            "tsymex_rfc0005_s8bu_term",
            # items 2-3: closure and proc-value calls into an address-taken
            # variable, and `addr` of a part of one.
            "tsymex_rfc0005_s8bu_calls",
            # item 4: openArray views (read, `var`).
            "tsymex_rfc0005_s8bu_views",
            "tsymex_rfc0005_s8bu_varviews",
            # item 4: mitems / mpairs.
            "tsymex_rfc0005_s8bu_mitems",
            # items 5-6: an array element on a path into an address-taken
            # variable; a by-value seq whose whole address is taken.
            "tsymex_rfc0005_s8bu_paths",
            # RFC-0005 S8br -- S8bk's remainder: a call in a by-address
            # actual's index is evaluated once, where the argument stands;
            # a check no snapshot carries declines only when a later
            # argument may write what the lvalue reads (`_framecond`).
            # Walker 223->229.
            "tsymex_rfc0005_s8br_remainder",
            "tsymex_rfc0005_s8br_framecond",
            # RFC-0005 S8bx -- S8bl's remainder: a raise inside in-walk
            # witness extraction (lost on the C backend; fault injection
            # through the file's .nim.cfg); walker 213->228 (provisional).
            "tsymex_rfc0005_s8bx_extractraise",
            "tsymex_rfc0005_s8bx_extractraise_b",
            # S8bx item 2: one classifier for the seq witness reader and
            # the renderability predicate; a type is always rendered.
            "tsymex_rfc0005_s8bx_witnessdrift",
            # S8bx item 3: an mpairs view passed to one call with its
            # Table is one location (IRStmt.cViewAliases, syncViewAliases).
            "tsymex_rfc0005_s8bx_mpairs",
            # S8bx item 4: a key removed while iterating a Table, the
            # length kept, declines (native runs prove the slot walk
            # depends on the hashes).
            "tsymex_rfc0005_s8bx_iterchange",
            # S8bx item 5: a string's setLen over a symbolic string decides.
            "tsymex_rfc0005_s8bx_setlenstr",
            "tsymex_rfc0005_s8cn_step1d",
            "tsymex_rfc0005_s8cn_step1d_b",
            "tsymex_rfc0005_s8cn_step1d_c",
            "tsymex_rfc0005_s8cn_step1d_d",
            "tsymex_rfc0005_s8cn_step1d_e",
            "tsymex_rfc0005_s8cn_step1d_f",
            # S8cn item 2: step 1e, a bounded concrete search.
            "tsymex_rfc0005_s8cn_probe",
            # S8cn items 3 and 4: an mpairs view and its Table.
            "tsymex_rfc0005_s8cn_views",
            "tsymex_rfc0005_s8cn_views_b",
            "tsymex_rfc0005_s8cn_views_c",
            "tsymex_rfc0005_s8cn_views_d",
            "tsymex_rfc0005_s8cn_views_e",
            "tsymex_rfc0005_s8cn_views_f",
            "tsymex_rfc0005_s8cn_seqview",
            "tsymex_rfc0005_s8cn_seqview_b",
            "tsymex_rfc0005_s8cn_seqview_c",
            "tsymex_rfc0005_s8cn_seqview_d",
            "tsymex_rfc0005_s8cn_seqview_e",
            "tsymex_rfc0005_s8cn_seqview_f",
            "tsymex_rfc0005_s8cn_lent",
            "tsymex_rfc0005_s8cn_lent_b",
            "tsymex_rfc0005_s8cn_lent_c",
            "tsymex_rfc0005_s8cn_lent_d",
            "tsymex_rfc0005_s8cn_lent_e",
            "tsymex_rfc0005_s8cn_lent_f",
            "tsymex_rfc0005_s8cn_lentnative",
            "tsymex_0016_k6a_maywrite",
            "tsymex_0016_k6b_hookcopy",
            "tsymex_0016_k6c_round",
            # RFC-0005 S8cq: by-value sharing, var-returning actuals, a call in
            # a location lowered twice.
            "tsymex_rfc0005_s8cq_argorder",
            "tsymex_rfc0005_s8cq_byvalue",
            "tsymex_rfc0005_s8cq_byvalue10",
            "tsymex_rfc0005_s8cq_byvalue11",
            "tsymex_rfc0005_s8cq_byvalue12",
            "tsymex_rfc0005_s8cq_byvalue13",
            "tsymex_rfc0005_s8cq_byvalue2",
            "tsymex_rfc0005_s8cq_byvalue3",
            "tsymex_rfc0005_s8cq_byvalue4",
            "tsymex_rfc0005_s8cq_byvalue5",
            "tsymex_rfc0005_s8cq_byvalue6",
            "tsymex_rfc0005_s8cq_byvalue7",
            "tsymex_rfc0005_s8cq_byvalue8",
            "tsymex_rfc0005_s8cq_byvalue9",
            "tsymex_rfc0005_s8cq_native",
            "tsymex_rfc0005_s8cq_stops",
            "tsymex_rfc0005_s8cq_twice",
            "tsymex_rfc0005_s8cq_twice10",
            "tsymex_rfc0005_s8cq_twice11",
            "tsymex_rfc0005_s8cq_twice12",
            "tsymex_rfc0005_s8cq_twice2",
            "tsymex_rfc0005_s8cq_twice3",
            "tsymex_rfc0005_s8cq_twice4",
            "tsymex_rfc0005_s8cq_twice5",
            "tsymex_rfc0005_s8cq_twice6",
            "tsymex_rfc0005_s8cq_twice7",
            "tsymex_rfc0005_s8cq_twice8",
            "tsymex_rfc0005_s8cq_twice9",
            "tsymex_rfc0005_s8cq_varret",
            "tsymex_rfc0005_s8cq_varret2",
            "tsymex_rfc0005_s8cq_varret3",
            # RFC-0005 S8ce: nim-z3's hooks no longer swallow an in-flight raise
            "tsymex_rfc0005_s8ce_hookraise",
            "tsymex_rfc0005_s8ce_raiseshapes",
            # S8bu's item 6, split out by RFC-0005 S8ca item 9.
            "tsymex_rfc0005_s8bu_byvalseq",
            # RFC-0005 S8ca -- S8bu's remainder; walker 233. Item 1: a call
            # declines in-band when the native stack left is under one more
            # level's need.
            "tsymex_rfc0005_s8ca_stack",
            # item 2: a view follows logged in-place writes, not term
            # shapes; `swap` is modelled.
            "tsymex_rfc0005_s8ca_views",
            # item 3: an `addr s[i]` actual of a seq with element cells.
            "tsymex_rfc0005_s8ca_calls",
            # item 4: closures over address-taken variables and heap lvalues.
            "tsymex_rfc0005_s8ca_closures",
            "tsymex_rfc0005_s8ca_closures_heap",
            # item 5: a seq argument of a proc value or a closure.
            "tsymex_rfc0005_s8ca_procvals",
            # item 6: strings (character writes, openArray[char], views).
            "tsymex_rfc0005_s8ca_strings",
            "tsymex_rfc0005_s8ca_strings_b",
            "tsymex_rfc0005_s8ca_strings_byvalue",
            # item 7: a negative-length toOpenArray; a resizing mitems body.
            "tsymex_rfc0005_s8ca_resize",
            # item 8: a mutation through a pointer to the whole value.
            "tsymex_rfc0005_s8ca_derefmut",
            # RFC-0005 S8by: no (1b)/(1c) after a facts-first SAT; concolic
            # scratch solves in contexts of their own; a regex membership
            # under a disjunction or an ite merged with those that hold
            # where it is read. Walker 219->231.
            "tsymex_rfc0005_s8by_remainder",
            # RFC-0005 S8cc -- S8br's remainder: the address cell's query at
            # a non-literal index is pinned to a step budget; a callee's
            # global counts as written only where it may be; an index call
            # with no symbol is bound once. Walker 237->238.
            "tsymex_rfc0005_s8cc_cellquery",
            "tsymex_rfc0005_s8cc_cellquery_b",
            "tsymex_rfc0005_s8cc_remainder",
            "tsymex_rfc0005_s8cc_remainder_b",
            "tsymex_rfc0005_s8cc_remainder_c",
            # RFC-0005 batch 9: S8ce, S8ca, S8by and S8cc stacked on batch 8.
            # A proc value's aliasing shapes decline; walker 241->245.
            "tsymex_rfc0005_b9_integration",
            "tsymex_rfc0005_b9_integration_b",
            "tsymex_rfc0005_b9_integration_c",
            # A call declines before Nim's call depth limit ends the process.
            "tsymex_rfc0005_b9_calldepth",
            # RFC-0005 batch 10: S8cf, S8cb, S8cd, S8cl and S8cr stacked on
            # batch 9. walker 245->252.
            "tsymex_rfc0005_b10_integration",
            "tsymex_rfc0005_b10_integration_b",
            "tsymex_rfc0005_b10_integration_c",
            # RFC-0005 S8cl: the allocation and lifetime magics, `newString`.
            "tsymex_rfc0005_s8cl_magics",
            "tsymex_rfc0005_s8cl_lifetime",
            "tsymex_rfc0005_s8cl_lifetime_b",
            "tsymex_rfc0005_s8cl_strings",
            # RFC-0005 S8cr: the definition-of-done audit's gaps. The six
            # unpinned fresh-symbol kinds and the coverage invariant; a live
            # sevError beside a clean witness and symexForAll's own pins; a
            # helper check for each to-unsat flip. No bump.
            "tsymex_rfc0005_s8cr_intro",
            "tsymex_rfc0005_s8cr_intro_b",
            "tsymex_rfc0005_s8cr_pins",
            "tsymex_rfc0005_s8cr_flips",
            "tsymex_rfc0005_s8cr_flips_str",
            # RFC-0005 S8ct: no replay runs in the host process, and a term too
            # deep for a recursive walk leaves the process alive; walker 252->261.
            "tsymex_rfc0005_s8ct_isolation",
            "tsymex_rfc0005_s8ct_isolation_b",
            "tsymex_rfc0005_s8ct_isolation_c",
            "tsymex_rfc0005_s8ct_isolation_d",
            "tsymex_rfc0005_s8ct_isolation_e",
            "tsymex_rfc0005_s8ct_reexec",
            "tsymex_rfc0005_s8ct_reexec_b",
            "tsymex_rfc0005_s8ct_reexec_c",
            "tsymex_rfc0005_s8ct_reexec_d",
            "tsymex_rfc0005_s8ct_reexec_e",
            "tsymex_0016_prc01_reexec",
            "tsymex_rfc0005_b11_hoststate",
            "tsymex_rfc0005_b11_hoststate_reexec",
            "tsymex_rfc0005_s8ct_deepterm",
            "tsymex_rfc0005_s8ct_deepterm_b",
            # Batch 11: row B19's exact SUT, split out of deepterm (86 s of its
            # 186 s on Windows, against a 240 s kill).
            "tsymex_rfc0005_s8ct_b19",
            # RFC-0005 S8cu -- a routine compiled under a disabled check declines
            # by name. Walker 252->260.
            "tsymex_rfc0005_s8cu_push",
            "tsymex_rfc0005_s8cu_forms",
            "tsymex_rfc0005_s8cu_kinds",
            "tsymex_rfc0005_s8cu_modules",
            "tsymex_rfc0005_s8cu_import",
            "tsymex_rfc0005_s8cu_scan",
            "tsymex_rfc0005_s8cu_cl_field",
            "tsymex_rfc0005_s8cu_cl_over",
            "tsymex_rfc0005_s8cu_cl_rbo",
            "tsymex_rfc0005_s8cu_cl_checks",
            "tsymex_rfc0005_s8cu_cl_danger",
            "tsymex_rfc0005_s8cu_cl_float",
            "tsymex_rfc0005_s8cu_assert",
            "tsymex_rfc0005_s8cu_cl_assert",
            "tsymex_rfc0005_s8cu_hidden",
            "tsymex_rfc0005_s8cu_nil",
            "tsymex_rfc0005_s8cu_nil_setjmp",
            "tsymex_rfc0005_s8cu_nil_native",
            # RFC-0016 K9a: the native-pin verbs and the pin record.
            "tsymex_0016_k9a_pins",
            "tsymex_0016_k9d0_entries",
            # RFC-0016 K10a-concolic: the flip solve keeps the prefix defined.
            "tsymex_0016_k10ac_concolic",
            "tsymex_0016_k10ac_concolic_checksoff",
            "tsymex_0016_k8a_gen",
            "tsymex_0016_k8a_sink",
            "tsymex_0016_k5a_fwrapv",
            "tsymex_0016_k5a_profile",
            "tsymex_0016_k5a_reads",
            "tsymex_0016_k5a_segment",
            # RFC-0016 K5b: refusals, the stock-Nim slice, the cross-build cfg suites (W-58), per-build pins (W-51).
            "tsymex_0016_k5b_refusals",
            "tsymex_0016_k5b_stock",
            "tsymex_0016_k5b_pcre",
            "tsymex_0016_k5b_cfg_mm_arc",
            "tsymex_0016_k5b_cfg_mm_atomicarc",
            "tsymex_0016_k5b_cfg_usemalloc",
            "tsymex_0016_k5b_cfg_setjmp",
            "tsymex_0016_k5b_cfg_release",
            "tsymex_0016_k5b_cfg_fwrapv",
            # RFC-0016 K7a: Survivors, CapKind and the halted/continued sites.
            "tsymex_0016_k7a_survivors",
            "tsymex_0016_k7b_unsupported",
            "tsymex_0016_k10at_target",
            # RFC-0016 K7: a walk's total solver work is bounded (walkRLimit).
            "tsymex_0016_k7_splitlines_unbounded",
            "tsymex_0016_k10aa_axis",
            "tsymex_0016_k10af_float",
            "tsymex_0016_k10af_sites",
            "tsymex_0016_k10af_sites_checksoff",
            "tsymex_0016_k10c_ubsan",
            "tsymex_0016_k10c_fma",
            "tsymex_0016_k10b_round",
            "tsymex_0016_admir",
            "tsymex_0016_k10d_removals",
            "tsymex_0016_k10d_drain_checksoff",
            "tsymex_0016_rangeoff",
            "tsymex_0016_boundoff",
            "tsymex_0016_objoff",
            "tsymex_0016_fieldoff",
            "tsymex_0016_fieldhooks",
            "tsymex_0016_fieldrangeoff",
            "tsymex_0016_fieldref",
            "tsymex_0016_k7_twosearch",
            "tsymex_0016_adm1_admission",
            "tsymex_0016_k4a_table",
            "tsymex_0016_k4a_dispatch",
            "tsymex_0016_k4a_guard",
            "tsymex_0016_k4b",
            "tsymex_0016_k4b_cells",
            "tsymex_0016_k4c",
            "tsymex_0016_k4c_off",
            "tsymex_0016_k4c_cells",
            "tsymex_0016_k4c_never",
            "tsymex_0016_k4c_math",
            "tsymex_0016_w1c1a_buildprofile",
            "tsymex_0016_w1c1b_reads",
            "tsymex_0016_w1c3_splat_defect",
            # RFC-0016 W1-c2: a Defect under --panics:on crashes (W-03, INT-27).
            "tsymex_0016_panics",
            "tsymex_0016_panics_off",
            # RFC-0016 W1-a: one exception type id (W-01, W-33).
            "tsymex_0016_w1a_exn_typeid",
            "tsymex_0016_k8a1_template_except_as",
            # RFC-0016 W1-e: float32 <-> float64 conversions decline (W-04).
            "tsymex_0016_w1e_floatwidth",
            # RFC-0016 W1-p: the three probe agreements, natively (SND-07, SND-12, INT-21).
            "tsymex_0016_w1p_probes",
            # RFC-0016 K2-0: the probe batch (SND-13, CRH-06, CRH-08, CRH-09, INT-11, INT-12, INT-15, INT-22, PND-13, W-19b, W-19c, W-22, W-24).
            "tsymex_0016_k20_probes",
            "tsymex_0016_k20_probes_child",
            # RFC-0016 W1-b: local pragmas outside the allowlist decline (W-02).
            "tsymex_0016_w1b_localpragma",
            # RFC-0016 code review: zero-parameter SUTs through every entry point.
            "tsymex_0016_cr_zeroarg",
            # RFC-0016 W1-g: x in a..b / notin lower to bound comparisons (W-31).
            "tsymex_0016_w1g_inslice",
            # RFC-0016 W1-f: field defaults pinned against native; `case` with `elif` (W-20, W-21).
            "tsymex_0016_w1f_defaults_caseelif",
            # RFC-0016 W1-d1a: low(T) mod -1 and unchecked low(T) div -1 halt (W-52).
            "tsymex_0016_w1d1a_intminmod",
            "tsymex_0016_w1d1a_intminmod_checksoff",
            # RFC-0016 W1-d1b: unsigned div/mod by zero halts through haltUndefined.
            "tsymex_0016_w1d1b_udivzero",
            # RFC-0016 W1-d1c: a call summary relying on a pruned undefined side is reused only where the prune holds.
            "tsymex_0016_w1d1c_cachedprune",
            # RFC-0016 W1-d3: Path.undefined, Soundness.witnessUndefined, codec v4.
            "tsymex_0016_w1d3_undefined",
            # RFC-0016 W1-d2: checks-off signed arithmetic is undefined, not a wrap; arithChecks derives from the build (W-07).
            "tsymex_0016_checksoff",
            "tsymex_0016_w1d2_wraps",
            # RFC-0016 W1-d2c: a routine under `push overflowChecks: on` in a checks-off build raises OverflowDefect (per-routine ArithScope).
            "tsymex_0016_w1d2c_pushon",
            # RFC-0016 code review M1: symexFind's macro expansion names no deprecated field (compiled under --warningAsError:Deprecated).
            "tsymex_0016_crb_macro_deprecation",
            # RFC-0016 WA-A: closure-iterator loops and ordinal steps in a checks-off build; scope of magic bodies.
            "tsymex_0016_wa_checksoff",
            # RFC-0016 WA-A (P3): nelli imported under a check push reads the push as the build (documented, pinned).
            "tsymex_0016_wa_importpush",
            # RFC-0016 WA-B: signed div by zero (checks off) halts; 8/16-bit signed arithmetic wraps; a crash claim stays witnessUnsafe; witnessUndefined renders.
            "tsymex_0016_wa_runtime",
            "tsymex_0016_wa_runtime_checksoff",
            "tsymex_0016_wa_runtime_panics",
            # RFC-0016 CR-A: a generic exception type declines rather than being identified by its last type argument.
            "tsymex_0016_cr_generic_exn",
            # RFC-0016 S8cj: a run's Z3 context does not outlive the run (PRC-32, CI-03);
            # a verdict after Z3 5.1's mk_unique message is never a trusted sat/unsat (UPS-02, PND-10).
            "tsymex_0016_s8cj_runctx",
            "tsymex_0016_s8cj_mkunique",
            "tsymex_0016_wa_undefined_e2e",
            # RFC-0016 K1a-cells: the universe ledger (derived cells, the pin-record join, allowlists, the committed TSV).
            "tsymex_0016_universe",
            # RFC-0016 K2a: the dispatch census (case n.kind, Survivors(/Degrade( literals, bare skip(, platform arms) against its ratcheted allowlist.
            "tsymex_0016_k2a_census",
            # RFC-0016 K2c: one snippet per NimTypeKind through symexFind, and classifyType reading the named-feature rows (owned, Atomic, c_longdouble).
            "tsymex_0016_k2c_typeclass",
            # RFC-0016 K3a: the type-class and type x memory-op axes (tables, verbs), and the let-cursor x type pins through the walker.
            "tsymex_0016_k3a_typeaxes",
            "tsymex_0016_k3a_letcursor",
            "tsymex_0016_k3c_pragmaaxis",
            # RFC-0016 K3b: the field-default row of the type x memory-op axis (zeroValueForType reads it), and wasMoved/reset/move zero pins.
            "tsymex_0016_k3b_fielddefault",
            # RFC-0005 W1 (0.9.1 wiring) -- entry-point parity: the user
            # exception hierarchy, hints, diagnostics and a cached raise reach
            # symexFindAllWitnesses / symexForAll; the no-targets finding
            # carries soundness, gaps and violations. Walker 264->265.
            "tsymex_rfc0005_w1_parity",
            "tsymex_rfc0005_w3_seqiter",
            "tsymex_rfc0005_w3_opqchecks",
            "tsymex_rfc0005_w3_stmtargs",
            # RFC-0005 0.9.1 wiring slice W2 -- the replay settle and the
            # verdict cache (WA-2, WA-7, WA-8, WA-9). Walker 264->266.
            "tsymex_rfc0005_w2_settle",
            "tsymex_rfc0005_w2_settle_reexec",
            # RFC-0005 code review round 1 (0.9.1). Walker 268->269.
            "tsymex_rfc0005_r1_elif_preamble",
            "tsymex_rfc0005_r1_succ_pred",
            "tsymex_rfc0005_r1_lowertaint",
            "tsymex_rfc0005_r1_variantset",
            "tsymex_rfc0005_r1_pcrelimits",
            "tsymex_rfc0005_r1_rundependence",
            "tsymex_rfc0005_r1_findingapi",
            "tsymex_rfc0005_r1_replaychild",
            "tsymex_rfc0005_r1_replaychild_reexec",
            "tsymex_rfc0005_r1_keyflags",
            "tsymex_rfc0005_r1_keyimpl",
            "tsymex_rfc0005_r1_keymethod",
            "tsymex_rfc0005_r2_impldigest",
            "tsymex_rfc0005_r2_walktaint"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
