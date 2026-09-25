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
            "tsymex_rfc0005_s2_replay"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
