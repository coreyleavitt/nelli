# Package

version       = "0.1.0"
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
            "tfuzzfrontier", "tfuzzprobe", "tfuzzloop", "tfuzzexec", "tfuzzexternal", "tfuzzdiff", "tfuzzdedup", "tfuzzpersist", "tfuzzschedule", "tfuzzinterop", "tfuzzpackaging", "tautolabels",
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
            "tsymex_canonicalize",
            "tsymex_typebridge_variants",
            "tsymex_phase11_walker",
            "tsymex_phase11_fielddefect",
            "tsymex_phase15_z0_carryover",
            "tsymex_phase15_z1_canary",
            "tsymex_phase15_z3_infra",
            "tsymex_phase15_z3c_classify",
            "tsymex_phase15_z4_walkctx",
            "tsymex_phase15_l1_boundary",
            "tsymex_phase15_l2_untyped_template"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
