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
            "tcovguided", "treservedlabel", "tfuzzir", "tautolabels",
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
            "tsymex_rectify_mutation", "tsymex_rectify_nested_arrays"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
