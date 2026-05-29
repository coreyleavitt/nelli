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
            "tlinearisable", "tjsonschema",
            "tlaws", "tmetamorphic", "tparallelcheck", "tpipeline"]:
    exec "nim c -r --threads:on --hints:off --path:src tests/" & f & ".nim"
