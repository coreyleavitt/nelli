import std/unittest
import z3

# Phase 15 — Z1 nim-z3 v2.0.0 canary (reconciled; see
# docs/symex/RFC-phase15-reconciliation.md §F / Cluster Z).
#
# Smoke test confirming the v2.0.0 pin loaded and the Z3String sort is intact
# under it. Reconciled from the RFC's assumed `sortOf[Z3String]()`/`Z3StringSort`
# to the real v2.0.0 API: `Z3String = Z3Seq[Z3Char]`, `sortOf(Z3String, ctx)`.
# Imports none of the 8 v1 renamed symbols (toInt/strToInt/intToStr/mkNaN/mkInf/
# mkZero/toFp/mkRegexAll); their absence in nelli is grep-verified at commit.
#
# Requires the prebuilt toolchain (ghcr.io/coreyleavitt/nim:latest, Nim 2.2.10);
# nim-z3 v2.0.0 does not compile under Nim <= 2.2.4 (funcdecl tuple-type parser
# bug). See RFC-phase15-reconciliation.md §F.

suite "symex Phase 15 — Z1 nim-z3 v2.0.0 canary":
  test "z3 v2 canary: Z3String sort constructs and stringifies as String":
    let ctx = newContext()
    let strSort = sortOf(Z3String, ctx)
    check ($Z3_sort_to_string(ctx.raw, strSort)) == "String"
