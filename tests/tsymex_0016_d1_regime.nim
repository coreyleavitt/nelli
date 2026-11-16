## RFC-0016 review D1 (slice S1): `arith_regime`, the one owner of the
## arithmetic regime, against the current parser and walker rules.
## The default build (checks on, no `-fwrapv`).
import std/[unittest, os, strutils]
import nelli/smt/buildprofile
import nelli/smt/arith_regime
import ./d1_regime_helpers

suite "D1 S1: arith_regime (default build)":
  test "the truth table: readable x overflowOn x deviates x row x inherit, all four builds":
    checkTruthTable()
  test "literal rows, each citing the line it encodes":
    checkLiterals()
  test "profile, wrapDefined, ownerProfile against defProfile and signedWrapDefined":
    checkProfiles()
  test "frames: the walk rule, the parse rule, emits, the iterator test":
    checkFrames()
  test "stampFor is const-pure":
    checkConstPure()
  test "the cache-key bytes of a stamped block":
    checkKeyBytes()
  test "F-2 census: every overflow-exercising stdlib row calls only magics":
    checkOverflowRowCensus()
  test "the compiled build":
    check not buildSemantics.fwrapv
    check coOverflow in buildSemantics.checks
    check buildRegime() == rgChecked
    check not programMayWrap()

  test "S3 census: the parser names no build predicate and no profile literal":
    let src = readFile(currentSourcePath().parentDir() / ".." / "src" /
                       "nelli" / "smt" / "dsl_parser.nim")
    check "buildWraps(" notin src
    for lit in ["dpChecked", "dpUnchecked", "dpFwrapv"]:
      check lit notin src
