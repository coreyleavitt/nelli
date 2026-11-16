## RFC-0016 review D1 (slice S1): `arith_regime`, the one owner of the
## arithmetic regime, against the current parser and walker rules.
## `--overflowChecks:off` (its `.nim.cfg`).
import std/unittest
import nelli/smt/buildprofile
import nelli/smt/arith_regime
import ./d1_regime_helpers

suite "D1 S1: arith_regime (checks off)":
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
  test "D1-F2 + F-3: every routine body stamps its own regime; checking and wrapping are one regime":
    checkTotalStamp()
  test "the compiled build":
    check not buildSemantics.fwrapv
    check coOverflow notin buildSemantics.checks
    check buildRegime() == rgUnchecked
    check programMayWrap()
