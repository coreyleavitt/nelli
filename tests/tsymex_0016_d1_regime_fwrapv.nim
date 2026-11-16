## RFC-0016 review D1 (slice S1): `arith_regime`, the one owner of the
## arithmetic regime, against the current parser and walker rules.
## `--overflowChecks:off -d:nelliFwrapv` (its `.nim.cfg`). Under vcc the build
## is refused by design (`admitBuild`) and `nelli/smt/types` is not imported
## here, so that arm asserts the refusal, as `tsymex_0016_w3z_p2_fwrapv` does.
import nelli/smt/buildprofile
when defined(vcc):
  import std/[unittest, options]
  suite "D1 S1: arith_regime (checks off, -fwrapv, vcc)":
    test "symex refuses the build by name":
      check buildSemantics.fwrapv
      let refusal = admitBuild(buildSemantics, buildProvenance)
      check refusal.isSome
      if refusal.isSome:
        check refusal.get.field == bfFwrapv
else:
  import std/unittest
  import nelli/smt/arith_regime
  import nelli/smt/definedness
  import ./d1_regime_helpers

  suite "D1 S1: arith_regime (checks off, fwrapv)":
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
      check buildSemantics.fwrapv
      check coOverflow notin buildSemantics.checks
      check buildRegime() == rgUnchecked
      check programMayWrap()
      check profile(rgUnchecked) == dpFwrapv
      check profile(rgChecked) == dpChecked
