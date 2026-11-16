## RFC-0016 review D1 (slice S1): `arith_regime`, the one owner of the
## arithmetic regime, against the current parser and walker rules.
## The default build (checks on, no `-fwrapv`).
import std/[unittest, os, strutils]
import nelli/smt/buildprofile
import nelli/smt/arith_regime
from nelli/smt/types import nil
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

  test "S6 census: arith_regime owns the regime; no old vocabulary or profile literal elsewhere":
    let root = currentSourcePath().parentDir() / ".." / "src"
    var scanned = 0
    var offenders: seq[string]
    for f in walkDirRec(root):
      if not f.endsWith(".nim"): continue
      let name = extractFilename(f)
      inc scanned
      let src = readFile(f)
      if name != "arith_regime.nim":
        for pat in ["buildWraps", "signedWrapDefined", "WalkArith",
                    "arithChecksFor", "ArithScopeProof"]:
          if pat in src: offenders.add name & ": " & pat
      if name notin ["arith_regime.nim", "definedness.nim"]:
        for lit in ["dpChecked", "dpUnchecked", "dpFwrapv"]:
          if lit in src: offenders.add name & ": " & lit
    check offenders == newSeq[string]()
    check scanned > 20

  test "S6 census: nelli/smt/types exports none of the old vocabulary":
    check not declared(types.buildWraps)
    check not declared(types.signedWrapDefined)
    check not declared(types.arithChecksFor)
    check not declared(types.WalkArith)
    check not declared(types.ArithScopeProof)
    check declared(types.ArithScope)   # its names are cache-key bytes
    check declared(types.ArithCheck)   # the walker's gate type
