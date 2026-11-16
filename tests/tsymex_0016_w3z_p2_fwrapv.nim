## RFC-0016 W3-z P2 (Part 0, pins P1's fwrapv guard). A `-d:nelliFwrapv
## --overflowChecks:off` build (its `.nim.cfg`). The opaque-call scan answers
## `ubSignedOverflow` for an overflow-capable magic in an opaque callee whose
## owner has overflow checks off, unless the build wraps: under `-fwrapv` the
## signed `+` is a defined wrap and the sat carries no such kind. The opposite
## case (no `-fwrapv`, checks off) is `tsymex_0016_w3z_p1_off`. Under vcc the
## build is refused by design and cannot import `nelli/symex`, so this arm
## asserts the refusal through `admitBuild`, as `tsymex_0016_k5a_fwrapv` and
## `tsymex_0016_k5b_cfg_fwrapv` do; the msvc row's `build:fwrapv` cell is
## allowlisted (`tests/0016-allowlist/build.txt`, `rows=msvc`).
import nelli/smt/buildprofile
when defined(vcc):
  # Neither `nelli/symex` nor `s8cu_helpers` (which imports it) compiles here:
  # the build is refused at compile time.
  import std/[unittest, strutils, options]
  suite "W3-z P2: opaque scan, -fwrapv build (vcc)":
    test "symex refuses the build by name":
      check buildSemantics.fwrapv
      let refusal = admitBuild(buildSemantics, buildProvenance)
      check refusal.isSome
      if refusal.isSome:
        check refusal.get.field == bfFwrapv
        check "-fwrapv" in refusal.get.reason
else:
  import std/[unittest, strutils]
  import nelli
  import nelli/symex
  import nelli/smt/errorkind
  import nelli/smt/definedness
  import ./s8cu_helpers

  proc oAdd(a: int64) {.symexOpaque.} =
    discard a + 1

  proc sutOpaqueTail(x: int64) =
    if x == 5: symexTarget("hit")
    oAdd(x)

  suite "W3-z P2: opaque scan, -fwrapv build":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 313

    test "the build wraps":
      check buildSemantics.fwrapv

    test "an opaque signed add under -fwrapv is a defined wrap: no ubSignedOverflow":
      let r = symexFind(sutOpaqueTail, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds

  # RFC-0016 0.10.0 review F1 (CR-7): `-fwrapv` defines the signed wrap of
  # `+ - *` and nothing else, so a signed zero divisor stays undefined (rows
  # `div/zeroDivisorSigned` and `mod/zeroDivisorSigned` under `dpFwrapv`). The
  # scan had copied the add guard onto the zero divisor and left
  # `ubSignedDivZero` out of `witnessUndefined`; it now asks the table.
  proc oDiv(a, b: int64) {.symexOpaque.} =
    discard a div b

  proc oMod(a, b: int64) {.symexOpaque.} =
    discard a mod b

  proc oAdd2(a, b: int64) {.symexOpaque.} =
    discard a + b

  proc sutDiv(x, y: int64) =
    if x == 5: symexTarget("hit")
    oDiv(x, y)

  proc sutMod(x, y: int64) =
    if x == 5: symexTarget("hit")
    oMod(x, y)

  proc sutAdd(x, y: int64) =
    if x == 5: symexTarget("hit")
    oAdd2(x, y)

  suite "CR-7: opaque signed division, -fwrapv build":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 359

    test "the build wraps and has overflow checks off":
      check buildSemantics.fwrapv
      check definedness(aoDiv, ocZeroDivisorSigned, dpFwrapv).kind == dkUndefined

    test "an opaque signed div under -fwrapv may divide by zero: never a trusted sat":
      let r = symexFind(sutDiv, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check not r.trusted
      check UbKind(ubSignedDivZero) in r.soundness.undefinedKinds

    test "an opaque signed mod under -fwrapv may divide by zero: never a trusted sat":
      let r = symexFind(sutMod, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check not r.trusted
      check UbKind(ubSignedDivZero) in r.soundness.undefinedKinds

    test "control: an opaque signed add under -fwrapv is a defined wrap":
      let r = symexFind(sutAdd, tLabel("hit"), pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check r.status == sxSat
      check UbKind(ubSignedOverflow) notin r.soundness.undefinedKinds
      check UbKind(ubSignedDivZero) notin r.soundness.undefinedKinds

  # RFC-0016 review D1 (slice S1): `arith_regime` against the current parser
  # and walker rules under this build (checks off, -fwrapv). Folded here so
  # the vcc arm above stays this build's one platform site (K2a census).
  import nelli/smt/arith_regime
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
    test "D1-F2 + F-3: every routine body stamps its own regime; checking and wrapping are one regime":
      checkTotalStamp()
    test "the compiled build":
      check buildSemantics.fwrapv
      check coOverflow notin buildSemantics.checks
      check buildRegime() == rgUnchecked
      check programMayWrap()
      check profile(rgUnchecked) == dpFwrapv
      check profile(rgChecked) == dpChecked

  # RFC-0016 review R2-1: a lambda's alias bodies (`lambdaAliasBodies`, walked
  # when one call passes one location to two `var` formals) are the lambda's
  # own, stamped with its regime. Here the lambda is compiled pushed
  # `overflowChecks: on` (it raises) and called from a routine of the build's
  # wrapping regime: the aliased call took the caller's, wrapped, and reached
  # the label the native run never does.
  {.push overflowChecks: on.}
  proc mkAdder(): proc (a, b: var int) =
    result = proc (a, b: var int) = a = a + b
  {.pop.}

  proc sutAdderPlain(k: int) =
    var x = k
    var y = k
    let f = mkAdder()
    f(x, y)
    if k > 0 and x < 0: symexTarget("hit")

  proc sutAdderAliased(k: int) =
    var x = k
    let f = mkAdder()
    f(x, x)
    if k > 0 and x < 0: symexTarget("hit")

  suite "R2-1: lambda alias bodies take the lambda's regime (-fwrapv build)":
    test "native: the pushed-on lambda raises on both calls":
      check native(sutAdderPlain(high(int))) == "OverflowDefect"
      check native(sutAdderAliased(high(int))) == "OverflowDefect"
    test "the plain call does not reach the label":
      let r = symexFind(sutAdderPlain, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status != sxSat
    test "walker version floor (R2-1: alias bodies are stamped)":
      check parseInt(symexWalkerVersion) >= 363
    test "the aliased call answers as the plain call does":
      let p = symexFind(sutAdderPlain, tLabel("hit"))
      let r = symexFind(sutAdderAliased, tLabel("hit"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == p.status
      check r.status != sxSat
