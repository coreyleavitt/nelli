## RFC-0016 0.10.0 review F1 (fix slice CR-7). A `-d:nelliFwrapv
## --overflowChecks:off` build (its `.nim.cfg`). `-fwrapv` defines the signed
## wrap of `+ - *` and nothing else: a signed zero divisor stays undefined
## (row `div/zeroDivisorSigned` and `mod/zeroDivisorSigned` under `dpFwrapv`
## is `ubSignedDivZero`). The opaque-call scan used to copy the signed-add
## guard (`not fwrapv`) onto the zero divisor, so an opaque `a div b` under
## this build answered a trusted sat where the native run raises SIGFPE. The
## scan now asks the definedness table under the build's profile. The control
## (an opaque signed add stays a defined wrap) is the one
## `tsymex_0016_w3z_p2_fwrapv` pins. Under vcc the build is refused by design
## and cannot import `nelli/symex`, so this arm asserts the refusal.
import nelli/smt/buildprofile
when defined(vcc):
  import std/[unittest, strutils, options]
  suite "CR-7: opaque signed division, -fwrapv build (vcc)":
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

  proc oDiv(a, b: int64) {.symexOpaque.} =
    discard a div b

  proc oMod(a, b: int64) {.symexOpaque.} =
    discard a mod b

  proc oAdd(a, b: int64) {.symexOpaque.} =
    discard a + b

  proc sutDiv(x, y: int64) =
    if x == 5: symexTarget("hit")
    oDiv(x, y)

  proc sutMod(x, y: int64) =
    if x == 5: symexTarget("hit")
    oMod(x, y)

  proc sutAdd(x, y: int64) =
    if x == 5: symexTarget("hit")
    oAdd(x, y)

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
