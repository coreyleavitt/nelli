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
