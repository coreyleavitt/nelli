## RFC-0016 int6-o: `tsymex_0016_int6o_overflow`'s overflow-off region under
## `-d:nelliFwrapv` (this file's `.nim.cfg`), overflow checks left ON in the
## build. Native, probed on the pinned toolchain (c and cpp identical, x86-64
## Linux, `--passC:-fwrapv`): inside `{.push overflowChecks: off.}` the signed
## `+` is a defined wrap, so `v + 1 > v` is false at `high(int)` and the label
## is reached; outside it the build's checks hold (`OverflowDefect`), and
## system's `*=` is the build's inside it too. The walker answers the region
## exactly: the witness is `high(int)`, judged against the native binary.
##
## The suite keys on the product's own admission of the build, never on the C
## compiler: a build `nelli/symex` refuses (under vcc, which has no `-fwrapv`)
## cannot import it, so that arm asserts the refusal through `admitBuild`, as
## `tsymex_0016_k5b_cfg_fwrapv` does.
import std/options
import nelli/smt/buildprofile
const admission = admitBuild(buildSemantics, buildProvenance)
when admission.isSome:
  import std/[unittest, strutils]
  suite "int6-o: overflow-off region, -fwrapv build (refused build)":
    test "symex refuses the build by name":
      check buildSemantics.fwrapv
      check admission.get.field == bfFwrapv
      check "-fwrapv" in admission.get.reason
else:
  import std/[unittest, strutils]
  import nelli/smt/arith_regime
  import nelli
  import nelli/symex
  import ./s8cu_helpers

  proc checkedAdd(v: int): int = v + 1

  {.push overflowChecks: off.}
  proc sutWrapCmp(v: int) =
    if v + 1 > v: discard
    else: symexTarget("hit")

  proc sutWrapValue(v: int) =
    if v > 0 and v + 1 == low(int): symexTarget("hit")

  proc sutCallsChecked(v: int) =
    if checkedAdd(v) == 7: symexTarget("hit")

  proc sutMulEq(v: int) =
    var x = v
    x *= 2
    if x == 14: symexTarget("hit")

  proc offAdd(v: int): int = v + 1
  {.pop.}

  proc sutCallerAfter(v: int) =
    let w = offAdd(v)
    if w - 1 == 3: symexTarget("hit")

  suite "int6-o: an overflow-off region in a checked -fwrapv build":
    test "the build checks overflow and wraps":
      check coOverflow in buildSemantics.checks
      check buildRegime() == rgChecked
      check buildSemantics.fwrapv

    test "native: v + 1 > v is false at high(int) under -fwrapv":
      check "hit" in nativeRun(sutWrapCmp(high(int))).hits

    test "the region's signed wrap is exact":
      let r = pinExact(sutWrapCmp, cellKey(axDefinedness, "add/signed/pushOff/fwrapv"))
      check r.status == sxSat
      check r.trusted
      let v = pinExact(sutWrapValue,
                       cellKey(axDefinedness, "add/signed/pushOff/fwrapvValue"))
      check v.status == sxSat

    test "a callee declared outside the push keeps its checks":
      let x = pinFind(sutCallsChecked, tRaisedExn("OverflowDefect"))
      checkpoint show(x.errors)
      check x.status == sxRaised

    test "the checked caller's arithmetic after the call still raises":
      check native(sutCallerAfter(high(int))) == "OverflowDefect"
      let x = pinFind(sutCallerAfter, tRaisedExn("OverflowDefect"))
      checkpoint show(x.errors)
      check x.status == sxRaised

    test "system's *= is the build's: it raises inside the push":
      check native(sutMulEq(high(int))) == "OverflowDefect"
      let x = pinFind(sutMulEq, tRaisedExn("OverflowDefect"))
      checkpoint show(x.errors)
      check x.status == sxRaised

  suite "int6-o fwrapv: walker version":
    test "walker version floor >= 467":
      check parseInt(symexWalkerVersion) >= 467
