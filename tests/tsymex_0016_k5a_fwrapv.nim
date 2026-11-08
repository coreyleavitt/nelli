## RFC-0016 K5a (section 8.3). A `-d:nelliFwrapv --overflowChecks:off` build
## (its `.nim.cfg`). `buildprofile.nim` turns the define into
## `{.passC: "-fwrapv".}`, so the C compiler defines signed `+`, `-`, `*` and
## negation as a wrap at every width. The walker then models the wrap for 32
## and 64 bit as it already does for 8 and 16: the overflow side is no
## `ubSignedOverflow` halt, and the verdict is trusted and agrees with the
## native run. `low(T) div -1` and `mod -1` stay undefined (`-fwrapv` does not
## define them), so they still halt.
when defined(vcc):
  # Under vcc the build is refused by design: cl.exe has no `-fwrapv`, so
  # `-d:nelliFwrapv` would claim a wrap the C compiler does not give, and
  # `nelli/symex` stops at its compile-time admission. This arm cannot import
  # it; it asserts the refusal through `admitBuild`, the function `symex.nim`
  # runs, against this build's own profile.
  import std/[unittest, strutils, options]
  import nelli/smt/buildprofile

  suite "K5a: -d:nelliFwrapv build (vcc)":
    test "the build declares the wrap":
      check buildSemantics.fwrapv
      check buildProvenance.ccFamily == ccVcc

    test "symex refuses it by name":
      let refusal = admitBuild(buildSemantics, buildProvenance)
      check refusal.isSome
      if refusal.isSome:
        check refusal.get.field == bfFwrapv
        check "vcc" in refusal.get.reason
        check "-fwrapv" in refusal.get.reason
        check "[field: fwrapv]" in refusalMessage(refusal.get)
else:
  import std/[unittest, strutils]
  import nelli
  import nelli/symex
  import ./s8cu_helpers

  proc sutWrap32(v: int32) =
    if v + 1 < v: symexTarget("hit")

  proc sutWrap64(v: int) =
    if v + 1 < v: symexTarget("hit")

  proc sutSubWrap32(v: int32) =
    if v - 1 > v: symexTarget("hit")

  proc sutMulWrap32(v: int32) =
    if v * 2 < 0 and v > 0: symexTarget("hit")

  proc sutNegWrap32(v: int32) =
    if v < 0 and -v < 0: symexTarget("hit")

  proc sutDivMinusOne32(v: int32) =
    ## Only `low(int32)` reaches the label, and `low(int32) div -1` is undefined
    ## even under `-fwrapv`.
    if v < 0 and v div -1 < 0: symexTarget("hit")

  suite "K5a: -d:nelliFwrapv build":
    test "version floor":
      check parseInt(symexWalkerVersion) >= 288

    test "the build declares the wrap and produces the flag":
      check buildSemantics.fwrapv
      check coOverflow notin buildSemantics.checks
      check buildWraps()

    test "native: -fwrapv defines the 32 and 64 bit wrap":
      check "hit" in nativeRun(sutWrap32(high(int32))).hits
      check "hit" in nativeRun(sutWrap64(high(int))).hits
      check "hit" in nativeRun(sutSubWrap32(low(int32))).hits
      check "hit" in nativeRun(sutNegWrap32(low(int32))).hits

    test "int32 add: the overflow is a trusted wrap, not a halt":
      let r = pinExact(sutWrap32, cellKey(axDefinedness, "add/signed32/fwrapv"),
                       domain = sampled([high(int32), 0'i32, 5'i32]))
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(ubSignedOverflow)

    test "int64 add":
      let r = pinExact(sutWrap64, cellKey(axDefinedness, "add/signed64/fwrapv"),
                       domain = sampled([high(int), 0, 5]))
      check r.status == sxSat
      check r.trusted
      check not r.errors.named(ubSignedOverflow)

    test "int32 sub":
      let r = pinExact(sutSubWrap32, cellKey(axDefinedness, "sub/signed32/fwrapv"),
                       domain = sampled([low(int32), 0'i32, 5'i32]))
      check r.status == sxSat
      check r.trusted

    test "int32 negation":
      let r = pinExact(sutNegWrap32, cellKey(axDefinedness, "neg/signed32/fwrapv"),
                       domain = sampled([low(int32), -5'i32, 5'i32]))
      check r.status == sxSat
      check r.trusted

    test "low(T) div -1 stays undefined":
      pinDecline(sutDivMinusOne32, cellKey(axDefinedness, "div/signed32/fwrapv"),
                 ubSignedOverflow)
