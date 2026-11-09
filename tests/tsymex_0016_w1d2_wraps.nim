## RFC-0016 W1-d2 (W-07), the push route, on a checks-ON build (the
## default). (The settings route, an explicit `arithChecks` that disagreed
## with the build, went with the setting in K10d.)
##
## Native, probed on the pinned toolchain (c and cpp identical, x86-64 Linux,
## default optimisation; MSVC differs, see the native test): under `{.push overflowChecks: off.}`,
## `if v + 1 > v: discard else: symexTarget("hit")` never reaches "hit" at
## `high(int)` (gcc folds the comparison: signed overflow is undefined),
## with the operand through a `noinline` identity or not; `id(high(int)) + 1`
## computes `low(int)`. A walker `sxSat` at `high(int)` is a witness the
## binary does not reach, and nothing in the arithmetic knows which routine
## it sits in, so a pushed-off routine declines on every setting.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

{.push overflowChecks: off.}
proc sutPushed(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")

proc sutPushedViaId(v: int) =
  let w = id(v)
  if w + 1 > w: discard
  else: symexTarget("hit")
{.pop.}

proc sutPlain(x: int) =
  if x == 7: symexTarget("hit")

suite "W1-d2 push route and explicit settings":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 282

  test "the build is checks-on":
    check coOverflow in buildSemantics.checks
    check not buildWraps()
    check arithChecksFor(buildSemantics) == {acOverflow, acDivByZero, acRange}

  test "native: a pushed-off v + 1 > v is compiler-dependent (undefined)":
    # gcc and clang fold the comparison and never reach "hit"; MSVC wraps
    # and does (fuzzer-msvc, 2026-11-07). Either is a legal reading of
    # undefined behaviour, which is why the walker declines.
    when defined(vcc):
      check "hit" in nativeRun(sutPushed(high(int))).hits
      check "hit" in nativeRun(sutPushedViaId(high(int))).hits
    else:
      check "hit" notin nativeRun(sutPushed(high(int))).hits
      check "hit" notin nativeRun(sutPushedViaId(high(int))).hits

  test "push: the marker declines, the verdict is not a trusted sxSat":
    pinDecline(sutPushed, cellKey(axDefinedness, "add/signed/pushOff"),
               feOverflowCheckOption)

  test "push: through a noinline identity too":
    pinDecline(sutPushedViaId, cellKey(axDefinedness, "add/signed/pushOffId"),
               feOverflowCheckOption)

  test "push: an explicit opt-out no longer passes the marker":
    let r = symexFind(sutPushed, tLabel("hit"), defaultSymexSettings())
    check not r.trusted
    check r.status != sxSat
    check r.errors.named(feOverflowCheckOption)

  test "the default settings agree with the build":
    let r = pinExact(sutPlain, cellKey(axDefinedness, "arithChecks/default"))
    check r.status == sxSat
    check not r.errors.named(feCheckOption)
