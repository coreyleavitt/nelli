## RFC-0016 W1-d2 (W-07), the whole-build route. This file builds with
## `--overflowChecks:off` (its `.nim.cfg`): signed `+`, `-` and `*` are
## UNCHECKED, which in C is undefined on overflow, not a wrap.
##
## Native, probed on the pinned toolchain (c and cpp identical, x86-64 Linux,
## default optimisation), for `if v + 1 > v: "miss" else: "hit"` at
## `high(int)`, with the operand through a `noinline` identity and without it,
## both under `{.push overflowChecks: off.}` and under `--overflowChecks:off`:
##   every variant answers "miss": gcc folds `v + 1 > v` to true (signed
##   overflow is undefined), so the label is never reached, while
##   `id(high(int)) + 1` itself evaluates to `low(int)` (two's complement).
## The old walker modelled the wrap and answered `sxSat` at `high(int)`, a
## witness the binary does not reach. The overflow is undefined, so the
## walker answers neither way: the overflow side halts (`ubSignedOverflow`).
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutAddCmp(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")

proc sutSubCmp(v: int) =
  if v - 1 < v: discard
  else: symexTarget("hit")

proc sutMulCmp(v: int) =
  if v * 2 > v or v <= 0: discard
  else: symexTarget("hit")

proc sutDefined(x: int) =
  ## The overflow side is ruled out by the guard: pruned, nothing recorded.
  if x > 0 and x < 100:
    if x + 1 == 5: symexTarget("hit")

proc sutDefinedUnsat(x: int) =
  if x > 0 and x < 100:
    if x + 1 == 1000: symexTarget("hit")

proc sutUnsigned(x: uint64) =
  ## Unsigned arithmetic is defined wrap: exact.
  if x + 1 == 0'u64: symexTarget("hit")

proc id(x: int): int {.noinline.} = x

proc nativeAddCmpIdentity(v: int): bool =
  let w = id(v)
  w + 1 > w

suite "W1-d2 checks-off build":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 282

  test "the build is checks-off and the default settings follow it":
    check coOverflow notin buildSemantics.checks
    check buildWraps()
    check acOverflow notin defaultSymexSettings().arithChecks
    check acDivByZero notin defaultSymexSettings().arithChecks
    check defaultSymexSettings().arithChecks == arithChecksFor(buildSemantics)
    check not arithChecksDisagree(defaultSymexSettings())
    check validateSymexSettings(defaultSymexSettings()).len == 0

  test "native: v + 1 > v at high(int) never reaches the else branch":
    let n = nativeRun(sutAddCmp(high(int)))
    check "hit" notin n.hits
    check n.raised == ""

  test "add: the overflow side halts, the verdict is not a trusted sxSat":
    pinDecline(sutAddCmp, cellKey(axDefinedness, "add/signed/checksOff"),
               ubSignedOverflow)

  test "sub: the same":
    pinDecline(sutSubCmp, cellKey(axDefinedness, "sub/signed/checksOff"),
               ubSignedOverflow)

  test "mul: the same":
    pinDecline(sutMulCmp, cellKey(axDefinedness, "mul/signed/checksOff"),
               ubSignedOverflow)

  test "the derived default does not taint":
    let r = symexFind(sutAddCmp, tLabel("hit"))
    check r.errors.named(ubSignedOverflow)
    check not r.errors.named(feCheckOption)

  test "the defined side is exact":
    let r = pinExact(sutDefined, cellKey(axDefinedness, "add/signed/checksOff/defined"))
    check r.status == sxSat
    check not r.errors.named(ubSignedOverflow)
    let u = pinExact(sutDefinedUnsat,
                     cellKey(axDefinedness, "add/signed/checksOff/definedUnsat"))
    check u.status == sxUnsat

  test "unsigned arithmetic stays an exact wrap":
    let r = pinExact(sutUnsigned, cellKey(axDefinedness, "add/unsigned/checksOff"),
                     domain = sampled([0'u64, 1, high(uint64) - 1, high(uint64)]))
    check r.status == sxSat
    check not r.errors.named(ubSignedOverflow)
