## RFC-0005 S8cu -- on the command line: overflowChecks off (`--overflowChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_cl_over")

## RFC-0016 W1-d2 (W-07). This build is checks-off, so the default settings
## follow it (`acOverflow` out) and there is no routine-level decline to make:
## the build is the program. A signed overflow is undefined, not a wrap, so the
## rows that decided a wrap now halt; an explicit setting that models what the
## build does not do taints `feCheckOption`.
const clSettings = SymexSettings(arithChecks: {acDivByZero, acRange})

suite "S8cu: --overflowChecks:off":

  test "the settings follow the build, and the signed overflow halts":
    ## Rule (a): was a feOverflowCheckOption decline under settings that
    ## modelled the check; the settings now agree with the build, and the
    ## overflowing `+` is the ubSignedOverflow halt.
    check native(clOver(high(int))) == "hit"
    check not arithChecksDisagree(defaultSymexSettings())
    pinDecline(clOver, declKey, ubSignedOverflow)
    check not symexFind(clOver, tLabel("hit")).errors.named(feOverflowCheckOption)

  test "settings that model the wrap disagree with the build and are not trusted":
    ## Rule (a): was a trusted sxSat/sxRaised/sxSat (S8w). The explicit
    ## arithChecks differs from this build's ({acRange}).
    let r = symexFind(clOver, tLabel("hit"), clSettings)
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(feCheckOption)
    let f = symexFind(clField, tLabel("hit"), clSettings)
    checkpoint show(f.errors)
    check not f.trusted
    check f.errors.named(feCheckOption)
    let p = symexFind(clPure, tLabel("hit"), clSettings)
    checkpoint show(p.errors)
    check not p.trusted
    check p.errors.named(feCheckOption)

  test "no routine declines for the build's own checks: one that never meets the check decides":
    ## Rule (c), premise changed: the old "per routine" decline existed because
    ## the settings modelled checks the build did not have. They now agree with
    ## the build, so a routine that never reaches the check is decided and
    ## carries no marker (W1-d2a's `withCheckDeclines` emits only when not
    ## `buildWraps()`; not a src defect).
    check native(clField(4)) == "FieldDefect"
    decides(clField, sxRaised)
    check native(clPure(7)) == "hit"
    decides(clPure, sxSat)
    check not symexFind(clField, tLabel("hit")).errors.named(feOverflowCheckOption)
    check not symexFind(clPure, tLabel("hit")).errors.named(feOverflowCheckOption)

  test "a routine under `push overflowChecks: on` in a checks-off build raises OverflowDefect":
    ## RFC-0016 W1-d2c. Natively it raises OverflowDefect, and so does the
    ## walker: checked-ness is per routine (`ArithScope`), so the pushed-on
    ## routine is modelled as a checked build models it, an exact sxRaised
    ## where W1-d2 answered the build's ubSignedOverflow halt (sxUnknown).
    check native(clOverOn(high(int))) == "OverflowDefect"
    let r = pinExact(clOverOn, cellKey(axDefinedness, "add/signed/clPushOn"))
    check r.status == sxRaised
    check r.trusted
