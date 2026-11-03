## RFC-0005 S8cu -- on the command line: overflowChecks off (`--overflowChecks:off`).
##
## Each row runs the routine natively on this build beside the walker's verdict.
import std/[unittest, sets]
import nelli
import nelli/symex
import ./s8cu_fix_cl
import ./s8cu_helpers

suite "S8cu: --overflowChecks:off":

  test "declines where the settings model the check":
    check native(clOver(high(int))) == "hit"
    declines(clOver, feOverflowCheckOption)

  test "decides where the settings model the wrap: S8w (control)":
    let r = symexFind(clOver, tLabel("hit"), SymexSettings(arithChecks: {acDivByZero, acRange}))
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check native(clOver(r.witness[0])) == "hit"
    let f = symexFind(clField, tLabel("hit"), SymexSettings(arithChecks: {acDivByZero, acRange}))
    checkpoint show(f.errors)
    check f.status == sxRaised
    check native(clField(4)) == "FieldDefect"
    let p = symexFind(clPure, tLabel("hit"), SymexSettings(arithChecks: {acDivByZero, acRange}))
    checkpoint show(p.errors)
    check p.status == sxSat
    check native(clPure(7)) == "hit"

  test "the rule is per routine: one that never meets the check declines too":
    check native(clField(4)) == "FieldDefect"
    declines(clField, feOverflowCheckOption)
    check native(clPure(7)) == "hit"
    declines(clPure, feOverflowCheckOption)

  test "a routine under `push overflowChecks: on` has it back (control)":
    check native(clOverOn(high(int))) == "OverflowDefect"
    decides(clOverOn, sxRaised)
