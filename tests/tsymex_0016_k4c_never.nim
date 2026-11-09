## RFC-0016 K4c (STY-06): the two `never` rows that had no declining site.
##
## `unicode.toLower/fullCaseFold` and `typedthreads.createThread/concurrency`
## are routines the walker must not enter: a symbolic `toLower(Rune)` walked
## its table binary search and never ended (a K7 violation: every walk ends in
## a verdict or a typed cap), and `createThread` is a walker fault (W-19b). The
## call is declined by the row's name, before its body is registered.
import std/[unittest, unicode, options]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import ./s8cu_helpers

proc sToLower(a: int) =
  if toLower(Rune(a)) == Rune(0x61) and a == 0x41: symexTarget("hit")
proc sToLowerStr(a: int) =
  if toLower($Rune(a)) == "a" and a == 0x41: symexTarget("hit")

var gT: int
var thr: Thread[int]
proc thrBody(v: int) {.thread.} = gT = v
proc sThread(v: int) =
  gT = 0
  createThread(thr, thrBody, 7)
  joinThread(thr)
  if gT == 7 and v == 1: symexTarget("hit")

suite "K4c STY-06: a never row with a declining site":
  test "stdlib:unicode.toLower/fullCaseFold (Rune)":
    let c = cellKey(axStdlibBody, "unicode.toLower/fullCaseFold")
    pinDecline(sToLower, c, feUnsupportedOp, needle = render(c))
  test "stdlib:unicode.toLower/fullCaseFold (string)":
    let c = cellKey(axStdlibBody, "unicode.toLower/fullCaseFold")
    pinDecline(sToLowerStr, c, seUnsupportedStringOp, needle = render(c))
  test "stdlib:typedthreads.createThread/concurrency":
    let c = cellKey(axStdlibBody, "typedthreads.createThread/concurrency")
    pinDecline(sThread, c, feUnsupportedOp, needle = render(c))
