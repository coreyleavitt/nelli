## RFC-0005 W3 (WA-4) -- an inert opaque callee's check options.
##
## An inert opaque call forks each `Defect` its body may raise
## (`opaqueDefectTypes`, S8be). The scan assumed the default checks, under
## which float arithmetic raises nothing. A callee compiled under
## `{.push nanChecks: on.}` (or `infChecks`, `floatChecks`) raises
## `FloatInvalidOpDefect` (`FloatOverflowDefect`) out of `+ - * /`: the walk
## forked neither, and a target in `except FloatingPointDefect:` was a clean
## false `sxUnsat`. The scan now reads each routine's options (`routineChecks`,
## as the walked routines do), the opaque callee's and every routine it calls.
##
## A callee compiled with a check OFF forks a `Defect` it cannot raise; the
## fork carries `feOpaqueEffectHavoc`, so a hit through it is replayed and the
## replay refutes it (`sxUnknown`), and an `sxUnsat` stands. No false verdict:
## the rows below pin it. A bodiless foreign callee is not Nim code and has no
## check options.
##
## Each row runs the routine natively beside the walk's verdict. `main` at
## 6cbfe8f answered `sxUnsat` for every row (the check-off rows too); the
## candidate 523dffe6 answered `sxUnsat` for the float rows and `sxUnknown`
## (`feOpaqueEffectHavoc`) for the check-off rows.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

{.push nanChecks: on.}
proc opqNan(x: float) {.symexOpaque.} =
  var y = x
  y = y - y
{.pop.}
{.push infChecks: on.}
proc opqInf(x: float) {.symexOpaque.} =
  var y = x
  y = y * y
{.pop.}
{.push floatChecks: on.}
proc opqFc(x: float) {.symexOpaque.} =
  var y = x
  y = y * y
{.pop.}
{.push nanChecks: on.}
proc helperNan(x: float): float = x - x
{.pop.}
proc opqViaHelper(x: float) {.symexOpaque.} =
  discard helperNan(x)
proc opqClean(x: float) {.symexOpaque.} =
  var y = x
  y = y - y
{.push boundChecks: off.}
proc opqIdxOff(a: int) {.symexOpaque.} =
  var s = [1, 2, 3]
  var j = a
  if j > 3: j = 3
  discard s[j]
{.pop.}
{.push overflowChecks: off.}
proc opqOvfOff(a: int) {.symexOpaque.} =
  discard a + 1
{.pop.}

proc fNan(x: float) =
  symexAssume(x > 1e308)
  try:
    opqNan(x * 10.0)
  except FloatInvalidOpDefect:
    symexTarget("hit")

proc fNanFp(x: float) =
  symexAssume(x > 1e308)
  try:
    opqNan(x * 10.0)
  except FloatingPointDefect:
    symexTarget("hit")

proc fNanFinite(x: float) =
  # A finite operand: `x - x` is 0, no NaN.
  symexAssume(x > 1.0 and x < 2.0)
  try:
    opqNan(x)
  except FloatingPointDefect:
    symexTarget("hit")

proc fInf(x: float) =
  symexAssume(x > 1e200)
  try:
    opqInf(x)
  except FloatOverflowDefect:
    symexTarget("hit")

proc fFc(x: float) =
  symexAssume(x > 1e200)
  try:
    opqFc(x)
  except FloatingPointDefect:
    symexTarget("hit")

proc fHelper(x: float) =
  symexAssume(x > 1e308)
  try:
    opqViaHelper(x * 10.0)
  except FloatingPointDefect:
    symexTarget("hit")

proc fClean(x: float) =
  symexAssume(x > 1e308)
  try:
    opqClean(x * 10.0)
  except FloatingPointDefect:
    symexTarget("hit")

proc fIdxOff(v: int) =
  symexAssume(v == 7)
  try:
    opqIdxOff(v)
  except IndexDefect:
    symexTarget("hit")

proc fOvfOff(v: int) =
  symexAssume(v == high(int))
  try:
    opqOvfOff(v)
  except OverflowDefect:
    symexTarget("hit")

suite "W3 WA-4: an opaque callee's check options":

  test "the walker version carries the fix":
    check parseInt(symexWalkerVersion) >= 267

  test "nanChecks on: FloatInvalidOpDefect is forked":
    check native(fNan(1.7e308)) == "hit"
    decides(fNan, sxSat)                # was a clean sxUnsat
    check native(fNanFp(1.7e308)) == "hit"
    decides(fNanFp, sxSat)              # was a clean sxUnsat

  test "infChecks and floatChecks on: FloatOverflowDefect is forked":
    check native(fInf(1e300)) == "hit"
    decides(fInf, sxSat)                # was a clean sxUnsat
    check native(fFc(1e300)) == "hit"
    decides(fFc, sxSat)                 # was a clean sxUnsat

  test "a routine the opaque callee calls has options of its own":
    check native(fHelper(1.7e308)) == "hit"
    decides(fHelper, sxSat)             # was a clean sxUnsat

  test "a fork the operands cannot take is refuted, not reported":
    check native(fNanFinite(1.5)) == "ran"
    let r = symexFind(fNanFinite, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status in {sxUnsat, sxUnknown}

  test "the default float checks raise nothing (control)":
    check native(fClean(1.7e308)) == "ran"
    decides(fClean, sxUnsat)

  test "a check off forks a Defect the replay refutes (guard)":
    check native(fIdxOff(7)) == "ran"
    let r1 = symexFind(fIdxOff, tLabel("hit"))
    checkpoint show(r1.errors)
    check r1.status in {sxUnsat, sxUnknown}
    check native(fOvfOff(high(int))) == "ran"
    let r2 = symexFind(fOvfOff, tLabel("hit"))
    checkpoint show(r2.errors)
    check r2.status in {sxUnsat, sxUnknown}
