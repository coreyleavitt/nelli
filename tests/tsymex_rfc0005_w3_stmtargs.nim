## RFC-0005 W3 (WA-5) -- a statement-position opaque call's argument order.
##
## S8ax / S8cq read a call's arguments where Nim's C backend reads them
## (`parseOrderedArgs`: `orderOperands` with `nimArgTemps`; the pin is
## `tsymex_rfc0005_s8cq_argorder`). The expression-position opaque arm did; the
## statement-position opaque / foreign arm, and the `{.symexTransparent.}`
## fallback beside it, parsed each argument with `parseExpr` in turn, so a later
## argument's call (hoisted) ran before an earlier argument was read.
## `opq(v div b, bump(b))` with `b == 0`: Nim reads `v div b` into a temporary
## first (`b` is written by the later `var` actual) and raises
## `DivByZeroDefect`; the walk ran `bump` first and divided by 1. A clean false
## `sxSat` after the call and a clean false `sxUnsat` in `except
## DivByZeroDefect`, and the mirror image with `zap`.
##
## Found beside it: an inert `{.symexTransparent.}` call is deleted, and its
## arguments were parsed for their preamble and their values thrown away, so a
## check a value carries (`v div b`) was never forked: `trv(v div b, 0)` with
## `b == 0` was a clean false `sxUnsat` on main and the candidate. Each
## argument that is not a literal or a variable is now bound to a sink `let`,
## as `discard <expr>` is.
##
## Each row runs the routine natively beside the walk's verdict (ORC, the
## default; c and cpp agree, as S8cq records). `main` at 6cbfe8f and the
## candidate 523dffe6 answered the verdicts named "was" (the same on both).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

proc opq(a, b: int) {.symexOpaque.} = discard
proc opqWalked(a, b: int) = discard
{.emit: "/*INCLUDESECTION*/ static void w3Two(int a, int b) {(void)a; (void)b;}".}
proc opqForeign(a, b: cint) {.importc: "w3Two", nodecl.}
proc tr(c: var int; a, b: int) {.symexTransparent.} = discard
proc opqR(a, b: int): int {.symexOpaque.} = 0
proc trv(a, b: int) {.symexTransparent.} = discard
proc bump(x: var int): int = (x = 1; 0)
proc zap(x: var int): int = (x = 0; 0)

proc s0After(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  opq(v div b, bump(b))
  symexTarget("hit")

proc s0Exc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    opq(v div b, bump(b))
  except DivByZeroDefect:
    symexTarget("hit")

proc s1After(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = v
  opq(v div b, zap(b))
  symexTarget("hit")

proc s1Exc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = v
  try:
    opq(v div b, zap(b))
  except DivByZeroDefect:
    symexTarget("hit")

proc sIdxExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var a = [1, 2]
  var i = 5
  try:
    opq(a[i], bump(i))
  except IndexDefect:
    symexTarget("hit")

proc sForeignExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    opqForeign(cint(v div b), cint(bump(b)))
  except DivByZeroDefect:
    symexTarget("hit")

proc sForeignAfter(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = v
  opqForeign(cint(v div b), cint(zap(b)))
  symexTarget("hit")

proc sTrExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  var c = 0
  try:
    tr(c, v div b, bump(b))
  except DivByZeroDefect:
    symexTarget("hit")

proc sTrAfter(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  var c = 0
  tr(c, v div b, bump(b))
  symexTarget("hit")

proc sTrvExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    trv(v div b, bump(b))
  except DivByZeroDefect:
    symexTarget("hit")

proc sTrvPlainExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    trv(v div b, 0)
  except DivByZeroDefect:
    symexTarget("hit")

proc sTrvAfter(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = v
  trv(v div b, zap(b))
  symexTarget("hit")

proc sWalkedExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    opqWalked(v div b, bump(b))
  except DivByZeroDefect:
    symexTarget("hit")

proc sExprExc(v: int) =
  symexAssume(v > 0 and v < 100)
  var b = 0
  try:
    discard opqR(v div b, bump(b))
  except DivByZeroDefect:
    symexTarget("hit")

suite "W3 WA-5: a statement-position opaque call reads its arguments in order":

  test "the walker version carries the fix":
    check parseInt(symexWalkerVersion) >= 267

  test "an earlier argument is read before a later one writes it":
    check native(s0After(5)) == "DivByZeroDefect"
    decides(s0After, sxRaised)          # was a clean sxSat
    check native(s0Exc(5)) == "hit"
    decides(s0Exc, sxSat)               # was a clean sxUnsat
    check native(s1After(5)) == "hit"
    decides(s1After, sxSat)             # was a clean sxRaised
    check native(s1Exc(5)) == "ran"
    decides(s1Exc, sxUnsat)             # was a clean sxSat
    check native(sIdxExc(5)) == "hit"
    decides(sIdxExc, sxSat)

  test "a bodiless foreign callee, the same arm":
    check native(sForeignExc(5)) == "hit"
    decides(sForeignExc, sxSat)         # was sxUnsat (feOpaqueEffectHavoc)
    check native(sForeignAfter(5)) == "hit"
    let r = symexFind(sForeignAfter, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status in {sxSat, sxUnknown}

  test "the symexTransparent fallback (guard: it declines)":
    check native(sTrExc(5)) == "hit"
    let r1 = symexFind(sTrExc, tLabel("hit"))
    checkpoint show(r1.errors)
    check r1.status in {sxSat, sxUnknown}
    check native(sTrAfter(5)) == "DivByZeroDefect"
    let r2 = symexFind(sTrAfter, tLabel("hit"))
    checkpoint show(r2.errors)
    check r2.status in {sxRaised, sxUnsat, sxUnknown}

  test "an inert symexTransparent call is deleted, its arguments kept":
    check native(sTrvExc(5)) == "hit"
    decides(sTrvExc, sxSat)
    check native(sTrvPlainExc(5)) == "hit"
    decides(sTrvPlainExc, sxSat)
    check native(sTrvAfter(5)) == "hit"
    decides(sTrvAfter, sxSat)

  test "a walked callee and an expression-position opaque call (controls)":
    check native(sWalkedExc(5)) == "hit"
    decides(sWalkedExc, sxSat)
    check native(sExprExc(5)) == "hit"
    decides(sExprExc, sxSat)
