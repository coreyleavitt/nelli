## Phase 15 — Cluster S, cycle S10b: the `parseInt` RAISES-PATH + `$float` /
## `parseFloat` classification. S10a wired the int↔string conversions Z3 String
## theory supports directly (DIGITS-PATH only) and flagged the non-digit case
## with a `seParseIntPreE` sevHint (a deliberate pre-E1 unsoundness window). The
## exception infrastructure (E1–E6: `sxRaised`/`routeRaise`/handler-stack) is now
## shipped, so S10b CLOSES that window:
##
##   parseInt(s)  on a non-digit, non-`-`-prefixed `s`  → RAISES `ValueError`
##                (the digits sub-path keeps S10a's int value semantics; the
##                 non-digit sub-path routes `sxRaised("ValueError")` via E3's
##                 `routeRaise` and TERMINATES — no continuation).
##   parseInt("-42")                                    → sxSat, int value -42
##                (the negative-prefix fork from S10a still works under the
##                 raise fork — regression).
##   `$f`  (f: float)  /  parseFloat(s)  (s: string)    → seUnsupportedStringOp
##                (Z3 String theory has no float↔string conversion).
##
## The `seParseIntPreE` hint is NO LONGER emitted (the window is now correctly
## closed by the raises-path).
import std/[unittest, strutils]
import nelli/symex

# --- parseInt raises-path: non-digit input raises ValueError ----------------
# `s` is pinned to a non-digit string; `let n = parseInt(s)` must RAISE
# ValueError (the digits sub-path is UNSAT under `s == "abc"`).
proc parseRaises(s: string) =
  if s == "abc":
    let n = parseInt(s)
    symexTarget("unreached")

# --- parseInt negative: parseInt("-42") still sxSat with int -42 ------------
# The negative-prefix fork (S10a) under the new raise fork — regression.
proc parseNeg(s: string) =
  if s == "-42" and parseInt(s) == -42:
    symexTarget("piNeg")

# --- $float → seUnsupportedStringOp -----------------------------------------
proc dollarFloat(f: float) =
  if $f == "1.5":
    symexTarget("df")

# --- parseFloat → seUnsupportedStringOp -------------------------------------
proc pf(s: string) =
  if parseFloat(s) == 1.5:
    symexTarget("pf")

suite "symex Phase 15 S10b — parseInt raises-path + $float/parseFloat":
  test "parseInt: non-digit input RAISES ValueError (sxRaised)":
    let r = symexFind(parseRaises, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # The S10a unsoundness-window hint is gone — closed by the raises-path.
    for e in r.errors:
      check e.kind != seParseIntPreE

  test "parseInt: parseInt(\"-42\") is sxSat with int value -42 (regression)":
    let r = symexFind(parseNeg, tLabel("piNeg"))
    check r.status == sxSat
    check r.witness[0] == "-42"

  test "$float: `$f` is classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(dollarFloat, tLabel("df"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == seUnsupportedStringOp

  test "parseFloat: `parseFloat(s)` is classified seUnsupportedStringOp → sxUnknown":
    let r = symexFind(pf, tLabel("pf"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == seUnsupportedStringOp
