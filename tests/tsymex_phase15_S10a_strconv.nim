## Phase 15 — Cluster S, cycle S10a: `$int` / `parseInt` digits-path (pre-E1).
##
## Wires the int↔string conversion ops Z3 String theory supports directly,
## covering ONLY the digits-path (the raises-path needs E1 and is split into
## S10b, deferred):
##   `$n`  (n: int)   → Z3 `(str.from-int n)`  (`Z3_mk_int_to_str`, nim-z3 `toStr`)
##   parseInt(s)      → Z3 `(str.to-int s)`    (`Z3_mk_str_to_int`, nim-z3 `toInt`)
##                      with a `toInt(s) >= 0` digits soundness gate + a
##                      leading-`-` negative fork (an ITE over the int result).
##
## The non-digit input case (where S10a flagged a `seParseIntPreE` sevHint as a
## pre-E1 unsoundness window) is now CLOSED by S10b: a non-digit, non-`-`-prefixed
## `parseInt` RAISES `ValueError` (the digits sub-path is constrained out). The
## 4th case below therefore asserts `sxRaised{ValueError}` (the S10b behavior) —
## the `seParseIntPreE` hint is no longer emitted.
##
## Per the S7b finding, bool-returning string helper procs do NOT inline under
## symex, so every condition is inlined directly in the SUT body.
import std/[unittest, strutils]
import proptest/symex

# --- `$n`: a SUT where `$n == "42"` (n: int) pins n to 42 -------------------
proc dollarEq(n: int) =
  if $n == "42":
    symexTarget("dollar")

# --- parseInt digits-path: parseInt(s) == 42 → witness s == "42" ------------
proc parseEq(s: string) =
  if parseInt(s) == 42:
    symexTarget("pi")

# --- parseInt negative: parseInt(s) == -42 with s == "-42" → witness -42 ----
# (asserts BOTH the string witness and that the int model is -42 via the
# pinned literal — the negative-prefix ITE fork.)
proc parseNeg(s: string) =
  if s == "-42" and parseInt(s) == -42:
    symexTarget("piNeg")

# --- non-digit input: RAISES ValueError (S10b closed the pre-E1 window) -----
# `parseInt("abc")` on a non-digit, non-`-`-prefixed string RAISES `ValueError`
# (S10b). The raise fork happens during cond evaluation; the digits continuation
# (which `== -1` would have used) is constrained out, so this surfaces as
# `sxRaised{ValueError}` under a raised-exn search.
proc parseNonDigit(s: string) =
  if s == "abc":
    let n = parseInt(s)
    symexTarget("piND")

suite "symex Phase 15 S10a — $int/parseInt digits-path (pre-E1 window)":
  test "$int: $n == \"42\" pins n == 42 (decimal string repr)":
    let r = symexFind(dollarEq, tLabel("dollar"))
    check r.status == sxSat
    check r.witness[0] == 42

  test "parseInt: parseInt(s) == 42 is SAT with witness s == \"42\"":
    let r = symexFind(parseEq, tLabel("pi"))
    check r.status == sxSat
    check r.witness[0] == "42"

  test "parseInt: parseInt(\"-42\") produces sxSat with int result -42":
    let r = symexFind(parseNeg, tLabel("piNeg"))
    check r.status == sxSat
    check r.witness[0] == "-42"

  test "parseInt: non-digit input RAISES ValueError (S10b closed the window)":
    let r = symexFind(parseNonDigit, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # the S10a unsoundness-window hint is no longer emitted (S10b closed it).
    for e in r.errors:
      check e.kind != seParseIntPreE
