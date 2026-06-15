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
## EXPLICIT pre-E1 unsoundness window: for a non-digit input, Z3's `str.to-int`
## leaves the result unconstrained (the `>= 0` gate does not exclude every Nim
## `raise ValueError` case), so the walker emits a classified `seParseIntPreE`
## `sevHint`. The path STAYS sxSat (the hint is informational; sxSat + a sevHint
## still satisfies the Invariant-7 severity contract — only sxUnknown requires a
## sevError). The precise raises-path lands at S10b (post-E1).
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

# --- non-digit input: still sxSat, but with a seParseIntPreE hint -----------
# The pre-E1 unsoundness window: nim-z3's `str.to_int` returns the fixed value
# −1 for a non-digit string, so `parseInt(s) == -1` is sxSat for a non-digit `s`
# — whereas Nim's `parseInt("abc")` would RAISE before the comparison. Modeling
# the raise needs E1 (S10b); until then the walker flags this with a
# `seParseIntPreE` sevHint and the path stays sxSat.
proc parseNonDigit(s: string) =
  if s == "abc" and parseInt(s) == -1:
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

  test "parseInt: non-digit input emits seParseIntPreE hint, stays sxSat":
    let r = symexFind(parseNonDigit, tLabel("piND"))
    check r.status == sxSat
    check r.witness[0] == "abc"
    # the documented unsoundness window: a hint is present, result still sxSat.
    var sawHint = false
    for e in r.errors:
      if e.kind == seParseIntPreE:
        check e.severity == sevHint
        sawHint = true
    check sawHint
