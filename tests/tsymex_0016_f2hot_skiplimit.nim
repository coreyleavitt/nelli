## RFC-0016 S8co hotfix probe (PRC-33): a regex call on a literal or pinned
## subject, with a SKIP:NAME pattern under an in-pattern limit, against native
## PCRE 8.37. Each call's value is stated natively first; the walker must
## find the native value reachable and the value it used to compute refuted.
## Red on main at 3ed885e2 (walker 401) for every case but p10m8: the walker
## reads `find` as -21 where native returns -1 or 0, and as -1 or 0 where
## native stops at LIMIT_RECURSION (-21).
import std/[unittest, re]
import nelli/symex

proc lit_p6r6_nat() =
  let s = "acab"
  if s.find(re"(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -1:
    symexTarget("lit_p6r6_nat")
proc pin_p6r6_nat(s: string) =
  if s == "acab" and s.find(re"(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -1:
    symexTarget("pin_p6r6_nat")
proc lit_p6r6_bad() =
  let s = "acab"
  if s.find(re"(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -21:
    symexTarget("lit_p6r6_bad")
proc pin_p6r6_bad(s: string) =
  if s == "acab" and s.find(re"(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -21:
    symexTarget("pin_p6r6_bad")
proc lit_p10m8_nat() =
  let s = "aca"
  if s.find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == 0:
    symexTarget("lit_p10m8_nat")
proc pin_p10m8_nat(s: string) =
  if s == "aca" and s.find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == 0:
    symexTarget("pin_p10m8_nat")
proc lit_p10m8_bad() =
  let s = "aca"
  if s.find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -1:
    symexTarget("lit_p10m8_bad")
proc pin_p10m8_bad(s: string) =
  if s == "aca" and s.find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -1:
    symexTarget("pin_p10m8_bad")
proc lit_p11r7a_nat() =
  let s = "acaa"
  if s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == 0:
    symexTarget("lit_p11r7a_nat")
proc pin_p11r7a_nat(s: string) =
  if s == "acaa" and s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == 0:
    symexTarget("pin_p11r7a_nat")
proc lit_p11r7a_bad() =
  let s = "acaa"
  if s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == -21:
    symexTarget("lit_p11r7a_bad")
proc pin_p11r7a_bad(s: string) =
  if s == "acaa" and s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == -21:
    symexTarget("pin_p11r7a_bad")
proc lit_p11r7b_nat() =
  let s = "abxa"
  if s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == -21:
    symexTarget("lit_p11r7b_nat")
proc pin_p11r7b_nat(s: string) =
  if s == "abxa" and s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == -21:
    symexTarget("pin_p11r7b_nat")
proc lit_p11r7b_bad() =
  let s = "abxa"
  if s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == 0:
    symexTarget("lit_p11r7b_bad")
proc pin_p11r7b_bad(s: string) =
  if s == "abxa" and s.find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == 0:
    symexTarget("pin_p11r7b_bad")
proc lit_p10r2_nat() =
  let s = "a"
  if s.find(re"(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -21:
    symexTarget("lit_p10r2_nat")
proc pin_p10r2_nat(s: string) =
  if s == "a" and s.find(re"(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -21:
    symexTarget("pin_p10r2_nat")
proc lit_p10r2_bad() =
  let s = "a"
  if s.find(re"(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -1:
    symexTarget("lit_p10r2_bad")
proc pin_p10r2_bad(s: string) =
  if s == "a" and s.find(re"(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -1:
    symexTarget("pin_p10r2_bad")
proc lit_p5r2_nat() =
  let s = "a"
  if s.find(re"(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.") == -21:
    symexTarget("lit_p5r2_nat")
proc pin_p5r2_nat(s: string) =
  if s == "a" and s.find(re"(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.") == -21:
    symexTarget("pin_p5r2_nat")
proc lit_p5r2_bad() =
  let s = "a"
  if s.find(re"(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.") == 0:
    symexTarget("lit_p5r2_bad")
proc pin_p5r2_bad(s: string) =
  if s == "a" and s.find(re"(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.") == 0:
    symexTarget("pin_p5r2_bad")
proc lit_p6r5_nat() =
  let s = "aca"
  if s.find(re"(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -21:
    symexTarget("lit_p6r5_nat")
proc pin_p6r5_nat(s: string) =
  if s == "aca" and s.find(re"(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -21:
    symexTarget("pin_p6r5_nat")
proc lit_p6r5_bad() =
  let s = "aca"
  if s.find(re"(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == 0:
    symexTarget("lit_p6r5_bad")
proc pin_p6r5_bad(s: string) =
  if s == "aca" and s.find(re"(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == 0:
    symexTarget("pin_p6r5_bad")

template verdict(f: untyped; l: string): untyped =
  let res = symexFind(f, tLabel(l))
  echo "  ", l, ": ", res.status
  res.status

suite "hotfix probe: SKIP:NAME under a limit on a concrete subject":
  test "native":
    check "acab".find(re"(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -1
    check "aca".find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == 0
    check "acaa".find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == 0
    check "abxa".find(re"(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d") == -21
    check "a".find(re"(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == -21
    check "a".find(re"(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.") == -21
    check "aca".find(re"(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+") == -21
  test "the walker agrees with native":
    check verdict(lit_p6r6_nat, "lit_p6r6_nat") == sxSat
    check verdict(lit_p6r6_bad, "lit_p6r6_bad") == sxUnsat
    check verdict(pin_p6r6_nat, "pin_p6r6_nat") == sxSat
    check verdict(pin_p6r6_bad, "pin_p6r6_bad") == sxUnsat
    check verdict(lit_p10m8_nat, "lit_p10m8_nat") == sxSat
    check verdict(lit_p10m8_bad, "lit_p10m8_bad") == sxUnsat
    check verdict(pin_p10m8_nat, "pin_p10m8_nat") == sxSat
    check verdict(pin_p10m8_bad, "pin_p10m8_bad") == sxUnsat
    check verdict(lit_p11r7a_nat, "lit_p11r7a_nat") == sxSat
    check verdict(lit_p11r7a_bad, "lit_p11r7a_bad") == sxUnsat
    check verdict(pin_p11r7a_nat, "pin_p11r7a_nat") == sxSat
    check verdict(pin_p11r7a_bad, "pin_p11r7a_bad") == sxUnsat
    check verdict(lit_p11r7b_nat, "lit_p11r7b_nat") == sxSat
    check verdict(lit_p11r7b_bad, "lit_p11r7b_bad") == sxUnsat
    check verdict(pin_p11r7b_nat, "pin_p11r7b_nat") == sxSat
    check verdict(pin_p11r7b_bad, "pin_p11r7b_bad") == sxUnsat
    check verdict(lit_p10r2_nat, "lit_p10r2_nat") == sxSat
    check verdict(lit_p10r2_bad, "lit_p10r2_bad") == sxUnsat
    check verdict(pin_p10r2_nat, "pin_p10r2_nat") == sxSat
    check verdict(pin_p10r2_bad, "pin_p10r2_bad") == sxUnsat
    check verdict(lit_p5r2_nat, "lit_p5r2_nat") == sxSat
    check verdict(lit_p5r2_bad, "lit_p5r2_bad") == sxUnsat
    check verdict(pin_p5r2_nat, "pin_p5r2_nat") == sxSat
    check verdict(pin_p5r2_bad, "pin_p5r2_bad") == sxUnsat
    check verdict(lit_p6r5_nat, "lit_p6r5_nat") == sxSat
    check verdict(lit_p6r5_bad, "lit_p6r5_bad") == sxUnsat
    check verdict(pin_p6r5_nat, "pin_p6r5_nat") == sxSat
    check verdict(pin_p6r5_bad, "pin_p6r5_bad") == sxUnsat
