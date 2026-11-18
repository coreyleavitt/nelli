## RFC-0016 PRC-33 hotfix (SND-16): a regex call on a literal or pinned
## subject, with a SKIP:NAME pattern under an in-pattern limit, against
## native PCRE 8.37. Each call's value is stated natively first.
## Red on main at 3ed885e2 (walker 401) for every case but p10m8: the walker
## read `find` as -21 where native returns -1 or 0, and as -1 or 0 where
## native stops at LIMIT_RECURSION (-21) -- both literal and pinned queries
## answered the wrong `sxSat` / `sxUnsat`.
##
## The fix is a decline, not a model: a SKIP:NAME that can run without its
## MARK under `(*LIMIT_RECURSION=n)` is unmodelled (`buildNfa` is not `ok`,
## the concrete call too), so for those cases the expectation is "not a
## wrong verdict": the native value is never refuted (`!= sxUnsat`) and the
## value main computed is never reached (`!= sxSat`); the walker answers
## unknown. Under `(*LIMIT_MATCH=n)` (p10m8) the call stays modelled and
## must still agree exactly; so must every case on the 8.37 JIT, which
## ignores LIMIT_RECURSION.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8cu_helpers

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
  let res = pinFind(f, tLabel(l))
  echo "  ", l, ": ", res.status
  res.status

suite "hotfix: SKIP:NAME under a limit on a concrete subject":
  test "the walker's version floor (SND-16)":
    check parseInt(symexWalkerVersion) >= 412

  test "a SKIP:NAME without its MARK under LIMIT_RECURSION declines":
    for q in ["(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
              "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
              "(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
              "(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.",
              "(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+"]:
      let pr = parsePcre(q)
      check pr.status == psOk
      check not buildNfa(pr, limitRoom = 0).ok
      check not buildNfa(pr, limitRoom = 0, concrete = true).ok
    # LIMIT_MATCH stays modelled, and the concrete call agrees with native.
    let pr = parsePcre("(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?")
    let nc = buildNfa(pr, limitRoom = 0, concrete = true)
    check nc.ok
    check pcreExec(nc, "aca", 0, false)[0] == 1
    check pcreExec(nc, "aca", 0, false)[1] == 0

  # The cases: subject, pattern, the interpreter's native value, the value
  # main computed. An unanchored `find` runs on std/re's library engine: on
  # the 8.37 JIT (`pcre-8.37-jit` image) LIMIT_RECURSION has no effect, the
  # call stays modelled, and the walker must agree with that native value
  # exactly.
  let jit = pcreSearchEngine() == peJit837

  template rcase(nat, bad, pnat, pbad: untyped; subj, pat: string;
                 vNat, vBad: int) =
    let v = subj.find(re(pat))
    if jit:
      check verdict(nat, astToStr(nat)) ==
        (if v == vNat: sxSat else: sxUnsat)
      check verdict(bad, astToStr(bad)) ==
        (if v == vBad: sxSat else: sxUnsat)
      check verdict(pnat, astToStr(pnat)) ==
        (if v == vNat: sxSat else: sxUnsat)
      check verdict(pbad, astToStr(pbad)) ==
        (if v == vBad: sxSat else: sxUnsat)
    else:
      check v == vNat
      # Declined: never a wrong verdict.
      check verdict(nat, astToStr(nat)) != sxUnsat
      check verdict(bad, astToStr(bad)) != sxSat
      check verdict(pnat, astToStr(pnat)) != sxUnsat
      check verdict(pbad, astToStr(pbad)) != sxSat

  test "LIMIT_MATCH stays exact (p10m8)":
    check "aca".find(re"(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?") == 0
    check verdict(lit_p10m8_nat, "lit_p10m8_nat") == sxSat
    check verdict(lit_p10m8_bad, "lit_p10m8_bad") == sxUnsat
    check verdict(pin_p10m8_nat, "pin_p10m8_nat") == sxSat
    check verdict(pin_p10m8_bad, "pin_p10m8_bad") == sxUnsat

  test "LIMIT_RECURSION: native first, then no wrong verdict":
    rcase(lit_p6r6_nat, lit_p6r6_bad, pin_p6r6_nat, pin_p6r6_bad, "acab",
          "(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
          -1, -21)
    rcase(lit_p11r7a_nat, lit_p11r7a_bad, pin_p11r7a_nat, pin_p11r7a_bad,
          "acaa",
          "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
          0, -21)
    rcase(lit_p11r7b_nat, lit_p11r7b_bad, pin_p11r7b_nat, pin_p11r7b_bad,
          "abxa",
          "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
          -21, 0)
    rcase(lit_p10r2_nat, lit_p10r2_bad, pin_p10r2_nat, pin_p10r2_bad, "a",
          "(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?", -21, -1)
    rcase(lit_p5r2_nat, lit_p5r2_bad, pin_p5r2_nat, pin_p5r2_bad, "a",
          "(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.", -21, 0)
    rcase(lit_p6r5_nat, lit_p6r5_bad, pin_p6r5_nat, pin_p6r5_bad, "aca",
          "(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
          -21, 0)
