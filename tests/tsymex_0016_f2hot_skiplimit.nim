## RFC-0016 SND-16: a regex call on a literal or pinned subject, with a
## SKIP:NAME pattern under an in-pattern limit, against native PCRE 8.37.
## Each call's value is stated natively first.
## Red on main at 3ed885e2 (walker 401) for every case but p10m8: the walker
## read `find` as -21 where native returns -1 or 0, and as -1 or 0 where
## native stops at LIMIT_RECURSION (-21) -- both literal and pinned queries
## answered the wrong `sxSat` / `sxUnsat`. The hotfix (walker 412) declined a
## SKIP:NAME that can run without its MARK under `(*LIMIT_RECURSION=n)`.
##
## S8co (walker 419) models the re-run's depths and lifts the decline: a
## SKIP:NAME terminal a decided item cut stays in the agenda wherever the
## call counts (`keepsCut`), so `rerunCosts` lifts its continuation's depth,
## and `capCosts` keeps an item the re-run brings back under the match limit
## (`argCap` of slack). Every case is now exact: each verdict is pinned
## (`pinExact`, the `construct:regex/skipName/*` cells) and must be the one
## native gives. An unanchored `find` runs on std/re's library engine: on
## the 8.37 JIT (`pcre-8.37-jit` image) LIMIT_RECURSION has no effect, so
## there the expected verdict is read from the native value at run time.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import nelli/smt/admission
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

const
  matchCell = cellKey(axConstruct, "regex/skipName/limitMatch")
  recCell = cellKey(axConstruct, "regex/skipName/limitRecursion")

template pinCase(fn: untyped; cell: CellKey; want: bool;
               dom: untyped): untyped =
  ## The pinned verdict (its record judged against the native run) is the
  ## one the native value gives.
  let r = pinExact(fn, cell, target = tLabel(astToStr(fn)), domain = dom)
  echo "  ", astToStr(fn), ": ", r.status
  check r.status == (if want: sxSat else: sxUnsat)

suite "SND-16: SKIP:NAME under a limit on a concrete subject":
  test "the walker's version floor (S8co lifts the SND-16 decline)":
    check parseInt(symexWalkerVersion) >= 419

  test "a SKIP:NAME without its MARK under LIMIT_RECURSION is modelled":
    for q in ["(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
              "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
              "(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
              "(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.",
              "(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+"]:
      let pr = parsePcre(q)
      check pr.status == psOk
      check buildNfa(pr, limitRoom = 0).ok
      check buildNfa(pr, limitRoom = 0, concrete = true).ok
    let pr = parsePcre("(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?")
    let nc = buildNfa(pr, limitRoom = 0, concrete = true)
    check nc.ok
    check pcreExec(nc, "aca", 0, false)[0] == 1
    check pcreExec(nc, "aca", 0, false)[1] == 0

  # The cases: subject, pattern, the interpreter's native value, the value
  # main computed at 3ed885e2. On the interpreter the native value is
  # checked first; on the JIT the expected verdicts follow its own value.
  let jit = pcreSearchEngine() == peJit837

  template rcase(nat, bad, pnat, pbad: untyped; cell: CellKey;
                 subj, pat: string; vNat, vBad: int) =
    let v = subj.find(re(pat))
    if not jit: check v == vNat
    let dom = sampled([subj, "", "b" & subj])
    pinCase(nat, cell, v == vNat, sampled([0]))
    pinCase(bad, cell, v == vBad, sampled([0]))
    pinCase(pnat, cell, v == vNat, dom)
    pinCase(pbad, cell, v == vBad, dom)

  test "LIMIT_MATCH: the re-run's calls (p10m8)":
    rcase(lit_p10m8_nat, lit_p10m8_bad, pin_p10m8_nat, pin_p10m8_bad,
          matchCell, "aca", "(*LIMIT_MATCH=8)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
          0, -1)

  test "LIMIT_RECURSION: the re-run's depths":
    rcase(lit_p6r6_nat, lit_p6r6_bad, pin_p6r6_nat, pin_p6r6_bad, recCell,
          "acab",
          "(*LIMIT_RECURSION=6)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
          -1, -21)
    rcase(lit_p11r7a_nat, lit_p11r7a_bad, pin_p11r7a_nat, pin_p11r7a_bad,
          recCell, "acaa",
          "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
          0, -21)
    rcase(lit_p11r7b_nat, lit_p11r7b_bad, pin_p11r7b_nat, pin_p11r7b_bad,
          recCell, "abxa",
          "(*LIMIT_RECURSION=7)(?:a(*SKIP:N)c|a(*SKIP:N)(?:ab(*SKIP)q|b(*SKIP:N)x)|b)+|d",
          -21, 0)
    rcase(lit_p10r2_nat, lit_p10r2_bad, pin_p10r2_nat, pin_p10r2_bad,
          recCell, "a", "(*LIMIT_RECURSION=2)(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
          -21, -1)
    rcase(lit_p5r2_nat, lit_p5r2_bad, pin_p5r2_nat, pin_p5r2_bad, recCell,
          "a", "(*LIMIT_RECURSION=2)a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.",
          -21, 0)
    rcase(lit_p6r5_nat, lit_p6r5_bad, pin_p6r5_nat, pin_p6r5_bad, recCell,
          "aca", "(*LIMIT_RECURSION=5)(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
          -21, 0)
