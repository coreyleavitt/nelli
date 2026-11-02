## RFC-0005 S8cf (item 5) -- a SKIP:NAME count past `argCap`: no automaton holds
## it, a concrete call does, so the call is read at points. Native std/re
## states the value.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine

const
  unbounded = "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c"
  w = "abqbxabqbxabqbxabqbxabc"  # a failing try per iteration: past argCap

proc atPoint(s: string) =
  if s == w and s.find(re"(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == 22:
    symexTarget("cf_skip_at")

proc notAtPoint(s: string) =
  if s == w and s.find(re"(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == 3:
    symexTarget("cf_skip_not")

proc lit() =
  let s = w
  if s.find(re"(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == 22:
    symexTarget("cf_skip_lit")

suite "S8cf: SKIP:NAME past argCap":
  test "concrete calls against native":
    let rx = re(unbounded)
    let eng = pcreSearchEngine()
    let n = buildNfa(parsePcre(unbounded), eng)
    var compared = 0
    for reps in 1 .. 25:
      for tail in ["", "c", "a", "b", "ab", "ax", "abc", "by"]:
        for head in ["abq", "bx", "abqbx", "bxabq", "bxb", "abqb", "abqa", "aby"]:
          let s = head.repeat(reps) & tail
          let got = pcreExec(n, s, 0, false)
          check got[0] != pcreUnmodelled
          inc compared
          checkpoint s
          let g = if got[0] >= 0: got[1] else: got[0]
          check g == find(s, rx)
    echo "  compared ", compared
    check compared == 1600

  test "the walker decides it":
    check find(w, re(unbounded)) == 22
    check symexFind(atPoint, tLabel("cf_skip_at")).status == sxSat
    check symexFind(notAtPoint, tLabel("cf_skip_not")).status == sxUnsat
    check symexFind(lit, tLabel("cf_skip_lit")).status == sxSat
