## RFC-0016 S8co (PRC-33 item 5) -- group repeats on 8.37's JIT.
## pcre_jit_compile.c's `detect_repeat` folds a run of identical brackets into
## one compiled copy with a counter: OP_EXACT (three or more copies, a
## `count_match` at the end of each) and OP_UPTO / OP_MINUPTO (the last
## mandatory copy and a chain of nested optional ones, a KETRMAX / KETRMIN
## loop counted where it goes on). Which copies fold is read off the linear
## code, literal duplicates and auto-possessified copies included. A fold that
## starts at a bracket behind OP_BRAZERO or OP_SKIPZERO is a JIT defect
## (pcre_jit_compile.c compiles the whole fold under the zero bracket; the
## native call crashes): the walker declines it.
##
## On the native 8.37 JIT (`scripts/dt-bounded.sh -i pcre-8.37-jit`) every
## corpus call is checked against std/re; the automaton is pinned anywhere.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8cu_helpers
import ./s8bt_harness/limit_oracle

const
  patterns = [
    "(?:ab){3}", "(?:ab){4}", "(?:ab){2,4}", "(?:ab){1,3}", "(?:ab){3,5}",
    "(?:ab){0,3}", "(?:ab){0,2}", "(?:ab|a){0,2}", "(?:ab|a){2,4}",
    "(a|b){3}", "(a|ab){1,4}c", "(?:ab){4,}", "(?:ab){3,}",
    "(?:ab)(?:ab)(?:ab)", "(?:ab)(?:ab){2,4}", "(?:ab){2}(?:ab)",
    "(?:a+){3}", "(?:a+){2,4}b", "(?:a|b){0,4}c", "(?:ab){2,3}",
    "x(?:ab){3,5}y", "(?:ab){1,3}?", "(?:ab){2,4}?c", "(?:ab){0,3}?c",
    "(?:a|ab){1,4}?c", "(?:ab){3}?", "(?:(?:ab){2}){3}", "(?:a(?:b){3}){2,3}",
    "(?:a|b){2,5}?b",
    "(ab){0,4}c", "(?:a*){3}b", "(?:ab){5,6}"]
  # A fold that starts behind OP_BRAZERO / OP_BRAMINZERO / OP_SKIPZERO: the
  # native JIT crashes (greedy; probed) or runs the fold where the zero
  # bracket's copy belongs (lazy), so the model declines the pattern on the JIT.
  crashing = ["(?:ab)?(?:ab)(?:ab)", "(?:ab)?(?:ab){3,4}",
    "(?:a|b)?(?:a|b)(?:a|b)", "(?:ab){0}(?:ab)(?:ab)(?:ab)",
    "(?:ab)??(?:ab)(?:ab)", "(?:ab)??(?:ab){2}c"]
  subjects = ["", "ab", "abab", "ababab", "abababab", "ababababab",
    "abababababab", "aaaa", "abababc", "ababc", "xababy", "xabababy",
    "xababababy", "aaab", "aab", "abc", "abbbabbb", "ababababc", "bbbb"]
  limits = [1, 2, 3, 4, 5, 6, 7, 8, 10, 13]

proc foldSym(s: string) =
  if s == "abababab" and s.find(re"(*LIMIT_MATCH=4)(?:ab){4}") == -8:
    symexTarget("co_fold")

proc foldSymNo(s: string) =
  if s == "abababab" and s.find(re"(*LIMIT_MATCH=4)(?:ab){4}") != -8:
    symexTarget("co_fold_no")

proc crashSym(s: string) =
  if s.find(re"(?:ab)?(?:ab)(?:ab)") == 0:
    symexTarget("co_crash")

suite "S8co item 5: detect_repeat group repeats on the JIT":
  test "every limited call is read":
    var unread: seq[string]
    for p in patterns:
      for lim in limits:
        let q = "(*LIMIT_MATCH=" & $lim & ")" & p
        let pr = parsePcre(q)
        if pr.status != psOk:
          unread.add q & " parse " & $pr.status & " " & pr.reason
          continue
        let n = buildNfa(pr, peJit837, limitRoom = 0)
        if not n.ok or limitEffect(n)[0] == leUnknown:
          unread.add q & " ok=" & $n.ok & " " & n.why
    for u in unread[0 ..< min(unread.len, 20)]: echo "  unread ", u
    check unread.len == 0

  test "a fold behind a zero bracket is declined on the JIT":
    for p in crashing:
      require parsePcre(p).status == psOk
      let n = buildNfa(parsePcre(p), peJit837)
      check not n.ok
      check "detect_repeat" in n.why and "starting behind OP_" in n.why
      # The interpreter has no folds.
      check buildNfa(parsePcre(p), peInterp).ok

  test "native JIT against the automaton":
    if not pcreRunsJit() or pcreVersion() != "8.37 2015-04-28":
      skipCell(cellKey(axBuild, "8.37 2015-04-28|jit"),
        "the native JIT 8.37 is not the PCRE this host runs (" & pcreVersion() &
        ", jit=" & $pcreRunsJit() & "); folds are compared against it only there")
    else:
      var bad: seq[string]
      var calls, stops = 0
      for p in patterns:
        for lim in limits:
          let q = "(*LIMIT_MATCH=" & $lim & ")" & p
          let pr = parsePcre(q)
          if pr.status != psOk: continue
          let n = buildNfa(pr, peJit837, limitRoom = 0)
          if not n.ok or limitEffect(n)[0] == leUnknown: continue
          let rx = re(q)
          for s in subjects:
            inc calls
            let got = pcreExec(n, s, 0, false)
            let want = find(s, rx)
            let g = if got[0] >= 0: got[1] else: got[0]
            if g == pcreErrMatchLimit: inc stops
            if g != want and bad.len < 40:
              bad.add escape(q) & " on " & escape(s) & ": model " & $g &
                      " native " & $want
      echo "  calls ", calls, " stops ", stops, " differ ", bad.len
      for b in bad: echo "  ", b
      check bad.len == 0
      check stops > 0
      # The lazy zero-led fold is not a crash: the JIT runs the wrong copies.
      let lz = "(?:ab)??(?:ab)(?:ab)c"
      check find("abababc", re(lz)) == 2
      check initLimitOracle(lz).execInterp("abababc", 0) == (1, 0, 7)

  test "the walker reads a fold, and declines a crashing one":
    check parseInt(symexWalkerVersion) >= 419
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    check pinFind(foldSym, tLabel("co_fold")).status == sxSat
    check pinFind(foldSymNo, tLabel("co_fold_no")).status == sxUnsat
    check symexFind(crashSym, tLabel("co_crash")).status notin {sxSat, sxUnsat}
