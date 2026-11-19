## RFC-0016 S8co (PRC-33, a finding of item 5) -- OP_BRAMINZERO's count on
## 8.37's JIT. compile_matchingpath's OP_BRAMINZERO case moves `cc` past the
## bracket (`bracketend`) before it tests `cc[1] > OP_ASSERTBACK_NOT`, so the
## byte it reads is the one after the opcode that follows the bracket (an
## OP_CHAR's character, the next opcode after an operand-less one, a link's
## high byte), not the bracket's opcode: a `count_match` runs at the label
## where the rest after the lazy group is tried only when that byte is past
## OP_ASSERTBACK_NOT. Every limited call is compared with the native 8.37 JIT
## (`scripts/dt-bounded.sh -i pcre-8.37-jit`); the automaton and the walker
## are pinned anywhere. A unit that is not read (a bitmap class's, an
## OP_XCLASS's) declines the call accounting.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8cu_helpers

const
  patterns = [
    "(?:ab)*?\xE9", "(?:ab)*?c", "(?:ab)??\xE9", "(?:ab)??c",
    "(?:ab|a)*?\xE9c", "(?:ab)*?\\z(?:c)", "(?:ab)*?\\z", "(?:ab)*?$(?:c|d)",
    "x(?:ab)*?\xE9", "(?:ab)*?(?:\xE9)", "(ab)*?\xE9",
    "(?:ab)*?\xE9\xE9", "(?:a|ab)*?\xE9b",
    "(?:ab){1,3}?\xE9", "(?:ab|)*?\xE9", "(?:ab|)*?c", "(?:a?)*?\xE9",
    "(?:ab){0,3}?\xE9", "(?:ab){1,3}?c", "(?:ab){0,3}?c"]
  subjects = ["", "ab", "abab", "ababab", "abababab", "\xE9", "ab\xE9",
    "abab\xE9", "ababab\xE9", "abababab\xE9", "ababc", "ababababc",
    "abab\xE9c", "xab\xE9", "xabab\xE9", "aab\xE9", "aaab\xE9b", "abd",
    "ab\xE9\xE9", "ababx", "abababx"]
  limits = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 20]

proc bzSym(s: string) =
  if s == "\xE9" and s.find(re"(*LIMIT_MATCH=1)(?:ab)*?\xE9") == -8:
    symexTarget("co_bz")

proc bzSymNo(s: string) =
  if s == "\xE9" and s.find(re"(*LIMIT_MATCH=1)(?:ab)*?\xE9") != -8:
    symexTarget("co_bz_no")

proc bzClass(s: string) =
  if s.len <= 3 and s.find(re"(*LIMIT_MATCH=2)(?:ab)*?[\xE9c]") == -8:
    symexTarget("co_bz_class")

suite "S8co: OP_BRAMINZERO's count on the 8.37 JIT":
  test "the automaton counts where the unit says so, and declines an unread one":
    proc stop(p, s: string): int =
      let n = buildNfa(parsePcre(p), peJit837, limitRoom = 0)
      check n.ok
      let g = pcreExec(n, s, 0, false)
      if g[0] >= 0: g[1] else: g[0]
    # The unit after OP_CHAR: 0xE9 counts, `c` does not.
    check stop("(*LIMIT_MATCH=1)(?:ab)*?\xE9", "\xE9") == pcreErrMatchLimit
    check stop("(*LIMIT_MATCH=1)(?:ab)*?c", "ababc") == 0
    # After an operand-less OP_EOD, the next opcode (an OP_BRA) counts.
    proc maxStop(p, s: string): int =
      for lim in 1 .. 30:
        if stop("(*LIMIT_MATCH=" & $lim & ")" & p, s) == pcreErrMatchLimit:
          result = lim
    # (A subject with the required `c`, so the attempt runs.)
    check maxStop("(?:ab)*?\\z(?:c)", "ababc") > maxStop("(?:ab)*?\\z", "ababc")
    # A nullable group's empty iteration goes on past OP_BRAMINZERO's label.
    check maxStop("(?:ab|)*?\xE9", "abab\xE9") > maxStop("(?:ab|)*?c", "ababc")
    check stop("(*LIMIT_MATCH=2)(?:ab)??\xE9", "ab\xE9") == pcreErrMatchLimit
    # A bounded lazy chain: its outermost OP_BRAMINZERO reads the unit. One
    # behind a mandatory copy is folded (`detect_repeat`'s OP_MINUPTO): no
    # OP_BRAMINZERO runs.
    check maxStop("(?:ab){0,3}?\xE9", "abab\xE9") >
      maxStop("(?:ab){0,3}?c", "ababc")
    check maxStop("(?:ab){1,3}?\xE9", "abab\xE9") ==
      maxStop("(?:ab){1,3}?c", "ababc")
    for p in ["(*LIMIT_MATCH=2)(?:ab)*?[\xE9c]", "(*LIMIT_MATCH=2)(?:ab)??[a-c]"]:
      let n = buildNfa(parsePcre(p), peJit837, limitRoom = 0)
      check not n.ok and "OP_BRAMINZERO" in n.why

  test "the walker reads the count, and declines an unread unit":
    check parseInt(symexWalkerVersion) >= 419
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    check pinFind(bzSym, tLabel("co_bz")).status == sxSat
    check pinFind(bzSymNo, tLabel("co_bz_no")).status == sxUnsat
    check symexFind(bzClass, tLabel("co_bz_class")).status notin {sxSat, sxUnsat}

  test "every limited call is read":
    var unread: seq[string]
    for p in patterns:
      for lim in limits:
        let q = "(*LIMIT_MATCH=" & $lim & ")" & p
        let pr = parsePcre(q)
        if pr.status != psOk:
          unread.add q & " parse " & $pr.status
          continue
        let n = buildNfa(pr, peJit837, limitRoom = 0)
        if not n.ok or limitEffect(n)[0] == leUnknown:
          unread.add escape(q) & " " & n.why
    for u in unread[0 ..< min(unread.len, 20)]: echo "  unread ", u
    check unread.len == 0

  test "native JIT against the automaton":
    if not pcreRunsJit() or pcreVersion() != "8.37 2015-04-28":
      skipCell(cellKey(axBuild, "8.37 2015-04-28|jit"),
        "the native JIT 8.37 is not the PCRE this host runs (" & pcreVersion() &
        ", jit=" & $pcreRunsJit() & "); compared against it only there")
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
