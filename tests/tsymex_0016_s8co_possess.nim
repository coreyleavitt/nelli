## RFC-0016 S8co (PRC-33 item 3) -- auto-possessification next to a
## character property (OP_PROP / OP_NOTPROP) or an extended class
## (OP_XCLASS): pcre_compile.c's `compare_opcodes` (PCRE 8.45) reads them
## through `propposstab`, `catposstab`, `posspropstab`, `check_char_prop`,
## the XCLASS bitmap and `PRIV(xclass)`. A concrete call under a match limit
## reads them, each compared with native PCRE's interpreter, and the walker
## decides a call it used to decline.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import nelli/smt/pcre_engine
import ./s8cu_helpers
import ./s8bt_harness/limit_oracle

const
  utfPatterns = [
    # property against property (propposstab cases 1 to 17)
    "\\p{L}+\\p{N}", "\\p{L}*\\P{L}", "\\p{L}+\\p{L}", "\\P{N}+\\p{N}",
    "\\p{Lu}+\\p{L}", "\\p{L}+\\p{Lu}", "\\p{L}+\\p{Nd}", "\\p{Nd}+\\p{L}",
    "\\p{Lu}+\\p{Ll}", "\\p{Lu}+\\P{Lu}", "\\P{Lu}+\\p{Lu}", "\\p{Lu}+\\P{N}",
    "\\p{Greek}+\\p{Latin}", "\\p{Latin}+\\p{Latin}", "\\p{Latin}+\\P{Latin}",
    "\\p{L&}+\\p{Xsp}", "\\p{L&}+\\p{Xan}", "\\p{Xan}+\\p{Xsp}",
    "\\p{Xan}+\\p{P}", "\\p{Xan}+\\p{N}", "\\p{Xwd}+\\p{P}", "\\p{Xwd}+\\p{Zs}",
    "\\p{Xwd}+\\p{Po}", "\\p{Xwd}+\\p{Pd}", "\\p{Xsp}+\\p{Z}", "\\p{Xsp}+\\p{C}",
    "\\p{Xsp}+\\p{L}", "\\p{Xsp}+\\p{Cc}", "\\p{Xsp}+\\p{Lu}", "\\p{P}+\\p{Xwd}",
    "\\p{Po}+\\p{Xwd}", "\\p{Pd}+\\p{Xwd}", "\\p{L}+\\p{Xsp}", "\\p{Lu}+\\p{Xan}",
    "\\p{N}+\\P{Xan}", "\\P{L}+\\p{Xwd}", "\\p{Xps}+\\p{Xwd}", "\\p{Xuc}+\\P{Xuc}",
    "\\p{Any}+\\p{L}", "\\p{L}+(?:\\p{N}|\\p{Zs})", "\\p{L}+\\z", "\\p{L}+$",
    # a character against a property
    "a+\\p{N}", "a+\\p{L}", "\\p{N}+a", "\\p{L}+a", "1*\\P{N}", "a+\\P{L}",
    "\\x{e9}+\\p{Ll}",
    # extended classes
    "[a-c]+[\\x{100}d]", "[a-c]+[\\x{100}b]", "[a-c]+[^\\x{100}a]",
    "[a-c]+[^\\x{100}d]", "[ab]+[\\x{100}-\\x{200}]", "[ab]*[^\\x{100}-\\x{200}]",
    "[ab]+[\\x{100}\\p{N}]", "a+[\\x{100}b]", "a+[\\x{100}a]",
    "[\\x{100}a]+b", "[\\x{100}a]+a", "[\\x{100}a]+\\p{N}", "\\p{N}+[\\x{100}a]",
    "[\\x{100}a]+[\\x{100}b]", "\\d+[\\x{100}a]", "[\\x{100}a]+\\d",
    "(*UCP)\\d+\\w", "(*UCP)\\w+\\s", "(*UCP)\\d+\\D", "(*UCP)\\s+\\S",
    "(*UCP)\\w+[\\x{e9}]"]
  byteCorpus = [
    "\\p{L}+\\p{N}", "\\p{L}+\\d", "\\d+\\p{L}", "a+\\p{N}", "\\p{N}+a",
    "\\p{Lu}+\\p{Ll}", "(*UCP)\\d+\\w", "(*UCP)\\w+\\s", "[ab]+\\p{L}"]
  subjects = ["", "a", "ab1", "aB1 ", "1a", "ab_", "abab", "a.b", "Ab-c d",
    "\xce\xb1\xce\xb21", "\xc4\x80b", "aa\xc4\x80", "a1a1", "AB\xc3\xa9",
    "abd", "ab\xc4\x80", "\xc3\xa9\xc3\xa9x", "a\tb", "11a2"]

proc runCorpus(pats: openArray[string]; prefix: string;
               declined: var seq[string]; bad: var seq[string];
               calls, stops: var int) =
  for p in pats:
    for lim in [1, 2, 3, 4, 5, 6, 8, 13]:
      let q = "(*LIMIT_MATCH=" & $lim & ")" & prefix & p
      let pr = parsePcre(q)
      if pr.status != psOk:
        declined.add q & ": parse " & $pr.status & " " & pr.reason
        continue
      let n = buildNfa(pr, limitRoom = 0, concrete = true)
      if not n.ok:
        declined.add q & ": " & n.why
        continue
      let o = initLimitOracle(q)
      for s in subjects:
        if pr.utf and utf8Error(s) >= 0: continue
        for anch in [true, false]:
          inc calls
          let got = pcreExec(n, s, 0, anch)
          if got[0] == pcreUnmodelled:
            declined.add q & " " & escape(s) & ": unmodelled"
            continue
          if got[0] < -1: inc stops
          let want = o.execInterp(s, 0, anch)
          if got != want and bad.len < 40:
            bad.add escape(q) & (if anch: " anch " else: " ") & escape(s) &
              ": model " & $got & " native " & $want

proc propSym(s: string) =
  if s == "abc1" and s.matchLen(re"(*LIMIT_MATCH=3)(*UTF)\p{L}+\p{N}") == 4:
    symexTarget("co_prop")

proc propSymNo(s: string) =
  if s == "abc1" and s.matchLen(re"(*LIMIT_MATCH=3)(*UTF)\p{L}+\p{N}") != 4:
    symexTarget("co_prop_no")

proc xclassSym(s: string) =
  if s == "aab" and s.matchLen(re"(*LIMIT_MATCH=3)(*UTF)a+[\x{100}b]") == 3:
    symexTarget("co_xclass")

suite "S8co item 3: auto-possession next to a property or an XCLASS":
  test "every pattern is read, and agrees with native":
    # The model is 8.45's `compare_opcodes`; an older native interpreter
    # (the 8.37 JIT image's) auto-possessifies differently next to an
    # XCLASS, so the comparison runs only against 8.45.
    if not pcreVersion().startsWith("8.45"):
      skipCell(cellKey(axBuild, "8.45|interp"),
        "the native interpreter is not PCRE 8.45 (" & pcreVersion() &
        "); the auto-possession model is compared against 8.45 only")
    else:
      var declined, bad: seq[string]
      var calls, stops = 0
      runCorpus(utfPatterns, "(*UTF)", declined, bad, calls, stops)
      runCorpus(byteCorpus, "", declined, bad, calls, stops)
      echo "  calls ", calls, " stops ", stops, " declined ", declined.len,
        " differ ", bad.len
      for d in declined[0 ..< min(declined.len, 20)]: echo "  declined ", d
      for b in bad: echo "  ", b
      check declined.len == 0
      check bad.len == 0
      check stops > 0

  test "the walker reads them":
    # Walker 419 (S8co) is the version that reads them.
    check parseInt(symexWalkerVersion) >= 419
    check "abc1".matchLen(re"(*LIMIT_MATCH=3)(*UTF)\p{L}+\p{N}") == 4
    check "aab".matchLen(re"(*LIMIT_MATCH=3)(*UTF)a+[\x{100}b]") == 3
    check pinFind(propSym, tLabel("co_prop")).status == sxSat
    check pinFind(propSymNo, tLabel("co_prop_no")).status == sxUnsat
    check pinFind(xclassSym, tLabel("co_xclass")).status == sxSat
