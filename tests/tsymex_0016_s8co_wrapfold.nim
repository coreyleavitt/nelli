## RFC-0016 S8co (PRC-33 item 4c) -- a literal group byte-identical to a
## repeat's optional-copy wrapper, on 8.37's JIT. pcre_jit_compile.c's
## `detect_repeat` compares code bytes, not the pattern: an OP_BRAZERO'd
## `(?:(?:ab)(?:ab)?)` after `(?:ab)` is the chain `(?:ab){1,3}` compiles
## to, so the JIT folds it into an OP_UPTO loop; a literal `(?:(?:ab)(?:ab))`
## and a `(?:(?:ab){2})` are one bracket's bytes, and three in a row fold
## into OP_EXACT. The folds are read off the code's layout
## (`pcre_jitrepeat.nim`, a token per opcode) instead of off the pattern's
## repeats, so each one is counted where the JIT counts it. A fold that
## starts at a repeat's own wrapper (behind its OP_BRAZERO) is the zero
## bracket defect item 5 declines.
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

const
  patterns = [
    # A literal wrapper extends the chain: one OP_UPTO / OP_MINUPTO loop.
    "(?:ab)(?:(?:ab)(?:ab)?)?", "(?:ab)(?:(?:ab)(?:ab)?)?c",
    "(?:ab)(?:(?:ab)(?:ab)??)??c", "(?:ab)(?:(?:ab)(?:ab){0,2})?",
    "(?:ab){2}(?:(?:ab)(?:ab)?)?", "(?:ab)(?:ab)(?:ab)(?:(?:ab)(?:ab)?)?",
    "(?:ab)(?:(?:ab){1,2})?c", "(?:ab)(?:(?:ab)(?:(?:ab)(?:ab)?)?)?c",
    "x(?:(?:ab)(?:(?:ab)(?:ab)?)?)?y", "(a|b)(?:(a|b)(a|b)?)?c",
    "(?:ab)(?:(?:ab)(?:ab)?)?(?:ab)",
    # A literal bracket with a repeat's bytes: OP_EXACT across the spellings.
    "(?:(?:ab){1,2})(?:(?:ab)(?:ab)?)(?:(?:ab)(?:ab)?)",
    "(?:(?:ab){2})(?:(?:ab)(?:ab))(?:(?:ab)(?:ab))c",
    "(?:(?:ab)(?:ab)?){2}(?:(?:ab){1,2})c",
    # Close to a chain, but not one: no fold.
    "(?:ab)(?:(?:ab)(?:ab)?)*", "(?:ab)(?:(?:ab)(?:ab)?c)?",
    "(?:ab)(?:(?:ab)(?:ac)?)?", "(?:ab)(?:(?:ab)(?:ab)?)??",
    "(?:ab)(?:(?:ab)(?:ab)?x?)?", "(?:ab)(ab(?:ab)?)?"]
  # A fold that starts at a repeat's wrapper, behind its OP_BRAZERO.
  zeroLed = ["(?:ab){0,2}(?:(?:ab)(?:ab)?)(?:(?:ab)(?:ab)?)",
             "(?:ab){0,2}(?:(?:ab)(?:ab)?){2}c"]
  subjects = ["", "ab", "abab", "ababab", "abababab", "ababababab",
    "abababababab", "abc", "ababc", "abababc", "ababababc", "xababy",
    "xabababy", "xay", "aab", "abbbc", "bac", "abacab", "ababx"]
  limits = [1, 2, 3, 4, 5, 6, 7, 8, 10, 13]

proc wrapSym(s: string) =
  if s == "abab" and s.find(re"(*LIMIT_MATCH=2)(?:ab)(?:(?:ab)(?:ab)?)?") == 0:
    symexTarget("co_wrap")

proc wrapSymNo(s: string) =
  if s == "abab" and s.find(re"(*LIMIT_MATCH=2)(?:ab)(?:(?:ab)(?:ab)?)?") != 0:
    symexTarget("co_wrap_no")

proc exactSym(s: string) =
  if s == "abababc" and
     s.find(re"(*LIMIT_MATCH=1)(?:(?:ab){1,2})(?:(?:ab)(?:ab)?)(?:(?:ab)(?:ab)?)c") == -8:
    symexTarget("co_wrapx")

suite "S8co item 4c: a literal group with a wrapper's bytes on the JIT":
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

  test "a fold that starts at a repeat's wrapper is declined on the JIT":
    for p in zeroLed:
      require parsePcre(p).status == psOk
      let n = buildNfa(parsePcre(p), peJit837)
      check not n.ok
      check "detect_repeat" in n.why and "starting behind OP_BRAZERO" in n.why
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

  test "the walker counts a literal wrapper's fold":
    check parseInt(symexWalkerVersion) >= 393
    # read before the override: std/re's own engine, the native oracle
    let nativeJit = pcreSearchEngine() == peJit837
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    # The wrapper's fold is the 8.37 JIT's: the interpreter's native count
    # differs (RFC-0016 K9d), so these two are pinned natively on the JIT
    # image (`pcre-8.37-jit`) and checked as walker verdicts elsewhere.
    if nativeJit:
      check pinFind(wrapSym, tLabel("co_wrap")).status == sxSat
      check pinFind(wrapSymNo, tLabel("co_wrap_no")).status == sxUnsat
    else:
      check symexFind(wrapSym, tLabel("co_wrap")).status == sxSat
      check symexFind(wrapSymNo, tLabel("co_wrap_no")).status == sxUnsat
    check pinFind(exactSym, tLabel("co_wrapx")).status == sxSat
