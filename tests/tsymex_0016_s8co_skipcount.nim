## RFC-0016 S8co (PRC-33 item 6) -- SKIP:NAME counts with no model cap.
## pcre_exec.c counts the SKIP:NAMEs an attempt runs (`skip_arg_count`, an
## `int`) and keeps the run number of a SKIP:NAME without its MARK for the
## next attempt (`ignore_skip_arg`, an `int`). A concrete call holds both
## as PCRE does, so a count past the old cap of 100 is read, not declined;
## each call is compared with native std/re (8.45, the interpreter). Within
## an attempt the automata need no count past `argCap` either: a re-run
## ignores exactly the SKIP:NAMEs of its chain (`resolveBarrier`), so a
## saturated count decides nothing there; the search languages of patterns
## that run more than `argCap` SKIP:NAMEs before a re-run are built and
## checked against the concrete reading, word by word. On the 8.37 JIT
## (`pcreSearchEngine()`) a SKIP:NAME without its MARK is ignored in place
## and nothing is counted; every check reads the engine std/re runs on, and
## the walker must decide the 303-byte call there too (RFC-0016 S8co: its
## scratch solves took minutes over the JIT languages at a pinned subject).
import std/[unittest, re, strutils]
import ./s8bt_harness/[member, jit_corpus]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine

const
  unbounded = "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c"
  w = "abqbx".repeat(60) & "abc"   # a count well past 100
  nine = "(*SKIP:N)".repeat(9)
  # A plain SKIP in each: pcre_exec.c's count is then observable
  # (`Nfa.countArgs`).
  deep = ["x" & nine & "y|x|w(*SKIP)c", "x" & nine & "y|xz|z|b(*SKIP)c",
    "(?:x" & nine & "y|x)z|ab(*SKIP)c", "a(*SKIP:M)" & nine & "b|ab(*SKIP)c|a",
    "x" & nine & "(?:y|z" & nine & "w)|x.|a(*SKIP)b"]

proc atPoint(s: string) =
  if s == w and s.find(re"(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == 302:
    symexTarget("co_skip_at")

proc notAtPoint(s: string) =
  if s == w and s.find(re"(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == 3:
    symexTarget("co_skip_not")

suite "S8co: SKIP:NAME counts past the old concrete cap":
  test "concrete calls against native, counts to past 100":
    let rx = re(unbounded)
    let n = buildNfa(parsePcre(unbounded), pcreSearchEngine())
    check n.ok
    # The 8.37 JIT looks a SKIP:NAME's MARK up on the current path and
    # ignores one it does not find, in place: no count, no re-run
    # (`pcre_jit_compile.c`'s `do_search_mark`); the interpreter counts.
    check n.countArgs == (pcreSearchEngine() == peInterp)
    var compared = 0
    var bad: seq[string]
    for reps in [1, 2, 7, 8, 9, 20, 33, 34, 50, 51, 52, 60, 70, 101, 130]:
      for tail in ["", "c", "a", "abc", "by"]:
        for head in ["abq", "bx", "abqbx", "bxabq", "abqb", "aby"]:
          let s = head.repeat(reps) & tail
          let (got, _) = pcreExecIgn(n, s, 0, false)
          inc compared
          if got[0] == pcreUnmodelled:
            bad.add "declined " & s.len.intToStr & " " & head & "*" & $reps
            continue
          let g = if got[0] >= 0: got[1] else: got[0]
          if g != find(s, rx):
            bad.add "differs " & head & "*" & $reps & tail
    echo "  compared ", compared, ", ", bad.len, " bad"
    checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
    check bad.len == 0

  test "the walker decides a call past the old cap":
    check find(w, re(unbounded)) == 302
    check symexFind(atPoint, tLabel("co_skip_at")).status == sxSat
    check symexFind(notAtPoint, tLabel("co_skip_not")).status == sxUnsat

  test "search languages of a re-run past argCap":
    var bad: seq[string]
    var srch = 0
    for p in deep:
      let rx = re(p)
      let n = buildNfa(parsePcre(p), pcreSearchEngine())
      check n.ok
      check n.countArgs == (pcreSearchEngine() == peInterp)
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        let key = "co_deep:" & p
        let noOcc = searchLangV(n, key, skNoOcc, pc)
        let first = searchLangV(n, key, skFirst, pc)
        if not (noOcc.ok and first.ok):
          bad.add "declined " & p & " " & $pc & ": " & noOcc.why & first.why
          continue
        for u in words("xyzwabc", 4):
          let subj = pre & u
          let st = pre.len
          let (rc, a, _) = pcreExec(n, subj, st, false)
          inc srch
          let nat = find(subj, rx, st)
          if (if rc == 1: a else: rc) != nat:
            bad.add "native " & p & " " & escape(subj) & ": " & $rc & " " &
                    $a & " vs " & $nat
          let q = (if rc == 1: a - st else: -1)
          if member(noOcc.re, toSyms(u)) != (q == -1):
            bad.add "skNoOcc " & p & " " & escape(u)
          for k in 0 .. u.len:
            let w = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
            if member(first.re, w) != (q == k):
              bad.add "skFirst " & p & " " & escape(u) & " " & $k
          if bad.len > 20: break
    echo "  ", srch, " searches, ", bad.len, " bad"
    checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
    check bad.len == 0
