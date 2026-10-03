## RFC-0005 S8bt (item 3) -- a `(*LIMIT_MATCH=)` / `(*LIMIT_RECURSION=)`
## between 0 and PCRE's default, symbolically: the attempt's languages
## (`lkErrM`, `lkErrR`, `lkMark`, `lkNone`), the search's (`skErrM`,
## `skErrR` and their marked forms, `skNoOcc`, `skFirst`) and the step
## table's `replace` against the concrete reference (`pcreExec`, pinned
## against libpcre by `tsymex_rfc0005_s8bt_limit`), in every start
## variant; the Z3 `replace` term; and the walker's verdicts.
import std/[unittest, strutils, times, re]
import z3
import nelli/symex
import nelli/smt/types
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]
import nelli/smt/pcre_engine
import ./s8bt_harness/[member, stepref, limit_oracle]

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

const limPats = [
  "(*LIMIT_MATCH=4)a+b", "(*LIMIT_MATCH=6)(?:a|b)*c", "(*LIMIT_MATCH=3)a|b",
  "(*LIMIT_MATCH=9)(a|ab)(c|bcd)", "(*LIMIT_MATCH=5)a*?b",
  "(*LIMIT_RECURSION=3)(?:a|b)*c", "(*LIMIT_RECURSION=2)a+b|ab",
  "(*LIMIT_MATCH=7)(*LIMIT_RECURSION=3)a(?:b|c)+d",
  "(*LIMIT_MATCH=5)a(*COMMIT)b|.", "(*LIMIT_MATCH=6)\\s+a"]

proc subjects(): seq[string] =
  result = @[""]
  var cur = @[""]
  for n in 1 .. 4:
    var nx: seq[string]
    for w in cur:
      for c in "abc ": nx.add w & c
    result.add nx
    cur = nx

suite "S8bt: a limit between, symbolically":

  test "the attempt's languages":
    var bad: seq[string]
    var calls = 0
    for p in limPats:
      let n = limitNfa(parsePcre(p), peInterp)
      check n.ok and n.costs
      if not n.ok: continue
      let key = "lim:" & p
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        let eM = selectionLangV(n, key, lkErrM, pc)
        let eR = selectionLangV(n, key, lkErrR, pc)
        let none = selectionLangV(n, key, lkNone, pc)
        let mark = selectionLangV(n, key, lkMark, pc)
        check eM.ok and eR.ok and none.ok and mark.ok
        if not (eM.ok and eR.ok and none.ok and mark.ok): continue
        for u in subjects():
          inc calls
          let s = pre & u
          let st = pre.len
          let (k, pos, _) = runAttempt(n, s, st, st, true)
          let w = escape(p) & " " & escape(u) & " after " & $pc
          if member(eM.re, toSyms(u)) != (k == okLimitM):
            bad.add "lkErrM " & w
          if member(eR.re, toSyms(u)) != (k == okLimitR):
            bad.add "lkErrR " & w
          if member(none.re, toSyms(u)) != (k != okMatch):
            bad.add "lkNone " & w
          for q in 0 .. u.len:
            let mw = toSyms(u[0 ..< q]) & @[markSym] & toSyms(u[q .. ^1])
            if member(mark.re, mw) != (k == okMatch and pos - st == q):
              bad.add "lkMark " & w & " " & $q
        if bad.len > 20: break
    echo "  ", calls, " attempts, ", bad.len, " differ, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0

  test "the search's languages":
    var bad: seq[string]
    var calls, errs = 0
    for p in limPats:
      let n = limitNfa(parsePcre(p), peInterp)
      if not n.ok: continue
      let key = "lim:" & p
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        var ls: seq[SelLang]
        for k in [skErrM, skErrR, skErrMAt, skErrRAt, skNoOcc, skFirst]:
          ls.add searchLangV(n, key, k, pc)
          check ls[^1].ok
        for u in subjects():
          inc calls
          let s = pre & u
          let st = pre.len
          let (rc, a, _) = pcreExec(n, s, st, false)
          if rc < -1: inc errs
          let w = escape(p) & " " & escape(u) & " after " & $pc
          # The error, were its attempt made (the languages leave that
          # check to the caller): at the marked attempt.
          proc hitOf(l, lAt: SelLang): bool =
            if not member(l.re, toSyms(u)): return false
            var qs: seq[int]
            for q in 0 .. u.len:
              let mw = toSyms(u[0 ..< q]) & @[markSym] & toSyms(u[q .. ^1])
              if member(lAt.re, mw): qs.add q
            doAssert qs.len == 1, w & " " & $qs
            attemptMade(n, s, st + qs[0], n.filter == fkFirst)
          let hitM = hitOf(ls[0], ls[2])
          let hitR = hitOf(ls[1], ls[3])
          if hitM != (rc == pcreErrMatchLimit): bad.add "skErrM " & w
          if hitR != (rc == pcreErrRecursionLimit): bad.add "skErrR " & w
          if not (hitM or hitR):
            let q = (if rc == 1: a - st else: -1)
            if member(ls[4].re, toSyms(u)) != (q == -1):
              bad.add "skNoOcc " & w
            for k in 0 .. u.len:
              let mw = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
              if member(ls[5].re, mw) != (q == k):
                bad.add "skFirst " & w & " " & $k
        if bad.len > 20: break
    echo "  ", calls, " searches (", errs, " limit errors), ", bad.len,
         " differ, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0
    check errs > 100

  test "replace: the step table and the Z3 term":
    var bad: seq[string]
    var runs, checked = 0
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for p in limPats:
      let n = limitNfa(parsePcre(p), peInterp)
      if not n.ok: continue
      let t = stepTable(n)
      check t.ok
      if not t.ok:
        bad.add escape(p) & " " & t.why
        continue
      let o = initLimitOracle(p)
      for s in subjects():
        inc runs
        let want = o.replaceInterp(s, "-")
        if pcreReplace(n, s, "-") != want: bad.add "ref " & escape(p) & " " & escape(s)
        if replaceRef(n, t, s, "-") != want:
          bad.add "table " & escape(p) & " " & escape(s)
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
      for k, s in subjects():
        if s.len == 4 and k mod 9 != 0: continue
        inc checked
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(s)
        sol.add r != mkString(o.replaceInterp(s, "-"))
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 20:
          bad.add "z3 " & escape(p) & " " & escape(s) & " " & res
    echo "  ", runs, " replace runs, ", checked, " Z3 values, ", bad.len,
         " differ, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0

proc findErrTarget(s: string) =
  if s.len <= 4 and s.find(re"(*LIMIT_MATCH=6)(?:a|b)*c") == -8:
    symexTarget("bt_limit_find_err")

proc findNeverTarget(s: string) =
  # libpcre: no subject of length 6 or less makes this call an error.
  if s.len <= 6 and s.find(re"(*LIMIT_MATCH=4)a+b") == -8:
    symexTarget("bt_limit_find_never")

proc findOkTarget(s: string) =
  if s.len <= 6 and s.find(re"(*LIMIT_MATCH=4)a+b") == 1:
    symexTarget("bt_limit_find_ok")

proc matchLenTarget(s: string) =
  if s.len <= 4 and s.matchLen(re"(*LIMIT_RECURSION=3)(?:a|b)*c") == -21:
    symexTarget("bt_limit_matchlen")

proc matchLenNeverTarget(s: string) =
  # libpcre: no subject of length 4 or less makes this call an error.
  if s.len <= 4 and s.matchLen(re"(*LIMIT_RECURSION=2)a+b|ab") == -21:
    symexTarget("bt_limit_matchlen_never")

proc replaceTarget(s: string) =
  if s.len == 1 and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") == "-":
    symexTarget("bt_limit_replace")

proc replaceErrTarget(s: string) =
  # A limit error ends `replace` as a miss does: the subject comes back
  # ("ac" is "-" without the limit).
  if s == "ac" and s.replace(re"(*LIMIT_MATCH=6)(?:a|b)*c", "-") != "ac":
    symexTarget("bt_limit_replace_err")

suite "S8bt: a limit between, through the walker":

  template verdict(sut: untyped; label: string; want = sxSat) =
    let t1 = epochTime()
    let r = symexFind(sut, tLabel(label))
    echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t1,
                                                       ffDecimal, 1), " s"
    check r.status == want

  test "an anchored call: sxSat, and sxUnsat where libpcre has none":
    verdict(matchLenTarget, "bt_limit_matchlen")
    verdict(matchLenNeverTarget, "bt_limit_matchlen_never", sxUnsat)

  # An unanchored call on the JIT (the Windows legs) declines: its
  # accounting is not modelled.
  test "unanchored calls: sxSat on the interpreter, never sxUnsat on the JIT":
    if pcreSearchEngine() == peInterp:
      verdict(findErrTarget, "bt_limit_find_err")
      verdict(findOkTarget, "bt_limit_find_ok")
      verdict(findNeverTarget, "bt_limit_find_never", sxUnsat)
      verdict(replaceTarget, "bt_limit_replace")
      verdict(replaceErrTarget, "bt_limit_replace_err", sxUnsat)
    else:
      # Declined: never a refutation (a replayed witness may still be
      # found -- the JIT's `replace` of "ac" is "-").
      template notRefuted(sut: untyped; label: string) =
        let r = symexFind(sut, tLabel(label))
        echo "  ", label, " (JIT): ", r.status
        check r.status != sxUnsat
      notRefuted(findErrTarget, "bt_limit_find_err")
      notRefuted(replaceErrTarget, "bt_limit_replace_err")
