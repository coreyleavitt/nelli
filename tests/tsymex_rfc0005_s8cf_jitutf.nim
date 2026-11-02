## RFC-0005 S8cf (item 6) -- UTF mode on 8.37's JIT. Its prefix scan can stop
## at a continuation byte, and in UTF mode it runs only where the first items
## are literals and `\d \s \w`, which fail there: the U+0080..U+00BF first
## characters read as any other. Under (*ANY) a concrete call reads an attempt
## that starts inside a multi-byte newline; the search's languages decline it
## and the walker reads the call at points. Each is compared with the library,
## and each language with the concrete reference.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8bt_harness/member

const
  heads = ["(?:\\sb|\\x{a9})c", "(?:\\d|\\x{80})ab", "\\x{a9}b", "\\x{85}b",
    "\\x{85}\\x{85}", "[\\x{a9}]b", "\\x{ac}+b", "\\x{82}\\x{ac}", "(\\x{a9})b",
    "(?:\\x{a9}|a)b", "(?:\\sb|\\x{85})b", "\\s\\x{a9}", "\\d\\x{ac}b",
    "\\w\\x{ac}", "\\sb", "\\d\\db", "\\w{2}b", "(?i)\\x{e0}b"]
  tails = ["", "(*SKIP)", "(*COMMIT)", "(*SKIP:A)b|."]
  conventions = ["(*UTF)", "(*UTF)(*CRLF)", "(*UTF)(*ANY)"]
  chars = ["a", "b", "\xc3\xa9", "\xe2\x82\xac", "\xc2\x85", "\xc2\xa9",
           "\xe2\x80\xa9", "\n", "\r", " "]

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in chars: nx.add w & c
    result.add nx
    fr = nx

proc litHit(s: string) =
  if s.len <= 4 and s.find(re"(*UTF)\x{a9}b") == 1:
    symexTarget("cf_ju_lit")

proc litMid(s: string) =
  # The scan reaches the A9 of U+2029; the literal's bytes are not there.
  if s == "\xe2\x80\xa9b" and s.find(re"(*UTF)\x{a9}b") >= 0:
    symexTarget("cf_ju_mid")

proc anyHit(s: string) =
  if s == "a b" and s.find(re"(*UTF)(*ANY)\sb(*SKIP)") == 1:
    symexTarget("cf_ju_any")

proc anyNo(s: string) =
  if s == "a b" and s.find(re"(*UTF)(*ANY)\sb(*SKIP)") == 0:
    symexTarget("cf_ju_any_no")

suite "S8cf: UTF mode under the JIT's scan":
  test "concrete calls against native":
    if pcreSearchEngine() != peJit837:
      skip()
    else:
      var calls, scanned, midSeen = 0
      var bad: seq[string]
      let ws = words(3)
      for cv in conventions:
        for h in heads:
          for t in tails:
            let p = cv & h & t
            let pr = parsePcre(p)
            check pr.status == psOk
            let n = buildNfa(pr, peJit837)
            check n.ok
            if not n.ok: continue
            if n.jit.on: inc scanned
            let rx = re(p)
            for s in ws:
              inc calls
              let g = pcreExec(n, s, 0, false)
              let nat = findBounds(s, rx)
              let want = (if nat.first >= 0: (nat.first, nat.last + 1) else: (-1, 0))
              let have = (if g[0] >= 0: (g[1], g[2]) else: (-1, 0))
              if have[0] >= 0 and have[0] < s.len and
                 (ord(s[have[0]]) and 0xC0) == 0x80: inc midSeen
              if want != have and bad.len < 40:
                bad.add p & " " & escape(s) & ": model " & $have & " native " & $want
      echo "  calls ", calls, " patterns under the scan ", scanned,
        " mid-character matches ", midSeen, " differ ", bad.len
      for b in bad: echo "  ", b
      check bad.len == 0
      check scanned > 50

  test "search languages against the concrete reference":
    var runs, jitOn = 0
    var bad: seq[string]
    let ws = words(2)
    for cv in ["(*UTF)", "(*UTF)(*CRLF)"]:
      for h in heads:
        for t in ["", "(*SKIP)"]:
          let p = cv & h & t
          let pr = parsePcre(p)
          let n = buildNfa(pr, peJit837)
          check n.ok
          if not n.ok: continue
          if jitScanObservable(n): inc jitOn
          let key = "cfju:" & p
          for pc in startClasses(n):
            let pre = prefixOf(pc)
            let noOcc = searchLangV(n, key, skNoOcc, pc)
            let first = searchLangV(n, key, skFirst, pc)
            check noOcc.ok and first.ok
            if not (noOcc.ok and first.ok):
              bad.add "declined " & p & " " & noOcc.why & first.why
              continue
            for u in ws:
              inc runs
              let s = pre & u
              let st = pre.len
              let (rc, a, _) = pcreExec(n, s, st, false)
              if rc < -1: continue
              let q = (if rc == 1: a - st else: -1)
              if member(noOcc.re, toSyms(u)) != (q == -1) and bad.len < 40:
                bad.add "skNoOcc " & p & " " & escape(u) & " after " & $pc
              for j in 0 .. u.len:
                let mw = toSyms(u[0 ..< j]) & @[markSym] & toSyms(u[j .. ^1])
                if member(first.re, mw) != (q == j) and bad.len < 40:
                  bad.add "skFirst " & p & " " & escape(u) & " " & $j & " after " & $pc
    echo "  runs ", runs, " observable scans ", jitOn, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    check jitOn > 0
    # Stated by name, and the walker's route below decides the calls.
    let an = buildNfa(parsePcre("(*UTF)(*ANY)\\sb(*SKIP)"), peJit837)
    let al = searchLangV(an, "cfju:any", skFirst, pcOther)
    check not al.ok and "multi-byte newline" in al.why

  test "the walker reads them":
    check "\xe2\x80\xa9b".find(re"(*UTF)\x{a9}b") == -1
    check symexFind(litHit, tLabel("cf_ju_lit")).status == sxSat
    check symexFind(litMid, tLabel("cf_ju_mid")).status == sxUnsat
    check "a b".find(re"(*UTF)(*ANY)\sb(*SKIP)") == 1
    check symexFind(anyHit, tLabel("cf_ju_any")).status == sxSat
    check symexFind(anyNo, tLabel("cf_ju_any_no")).status == sxUnsat
