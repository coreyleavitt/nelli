## RFC-0016 S8co (PRC-33 item 7) -- `(*ANY)` in UTF mode under 8.37's JIT
## prefix scan. The scan can stop at a continuation byte, so an attempt can
## start inside a multi-byte newline (U+0085, U+2028, U+2029: start classes
## `pcU1` .. `pcU3`). The search's verifier for such an attempt starts from the
## search's own progress through the newline (`startNl`), so it reads a final
## newline's remaining bytes as the search does. Each search language is
## compared with the concrete reference (`pcreExec`, itself checked against
## the native JIT in `tsymex_rfc0005_s8cf_jitutf`), and the walker decides a
## symbolic call.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8bt_harness/member
from ./s8cu_helpers import pinFind

const
  heads = ["\\x{85}b", "\\x{85}\\x{85}", "\\sb", "(?:\\sb|\\x{85})b",
           "\\x{a9}b", "(\\x{a9})b", "\\s\\x{a9}", "\\w\\x{ac}", "\\d\\db"]
  tails = ["", "(*SKIP)"]
  chars = ["a", "b", "\xc3\xa9", "\xc2\x85", "\xc2\xa9", "\xe2\x80\xa9",
           "\xe2\x80\xa8", "\n", "\r", " "]

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in chars: nx.add w & c
    result.add nx
    fr = nx

proc anyHit(s: string) =
  if s.len <= 4 and s.find(re"(*UTF)(*ANY)\sb(*SKIP)") == 1:
    symexTarget("co_any_hit")

proc anyNo(s: string) =
  # A U+0085 first: the scan can stop at its 85, where no `\s` starts.
  if s.len <= 4 and s.startsWith("\xc2\x85") and
     s.find(re"(*UTF)(*ANY)\sb(*SKIP)") == 0:
    symexTarget("co_any_no")

suite "S8co item 7: (*ANY) in UTF mode under the JIT's scan":
  test "search languages against the concrete reference":
    var runs, jitOn = 0
    var bad: seq[string]
    let ws = words(2)
    for h in heads:
      for t in tails:
        let p = "(*UTF)(*ANY)" & h & t
        let n = buildNfa(parsePcre(p), peJit837)
        check n.ok
        if not n.ok: continue
        if jitScanObservable(n): inc jitOn
        let key = "coany:" & p
        for pc in startClasses(n):
          let pre = prefixOf(pc)
          let noOcc = searchLangV(n, key, skNoOcc, pc)
          let first = searchLangV(n, key, skFirst, pc)
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
                bad.add "skFirst " & p & " " & escape(u) & " " & $j &
                        " after " & $pc
    echo "  runs ", runs, " observable scans ", jitOn, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    check jitOn > 0

  test "the walker decides a symbolic call":
    check parseInt(symexWalkerVersion) >= 380
    overridePcreLib("8.37 2015-04-28", true)
    defer: clearPcreLibOverride()
    check pinFind(anyHit, tLabel("co_any_hit")).status == sxSat
    check pinFind(anyNo, tLabel("co_any_no")).status == sxUnsat
