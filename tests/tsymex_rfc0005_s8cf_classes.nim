## RFC-0005 S8cf (item 7) -- UTF classes on libpcre 8.37. A negated escape
## reads the same on 8.37 and 8.45; a lone `(*UCP)` POSIX class reads with
## 8.37's `[:punct:]` (the symbols below 256); only a `[:graph:]`, `[:print:]`,
## `[:punct:]` or negated ascii / cntrl / xdigit beside another item declines.
## Each class is compared with the running library at every code point below
## U+0180 and at the wide samples.
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cf_classes_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 66 s).

import std/[unittest, re, strutils, unicode]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine

const
  posixNames = ["alpha", "lower", "upper", "alnum", "ascii", "blank", "cntrl",
    "digit", "graph", "print", "punct", "space", "word", "xdigit"]
  flipEscapes = ["\\S", "\\D", "\\W", "\\H", "\\V"]
  wideSamples = [0x180E, 0x2000, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000, 0x660,
    0x4E00, 0xFF10, 0x10000, 0x10FFFF, 0x1680, 0x212A]

proc negEscape(s: string) =
  if s == "\xc3\xa9" and s.matchLen(re"(*UTF)[\S\x{100}]") == 2:
    symexTarget("cf_cls_neg")

proc negEscapeNo(s: string) =
  if s == "\xc3\xa9" and s.matchLen(re"(*UTF)[\S\x{100}]") != 2:
    symexTarget("cf_cls_neg_no")

suite "S8cf: UTF classes":
  test "against the running library":
    var pats: seq[string]
    for nm in posixNames:
      for body in ["[[:$1:]]", "[[:^$1:]]", "[^[:$1:]]", "[^[:^$1:]]",
                   "[[:$1:]\\x{100}]", "[[:^$1:]\\x{100}]", "[[:$1:]_]",
                   "[[:^$1:]_]"]:
        pats.add "(*UTF)(*UCP)" & body % nm
    for e in flipEscapes:
      for pre in ["(*UTF)", "(*UTF)(*UCP)"]:
        for body in ["[$1]", "[^$1]", "[$1a]", "[^$1a]", "[$1\\x{100}]",
                     "[^$1\\x{100}]", "[$1\\x{e9}]"]:
          pats.add pre & body % e
    var cps: seq[int]
    for c in 0 .. 0x17F: cps.add c
    cps.add wideSamples
    let old = pcreOlderThan(8, 45)
    var calls, declined = 0
    var bad: seq[string]
    for p in pats:
      let pr = parsePcre(p, false, old)
      check pr.status == psOk
      if old and pr.classPre845:
        inc declined
        continue
      let n = buildNfa(pr)
      check n.ok
      let rx = re(p)
      for c in cps:
        let u = Rune(c).toUTF8
        inc calls
        let nat = matchLen(u, rx) == u.len
        let g = pcreExec(n, u, 0, true)
        if nat != (g[0] >= 0 and g[2] - g[1] == u.len) and bad.len < 30:
          bad.add p & " at U+" & toHex(c, 4) & " native " & $nat
    echo "  calls ", calls, " declined patterns ", declined, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    # What stays declined on 8.37, and nothing else: S8bt declined all of them.
    if old: check declined == 18

  test "the walker reads a negated escape on every library":
    check "\xc3\xa9".matchLen(re"(*UTF)[\S\x{100}]") == 2
    check symexFind(negEscape, tLabel("cf_cls_neg")).status == sxSat
    check symexFind(negEscapeNo, tLabel("cf_cls_neg_no")).status == sxUnsat
