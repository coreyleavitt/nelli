## RFC-0005 S8bj -- PCRE's start-of-match optimisation data, computed from
## the reader's tree (`pcre_startopt.startOpt`), against what the linked
## PCRE compiles and studies for the same pattern: the anchoring, the first
## character and its caselessness, the line-start flag, the required
## character and its caselessness, the start bits and the minimum length.
##
## `pcre_fullinfo` gives all but the two caseless flags; those are read from
## the compiled pattern's private `flags` word (pcre_internal.h's
## `real_pcre8_or_16`: magic, size, options, flags), PCRE_FCH_CASELESS 0x20
## and PCRE_RCH_CASELESS 0x80.
##
## The corpus: the probed patterns of `s8bj_harness/fullinfo-linux-8.45.txt`
## and generated ones (one to three items of a pool of characters, classes,
## escapes, repeats, groups, alternations, anchors, verbs and options, in
## and out of UTF mode).
import std/[unittest, strutils, re]
import pcre
import nelli/smt/[pcre_syntax, pcre_startopt, pcre_engine]

const probed = staticRead("s8bj_harness/fullinfo-linux-8.45.txt")

type Real = object
  anchored, startline, hasBits, fcCaseless, rcCaseless: bool
  firstChar, reqChar, minLength: int
  bits: set[char]

proc real(p: string): Real =
  var msg: cstring
  var off: cint
  let h = pcre.compile(p.cstring, 0, addr msg, addr off, nil)
  doAssert h != nil, p
  let ex = pcre.study(h, 0, addr msg)
  var opts: culong
  discard pcre.fullinfo(h, nil, pcre.INFO_OPTIONS, addr opts)
  result.anchored = (opts and pcre.ANCHORED.culong) != 0
  var fcf, rcf: cint
  var fc, rc: uint32
  discard pcre.fullinfo(h, nil, pcre.INFO_FIRSTCHARACTERFLAGS, addr fcf)
  discard pcre.fullinfo(h, nil, pcre.INFO_FIRSTCHARACTER, addr fc)
  discard pcre.fullinfo(h, nil, pcre.INFO_REQUIREDCHARFLAGS, addr rcf)
  discard pcre.fullinfo(h, nil, pcre.INFO_REQUIREDCHAR, addr rc)
  result.firstChar = (if fcf == 1: int(fc) else: -1)
  result.startline = fcf == 2
  result.reqChar = (if rcf == 1: int(rc) else: -1)
  let flags = cast[ptr UncheckedArray[uint32]](h)[3]
  result.fcCaseless = fcf == 1 and (flags and 0x20) != 0
  result.rcCaseless = rcf == 1 and (flags and 0x80) != 0
  var minl: cint
  discard pcre.fullinfo(h, ex, pcre.INFO_MINLENGTH, addr minl)
  result.minLength = (if minl > 0: int(minl) else: -1)
  var tbl: ptr array[32, uint8]
  discard pcre.fullinfo(h, ex, pcre.INFO_FIRSTTABLE, addr tbl)
  if tbl != nil:
    result.hasBits = true
    for b in 0 .. 255:
      if (tbl[b shr 3] and uint8(1 shl (b and 7))) != 0: result.bits.incl char(b)
  if ex != nil: pcre.free_study(ex)

proc `$`(x: Real): string =
  ## Compact: the bits as hex ranges.
  var bs = ""
  var b = 0
  while b < 256:
    if char(b) in x.bits:
      var e = b
      while e + 1 < 256 and char(e + 1) in x.bits: inc e
      bs.add toHex(b, 2) & (if e > b: "-" & toHex(e, 2) else: "") & " "
      b = e + 1
    else: inc b
  "anch=" & $x.anchored & " sl=" & $x.startline & " fc=" & $x.firstChar &
    (if x.fcCaseless: "i" else: "") & " rc=" & $x.reqChar &
    (if x.rcCaseless: "i" else: "") & " min=" & $x.minLength &
    " bits=" & (if x.hasBits: "{" & bs & "}" else: "nil")

proc mine(so: StartOpt): Real =
  Real(anchored: so.anchored, startline: so.startline, hasBits: so.hasBits,
       fcCaseless: so.firstCaseless, rcCaseless: so.reqCaseless,
       firstChar: so.firstChar, reqChar: so.reqChar,
       minLength: so.minLength, bits: so.bits)

var oldLibSkipped = 0

proc check1(p: string; bad: var seq[string]; n: var int) =
  let pr = parsePcre(p)
  if pr.status != psOk: return
  inc n
  let want = real(p)
  let got = mine(startOpt(pr))
  # RFC-0005 S8bj: PCRE 8.37 (the Windows legs') drops the caseless flag of
  # a required character after a `{0}` item; the walker declines those
  # patterns there (`pcre_syntax.parseSpec`), pinned below.
  if want != got and pcreBefore838() and "{0}" in p and
     parseSpec(RegexSpec(entry: "find", flag: "re", pattern: p)).status ==
       psUnmodelled:
    inc oldLibSkipped
    return
  if want != got:
    bad.add escape(p) & "\n    read " & $got & "\n    pcre " & $want

proc generated(): seq[string] =
  let pool = @["a", "b", "A", "\\n", "\r", "\xE9", "ab", "a*", "a+", "a?",
    "a{2}", "a{2,}", "a{0,2}", "a{3}b", "[ab]", "[a]", "[^a]", "[a-a]",
    "[^ab]", "[ab]*", "[ab]{2}", "[ab]{0,1}", "[\\d_]", "[^\\d]", "[\\D]",
    "[\\h]", "[\\H]", "[[:alpha:]]", "[[:^digit:]]", "[\\x{100}a]",
    "[^\\x{100}]", ".", ".*", ".+", "\\d", "\\D", "\\d*", "\\s+", "\\W?",
    "\\h", "\\h*", "\\v", "\\v?", "\\H", "\\V*", "\\N", "^", "$", "\\A",
    "\\z", "\\Z", "(a)", "(?:ab|ac)", "(a|b)", "(a)*", "(ab)+", "(a|bc){2}",
    "(?:a*)", "(a?b)", "(?:^a|^b)", "(?i)", "(?i:a)", "(?s)", "(?m)",
    "(?-i)", "|", "|b", "(*COMMIT)", "(*PRUNE)", "(*SKIP)", "(*THEN)",
    "(*MARK:x)", "(*SKIP:x)", "(*ACCEPT)", "(*F)", "(?s).*", "(.*)",
    "\\x{e9}", "\\x{20ac}", "[\\x{e9}-\\x{ff}]", "x{0}", "(x){0}", "k"]
  let prefixes = @["", "(*UTF8)", "(*UCP)", "(?i)", "(*CRLF)",
                   "(*UTF8)(?i)", "(*NO_START_OPT)"]
  for pre in prefixes:
    for a in pool:
      result.add pre & a
      for b in pool:
        result.add pre & a & b
  # Some triples.
  var k = 0
  for a in pool:
    for b in pool:
      for c in pool:
        inc k
        if k mod 7 == 0: result.add a & b & c
        if k mod 23 == 0: result.add "(*UTF8)" & a & b & c

suite "S8bj: PCRE's start-of-match data from the reader's tree":

  test "the probed patterns":
    var bad: seq[string]
    var n = 0
    for line in probed.splitLines():
      if not line.startsWith("INFO "): continue
      let q = line.find("\" anch=")
      if q < 0: continue   # a pattern PCRE rejects
      check1(line[5 .. q].unescape(), bad, n)
    echo "  probed: ", n, " patterns read"
    checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
    check bad.len == 0
    check n >= 100

  test "the generated patterns":
    var bad: seq[string]
    var n = 0
    for p in generated(): check1(p, bad, n)
    echo "  generated: ", n, " patterns read, ", bad.len, " differ"
    checkpoint bad[0 ..< min(bad.len, 25)].join("\n")
    check bad.len == 0
    check n >= 30_000

suite "S8bj: the library version scopes the walker's reading":

  test "PCRE before 8.38 drops a caseless required character after {0}":
    # std/re's own library decides it: 8.37 does not match "A", 8.45 does.
    let old = not "A".contains(re"x{0}(?i)a")
    check pcreBefore838() == old
    let sp = RegexSpec(entry: "find", flag: "re", pattern: "x{0}(?i)a")
    check parseSpec(sp).status == (if old: psUnmodelled else: psOk)
    # Without a `{0}` item, or with no caseless character, it is read.
    for p in ["(?i)a", "x{0}a"]:
      check parseSpec(RegexSpec(entry: "find", flag: "re",
                                pattern: p)).status == psOk
    echo "  libpcre ", pcreVersion(), ", ", oldLibSkipped,
         " generated patterns declined as pre-8.38"
