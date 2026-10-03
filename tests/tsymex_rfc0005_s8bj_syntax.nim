## RFC-0005 S8bj -- the reader (`pcre_syntax.parsePcre`) against the real
## `re()` on the constructs S8bb left undecided: the backtracking verbs
## and marks, the `(*LIMIT_..)` start options, UTF mode, `(?m)` and `(?X)`,
## and PCRE's numeric and case escapes.
##
## Every pattern of the probed corpus (`tests/s8bj_harness/pc1.txt`, whose
## Linux PCRE 8.45 results are `pc1.linux-8.45.out`) and of a generated
## corpus is compiled by `re()` and read: a pattern `re()` rejects must be
## `psRejected` with Nim's exact `RegexError.msg` (PCRE's message, the
## pattern, the caret at PCRE's offset), and an accepted one `psOk` or
## `psUnmodelled`. Only the escapes the reader leaves undecided (`\C \K \R
## \X \g \k`) may be `psUnknown`. The start options the reader records are
## pinned against `pcre.fullinfo` (UTF, NO_START_OPT, the two limits).
import std/[unittest, strutils, re]
import pcre
import nelli/smt/pcre_syntax

const corpus = staticRead("s8bj_harness/pc1.txt")

proc undecidedOk(p: string): bool =
  ## The escapes the reader does not decide.
  for e in ["\\C", "\\K", "\\R", "\\X", "\\g", "\\k"]:
    if e in p: return true
  false

proc compare(p: string; bad: var seq[string]; counts: var array[PcreStatus, int]) =
  let pr = parsePcre(p)
  inc counts[pr.status]
  var real = ""
  var ok = true
  try: discard re(p)
  except RegexError as e:
    ok = false
    real = e.msg
  let where = escape(p) & " -> " & $pr.status & " " & pr.reason
  if ok:
    if pr.status == psRejected:
      bad.add where & " (re() accepts it): " & escape(pr.errMsg)
    elif pr.status == psUnknown and not undecidedOk(p):
      bad.add where & " (undecided)"
  else:
    if pr.status == psUnknown:
      if not undecidedOk(p): bad.add where & " (undecided; re(): " &
                                     escape(real) & ")"
    elif pr.status != psRejected or pr.errMsg != real:
      bad.add where & " " & escape(pr.errMsg) & " but re(): " & escape(real)

proc generated(): seq[string] =
  ## Each atom alone and under each prefix and suffix.
  let atoms = @[
    # verbs and marks
    "(*COMMIT)", "(*commit)", "(*Commit)", "(*COMMIT:)", "(*COMMIT:x)",
    "(*PRUNE)", "(*PRUNE:)", "(*PRUNE:n)", "(*SKIP)", "(*SKIP:)", "(*SKIP:n)",
    "(*THEN)", "(*THEN:)", "(*THEN:n)", "(*MARK:n)", "(*MARK:)", "(*MARK)",
    "(*:n)", "(*:)", "(*ACCEPT)", "(*ACCEPT:x)", "(*F)", "(*FAIL)",
    "(*F:x)", "(*FOO)", "(*SKIP:" & repeat('a', 255) & ")",
    "(*SKIP:" & repeat('a', 256) & ")", "(*THEN", "(*SKIP:ab", "(*1)",
    "(*:n)a", "a(*SKIP)b|c", "(?:a(*THEN)b|c)", "(*MARK:n)(*SKIP:n)",
    # numeric escapes
    "\\x{41}", "\\x{0041}", "\\x{000000000041}", "\\x{100}", "\\x{ff}",
    "\\x{}", "\\x{g}", "\\x{41", "\\x41", "\\x4", "\\xg", "\\o{101}",
    "\\o{400}", "\\o{377}", "\\o{}", "\\o", "\\o{8}", "\\o{1", "\\101",
    "\\400", "\\777", "\\377", "\\0", "\\07", "\\077", "\\0777", "\\8",
    "\\9", "\\81", "\\12", "\\1", "(a)\\1", "(a)\\2", "\\8(a)", "[\\1]",
    "[\\8]", "[\\400]", "[\\x{100}]", "[\\o{101}-\\o{102}]",
    "\\99999999999", "\\x{d800}", "\\x{10ffff}", "\\x{110000}",
    "\\o{4000000}", "\\o{154000}",
    # case escapes and \N
    "\\L", "\\l", "\\U", "\\u", "[\\L]", "[a-\\u]", "\\N{x}", "\\N{1}",
    "\\N{1,}", "\\N{,1}", "\\N", "[\\N]", "\\N{1,2}",
    # PCRE_EXTRA letters
    "\\i", "\\j", "\\m", "\\q", "\\y", "\\F", "\\I", "\\J", "\\M", "\\O",
    "\\T", "\\Y", "[\\i]", "[\\T-\\Y]", "\\_",
    # options
    "(?m)", "(?m)^a$", "(?m:^)", "(?X)", "(?-X)", "(?mX)", "(?m-X)",
    # UTF characters
    "\xC3\xA9", "\xC3\xA9+", "[\xC3\xA9-\xC3\xBF]", "[\xC3\xBF-\xC3\xA9]",
    "\xE2\x82\xAC{2}", "\xFF", "\xC3", "\xC3\x28", "\xED\xA0\x80",
    "\xF4\x90\x80\x80", "\xC0\x80", "\\\xC3\xA9", "[\\\xC3\xA9]",
    "\\x{e9}", "\\xe9", "\\351", "[^\xC3\xA9]", "\\Q\xC3\xA9\\E+",
    "(*LIMIT_MATCH=5)", "(*LIMIT_RECURSION=0)",
  ]
  let prefixes = @["", "(*UTF8)", "(*UTF)", "(?X)", "(?m)", "(*UTF8)(?X)",
                   "(?i)", "(*UTF8)(?i)", "a(?X)|", "(?X:", "(*LIMIT_MATCH=7)"]
  let suffixes = @["", "+", "{2}", "?", ")", "\\i"]
  for a in atoms:
    for p in prefixes:
      for s in suffixes:
        result.add p & a & s

suite "S8bj: the reader against re()":

  test "the probed corpus: every pattern decided as re() decides it":
    var bad: seq[string]
    var counts: array[PcreStatus, int]
    var n = 0
    for line in corpus.splitLines():
      if line.len == 0 or line.startsWith("#"): continue
      inc n
      compare(line.unescape("", ""), bad, counts)
    echo "  pc1: ", n, " patterns ", counts
    checkpoint bad.join("\n")
    check bad.len == 0
    check n >= 150

  test "a generated corpus: verbs, escapes, UTF, (?m) and (?X)":
    var bad: seq[string]
    var counts: array[PcreStatus, int]
    let pats = generated()
    for p in pats:
      compare(p, bad, counts)
    echo "  generated: ", pats.len, " patterns ", counts
    checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
    check bad.len == 0
    check counts[psRejected] > 500
    check counts[psOk] > 1000

  test "the start options recorded are PCRE's":
    var bad: seq[string]
    let pats = @["(*LIMIT_MATCH=5)a", "(*LIMIT_MATCH=5)(*LIMIT_MATCH=3)a",
      "(*LIMIT_MATCH=3)(*LIMIT_MATCH=5)a", "(*LIMIT_MATCH=)a",
      "(*LIMIT_MATCH=0012)a", "(*LIMIT_RECURSION=9)(*UTF8)a",
      "(*UTF8)(*LIMIT_MATCH=1)(*LIMIT_RECURSION=2)a",
      "(*LIMIT_MATCH=9999999)a", "(*LIMIT_MATCH=10000000)a",
      "(*LIMIT_MATCH=429496728)a", "(*NO_START_OPT)a", "(*UTF)a",
      "(*UCP)(*UTF8)(*NO_START_OPT)a", "(*CRLF)(*LIMIT_MATCH=4)a", "a"]
    for p in pats:
      let pr = parsePcre(p)
      check pr.status == psOk
      var msg: cstring
      var off: cint
      let h = pcre.compile(p.cstring, 0, addr msg, addr off, nil)
      var opts: culong
      discard pcre.fullinfo(h, nil, pcre.INFO_OPTIONS, addr opts)
      var ml, rl: uint32
      let mrc = pcre.fullinfo(h, nil, pcre.INFO_MATCHLIMIT, addr ml)
      let rrc = pcre.fullinfo(h, nil, pcre.INFO_RECURSIONLIMIT, addr rl)
      let wantM = (if mrc == 0: int64(ml) else: -1'i64)
      let wantR = (if rrc == 0: int64(rl) else: -1'i64)
      let wantUtf = (opts and pcre.UTF8.culong) != 0
      let wantNso = (opts and pcre.NO_START_OPTIMIZE.culong) != 0
      if pr.limitMatch != wantM or pr.limitRecursion != wantR or
         pr.utf != wantUtf or pr.noStartOpt != wantNso:
        bad.add escape(p) & " read " & $(pr.limitMatch, pr.limitRecursion,
          pr.utf, pr.noStartOpt) & " pcre " & $(wantM, wantR, wantUtf, wantNso)
    checkpoint bad.join("\n")
    check bad.len == 0

  test "the tree: verbs, marks, (?m) anchors and UTF characters":
    proc kinds(x: Rx; acc: var seq[string]) =
      case x.kind
      of rxVerb: acc.add $x.verb & (if x.name.len > 0: ":" & x.name else: "")
      of rxBol, rxEol: acc.add $x.kind & (if x.multi: "m" else: "")
      of rxChars: acc.add "chars" & $x.cps
      of rxCat, rxAlt:
        for k in x.kids: kinds(k, acc)
      of rxRep: kinds(x.sub, acc)
      else: discard
    proc read(p: string): string =
      let pr = parsePcre(p)
      check pr.status == psOk
      var acc: seq[string]
      kinds(pr.root, acc)
      acc.join(" ")
    check read("(*COMMIT)a(*PRUNE:x)b(*THEN:y)") == "vbCommit vbPrune vbThen"
    check read("(*MARK:x)(*:y)(*SKIP:x)(*SKIP)") ==
          "vbMark:x vbMark:y vbSkipName:x vbSkip"
    check read("(*SKIP:)") == "vbSkip"
    check read("(?m)^a$|\\A(?-m)^\\Z") == "rxBolm rxEolm rxBol rxBol rxEol"
    check read("(*UTF8)\xC3\xA9\\x{20ac}") ==
          "chars@[(lo: 233, hi: 233)] chars@[(lo: 8364, hi: 8364)]"
    check read("(*UTF)[^a]") ==
          "chars@[(lo: 0, hi: 96), (lo: 98, hi: 1114111)]"
    check read("(*UTF)\\D") ==
          "chars@[(lo: 0, hi: 47), (lo: 58, hi: 1114111)]"
    # RFC-0005 S8bt: Unicode case folding, properties, (*UCP) and (*ANY)
    # are modelled in UTF mode (`tsymex_rfc0005_s8bt_utf`).
    for p in ["(*UTF8)(?i)k", "(*UTF8)(?i)[r-t]", "(*UTF8)(?i)\xC3\xA9",
              "(*UTF8)\\p{L}", "(*UTF8)(*UCP)\\w", "(*UTF8)(*ANY)a"]:
      checkpoint escape(p)
      check parsePcre(p).status == psOk
    check parsePcre("(*UTF8)(?i)a").status == psOk
