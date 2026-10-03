## S8bj probe: dump std/re behaviour (and pcre_fullinfo start-optimisation
## data) for verbs, limits, UTF, (?m), (?X), CRLF skip. Run on Linux and on
## the Windows leg; compare the per-pattern hashes.
import std/[re, strutils, os]
import pcre

proc fnv(s: string): uint64 =
  result = 1469598103934665603'u64
  for c in s:
    result = (result xor uint64(ord(c))) * 1099511628211'u64

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

type Group = object
  alpha: string
  maxLen: int
  pats: seq[string]

let groups = @[
  Group(alpha: "abc", maxLen: 4, pats: @[
    "(*COMMIT)abc", "(*NO_START_OPT)(*COMMIT)abc", "a(*COMMIT)b", "a+(*COMMIT)b",
    "(*COMMIT)a|b", "a(*COMMIT)b|ac", "(?:a(*COMMIT)b|ac)", "a(*COMMIT)(?:b|c)c",
    "(?:a(*COMMIT)b)*c", "(*COMMIT)", "(*COMMIT)b?", "b(*COMMIT)", "[ab](*COMMIT)c",
    "(*NO_START_OPT)[ab](*COMMIT)c", "(?i)A(*COMMIT)b", "^(*COMMIT)a", "c*(*COMMIT)a",
    ".*(*COMMIT)b", "(*NO_START_OPT).*(*COMMIT)b", "a?(*COMMIT)c", "(*COMMIT)(?:a|b)c",
    "x*a(*COMMIT)bc", "ab(*COMMIT)c|b",
    "(*PRUNE)", "a(*PRUNE)b", "a+(*PRUNE)b", "aa(*PRUNE)b|ab", "(?:a(*PRUNE)b|ac)c",
    "a(*PRUNE)|b", "(*PRUNE)a", "(*NO_START_OPT)(*PRUNE)a", "a*(*PRUNE)c",
    "(*PRUNE:X)a(*PRUNE)b", "a(*PRUNE:N)b|ac",
    "(*SKIP)", "a(*SKIP)b", "a+(*SKIP)b", "aa(*SKIP)b|a", "(*SKIP)a", "a(*SKIP)(*FAIL)|b",
    "a+(*SKIP)(*F)|c", "ab(*SKIP)c|bc", "(?:a(*SKIP)b|ac)", "a*(*SKIP)b", "b*(*SKIP)a",
    "(*NO_START_OPT)a(*SKIP)b", "(*NO_START_OPT)ab(*SKIP)c|bc",
    "(*SKIP:X)a", "(*MARK:X)a(*SKIP:X)b", "a(*MARK:X)a(*SKIP:X)b|aac", "a(*SKIP:X)b|ac",
    "a(*MARK:X)b(*SKIP:X)c|bd", "(*MARK:X)ab(*SKIP:X)(*F)|c", "a(*:X)b(*SKIP:X)(*F)|bc",
    "a(*SKIP:X)b(*MARK:X)c|a", "(*MARK:X)a(*SKIP:Y)b|ac", "a(*SKIP:X)(*SKIP)b|c",
    "(?:a(*SKIP:X)b|c)+", "a(*SKIP:X)b(*SKIP:X)c|abd|bd",
    "(*THEN)", "a(*THEN)b|ac", "(?:a(*THEN)b|ac)c", "a(?:b(*THEN)c|bd)", "(?:a(*THEN)b)c|ad",
    "a(*THEN)b", "(?:a(*THEN)b|a)+c", "(a(*THEN)b|ac)*", "a(?:b(*THEN)|c)d|abc",
    "(?:a|ab)(*THEN)c|abd", "a(*THEN:X)b|ac", "(?:(?:a(*THEN)b)|ac)", "(?:a(*THEN)b|ac|ad)",
    "a(*COMMIT)(*PRUNE)b|ac", "a(*THEN)b(*COMMIT)c|abd", "a(*SKIP)b(*PRUNE)c|bc",
    "(*ACCEPT)(*COMMIT)a", "a(*COMMIT)(*ACCEPT)b|ac", "(*UTF8)a(*COMMIT)b",
  ]),
  Group(alpha: "ab\r\n", maxLen: 3, pats: @[
    "(*CRLF)[\\x09-\\x0b]\\z", "(*CRLF)(?:[\\x09-\\x0b]\\x00)?.", "(*CRLF)\\n",
    "(*CRLF)[\\n]", "(*CRLF)\\s", "(*CRLF)\\v", "(*CRLF)[^a]", "(*CRLF)$", "(*CRLF)\\z",
    "(*CRLF)(*NO_START_OPT)[\\x09-\\x0b]\\z", "(*ANYCRLF)\\s", "(*ANY)\\v", "(*ANYCRLF)b?\\z",
    "(*CRLF)b?\\Z", "(*CRLF)[^ab]", "(*CRLF)(*COMMIT)\\s", "(*CRLF)\\s(*SKIP)b",
    "(*CRLF)x*", "(*ANY)x?", "(*CRLF).", "(*CRLF)\\s*\\z", "(*CRLF)\\v|a",
    "(?m)^a", "(?m)a$", "(?m)^$", "(?m)^", "(?m)$", "(?m)^b|a", "(?m)(?:^|a)b", "(?m)a$\\n?",
    "(*CRLF)(?m)^", "(*CRLF)(?m)$", "(*CRLF)(?m)^a", "(*CRLF)(?m)a$", "(*ANYCRLF)(?m)^",
    "(*ANYCRLF)(?m)$", "(*ANY)(?m)^", "(*ANY)(?m)$", "(*CR)(?m)^", "(*CR)(?m)$",
    "(?m)^.*", "(?m).*$", ".*b", "(*CRLF).*b", "(*ANYCRLF).*b", "(*ANYCRLF)(?m)^b",
    "(?m)\\A|b", "(?m)^\\n", "(?m:^)a|b", "a(?m)$|b$", "(?m)(?-m)^a", "(?m)^(?:a|)",
    "(*NO_START_OPT)(?m)^b", "(*CRLF)(?m)^b", "(*ANY)(?m)^b", "(?m)^(*COMMIT)b",
  ]),
  Group(alpha: "a\xC3\xA9\x80\xE2\x82\xAC\xFF", maxLen: 3, pats: @[
    "(*UTF8).", "(*UTF8)..", "(*UTF8)a", "(*UTF8)\xC3\xA9", "(*UTF8)[^a]", "(*UTF8)\\x{e9}",
    "(*UTF8)[\\x{80}-\\x{7ff}]", "(*UTF8)[\\x{800}-\\x{ffff}]", "(*UTF8).+", "(*UTF8)a.?",
    "(*UTF)\\W", "(*UTF)\\D", "(*UTF)\\h", "(*UTF)\\v", "(*UTF)\\S", "(*UTF)[[:^alpha:]]",
    "(*UTF8)$", "(*UTF8)x*", "(*UTF8)\xE2\x82\xAC+", "(*UTF8)[\xC3\xA9a]", "(*UTF8)(?i)\xC3\xA9",
    "(*UTF8)(?i)a", "(*UTF8)\\xe9", "(*UTF8)[\\xe9-\\x{20ac}]", "(*UTF8)\\C", "(*UTF8)\\N",
    "(*UTF8)(*COMMIT)a", "(*UTF8)(*SKIP)a", "(*UTF8)a(*SKIP)b",
    "(*UTF8)\xFF", "(*UTF8)\xC3", "(*UTF8)\\x{d800}", "(*UTF8)\\x{110000}",
    "(*UTF8)\\p{L}", "(*UTF8)(*UCP)\\w", "(*UTF8)\\X",
  ]),
  Group(alpha: "ab", maxLen: 5, pats: @[
    "(*LIMIT_MATCH=1)a", "(*LIMIT_MATCH=2)a", "(*LIMIT_MATCH=3)a", "(*LIMIT_MATCH=0)a",
    "(*LIMIT_MATCH=2)a*b", "(*LIMIT_MATCH=3)a*b", "(*LIMIT_MATCH=5)a*b",
    "(*LIMIT_MATCH=3)(*NO_AUTO_POSSESS)a*b", "(*LIMIT_MATCH=4)(a|b)*b",
    "(*LIMIT_MATCH=8)(a|b)*b", "(*LIMIT_RECURSION=1)a", "(*LIMIT_RECURSION=2)(a|b)*b",
    "(*LIMIT_RECURSION=4)(a|b)*b", "(*LIMIT_RECURSION=0)a", "(*LIMIT_MATCH=10)(?:a|ab)*$",
    "(*LIMIT_MATCH=1)b", "(*LIMIT_MATCH=1)(*NO_START_OPT)b", "(*LIMIT_MATCH=2)ab|ba",
  ]),
]

let xpats = @["(?X)\\i", "(?X)a\\j", "(?X)\\y", "(?X)\\F", "(?X)[\\i]", "(?X)\\q",
  "a(?X)\\m", "(?X:\\i)", "(?X)(?-X)\\i", "(?X)\\_", "(?X)\\8", "(?X)\\T",
  "\\i(?X)", "(?X)\\Qi\\E", "(?X)\\c", "(?X)\\N", "(?X)\\M", "(?X)\\O", "(?X)\\I",
  "(?X)\\J", "(?X)\\Y", "(?X)[\\y]", "(?X)\\L", "(?X)\\u", "(?X)\\U", "(?X)\\l",
  "(?Xi)\\i", "(?iX)\\j", "(*UTF8)(?X)\\i", "(?X)", "(?X)a", "(?-X)\\i", "(?X)\\9",
  "(?X)[\\8]", "(?X)\\o", "(?X)\\o{1}", "(?X)\\x{1}", "(?X)[\\N]", "(?X)[\\j-k]"]

var jit: cint = 0
discard pcre.config(pcre.CONFIG_JIT, addr jit)
echo "JIT ", jit, " version ", pcre.version()

proc info(p: string) =
  var msg: cstring
  var off: cint
  let h = pcre.compile(p, 0, addr msg, addr off, nil)
  if h == nil:
    echo "INFO ", escape(p), " compile-error"
    return
  var smsg: cstring
  let e = pcre.study(h, (if jit == 1: pcre.STUDY_JIT_COMPILE else: 0), addr smsg)
  var opts: culong
  discard pcre.fullinfo(h, e, pcre.INFO_OPTIONS, addr opts)
  var fc, fcf, rc, rcf, minl, crlf: cint
  discard pcre.fullinfo(h, e, pcre.INFO_FIRSTCHARACTER, addr fc)
  discard pcre.fullinfo(h, e, pcre.INFO_FIRSTCHARACTERFLAGS, addr fcf)
  discard pcre.fullinfo(h, e, pcre.INFO_REQUIREDCHAR, addr rc)
  discard pcre.fullinfo(h, e, pcre.INFO_REQUIREDCHARFLAGS, addr rcf)
  discard pcre.fullinfo(h, e, pcre.INFO_MINLENGTH, addr minl)
  discard pcre.fullinfo(h, e, pcre.INFO_HASCRORLF, addr crlf)
  var tbl: ptr array[32, uint8]
  discard pcre.fullinfo(h, e, pcre.INFO_FIRSTTABLE, addr tbl)
  var bits = ""
  if tbl != nil:
    for b in 0 .. 255:
      if (tbl[b div 8] and uint8(1 shl (b mod 8))) != 0: bits.add toHex(b, 2)
  else: bits = "nil"
  echo "INFO ", escape(p), " anch=", (opts and 0x10) != 0, " fc=", fc, "/", fcf,
       " rc=", rc, "/", rcf, " min=", minl, " crlf=", crlf, " bits=", bits

proc res(s: string; rx: Regex; caps: bool): string =
  for st in -1 .. s.len + 1:
    result.add $find(s, rx, st) & ","
    result.add $matchLen(s, rx, st) & ","
    result.add $findBounds(s, rx, st) & ","
    result.add $int(match(s, rx, st)) & ","
    result.add $int(contains(s, rx, st)) & ","
    if caps:
      var m: array[3, string]
      for k in 0 .. 2: m[k] = "?"
      let fb = findBounds(s, rx, m, st)
      result.add $fb & $m & ","
  result.add replace(s, rx, "-").escape & ","
  result.add $int(endsWith(s, rx)) & $int(startsWith(s, rx))

var total = ""
for g in groups:
  let subs = words(g.alpha, g.maxLen)
  for p in g.pats:
    info(p)
    var rx: Regex
    try:
      rx = re(p)
    except RegexError as e:
      echo "PAT ", escape(p), " E:", escape(e.msg)
      total.add e.msg
      continue
    var all = ""
    var detail = ""
    for s in subs:
      let r = res(s, rx, '(' in p)
      all.add r & ";"
      if s.len <= 2: detail.add escape(s) & "=" & r & " "
    echo "PAT ", escape(p), " H:", toHex(fnv(all)), " D:", detail
    total.add all
for p in xpats:
  try:
    let rx = re(p)
    echo "XPAT ", escape(p), " ok ", int("ai\\".contains(rx)), int("_".contains(rx))
  except RegexError as e:
    echo "XPAT ", escape(p), " E:", escape(e.msg)
echo "TOTAL ", toHex(fnv(total))
