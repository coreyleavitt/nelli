## RFC-0016 K9d-9: the regex part of `pinFind`'s string domain.
##
## A SUT that matches a string against a regex literal (`re"..."`,
## `rex"..."`; std/re and std/nre alike) is pinned over strings near that
## pattern's language: its shortest members and the strings one step outside
## it. The fixed string core and the literal neighbours rarely reach either
## (a `[a-z]{3}` member is three lowercase letters, which the core holds only
## by accident).
##
## The pattern is read by a small parser of its own over the subset the walker
## models (literals, escapes, `.`, classes with ranges, negation and POSIX
## names, groups, alternation, the quantifiers with their lazy and possessive
## forms, `^ $ \A \z \Z \b \B`, and the leading `(*VERB)` items, which are
## zero-width here). It is deliberately not the walker's parser: a domain
## derived from the walker's own reading of a pattern would share its
## mistakes. A pattern outside the subset (a backreference, a lookaround, an
## inline option, an unread escape) yields no values and is recorded as
## outside; its SUT keeps the plain string domain.
##
## From the parse, deterministically and in priority order:
##
## 1. members: each node's representatives combined one factor at a time (a
##    class's first printable, lowest and highest byte; each alternation arm;
##    a quantifier at its min, min+1 and max);
## 2. boundaries: a member with a newline, CRLF, NUL or high byte after it,
##    and with a newline or high byte before it (where `^`, `$` and `.`
##    differ between PCRE and a naive reading), the empty string and "\n";
## 3. structural near-misses: a quantifier at min-1 and max+1, a class's
##    neighbouring bytes outside it, a literal's case swap and next byte, `.`
##    as a newline, each in the context of the canonical member;
## 4. case variants of the members when the pattern has letters;
## 5. one-edit neighbours of the shortest members: each byte deleted, a byte
##    inserted at each position (the byte itself, newline, NUL, 0xFF) and each
##    byte substituted (+1, -1, newline, 0xFF).
##
## Every stage holds at most `rxNodeCap` values per node and the whole set at
## most `regexDomainCap`; a value longer than `rxMaxLen` bytes is dropped.
import std/[strutils, sets]

const
  regexDomainCap* = 768
    ## the most values the regex part adds, however many patterns
  rxNodeCap = 24
  rxMaxLen = 64
  rxEditMembers = 4
  rxEditMaxLen = 12

type
  RxCon* = enum
    ## the constructs a pattern uses, as a record names them
    rcLit = "lit", rcEscape = "escape", rcDot = "dot", rcClass = "class",
    rcNegClass = "negclass", rcPosix = "posix", rcGroup = "group",
    rcAlt = "alt", rcStar = "star", rcPlus = "plus", rcOpt = "opt",
    rcBound = "bound", rcLazy = "lazy", rcBol = "bol", rcEol = "eol",
    rcWordB = "wordb", rcVerb = "verb", rcUtf = "utf", rcCodepoint = "codepoint"

  RxK = enum rkEmpty, rkLit, rkSet, rkAny, rkCat, rkAlt, rkRep, rkZero

  RxN = ref object
    case k: RxK
    of rkLit: s: string               # one byte, or a code point's UTF-8
    of rkSet:
      cs: set[char]
      cps: seq[string]                # code points past 0x7F, UTF mode
    of rkCat, rkAlt: kids: seq[RxN]
    of rkRep:
      sub: RxN
      lo, hi: int                     # hi < 0: unbounded
    of rkEmpty, rkAny, rkZero: discard

  RxParse* = object
    ok*: bool
    why*: string                      ## why a pattern is outside the subset
    cons*: set[RxCon]
    utf: bool
    root: RxN

  RxError = object of ValueError

  Parser = object
    p: string
    i: int
    utf: bool
    cons: set[RxCon]

proc fail(why: string) {.noreturn.} =
  raise newException(RxError, why)

proc utf8Of(cp: int): string =
  if cp < 0x80: result.add char(cp)
  elif cp < 0x800:
    result.add char(0xC0 or (cp shr 6))
    result.add char(0x80 or (cp and 0x3F))
  elif cp < 0x10000:
    result.add char(0xE0 or (cp shr 12))
    result.add char(0x80 or ((cp shr 6) and 0x3F))
    result.add char(0x80 or (cp and 0x3F))
  else:
    result.add char(0xF0 or (cp shr 18))
    result.add char(0x80 or ((cp shr 12) and 0x3F))
    result.add char(0x80 or ((cp shr 6) and 0x3F))
    result.add char(0x80 or (cp and 0x3F))

const
  digitSet = {'0' .. '9'}
  wordSet = {'a' .. 'z', 'A' .. 'Z', '0' .. '9', '_'}
  spaceSet = {' ', '\t', '\n', '\v', '\f', '\r'}
  allBytes = {'\0' .. '\xFF'}

proc posixSet(name: string): set[char] =
  case name
  of "alpha": {'a' .. 'z', 'A' .. 'Z'}
  of "digit": digitSet
  of "alnum": {'a' .. 'z', 'A' .. 'Z', '0' .. '9'}
  of "upper": {'A' .. 'Z'}
  of "lower": {'a' .. 'z'}
  of "space": spaceSet
  of "blank": {' ', '\t'}
  of "punct": {'!' .. '/', ':' .. '@', '[' .. '`', '{' .. '~'}
  of "xdigit": {'0' .. '9', 'a' .. 'f', 'A' .. 'F'}
  of "word": wordSet
  of "cntrl": {'\0' .. '\x1F', '\x7F'}
  of "print": {' ' .. '~'}
  of "graph": {'!' .. '~'}
  else: fail("posix class [:" & name & ":]")

proc more(ps: Parser): bool = ps.i < ps.p.len
proc peek(ps: Parser; o = 0): char =
  if ps.i + o < ps.p.len: ps.p[ps.i + o] else: '\0'

proc readHex(ps: var Parser): int =
  ## after `\x`: two hex digits, or `{h...}`
  if ps.peek == '{':
    inc ps.i
    var h = ""
    while ps.more and ps.peek != '}':
      h.add ps.peek
      inc ps.i
    if not ps.more or h.len == 0: fail("unterminated \\x{")
    inc ps.i
    try: result = parseHexInt(h)
    except ValueError: fail("\\x{" & h & "}")
    ps.cons.incl rcCodepoint
  else:
    var h = ""
    while h.len < 2 and ps.peek in HexDigits:
      h.add ps.peek
      inc ps.i
    result = if h.len == 0: 0 else: parseHexInt(h)

proc cpNode(ps: Parser; cp: int): RxN =
  if cp <= 0x7F or (cp <= 0xFF and not ps.utf): RxN(k: rkLit, s: $char(cp))
  elif ps.utf and cp <= 0x10FFFF: RxN(k: rkLit, s: utf8Of(cp))
  else: fail("code point " & $cp & " outside the mode")

proc escapeChar(c: char): int =
  ## a one-character escape's byte, or -1
  case c
  of 'n': 10
  of 't': 9
  of 'r': 13
  of 'f': 12
  of 'v': 11
  of 'a': 7
  of 'e': 27
  of '0': 0
  else: -1

proc classItem(ps: var Parser; cs: var set[char]; cps: var seq[string]):
    tuple[single: bool, c: int] =
  ## one class item; a single byte (or code point) is returned for a range
  let c = ps.peek
  if c == '[' and ps.peek(1) == ':':
    let j = ps.p.find(":]", ps.i + 2)
    if j < 0: fail("unterminated POSIX class")
    cs = cs + posixSet(ps.p[ps.i + 2 ..< j])
    ps.cons.incl rcPosix
    ps.i = j + 2
    return (false, 0)
  if c == '\\':
    inc ps.i
    let e = ps.peek
    inc ps.i
    ps.cons.incl rcEscape
    case e
    of 'd': cs = cs + digitSet
    of 'D': cs = cs + (allBytes - digitSet)
    of 'w': cs = cs + wordSet
    of 'W': cs = cs + (allBytes - wordSet)
    of 's': cs = cs + spaceSet
    of 'S': cs = cs + (allBytes - spaceSet)
    of 'x': return (true, ps.readHex)
    else:
      let b = escapeChar(e)
      if b >= 0: return (true, b)
      if e in Letters + Digits: fail("escape \\" & e & " in a class")
      return (true, ord(e))
    return (false, 0)
  inc ps.i
  (true, ord(c))

proc addCp(ps: Parser; cs: var set[char]; cps: var seq[string]; cp: int) =
  if cp <= 0x7F or (cp <= 0xFF and not ps.utf): cs.incl char(cp)
  elif ps.utf and cp <= 0x10FFFF:
    let u = utf8Of(cp)
    if u notin cps: cps.add u
  else: fail("code point " & $cp & " outside the mode")

proc parseClass(ps: var Parser): RxN =
  inc ps.i                           # '['
  var neg = false
  if ps.peek == '^':
    neg = true
    inc ps.i
  var cs: set[char]
  var cps: seq[string]
  var first = true
  while true:
    if not ps.more: fail("unterminated class")
    if ps.peek == ']' and not first: break
    first = false
    let a = ps.classItem(cs, cps)
    if not a.single: continue
    if ps.peek == '-' and ps.peek(1) != ']' and ps.i + 1 < ps.p.len:
      inc ps.i
      let b = ps.classItem(cs, cps)
      if not b.single: fail("range to a class")
      if b.c < a.c: fail("reversed range")
      for cp in a.c .. min(b.c, if ps.utf: 0x7F else: 0xFF): cs.incl char(cp)
      if ps.utf and b.c > 0x7F:
        # a code-point range: its two ends stand for it
        ps.addCp(cs, cps, max(a.c, 0x80))
        ps.addCp(cs, cps, b.c)
    else:
      ps.addCp(cs, cps, a.c)
  inc ps.i                           # ']'
  ps.cons.incl rcClass
  if neg:
    ps.cons.incl rcNegClass
    cs = allBytes - cs
    if ps.utf:
      cs = cs - {'\x80' .. '\xFF'}
      if "\xC3\xA9" notin cps: cps = @["\xC3\xA9"]   # a code point outside
      else: cps = @["\xE2\x82\xAC"]
    else: cps = @[]
  RxN(k: rkSet, cs: cs, cps: cps)

proc parseAlt(ps: var Parser): RxN

proc parseAtom(ps: var Parser): RxN =
  let c = ps.peek
  case c
  of '(':
    if ps.peek(1) == '*':
      let j = ps.p.find(')', ps.i)
      if j < 0: fail("unterminated verb")
      let v = ps.p[ps.i + 2 ..< j]
      if v in ["UTF", "UTF8"]:
        ps.utf = true
        ps.cons.incl rcUtf
      ps.cons.incl rcVerb
      ps.i = j + 1
      return RxN(k: rkZero)
    inc ps.i
    if ps.peek == '?':
      if ps.peek(1) == ':': ps.i += 2
      else: fail("group (?" & ps.peek(1) & "...")
    ps.cons.incl rcGroup
    let inner = ps.parseAlt
    if ps.peek != ')': fail("unterminated group")
    inc ps.i
    inner
  of '[': ps.parseClass
  of '.':
    inc ps.i
    ps.cons.incl rcDot
    RxN(k: rkAny)
  of '^':
    inc ps.i
    ps.cons.incl rcBol
    RxN(k: rkZero)
  of '$':
    inc ps.i
    ps.cons.incl rcEol
    RxN(k: rkZero)
  of '\\':
    inc ps.i
    let e = ps.peek
    inc ps.i
    ps.cons.incl rcEscape
    case e
    of 'd': RxN(k: rkSet, cs: digitSet)
    of 'D': RxN(k: rkSet, cs: allBytes - digitSet)
    of 'w': RxN(k: rkSet, cs: wordSet)
    of 'W': RxN(k: rkSet, cs: allBytes - wordSet)
    of 's': RxN(k: rkSet, cs: spaceSet)
    of 'S': RxN(k: rkSet, cs: allBytes - spaceSet)
    of 'b', 'B':
      ps.cons.incl rcWordB
      RxN(k: rkZero)
    of 'A':
      ps.cons.incl rcBol
      RxN(k: rkZero)
    of 'z', 'Z':
      ps.cons.incl rcEol
      RxN(k: rkZero)
    of 'x': ps.cpNode(ps.readHex)
    of '1' .. '9': fail("backreference \\" & e)
    else:
      let b = escapeChar(e)
      if b >= 0: RxN(k: rkLit, s: $char(b))
      elif e in Letters + Digits or e == '\0': fail("escape \\" & e)
      else: RxN(k: rkLit, s: $e)
  of '*', '+', '?': fail("quantifier with nothing to repeat")
  else:
    inc ps.i
    ps.cons.incl rcLit
    RxN(k: rkLit, s: $c)

proc readBound(ps: var Parser): tuple[ok: bool, lo, hi: int] =
  ## `{m}`, `{m,}`, `{m,n}` at `ps.i`; not a bound: a literal `{`
  var j = ps.i + 1
  var a, b = ""
  while j < ps.p.len and ps.p[j] in Digits:
    a.add ps.p[j]
    inc j
  if a.len == 0 or j >= ps.p.len: return
  if ps.p[j] == '}':
    ps.i = j + 1
    let n = parseInt(a)
    return (true, n, n)
  if ps.p[j] != ',': return
  inc j
  while j < ps.p.len and ps.p[j] in Digits:
    b.add ps.p[j]
    inc j
  if j >= ps.p.len or ps.p[j] != '}': return
  ps.i = j + 1
  let lo = parseInt(a)
  let hi = if b.len == 0: -1 else: parseInt(b)
  if hi >= 0 and hi < lo: fail("bound {" & a & "," & b & "}")
  (true, lo, hi)

proc parseQuant(ps: var Parser): RxN =
  result = ps.parseAtom
  while ps.more:
    var lo, hi: int
    case ps.peek
    of '*':
      inc ps.i
      (lo, hi) = (0, -1)
      ps.cons.incl rcStar
    of '+':
      inc ps.i
      (lo, hi) = (1, -1)
      ps.cons.incl rcPlus
    of '?':
      inc ps.i
      (lo, hi) = (0, 1)
      ps.cons.incl rcOpt
    of '{':
      let b = ps.readBound
      if not b.ok: return
      (lo, hi) = (b.lo, b.hi)
      ps.cons.incl rcBound
    else: return
    if ps.peek in {'?', '+'}:
      inc ps.i
      ps.cons.incl rcLazy
    if result.k == rkZero: continue   # a repeated zero-width item
    result = RxN(k: rkRep, sub: result, lo: lo, hi: hi)

proc parseCat(ps: var Parser): RxN =
  var kids: seq[RxN]
  while ps.more and ps.peek notin {'|', ')'}:
    kids.add ps.parseQuant
  if kids.len == 0: RxN(k: rkEmpty)
  elif kids.len == 1: kids[0]
  else: RxN(k: rkCat, kids: kids)

proc parseAlt(ps: var Parser): RxN =
  var arms = @[ps.parseCat]
  while ps.peek == '|' and ps.more:
    inc ps.i
    ps.cons.incl rcAlt
    arms.add ps.parseCat
  if arms.len == 1: arms[0] else: RxN(k: rkAlt, kids: arms)

proc parseRegex*(pat: string): RxParse =
  ## `pat` read over the modelled subset; `ok` false (with `why`) outside it
  var ps = Parser(p: pat)
  try:
    let root = ps.parseAlt
    if ps.more: fail("unbalanced ')'")
    RxParse(ok: true, cons: ps.cons, utf: ps.utf, root: root)
  except RxError as e:
    RxParse(ok: false, why: e.msg, cons: ps.cons)

# --- generation --------------------------------------------------------------

type Gen = tuple[mem, miss: seq[string]]

proc putCapped(s: var seq[string]; v: string) =
  if s.len < rxNodeCap and v.len <= rxMaxLen and v notin s: s.add v

proc reps(cs: set[char]): seq[string] =
  ## a set's representatives: its first printable, lowest, highest byte
  var lo, hi, pr = -1
  for c in cs:
    if lo < 0: lo = ord(c)
    hi = ord(c)
    if pr < 0 and c in {'!' .. '~'}: pr = ord(c)
  for x in [pr, lo, hi]:
    if x >= 0 and $char(x) notin result: result.add $char(x)

proc outside(cs: set[char]): seq[string] =
  ## the bytes just outside each run of the set
  var prev = false
  for x in 0 .. 255:
    let inn = char(x) in cs
    if inn and not prev and x > 0: result.putCapped $char(x - 1)
    if not inn and prev: result.putCapped $char(x)
    prev = inn
  if result.len > 4: result.setLen 4

proc swapCase(c: char): char =
  if c in {'a' .. 'z'}: char(ord(c) - 32)
  elif c in {'A' .. 'Z'}: char(ord(c) + 32)
  else: c

proc gen(n: RxN; utf: bool): Gen =
  case n.k
  of rkEmpty, rkZero:
    result.mem = @[""]
  of rkLit:
    result.mem = @[n.s]
    if n.s.len == 1:
      let c = n.s[0]
      if swapCase(c) != c: result.miss.putCapped $swapCase(c)
      result.miss.putCapped $char((ord(c) + 1) and 255)
  of rkSet:
    # in UTF mode a lone byte past 0x7F is not a code point: no member
    let hi = if utf: n.cs * {'\x80' .. '\xFF'} else: {}
    result.mem = reps(n.cs - hi)
    for u in n.cps: result.mem.putCapped u
    result.miss = outside(n.cs)
    for v in reps(hi): result.miss.putCapped v
  of rkAny:
    # one code point: a multi-byte one is one `.` only in UTF mode, and a
    # lone high byte only outside it
    if utf:
      result.mem = @["a", "\xC3\xA9"]
      result.miss = @["\n", "\x80"]
    else:
      result.mem = @["a", "\x80"]
      result.miss = @["\n", "\xC3\xA9"]
  of rkCat:
    var gs: seq[Gen]
    for k in n.kids: gs.add gen(k, utf)
    for g in gs:
      if g.mem.len == 0: return     # an empty language: no member, no context
    var base = ""
    for g in gs: base.add g.mem[0]
    result.mem.putCapped base
    proc around(i: int; v: string): string =
      for j, g in gs:
        result.add(if j == i: v else: g.mem[0])
    for i, g in gs:
      for v in g.mem[1 .. ^1]: result.mem.putCapped around(i, v)
    for i, g in gs:
      for v in g.miss: result.miss.putCapped around(i, v)
  of rkAlt:
    var gs: seq[Gen]
    for k in n.kids: gs.add gen(k, utf)
    for g in gs:
      if g.mem.len > 0: result.mem.putCapped g.mem[0]
    for g in gs:
      for v in g.mem: result.mem.putCapped v
    for g in gs:
      for v in g.miss: result.miss.putCapped v
  of rkRep:
    let g = gen(n.sub, utf)
    if g.mem.len == 0:
      if n.lo == 0: result.mem = @[""]
      return
    let unit = g.mem[0]
    var counts = @[n.lo, n.lo + 1]
    if n.hi >= 0: counts.add n.hi
    else: counts.add n.lo + 2
    for k in counts:
      if (n.hi < 0 or k <= n.hi) and unit.len * k <= rxMaxLen:
        result.mem.putCapped unit.repeat(k)
    let k1 = max(n.lo, 1)
    if n.hi < 0 or k1 <= n.hi:
      for v in g.mem[1 .. ^1]:
        result.mem.putCapped unit.repeat(k1 - 1) & v
      for v in g.miss:
        result.miss.putCapped unit.repeat(k1 - 1) & v
    if n.lo > 0: result.miss.putCapped unit.repeat(n.lo - 1)
    if n.hi >= 0 and unit.len * (n.hi + 1) <= rxMaxLen:
      result.miss.putCapped unit.repeat(n.hi + 1)

proc hasLetters(pat: string): bool =
  var i = 0
  while i < pat.len:
    if pat[i] == '\\': i += 2; continue   # an escape's letter is not data
    if pat[i] in Letters: return true
    inc i

proc regexStages*(pats: openArray[string]): array[5, seq[string]] =
  ## the five stages (see the module doc) over every pattern in the subset,
  ## each stage pattern-major, deduplicated within the stage
  var gens: seq[tuple[g: Gen, letters: bool]]
  for p in pats:
    let r = parseRegex(p)
    if r.ok: gens.add (gen(r.root, r.utf), hasLetters(p))
  template add(st: int; v: string) =
    if v.len <= rxMaxLen and v notin result[st]: result[st].add v
  for x in gens:
    for m in x.g.mem: add(0, m)
  if gens.len > 0:
    add(1, "")
    add(1, "\n")
  for x in gens:
    for m in x.g.mem[0 ..< min(4, x.g.mem.len)]:
      for v in [m & "\n", "\n" & m, m & "\r\n", m & "\0", m & "\xFF",
                "\x80" & m]:
        add(1, v)
  for x in gens:
    for m in x.g.miss: add(2, m)
  for x in gens:
    if not x.letters: continue
    for m in x.g.mem[0 ..< min(8, x.g.mem.len)]:
      add(3, m.toUpperAscii)
      add(3, m.toLowerAscii)
      for i, c in m:
        if swapCase(c) != c:
          var v = m
          v[i] = swapCase(c)
          add(3, v)
          break
  for x in gens:
    var short: seq[string]
    for m in x.g.mem:
      if m.len in 1 .. rxEditMaxLen and short.len < rxEditMembers: short.add m
    for m in short:
      for i in 0 ..< m.len: add(4, m[0 ..< i] & m[i + 1 .. ^1])
      for i in 0 .. m.len:
        let dup = if i < m.len: m[i] else: m[^1]
        for b in [dup, '\n', '\0', '\xFF']: add(4, m[0 ..< i] & $b & m[i .. ^1])
      for i in 0 ..< m.len:
        for b in [char((ord(m[i]) + 1) and 255), char((ord(m[i]) + 255) and 255),
                  '\n', '\xFF']:
          var v = m
          v[i] = b
          add(4, v)

proc regexValues*(pats: openArray[string]): seq[string] =
  ## the regex part of the string domain: the five stages in order, at most
  ## `regexDomainCap` values
  var seen = initHashSet[string]()
  for st in regexStages(pats):
    for v in st:
      if result.len >= regexDomainCap: return
      if not seen.containsOrIncl(v): result.add v

proc regexSummary*(pats: openArray[string]): string =
  ## what a record says of the patterns: how many, how many outside the
  ## subset, and the constructs the modelled ones use
  if pats.len == 0: return ""
  var cons: set[RxCon]
  var outside = 0
  for p in pats:
    let r = parseRegex(p)
    if r.ok: cons = cons + r.cons
    else: inc outside
  var names: seq[string]
  for c in cons: names.add $c
  " regex[" & $pats.len & " patterns, " & $outside & " outside]{" &
    names.join(",") & "}"
