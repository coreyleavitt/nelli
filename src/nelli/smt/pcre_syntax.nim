## RFC-0005 S8ay. A byte-level reader of PCRE 8.45 pattern syntax as Nim's
## `std/re` compiles it (`re"..."`: flags `{reStudy}`, no UTF, no UCP;
## `rex"..."` adds `reExtended`).
##
## Pure Nim (no Z3), so the compile-time parser (`dsl_parser.nim`) can tell a
## pattern PCRE rejects -- `re"..."` raising `RegexError` at run time -- and
## the walker (`regex_parser.nim`, `runtime_strings.nim`) can build the Z3
## language of an accepted one from the same reading.
##
## Four outcomes (`PcreStatus`):
##   * `psOk`         -- accepted, and every construct is modelled: `root`
##                       is the pattern's tree;
##   * `psUnmodelled` -- accepted by PCRE (the reader went through the whole
##                       pattern and found no rejection), but a construct
##                       has no model here (a back-reference, a lookaround,
##                       a possessive quantifier, an anchor away from a
##                       top-level edge, ...). `reason` names the first;
##   * `psRejected`   -- PCRE rejects it: `errMsg` is the exact
##                       `RegexError.msg` Nim raises (PCRE's message, the
##                       pattern, and a caret at PCRE's error offset);
##   * `psUnknown`    -- the reader stopped at a construct whose validity
##                       or meaning it does not decide (`\X`, `\R`, the
##                       `m` and `X` options, a backtracking verb, a UTF or
##                       newline-convention start option, ...). Neither
##                       accepted nor rejected.
##
## Every outcome other than `psUnknown` is pinned against the real `re`/
## `rex` by the differential corpus in
## `tests/tsymex_rfc0005_s8ay_remainder.nim`.
##
## PCRE semantics the tree carries (all verified concretely, RFC-0005 S8ay):
##   * `.` is every byte but `\n`; `\N` is `.`.
##   * `\d \w \s` are ASCII (`\s` = HT LF VT FF CR SP), `\D \W \S` their
##     complements over all 256 bytes; `\h` = {HT SP 0xA0}, `\v` = {LF VT FF
##     CR 0x85}, `\H \V` complements.
##   * `^` / `\A` match at subject position 0 only (never at a non-zero
##     `start`); `$` / `\Z` match at the end or before a final `\n`; `\z` at
##     the end only.
##   * `rex` skips whitespace (SP HT LF VT FF CR) and `#` comments up to LF
##     outside classes, including between an atom and its quantifier.
##
## RFC-0005 S8bb adds (each probed against PCRE 8.45, and pinned by
## `tests/tsymex_rfc0005_s8bb_selection.nim`):
##   * named groups `(?<n>..)`, `(?P<n>..)`, `(?'n'..)` are capturing groups
##     (a repeated name stays undecided);
##   * inline options `i s x U J` and their `-` forms, as `(?..)` (to the end
##     of the enclosing group, across its later alternatives) or `(?..:..)`;
##     `i` adds the other case of each ASCII letter to a literal, an
##     escape's byte and each byte or range of a class, and reads
##     `[:upper:]` / `[:lower:]` as `[:alpha:]`; class escapes and `\p` are
##     unchanged;
##   * `\p{X}` `\P{X}` `\p{^X}` `\pX` are byte sets (`pcre_props.nim`):
##     without UTF a byte is the code point of its value;
##   * start options `(*UCP)` (the `\w \s` and POSIX sets of
##     `pcre_props.nim`), `(*LF)`, `(*NO_START_OPT)`, `(*NO_AUTO_POSSESS)`,
##     `(*BSR_ANYCRLF)`, `(*BSR_UNICODE)` (none changes a modelled
##     construct's meaning; `\R` stays undecided); `(*F)` / `(*FAIL)`
##     never match; `(*MARK:n)` / `(*:n)` change no match;
##   * the newline conventions `(*CR)`, `(*CRLF)`, `(*ANYCRLF)`, `(*ANY)`
##     (`nl`; the last one given wins): `.` and `\N` exclude the
##     convention's newline bytes (`nlBytes`; under `(*CRLF)` a CR only
##     when an LF follows it -- `rxSet.crlfDot`), and `$` / `\Z` hold at
##     the end or before a final newline SEQUENCE (CRLF is one). `hasCrLf`
##     is PCRE_HASCRORLF (an explicit CR or LF in the pattern: a literal
##     byte, a one-byte escape, a class member or a range end; not `\s`,
##     `\v`, a property or a range interior -- probed), which turns off
##     the bumpalong's CRLF skip;
##   * `(*ACCEPT)` (`rxAccept`) ends the match where it is reached, closing
##     the capturing groups it is in.
##
## Still undecided (RFC-0005 S8bb, the evidence in its "As landed"):
## `(*COMMIT)`, `(*PRUNE)`, `(*SKIP)`, `(*THEN)` and `(*LIMIT_...)`, whose
## outcome depends on PCRE's start-of-match optimisations and its internal
## call count (`(*COMMIT)abc` on "xyzabc" finds 3, with `(*NO_START_OPT)`
## -1); `(*UTF)` / `(*UTF8)` (a code-point subject model).

import std/strutils
import ./pcre_props

type
  RxKind* = enum
    rxSet      ## one byte from `bytes`
    rxCat      ## `kids` in sequence (empty: the empty string)
    rxAlt      ## any of `kids`
    rxRep      ## `sub` repeated `lo .. hi` times (`hi == -1`: unbounded)
    rxBol      ## `^` / `\A`
    rxEol      ## `$` / `\Z`: end, or before a final `\n`
    rxEolAbs   ## `\z`: end only
    rxAccept   ## RFC-0005 S8bb: `(*ACCEPT)`

  Rx* = ref object
    cap*: int          ## RFC-0005 S8bb: the capturing group this node is
                       ## the body of (1-based), 0 if none
    case kind*: RxKind
    of rxSet:
      bytes*: set[char]
      crlfDot*: bool   ## RFC-0005 S8bb: `.` / `\N` under `(*CRLF)`: a CR
                       ## only when no LF follows it
    of rxCat, rxAlt:
      kids*: seq[Rx]
    of rxRep:
      sub*: Rx
      lo*, hi*: int
      lazy*: bool       ## `*?` etc.; irrelevant to the language
    of rxBol, rxEol, rxEolAbs:
      discard
    of rxAccept:
      open*: seq[int]   ## the capturing groups it is in

  PcreStatus* = enum
    psOk, psUnmodelled, psRejected, psUnknown

  NlConv* = enum
    ## RFC-0005 S8bb: the newline convention (a start option).
    nlLF, nlCR, nlCRLF, nlANY, nlANYCRLF

  PcreParse* = object
    status*: PcreStatus
    root*: Rx          ## psOk: the tree
    groups*: int       ## psOk: capturing groups (RFC-0005 S8bb)
    nl*: NlConv        ## psOk: the newline convention (RFC-0005 S8bb)
    hasCrLf*: bool     ## psOk: PCRE_HASCRORLF (RFC-0005 S8bb)
    errMsg*: string    ## psRejected: Nim's exact `RegexError.msg`
    reason*: string    ## psUnmodelled / psUnknown: the construct

const
  pcreDigit* = {'0'..'9'}
  pcreWord* = {'a'..'z', 'A'..'Z', '0'..'9', '_'}
  pcreSpace* = {'\t', '\n', '\v', '\f', '\r', ' '}
  pcreHSpace* = {'\t', ' ', '\xA0'}
  pcreVSpace* = {'\n', '\v', '\f', '\r', '\x85'}
  pcreAnyByte* = {'\x00'..'\xFF'}
  pcreDot* = pcreAnyByte - {'\n'}
  xSpace = {' ', '\t', '\n', '\v', '\f', '\r'}
    ## Skipped by `rex` outside a class (VT since PCRE 8.34; NEL and NBSP
    ## are literal -- probed).

proc nlBytes*(nl: NlConv): set[char] =
  ## RFC-0005 S8bb. The bytes that are a newline on their own.
  case nl
  of nlLF: {'\n'}
  of nlCR: {'\r'}
  of nlCRLF: {}
  of nlANYCRLF: {'\n', '\r'}
  of nlANY: {'\n', '\v', '\f', '\r', '\x85'}

proc nlPair*(nl: NlConv): bool =
  ## RFC-0005 S8bb. CRLF is a (two-byte) newline.
  nl in {nlCRLF, nlANYCRLF, nlANY}

proc posixSet(name: string): (bool, set[char]) =
  ## PCRE's default (C-locale) character tables.
  case name
  of "alpha": (true, {'a'..'z', 'A'..'Z'})
  of "lower": (true, {'a'..'z'})
  of "upper": (true, {'A'..'Z'})
  of "alnum": (true, {'a'..'z', 'A'..'Z', '0'..'9'})
  of "ascii": (true, {'\x00'..'\x7F'})
  of "blank": (true, {'\t', ' '})
  of "cntrl": (true, {'\x00'..'\x1F', '\x7F'})
  of "digit": (true, pcreDigit)
  of "graph": (true, {'\x21'..'\x7E'})
  of "print": (true, {'\x20'..'\x7E'})
  of "punct": (true, {'\x21'..'\x7E'} - {'a'..'z', 'A'..'Z', '0'..'9'})
  of "space": (true, pcreSpace)
  of "word": (true, pcreWord)
  of "xdigit": (true, {'0'..'9', 'a'..'f', 'A'..'F'})
  else: (false, {})

type
  Stop = object of CatchableError
    ## Internal: unwinds the recursive descent on a rejection or an unknown
    ## construct. Caught once, in `parsePcre`.

  Reader = object
    pat: string
    i: int
    ext: bool
    groups: int          ## capturing groups opened so far
    maxBackref: int      ## highest `\n` back-reference seen
    unmodelled: string   ## first unmodelled construct, "" if none
    status: PcreStatus   ## set on Stop
    errMsg, reason: string
    # RFC-0005 S8bb: the options in force (`(?isxU)`, `(*UCP)`).
    caseless, dotall, ungreedy, ucp: bool
    names: seq[string]   ## named groups so far
    nl: NlConv           ## the newline convention
    hasCrLf: bool        ## PCRE_HASCRORLF
    open: seq[int]       ## the capturing groups being read

proc reject(r: var Reader; msg: string; offset: int) {.noreturn.} =
  r.status = psRejected
  # Nim's `rawCompile`: `msg & "\n" & pattern & "\n" & spaces(offset) & "^\n"`.
  r.errMsg = msg & "\n" & r.pat & "\n" & spaces(offset) & "^\n"
  raise newException(Stop, "")

proc unknown(r: var Reader; why: string) {.noreturn.} =
  r.status = psUnknown
  r.reason = why
  raise newException(Stop, "")

proc unmodelled(r: var Reader; why: string) =
  if r.unmodelled.len == 0: r.unmodelled = why

proc atEnd(r: Reader): bool = r.i >= r.pat.len
proc cur(r: Reader): char = (if r.i < r.pat.len: r.pat[r.i] else: '\0')
proc at(r: Reader; k: int): char =
  (if r.i + k < r.pat.len and r.i + k >= 0: r.pat[r.i + k] else: '\0')

proc skipX(r: var Reader) =
  ## `rex`: whitespace and `#`-to-LF comments outside a class.
  if not r.ext: return
  while not r.atEnd:
    if r.cur in xSpace:
      inc r.i
    elif r.cur == '#':
      while not r.atEnd and r.cur != '\n': inc r.i
    else:
      break

proc mkSet(s: set[char]): Rx = Rx(kind: rxSet, bytes: s)

proc mkDot(r: Reader; dotall: bool): Rx =
  ## RFC-0005 S8bb. `.` (`dotall`: under `(?s)`) or `\N` (never dotall).
  if dotall: return mkSet(pcreAnyByte)
  Rx(kind: rxSet, bytes: pcreAnyByte - nlBytes(r.nl),
     crlfDot: r.nl == nlCRLF)

proc noteByte(r: var Reader; c: char) =
  ## RFC-0005 S8bb. PCRE_HASCRORLF: an explicit CR or LF.
  if c in {'\r', '\n'}: r.hasCrLf = true

proc fold(s: set[char]): set[char] =
  ## RFC-0005 S8bb. `s` with the other case of each ASCII letter (PCRE's
  ## default tables fold no byte above 0x7F -- probed).
  result = s
  for c in s:
    if c in {'a'..'z'}: result.incl char(ord(c) - 32)
    elif c in {'A'..'Z'}: result.incl char(ord(c) + 32)

proc foldIf(r: Reader; s: set[char]): set[char] =
  (if r.caseless: fold(s) else: s)
proc mkCat(kids: seq[Rx]): Rx = Rx(kind: rxCat, kids: kids)

proc isHex(c: char): bool = c in {'0'..'9', 'a'..'f', 'A'..'F'}

type EscKind = enum
  ekByte      ## a single byte
  ekSet       ## a byte set (`\d` ...)
  ekBol, ekEol, ekEolAbs
  ekAssert    ## `\b \B \G`: zero-width, unmodelled, not quantifiable
  ekBackref   ## `\1`..`\7`
  ekQuote     ## `\Q`
  ekQuoteEnd  ## `\E`
  ekDot       ## `\N` (RFC-0005 S8bb: the convention decides it)

type Esc = object
  kind: EscKind
  b: char
  s: set[char]
  n: int

proc readEscape(r: var Reader; inClass: bool): Esc =
  ## `r.cur == '\\'`. Leaves `r.i` past the escape. Every branch was probed
  ## against PCRE 8.45 (RFC-0005 S8ay); escapes it does not decide stop as
  ## `psUnknown`.
  inc r.i
  if r.atEnd:
    r.reject("\\ at end of pattern", r.pat.len)
  let c = r.cur
  inc r.i
  case c
  of 'a': Esc(kind: ekByte, b: '\a')
  of 'e': Esc(kind: ekByte, b: '\e')
  of 'f': Esc(kind: ekByte, b: '\f')
  of 'n': Esc(kind: ekByte, b: '\n')
  of 'r': Esc(kind: ekByte, b: '\r')
  of 't': Esc(kind: ekByte, b: '\t')
  of 'd': Esc(kind: ekSet, s: pcreDigit)
  of 'D': Esc(kind: ekSet, s: pcreAnyByte - pcreDigit)
  of 'w', 'W', 's', 'S':
    # RFC-0005 S8bb: `(*UCP)` reads them as Unicode properties.
    let (u, us) = (if r.ucp: pcreUcpSet("\\" & c) else: (false, {}))
    if u: Esc(kind: ekSet, s: us)
    else:
      case c
      of 'w': Esc(kind: ekSet, s: pcreWord)
      of 'W': Esc(kind: ekSet, s: pcreAnyByte - pcreWord)
      of 's': Esc(kind: ekSet, s: pcreSpace)
      else: Esc(kind: ekSet, s: pcreAnyByte - pcreSpace)
  of 'p', 'P':
    # RFC-0005 S8bb: `\p{X}` `\p{^X}` `\pX`, `\P` the complement.
    var name = ""
    if r.cur == '{':
      let close = r.pat.find('}', r.i)
      if close < 0: r.unknown("the escape \\" & c & " without a closing }")
      name = r.pat[r.i + 1 ..< close]
      r.i = close + 1
    elif r.atEnd:
      r.unknown("the escape \\" & c & " at the end")
    else:
      name = $r.cur
      inc r.i
    var neg = c == 'P'
    if name.len > 0 and name[0] == '^':
      neg = not neg
      name = name[1 .. ^1]
    let (known, ps) = pcrePropSet(name)
    if not known: r.unknown("the property \\" & c & "{" & name & "}")
    Esc(kind: ekSet, s: (if neg: pcreAnyByte - ps else: ps))
  of 'h': Esc(kind: ekSet, s: pcreHSpace)
  of 'H': Esc(kind: ekSet, s: pcreAnyByte - pcreHSpace)
  of 'v': Esc(kind: ekSet, s: pcreVSpace)
  of 'V': Esc(kind: ekSet, s: pcreAnyByte - pcreVSpace)
  of 'b':
    if inClass: Esc(kind: ekByte, b: '\b')
    else: Esc(kind: ekAssert)
  of 'B', 'G':
    if inClass: r.unknown("the escape \\" & c & " in a class")
    Esc(kind: ekAssert)
  of 'A':
    if inClass: r.unknown("the escape \\A in a class")
    Esc(kind: ekBol)
  of 'Z':
    if inClass: r.unknown("the escape \\Z in a class")
    Esc(kind: ekEol)
  of 'z':
    if inClass: r.unknown("the escape \\z in a class")
    Esc(kind: ekEolAbs)
  of 'N':
    if inClass:
      r.reject("\\N is not supported in a class", r.i - 1)
    if r.cur == '{':
      r.unknown("the escape \\N{...}")
    Esc(kind: ekDot)
  of 'Q':
    if inClass: r.unknown("\\Q in a class")
    Esc(kind: ekQuote)
  of 'E':
    if inClass: r.unknown("\\E in a class")
    Esc(kind: ekQuoteEnd)
  of 'x':
    if r.cur == '{':
      # `\x{h..}`: modelled only as one or two hex digits and `}`.
      var j = r.i + 1
      var v = 0
      var nd = 0
      while j < r.pat.len and isHex(r.pat[j]) and nd < 3:
        v = v * 16 + parseHexInt($r.pat[j])
        inc j
        inc nd
      if nd in 1..2 and j < r.pat.len and r.pat[j] == '}':
        r.i = j + 1
        return Esc(kind: ekByte, b: char(v))
      r.unknown("the escape \\x{...} beyond two hex digits")
    var v = 0
    var nd = 0
    while nd < 2 and isHex(r.cur):
      v = v * 16 + parseHexInt($r.cur)
      inc r.i
      inc nd
    Esc(kind: ekByte, b: char(v))
  of 'c':
    if r.atEnd:
      r.reject("\\c at end of pattern", r.pat.len)
    let x = r.cur
    if ord(x) > 127:
      r.reject("\\c must be followed by an ASCII character", r.i)
    inc r.i
    Esc(kind: ekByte, b: char(ord(toUpperAscii(x)) xor 0x40))
  of '0':
    # Up to two further octal digits.
    var v = 0
    var nd = 0
    while nd < 2 and r.cur in {'0'..'7'}:
      v = v * 8 + (ord(r.cur) - ord('0'))
      inc r.i
      inc nd
    Esc(kind: ekByte, b: char(v))
  of '1'..'7':
    if inClass or r.cur in {'0'..'9'}:
      r.unknown("the escape \\" & c & r.cur & " (octal or back-reference)")
    Esc(kind: ekBackref, n: ord(c) - ord('0'))
  of '8', '9':
    r.unknown("the escape \\" & c)
  of 'L', 'l', 'U', 'u':
    r.unknown("the escape \\" & c)
  of 'C', 'K', 'R', 'X', 'g', 'k', 'o':
    r.unknown("the escape \\" & c)
  of 'i', 'j', 'm', 'q', 'y', 'F', 'I', 'J', 'M', 'O', 'T', 'Y':
    # PCRE without PCRE_EXTRA: an unrecognised letter escape is the letter.
    Esc(kind: ekByte, b: c)
  else:
    if c in {'a'..'z', 'A'..'Z', '0'..'9'}:
      r.unknown("the escape \\" & c)
    # `\` before a non-alphanumeric byte is that byte.
    Esc(kind: ekByte, b: c)

proc checkPosixSyntax(r: Reader; start: int): int =
  ## PCRE's `check_posix_syntax` at `pat[start] == '['` with `pat[start+1]`
  ## one of `:.=`: the index of the terminator (`:` `.` `=`) before the
  ## closing `]`, or -1 when it is not POSIX syntax.
  let term = r.pat[start + 1]
  var j = start + 2
  while j < r.pat.len:
    let c = r.pat[j]
    if c == '\\' and j + 1 < r.pat.len and r.pat[j + 1] in {']', '\\'}:
      j += 2
      continue
    if (c == '[' and j + 1 < r.pat.len and r.pat[j + 1] == term) or c == ']':
      return -1
    if c == term and j + 1 < r.pat.len and r.pat[j + 1] == ']':
      return j
    inc j
  -1

proc readClass(r: var Reader): set[char] =
  ## `r.cur == '['` outside a class. Leaves `r.i` past the closing `]`.
  inc r.i
  var negated = false
  if r.cur == '^':
    negated = true
    inc r.i
  var cs: set[char]
  var first = true
  while true:
    if r.atEnd:
      r.reject("missing terminating ] for character class", r.pat.len)
    let c = r.cur
    if c == ']' and not first:
      inc r.i
      break
    first = false
    # One item: a byte (`loCh`, range-able) or a set.
    var isByte = true
    var loCh = c
    var itemSet: set[char]
    if c == '[' and r.at(1) in {':', '.', '='}:
      let t = r.checkPosixSyntax(r.i)
      if t >= 0:
        if r.at(1) != ':':
          r.unknown("a POSIX collating element")
        var name = r.pat[r.i + 2 ..< t]
        var neg = false
        if name.len > 0 and name[0] == '^':
          neg = true
          name = name[1 .. ^1]
        var (ok, ps) = posixSet(name)
        if not ok:
          r.unknown("the POSIX class [:" & name & ":]")
        # RFC-0005 S8bb: caseless reads upper / lower as alpha; `(*UCP)`
        # reads the class as a Unicode property.
        if r.caseless and name in ["upper", "lower"]:
          name = "alpha"
          ps = posixSet(name)[1]
        if r.ucp:
          let (u, us) = pcreUcpSet("[[:" & name & ":]]")
          if u: ps = us
        r.i = t + 2
        isByte = false
        itemSet = (if neg: pcreAnyByte - ps else: ps)
        if r.cur == '-' and r.at(1) != ']':
          r.unknown("a range after a POSIX class")
      else:
        inc r.i
    elif c == '\\':
      let e = r.readEscape(inClass = true)
      case e.kind
      of ekByte: loCh = e.b
      of ekSet:
        isByte = false
        itemSet = e.s
      else: r.unknown("an escape in a class")
    else:
      inc r.i
    if isByte: r.noteByte(loCh)
    if not isByte:
      # PCRE: `-` after a class escape is a literal (`[\d-z]`).
      cs = cs + itemSet
      continue
    if r.cur == '-' and r.i + 1 < r.pat.len and r.at(1) != ']':
      # A range `lo-hi`.
      inc r.i
      var hiCh = r.cur
      if hiCh == '[' and r.at(1) in {':', '.', '='} and
         r.checkPosixSyntax(r.i) >= 0:
        r.unknown("a range to a POSIX class")
      if hiCh == '\\':
        let e = r.readEscape(inClass = true)
        case e.kind
        of ekByte: hiCh = e.b
        of ekSet:
          r.reject("invalid range in character class", r.i - 1)
        else: r.unknown("an escape ending a range")
      else:
        inc r.i
      if hiCh < loCh:
        r.reject("range out of order in character class", r.i - 1)
      r.noteByte(hiCh)
      cs = cs + r.foldIf({loCh .. hiCh})
    else:
      cs = cs + r.foldIf({loCh})
  if negated: pcreAnyByte - cs else: cs

proc isCountedRepeat(r: Reader; j: int): bool =
  ## PCRE's `is_counted_repeat` at `pat[j-1] == '{'`.
  var k = j
  if k >= r.pat.len or r.pat[k] notin pcreDigit: return false
  while k < r.pat.len and r.pat[k] in pcreDigit: inc k
  if k < r.pat.len and r.pat[k] == '}': return true
  if k >= r.pat.len or r.pat[k] != ',': return false
  inc k
  if k < r.pat.len and r.pat[k] == '}': return true
  if k >= r.pat.len or r.pat[k] notin pcreDigit: return false
  while k < r.pat.len and r.pat[k] in pcreDigit: inc k
  k < r.pat.len and r.pat[k] == '}'

proc readCounts(r: var Reader): (int, int) =
  ## PCRE's `read_repeat_counts`, `r.cur == '{'` and `isCountedRepeat`.
  ## Leaves `r.i` AT the closing `}` (PCRE's error offset for a following
  ## "nothing to repeat").
  inc r.i
  var lo = 0
  while r.cur in pcreDigit:
    lo = lo * 10 + (ord(r.cur) - ord('0'))
    inc r.i
    if lo > 65535:
      r.reject("number too big in {} quantifier", r.i)
  var hi = lo
  if r.cur != '}':
    inc r.i   # the ','
    if r.cur == '}':
      hi = -1
    else:
      hi = 0
      while r.cur in pcreDigit:
        hi = hi * 10 + (ord(r.cur) - ord('0'))
        inc r.i
        if hi > 65535:
          r.reject("number too big in {} quantifier", r.i)
      if hi < lo:
        r.reject("numbers out of order in {} quantifier", r.i)
  (lo, hi)

proc readAlt(r: var Reader; depth: int): Rx

proc readOptions(r: var Reader) =
  ## RFC-0005 S8bb. At `(?` + option letters: sets / unsets `i s x U J`,
  ## leaving `r.i` at the `)` or `:`. `m` (multiline) and `X`
  ## (PCRE_EXTRA) are undecided.
  var j = r.i + 2
  var on = true
  while j < r.pat.len and r.pat[j] notin {')', ':'}:
    case r.pat[j]
    of '-': on = false
    of 'i': r.caseless = on
    of 's': r.dotall = on
    of 'x': r.ext = on
    of 'U': r.ungreedy = on
    of 'J': discard   # duplicate names, which stay undecided anyway
    else: r.unknown("the inline option " & r.pat[j])
    inc j
  if j >= r.pat.len: r.unknown("an unterminated option setting")
  r.i = j

type Prev = enum
  pvNone       ## nothing to repeat (start, after `|`, `(`, an anchor, a
               ## quantifier)
  pvAtom       ## a quantifiable item, last in `items`
  pvOpaque     ## a quantifiable unmodelled item (no tree)

proc readCat(r: var Reader; depth: int): Rx =
  ## One alternative, up to `|`, `)` or the end.
  var items: seq[Rx]
  var prev = pvNone
  var zeroWidth = false   ## RFC-0005 S8bb: the last item was `(?i)`, `(*F)`, ...
  while true:
    r.skipX()
    if r.atEnd: break
    let c = r.cur
    if c == '|' or c == ')': break
    let start = r.i
    let afterZero = zeroWidth
    zeroWidth = false
    case c
    of '*', '+', '?', '{':
      var lo, hi: int
      if c == '{':
        if not r.isCountedRepeat(r.i + 1):
          # A literal `{`.
          inc r.i
          items.add mkSet({'{'})
          prev = pvAtom
          continue
        (lo, hi) = r.readCounts()
      else:
        lo = (if c == '+': 1 else: 0)
        hi = (if c == '?': 1 else: -1)
      if afterZero:
        r.unknown("a quantifier after an option setting or a verb")
      if prev == pvNone:
        r.reject("nothing to repeat", r.i)
      discard start
      inc r.i   # past `*` / `+` / `?` / `}`
      r.skipX()
      var lazy = false
      if r.cur == '+':
        inc r.i
        r.unmodelled("a possessive quantifier")
      elif r.cur == '?':
        inc r.i
        lazy = true
      # RFC-0005 S8bb: `(?U)` swaps greedy and lazy.
      if r.ungreedy: lazy = not lazy
      if prev == pvAtom:
        let sub = items.pop()
        items.add Rx(kind: rxRep, sub: sub, lo: lo, hi: hi, lazy: lazy)
      prev = pvNone
    of '.':
      inc r.i
      items.add r.mkDot(r.dotall)
      prev = pvAtom
    of '^':
      inc r.i
      items.add Rx(kind: rxBol)
      prev = pvNone
    of '$':
      inc r.i
      items.add Rx(kind: rxEol)
      prev = pvNone
    of '[':
      if r.at(1) in {':', '.', '='} and r.checkPosixSyntax(r.i) >= 0:
        r.unknown("a POSIX class outside a class")
      items.add mkSet(r.readClass())
      prev = pvAtom
    of '(':
      if r.at(1) == '*':
        if r.at(2) in {'A'..'Z', ':'}:
          # RFC-0005 S8bb: `(*F)` / `(*FAIL)` never match; a mark changes
          # no match. Other verbs and start options stay undecided.
          let close = r.pat.find(')', r.i)
          let verb = (if close < 0: "" else: r.pat[r.i + 2 ..< close])
          if verb in ["F", "FAIL"]:
            r.i = close + 1
            items.add mkSet({})
            prev = pvNone
            zeroWidth = true
            continue
          if (verb.startsWith("MARK:") and verb.len > 5) or
             (verb.startsWith(":") and verb.len > 1):
            r.i = close + 1
            prev = pvNone
            zeroWidth = true
            continue
          if verb == "ACCEPT":
            # RFC-0005 S8bb: the match ends here; the groups it is in
            # close (PCRE compiles an OP_CLOSE for each before OP_ACCEPT).
            r.i = close + 1
            items.add Rx(kind: rxAccept, open: r.open)
            prev = pvNone
            zeroWidth = true
            continue
          r.unknown("the verb (*" & verb & ")")
        # `(*...)`: a group whose first item is a quantifier.
      var capture = true
      var opaque = false
      let saved = (r.caseless, r.dotall, r.ungreedy, r.ext)
      if r.at(1) == '?':
        let k = r.at(2)
        case k
        of '#':
          # A comment: skipped, `prev` unchanged.
          var j = r.i + 3
          while j < r.pat.len and r.pat[j] != ')': inc j
          if j >= r.pat.len:
            r.reject("missing ) after comment", r.pat.len)
          r.i = j + 1
          continue
        of ':':
          capture = false
          r.i += 3
        of '=', '!':
          capture = false
          opaque = true
          r.unmodelled("a lookahead assertion")
          r.i += 3
        of '>':
          capture = false
          opaque = true
          r.unmodelled("an atomic group")
          r.i += 3
        of '<', 'P', '\'':
          if k == '<' and r.at(3) in {'=', '!'}:
            r.unknown("a lookbehind assertion")
          # RFC-0005 S8bb: a named group is a capturing group.
          var j = r.i + 3
          var close = '>'
          if k == 'P':
            if r.at(3) != '<': r.unknown("the group (?P" & r.at(3))
            j = r.i + 4
          elif k == '\'':
            close = '\''
          let n0 = j
          while j < r.pat.len and r.pat[j] in pcreWord: inc j
          let name = r.pat[n0 ..< j]
          if j >= r.pat.len or r.pat[j] != close or name.len == 0 or
             name.len > 32 or name[0] in pcreDigit or name in r.names:
            r.unknown("the group name `" & name & "`")
          r.names.add name
          r.i = j + 1
        of '|', '(', 'C', '&', 'R', '+', '-', '0'..'9':
          if k == '-' and r.at(3) in {'i', 'm', 's', 'x', 'X', 'J', 'U'}:
            r.readOptions()
            if r.cur == ')':
              inc r.i
              prev = pvNone
              zeroWidth = true
              continue
            capture = false
            inc r.i   # `:`
          else:
            r.unknown("the group (?" & k)
        else:
          # Option letters `imsxXJU`; any other byte is rejected at its
          # offset (PCRE ERR12). RFC-0005 S8bb: `i s x U J` are read.
          var j = r.i + 2
          while j < r.pat.len and r.pat[j] in {'i', 'm', 's', 'x', 'X', 'J',
                                               'U', '-'}:
            inc j
          if not (j < r.pat.len and r.pat[j] in {')', ':'}):
            r.reject("unrecognized character after (? or (?-", j)
          r.readOptions()
          if r.cur == ')':
            # To the end of the enclosing group: `saved` is not restored.
            inc r.i
            prev = pvNone
            zeroWidth = true
            continue
          capture = false
          inc r.i   # `:`
      else:
        inc r.i
      if capture: inc r.groups
      let group = (if capture: r.groups else: 0)
      if capture: r.open.add group
      let inner = r.readAlt(depth + 1)
      if capture: discard r.open.pop()
      inner.cap = group
      if r.atEnd:
        r.reject("missing )", r.pat.len)
      inc r.i   # `)`
      # RFC-0005 S8bb: an option set inside a group ends with it.
      (r.caseless, r.dotall, r.ungreedy, r.ext) = saved
      if opaque:
        prev = pvOpaque
      else:
        items.add inner
        prev = pvAtom
    of '\\':
      let e = r.readEscape(inClass = false)
      case e.kind
      of ekByte:
        r.noteByte(e.b)
        items.add mkSet(r.foldIf({e.b}))
        prev = pvAtom
      of ekSet:
        items.add mkSet(e.s)
        prev = pvAtom
      of ekDot:
        items.add r.mkDot(false)
        prev = pvAtom
      of ekBol:
        items.add Rx(kind: rxBol)
        prev = pvNone
      of ekEol:
        items.add Rx(kind: rxEol)
        prev = pvNone
      of ekEolAbs:
        items.add Rx(kind: rxEolAbs)
        prev = pvNone
      of ekAssert:
        r.unmodelled("the assertion " & r.pat[start ..< r.i])
        prev = pvNone
      of ekBackref:
        r.unmodelled("a backreference \\" & $e.n)
        r.maxBackref = max(r.maxBackref, e.n)
        prev = pvOpaque
      of ekQuote:
        # Literal bytes up to `\E` or the end.
        while not r.atEnd:
          if r.cur == '\\' and r.at(1) == 'E':
            r.i += 2
            break
          r.noteByte(r.cur)
          items.add mkSet(r.foldIf({r.cur}))
          inc r.i
          prev = pvAtom
      of ekQuoteEnd:
        discard   # a stray `\E` is ignored; `prev` unchanged
    else:
      inc r.i
      r.noteByte(c)
      items.add mkSet(r.foldIf({c}))
      prev = pvAtom
  mkCat(items)

proc readAlt(r: var Reader; depth: int): Rx =
  var alts = @[r.readCat(depth)]
  while r.cur == '|' and not r.atEnd:
    inc r.i
    alts.add r.readCat(depth)
  if r.cur == ')' and not r.atEnd and depth == 0:
    r.reject("unmatched parentheses", r.i)
  if alts.len == 1: alts[0] else: Rx(kind: rxAlt, kids: alts)

proc parsePcre*(pattern: string; extended = false): PcreParse =
  ## RFC-0005 S8ay. Reads `pattern` as `re(pattern)` (`extended = false`)
  ## or `rex(pattern)` (`extended = true`) compiles it. See the module doc.
  var r = Reader(pat: pattern, ext: extended)
  if '\0' in pattern:
    # Nim passes the pattern to PCRE as a cstring: it ends at the NUL.
    return PcreParse(status: psUnknown, reason: "a NUL byte in the pattern")
  try:
    # RFC-0005 S8bb: start-of-pattern options.
    while r.pat.continuesWith("(*", r.i):
      let close = r.pat.find(')', r.i)
      if close < 0: break
      let opt = r.pat[r.i + 2 ..< close]
      case opt
      of "UCP": r.ucp = true
      of "NO_START_OPT", "NO_AUTO_POSSESS", "BSR_ANYCRLF",
         "BSR_UNICODE": discard
      of "UTF8", "UTF":
        r.unknown("the start option (*" & opt & ") (UTF mode)")
      # RFC-0005 S8bb: the newline conventions; the last one wins.
      of "LF": r.nl = nlLF
      of "CR": r.nl = nlCR
      of "CRLF": r.nl = nlCRLF
      of "ANY": r.nl = nlANY
      of "ANYCRLF": r.nl = nlANYCRLF
      else:
        if opt.startsWith("LIMIT_"):
          r.unknown("the start option (*" & opt & ")")
        break
      r.i = close + 1
    let root = r.readAlt(0)
    if r.maxBackref > r.groups:
      r.reject("reference to non-existent subpattern", pattern.len)
    if r.unmodelled.len > 0:
      return PcreParse(status: psUnmodelled, reason: r.unmodelled)
    PcreParse(status: psOk, root: root, groups: r.groups, nl: r.nl,
              hasCrLf: r.hasCrLf)
  except Stop:
    case r.status
    of psRejected: PcreParse(status: psRejected, errMsg: r.errMsg)
    else: PcreParse(status: psUnknown, reason: r.reason)

# ---- shape queries ---------------------------------------------------------

type Edge* = object
  ## One top-level alternative with its anchors split off.
  bol*: bool          ## `^` / `\A` first
  eol*: RxKind        ## rxCat (none), rxEol (`$`/`\Z`) or rxEolAbs (`\z`)
  body*: Rx

proc hasAnchor(x: Rx): bool =
  ## (RFC-0005 S8bb: `(*ACCEPT)` too -- it ends the match away from the
  ## pattern's end, so only the priority automaton reads it.)
  case x.kind
  of rxBol, rxEol, rxEolAbs, rxAccept: true
  of rxSet: false
  of rxCat, rxAlt:
    for k in x.kids:
      if hasAnchor(k): return true
    false
  of rxRep: hasAnchor(x.sub)

proc splitEdges*(root: Rx): (bool, seq[Edge], string) =
  ## The top-level alternatives of `root`, each with a leading `^`/`\A` and
  ## a trailing `$`/`\Z`/`\z` split off. `(false, _, why)` when an anchor
  ## sits anywhere else (RFC-0005 S8ay models anchors at those edges only).
  let alts = (if root.kind == rxAlt: root.kids else: @[root])
  var edges: seq[Edge]
  for a in alts:
    var items = (if a.kind == rxCat: a.kids else: @[a])
    var e = Edge(eol: rxCat)
    if items.len > 0 and items[0].kind == rxBol:
      e.bol = true
      items = items[1 .. ^1]
    if items.len > 0 and items[^1].kind in {rxEol, rxEolAbs}:
      e.eol = items[^1].kind
      items = items[0 .. ^2]
    for it in items:
      if hasAnchor(it):
        return (false, @[], "an anchor away from the start or end of a " &
                            "top-level alternative")
    e.body = mkCat(items)
    edges.add e
  (true, edges, "")

proc lenRange*(x: Rx): (int, int) =
  ## Shortest and longest word length of `x` (-1: unbounded). Anchors are
  ## zero-width.
  case x.kind
  of rxSet: (1, 1)
  of rxBol, rxEol, rxEolAbs, rxAccept: (0, 0)
  of rxCat:
    var lo, hi = 0
    for k in x.kids:
      let (a, b) = lenRange(k)
      lo += a
      if hi >= 0:
        hi = (if b < 0: -1 else: hi + b)
    (lo, hi)
  of rxAlt:
    var lo = high(int)
    var hi = 0
    for k in x.kids:
      let (a, b) = lenRange(k)
      lo = min(lo, a)
      if hi >= 0:
        hi = (if b < 0: -1 else: max(hi, b))
    (lo, hi)
  of rxRep:
    let (a, b) = lenRange(x.sub)
    # `{0}` (or a zero-width body) has only the empty word, whatever the
    # body's own bound; a product past `lenCap` reads as unbounded (callers
    # use the bound only to recognise a fixed length, so that declines).
    const lenCap = 1 shl 30
    let lo = min(a * x.lo, lenCap)
    let hi =
      if x.hi == 0 or b == 0: 0
      elif x.hi < 0 or b < 0 or b * x.hi > lenCap: -1
      else: b * x.hi
    (lo, hi)

proc hasCrlfDot*(x: Rx): bool =
  ## RFC-0005 S8bb. A `(*CRLF)` dot anywhere in `x`.
  case x.kind
  of rxSet: x.crlfDot
  of rxCat, rxAlt:
    for k in x.kids:
      if hasCrlfDot(k): return true
    false
  of rxRep: hasCrlfDot(x.sub)
  else: false

proc flattenCat*(x: Rx): seq[Rx] =
  ## `x`'s concatenation items, nested concatenations inlined.
  if x.kind == rxCat:
    for k in x.kids: result.add flattenCat(k)
  else:
    result.add x

proc asSet*(x: Rx): (bool, set[char]) =
  ## `x` as one byte set: a set, or an alternation / one-item concatenation
  ## of them.
  case x.kind
  of rxSet:
    # RFC-0005 S8bb: a `(*CRLF)` dot depends on the next byte.
    if x.crlfDot: (false, {}) else: (true, x.bytes)
  of rxAlt:
    var s: set[char]
    for k in x.kids:
      let (ok, ks) = asSet(k)
      if not ok: return (false, {})
      s = s + ks
    (true, s)
  of rxCat:
    if x.kids.len == 1: asSet(x.kids[0]) else: (false, {})
  else: (false, {})

# ---- RFC-0005 S8ay: the regex call's IR encoding ------------------------------

type
  RegexSpec* = object
    ## RFC-0005 S8ay. `iekStrMatch` / `iekStrFindRe` / `iekStrReplaceRe` /
    ## regex `iekStrUnsupported` carry `"<entry>:<flag>:<pattern>"` in
    ## `strOp`; `flag` is `re`, `rex`, or `?` (a pattern the parser could
    ## not read off a literal).
    entry*, flag*, pattern*: string

proc encodeRegexSpec*(entry, flag, pattern: string): string =
  entry & ":" & flag & ":" & pattern

proc decodeRegexSpec*(strOp: string): RegexSpec =
  let a = strOp.find(':')
  let b = strOp.find(':', a + 1)
  doAssert a > 0 and b > a, "decodeRegexSpec: malformed `" & strOp & "`"
  RegexSpec(entry: strOp[0 ..< a], flag: strOp[a + 1 ..< b],
            pattern: strOp[b + 1 .. ^1])

proc parseSpec*(sp: RegexSpec): PcreParse =
  if sp.flag notin ["re", "rex"]:
    return PcreParse(status: psUnknown,
                     reason: "a Regex value that is not a `re\"...\"` / " &
                             "`rex\"...\"` literal")
  parsePcre(sp.pattern, sp.flag == "rex")

