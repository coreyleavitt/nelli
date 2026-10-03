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
##                       a possessive quantifier, ...). `reason` names the
##                       first;
##   * `psRejected`   -- PCRE rejects it: `errMsg` is the exact
##                       `RegexError.msg` Nim raises (PCRE's message, the
##                       pattern, and a caret at PCRE's error offset);
##   * `psUnknown`    -- the reader stopped at a construct whose validity
##                       or meaning it does not decide (`\X`, `\R`, `\g`,
##                       `\C`, a lookbehind, ...). Neither accepted nor
##                       rejected.
##
## Every outcome other than `psUnknown` is pinned against the real `re`/
## `rex` by the differential corpus in
## `tests/tsymex_rfc0005_s8ay_remainder.nim` (RFC-0005 S8bj: and
## `tests/tsymex_rfc0005_s8bj_syntax.nim`).
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
##     never match;
##   * the newline conventions `(*CR)`, `(*CRLF)`, `(*ANYCRLF)`, `(*ANY)`
##     (`nl`; the last one given wins): `.` and `\N` exclude the
##     convention's newline bytes (`nlBytes`; under `(*CRLF)` a CR only
##     when an LF follows it -- `Rx.crlfDot`), and `$` / `\Z` hold at
##     the end or before a final newline SEQUENCE (CRLF is one). `hasCrLf`
##     is PCRE_HASCRORLF (an explicit CR or LF in the pattern: a literal
##     byte, a one-byte escape, a class member or a range end; not `\s`,
##     `\v`, a property or a range interior -- probed), which turns off
##     the bumpalong's CRLF skip;
##   * `(*ACCEPT)` (`rxAccept`) ends the match where it is reached, closing
##     the capturing groups it is in.
##
## RFC-0005 S8bj adds (each probed against PCRE 8.45; the compile-time
## corpus is `tests/s8bj_harness/pc1.txt`, pinned by
## `tests/tsymex_rfc0005_s8bj_syntax.nim`):
##   * the backtracking verbs `(*COMMIT)`, `(*PRUNE)`, `(*SKIP)`,
##     `(*SKIP:NAME)`, `(*THEN)` and the marks `(*MARK:NAME)` / `(*:NAME)`
##     as `rxVerb` nodes (`(*PRUNE:NAME)` and `(*THEN:NAME)` are `(*PRUNE)`
##     and `(*THEN)`: their name is only reported). A verb is read exactly
##     as `pcre_compile.c` reads it: a verb name is a run of ASCII letters,
##     an argument runs to the next `)`; an unknown or unterminated verb is
##     "(*VERB) not recognized or malformed" at the end of the letter run
##     or of the argument, and a quantifier after any verb is "nothing to
##     repeat";
##   * the start options `(*LIMIT_MATCH=d)` / `(*LIMIT_RECURSION=d)`
##     (`limitMatch`, `limitRecursion`; the smallest given wins; a digit
##     run past PCRE's overflow guard ends the start options, and the rest
##     is read as a pattern), and `(*NO_START_OPT)` (`noStartOpt`);
##   * UTF mode, `(*UTF8)` / `(*UTF)` (`utf`): the pattern must be valid
##     UTF-8 ("invalid UTF-8 string" at the bad character's first byte),
##     a character is a code point (`rxChars`: one character of a code
##     point set, matched as its UTF-8 bytes -- the subject stays a Nim
##     byte string), `\x{..}` / `\o{..}` / octal escapes reach U+10FFFF
##     (surrogates rejected), `\d \w \s` and the POSIX classes stay ASCII
##     and their complements take every other code point, and `\h` / `\v`
##     are PCRE's Unicode lists. Unicode case folding (a caseless `k`, `s`
##     or non-ASCII character), `\p` and `(*UCP)` classes, and `(*ANY)`'s
##     non-ASCII newlines are not modelled (`psUnmodelled`);
##   * without UTF, `\x{..}` / `\o{..}` above 0xFF and octal above \377 are
##     rejected, as are `\L \l \U \u \N{name}` everywhere;
##   * `(?m)` (`Rx.multi` on `^` / `$`: line starts and ends under the
##     newline convention) and `(?X)` (PCRE_EXTRA: an escape of an
##     unrecognised letter is rejected), scoped like the other options;
##   * decimal escapes `\1`..`\9` as PCRE reads them (a back-reference
##     below 8 or to an open group, else octal, `\8` / `\9` the digit).

import std/[strutils, algorithm]
import ./pcre_props
import ./pcre_engine

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
    rxChars    ## RFC-0005 S8bj: UTF mode, one character of `cps`
    rxVerb     ## RFC-0005 S8bj: a backtracking verb or a mark

  CpRange* = tuple[lo, hi: int32]
  CpSet* = seq[CpRange]
    ## RFC-0005 S8bj: sorted, disjoint, non-adjacent code point ranges.

  VerbKind* = enum
    ## RFC-0005 S8bj.
    vbCommit, vbPrune, vbSkip, vbSkipName, vbThen, vbMark

  AtomOp* = enum
    ## RFC-0005 S8bj. The opcode PCRE compiles a one-character item to
    ## (pcre_compile.c), which its start-of-match optimiser reads
    ## (`pcre_startopt.nim`).
    aoChar       ## OP_CHAR / OP_CHARI: the character `ch` (a literal, an
                 ## escape, or a class of one character)
    aoNot        ## OP_NOT / OP_NOTI: a negated class of one character
    aoClass      ## OP_CLASS: a bitmap class
    aoNClass     ## OP_NCLASS: a bitmap class taking every character > 255
    aoXClass     ## OP_XCLASS (`xNot`, `xMap`, `xProp`)
    aoType       ## OP_DIGIT .. OP_WORDCHAR: `\d \D \s \S \w \W`
    aoHSpace     ## OP_HSPACE: `\h`
    aoVSpace     ## OP_VSPACE: `\v`
    aoNotSpace   ## OP_NOT_HSPACE / OP_NOT_VSPACE: `\H` / `\V`
    aoAny        ## OP_ANY / OP_ALLANY: `.` and `\N`
    aoProp       ## OP_PROP / OP_NOTPROP: `\p`, and `(*UCP)`'s classes
    aoFail       ## OP_FAIL: `(*F)` / `(*FAIL)`

  Rx* = ref object
    cap*: int          ## RFC-0005 S8bb: the capturing group this node is
                       ## the body of (1-based), 0 if none
    crlfDot*: bool     ## RFC-0005 S8bb: rxSet / rxChars of `.` / `\N`
                       ## under `(*CRLF)`: a CR only when no LF follows it
    multi*: bool       ## RFC-0005 S8bj: rxBol / rxEol under `(?m)`
    op*: AtomOp        ## RFC-0005 S8bj: rxSet / rxChars: the opcode
    ch*: int32         ## RFC-0005 S8bj: aoChar: the character
    ci*: bool          ## RFC-0005 S8bj: aoChar / aoNot: caseless
    negType*: bool     ## RFC-0005 S8bj: aoType: `\D \S \W`
    xNot*, xMap*, xProp*: bool
      ## RFC-0005 S8bj: aoXClass: negated, with a bitmap, with a property
    case kind*: RxKind
    of rxSet:
      bytes*: set[char]
    of rxChars:
      cps*: CpSet
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
    of rxVerb:
      verb*: VerbKind
      name*: string     ## vbSkipName / vbMark

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
    utf*: bool         ## psOk: UTF mode (RFC-0005 S8bj)
    noStartOpt*: bool  ## psOk: `(*NO_START_OPT)` (RFC-0005 S8bj)
    limitMatch*, limitRecursion*: int64
      ## psOk: `(*LIMIT_MATCH=)` / `(*LIMIT_RECURSION=)` (the smallest
      ## given), -1 when not given (RFC-0005 S8bj). `pcre_exec` applies one
      ## only below its default `pcreDefaultLimit`.
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
  maxCp* = 0x10FFFF'i32
  pcreDefaultLimit* = 10_000_000'i64
    ## RFC-0005 S8bj: PCRE's MATCH_LIMIT (and MATCH_LIMIT_RECURSION, which
    ## defaults to it): a start option's limit counts only below it.
  uHSpace: CpSet = @[(9'i32, 9'i32), (0x20'i32, 0x20'i32),
    (0xA0'i32, 0xA0'i32), (0x1680'i32, 0x1680'i32), (0x180E'i32, 0x180E'i32),
    (0x2000'i32, 0x200A'i32), (0x202F'i32, 0x202F'i32),
    (0x205F'i32, 0x205F'i32), (0x3000'i32, 0x3000'i32)]
    ## RFC-0005 S8bj: `\h` in UTF mode (pcre_internal.h's HSPACE_LIST).
  uVSpace: CpSet = @[(0x0A'i32, 0x0D'i32), (0x85'i32, 0x85'i32),
    (0x2028'i32, 0x2029'i32)]
    ## RFC-0005 S8bj: `\v` in UTF mode (VSPACE_LIST).

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

# ---- RFC-0005 S8bj: code point sets ---------------------------------------------

proc cpNorm*(s: CpSet): CpSet =
  ## Sorted, merged ranges.
  var xs = s
  xs.sort(proc (a, b: CpRange): int = cmp(a.lo, b.lo))
  for r in xs:
    if r.lo > r.hi: continue
    if result.len > 0 and r.lo <= result[^1].hi + 1:
      result[^1].hi = max(result[^1].hi, r.hi)
    else:
      result.add r

proc cpUnion*(a, b: CpSet): CpSet = cpNorm(a & b)

proc cpComplement*(s: CpSet; top = maxCp): CpSet =
  ## Every code point in `0 .. top` not in `s`.
  var next = 0'i32
  for r in cpNorm(s):
    if r.lo > top: break
    if r.lo > next: result.add (next, r.lo - 1)
    next = r.hi + 1
  if next <= top: result.add (next, top)

proc cpOfBytes*(s: set[char]): CpSet =
  for c in s: result.add (int32(ord(c)), int32(ord(c)))
  result = cpNorm(result)

proc cpBytes*(s: CpSet): set[char] =
  ## The members below 256, as bytes.
  for r in s:
    for c in r.lo .. min(r.hi, 255'i32): result.incl char(c)

proc cpHas*(s: CpSet; c: int32): bool =
  for r in s:
    if c >= r.lo and c <= r.hi: return true
  false

proc utf8Len*(c: int32): int =
  if c < 0x80: 1 elif c < 0x800: 2 elif c < 0x10000: 3 else: 4

proc utf8Encode*(c: int32): string =
  ## RFC-0005 S8bj. The UTF-8 bytes of code point `c`.
  let c = int(c)
  if c < 0x80: result = $char(c)
  elif c < 0x800:
    result = $char(0xC0 or (c shr 6)) & $char(0x80 or (c and 0x3F))
  elif c < 0x10000:
    result = $char(0xE0 or (c shr 12)) & $char(0x80 or ((c shr 6) and 0x3F)) &
             $char(0x80 or (c and 0x3F))
  else:
    result = $char(0xF0 or (c shr 18)) & $char(0x80 or ((c shr 12) and 0x3F)) &
             $char(0x80 or ((c shr 6) and 0x3F)) & $char(0x80 or (c and 0x3F))

proc utf8Error*(s: string; start = 0): int =
  ## RFC-0005 S8bj. PCRE's `valid_utf` from byte `start`: -1 when `s[start
  ## ..]` is valid UTF-8 (RFC 3629: at most U+10FFFF, no surrogates, no
  ## overlong form), else the offset of the first byte of the first invalid
  ## character (PCRE's error offset).
  var p = start
  while p < s.len:
    let c = ord(s[p])
    if c < 0x80:
      inc p
      continue
    if c < 0xC0 or c >= 0xFE: return p
    let ab = (if c < 0xE0: 1 elif c < 0xF0: 2 elif c < 0xF8: 3
              elif c < 0xFC: 4 else: 5)
    if s.len - p - 1 < ab: return p
    for k in 1 .. ab:
      if (ord(s[p + k]) and 0xC0) != 0x80: return p
    let d = ord(s[p + 1])
    case ab
    of 1:
      if (c and 0x3E) == 0: return p
    of 2:
      if c == 0xE0 and (d and 0x20) == 0: return p
      if c == 0xED and d >= 0xA0: return p
    of 3:
      if c == 0xF0 and (d and 0x30) == 0: return p
      if c > 0xF4 or (c == 0xF4 and d > 0x8F): return p
    else:
      return p   # 5- and 6-byte forms (RFC 3629)
    p += ab + 1
  -1

proc utf8Decode*(s: string; p: int): (int32, int) =
  ## RFC-0005 S8bj. The code point at `s[p]` of valid UTF-8 and its length.
  let c = ord(s[p])
  if c < 0x80: return (int32(c), 1)
  if c < 0xE0:
    return (int32(((c and 0x1F) shl 6) or (ord(s[p + 1]) and 0x3F)), 2)
  if c < 0xF0:
    return (int32(((c and 0x0F) shl 12) or ((ord(s[p + 1]) and 0x3F) shl 6) or
                  (ord(s[p + 2]) and 0x3F)), 3)
  (int32(((c and 0x07) shl 18) or ((ord(s[p + 1]) and 0x3F) shl 12) or
         ((ord(s[p + 2]) and 0x3F) shl 6) or (ord(s[p + 3]) and 0x3F)), 4)

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
    # RFC-0005 S8bj.
    utf: bool            ## UTF mode
    multiline: bool      ## `(?m)`
    extra: bool          ## `(?X)` (PCRE_EXTRA)

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

proc mkSet(s: set[char]; op: AtomOp): Rx = Rx(kind: rxSet, bytes: s, op: op)

proc topCp(r: Reader): int32 =
  ## RFC-0005 S8bj. The largest character value: U+10FFFF in UTF mode.
  (if r.utf: maxCp else: 255'i32)

proc mkAtom(r: Reader; s: CpSet; op: AtomOp): Rx =
  ## RFC-0005 S8bj. One character of `s` (compiled to `op`): a byte set, or
  ## in UTF mode a code point set.
  if r.utf: Rx(kind: rxChars, cps: cpNorm(s), op: op)
  else: mkSet(cpBytes(s), op)

proc mkDot(r: Reader; dotall: bool): Rx =
  ## RFC-0005 S8bb. `.` (`dotall`: under `(?s)`) or `\N` (never dotall).
  ## RFC-0005 S8bj: every code point in UTF mode.
  if dotall: return r.mkAtom(@[(0'i32, r.topCp)], aoAny)
  result = r.mkAtom(cpComplement(cpOfBytes(nlBytes(r.nl)), r.topCp), aoAny)
  result.crlfDot = r.nl == nlCRLF

proc noteChar(r: var Reader; c: int32) =
  ## RFC-0005 S8bb. PCRE_HASCRORLF: an explicit CR or LF.
  if c in [10'i32, 13'i32]: r.hasCrLf = true

proc fold(s: set[char]): set[char] =
  ## RFC-0005 S8bb. `s` with the other case of each ASCII letter (PCRE's
  ## default tables fold no byte above 0x7F -- probed).
  result = s
  for c in s:
    if c in {'a'..'z'}: result.incl char(ord(c) - 32)
    elif c in {'A'..'Z'}: result.incl char(ord(c) + 32)

proc foldCps(r: var Reader; s: CpSet): CpSet =
  ## RFC-0005 S8bj. Caseless: `s` with the other case of each ASCII
  ## letter. In UTF mode PCRE folds through Unicode's case sets (`k` and
  ## `K` also match U+212A, `s` and `S` U+017F, a non-ASCII letter its
  ## other cases), which are not modelled.
  if not r.caseless: return s
  if r.utf:
    for x in s:
      if x.hi >= 128 or cpHas(@[x], int32('k')) or cpHas(@[x], int32('K')) or
         cpHas(@[x], int32('s')) or cpHas(@[x], int32('S')):
        r.unmodelled("caseless matching of `k`, `s` or a non-ASCII " &
                     "character in UTF mode (Unicode case folding)")
        return s
  cpUnion(s, cpOfBytes(fold(cpBytes(s))))

proc mkChar(r: var Reader; c: int32): Rx =
  ## RFC-0005 S8bj. A literal character (OP_CHAR / OP_CHARI).
  result = r.mkAtom(r.foldCps(@[(c, c)]), aoChar)
  result.ch = c
  result.ci = r.caseless

proc mkCat(kids: seq[Rx]): Rx = Rx(kind: rxCat, kids: kids)

proc isHex(c: char): bool = c in {'0'..'9', 'a'..'f', 'A'..'F'}

type EscKind = enum
  ekChar      ## a single character (`c`)
  ekSet       ## a character set (`\d` ...)
  ekBol, ekEol, ekEolAbs
  ekAssert    ## `\b \B \G`: zero-width, unmodelled, not quantifiable
  ekBackref   ## `\1`..: a back-reference
  ekQuote     ## `\Q`
  ekQuoteEnd  ## `\E`
  ekDot       ## `\N` (RFC-0005 S8bb: the convention decides it)

type Esc = object
  kind: EscKind
  c: int32
  s: CpSet
  n: int
  op: AtomOp    ## RFC-0005 S8bj: ekSet: the opcode
  neg: bool     ## RFC-0005 S8bj: ekSet: a negated type (`\D \S \W`)

proc escSet(r: var Reader; s: set[char]; negated: bool): Esc =
  ## RFC-0005 S8bj. An ASCII escape class: in UTF mode its complement takes
  ## every code point above 0xFF too.
  let base = cpOfBytes(s)
  Esc(kind: ekSet, s: (if negated: cpComplement(base, r.topCp) else: base),
      op: aoType, neg: negated)

proc isCountedRepeat(r: Reader; j: int): bool

proc readEscape(r: var Reader; inClass: bool): Esc =
  ## `r.cur == '\\'`. Leaves `r.i` past the escape. Every branch was probed
  ## against PCRE 8.45 (RFC-0005 S8ay, S8bj; `check_escape` in
  ## pcre_compile.c); escapes it does not decide stop as `psUnknown`. A
  ## rejection's offset is PCRE's: the last byte the escape read.
  inc r.i
  if r.atEnd:
    r.reject("\\ at end of pattern", r.pat.len)
  if r.utf and ord(r.cur) >= 0x80:
    # RFC-0005 S8bj: a non-ASCII character after `\` is that character.
    let (cp, n) = utf8Decode(r.pat, r.i)
    r.i += n
    return Esc(kind: ekChar, c: cp)
  let c = r.cur
  let at0 = r.i       ## the escape letter's offset
  inc r.i
  case c
  of 'a': Esc(kind: ekChar, c: 7)
  of 'e': Esc(kind: ekChar, c: 27)
  of 'f': Esc(kind: ekChar, c: 12)
  of 'n': Esc(kind: ekChar, c: 10)
  of 'r': Esc(kind: ekChar, c: 13)
  of 't': Esc(kind: ekChar, c: 9)
  of 'd', 'D', 'w', 'W', 's', 'S':
    # RFC-0005 S8bb: `(*UCP)` reads them as Unicode properties.
    if r.ucp and r.utf:
      r.unmodelled("the escape \\" & c & " under (*UCP) in UTF mode")
      return Esc(kind: ekSet, op: aoProp)
    let (u, us) = (if r.ucp: pcreUcpSet("\\" & c) else: (false, {}))
    if u: Esc(kind: ekSet, s: cpOfBytes(us), op: aoProp)
    elif r.ucp and c in {'d', 'D'}:
      # RFC-0005 S8bj: `\p{Nd}` / `\P{Nd}` (OP_PROP): below 0x100 the
      # ASCII digits.
      var e = r.escSet(pcreDigit, c == 'D')
      e.op = aoProp
      e
    else:
      case c
      of 'd': r.escSet(pcreDigit, false)
      of 'D': r.escSet(pcreDigit, true)
      of 'w': r.escSet(pcreWord, false)
      of 'W': r.escSet(pcreWord, true)
      of 's': r.escSet(pcreSpace, false)
      else: r.escSet(pcreSpace, true)
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
    if r.utf:
      # RFC-0005 S8bj: a property of every code point, not of a byte.
      r.unmodelled("the property \\" & c & "{" & name & "} in UTF mode")
      return Esc(kind: ekSet, op: aoProp)
    Esc(kind: ekSet, s: cpOfBytes(if neg: pcreAnyByte - ps else: ps),
        op: aoProp)
  of 'h', 'H', 'v', 'V':
    let list = (if c in {'h', 'H'}: (if r.utf: uHSpace else: cpOfBytes(pcreHSpace))
                else: (if r.utf: uVSpace else: cpOfBytes(pcreVSpace)))
    let op = (case c
              of 'h': aoHSpace
              of 'v': aoVSpace
              else: aoNotSpace)
    Esc(kind: ekSet, op: op,
        s: (if c in {'h', 'v'}: list else: cpComplement(list, r.topCp)))
  of 'b':
    if inClass: Esc(kind: ekChar, c: 8)
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
    # RFC-0005 S8bj: `\N{` not starting a counted repeat is `\N{name}`.
    if r.cur == '{' and not r.isCountedRepeat(r.i + 1):
      r.reject("PCRE does not support \\L, \\l, \\N{name}, \\U, or \\u", at0)
    if inClass:
      r.reject("\\N is not supported in a class", at0)
    Esc(kind: ekDot)
  of 'Q':
    if inClass: r.unknown("\\Q in a class")
    Esc(kind: ekQuote)
  of 'E':
    if inClass: r.unknown("\\E in a class")
    Esc(kind: ekQuoteEnd)
  of 'L', 'l', 'U', 'u':
    # RFC-0005 S8bj: Perl's case escapes, rejected everywhere.
    r.reject("PCRE does not support \\L, \\l, \\N{name}, \\U, or \\u", at0)
  of 'x':
    if r.cur == '{':
      # RFC-0005 S8bj: `\x{h..}`, leading zeros skipped, at most 0xFF
      # (U+10FFFF in UTF mode).
      r.i += 1
      if r.cur == '}':
        r.reject("digits missing in \\x{} or \\o{}", r.i)
      var v = 0'i64
      var over = false
      while isHex(r.cur):
        let d = parseHexInt($r.cur)
        inc r.i
        if v == 0 and d == 0: continue
        v = v * 16 + d
        if v > int64(r.topCp):
          over = true
          break
      if over:
        while isHex(r.cur): inc r.i
        r.reject("character value in \\x{} or \\o{} is too large", r.i)
      if r.cur != '}':
        r.reject("non-hex character in \\x{} (closing brace missing?)", r.i)
      if r.utf and v >= 0xD800 and v <= 0xDFFF:
        r.reject("disallowed Unicode code point (>= 0xd800 && <= 0xdfff)", r.i)
      inc r.i
      return Esc(kind: ekChar, c: int32(v))
    var v = 0
    var nd = 0
    while nd < 2 and isHex(r.cur):
      v = v * 16 + parseHexInt($r.cur)
      inc r.i
      inc nd
    Esc(kind: ekChar, c: int32(v))
  of 'o':
    # RFC-0005 S8bj: `\o{ddd}`.
    if r.cur != '{':
      r.reject("missing opening brace after \\o", at0)
    if r.at(1) == '}':
      r.reject("digits missing in \\x{} or \\o{}", at0)
    r.i += 1
    var v = 0'i64
    var over = false
    while r.cur in {'0'..'7'}:
      let d = ord(r.cur) - ord('0')
      inc r.i
      if v == 0 and d == 0: continue
      v = v * 8 + d
      if v > int64(r.topCp):
        over = true
        break
    if over:
      while r.cur in {'0'..'7'}: inc r.i
      r.reject("character value in \\x{} or \\o{} is too large", r.i)
    if r.cur != '}':
      r.reject("non-octal character in \\o{} (closing brace missing?)", r.i)
    if r.utf and v >= 0xD800 and v <= 0xDFFF:
      r.reject("disallowed Unicode code point (>= 0xd800 && <= 0xdfff)", r.i)
    inc r.i
    Esc(kind: ekChar, c: int32(v))
  of 'c':
    if r.atEnd:
      r.reject("\\c at end of pattern", r.pat.len)
    let x = r.cur
    if ord(x) > 127:
      r.reject("\\c must be followed by an ASCII character", r.i)
    inc r.i
    Esc(kind: ekChar, c: int32(ord(toUpperAscii(x)) xor 0x40))
  of '0'..'9':
    # RFC-0005 S8bj: PCRE's decimal escape. Outside a class a number below
    # 8, or not above the groups opened so far, is a back-reference; else
    # (and always in a class) up to three octal digits from the first,
    # and `\8` / `\9` the digit itself.
    if c != '0' and not inClass:
      var s = int64(ord(c) - ord('0'))
      var j = r.i
      while j < r.pat.len and r.pat[j] in pcreDigit:
        if s > 214748363:
          while j < r.pat.len and r.pat[j] in pcreDigit: inc j
          r.reject("number is too big", j - 1)
        s = s * 10 + (ord(r.pat[j]) - ord('0'))
        inc j
      if s < 8 or s <= r.groups:
        r.i = j
        return Esc(kind: ekBackref, n: int(s))
    if c in {'8', '9'}:
      return Esc(kind: ekChar, c: int32(ord(c)))
    var v = ord(c) - ord('0')
    var nd = 0
    while nd < 2 and r.cur in {'0'..'7'}:
      v = v * 8 + (ord(r.cur) - ord('0'))
      inc r.i
      inc nd
    if not r.utf and v > 0xFF:
      r.reject("octal value is greater than \\377 in 8-bit non-UTF-8 mode",
               r.i - 1)
    Esc(kind: ekChar, c: int32(v))
  of 'C', 'K', 'R', 'X', 'g', 'k':
    r.unknown("the escape \\" & c)
  of 'i', 'j', 'm', 'q', 'y', 'F', 'I', 'J', 'M', 'O', 'T', 'Y':
    # PCRE without PCRE_EXTRA: an unrecognised letter escape is the letter.
    # RFC-0005 S8bj: under `(?X)` it is rejected.
    if r.extra:
      r.reject("unrecognized character follows \\", at0)
    Esc(kind: ekChar, c: int32(ord(c)))
  else:
    if c in {'a'..'z', 'A'..'Z'}:
      r.unknown("the escape \\" & c)
    # `\` before a non-alphanumeric byte is that byte.
    Esc(kind: ekChar, c: int32(ord(c)))

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

proc readChar(r: var Reader): int32 =
  ## RFC-0005 S8bj. The literal character at `r.i` (a byte, or in UTF mode
  ## a code point), leaving `r.i` past it.
  if r.utf:
    let (cp, n) = utf8Decode(r.pat, r.i)
    r.i += n
    return cp
  result = int32(ord(r.cur))
  inc r.i

proc readClass(r: var Reader): Rx =
  ## `r.cur == '['` outside a class. Leaves `r.i` past the closing `]`.
  ## RFC-0005 S8bj: the members are code points (bytes without UTF), and
  ## the atom carries the opcode pcre_compile.c gives the class: a class
  ## of one character is OP_CHAR (OP_NOT when negated); otherwise OP_CLASS
  ## / OP_NCLASS, or OP_XCLASS when it lists characters above 0xFF (UTF)
  ## or holds a property -- the class end in `compile_branch`.
  inc r.i
  var negated = false
  if r.cur == '^':
    negated = true
    inc r.i
  var cs: CpSet
  var first = true
  var items = 0          ## class items read
  var single = false     ## the last item was one character
  var oneCh = 0'i32      ## ... that character
  var flip = false       ## PCRE's should_flip_negation
  var xclass = false     ## characters above 0xFF listed (UTF mode)
  var hasProp = false    ## a property item (xclass_has_prop)
  var has8 = false       ## an item below 0x100 (class_has_8bitchar)
  while true:
    if r.atEnd:
      r.reject("missing terminating ] for character class", r.pat.len)
    let c = r.cur
    if c == ']' and not first:
      inc r.i
      break
    first = false
    inc items
    single = false
    # One item: a character (`lo`, range-able) or a set.
    var isChar = true
    var lo = int32(ord(c))
    var itemSet: CpSet
    if c == '[' and r.at(1) in {':', '.', '='}:
      let t = r.checkPosixSyntax(r.i)
      if t >= 0:
        if r.at(1) != ':':
          r.unknown("a POSIX collating element")
        var name = r.pat[r.i + 2 ..< t]
        var neg = false
        if name.len > 0 and name[0] == '^':
          neg = true
          flip = true
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
          if r.utf:
            r.unmodelled("the POSIX class [:" & name & ":] under (*UCP) " &
                         "in UTF mode")
          let (u, us) = pcreUcpSet("[[:" & name & ":]]")
          if u: ps = us
          # RFC-0005 S8bj: `(*UCP)` substitutes a property for these.
          if name notin ["ascii", "cntrl", "xdigit", "blank"]: hasProp = true
        has8 = true
        r.i = t + 2
        isChar = false
        itemSet = (if neg: cpComplement(cpOfBytes(ps), r.topCp)
                   else: cpOfBytes(ps))
        if r.cur == '-' and r.at(1) != ']':
          r.unknown("a range after a POSIX class")
      else:
        inc r.i
    elif c == '\\':
      let e = r.readEscape(inClass = true)
      case e.kind
      of ekChar: lo = e.c
      of ekSet:
        isChar = false
        itemSet = e.s
        case e.op
        of aoProp: hasProp = true
        of aoType:
          has8 = true
          if e.neg: flip = true
        else:
          # `\h \H \v \V`: in UTF mode their lists reach above 0xFF.
          has8 = true
          if r.utf: xclass = true
      else: r.unknown("an escape in a class")
    else:
      lo = r.readChar()
    if isChar: r.noteChar(lo)
    if not isChar:
      # PCRE: `-` after a class escape is a literal (`[\d-z]`).
      cs = cpUnion(cs, itemSet)
      continue
    var hi = lo
    if r.cur == '-' and r.i + 1 < r.pat.len and r.at(1) != ']':
      # A range `lo-hi`.
      inc r.i
      if r.cur == '[' and r.at(1) in {':', '.', '='} and
         r.checkPosixSyntax(r.i) >= 0:
        r.unknown("a range to a POSIX class")
      if r.cur == '\\':
        let e = r.readEscape(inClass = true)
        case e.kind
        of ekChar: hi = e.c
        of ekSet:
          r.reject("invalid range in character class", r.i - 1)
        else: r.unknown("an escape ending a range")
      else:
        hi = r.readChar()
      if hi < lo:
        r.reject("range out of order in character class", r.i - 1)
      r.noteChar(hi)
    if lo == hi:
      # PCRE reads a range `a-a` as its one character.
      single = true
      oneCh = lo
    if lo < 256: has8 = true
    if hi > 255: xclass = true
    cs = cpUnion(cs, r.foldCps(@[(lo, hi)]))
  if hasProp: xclass = true
  let members = (if negated: cpComplement(cs, r.topCp) else: cs)
  if items == 1 and single and not hasProp:
    # PCRE's one-character optimisation: OP_CHAR[I] / OP_NOT[I].
    result = r.mkAtom(members, (if negated: aoNot else: aoChar))
    result.ch = oneCh
    result.ci = r.caseless
  elif xclass and (hasProp or not flip or r.ucp):
    result = r.mkAtom(members, aoXClass)
    result.xNot = negated
    result.xMap = has8
    result.xProp = hasProp
  else:
    result = r.mkAtom(members, (if negated == flip: aoClass else: aoNClass))

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
  ## leaving `r.i` at the `)` or `:`. RFC-0005 S8bj: and `m` (multiline)
  ## and `X` (PCRE_EXTRA).
  var j = r.i + 2
  var on = true
  while j < r.pat.len and r.pat[j] notin {')', ':'}:
    case r.pat[j]
    of '-': on = false
    of 'i': r.caseless = on
    of 's': r.dotall = on
    of 'x': r.ext = on
    of 'U': r.ungreedy = on
    of 'm': r.multiline = on
    of 'X': r.extra = on
    of 'J': discard   # duplicate names, which stay undecided anyway
    else: r.unknown("the inline option " & r.pat[j])
    inc j
  if j >= r.pat.len: r.unknown("an unterminated option setting")
  r.i = j

proc readVerb(r: var Reader): Rx =
  ## RFC-0005 S8bj. `r.cur == '('`, `r.at(1) == '*'` and `r.at(2)` a
  ## letter or `:`: a verb, read as pcre_compile.c's `compile_branch`
  ## does (`(*F)` / `(*FAIL)` are the empty set, `(*ACCEPT)` an
  ## `rxAccept`, the rest `rxVerb` nodes).
  let n0 = r.i + 2
  var j = n0
  while j < r.pat.len and r.pat[j] in {'a'..'z', 'A'..'Z'}: inc j
  let name = r.pat[n0 ..< j]
  var arg = ""
  var hasArg = false
  if j < r.pat.len and r.pat[j] == ':':
    let a0 = j + 1
    j = a0
    while j < r.pat.len and r.pat[j] != ')': inc j
    arg = r.pat[a0 ..< j]
    hasArg = arg.len > 0
    if arg.len > 255:
      r.reject("name is too long in (*MARK), (*PRUNE), (*SKIP), or (*THEN)", j)
  if j >= r.pat.len or r.pat[j] != ')':
    r.reject("(*VERB) not recognized or malformed", j)
  const noArg = "an argument is not allowed for (*ACCEPT), (*FAIL), or (*COMMIT)"
  const needArg = "(*MARK) must have an argument"
  var node: Rx
  case name
  of "", "MARK":
    if not hasArg: r.reject(needArg, j)
    node = Rx(kind: rxVerb, verb: vbMark, name: arg)
  of "ACCEPT":
    if hasArg: r.reject(noArg, j)
    node = Rx(kind: rxAccept, open: r.open)
  of "COMMIT":
    if hasArg: r.reject(noArg, j)
    node = Rx(kind: rxVerb, verb: vbCommit)
  of "F", "FAIL":
    if hasArg: r.reject(noArg, j)
    node = r.mkAtom(@[], aoFail)
  of "PRUNE":
    node = Rx(kind: rxVerb, verb: vbPrune)
  of "SKIP":
    node = (if hasArg: Rx(kind: rxVerb, verb: vbSkipName, name: arg)
            else: Rx(kind: rxVerb, verb: vbSkip))
  of "THEN":
    node = Rx(kind: rxVerb, verb: vbThen)
  else:
    r.reject("(*VERB) not recognized or malformed", j)
  r.i = j + 1
  node

type Prev = enum
  pvNone       ## nothing to repeat (start, after `|`, `(`, an anchor, a
               ## quantifier, a verb)
  pvAtom       ## a quantifiable item, last in `items`
  pvOpaque     ## a quantifiable unmodelled item (no tree)

proc readCat(r: var Reader; depth: int): Rx =
  ## One alternative, up to `|`, `)` or the end.
  var items: seq[Rx]
  var prev = pvNone
  while true:
    r.skipX()
    if r.atEnd: break
    let c = r.cur
    if c == '|' or c == ')': break
    let start = r.i
    case c
    of '*', '+', '?', '{':
      var lo, hi: int
      if c == '{':
        if not r.isCountedRepeat(r.i + 1):
          # A literal `{`.
          inc r.i
          items.add r.mkChar(int32('{'))
          prev = pvAtom
          continue
        (lo, hi) = r.readCounts()
      else:
        lo = (if c == '+': 1 else: 0)
        hi = (if c == '?': 1 else: -1)
      # RFC-0005 S8bj: an option setting `(?i)` leaves nothing to repeat
      # (pcre_compile.c sets `previous = NULL`).
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
      items.add Rx(kind: rxBol, multi: r.multiline)
      prev = pvNone
    of '$':
      inc r.i
      items.add Rx(kind: rxEol, multi: r.multiline)
      prev = pvNone
    of '[':
      if r.at(1) in {':', '.', '='} and r.checkPosixSyntax(r.i) >= 0:
        r.unknown("a POSIX class outside a class")
      items.add r.readClass()
      prev = pvAtom
    of '(':
      if r.at(1) == '*' and r.at(2) in {'a'..'z', 'A'..'Z', ':'}:
        # RFC-0005 S8bj: a verb (S8bb read `(*F)`, the marks and
        # `(*ACCEPT)`). PCRE sets nothing to repeat after any of them.
        items.add r.readVerb()
        prev = pvNone
        continue
      # `(*...)` otherwise: a group whose first item is a quantifier.
      var capture = true
      var opaque = false
      let saved = (r.caseless, r.dotall, r.ungreedy, r.ext, r.multiline,
                   r.extra)
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
              continue
            capture = false
            inc r.i   # `:`
          else:
            r.unknown("the group (?" & k)
        else:
          # Option letters `imsxXJU`; any other byte is rejected at its
          # offset (PCRE ERR12). RFC-0005 S8bb: `i s x U J` are read;
          # RFC-0005 S8bj: and `m` and `X`.
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
      (r.caseless, r.dotall, r.ungreedy, r.ext, r.multiline, r.extra) = saved
      if opaque:
        prev = pvOpaque
      else:
        items.add inner
        prev = pvAtom
    of '\\':
      let e = r.readEscape(inClass = false)
      case e.kind
      of ekChar:
        r.noteChar(e.c)
        items.add r.mkChar(e.c)
        prev = pvAtom
      of ekSet:
        let a = r.mkAtom(e.s, e.op)
        a.negType = e.neg
        items.add a
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
        # Literal characters up to `\E` or the end.
        while not r.atEnd:
          if r.cur == '\\' and r.at(1) == 'E':
            r.i += 2
            break
          let q = r.readChar()
          r.noteChar(q)
          items.add r.mkChar(q)
          prev = pvAtom
      of ekQuoteEnd:
        discard   # a stray `\E` is ignored; `prev` unchanged
    else:
      let q = r.readChar()
      r.noteChar(q)
      items.add r.mkChar(q)
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

proc readLimit(r: Reader; j: int): (bool, int64, int) =
  ## RFC-0005 S8bj. The digits of `(*LIMIT_..=` from `j`, as
  ## pcre_compile2 reads them: `(false, ..)` when the digit run passes the
  ## overflow guard or no `)` follows it (the start options end there);
  ## else the value and the offset past the `)`.
  var c = 0'i64
  var p = j
  while p < r.pat.len and r.pat[p] in pcreDigit:
    if c > 429496728: break
    c = c * 10 + (ord(r.pat[p]) - ord('0'))
    inc p
  if p >= r.pat.len or r.pat[p] != ')': return (false, 0'i64, p)
  (true, c, p + 1)

proc parsePcre*(pattern: string; extended = false): PcreParse =
  ## RFC-0005 S8ay. Reads `pattern` as `re(pattern)` (`extended = false`)
  ## or `rex(pattern)` (`extended = true`) compiles it. See the module doc.
  var r = Reader(pat: pattern, ext: extended)
  if '\0' in pattern:
    # Nim passes the pattern to PCRE as a cstring: it ends at the NUL.
    return PcreParse(status: psUnknown, reason: "a NUL byte in the pattern")
  var noStartOpt = false
  var limitMatch, limitRecursion = -1'i64
  try:
    # RFC-0005 S8bb: start-of-pattern options. RFC-0005 S8bj: read as
    # pcre_compile2's loop reads them (an exact prefix each; the limits'
    # digits; anything else ends the options).
    while r.pat.continuesWith("(*", r.i):
      let rest = r.i + 2
      template opt(s: string): bool = r.pat.continuesWith(s, rest)
      if opt("UTF8)"):
        r.utf = true
        r.i += 7
      elif opt("UTF)"):
        r.utf = true
        r.i += 6
      elif opt("UCP)"):
        r.ucp = true
        r.i += 6
      elif opt("NO_AUTO_POSSESS)"): r.i += 18
      elif opt("NO_START_OPT)"):
        noStartOpt = true
        r.i += 15
      elif opt("LIMIT_MATCH="):
        let (ok, v, p) = r.readLimit(r.i + 14)
        if not ok: break
        if limitMatch < 0 or v < limitMatch:
          limitMatch = v
        r.i = p
      elif opt("LIMIT_RECURSION="):
        let (ok, v, p) = r.readLimit(r.i + 18)
        if not ok: break
        if limitRecursion < 0 or v < limitRecursion:
          limitRecursion = v
        r.i = p
      # RFC-0005 S8bb: the newline conventions; the last one wins.
      elif opt("CR)"):
        r.nl = nlCR
        r.i += 5
      elif opt("LF)"):
        r.nl = nlLF
        r.i += 5
      elif opt("CRLF)"):
        r.nl = nlCRLF
        r.i += 7
      elif opt("ANY)"):
        r.nl = nlANY
        r.i += 6
      elif opt("ANYCRLF)"):
        r.nl = nlANYCRLF
        r.i += 10
      elif opt("BSR_ANYCRLF)") or opt("BSR_UNICODE)"): r.i += 14
      else: break
    if r.utf:
      # RFC-0005 S8bj: the whole pattern must be valid UTF-8.
      let bad = utf8Error(pattern)
      if bad >= 0: r.reject("invalid UTF-8 string", bad)
    let root = r.readAlt(0)
    if r.maxBackref > r.groups:
      r.reject("reference to non-existent subpattern", pattern.len)
    if r.utf and r.nl == nlANY:
      r.unmodelled("the (*ANY) newline convention in UTF mode (U+0085, " &
                   "U+2028 and U+2029 are multi-byte newlines)")
    if r.unmodelled.len > 0:
      return PcreParse(status: psUnmodelled, reason: r.unmodelled)
    PcreParse(status: psOk, root: root, groups: r.groups, nl: r.nl,
              hasCrLf: r.hasCrLf, utf: r.utf, noStartOpt: noStartOpt,
              limitMatch: limitMatch, limitRecursion: limitRecursion)
  except Stop:
    case r.status
    of psRejected: PcreParse(status: psRejected, errMsg: r.errMsg)
    else: PcreParse(status: psUnknown, reason: r.reason)

type Edge* = object
  ## One top-level alternative with its anchors split off.
  bol*: bool          ## `^` / `\A` first
  eol*: RxKind        ## rxCat (none), rxEol (`$`/`\Z`) or rxEolAbs (`\z`)
  body*: Rx

proc hasAnchor(x: Rx): bool =
  ## (RFC-0005 S8bb: `(*ACCEPT)` too -- it ends the match away from the
  ## pattern's end, so only the priority automaton reads it. RFC-0005
  ## S8bj: and a verb or a mark, and a UTF character, for the same reason.)
  case x.kind
  of rxBol, rxEol, rxEolAbs, rxAccept, rxVerb, rxChars: true
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
    if items.len > 0 and items[0].kind == rxBol and not items[0].multi:
      e.bol = true
      items = items[1 .. ^1]
    if items.len > 0 and items[^1].kind in {rxEol, rxEolAbs} and
       not items[^1].multi:
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
  of rxChars:
    # RFC-0005 S8bj: a character's UTF-8 length.
    if x.cps.len == 0: (1, 1)
    else: (utf8Len(x.cps[0].lo), utf8Len(x.cps[^1].hi))
  of rxBol, rxEol, rxEolAbs, rxAccept, rxVerb: (0, 0)
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
  of rxSet, rxChars: x.crlfDot
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

proc zeroRepAndCaseless(x: Rx; zero, ci: var bool) =
  if x.kind in {rxSet, rxChars} and x.ci: ci = true
  case x.kind
  of rxCat, rxAlt:
    for k in x.kids: zeroRepAndCaseless(k, zero, ci)
  of rxRep:
    if x.hi == 0: zero = true
    zeroRepAndCaseless(x.sub, zero, ci)
  else: discard

proc parseSpec*(sp: RegexSpec): PcreParse =
  ## The walker's reading of a regex literal: `parsePcre`, and RFC-0005
  ## S8bj's library-version scoping (`pcre_engine.pcreBefore838`).
  if sp.flag notin ["re", "rex"]:
    return PcreParse(status: psUnknown,
                     reason: "a Regex value that is not a `re\"...\"` / " &
                             "`rex\"...\"` literal")
  result = parsePcre(sp.pattern, sp.flag == "rex")
  if result.status == psOk:
    var zero, ci = false
    zeroRepAndCaseless(result.root, zero, ci)
    if zero and ci and pcreBefore838():
      return PcreParse(status: psUnmodelled,
        reason: "a `{0}` item in a pattern with caseless characters, and " &
                "std/re's libpcre predates 8.38 (its required-character " &
                "data drops the caseless flag there)")

