## Phase 15 S6a; RFC-0005 S8ay. Nim `std/re` patterns as Z3 regexes, and the
## Z3 meaning of each `std/re` entry point.
##
## RFC-0005 S8ay replaced S6a's own reader (which read `.` as any byte,
## `\D \W \S \n \t` as literal letters, `^ $` as literal bytes, accepted
## `a**`, and had no `rex`) with `pcre_syntax.nim`, a byte-level reader of
## PCRE 8.45 as Nim compiles it, and gave every entry point its own formula
## (`lowerRegexEntry`). Before S8ay every entry point was the full-string
## membership `s in R` with `start` dropped: `contains` (an occurrence
## anywhere) and `match` (a match of a PREFIX of `s[start..]`) were both
## wrong.
##
## ## Byte-faithful model (ADR-0006)
##
## Strings are byte strings (every char <= 0xFF); a byte set is a union of
## `re.range` over single-byte literals, never `re.allchar` (which would
## admit codepoints > 0xFF). The only exceptions are `findMarker` (code 256)
## and `findMarker2` (code 257, RFC-0005 S8bb), which never occur in a
## subject: they mark positions inside a derived term (the leftmost-match
## and selection encodings, a capture's span).
##
## ## The entry points (Nim 2.2 `std/re`, all probed concretely)
##
## `bad` is `start < 0 or start > s.len` (PCRE_ERROR_BADOFFSET, -24); `U`
## is `s[start..]`; a `^`/`\A` alternative matches only at subject
## position 0.
##   * `match(s, R, start)`    -- `matchLen(...) != -1`: `bad`, or a prefix
##                                of `U` is in R (Tail included).
##   * `contains(s, R, start)` -- `find(...) >= 0`: not `bad`, and R occurs
##                                in `U`.
##   * `startsWith(s, R)`      -- `matchLen(s, R) >= 0`: `match` at 0.
##   * `find(s, R, start)`     -- -24 if `bad`, -1 if no occurrence, else
##                                the LEFTMOST occurrence start (a fresh Int
##                                fixed by definitional constraints).
##   * `matchLen(s, R, start)` -- -24 / -1 / the length of PCRE's chosen
##                                match at `start`;
##   * `endsWith(s, R)`        -- some `i < s.len` has
##                                `matchLen(s, R, i) == s.len - i`;
##   * `findBounds(s, R, start)` -- (`find`, its match's last index), or
##                                (-1, 0) / (-24, 0).
## `matchLen`, `endsWith` and `findBounds`'s `last` depend on WHICH match
## PCRE picks. A "longest-selection" pattern fixes it by its shape
## (`selectionForm`): a fixed-length body, or a fixed-length prefix then one
## greedy run of a single byte set (PCRE's backtracking then returns the
## longest match whose Tail holds). RFC-0005 S8bb: every other pattern
## (`a|ab`, `a*b`, `(ab)+`, an anchor anywhere) goes through PCRE's
## priority order itself, as the regular languages of `pcre_select.nim`;
## S8ay declined them (a fresh value). `match` and `startsWith` with an
## anchor away from a top-level edge use the same automaton.

import std/[strutils, tables]
import z3
import ./pcre_syntax
import ./pcre_select
import ./pcre_engine
export pcre_syntax

type
  RegexParseResult* = object
    isOk*: bool
    regex*: Z3Regex[Z3String]
    error*: string

proc ok(r: Z3Regex[Z3String]): RegexParseResult =
  RegexParseResult(isOk: true, regex: r)

proc err(msg: string): RegexParseResult =
  RegexParseResult(isOk: false, error: msg)

# ---- byte sets and trees -----------------------------------------------------

proc epsRe(): Z3Regex[Z3String] = mkRegex(mkString(""))

proc findMarker*(): Z3String =
  ## RFC-0005 S8ay. The one-character string of code 256: outside every
  ## subject's byte alphabet, so it marks a position unambiguously.
  simplify(fromCode(mkInt(256)))

proc findMarker2*(): Z3String =
  ## RFC-0005 S8bb. The one-character string of code 257: a second marker
  ## (a capture's end, `pcre_select.captureLang`).
  simplify(fromCode(mkInt(257)))

proc byteSetRe*(cs: set[char]): Z3Regex[Z3String] =
  ## `cs` as a union of byte ranges; the empty set is the empty language.
  var parts: seq[Z3Regex[Z3String]]
  var b = 0
  while b <= 255:
    if char(b) notin cs:
      inc b
      continue
    var e = b
    while e + 1 <= 255 and char(e + 1) in cs: inc e
    parts.add(if b == e: mkRegex(mkString($char(b)))
              else: range(mkString($char(b)), mkString($char(e))))
    b = e + 1
  if parts.len == 0: mkRegexEmpty[Z3String]()
  elif parts.len == 1: parts[0]
  else: union(parts)

proc atomRe(cs: set[char]; marked: bool): Z3Regex[Z3String] =
  ## A byte of `cs`; under `marked`, followed by any number of markers (the
  ## "insert one marker after a non-empty prefix" closure of `reFind`).
  if marked: concat(byteSetRe(cs), star(mkRegex(findMarker())))
  else: byteSetRe(cs)

proc rxToZ3*(x: Rx; marked = false): Z3Regex[Z3String] =
  ## The language of an anchor-free tree.
  case x.kind
  of rxSet: atomRe(x.bytes, marked)
  of rxCat:
    if x.kids.len == 0: return epsRe()
    var parts: seq[Z3Regex[Z3String]]
    for k in x.kids: parts.add rxToZ3(k, marked)
    if parts.len == 1: parts[0] else: concat(parts)
  of rxAlt:
    var parts: seq[Z3Regex[Z3String]]
    for k in x.kids: parts.add rxToZ3(k, marked)
    if parts.len == 1: parts[0] else: union(parts)
  of rxRep:
    let sub = rxToZ3(x.sub, marked)
    if x.hi == 0: epsRe()
    elif x.hi < 0:
      if x.lo == 0: star(sub)
      elif x.lo == 1: plus(sub)
      else: concat(power(sub, x.lo), star(sub))
    elif x.lo == x.hi: power(sub, x.lo)
    else: loop(sub, x.lo, x.hi)
  of rxBol, rxEol, rxEolAbs, rxAccept, rxVerb, rxChars:
    # RFC-0005 S8bj: a verb or a UTF character routes the pattern to the
    # priority automaton (`splitEdges`' `hasAnchor`).
    raiseAssert "rxToZ3: anchors, (*ACCEPT), verbs and UTF characters " &
                "are split off first"

proc tailRe(eol: RxKind; marked = false): Z3Regex[Z3String] =
  ## What may follow the match up to the subject's end: anything (no
  ## anchor), nothing or a final `\n` (`$`, `\Z`), nothing (`\z`).
  case eol
  of rxEol: union(epsRe(), atomRe({'\n'}, marked))
  of rxEolAbs: epsRe()
  else: star(atomRe(pcreAnyByte, marked))

proc parseNimRegexToZ3Regex*(pattern: string;
                             extended = false): RegexParseResult =
  ## The full-string language of `re(pattern)` (`rex` when `extended`):
  ## S6a's API, kept for its unit tests. A pattern with an anchor, an
  ## unmodelled construct, a PCRE rejection or an undecided construct is
  ## `isOk == false`, its `error` naming why.
  let pr = parsePcre(pattern, extended)
  case pr.status
  of psOk:
    if hasCrlfDot(pr.root):
      return err("a `(*CRLF)` dot, which depends on the byte after it " &
                 "(seUnsupportedRegex: no full-string language)")
    let (fine, edges, why) = splitEdges(pr.root)
    # A top-level alternation splits into several edges; the full-string
    # language is still the plain union when no edge carries an anchor.
    if not fine:
      return err(why & " (seUnsupportedRegex: no full-string language)")
    for e in edges:
      if e.bol or e.eol != rxCat:
        return err("an anchor (seUnsupportedRegex: no full-string language)")
    ok(rxToZ3(pr.root))
  of psUnmodelled, psUnknown:
    err(pr.reason & " (seUnsupportedRegex)")
  of psRejected:
    err("PCRE rejects the pattern, `re` raises RegexError: " &
        pr.errMsg.splitLines()[0] & " (seUnsupportedRegex)")

# ---- selection forms ---------------------------------------------------------

type
  SelKind* = enum skNone, skFixed, skRun
  SelForm* = object
    ## RFC-0005 S8ay. A pattern whose PCRE-chosen match at a position is
    ## the LONGEST one whose Tail holds.
    kind*: SelKind
    bol*: bool
    eol*: RxKind
    m*: int                  ## fixed prefix length (skFixed: the length)
    prefix*: Rx              ## fixed-length part
    runSet*: set[char]       ## skRun: the repeated byte set
    runLo*, runHi*: int      ## skRun: its bounds (-1: unbounded)
    body*: Rx                ## the whole body, for language checks
    why*: string             ## skNone: the reason

proc selectionForm*(edges: seq[Edge]): SelForm =
  ## RFC-0005 S8ay. See `SelForm`.
  if edges.len > 1:
    # Several top-level alternatives: only all fixed-length, of one length
    # and anchor-free, fixes the chosen length.
    var kids: seq[Rx]
    var m = -1
    for e in edges:
      let (lo, hi) = lenRange(e.body)
      if e.bol or e.eol != rxCat or lo != hi or (m >= 0 and lo != m):
        return SelForm(kind: skNone, why: "top-level alternatives of " &
          "different lengths or with anchors (PCRE takes the first " &
          "alternative that matches, not the longest)")
      m = lo
      kids.add e.body
    let body = Rx(kind: rxAlt, kids: kids)
    return SelForm(kind: skFixed, eol: rxCat, m: m, prefix: body, body: body)
  let e = edges[0]
  let (lo, hi) = lenRange(e.body)
  if lo == hi:
    return SelForm(kind: skFixed, bol: e.bol, eol: e.eol, m: lo,
                   prefix: e.body, body: e.body)
  let items = flattenCat(e.body)
  let last = items[^1]
  let pre = Rx(kind: rxCat, kids: items[0 .. ^2])
  let (plo, phi) = lenRange(pre)
  let (isSet, cs) = (if last.kind == rxRep: asSet(last.sub)
                     else: (false, {}))
  if plo != phi or not isSet:
    return SelForm(kind: skNone, why: "a variable-length part other than " &
      "one byte-set repetition at the end (PCRE's match choice follows " &
      "its backtracking order, not the longest match)")
  if last.lazy:
    if e.eol != rxCat:
      return SelForm(kind: skNone, why: "a lazy repetition before an " &
                                        "end anchor")
    # A lazy run at the end stops at its minimum.
    let fixedBody = Rx(kind: rxCat, kids: items[0 .. ^2] & @[Rx(kind: rxRep,
      sub: Rx(kind: rxSet, bytes: cs), lo: last.lo, hi: last.lo)])
    return SelForm(kind: skFixed, bol: e.bol, eol: e.eol, m: plo + last.lo,
                   prefix: fixedBody, body: fixedBody)
  SelForm(kind: skRun, bol: e.bol, eol: e.eol, m: plo, prefix: pre,
          runSet: cs, runLo: last.lo, runHi: last.hi, body: e.body)

# ---- entry-point lowering ----------------------------------------------------

type
  RxOutcome* = enum
    roValue       ## `b` / `i` / `s` hold the result; `defs` must be asserted
    roRejected    ## PCRE rejects the pattern: `msg` is the RegexError msg
    roUnmodelled  ## accepted, not modelled for this entry: `msg` says why
    roUnknown     ## validity undecided: `msg` says why

  RxResult* = object
    outcome*: RxOutcome
    b*: Z3Bool
    i*: Z3Int
    s*: Z3String
    defs*: seq[Z3Bool]  ## definitional constraints on fresh constants
    msg*: string


proc inSet(code: Z3Int; cs: set[char]): Z3Bool =
  var parts: seq[Z3Bool]
  var b = 0
  while b <= 255:
    if char(b) notin cs:
      inc b
      continue
    var e = b
    while e + 1 <= 255 and char(e + 1) in cs: inc e
    parts.add(if b == e: code == mkInt(b)
              else: (code >= mkInt(b)) and (code <= mkInt(e)))
    b = e + 1
  if parts.len == 0: return mkBool(false)
  result = parts[0]
  for j in 1 ..< parts.len: result = result or parts[j]

proc orAll(xs: seq[Z3Bool]): Z3Bool =
  if xs.len == 0: return mkBool(false)
  result = xs[0]
  for j in 1 ..< xs.len: result = result or xs[j]

proc andAll(xs: seq[Z3Bool]): Z3Bool =
  if xs.len == 0: return mkBool(true)
  result = xs[0]
  for j in 1 ..< xs.len: result = result and xs[j]

proc tailOk(s: Z3String; pos: Z3Int; eol: RxKind): Z3Bool =
  ## The Tail at absolute position `pos` of `s`.
  case eol
  of rxEol: (pos == len(s)) or
            ((pos + mkInt(1) == len(s)) and (at(s, pos) == mkString("\n")))
  of rxEolAbs: pos == len(s)
  else: mkBool(true)

proc unmodelled(why: string): RxResult =
  RxResult(outcome: roUnmodelled, msg: why)

type FreshName* = proc (tag: string): string
  ## A per-run-unique Z3 constant name for `tag`.

proc chosenLen(s: Z3String; p: Z3Int; f: SelForm; fresh: FreshName;
               defs: var seq[Z3Bool]): Z3Int =
  ## PCRE's chosen match length at absolute position `p` (0 <= p <=
  ## s.len), or -1: the longest match whose Tail holds (see `SelForm`).
  let lenS = len(s)
  let bolOk = (if f.bol: p == mkInt(0) else: mkBool(true))
  let fits = (p + mkInt(f.m) <= lenS) and
             matches(substr(s, p, mkInt(f.m)), rxToZ3(f.prefix))
  case f.kind
  of skFixed:
    ite(bolOk and fits and tailOk(s, p + mkInt(f.m), f.eol),
        mkInt(f.m), mkInt(-1))
  of skRun:
    # `r`: the maximal run of `runSet` from `q0`, fixed definitionally.
    let q0 = p + mkInt(f.m)
    let r = mkIntVar(fresh("__regexRun"))
    defs.add ite(q0 <= lenS,
      (r >= mkInt(0)) and (q0 + r <= lenS) and
        matches(substr(s, q0, r), star(byteSetRe(f.runSet))) and
        ((q0 + r == lenS) or not inSet(toCode(at(s, q0 + r)), f.runSet)),
      r == mkInt(0))
    let c = (if f.runHi < 0: r else: ite(r > mkInt(f.runHi), mkInt(f.runHi), r))
    ite(bolOk and fits and (c >= mkInt(f.runLo)) and
        tailOk(s, q0 + c, f.eol), mkInt(f.m) + c, mkInt(-1))
  of skNone:
    raiseAssert "chosenLen: no selection form"

proc selToZ3Memo(r: RNode; memo: var Table[pointer, Z3Regex[Z3String]]):
                 Z3Regex[Z3String] =
  let key = cast[pointer](r)
  if key in memo: return memo[key]
  result =
    case r.kind
    of rkEmpty: mkRegexEmpty[Z3String]()
    of rkEps: epsRe()
    of rkSet: byteSetRe(r.bytes)
    of rkMark: mkRegex(findMarker())
    of rkMark2: mkRegex(findMarker2())
    of rkStar: star(selToZ3Memo(r.kids[0], memo))
    of rkCat, rkAlt:
      var parts: seq[Z3Regex[Z3String]]
      for k in r.kids: parts.add selToZ3Memo(k, memo)
      if parts.len == 1: parts[0]
      elif r.kind == rkCat: concat(parts)
      else: union(parts)
  memo[key] = result

proc selToZ3*(r: RNode): Z3Regex[Z3String] =
  ## RFC-0005 S8bb. A `pcre_select` regex as Z3's. RFC-0005 S8bj: once per
  ## shared subterm (state elimination shares them).
  var memo = initTable[pointer, Z3Regex[Z3String]]()
  selToZ3Memo(r, memo)

const limitDecline* = "a (*LIMIT_MATCH=) / (*LIMIT_RECURSION=) start " &
  "option between 0 and PCRE's default, whose effect (a count of " &
  "pcre_exec.c's match() calls) is not computed"

proc jitDeclines*(n: Nfa): string =
  ## RFC-0005 S8bj. Why an unanchored call is declined on the engine std/re
  ## runs it on (`pcre_engine`), "" when it is modelled.
  if pcreRunsJit(): jitDeclined(n) else: ""

proc s8bjRoute(pr: PcreParse): bool =
  ## RFC-0005 S8bj. A pattern whose every entry is the priority automaton's
  ## (with `pcre_exec`'s errors): UTF mode or a limit start option.
  pr.utf or (pr.limitMatch >= 0 and pr.limitMatch < pcreDefaultLimit) or
    (pr.limitRecursion >= 0 and pr.limitRecursion < pcreDefaultLimit)

# ---- RFC-0005 S8bb, S8bj: the priority automaton's languages ------------------

proc rawClassIs(s: Z3String; p: Z3Int; c: PrevClass): Z3Bool =
  ## RFC-0005 S8bj. What precedes position `p` of `s` is of class `c`.
  let b1 = toCode(at(s, p - mkInt(1)))
  let b2 = toCode(at(s, p - mkInt(2)))
  case c
  of pcStart: p == mkInt(0)
  of pcOther: (p > mkInt(0)) and not inSet(b1, {'\n', '\r', '\v', '\f', '\x85'})
  of pcLF: (p > mkInt(0)) and (b1 == mkInt(10)) and
           ((p == mkInt(1)) or (b2 != mkInt(13)))
  of pcCRLF: (p >= mkInt(2)) and (b1 == mkInt(10)) and (b2 == mkInt(13))
  of pcCR: (p > mkInt(0)) and (b1 == mkInt(13))
  of pcNl: (p > mkInt(0)) and inSet(b1, {'\v', '\f', '\x85'})

proc rawClassRe(c: PrevClass): Z3Regex[Z3String] =
  ## RFC-0005 S8bj. The words after which a position is of class `c`.
  let anyB = star(byteSetRe(pcreAnyByte))
  case c
  of pcStart: epsRe()
  of pcOther: concat(anyB, byteSetRe(pcreAnyByte -
                                     {'\n', '\r', '\v', '\f', '\x85'}))
  of pcLF: concat(union(epsRe(), concat(anyB, byteSetRe(pcreAnyByte - {'\r'}))),
                  byteSetRe({'\n'}))
  of pcCRLF: concat(anyB, mkRegex(mkString("\r\n")))
  of pcCR: concat(anyB, byteSetRe({'\r'}))
  of pcNl: concat(anyB, byteSetRe({'\v', '\f', '\x85'}))

type PrioLangs = object
  ## RFC-0005 S8bb, S8bj. A pattern's selection languages, per variant: the
  ## canonical class of what precedes the start (`pcre_select.canonPc0`;
  ## one variant when the pattern cannot tell them apart).
  ok: bool
  why: string
  n: Nfa
  vars: seq[PrevClass]
  mark, none, ends, noOcc, first, span: seq[Z3Regex[Z3String]]

proc prioLangs(sp: RegexSpec; pr: PcreParse; wantAnch, wantEnds: bool;
               wantSearch = false; wantSpan = false): PrioLangs =
  let n = buildNfa(pr)
  let key = sp.flag & ":" & sp.pattern
  result.n = n
  if not n.ok: return PrioLangs(ok: false, why: n.why)
  result.ok = true
  result.vars = startClasses(n)
  for pc in result.vars:
    template take(l: SelLang; dst: untyped) =
      if not l.ok: return PrioLangs(ok: false, why: l.why)
      result.dst.add selToZ3(l.re)
    if wantAnch:
      take(selectionLangV(n, key, lkMark, pc), mark)
      take(selectionLangV(n, key, lkNone, pc), none)
    if wantEnds:
      take(selectionLangV(n, key, lkEnds, pc, nonEmpty = true), ends)
    if wantSearch:
      take(searchLangV(n, key, skNoOcc, pc), noOcc)
      take(searchLangV(n, key, skFirst, pc), first)
    if wantSpan:
      take(searchLangV(n, key, skSpan, pc), span)

proc classIs(n: Nfa; s: Z3String; p: Z3Int; rep: PrevClass): Z3Bool =
  var parts: seq[Z3Bool]
  for c in PrevClass:
    if canonPc0(n, c) == rep: parts.add rawClassIs(s, p, c)
  orAll(parts)

proc variant(pl: PrioLangs; s: Z3String; p: Z3Int;
             f: proc (v: int): Z3Bool): Z3Bool =
  ## `f` of the variant of position `p` of `s`.
  result = f(pl.vars.high)
  for v in countdown(pl.vars.high - 1, 0):
    result = ite(classIs(pl.n, s, p, pl.vars[v]), f(v), result)

proc splitAt(u: Z3String; k: Z3Int; fresh: FreshName; tag: string;
             defs: var seq[Z3Bool]): (Z3String, Z3String) =
  ## RFC-0005 S8bb. `u[0 ..< k]` and `u[k ..]` as fresh strings whose
  ## concatenation is `u` (`0 <= k <= len(u)` holds wherever `k` is
  ## defined). Z3 decides a marked word built from these concatenation
  ## equations far more reliably than one built from nested `substr`s of a
  ## symbolic offset (measured: the captures differential timed out on 6 of
  ## 3150 ground queries with `substr`).
  let x = mkStringVar(fresh(tag & "Pre"))
  let y = mkStringVar(fresh(tag & "Post"))
  defs.add (u == concat(x, y)) and (len(x) == k)
  (x, y)

proc utf8ValidRe*(): Z3Regex[Z3String] =
  ## RFC-0005 S8bj. The valid UTF-8 strings (RFC 3629, PCRE's `valid_utf`).
  let t = byteSetRe({'\x80'..'\xBF'})
  proc b(lo, hi: char): Z3Regex[Z3String] = byteSetRe({lo..hi})
  star(union(@[
    b('\x00', '\x7F'),
    concat(b('\xC2', '\xDF'), t),
    concat(@[b('\xE0', '\xE0'), b('\xA0', '\xBF'), t]),
    concat(@[byteSetRe({'\xE1'..'\xEC', '\xEE', '\xEF'}), t, t]),
    concat(@[b('\xED', '\xED'), b('\x80', '\x9F'), t]),
    concat(@[b('\xF0', '\xF0'), b('\x90', '\xBF'), t, t]),
    concat(@[b('\xF1', '\xF3'), t, t, t]),
    concat(@[b('\xF4', '\xF4'), b('\x80', '\x8F'), t, t])]))

proc attemptMadeZ3(n: Nfa; u: Z3String; anchored: bool; fresh: FreshName;
                   defs: var seq[Z3Bool]): Z3Bool =
  ## RFC-0005 S8bj. A search on `u` (the subject from the start offset)
  ## calls `match()` at least once (`pcre_select.attemptMade` after the
  ## start-of-match scan): what a `(*LIMIT_..=0)` turns into an error.
  let so = n.so
  let filt = (if anchored or n.noStartOpt: fkNone else: n.filter)
  var v = u
  if filt in {fkFirst, fkBits}:
    let stop = (if filt == fkFirst:
                  {char(so.firstChar)} + (if so.firstCaseless:
                    {otherCaseOf(char(so.firstChar))} else: {})
                else: so.bits)
    let q = mkIntVar(fresh("__regexScan"))
    let (pre, rest) = splitAt(u, q, fresh, "__regexScan", defs)
    defs.add matches(pre, star(byteSetRe(pcreAnyByte - stop))) and
             ((len(rest) == mkInt(0)) or inSet(toCode(at(rest, mkInt(0))), stop))
    v = rest
  if n.noStartOpt: return mkBool(true)
  var conds: seq[Z3Bool]
  if so.minLength > 0: conds.add len(v) >= mkInt(so.minLength)
  if so.reqChar >= 0:
    let r1 = char(so.reqChar)
    var rs = {r1}
    if so.reqCaseless: rs.incl otherCaseOf(r1)
    let skip = (if filt == fkFirst: 1 else: 0)
    let tl = substr(v, mkInt(skip), len(v) - mkInt(skip))
    conds.add (len(v) >= mkInt(reqByteMax)) or
              matches(tl, concat(@[star(byteSetRe(pcreAnyByte)), byteSetRe(rs),
                                   star(byteSetRe(pcreAnyByte))]))
  andAll(conds)

proc callError(pl: PrioLangs; s: Z3String; start: Z3Int; anchored: bool;
               fresh: FreshName; defs: var seq[Z3Bool]): (Z3Bool, Z3Int) =
  ## RFC-0005 S8bj. Whether `pcre_exec` runs the call without an error, and
  ## the error code otherwise: a bad offset, an invalid UTF-8 subject, a
  ## start inside a character, a `(*LIMIT_..=0)` reached.
  let n = pl.n
  let lenS = len(s)
  let bad = (start < mkInt(0)) or (start > lenS)
  var okParts = @[not bad]
  var code = mkInt(0)
  let (le, lcode) = limitEffect(n)
  if le == leZero:
    let u = substr(s, start, lenS - start)
    let hit = attemptMadeZ3(n, u, anchored, fresh, defs)
    okParts.add not hit
    code = mkInt(lcode)
  if n.utf:
    let invalid = not matches(s, utf8ValidRe())
    let inside = (start > mkInt(0)) and (start < lenS) and
                 inSet(toCode(at(s, start)), {'\x80'..'\xBF'})
    okParts.add (not invalid) and not inside
    code = ite(invalid, mkInt(pcreErrBadUtf8),
               ite(inside, mkInt(pcreErrBadUtf8Offset), code))
  (andAll(okParts), ite(bad, mkInt(pcreErrBadOffset), code))

proc prioChosenLen(s: Z3String; p: Z3Int; pl: PrioLangs; fresh: FreshName;
                   defs: var seq[Z3Bool]; valid: Z3Bool): Z3Int =
  ## RFC-0005 S8bb. PCRE's (anchored) match length at absolute position `p`
  ## of `s` (`0 <= p <= s.len` where `valid`), or -1: a fresh Int fixed by
  ## a definitional constraint over the marked suffix (`lkMark`) and the
  ## no-match language (`lkNone`). Where not `valid` it is -1.
  let u = substr(s, p, len(s) - p)
  let k = mkIntVar(fresh("__regexLen"))
  let marked = concat(substr(u, mkInt(0), k), findMarker(),
                      substr(u, k, len(u) - k))
  let def = variant(pl, s, p, proc (v: int): Z3Bool =
    ((k == mkInt(-1)) and matches(u, pl.none[v])) or
    ((k >= mkInt(0)) and (k <= len(u)) and matches(marked, pl.mark[v])))
  defs.add ite(valid, def, k == mkInt(-1))
  k

proc prioEndsWith(s: Z3String; pl: PrioLangs): Z3Bool =
  ## RFC-0005 S8bb, S8bj. `endsWith(s, R)`: some `i < s.len` whose
  ## (anchored) match ends at the end -- `s[i..]` (non-empty) in `lkEnds`
  ## of the variant of `i`. Under UTF the subject must be valid (`matchLen`
  ## is an error code otherwise, and inside a character).
  var parts: seq[Z3Regex[Z3String]]
  for v, rep in pl.vars:
    var pre: seq[Z3Regex[Z3String]]
    for c in PrevClass:
      if canonPc0(pl.n, c) == rep: pre.add rawClassRe(c)
    parts.add concat((if pre.len == 1: pre[0] else: union(pre)), pl.ends[v])
  result = matches(s, (if parts.len == 1: parts[0] else: union(parts)))
  if pl.n.utf: result = result and matches(s, utf8ValidRe())
  if limitEffect(pl.n)[0] == leZero: result = mkBool(false)

proc prioLeftmost(pl: PrioLangs; s, u: Z3String; start: Z3Int;
                  fresh: FreshName; defs: var seq[Z3Bool];
                  callOk = mkBool(true)): (Z3Bool, Z3Int) =
  ## RFC-0005 S8bb. The match the search from `start` finds in `u` (the
  ## subject from `start`), from the search languages: whether there is
  ## one, and its offset `q` in `u` (0 when none) -- a fresh Int fixed by a
  ## definitional constraint over the marked `u` (`skFirst`).
  let occurs = not variant(pl, s, start, proc (v: int): Z3Bool =
    matches(u, pl.noOcc[v]))
  let q = mkIntVar(fresh("__regexFind"))
  let (pre, rest) = splitAt(u, q, fresh, "__regexFind", defs)
  let marked = concat(pre, findMarker(), rest)
  # RFC-0005 S8bj: only where the call runs without an error (in UTF mode
  # the languages say nothing of an invalid subject).
  defs.add ite((if pl.n.utf: callOk and occurs else: occurs),
    (q >= mkInt(0)) and (q <= len(u)) and
      variant(pl, s, start, proc (v: int): Z3Bool =
        matches(marked, pl.first[v])),
    q == mkInt(0))
  (occurs, q)

proc prioSpan(pl: PrioLangs; s, u: Z3String; start: Z3Int;
              fresh: FreshName; defs: var seq[Z3Bool];
              callOk = mkBool(true)): (Z3Bool, Z3Int) =
  ## RFC-0005 S8bj. The end `e` in `u` of the match the search finds (0
  ## when none), from `u` marked at its start and end (`skSpan`): for a
  ## pattern whose found attempt is not the anchored one (a SKIP:NAME
  ## without its MARK reads differently there).
  let occurs = not variant(pl, s, start, proc (v: int): Z3Bool =
    matches(u, pl.noOcc[v]))
  let q = mkIntVar(fresh("__regexFind"))
  let e = mkIntVar(fresh("__regexFindEnd"))
  let (pre, rest) = splitAt(u, q, fresh, "__regexFind", defs)
  let (mid, post) = splitAt(rest, e - q, fresh, "__regexFindEnd", defs)
  let marked = concat(@[pre, findMarker(), mid, findMarker2(), post])
  defs.add ite((if pl.n.utf: callOk and occurs else: occurs),
    (q >= mkInt(0)) and (q <= e) and (e <= len(u)) and
      variant(pl, s, start, proc (v: int): Z3Bool =
        matches(marked, pl.span[v])),
    (q == mkInt(0)) and (e == mkInt(0)))
  (occurs, e)

proc lowerCapture(sp: RegexSpec; pr: PcreParse; s: Z3String; start: Z3Int;
                  fresh: FreshName; arrLen: Z3Int; old: Z3String;
                  oldI: Z3Int): RxResult =
  ## RFC-0005 S8bb. One group of a captures overload, `sp.entry` being
  ## `capture|<call>|<g>`: the value of `matches[g - 1]` after the call
  ## (svString), `old` before it, `arrLen` the length of `matches`. For
  ## `findBounds`' bounds overload (`matches: var openArray[tuple[first,
  ## last: int]]`) `captureFirst` / `captureLast` are the element's fields
  ## (svInt; `oldI` the field before the call): the group's `(first, last)`
  ## in the subject, `(-1, 0)` when unset.
  ## `std/re` (Nim 2.2.10, probed): the call runs PCRE with an ovector of
  ## `arrLen + 1` pairs; on a match PCRE returns 1 + the highest SET group,
  ## or 0 when that group is past the ovector, and Nim writes `matches[i -
  ## 1]` for `i` in `1 ..< result` -- the group's span, or `""` when it is
  ## unset. So `matches[g - 1]` is written iff the call matched, no group
  ## past `arrLen` is set, and some group `>= g` is (and `g <= arrLen`).
  ## Nothing is written on a miss or an error. The match is PCRE's chosen
  ## one: the anchored attempt at `start` (`match`, `matchLen`) or the
  ## attempt the search finds (`find`, `contains`, `findBounds`; RFC-0005
  ## S8bj: an unanchored attempt, whose verbs read differently); its groups
  ## come from `pcre_select.captureLangV`.
  let parts = sp.entry.split('|')
  let what = parts[1]
  let g = parseInt(parts[2])
  let search = what in ["find", "contains", "findBounds"]
  let pl = prioLangs(sp, pr, not search, false, search)
  if not pl.ok: return unmodelled(sp.entry & ": " & pl.why)
  let n = pl.n
  if search and jitDeclines(n).len > 0:
    return unmodelled(sp.entry & ": " & jitDeclines(n))
  if limitEffect(n)[0] == leUnknown:
    return unmodelled(sp.entry & ": " & limitDecline)
  let key = sp.flag & ":" & sp.pattern
  # RFC-0005 S8bj: an unanchored attempt also reads whether it starts at a
  # CRLF's LF past the start offset (a SKIP:NAME without its MARK).
  let eligs = (if search and n.hasNeverSkip: @[false, true] else: @[false])
  var setRe, capRe: seq[seq[Z3Regex[Z3String]]]   # [group][variant*2+elig]
  for h in 1 .. pr.groups:
    var a, c: seq[Z3Regex[Z3String]]
    for pc in pl.vars:
      for el in [false, true]:
        if el and el notin eligs:
          a.add a[^1]
          if h == g: c.add c[^1]
          continue
        let ls = captureLangV(n, key, h, pc, false, not search, el)
        if not ls.ok: return unmodelled(sp.entry & ": " & ls.why)
        a.add selToZ3(ls.re)
        if h == g:
          let lc = captureLangV(n, key, h, pc, true, not search, el)
          if not lc.ok: return unmodelled(sp.entry & ": " & lc.why)
          c.add selToZ3(lc.re)
    setRe.add a
    capRe.add c
  let lenS = len(s)
  let u = substr(s, start, lenS - start)
  var res = RxResult(outcome: roValue)
  let (callOk, _) = callError(pl, s, start, not search, fresh, res.defs)
  var found: Z3Bool
  var p = start
  if search:
    let (occurs, q) = prioLeftmost(pl, s, u, start, fresh, res.defs, callOk)
    found = callOk and occurs
    p = start + q
  else:
    found = callOk and not variant(pl, s, start,
      proc (v: int): Z3Bool = matches(u, pl.none[v]))
  let w = substr(s, p, lenS - p)
  let elig = (if eligs.len == 2:
                (p > start) and rawClassIs(s, p, pcCR) and
                (toCode(at(s, p)) == mkInt(10))
              else: mkBool(false))
  proc atVariant(f: proc (i: int): Z3Bool): Z3Bool =
    variant(pl, s, p, proc (v: int): Z3Bool =
      ite(elig, f(2 * v + 1), f(2 * v)))
  proc isSet(h: int): Z3Bool =
    atVariant(proc (i: int): Z3Bool = matches(w, setRe[h - 1][i]))
  var fits, higher: seq[Z3Bool]
  for h in 1 .. pr.groups:
    fits.add (mkInt(h) <= arrLen) or not isSet(h)
    if h >= g: higher.add isSet(h)
  let written = found and (mkInt(g) <= arrLen) and andAll(fits) and
                orAll(higher)
  let a = mkIntVar(fresh("__regexCapStart"))
  let b = mkIntVar(fresh("__regexCapEnd"))
  let (wa, wRest) = splitAt(w, a, fresh, "__regexCapStart", res.defs)
  let (span, wb) = splitAt(wRest, b - a, fresh, "__regexCapEnd", res.defs)
  let marked = concat(@[wa, findMarker(), span, findMarker2(), wb])
  let on = found and isSet(g)
  res.defs.add ite(on,
    (a >= mkInt(0)) and (a <= b) and (b <= len(w)) and
      atVariant(proc (i: int): Z3Bool = matches(marked, capRe[g - 1][i])),
    (a == mkInt(0)) and (b == mkInt(0)))
  case parts[0]
  of "captureFirst":
    res.i = ite(written, ite(on, p + a, mkInt(-1)), oldI)
  of "captureLast":
    res.i = ite(written, ite(on, p + b - mkInt(1), mkInt(0)), oldI)
  else:
    res.s = ite(written, ite(on, span, mkString("")), old)
  res

proc lowerPrio(sp: RegexSpec; pr: PcreParse; s: Z3String; start: Z3Int;
               fresh: FreshName; why: string): RxResult =
  ## RFC-0005 S8bb, S8bj. Every entry from the priority automaton: the
  ## anchored attempt (`match`, `matchLen`, `startsWith`, `endsWith`) or
  ## the search (`find`, `contains`, `findBounds`), with `pcre_exec`'s
  ## errors (`callError`).
  let search = sp.entry in ["contains", "find", "findBoundsFirst",
                            "findBoundsFirstCap", "findBoundsLast"]
  let last = sp.entry == "findBoundsLast"
  var pl = prioLangs(sp, pr, last or not search and sp.entry != "endsWith",
                     sp.entry == "endsWith", search)
  if pl.ok and last and pl.n.hasNeverSkip:
    pl = prioLangs(sp, pr, false, false, true, true)
  if not pl.ok: return unmodelled(sp.entry & ": " & why & pl.why)
  let n = pl.n
  if limitEffect(n)[0] == leUnknown:
    return unmodelled(sp.entry & ": " & limitDecline)
  if search and jitDeclines(n).len > 0:
    return unmodelled(sp.entry & ": " & jitDeclines(n))
  let lenS = len(s)
  let u = substr(s, start, lenS - start)
  var res = RxResult(outcome: roValue)
  if sp.entry == "endsWith":
    res.b = prioEndsWith(s, pl)
    return res
  if sp.entry == "startsWith":
    # `matchLen(s, R, 0) >= 0`.
    let (ok0, _) = callError(pl, s, mkInt(0), true, fresh, res.defs)
    res.b = ok0 and not matches(s, pl.none[pl.vars.find(canonPc0(n, pcStart))])
    return res
  let (ok, err) = callError(pl, s, start, not search, fresh, res.defs)
  if search:
    let (occurs, q) = prioLeftmost(pl, s, u, start, fresh, res.defs, ok)
    case sp.entry
    of "contains":
      res.b = ok and occurs
    of "find", "findBoundsFirst":
      res.i = ite(ok, ite(occurs, start + q, mkInt(-1)), err)
    of "findBoundsFirstCap":
      res.i = ite(ok and occurs, start + q, mkInt(-1))
    else:
      # The found match's end: the anchored attempt's at `q` (the same
      # match), or the span language's.
      var e: Z3Int
      if pl.span.len > 0:
        e = start + prioSpan(pl, s, u, start, fresh, res.defs, ok)[1]
      else:
        let first = start + q
        e = first + prioChosenLen(s, first, pl, fresh, res.defs, ok and occurs)
      res.i = ite(ok and occurs, e - mkInt(1), mkInt(0))
    return res
  case sp.entry
  of "match":
    # `matchLen != -1`: an error code reads as a match.
    res.b = (not ok) or not variant(pl, s, start, proc (v: int): Z3Bool =
      matches(u, pl.none[v]))
  of "matchLen":
    res.i = ite(ok, prioChosenLen(s, start, pl, fresh, res.defs, ok), err)
  else:
    raiseAssert "lowerPrio: entry `" & sp.entry & "`"
  res

proc lowerRegexEntry*(sp: RegexSpec; pr: PcreParse; s: Z3String;
                      start: Z3Int; fresh: FreshName;
                      arrLen = mkInt(0); old = mkString("");
                      oldI = mkInt(0)): RxResult =
  ## RFC-0005 S8ay. The value of `sp.entry` on subject `s` from `start` (0
  ## for `startsWith` / `endsWith`). `replace` is lowered by the walker
  ## (`runtime_strings.nim`), not here. RFC-0005 S8bb: a captures
  ## overload's group (`lowerCapture`; `arrLen` the `matches` length, `old`
  ## the element before the call, `oldI` a bounds element's field).
  case pr.status
  of psRejected: return RxResult(outcome: roRejected, msg: pr.errMsg)
  of psUnknown: return RxResult(outcome: roUnknown, msg: pr.reason)
  of psUnmodelled:
    return unmodelled(pr.reason)
  of psOk: discard
  if sp.entry.startsWith("capture"):
    return lowerCapture(sp, pr, s, start, fresh, arrLen, old, oldI)
  let (fine, edges, why) = splitEdges(pr.root)
  let lenS = len(s)
  let bad = (start < mkInt(0)) or (start > lenS)
  let u = substr(s, start, lenS - start)
  let st0 = start == mkInt(0)
  if not fine or pr.nl != nlLF or s8bjRoute(pr):
    # RFC-0005 S8bb: an anchor away from a top-level edge, `(*ACCEPT)`, a
    # verb, or a newline convention other than LF (whose `$` and bumpalong
    # the edge-split reading does not know); RFC-0005 S8bj: UTF mode or a
    # limit start option: every entry is the priority automaton's.
    return lowerPrio(sp, pr, s, start, fresh,
                     (if fine: "" else: why & "; "))
  let anyByte = byteSetRe(pcreAnyByte)
  var nb, bl: seq[Z3Regex[Z3String]]
  var nbM: seq[Z3Regex[Z3String]]
  for e in edges:
    let r = concat(rxToZ3(e.body), tailRe(e.eol))
    if e.bol: bl.add r
    else:
      nb.add r
      nbM.add concat(rxToZ3(e.body, marked = true), tailRe(e.eol, true))
  let nbRe = (if nb.len == 0: mkRegexEmpty[Z3String]()
              elif nb.len == 1: nb[0] else: union(nb))
  let blRe = (if bl.len == 0: mkRegexEmpty[Z3String]()
              elif bl.len == 1: bl[0] else: union(bl))
  proc inNb(x: Z3String): Z3Bool =
    (if nb.len > 0: matches(x, nbRe) else: mkBool(false))
  proc inBl(x: Z3String): Z3Bool =
    (if bl.len > 0: matches(x, blRe) else: mkBool(false))
  let occurs = (if nb.len > 0: matches(u, concat(star(anyByte), nbRe))
                else: mkBool(false)) or (st0 and inBl(u))
  var res = RxResult(outcome: roValue)
  proc leftmost(res: var RxResult): Z3Int =
    # The leftmost occurrence offset `q` in `u` (when `occurs`): a match
    # starts at `q`, and none starts earlier -- for an anchor-free
    # alternative, the marked subject `u[0..<q] & '#' & u[q..]` is not in
    # `B* . X`, X the words of the language with one marker inserted after
    # a non-empty prefix (`rxToZ3(marked = true)` intersected with "exactly
    # one marker").
    let q = mkIntVar(fresh("__regexFind"))
    let rest = substr(u, q, len(u) - q)
    var atQ = @[inNb(rest)]
    if bl.len > 0: atQ.add((q == mkInt(0)) and st0 and inBl(u))
    var earlier: seq[Z3Bool]
    if bl.len > 0: earlier.add(st0 and (q > mkInt(0)) and inBl(u))
    if nb.len > 0:
      let marked = concat(substr(u, mkInt(0), q), findMarker(), rest)
      let one = concat(star(anyByte), mkRegex(findMarker()), star(anyByte))
      let x = intersect(one, (if nbM.len == 1: nbM[0] else: union(nbM)))
      earlier.add matches(marked, concat(star(anyByte), x))
    res.defs.add ite(occurs,
      (q >= mkInt(0)) and (q <= len(u)) and orAll(atQ) and not orAll(earlier),
      q == mkInt(0))
    q
  case sp.entry
  of "match":
    res.b = bad or inNb(u) or (st0 and inBl(u))
  of "startsWith":
    res.b = inNb(s) or inBl(s)
  of "contains":
    res.b = (not bad) and occurs
  of "find", "findBoundsFirst":
    let q = leftmost(res)
    res.i = ite(bad, mkInt(-24), ite(occurs, start + q, mkInt(-1)))
  of "findBoundsFirstCap":
    # RFC-0005 S8bb: the captures overload of `findBounds` returns
    # `(-1, 0)` on every PCRE error, a bad offset included (probed); the
    # plain one returns the error code first.
    let q = leftmost(res)
    res.i = ite((not bad) and occurs, start + q, mkInt(-1))
  of "matchLen", "endsWith", "findBoundsLast":
    let f = selectionForm(edges)
    if f.kind == skNone:
      # RFC-0005 S8bb: PCRE's priority order (`pcre_select`).
      let pl = prioLangs(sp, pr, sp.entry != "endsWith",
                         sp.entry == "endsWith")
      if not pl.ok:
        return unmodelled(sp.entry & " depends on which match PCRE picks: " &
                          f.why & "; " & pl.why)
      case sp.entry
      of "matchLen":
        res.i = ite(bad, mkInt(-24),
                    prioChosenLen(s, start, pl, fresh, res.defs, not bad))
      of "endsWith":
        res.b = prioEndsWith(s, pl)
      else:
        let q = leftmost(res)
        let first = start + q
        let ml = prioChosenLen(s, first, pl, fresh, res.defs,
                               (not bad) and occurs)
        res.i = ite(bad or not occurs, mkInt(0), first + ml - mkInt(1))
      return res
    case sp.entry
    of "matchLen":
      res.i = ite(bad, mkInt(-24), chosenLen(s, start, f, fresh, res.defs))
    of "endsWith":
      # The chosen match at `i` is the longest, so it reaches the end iff
      # `s[i..]` is in the body's language (`i < s.len`: non-empty).
      let bodyRe = rxToZ3(f.body)
      res.b =
        if f.bol: (lenS >= mkInt(1)) and matches(s, bodyRe)
        else: matches(s, concat(star(anyByte),
                                intersect(bodyRe, plus(anyByte))))
    else:
      let q = leftmost(res)
      let first = start + q
      let ml = chosenLen(s, first, f, fresh, res.defs)
      res.i = ite(bad or not occurs, mkInt(0), first + ml - mkInt(1))
  else:
    raiseAssert "lowerRegexEntry: entry `" & sp.entry & "`"
  res

# ---- RFC-0005 S8bb (item 6): `replace` by the priority run ----------------------

proc replaceRunZ3*(s, by: Z3String; t: RunTable; nl: NlConv;
                   fresh: FreshName): Z3String =
  ## RFC-0005 S8bb (item 6). Nim's `replace(s, re, by)` for any pattern the
  ## priority run reads (an alternation, an anchor, a pattern that matches
  ## empty), as two recursive functions over the subject's suffixes:
  ##   * `run(u, st)`: the rest of `u` after PCRE's chosen match for the
  ##     Pike run in state `st` at `u`'s start, or the marker (code 256,
  ##     outside every byte) when there is none -- the match ends at the
  ##     last position where a thread reached `Match`
  ##     (`pcre_select.chosenEnd`), stepped by the table `t`
  ##     (`pcre_select.runTable`);
  ##   * `rep(u, flags, fuel)`: the output from search position `u`
  ##     (flags: NOTEMPTY_ATSTART there, and whether it is subject position
  ##     0). A match at `u`'s start emits `by`; an empty one (the rest is
  ##     `u`) retries at the same position under NOTEMPTY_ATSTART, a
  ##     non-empty one resumes at the rest, and Nim's loop stops once a
  ##     match reaches the end (the rest is empty). No match keeps `u[0]`
  ##     and searches on from the next byte (PCRE's bumpalong,
  ##     NOTEMPTY_ATSTART at the start offset only). An empty receiver is
  ##     returned as is (Nim's loop never runs).
  ## Every recursive call names its state by a numeral, so Z3 instantiates
  ## the body at that state alone, and every argument is a suffix of `s`
  ## (never a value), which keeps the rewriter from unfolding a call
  ## eagerly. Measured on Z3 5.1 against the alternatives
  ## (`tests/tprobe_s8bb_rep.nim`, scratch): a state chosen by an `ite`
  ## term ran out of the resource limit on "ab" / `x*`; an integer
  ## position argument made the rewriter unfold without end; a match end
  ## returned as an offset (the rest a `substr` at it, or dropped one byte
  ## per call) left `len(s) == 2 and replace(s, re"a|ab", "x") == "x"`
  ## undecided under the byte-range constraint of a free string (ADR-0006),
  ## which the rest-as-suffix form refutes in 2.5 s.
  ## The `fuel` argument is load-bearing, not a cut: `rep`'s argument is
  ## `run`'s result, which Z3 cannot see is shorter than `u`, so without a
  ## decreasing bound it unfolded `rep(run(run(...)))` without end and
  ## without spending its resource limit (`len(s) == 1 and
  ## s.replace(re"$", "-") == "q-"` ran past 1000 s under a 20M `rlimit`,
  ## on Z3 5.1 and 4.13.4: 96k steps counted in 15 s). With it the same
  ## query is SAT in 0.3 s and every unfolding is bounded by `len(s)`.
  ## Pinned against `std/re` (`tests/tsymex_rfc0005_s8bb_replace.nim`).
  let ctx = s.ctx
  let empty = mkString("")
  let mark = findMarker()
  let nlSet = nlBytes(nl)
  let pair = nlPair(nl)
  # RFC-0005 S8bi: `run` carries fuel too (`len(u) + 1` at each call from
  # `rep`, one less per unfolding; each unfolding drops a byte, so a real
  # run never exhausts it), so no unfolding of it is unbounded whatever Z3
  # makes of `tl`.
  let run = defineRecFun[Z3String, Z3Int, Z3Int, Z3String](ctx,
    fresh("__regexRun"),
    proc (self: Z3FuncDecl[(Z3String, Z3Int, Z3Int), Z3String]; u: Z3String;
          st, fuel: Z3Int): Z3String =
      let f1 = fuel - mkInt(1)
      let lenU = len(u)
      let atEnd = lenU == mkInt(0)
      let b = toCode(at(u, mkInt(0)))
      let lf = b == mkInt(10)
      var nll = (lenU == mkInt(1)) and inSet(b, nlSet)
      if pair:
        nll = nll or ((lenU == mkInt(2)) and (b == mkInt(13)) and
                      (toCode(at(u, mkInt(1))) == mkInt(10)))
      let tl = substr(u, mkInt(1), lenU - mkInt(1))
      proc call(tgt: int32): Z3String =
        (if tgt < 0: mark else: self(tl, mkInt(int(tgt)), f1))
      proc row(r: array[256, int32]): Z3String =
        # The byte partition by target, the largest part the default.
        var parts = initTable[int32, set[char]]()
        for x in 0 .. 255:
          parts.mgetOrPut(r[x], {}).incl char(x)
        var dflt = r[0]
        var best = -1
        for tgt, cs in parts:
          if card(cs) > best:
            best = card(cs)
            dflt = tgt
        result = call(dflt)
        for tgt, cs in parts:
          if tgt != dflt:
            result = ite(inSet(b, cs), call(tgt), result)
      proc byLf(a: array[2, bool]): Z3Bool =
        if a[0] == a[1]: mkBool(a[0])
        else: ite(lf, mkBool(a[1]), mkBool(a[0]))
      result = mark
      for k in countdown(t.matched.high, 0):
        let m = t.matched[k]
        let mk = ite(atEnd, mkBool(m[rcEnd][0]),
                     (if m[rcNll] == m[rcOther]: byLf(m[rcOther])
                      else: ite(nll, byLf(m[rcNll]), byLf(m[rcOther]))))
        let nx = t.next[k]
        let later =
          if nx[rcNll] == nx[rcOther]: row(nx[rcOther])
          else: ite(nll, row(nx[rcNll]), row(nx[rcOther]))
        let here = ite(mk, u, mark)
        let rk = ite(atEnd, here, ite(later != mark, later, here))
        result = ite(st == mkInt(k), rk, result)
      result = ite(fuel <= mkInt(0), mark, result))
  # `rep(u, flags, fuel)`: flags 1 = NOTEMPTY_ATSTART, 2 = subject
  # position 0 (numerals at every call). `fuel` counts the calls left: each
  # call drops at least one byte or is the one NOTEMPTY_ATSTART retry at
  # its position, so `2 * len(s) + 2` never runs out on a real run.
  let rep = defineRecFun[Z3String, Z3Int, Z3Int, Z3String](ctx,
    fresh("__regexReplaceRun"),
    proc (self: Z3FuncDecl[(Z3String, Z3Int, Z3Int), Z3String];
          u: Z3String; flags, fuel: Z3Int): Z3String =
      let lenU = len(u)
      let ne = (flags == mkInt(1)) or (flags == mkInt(3))
      let st0 = flags >= mkInt(2)
      proc start(bol: int): Z3String =
        ite(ne, run(u, mkInt(t.start[bol][1]), lenU + mkInt(1)),
            run(u, mkInt(t.start[bol][0]), lenU + mkInt(1)))
      let r = (if t.start[1] == t.start[0]: start(0)
               else: ite(st0, start(1), start(0)))
      let f1 = fuel - mkInt(1)
      ite(fuel <= mkInt(0), empty,
          ite(r != mark,
              concat(by, ite(len(r) == mkInt(0), empty,
                             ite(len(r) == lenU,
                                 self(u, flags + mkInt(1), f1),
                                 self(r, mkInt(0), f1)))),
              ite(lenU == mkInt(0), empty,
                  concat(at(u, mkInt(0)),
                         self(substr(u, mkInt(1), lenU - mkInt(1)),
                              mkInt(0), f1))))))
  ite(len(s) == mkInt(0), empty,
      rep(s, mkInt(2), mkInt(2) * len(s) + mkInt(2)))

# ---- RFC-0005 S8bj: `replace` by the agenda's step table ---------------------

proc codeStr(c: int): Z3String = simplify(fromCode(mkInt(c)))

proc replaceStepZ3*(s, by: Z3String; n: Nfa; t: StepTable;
                    fresh: FreshName): Z3String =
  ## RFC-0005 S8bj. Nim's `replace(s, re, by)` for every pattern the S8bb
  ## run does not read (a verb, a `(?m)` anchor, UTF mode, an observable
  ## CRLF start skip): `replaceRunZ3`'s two recursive functions over the
  ## subject's suffixes, generalized.
  ##   * `run(u, st)`: the outcome of the attempt (`pcre_select.stepTable`)
  ##     in state `st` at `u`'s start: the rest after its match; code 256
  ##     (no match: bump along); code 257 (`(*COMMIT)`); code 258 then the
  ##     rest at a `(*SKIP)` landing. A match or landing recorded at an
  ##     earlier position (a register of `st`) is returned as the one
  ##     character `300 + 2 * register + skip` and resolved by the call
  ##     that recorded it (where the position is its own `u`): the
  ##     registers never become arguments.
  ##   * `rep(u, mode, fuel)`: the output from `u`, `mode` the numeral of
  ##     the search cursor (at the call's start offset, with or without
  ##     NOTEMPTY_ATSTART; scanning; just bumped or landed, where the CRLF
  ##     skip applies; inside a UTF-8 character) and the class of the byte
  ##     before `u` (`pcre_select.PrevClass`). It follows pcre_exec.c's
  ##     loop: the start-of-match scan, the attempt, the bump by one
  ##     character, the SKIP's jump, the COMMIT's end; on a miss the rest
  ##     is kept (std/re's loop ends), after a match it emits `by` and calls
  ##     PCRE again from the match's end.
  ## An invalid UTF-8 subject is returned as is (every call is an error).
  ## Pinned against `std/re` (`tests/tsymex_rfc0005_s8bj_replace.nim`).
  let ctx = s.ctx
  let empty = mkString("")
  let bump = codeStr(256)
  let commit = codeStr(257)
  let skipMark = codeStr(258)
  let nlSet = nlBytes(n.nl)
  let pair = nlPair(n.nl)
  proc refStr(reg: int; skip: bool): Z3String =
    codeStr(300 + 2 * reg + ord(skip))
  # RFC-0005 batch 5 (S8bi's fuel on S8bj's `run`): `fuel` is `len(u) + 1`
  # at each call from `rep`, one less per unfolding; each unfolding drops a
  # byte, so a real run never exhausts it, and no unfolding is unbounded
  # whatever Z3 makes of `tl`.
  let run = defineRecFun[Z3String, Z3Int, Z3Int, Z3String](ctx,
    fresh("__regexStep"),
    proc (self: Z3FuncDecl[(Z3String, Z3Int, Z3Int), Z3String]; u: Z3String;
          st, fuel: Z3Int): Z3String =
      let f1 = fuel - mkInt(1)
      let lenU = len(u)
      let atEnd = lenU == mkInt(0)
      let b = toCode(at(u, mkInt(0)))
      var nll = (lenU == mkInt(1)) and inSet(b, nlSet)
      if pair:
        nll = nll or ((lenU == mkInt(2)) and (b == mkInt(13)) and
                      (toCode(at(u, mkInt(1))) == mkInt(10)))
      let tl = substr(u, mkInt(1), lenU - mkInt(1))
      proc leafVal(lf: Leaf): Z3String =
        case lf.kind
        of lfBump: result = bump
        of lfCommit: result = commit
        of lfMatch: result = (if lf.reg < 0: u else: refStr(lf.reg, false))
        of lfSkip:
          result = (if lf.reg < 0: concat(skipMark, u)
                    else: refStr(lf.reg, true))
        of lfNext:
          let later = self(tl, mkInt(int(lf.next)), f1)
          result = later
          for i in countdown(lf.regMap.high, 0):
            let m = lf.regMap[i]
            for skip in [false, true]:
              let here =
                if m >= 0: refStr(m, skip)
                elif skip: concat(skipMark, u)
                else: u
              result = ite(later == refStr(i, skip), here, result)
      proc row(leaves: seq[Leaf]): Z3String =
        # The bytes grouped by leaf, the largest group the default.
        var groups: seq[(Leaf, set[char])]
        for x in 0 .. 255:
          var found = false
          for g in groups.mitems:
            if g[0] == leaves[x]:
              g[1].incl char(x)
              found = true
              break
          if not found: groups.add (leaves[x], {char(x)})
        var dflt = 0
        for gi, g in groups:
          if card(g[1]) > card(groups[dflt][1]): dflt = gi
        result = leafVal(groups[dflt][0])
        for gi, g in groups:
          if gi != dflt:
            result = ite(inSet(b, g[1]), leafVal(g[0]), result)
      result = bump
      for k in countdown(t.rows.high, 0):
        let r = t.rows[k]
        var nllLeaves = r.nll
        for x in 0 .. 255:
          if char(x) notin nlSet and not (pair and x == 13):
            nllLeaves[x] = r.other[x]
        let body = ite(atEnd, leafVal(r.atEnd),
                       (if nllLeaves == r.other: row(r.other)
                        else: ite(nll, row(nllLeaves), row(r.other))))
        result = ite(st == mkInt(k), body, result)
      result = ite(fuel <= mkInt(0), bump, result))
  # The modes: cursor * 8 + the class before `u`.
  const cuS0 = 0
  const cuS0ne = 1
  const cuScan = 2
  const cuLanded = 3
  const cuMid = 4
  let anchored = n.anchoredPat
  let pcs = (if n.needPc: @[pcStart, pcOther, pcLF, pcCRLF, pcCR, pcNl]
             else: @[pcStart, pcOther])
  proc modeNum(cur: int; pc: PrevClass): Z3Int = mkInt(cur * 8 + ord(pc))
  let rep = defineRecFun[Z3String, Z3Int, Z3Int, Z3String](ctx,
    fresh("__regexStepReplace"),
    proc (self: Z3FuncDecl[(Z3String, Z3Int, Z3Int), Z3String];
          u: Z3String; mode, fuel: Z3Int): Z3String =
      let lenU = len(u)
      let b = toCode(at(u, mkInt(0)))
      let tl = substr(u, mkInt(1), lenU - mkInt(1))
      let f1 = fuel - mkInt(1)
      proc next(c: char; pc: PrevClass): PrevClass =
        (if n.needPc: nextClass(c, pc) else: pcOther)
      proc callAfter(v: Z3String; cur: int; pcOf: proc (c: char): PrevClass;
                     lastByte: Z3Int): Z3String =
        # `self(v, cur, class)`, the class read off the byte before `v`
        # (`lastByte`) as numerals.
        var byClass: seq[(PrevClass, set[char])]
        for x in 0 .. 255:
          let c = pcOf(char(x))
          var found = false
          for g in byClass.mitems:
            if g[0] == c:
              g[1].incl char(x)
              found = true
          if not found: byClass.add (c, {char(x)})
        result = self(v, modeNum(cur, byClass[0][0]), f1)
        for gi in 1 ..< byClass.len:
          result = ite(inSet(lastByte, byClass[gi][1]),
                       self(v, modeNum(cur, byClass[gi][0]), f1), result)
      proc step(cur: int; pc: PrevClass): Z3String =
        # Keep `u[0]`, go on from the next byte.
        concat(at(u, mkInt(0)),
               callAfter(tl, cur, proc (c: char): PrevClass = next(c, pc), b))
      proc restAt(v: Z3String; cur: int; pc: PrevClass): Z3String =
        # Go on from the suffix `v` of `u` (shorter than `u`).
        let d = lenU - len(v)
        let b1 = toCode(at(u, d - mkInt(1)))
        if not n.needPc:
          return self(v, modeNum(cur, pcOther), f1)
        # The class before `v`: its last byte, and a CR before an LF.
        let prevCR = ite(d >= mkInt(2), toCode(at(u, d - mkInt(2))) == mkInt(13),
                         mkBool(pc == pcCR))
        ite(b1 == mkInt(10),
            ite(prevCR, self(v, modeNum(cur, pcCRLF), f1),
                self(v, modeNum(cur, pcLF), f1)),
            callAfter(v, cur, proc (c: char): PrevClass = next(c, pcOther), b1))
      proc attempt(pc: PrevClass; ne, elig: bool): Z3String =
        let st = t.start[(canonPc0(n, pc), ne, elig)]
        let r = run(u, mkInt(st), lenU + mkInt(1))
        let lenR = len(r)
        let isSkip = (lenR >= mkInt(1)) and
                     (substr(r, mkInt(0), mkInt(1)) == skipMark)
        let landing = substr(r, mkInt(1), lenR - mkInt(1))
        let bumped =
          if anchored: u
          else: ite(lenU == mkInt(0), empty,
                    step((if n.utf: cuMid else: cuLanded), pc))
        let skipped =
          if anchored: u
          else: ite(len(landing) < lenU,
                    concat(substr(u, mkInt(0), lenU - len(landing)),
                           restAt(landing, cuLanded, pc)),
                    bumped)
        let matched = concat(by, ite(lenR == mkInt(0), empty,
          ite(lenR == lenU, self(u, modeNum(cuS0ne, pc), f1),
              restAt(r, cuS0, pc))))
        ite(r == bump, bumped, ite(r == commit, u,
            ite(isSkip, skipped, matched)))
      proc created(pc: PrevClass; atS0: bool): Z3Bool =
        # The start-of-match scan stops here.
        if anchored: return mkBool(true)
        case n.filter
        of fkNone: mkBool(true)
        of fkFirst, fkBits:
          (lenU == mkInt(0)) or inSet(b, n.filterBytes)
        of fkStartline:
          if atS0: mkBool(true)
          elif not wasNl(n.nl, pc): lenU == mkInt(0)
          elif pc == pcCR and n.nl in {nlANY, nlANYCRLF}:
            (lenU == mkInt(0)) or (b != mkInt(10))
          else: mkBool(true)
      proc body(cur: int; pc: PrevClass): Z3String =
        case cur
        of cuMid:
          ite((lenU > mkInt(0)) and inSet(b, {'\x80'..'\xBF'}),
              step(cuMid, pc), body(cuLanded, pc))
        of cuLanded:
          if n.skipActive and pc == pcCR:
            ite((lenU > mkInt(0)) and (b == mkInt(10)), step(cuScan, pc),
                body(cuScan, pc))
          else: body(cuScan, pc)
        of cuScan:
          let elig = n.hasNeverSkip and n.skipActive and pc == pcCR
          let go =
            if elig:
              ite((lenU > mkInt(0)) and (b == mkInt(10)),
                  attempt(pc, false, true), attempt(pc, false, false))
            else: attempt(pc, false, false)
          ite(created(pc, false), go,
              ite(lenU == mkInt(0), empty, step(cuScan, pc)))
        else:
          let go = attempt(pc, cur == cuS0ne, false)
          ite(created(pc, true), go,
              ite(lenU == mkInt(0), empty, step(cuScan, pc)))
      result = empty
      for cur in [cuS0, cuS0ne, cuScan, cuLanded, cuMid]:
        if anchored and cur >= cuScan: continue
        if cur == cuMid and not n.utf: continue
        for pc in pcs:
          if pc == pcStart and cur >= cuScan: continue
          result = ite(mode == modeNum(cur, pc), body(cur, pc), result)
      result = ite(fuel <= mkInt(0), empty, result))
  result = ite(len(s) == mkInt(0), empty,
               rep(s, modeNum(cuS0, pcStart), mkInt(2) * len(s) + mkInt(2)))
  if n.utf: result = ite(matches(s, utf8ValidRe()), result, s)

# ---- RFC-0005 S8bj (item 5): facts of a `replace` value ------------------------

proc replaceLemmas*(s, by, r: Z3String; atoms: seq[set[char]]; plus: bool;
                    fresh: FreshName): seq[Z3Bool] =
  ## RFC-0005 S8bj. Facts of `r = replace(s, re, by)` for an S8aw shape
  ## (`atoms` a sequence of byte sets, one under a greedy `+` when `plus`),
  ## true of every receiver; Z3's unfolding of the exact recursive term
  ## does not reach them (S8bb's Q2, Q7, Q8 stayed `unknown`):
  ##   * the lengths: `k` matches removing `c` bytes, `len(r) = len(s) - c
  ##     + k * len(by)`, each match `m = atoms.len` bytes (at least `m`
  ##     under `plus`), `c <= len(s)` -- stated when `len(by)` is a numeral
  ##     (linear arithmetic);
  ##   * the image: for one byte set `S` and a literal `by`, every byte of
  ##     `s` in `S` is inside a match (a `+` run is maximal, a single byte
  ##     is its own match), so `r` is bytes outside `S` and copies of `by`:
  ##     `r in ([^S] | by)*`.
  let lenBy = simplify(len(by))
  if isNumeralAst(lenBy.ctx, lenBy.raw):
    let nb = parseInt(getNumeralString(lenBy))
    let m = atoms.len
    let k = mkIntVar(fresh("__regexReplaceK"))
    let c = mkIntVar(fresh("__regexReplaceC"))
    result.add (k >= mkInt(0)) and (c <= len(s)) and
               (len(r) == len(s) - c + k * mkInt(nb))
    result.add(if plus: c >= k * mkInt(m) else: c == k * mkInt(m))
  if atoms.len == 1:
    let byS = simplify(by)
    if Z3_is_string(byS.ctx.raw, byS.raw):
      result.add matches(r, star(union(byteSetRe(pcreAnyByte - atoms[0]),
                                       mkRegex(byS))))
      # The same fact per byte, as `contains` (Z3 4.13.4 does not derive
      # `not contains(r, "ff")` from the membership): a matched byte `b`
      # that `by` does not contain is not in `r`. Stated for a small set of
      # plain ASCII bytes (no literal-escape question); sound to omit.
      const plainBytes = {'0'..'9', 'a'..'z', 'A'..'Z', ' ', ',', '.', ':',
                          ';', '-', '_', '/', '+', '=', '!', '?', '@', '#'}
      let byCodes = getStringContents(byS)
      if card(atoms[0]) <= 16 and atoms[0] <= plainBytes:
        for b in atoms[0]:
          if ord(b) notin byCodes:
            result.add not contains(r, mkString($b))
