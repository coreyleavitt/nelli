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
  of rxBol, rxEol, rxEolAbs, rxAccept:
    raiseAssert "rxToZ3: anchors and (*ACCEPT) are split off first"

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

proc selToZ3*(r: RNode): Z3Regex[Z3String] =
  ## RFC-0005 S8bb. A `pcre_select` regex as Z3's.
  case r.kind
  of rkEmpty: mkRegexEmpty[Z3String]()
  of rkEps: epsRe()
  of rkSet: byteSetRe(r.bytes)
  of rkMark: mkRegex(findMarker())
  of rkMark2: mkRegex(findMarker2())
  of rkStar: star(selToZ3(r.kids[0]))
  of rkCat, rkAlt:
    var parts: seq[Z3Regex[Z3String]]
    for k in r.kids: parts.add selToZ3(k)
    if parts.len == 1: parts[0]
    elif r.kind == rkCat: concat(parts)
    else: union(parts)

type PrioLangs = object
  ## RFC-0005 S8bb. A pattern's selection languages, per `atStart` variant
  ## (index 1: the subject position is 0; one variant when the pattern has
  ## no `^` / `\A`, where it does not matter).
  ok: bool
  why: string
  hasBol: bool
  mark, none, ends, noOcc, first: array[2, Z3Regex[Z3String]]

proc prioLangs(sp: RegexSpec; pr: PcreParse; wantEnds: bool;
               wantSearch = false): PrioLangs =
  let n = buildNfa(pr)
  let key = sp.flag & ":" & sp.pattern
  result.hasBol = n.hasBol
  result.ok = true
  for v in 0 .. 1:
    if v == 1 and not n.hasBol: break
    let atStart = v == 1
    var langs: seq[(LangKind, bool)] = @[(lkMark, false), (lkNone, false)]
    if wantEnds: langs.add (lkEnds, true)
    for (lk, nonEmpty) in langs:
      # `lkEnds` serves `endsWith`'s suffixes, never empty.
      let l = selectionLang(n, key, lk, atStart, nonEmpty = nonEmpty)
      if not l.ok:
        return PrioLangs(ok: false, why: l.why)
      let z = selToZ3(l.re)
      case lk
      of lkMark: result.mark[v] = z
      of lkNone: result.none[v] = z
      of lkEnds: result.ends[v] = z
    if wantSearch:
      for sk in [skNoOcc, skFirst]:
        let l = searchLang(n, key, sk, atStart)
        if not l.ok:
          return PrioLangs(ok: false, why: l.why)
        if sk == skNoOcc: result.noOcc[v] = selToZ3(l.re)
        else: result.first[v] = selToZ3(l.re)

proc variant(pl: PrioLangs; atStart: Z3Bool;
             f: proc (v: int): Z3Bool): Z3Bool =
  if pl.hasBol: ite(atStart, f(1), f(0)) else: f(0)

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

proc prioChosenLen(s: Z3String; p: Z3Int; pl: PrioLangs; fresh: FreshName;
                   defs: var seq[Z3Bool]; valid: Z3Bool): Z3Int =
  ## RFC-0005 S8bb. PCRE's match length at absolute position `p` of `s`
  ## (`0 <= p <= s.len` where `valid`), or -1: a fresh Int fixed by a
  ## definitional constraint over the marked suffix (`lkMark`) and the
  ## no-match language (`lkNone`). Where not `valid` it is -1.
  let u = substr(s, p, len(s) - p)
  let k = mkIntVar(fresh("__regexLen"))
  let marked = concat(substr(u, mkInt(0), k), findMarker(),
                      substr(u, k, len(u) - k))
  let def = variant(pl, p == mkInt(0), proc (v: int): Z3Bool =
    ((k == mkInt(-1)) and matches(u, pl.none[v])) or
    ((k >= mkInt(0)) and (k <= len(u)) and matches(marked, pl.mark[v])))
  defs.add ite(valid, def, k == mkInt(-1))
  k

proc prioEndsWith(s: Z3String; pl: PrioLangs): Z3Bool =
  ## RFC-0005 S8bb. `endsWith(s, R)`: some `i < s.len` whose match ends at
  ## the end -- `s[i..]` (non-empty) in `lkEnds` of the variant of `i == 0`.
  let anyByte = byteSetRe(pcreAnyByte)
  if pl.hasBol:
    (len(s) >= mkInt(1) and matches(s, pl.ends[1])) or
      matches(s, concat(plus(anyByte), pl.ends[0]))
  else:
    matches(s, concat(star(anyByte), pl.ends[0]))

proc prioLeftmost(pl: PrioLangs; u: Z3String; st0: Z3Bool; fresh: FreshName;
                  defs: var seq[Z3Bool]): (Z3Bool, Z3Int, Z3String) =
  ## RFC-0005 S8bb. The leftmost match in `u` (the subject from `start`;
  ## `st0`: `start == 0`), from the search languages: whether one occurs,
  ## its offset `q` in `u` (0 when none) -- a fresh Int fixed by a
  ## definitional constraint over the marked `u` (`skFirst`) -- and
  ## `u[q ..]`.
  let occurs = not variant(pl, st0, proc (v: int): Z3Bool =
    matches(u, pl.noOcc[v]))
  let q = mkIntVar(fresh("__regexFind"))
  let (pre, rest) = splitAt(u, q, fresh, "__regexFind", defs)
  let marked = concat(pre, findMarker(), rest)
  defs.add ite(occurs,
    (q >= mkInt(0)) and (q <= len(u)) and
      variant(pl, st0, proc (v: int): Z3Bool = matches(marked, pl.first[v])),
    q == mkInt(0))
  (occurs, q, rest)

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
  ## Nothing is written on a miss or a bad offset. The match is PCRE's
  ## chosen one: at `start` (`match`, `matchLen`) or at the leftmost
  ## occurrence (`find`, `contains`, `findBounds`); its groups come from
  ## `pcre_select.captureLang`.
  let parts = sp.entry.split('|')
  let what = parts[1]
  let g = parseInt(parts[2])
  let search = what in ["find", "contains", "findBounds"]
  let pl = prioLangs(sp, pr, false, search)
  if not pl.ok: return unmodelled(sp.entry & ": " & pl.why)
  let n = buildNfa(pr)
  let key = sp.flag & ":" & sp.pattern
  var setRe, capRe: seq[array[2, Z3Regex[Z3String]]]
  for h in 1 .. pr.groups:
    var a, c: array[2, Z3Regex[Z3String]]
    for v in 0 .. 1:
      if v == 1 and not n.hasBol: break
      let ls = captureLang(n, key, h, v == 1, marked = false)
      if not ls.ok: return unmodelled(sp.entry & ": " & ls.why)
      a[v] = selToZ3(ls.re)
      if h == g:
        let lc = captureLang(n, key, h, v == 1, marked = true)
        if not lc.ok: return unmodelled(sp.entry & ": " & lc.why)
        c[v] = selToZ3(lc.re)
    setRe.add a
    capRe.add c
  let lenS = len(s)
  let bad = (start < mkInt(0)) or (start > lenS)
  let u = substr(s, start, lenS - start)
  let st0 = start == mkInt(0)
  var res = RxResult(outcome: roValue)
  var found: Z3Bool
  var p = start
  # The subject from the chosen match's start; `^` holds there iff it is
  # subject position 0.
  var w = u
  if search:
    let (occurs, q, rest) = prioLeftmost(pl, u, st0, fresh, res.defs)
    found = (not bad) and occurs
    p = start + q
    w = rest
  else:
    found = (not bad) and not variant(pl, st0, proc (v: int): Z3Bool =
      matches(u, pl.none[v]))
  let atP = p == mkInt(0)
  proc isSet(h: int): Z3Bool =
    variant(pl, atP, proc (v: int): Z3Bool = matches(w, setRe[h - 1][v]))
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
      variant(pl, atP, proc (v: int): Z3Bool = matches(marked, capRe[g - 1][v])),
    (a == mkInt(0)) and (b == mkInt(0)))
  case parts[0]
  of "captureFirst":
    res.i = ite(written, ite(on, p + a, mkInt(-1)), oldI)
  of "captureLast":
    res.i = ite(written, ite(on, p + b - mkInt(1), mkInt(0)), oldI)
  else:
    res.s = ite(written, ite(on, span, mkString("")), old)
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
  if not fine or pr.nl != nlLF:
    # RFC-0005 S8bb: an anchor away from a top-level edge, `(*ACCEPT)`, or
    # a newline convention other than LF (whose `$` and bumpalong the
    # edge-split reading does not know): every entry is the priority
    # automaton's.
    let search = sp.entry in ["contains", "find", "findBoundsFirst",
                              "findBoundsFirstCap",
                              "findBoundsLast"]
    let pl = prioLangs(sp, pr, sp.entry == "endsWith", search)
    if not pl.ok: return unmodelled(sp.entry & ": " & why & "; " & pl.why)
    var res = RxResult(outcome: roValue)
    if search:
      # The leftmost match from `start` (`prioLeftmost`).
      let (occurs, q, _) = prioLeftmost(pl, u, st0, fresh, res.defs)
      case sp.entry
      of "contains":
        res.b = (not bad) and occurs
      of "find", "findBoundsFirst":
        res.i = ite(bad, mkInt(-24), ite(occurs, start + q, mkInt(-1)))
      of "findBoundsFirstCap":
        res.i = ite((not bad) and occurs, start + q, mkInt(-1))
      else:
        let first = start + q
        let ml = prioChosenLen(s, first, pl, fresh, res.defs,
                               (not bad) and occurs)
        res.i = ite(bad or not occurs, mkInt(0), first + ml - mkInt(1))
      return res
    case sp.entry
    of "match":
      res.b = bad or not variant(pl, st0, proc (v: int): Z3Bool =
        matches(u, pl.none[v]))
    of "startsWith":
      res.b = not matches(s, pl.none[(if pl.hasBol: 1 else: 0)])
    of "matchLen":
      res.i = ite(bad, mkInt(-24),
                  prioChosenLen(s, start, pl, fresh, res.defs, not bad))
    else:
      res.b = prioEndsWith(s, pl)
    return res
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
      let pl = prioLangs(sp, pr, sp.entry == "endsWith")
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
  let run = defineRecFun[Z3String, Z3Int, Z3String](ctx, fresh("__regexRun"),
    proc (self: Z3FuncDecl[(Z3String, Z3Int), Z3String]; u: Z3String;
          st: Z3Int): Z3String =
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
        (if tgt < 0: mark else: self(tl, mkInt(int(tgt))))
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
        result = ite(st == mkInt(k), rk, result))
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
        ite(ne, run(u, mkInt(t.start[bol][1])),
            run(u, mkInt(t.start[bol][0])))
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
