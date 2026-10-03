## RFC-0005 S8bb, S8bj. PCRE's match SELECTION as finite automata.
##
## `matchLen`, `endsWith` and `findBounds`'s `last` (and `replace`) depend
## on WHICH match PCRE returns at a position, not only on whether one
## exists. PCRE backtracks: it returns the first match in its priority
## order (an alternation tries its alternatives left to right, a greedy
## quantifier tries one more iteration before stopping, a lazy one the
## reverse).
##
## ## The attempt (one call of pcre_exec.c's `match()` at a start)
##
## The pattern is a priority NFA (Thompson's construction with ordered
## epsilon splits) run as an ordered AGENDA: the backtracking order of the
## live alternatives. Its items, in priority order:
##   * threads: an NFA state waiting for the next byte;
##   * MATCH: a match recorded at a position (RFC-0005 S8bb: it cuts every
##     lower item);
##   * RFC-0005 S8bj, the backtracking verbs, each emitted AFTER the
##     continuation it guards (backtracking reaches the verb only once its
##     continuation has failed): `(*COMMIT)` (the search ends with no
##     match), `(*PRUNE)` and an uncaught `(*THEN)` (the attempt fails, the
##     search bumps along), `(*SKIP)` / a found `(*SKIP:NAME)` (the search
##     resumes where the verb, or the name's latest `(*MARK)`, was passed);
##   * RFC-0005 S8bj, `(*THEN)`'s jump: `THEN(m)` skips every lower item up
##     to the marker `m`, the end of the alternative that catches it. PCRE
##     catches a THEN in the innermost group frame with two or more
##     alternatives whose current branch ends after the THEN's code address
##     (pcre_exec.c, OP_BRA's MATCH_THEN test). Frames outlive their group
##     (the continuation runs inside them), so a frame left by an earlier
##     loop iteration can catch a later THEN; every thread carries, per
##     group instance, its latest frame (an older frame of the same group is
##     never the catcher), and code addresses mirror pcre_compile.c's layout
##     (a repeated group's copies, the last one looping), so that case is
##     modelled, not declined;
##   * markers: the ends of the alternatives a THEN can jump to.
## The agenda is normalized lazily: the front decides the attempt once it
## is a MATCH or a terminal verb; a front THEN jumps; an unconditional
## decided item kills the items after it up to the next marker (a THEN
## ahead of it can still jump past it to that marker, so nothing past a
## marker is cut). A thread is dropped when a higher-priority one is in the
## same NFA state with the same frames and marks (the same future).
##
## A `(*CRLF)` dot that reads a CR, and a `(?m)` `$` before a CR under
## `(*CRLF)`, leave CONDITIONAL items, settled by the next byte (an LF
## kills the first and is required by the second).
##
## ## The search (pcre_exec.c's bumpalong loop)
##
## RFC-0005 S8bj. Unanchored calls repeat the attempt: PCRE's start-of-match
## optimiser (the first character, the line-start flag, the start bits;
## `pcre_startopt.nim`) moves each start forward first; after a failed
## attempt the start moves one character, or to a `(*SKIP)` landing, or the
## search ends (`(*COMMIT)`); under a CRLF convention a CRLF's LF is never a
## start after a failed attempt at its CR. An attempt's start depends on the
## outcomes of the attempts before it, so the search languages guess each
## attempt's outcome (and a SKIP's landing) and verify it with that
## attempt's own automaton (`Verifier`), run in step.
##
## ## The languages
##
## The run is a deterministic automaton over the subject's bytes, so each
## value is a regular language of the subject, converted to a regex by state
## elimination:
##   * `lkMark`:  `u[0..k) # u[k..]` such that PCRE's match at the start of
##                `u` ends at `k` (`#` the marker byte of `regex_parser`);
##   * `lkNone`:  `u` with no match at its start;
##   * `lkEnds`:  `u` whose match at its start ends at its end;
##   * `skNoOcc`: `u` with no match found by the search;
##   * `skFirst`: `u[0..q) # u[q..]`: the search finds its match at `q`;
##   * the capture languages (`captureLang`).
## A final newline is its own input symbol so the automaton sees `$` / `\Z`
## (RFC-0005 S8bb, `nlStep`). RFC-0005 S8bj: the byte before the start
## (`PrevClass`) decides `^` / `\A` and `(?m)^`.
##
## Pure Nim (no Z3, no libpcre); `regex_parser.nim` turns the regexes into
## Z3's. Every language is pinned against the concrete `std/re` by the
## exhaustive differentials (`tests/tsymex_rfc0005_s8bb_*`,
## `tests/tsymex_rfc0005_s8bj_*`), together with the concrete reference runs
## `runAttempt` / `pcreExec`.

import std/[tables, hashes, sets, algorithm, sequtils]
import ./pcre_syntax
import ./pcre_startopt
import ./pcre_code
import ./pcre_jit
import ./pcre_engine
import ./pcre_possess

export pcre_startopt.StartOpt
export pcre_engine.PcreEngine

# ---- symbols ----------------------------------------------------------------

const
  maxNfaStates = 4000
  maxLoops = 63
  maxDfaStates* {.intdefine: "nelliMaxDfaStates".} = 4000
  maxRegexSize* {.intdefine: "nelliMaxRegexSize".} = 40000
  symFin = 256       ## 256 ..< 261: a final newline byte `finBytes[i]`
  symR2 = 261        ## RFC-0005 S8bb: the CR of a final CRLF
  # RFC-0005 S8bt: `(*ANY)` in UTF mode (`uAny`): the multi-byte newlines
  # U+0085 (C2 85), U+2028 and U+2029 (E2 80 A8 / A9). The lead byte of
  # one is always read as a symbol of its own, so the reading stays
  # unique: a final one (`symFC2`, `symFE2`, then `symF80`, and the final
  # byte as `symFin + 4` (0x85), `symFA8` or `symFA9`), or one with more
  # after it (`symNC2`, `symNE2`, its other bytes read plain).
  symFC2 = 262
  symFE2 = 263
  symF80 = 264
  symFA8 = 265
  symFA9 = 266
  symNC2 = 267
  symNE2 = 268
  symMark = 269      ## the marker `#` (a capture's start, RFC-0005 S8bb)
  symMark2 = 270     ## RFC-0005 S8bb: a capture's end marker
  symLand = 271      ## RFC-0005 S8bj: a `(*SKIP)` landing (verifiers only)
  nSyms = 272
  finBytes = ['\n', '\r', '\v', '\f', '\x85']
  nlMust = 1'i8      ## a newline byte read plain: another byte follows
  nlFinal = 2'i8     ## the final newline was read: only markers follow
  nlCRb = 4'i8       ## a CR read plain (CRLF a newline): no final LF next
  nlR2 = 8'i8        ## `symR2` read: the final LF is next
  # RFC-0005 S8bt (`uAny`): a multi-byte newline's progress, `16 * k`.
  # With `nlR2`, a final one: k = 1 after symFC2 (fin 0x85 next), 2 after
  # symFE2 (symF80 next), 3 after symF80 (symFA8 / symFA9 next). Without:
  # k = 1 after symNC2 (a plain 0x85 next), 2 after symNE2 (a plain 0x80
  # next), 3 after it (a plain A8 / A9 next); k = 4 after a plain C2 (no
  # 0x85 next), 5 after a plain E2, 6 after a plain E2 80 (no A8 / A9 next).
  nlU = 16'i8

proc symByte(s: int): char =
  if s < 256: char(s)
  elif s < symR2: finBytes[s - symFin]
  elif s == symR2: '\r'
  else:
    case s
    of symFC2, symNC2: '\xC2'
    of symFE2, symNE2: '\xE2'
    of symF80: '\x80'
    of symFA8: '\xA8'
    else: '\xA9'

proc nlStepU(st: int8; s: int): int8 =
  ## RFC-0005 S8bt. `nlStepFor` under `(*ANY)` in UTF mode: the single-byte
  ## newlines are LF, VT, FF and CR (and CRLF); 0x85 alone is no newline.
  let k = (st shr 4) and 7
  let base = st and 15
  let b = symByte(s)
  if (st and nlR2) != 0 and k > 0:
    # A final multi-byte newline: its next symbol.
    case k
    of 1: return (if s == symFin + 4: nlFinal else: -1'i8)
    of 2: return (if s == symF80: nlR2 or (3 * nlU) else: -1'i8)
    else: return (if s in [symFA8, symFA9]: nlFinal else: -1'i8)
  if k in 1 .. 3:
    # A multi-byte newline with more after it: its bytes, plain.
    case k
    of 1: return (if s == 0x85: nlMust else: -1'i8)
    of 2: return (if s == 0x80: 3 * nlU else: -1'i8)
    else: return (if s in [0xA8, 0xA9]: nlMust else: -1'i8)
  # After a plain lead: not the rest of a newline.
  if k == 4 and b == '\x85': return -1
  if k == 6 and b in {'\xA8', '\xA9'} and s < 256: return -1
  case s
  of symFC2, symFE2:
    if (base and nlR2) != 0: return -1
    return nlR2 or (if s == symFC2: nlU else: 2 * nlU)
  of symNC2: return nlU
  of symNE2: return 2 * nlU
  of symF80, symFA8, symFA9: return -1
  else: discard
  if s >= symFin and s < symR2:
    if b notin {'\n', '\r', '\v', '\f'}: return -1
    if (base and nlR2) != 0: return (if b == '\n': nlFinal else: -1'i8)
    if (base and nlCRb) != 0 and b == '\n': return -1
    return nlFinal
  if s == symR2:
    if (base and nlR2) != 0: return -1
    return nlR2
  if (base and nlR2) != 0: return -1
  result = 0
  if b in {'\n', '\r', '\v', '\f'}: result = result or nlMust
  if (base and nlCRb) != 0 and b == '\n': result = result or nlMust
  if b == '\r': result = result or nlCRb
  if b == '\xC2': result = result or (4 * nlU)
  if b == '\xE2': result = result or (5 * nlU)
  if k == 5 and b == '\x80': result = result or (6 * nlU)

proc nlStepFor(nl: NlConv; st: int8; s: int; u = false): int8 =
  ## RFC-0005 S8bb. The `nl` state after symbol `s` (not a marker), or -1
  ## when `s` cannot follow (the reading would not be unique). RFC-0005
  ## S8bt: `u`, `(*ANY)` in UTF mode (`nlStepU`).
  if (st and nlFinal) != 0: return -1
  if u: return nlStepU(st, s)
  if s > symR2: return -1
  let nl1 = nlBytes(nl)
  let b = symByte(s)
  if s >= symFin and s < symR2:
    if b notin nl1: return -1
    if (st and nlR2) != 0: return (if b == '\n': nlFinal else: -1'i8)
    if (st and nlCRb) != 0 and b == '\n': return -1
    return nlFinal
  if s == symR2:
    if not nlPair(nl) or (st and nlR2) != 0: return -1
    return nlR2
  if (st and nlR2) != 0:
    # `(*CRLF)`: the pair's LF is no newline on its own.
    return (if b == '\n' and '\n' notin nl1: nlFinal else: -1'i8)
  result = 0
  if b in nl1: result = result or nlMust
  if (st and nlCRb) != 0 and b == '\n': result = result or nlMust
  if nlPair(nl) and b == '\r': result = result or nlCRb

proc nlCanEnd(st: int8): bool =
  (st and (nlMust or nlR2)) == 0 and ((st shr 4) and 7) notin 1 .. 3

proc nlStates(u: bool): seq[int8] =
  ## RFC-0005 S8bt. The `nl` states the verifiers' fixpoint ranges over.
  if not u:
    for x in 0'i8 .. 15'i8: result.add x
  else:
    result = @[0'i8, nlMust, nlFinal, nlCRb, nlMust or nlCRb, nlR2]
    for k in 1'i8 .. 3'i8:
      result.add k * nlU
      result.add nlR2 or (k * nlU)
    for k in 4'i8 .. 6'i8: result.add k * nlU

proc nlSlot(st: int8): int =
  ## RFC-0005 S8bt. A state's index (0 .. 15) for `univIdx`: itself below
  ## 16; the multi-byte ones in the slots `nlStepFor` never reaches
  ## without `uAny`'s states (`nlStates(true)` holds no base state there).
  if st < 16: return int(st)
  const slots = [3, 6, 7, 9, 10, 11, 12, 13, 14]
  let k = int((st shr 4) and 7)
  if (st and nlR2) != 0: slots[k - 1]
  else: slots[k + 2]

type
  Ctx* = enum
    cxOther   ## the rest of the subject is not a newline (nor empty)
    cxNll     ## the rest of the subject is a newline
    cxEnd     ## the subject ends here

proc symCtx(s: int; u = false): Ctx =
  ## RFC-0005 S8bt: under `uAny`, a final multi-byte newline's lead starts
  ## it; its other bytes are inside a character.
  if s < symFin: cxOther
  elif u and s == symFin + 4: cxOther
  elif s <= symFE2: cxNll
  else: cxOther

# ---- the byte before a position -------------------------------------------------

type
  PrevClass* = enum
    ## RFC-0005 S8bj. What precedes a position: what `(?m)^`, the line-start
    ## filter and the CRLF skip read.
    pcStart   ## nothing: subject position 0
    pcOther   ## a byte that is no newline byte
    pcLF      ## an LF not after a CR
    pcCRLF    ## an LF after a CR
    pcCR      ## a CR
    pcNl      ## VT, FF or NEL (newlines under `(*ANY)` only); RFC-0005
              ## S8bt: under `(*ANY)` in UTF mode, VT, FF, U+0085, U+2028
              ## or U+2029
    pcU1      ## RFC-0005 S8bt (`uAny`): a C2 (a NEL's lead)
    pcU2      ## RFC-0005 S8bt (`uAny`): an E2
    pcU3      ## RFC-0005 S8bt (`uAny`): an E2 80

proc nextClass*(b: char; pc: PrevClass; u = false): PrevClass =
  ## RFC-0005 S8bt: `u`, `(*ANY)` in UTF mode: the multi-byte newlines
  ## (0x85 alone is no newline).
  if u:
    return (case b
            of '\n': (if pc == pcCR: pcCRLF else: pcLF)
            of '\r': pcCR
            of '\v', '\f': pcNl
            of '\xC2': pcU1
            of '\xE2': pcU2
            of '\x80': (if pc == pcU2: pcU3 else: pcOther)
            of '\x85': (if pc == pcU1: pcNl else: pcOther)
            of '\xA8', '\xA9': (if pc == pcU3: pcNl else: pcOther)
            else: pcOther)
  case b
  of '\n': (if pc == pcCR: pcCRLF else: pcLF)
  of '\r': pcCR
  of '\v', '\f', '\x85': pcNl
  else: pcOther

proc classAt*(s: string; x: int; u = false): PrevClass =
  ## The class of what precedes position `x` of `s`.
  if x <= 0: return pcStart
  if u:
    result = pcOther
    for j in max(0, x - 3) ..< x: result = nextClass(s[j], result, true)
    return
  nextClass(s[x - 1], (if x >= 2 and s[x - 2] == '\r': pcCR else: pcOther))

proc wasNl*(nl: NlConv; pc: PrevClass): bool =
  ## pcre_internal.h's WAS_NEWLINE: a newline ends just before.
  case nl
  of nlLF: pc in {pcLF, pcCRLF}
  of nlCR: pc == pcCR
  of nlCRLF: pc == pcCRLF
  of nlANYCRLF: pc in {pcLF, pcCRLF, pcCR}
  of nlANY: pc in {pcLF, pcCRLF, pcCR, pcNl}

# ---- the NFA ------------------------------------------------------------------

type
  NKind = enum
    nkByte    ## consume a byte of `bytes`, go to `out1`
    nkSplit   ## try `out1`, then `out2`
    nkBol     ## `^` / `\A`; `multi`: `(?m)^`
    nkEol     ## `$` / `\Z`; `multi`: `(?m)$`
    nkEolAbs  ## `\z`
    nkEnter   ## enter an iteration of loop `loop` (nullable body only)
    nkBack    ## end of an iteration: `out1` the loop head, `out2` the exit
    nkSave    ## capture slot `slot` (2*group or 2*group+1)
    nkMatch
    nkVerb    ## RFC-0005 S8bj: a backtracking verb or a mark
    nkAlt     ## RFC-0005 S8bj: entry to alternative `alt` of catcher `grp`
    nkCost    ## RFC-0005 S8bt: a `match()` call (`Nfa.costs`): `multi`
              ## one more frame deep (RMATCH), else the same frame
              ## (TAIL_RECURSE)
    nkPoss    ## RFC-0005 S8bt: a possessive repeat's exit: only where the
              ## next byte is not one of `bytes` (or at the end)

  NState = object
    kind: NKind
    bytes: set[char]
    crlfDot: bool   ## RFC-0005 S8bb: nkByte of a `(*CRLF)` dot
    multi: bool
    out1, out2: int
    loop: int
    slot: int
    verb: VerbKind
    name: int       ## nkVerb mark / SKIP:NAME: the name's index, -1 none
    address: int    ## nkVerb THEN: its code address
    grp, alt: int   ## nkAlt
    deep: bool      ## RFC-0005 S8bt: nkCost: RMATCH (one frame deeper)

  FilterKind* = enum
    ## RFC-0005 S8bj. The start-of-match optimisation of an unanchored call.
    fkNone, fkFirst, fkStartline, fkBits

  Nfa* = object
    states: seq[NState]
    start*: int
    loops: int
    groups*: int     ## capturing groups
    nl*: NlConv      ## RFC-0005 S8bb: the newline convention
    utf*: bool       ## RFC-0005 S8bj: UTF mode (whole characters)
    hasBol*: bool    ## a `^` / `\A`: subject position 0 matters
    hasBolMulti*: bool  ## RFC-0005 S8bj: a `(?m)^`
    hasEolMulti*: bool  ## RFC-0005 S8bj: a `(?m)$`
    hasCrLf*: bool   ## PCRE_HASCRORLF
    skipActive*: bool
      ## RFC-0005 S8bj: the bumpalong never starts at a CRLF's LF after a
      ## failed attempt (a CRLF-ish convention, no explicit CR or LF)
    nameIdx: Table[string, int]   ## SKIP:NAME names
    hasCommit*, hasSkip*, hasThen*, hasPrune*: bool
    hasNeverSkip*: bool
      ## a SKIP:NAME some path reaches without its MARK (RFC-0005 S8bt: on
      ## the interpreter; S8bj: no path passes it)
    reachArg: seq[bool]
      ## RFC-0005 S8bt: per state, a SKIP:NAME is reachable
    countArgs*: bool
      ## RFC-0005 S8bt: an attempt can end with `ignore_skip_arg` set for
      ## the next one, so the agenda counts SKIP:NAME runs in pcre_exec.c's
      ## order (`Item.ac`)
    altEnd: seq[seq[int]] ## per catcher group: each branch's end address
    filter*: FilterKind
    fc1, fc2: char
    bits: set[char]
    anchoredPat*: bool    ## pcre_compile.c's `is_anchored`
    noStartOpt*: bool
    so*: StartOpt
    limitMatch*, limitRecursion*: int64
    engine*: PcreEngine
      ## RFC-0005 S8bt: the engine of an unanchored call (`buildNfa`)
    jit*: JitScan
      ## RFC-0005 S8bt: peJit837's prefix scan, when it applies
    costs*: bool
      ## RFC-0005 S8bt: the automaton counts pcre_exec.c's `match()` calls
      ## (`nkCost`; `buildNfa`'s `limitRoom`), its threads are kept apart
    capRoom*: int
      ## RFC-0005 S8bt (`costs`): the groups the call's ovector has room
      ## for (a capturing bracket without room runs as a plain one)
    possess*: Possess
      ## RFC-0005 S8bt (`costs`): pcre_compile.c's auto-possessification
    ok*: bool
    why*: string

proc matchLimit*(n: Nfa): int =
  ## RFC-0005 S8bt. The `(*LIMIT_MATCH=)` pcre_exec.c applies (below its
  ## default), -1 none.
  if n.limitMatch >= 0 and n.limitMatch < pcreDefaultLimit: int(n.limitMatch)
  else: -1

proc recLimit(n: Nfa): int =
  ## RFC-0005 S8bt. The `(*LIMIT_RECURSION=)` pcre_exec.c applies.
  if n.limitRecursion >= 0 and n.limitRecursion < pcreDefaultLimit:
    int(n.limitRecursion)
  else: high(int)

proc countsLimits*(n: Nfa): bool =
  ## RFC-0005 S8bt. A limit between 0 and the default, read off the
  ## automaton's `match()` calls.
  n.costs and (n.matchLimit >= 0 or n.recLimit < high(int))

proc uAny*(n: Nfa): bool =
  ## RFC-0005 S8bt. `(*ANY)` in UTF mode: U+0085, U+2028 and U+2029 are
  ## multi-byte newlines (and a lone 0x85 byte is none).
  n.utf and n.nl == nlANY

proc nlBytesOf*(n: Nfa): set[char] =
  ## RFC-0005 S8bt. The bytes that are a newline on their own.
  if uAny(n): {'\n', '\v', '\f', '\r'} else: nlBytes(n.nl)

proc nlStartsAt*(n: Nfa; s: string; j: int): bool =
  ## RFC-0005 S8bt. A newline starts at `j` of `s` (`(?m)$`'s IS_NEWLINE;
  ## a CR under `(*CRLF)` aside).
  if j >= s.len: return false
  if s[j] in nlBytesOf(n): return true
  if not uAny(n): return false
  if s[j] == '\xC2': return j + 1 < s.len and s[j + 1] == '\x85'
  s[j] == '\xE2' and j + 2 < s.len and s[j + 1] == '\x80' and
    s[j + 2] in {'\xA8', '\xA9'}

proc symNls(n: Nfa; s: int): bool =
  ## RFC-0005 S8bt. A newline starts at symbol `s`.
  if s < 256: char(s) in nlBytesOf(n)
  elif s < symR2: not (uAny(n) and s == symFin + 4) and
                  symByte(s) in nlBytesOf(n)
  elif s == symR2: '\r' in nlBytesOf(n)
  else: s in [symFC2, symFE2, symNC2, symNE2]

proc needPc*(n: Nfa): bool =
  ## RFC-0005 S8bj. The automata track the byte before each position.
  n.hasBolMulti or n.filter == fkStartline or n.skipActive

type Build = object
  n: Nfa
  overflow: bool
  match: int
  catchers: bool   ## the pattern has a THEN: multi-alternative groups catch
  costWhy: string  ## RFC-0005 S8bt: why the call accounting is not modelled

proc cost(b: var Build; deep: bool; next: int): int

proc add(b: var Build; s: NState): int =
  if b.n.states.len >= maxNfaStates:
    b.overflow = true
    return 0
  b.n.states.add s
  b.n.states.high

proc utf8Seqs(lo, hi: int32; acc: var seq[seq[(char, char)]]) =
  ## RFC-0005 S8bj. The code points `lo .. hi` (surrogates left out: no
  ## valid subject holds one) as UTF-8 byte-range sequences.
  if lo > hi: return
  if lo <= 0xDFFF and hi >= 0xD800:
    utf8Seqs(lo, 0xD7FF, acc)
    utf8Seqs(0xE000, hi, acc)
    return
  for b in [0x7F'i32, 0x7FF, 0xFFFF]:
    if lo <= b and hi > b:
      utf8Seqs(lo, b, acc)
      utf8Seqs(b + 1, hi, acc)
      return
  if hi <= 0x7F:
    acc.add @[(char(lo), char(hi))]
    return
  for i in 1 .. 3:
    let m = (1'i32 shl (6 * i)) - 1
    if (lo and not m) != (hi and not m):
      if (lo and m) != 0:
        utf8Seqs(lo, lo or m, acc)
        utf8Seqs((lo or m) + 1, hi, acc)
        return
      if (hi and m) != m:
        utf8Seqs(lo, (hi and not m) - 1, acc)
        utf8Seqs(hi and not m, hi, acc)
        return
  let a = utf8Encode(lo)
  let z = utf8Encode(hi)
  var sq: seq[(char, char)]
  for k in 0 ..< a.len: sq.add (a[k], z[k])
  acc.add sq

proc compChars(b: var Build; x: Rx; next: int): int =
  ## RFC-0005 S8bj. One character of `x.cps` in UTF mode, as UTF-8 bytes.
  var single: set[char]
  var multi: seq[seq[(char, char)]]
  for (lo, hi) in x.cps:
    var acc: seq[seq[(char, char)]]
    utf8Seqs(lo, hi, acc)
    for sq in acc:
      if sq.len == 1:
        for c in sq[0][0] .. sq[0][1]: single.incl c
      else:
        multi.add sq
  var e = -1
  for sq in multi:
    var t = next
    for k in countdown(sq.high, 0):
      var bs: set[char]
      for c in sq[k][0] .. sq[k][1]: bs.incl c
      t = b.add NState(kind: nkByte, bytes: bs, out1: t)
    e = (if e < 0: t else: b.add NState(kind: nkSplit, out1: t, out2: e))
  if single.card > 0 or e < 0:
    let t = b.add NState(kind: nkByte, bytes: single, crlfDot: x.crlfDot,
                         out1: next)
    e = (if e < 0: t else: b.add NState(kind: nkSplit, out1: t, out2: e))
  e

proc compItem(b: var Build; x: Rx; next, base: int): int

proc compBranch(b: var Build; items: seq[Rx]; next, base: int): int =
  var bases = newSeq[int](items.len)
  var a = base
  for i, it in items:
    bases[i] = a
    a += codeSize(it)
  result = next
  for i in countdown(items.high, 0):
    result = b.compItem(items[i], result, bases[i])

proc compGroup(b: var Build; x: Rx; next, base: int; sGroup = false): int =
  ## A bracket: its alternatives in order. RFC-0005 S8bj: with a THEN in
  ## the pattern, each alternative of a multi-alternative group enters
  ## through `nkAlt` (a frame for THEN's catch test). RFC-0005 S8bt
  ## (`costs`): each alternative is a `match()` call, RMATCH but for the
  ## last one of a plain bracket (OP_BRA, or a capturing one without
  ## ovector room) in a pattern without THEN, which pcre_exec.c enters by
  ## TAIL_RECURSE; `sGroup`: an OP_SBRA / OP_SCBRA (a looping copy that
  ## can match the empty string).
  let alts = groupAlts(x)
  var inner = next
  if x.cap > 0:
    inner = b.add NState(kind: nkSave, slot: 2 * x.cap + 1, out1: next)
  var bases, ends: seq[int]
  var a = base + 1
  for br in alts:
    bases.add a
    a += branchSize(br)
    ends.add a
    a += 1
  let catcher = b.catchers and alts.len >= 2
  var gid = -1
  if catcher:
    gid = b.n.altEnd.len
    b.n.altEnd.add ends
  var e = -1
  let capturing = x.cap > 0 and x.cap <= b.n.capRoom
  for k in countdown(alts.high, 0):
    var entry = b.compBranch(branchItems(alts[k]), inner, bases[k])
    if b.n.costs:
      let tail = k == alts.high and not capturing and not sGroup and
                 not b.catchers
      entry = b.cost(not tail, entry)
    if catcher:
      entry = b.add NState(kind: nkAlt, grp: gid, alt: k, out1: entry)
    e = (if e < 0: entry else: b.add NState(kind: nkSplit, out1: entry, out2: e))
  if x.cap > 0:
    e = b.add NState(kind: nkSave, slot: 2 * x.cap, out1: e)
  e

proc compLoop(b: var Build; sub: Rx; lazy, once: bool; next, base: int): int =
  ## An unbounded loop of `sub` (`once`: at least one iteration, entered
  ## directly). A body that can match the empty string leaves the loop
  ## after an empty iteration (pcre_exec.c's OP_KETRMAX on an OP_SBRA),
  ## the first iteration included.
  let head = b.add NState(kind: nkSplit)
  var bodyIn: int
  if lenRange(sub)[0] == 0:
    if b.n.loops >= maxLoops:
      b.overflow = true
      return 0
    let id = b.n.loops
    inc b.n.loops
    let back = b.add NState(kind: nkBack, loop: id, out1: head, out2: next)
    bodyIn = b.add NState(kind: nkEnter, loop: id,
                          out1: b.compItem(sub, back, base))
  else:
    bodyIn = b.compItem(sub, head, base)
  if b.overflow: return 0
  if lazy:
    b.n.states[head].out1 = next
    b.n.states[head].out2 = bodyIn
  else:
    b.n.states[head].out1 = bodyIn
    b.n.states[head].out2 = next
  (if once: bodyIn else: head)

proc split(b: var Build; take, skip: int; lazy: bool): int =
  if lazy: b.add NState(kind: nkSplit, out1: skip, out2: take)
  else: b.add NState(kind: nkSplit, out1: take, out2: skip)

proc compRep(b: var Build; x: Rx; next, base: int): int =
  ## pcre_compile.c's repeat layout: `x{lo,hi}` is `lo` copies then
  ## `hi - lo` NESTED optional copies (skipping one skips the rest);
  ## `x{lo,}` is `lo` copies, the last one looping (one optional looping
  ## copy for `lo == 0`). RFC-0005 S8bj: each copy has its own code
  ## addresses (a group's copies are distinct catchers for THEN).
  let sub = x.sub
  if x.hi == 0: return next
  let sz = (if sub.isGroup: codeSize(sub) else: 0)
  let b0 = base + 1
  if x.hi < 0:
    let copies = max(x.lo, 1)
    result = b.compLoop(sub, x.lazy, x.lo >= 1, next, b0 + (copies - 1) * sz)
    for i in countdown(copies - 2, 0):
      result = b.compItem(sub, result, b0 + i * sz)
  else:
    var o = next
    for i in countdown(x.hi - 1, x.lo):
      o = b.split(b.compItem(sub, o, b0 + i * sz), next, x.lazy)
    result = o
    for i in countdown(x.lo - 1, 0):
      result = b.compItem(sub, result, b0 + i * sz)

proc compLoopCost(b: var Build; sub: Rx; lazy, once, sGrp: bool;
                  next, base: int): int =
  ## RFC-0005 S8bt. A group's looping copy with `match()`'s calls: entered
  ## by OP_BRAZERO (an RMATCH into the group, or none past it) /
  ## OP_BRAMINZERO (an RMATCH past it first, then the group in the same
  ## frame), or directly (`once`); after a non-empty iteration OP_KETRMAX
  ## re-enters the group by RMATCH, then goes on by TAIL_RECURSE; OP_KETRMIN
  ## goes on by RMATCH, then re-enters by RMATCH (`sGrp`, an OP_SBRA) or
  ## TAIL_RECURSE. An empty iteration of an OP_SBRA goes on in the same
  ## frame.
  let headK = b.add NState(kind: nkSplit)
  var bodyEnd = headK
  let nullable = lenRange(sub)[0] == 0
  var id = -1
  if nullable:
    if b.n.loops >= maxLoops:
      b.overflow = true
      return 0
    id = b.n.loops
    inc b.n.loops
    bodyEnd = b.add NState(kind: nkBack, loop: id, out1: headK, out2: next)
  var bodyIn = b.compGroup(sub, bodyEnd, base, sGrp)
  if b.overflow: return 0
  if nullable: bodyIn = b.add NState(kind: nkEnter, loop: id, out1: bodyIn)
  if lazy:
    let o1 = b.cost(true, next)
    let o2 = b.cost(sGrp, bodyIn)
    b.n.states[headK].out1 = o1
    b.n.states[headK].out2 = o2
  else:
    let o1 = b.cost(true, bodyIn)
    let o2 = b.cost(false, next)
    b.n.states[headK].out1 = o1
    b.n.states[headK].out2 = o2
  if once: return bodyIn
  if lazy: b.add NState(kind: nkSplit, out1: b.cost(true, next), out2: bodyIn)
  else: b.add NState(kind: nkSplit, out1: b.cost(true, bodyIn), out2: next)

proc compRepCost(b: var Build; x: Rx; next, base: int): int =
  ## RFC-0005 S8bt. A repeat with pcre_exec.c's `match()` calls (`costs`).
  ## A single-character repeat backs off one character at a time from its
  ## longest run, each try of the rest an RMATCH but the last (at the
  ## minimum: TAIL_RECURSE); a lazy one tries the rest by RMATCH before
  ## each further character; a possessive one (`Nfa.possess`) goes on only
  ## from its longest run, in the same frame. A group's copies follow
  ## pcre_compile.c's layout (`compLoopCost`; an optional copy behind
  ## OP_BRAZERO / OP_BRAMINZERO, nested ones inside a one-alternative
  ## OP_BRA).
  let sub = x.sub
  if x.hi == 0: return next
  if not sub.isGroup:
    let poss = base in b.n.possess.addrs
    let lazy = x.lazy and not poss
    var guard: set[char]
    if poss:
      if sub.crlfDot:
        b.costWhy = "a possessive (*CRLF) dot repeat"
      if sub.kind == rxChars:
        for (lo, hi) in sub.cps:
          if hi >= 128:
            b.costWhy = "a possessive repeat of a non-ASCII character class " &
                        "in UTF mode"
          for c in max(lo, 0) .. min(hi, 127): guard.incl char(c)
      else:
        guard = sub.bytes
    proc atomTo(b: var Build; t: int): int = b.compItem(sub, t, base + 1)
    proc exitAt(b: var Build; first: bool): int =
      if poss: b.add NState(kind: nkPoss, bytes: guard, out1: next)
      elif lazy: b.cost(true, next)
      else: b.cost(not first, next)
    if x.hi < 0:
      if lazy:
        let head = b.add NState(kind: nkSplit)
        let o1 = b.exitAt(false)
        let o2 = b.atomTo(head)
        b.n.states[head].out1 = o1
        b.n.states[head].out2 = o2
        result = head
      else:
        let headK = b.add NState(kind: nkSplit)
        let k1 = b.atomTo(headK)
        let k2 = b.exitAt(false)
        b.n.states[headK].out1 = k1
        b.n.states[headK].out2 = k2
        let f1 = b.atomTo(headK)
        let f2 = b.exitAt(true)
        result = b.add NState(kind: nkSplit, out1: f1, out2: f2)
    else:
      var o = next
      if x.hi > x.lo and not poss: o = b.cost(true, next)
      for i in countdown(x.hi - 1, x.lo):
        let skip = b.exitAt(i == x.lo)
        o = b.split(b.atomTo(o), skip, lazy)
      result = o
    for i in 0 ..< x.lo: result = b.atomTo(result)
    return
  let sz = codeSize(sub)
  let b0 = base + 1
  if x.hi < 0:
    let copies = max(x.lo, 1)
    result = b.compLoopCost(sub, x.lazy, x.lo >= 1, couldBeEmpty(sub), next,
                            b0 + (copies - 1) * sz)
    for i in countdown(copies - 2, 0):
      result = b.compGroup(sub, result, b0 + i * sz)
  else:
    var o = next
    for i in countdown(x.hi - 1, x.lo):
      var take = b.compGroup(sub, o, b0 + i * sz)
      if i != x.hi - 1: take = b.cost(b.catchers, take)   # the wrapper
      if x.lazy:
        o = b.add NState(kind: nkSplit, out1: b.cost(true, next), out2: take)
      else:
        o = b.add NState(kind: nkSplit, out1: b.cost(true, take), out2: next)
    result = o
    for i in countdown(x.lo - 1, 0):
      result = b.compGroup(sub, result, b0 + i * sz)

proc nameIndex(b: var Build; name: string): int =
  if name notin b.n.nameIdx:
    b.n.nameIdx[name] = b.n.nameIdx.len
  b.n.nameIdx[name]

proc cost(b: var Build; deep: bool; next: int): int =
  ## RFC-0005 S8bt. A `match()` call before `next`.
  b.add NState(kind: nkCost, deep: deep, out1: next)

proc compRepCost(b: var Build; x: Rx; next, base: int): int

proc compItem(b: var Build; x: Rx; next, base: int): int =
  if b.overflow: return 0
  case x.kind
  of rxSet:
    b.add NState(kind: nkByte, bytes: x.bytes, crlfDot: x.crlfDot, out1: next)
  of rxChars:
    b.compChars(x, next)
  of rxCat, rxAlt:
    b.compGroup(x, next, base)
  of rxRep:
    if b.n.costs: b.compRepCost(x, next, base)
    else: b.compRep(x, next, base)
  of rxBol:
    if x.multi: b.n.hasBolMulti = true
    else: b.n.hasBol = true
    b.add NState(kind: nkBol, multi: x.multi, out1: next)
  of rxEol:
    if x.multi: b.n.hasEolMulti = true
    b.add NState(kind: nkEol, multi: x.multi, out1: next)
  of rxEolAbs:
    b.add NState(kind: nkEolAbs, out1: next)
  of rxAccept:
    # RFC-0005 S8bb: close the groups it is in, then Match.
    var e = b.match
    for g in x.open:
      e = b.add NState(kind: nkSave, slot: 2 * g + 1, out1: e)
    e
  of rxVerb:
    var st = NState(kind: nkVerb, verb: x.verb, name: -1, address: base,
                    out1: next)
    case x.verb
    of vbCommit: b.n.hasCommit = true
    of vbPrune: b.n.hasPrune = true
    of vbSkip: b.n.hasSkip = true
    of vbThen: b.n.hasThen = true
    of vbSkipName: st.name = b.nameIndex(x.name)
    of vbMark: st.name = b.n.nameIdx.getOrDefault(x.name, -1)
    # RFC-0005 S8bt: every verb runs its continuation by RMATCH.
    if b.n.costs: st.out1 = b.cost(true, next)
    b.add st

proc hasThenVerb(x: Rx): bool =
  case x.kind
  of rxVerb: x.verb == vbThen
  of rxCat, rxAlt:
    for k in x.kids:
      if hasThenVerb(k): return true
    false
  of rxRep: hasThenVerb(x.sub)
  else: false

proc classifySkipNames(n: var Nfa) =
  ## RFC-0005 S8bj, S8bt. Whether a SKIP:NAME can be reached with and
  ## without a MARK of its name on the path: the interpreter reads the mark
  ## per path (`closure`), a SKIP:NAME without one re-running the attempt
  ## (pcre_exec.c's `ignore_skip_arg`).
  let k = n.nameIdx.len
  n.reachArg = newSeq[bool](n.states.len)
  if k == 0: return
  var seenMode = newSeq[set[bool]](k)   # passed a mark on the way: false/true
  for name in 0 ..< k:
    var seen = initHashSet[(int, bool)]()
    var work = @[(n.start, false)]
    while work.len > 0:
      let (s, passed) = work.pop()
      if (s, passed) in seen: continue
      seen.incl (s, passed)
      let st = n.states[s]
      var p2 = passed
      if st.kind == nkVerb:
        if st.verb == vbSkipName and st.name == name:
          seenMode[name].incl passed
        if st.verb == vbMark and st.name == name: p2 = true
      case st.kind
      of nkMatch: discard
      of nkSplit, nkBack:
        work.add (st.out1, p2)
        work.add (st.out2, p2)
      else:
        work.add (st.out1, p2)
  # The states a SKIP:NAME is reachable from (backwards).
  var preds = newSeq[seq[int]](n.states.len)
  for i, st in n.states:
    case st.kind
    of nkMatch: discard
    of nkSplit, nkBack:
      preds[st.out1].add i
      preds[st.out2].add i
    else: preds[st.out1].add i
  var work: seq[int]
  for i, st in n.states:
    if st.kind == nkVerb and st.verb == vbSkipName:
      n.reachArg[i] = true
      work.add i
  while work.len > 0:
    let i = work.pop()
    for p in preds[i]:
      if not n.reachArg[p]:
        n.reachArg[p] = true
        work.add p
  if n.engine == peJit837:
    # RFC-0005 S8bt: the JIT looks the name up on the current path
    # (`do_search_mark`) and ignores a SKIP:NAME it does not find there,
    # in place: no re-run.
    n.hasSkip = true
    return
  for name in 0 ..< k:
    if true in seenMode[name]: n.hasSkip = true
    if false in seenMode[name]: n.hasNeverSkip = true

proc firstBytes(n: Nfa): set[char] =
  ## RFC-0005 S8bt. The bytes an attempt can read first (zero-width items
  ## passed).
  var seen = initHashSet[int]()
  var work = @[n.start]
  while work.len > 0:
    let s = work.pop()
    if s in seen: continue
    seen.incl s
    let st = n.states[s]
    case st.kind
    of nkByte: result = result + st.bytes
    of nkMatch: discard
    of nkSplit, nkBack:
      work.add st.out1
      work.add st.out2
    else: work.add st.out1

proc buildNfa*(pr: PcreParse; engine = peInterp; limitRoom = -1): Nfa =
  ## RFC-0005 S8bb, S8bj. The priority NFA of a `psOk` reading, with PCRE's
  ## start-of-match data; `ok == false` past the size caps or for a
  ## declined construct (`why` says which). RFC-0005 S8bt: `engine` is the
  ## one an unanchored call runs on (anchored calls: always `peInterp`);
  ## `limitRoom` >= 0: the automaton counts `match()`'s calls (`costs`) for
  ## a call whose ovector has room for that many groups.
  var b = Build()
  b.n.engine = engine
  if limitRoom >= 0:
    b.n.costs = true
    b.n.capRoom = limitRoom
    b.n.possess = autoPossess(compileCode(pr), pr.utf)
  b.n.groups = pr.groups
  b.n.nl = pr.nl
  b.n.utf = pr.utf
  b.n.hasCrLf = pr.hasCrLf
  b.n.skipActive = nlPair(pr.nl) and not pr.hasCrLf
  b.n.noStartOpt = pr.noStartOpt
  b.n.limitMatch = pr.limitMatch
  b.n.limitRecursion = pr.limitRecursion
  b.catchers = hasThenVerb(pr.root)
  # SKIP:NAME names first, so a MARK knows whether it is tracked.
  proc collect(b: var Build; x: Rx) =
    case x.kind
    of rxVerb:
      if x.verb == vbSkipName: discard b.nameIndex(x.name)
    of rxCat, rxAlt:
      for k in x.kids: b.collect(k)
    of rxRep: b.collect(x.sub)
    else: discard
  b.collect(pr.root)
  let m = b.add NState(kind: nkMatch)
  b.match = m
  b.n.start = b.compGroup(pr.root, m, 0)
  # RFC-0005 S8bt: the attempt's own `match()` call.
  if b.n.costs: b.n.start = b.cost(false, b.n.start)
  result = b.n
  result.ok = not b.overflow
  if b.overflow:
    result.why = "the pattern's priority automaton is past its size cap (" &
                 $maxNfaStates & " states, " & $maxLoops & " nullable loops)"
    return
  if result.costs:
    # A SKIP:NAME without its MARK re-runs the attempt from a fresh count,
    # ignoring the SKIP:NAMEs it passed (no RMATCH for them).
    if result.possess.unknown:
      b.costWhy = "auto-possessification next to a character property or " &
                  "an extended class"
    if engine != peInterp:
      b.costWhy = "the JIT's match limit accounting"
    if b.costWhy.len > 0:
      result.ok = false
      result.why = "match()'s call accounting is not modelled for " &
                   b.costWhy
      return
  result.classifySkipNames()
  # RFC-0005 S8bt: an attempt can leave `ignore_skip_arg` set for the next
  # one when a SKIP:NAME without its MARK can re-run it and the attempt can
  # then end by a SKIP's jump or past a CRLF's LF.
  result.countArgs = engine == peInterp and result.hasNeverSkip and
                     (result.hasSkip or result.skipActive or result.costs)
  let so = startOpt(pr)
  result.so = so
  result.anchoredPat = so.anchored
  if pr.noStartOpt or so.anchored: result.filter = fkNone
  elif so.firstChar >= 0:
    result.filter = fkFirst
    result.fc1 = char(so.firstChar)
    result.fc2 = result.fc1
    if so.firstCaseless:
      result.fc2 = (if result.fc1 in {'a'..'z'}: char(ord(result.fc1) - 32)
                    else: char(ord(result.fc1) + 32))
  elif so.startline: result.filter = fkStartline
  elif so.hasBits:
    result.filter = fkBits
    result.bits = so.bits
  else: result.filter = fkNone
  if engine == peJit837 and not (pr.noStartOpt or so.anchored):
    # RFC-0005 S8bt: the JIT's own scan comes first.
    result.jit = jitScan(compileCode(pr), pr.utf)
    if pr.utf and result.jit.on and result.firstBytes().contains('\xC2'):
      # The scan steps a byte at a time and can stop inside a character,
      # where the JIT reads a continuation byte as the code point of its
      # value: modelled only where no first character is one of those.
      result.ok = false
      result.why = "UTF mode under the JIT's prefix scan, with a first " &
        "character in U+0080..U+00BF (the JIT can start an attempt inside " &
        "a character and read a continuation byte as that code point)"

proc filterBytes*(n: Nfa): set[char] =
  ## RFC-0005 S8bj. The bytes the start-of-match scan stops at (`fkFirst`,
  ## `fkBits`).
  case n.filter
  of fkFirst: {n.fc1, n.fc2}
  of fkBits: n.bits
  else: {}

proc buildNfa*(root: Rx; groups = 0; nl = nlLF; hasCrLf = false): Nfa =
  ## RFC-0005 S8bb. The priority NFA of a tree (non-UTF, no start options).
  buildNfa(PcreParse(status: psOk, root: root, groups: groups, nl: nl,
                     hasCrLf: hasCrLf, limitMatch: -1, limitRecursion: -1))

# ---- the agenda ------------------------------------------------------------------

type
  ItemKind = enum
    ikThread, ikMarker, ikThen, ikTerm, ikMatch
    ikCost   ## RFC-0005 S8bt: the calls of a path that failed here (`co`)
  TermKind = enum
    tmBump, tmCommit, tmSkip
    tmArgSkip   ## RFC-0005 S8bt: a SKIP:NAME with its MARK (id `marker`)
    tmBarrier   ## RFC-0005 S8bt: a SKIP:NAME without one (id `marker`)
    tmArgOff    ## RFC-0005 S8bt: a tmArgSkip a re-run ignores (a link)
    tmStale     ## RFC-0005 S8bt: a SKIP:NAME under a stale ignore count
  Cond = enum
    cdNone
    cdDieLF   ## a `(*CRLF)` dot read a CR: dies if the next byte is LF
    cdNeedLF  ## a `(?m)$` before a CR under `(*CRLF)`: needs an LF next
  Frame = tuple[grp, alt, marker: int32]

  Cost = object
    ## RFC-0005 S8bt (`Nfa.costs`). The `match()` calls pcre_exec.c makes
    ## on an item's path past where the item before it branched off (the
    ## shared part is the earlier item's: it is explored first).
    cc: int32    ## the calls
    dp: int16    ## a thread's frame depth (`rdepth`)
    md: int16    ## the deepest of those calls' depth, plus one (0: none)
    dv: int32    ## one plus the index among them of the first at or past
                 ## the recursion limit (0: none)
    pk: int32    ## the calls of an earlier run of the attempt (a SKIP:NAME
                 ## without its MARK re-runs it from a fresh count)

  Item[T] = object
    kind: ItemKind
    cond: Cond
    st: int32              ## ikThread: the NFA state
    frames: seq[Frame]     ## ikThread: per catcher group, its latest frame
    marks: seq[int32]      ## ikThread: per name, its latest MARK's tag
    marker: int32          ## ikMarker: its id; ikThen: the target;
                           ## a SKIP:NAME's terminal: its id
    term: TermKind         ## ikTerm
    tag: int32             ## ikTerm tmSkip / ikMatch: where
    anc: int32
      ## RFC-0005 S8bt: the latest SKIP:NAME terminal on the path whose
      ## continuation this is (-1 none): a thread's, a SKIP:NAME terminal's
      ## parent
    ac: int8
      ## RFC-0005 S8bt (`countArgs`): a thread's count of the SKIP:NAMEs
      ## pcre_exec.c runs before its next one; a SKIP:NAME terminal's run
      ## number (`skip_arg_count`), up to `argCap` (`argCap + 1`: more)
    stl: int8
      ## RFC-0005 S8bt: the attempt's `ignore_skip_arg`: the count it
      ## started with, then the run number of the last SKIP:NAME without
      ## its MARK that re-ran it
    soft: bool
      ## RFC-0005 S8bt: a tmArgSkip a re-run may still ignore (it decides
      ## only at the front)
    rerun: bool
      ## RFC-0005 S8bt: a tmBarrier whose re-run takes the CRLF start skip;
      ## a tmBump that is that re-run (`ignore_skip_arg` stays set)
    co: Cost
      ## RFC-0005 S8bt: the item's `match()` calls (`Nfa.costs`)
    cap: T

  StepCtx = object
    ctx: Ctx          ## the rest of the subject
    nb: int           ## the byte here, -1 at the end
    nls: bool         ## RFC-0005 S8bt: a newline starts here (`(?m)$`;
                      ## `nlStartsAt`)
    finCRLF: bool     ## the bytes here are a final CRLF (symR2)
    pc: PrevClass     ## what precedes this position
    pos0: bool        ## subject position 0
    atStart: bool     ## the attempt's start
    noEmpty: bool     ## NOTEMPTY_ATSTART holds here
    crlfElig: bool    ## the start is a CRLF's LF past the start offset
    anchored: bool    ## the call is anchored (a SKIP:NAME without mark
                      ## then fails the attempt)
    eligAll: bool     ## RFC-0005 S8bt: the attempt starts at a CRLF's LF
                      ## past the start offset (a re-run moves past it)
    tagNow: int32     ## the tag of an item created here
    capStart, capEnd: bool   ## capture events here (`captureLang`)

  OutcomeKind* = enum
    okUndecided, okNoMatch, okMatch, okBump, okCommit, okSkip
    okStale   ## RFC-0005 S8bt: a stale `ignore_skip_arg` read: not modelled
    okLimitM  ## RFC-0005 S8bt: PCRE_ERROR_MATCHLIMIT
    okLimitR  ## RFC-0005 S8bt: PCRE_ERROR_RECURSIONLIMIT

const argCap* = 7
  ## RFC-0005 S8bt: the SKIP:NAME run count the agenda keeps exactly

const costStaleWhy* = "match()'s call accounting where pcre_exec.c's " &
  "ignore_skip_arg outlives an attempt (a SKIP:NAME's provisional run " &
  "number decides whether it calls match()), or past " & $argCap &
  " SKIP:NAME runs"

const staleWhy* = "pcre_exec.c's ignore_skip_arg count past " & $argCap &
  " SKIP:NAME runs (an attempt re-run by a (*SKIP:NAME) without its " &
  "(*MARK:NAME) that ends by a SKIP's jump or past a CRLF's LF keeps it " &
  "for the next one)"

proc decided[T](it: Item[T]): bool =
  ## Decides when it reaches the front, so nothing after it matters.
  it.kind == ikMatch and it.cond == cdNone or
    it.kind == ikTerm and it.cond == cdNone and
      (it.term in {tmBump, tmCommit, tmSkip, tmStale} or
       it.term == tmArgSkip and not it.soft)

proc decidesAtFront[T](it: Item[T]): bool =
  decided(it) or
    it.kind == ikTerm and it.cond == cdNone and it.term == tmArgSkip

proc sat(x: int): int8 = int8(min(x, argCap + 1))

proc then(a, b: Cost): Cost =
  ## RFC-0005 S8bt. The calls of `a`, then those of `b`.
  Cost(cc: a.cc + b.cc, dp: b.dp, md: max(a.md, b.md),
       dv: (if a.dv > 0: a.dv elif b.dv > 0: a.cc + b.dv else: 0),
       pk: max(a.pk, b.pk))

proc spent(c: Cost): bool = c.cc > 0

proc ckey[T](it: Item[T]): (int32, seq[Frame], seq[int32], Cond, int32,
                            int8) =
  (it.st, it.frames, it.marks, it.cond, it.anc, it.ac)

proc exempt(n: Nfa; st: int32; ac: int8): bool =
  ## RFC-0005 S8bt. A thread kept beside an identical one: pcre_exec.c runs
  ## both, and the SKIP:NAMEs the second runs count (`countArgs`).
  n.countArgs and n.reachArg[st] and ac <= argCap

proc withFrame(fs: seq[Frame]; f: Frame): seq[Frame] =
  for x in fs:
    if x.grp != f.grp: result.add x
  result.add f

proc closure[T](n: Nfa; items: seq[Item[T]]; sc: StepCtx;
                markerCtr: var int32;
                save: proc (t: T; slot: int; sc: StepCtx): T): seq[Item[T]] =
  ## The epsilon closure of the agenda at one position (see the module
  ## doc): threads become consumers (byte states) in priority order, with
  ## the matches, verb items and markers their paths reach.
  type Entry = object
    kind: int8        ## 0 visit, 1 emit a marker, 2 emit `item`
    st: int32
    ent: uint64
    frames: seq[Frame]
    marks: seq[int32]
    cond: Cond
    anc: int32
    ac: int8
    stl: int8
    co: Cost
    cap: T
    item: Item[T]
  var visited = initHashSet[(int32, uint64, seq[Frame], seq[int32], Cond,
                             int32, int8)]()
  var seenC = initHashSet[(int32, seq[Frame], seq[int32], Cond, int32,
                           int8)]()
  var cutting = false
  var work = items
  var stack: seq[Entry]
  proc isArg(x: Item[T]): bool =
    x.kind == ikTerm and x.term in {tmArgSkip, tmBarrier, tmArgOff}
  proc countRun(anc: int32; from0: int) =
    ## RFC-0005 S8bt: a SKIP:NAME runs: pcre_exec.c runs it before every
    ## path after this one, so their counts move on -- the threads after
    ## it, and the SKIP:NAME terminals after it but those on its own path
    ## (`anc`'s chain, which ran before it).
    var chain = initHashSet[int32]()
    var a = anc
    while a >= 0:
      chain.incl a
      var nx = -1'i32
      for x in stack:
        if x.kind == 2 and isArg(x.item) and x.item.marker == a:
          nx = x.item.anc
      for k in from0 ..< work.len:
        if isArg(work[k]) and work[k].marker == a: nx = work[k].anc
      a = nx
    for x in stack.mitems:
      if x.kind == 0: x.ac = sat(int(x.ac) + 1)
    for k in from0 ..< work.len:
      if work[k].kind == ikThread or
         isArg(work[k]) and work[k].marker notin chain:
        work[k].ac = sat(int(work[k].ac) + 1)
  for idx in 0 ..< work.len:
    let it = work[idx]
    if it.kind != ikThread:
      if it.kind == ikMarker:
        cutting = false
        result.add it
      elif not cutting:
        result.add it
        if decided(it): cutting = true
      continue
    if cutting: continue
    stack = @[Entry(kind: 0, st: it.st, frames: it.frames, marks: it.marks,
                    cond: it.cond, anc: it.anc, ac: it.ac, stl: it.stl,
                    co: it.co, cap: it.cap)]
    while stack.len > 0:
      let e = stack.pop()
      case e.kind
      of 1:
        result.add Item[T](kind: ikMarker, marker: e.st)
        cutting = false
        continue
      of 2:
        if not cutting:
          result.add e.item
          if decided(e.item): cutting = true
        continue
      else: discard
      if cutting: continue
      # RFC-0005 S8bt: pcre_exec.c explores every path, the same ones
      # again too (`costs`: their calls count).
      if not n.costs:
        let vk = (e.st, e.ent, e.frames, e.marks, e.cond, e.anc, e.ac)
        if not exempt(n, e.st, e.ac):
          if vk in visited: continue
          visited.incl vk
      let s = n.states[e.st]
      template dead() =
        # RFC-0005 S8bt: the path fails here; its calls stay counted.
        if n.costs and spent(e.co):
          result.add Item[T](kind: ikCost, co: e.co)
      var coNext = e.co
      template goWith(target: int; fs: seq[Frame]; mk: seq[int32]; c: Cond;
                      a: int32; cnt: int8; cp: T; en: uint64) =
        stack.add Entry(kind: 0, st: int32(target), ent: en, frames: fs,
                        marks: mk, cond: c, anc: a, ac: cnt, stl: e.stl,
                        co: coNext, cap: cp)
      template go(target: int; c: Cond = e.cond) =
        goWith(target, e.frames, e.marks, c, e.anc, e.ac, e.cap, e.ent)
      template emitAfter(itm: Item[T]) =
        # The item comes after everything the continuation reaches.
        var x = itm
        x.stl = e.stl
        stack.add Entry(kind: 2, item: x)
      case s.kind
      of nkByte:
        let k = (e.st, e.frames, e.marks, e.cond, e.anc, e.ac)
        if n.costs or exempt(n, e.st, e.ac) or k notin seenC:
          seenC.incl k
          result.add Item[T](kind: ikThread, st: e.st, frames: e.frames,
                             marks: e.marks, cond: e.cond, anc: e.anc,
                             ac: e.ac, stl: e.stl, co: e.co, cap: e.cap)
      of nkSplit:
        # RFC-0005 S8bt: the first branch keeps the calls so far.
        coNext = Cost(dp: e.co.dp)
        go(s.out2)
        coNext = e.co
        go(s.out1)
      of nkCost:
        # RFC-0005 S8bt: a `match()` call: pcre_exec.c checks the call
        # count, then the frame depth against the limits.
        let d = e.co.dp + (if s.deep: 1'i16 else: 0'i16)
        coNext.dp = d
        coNext.md = max(e.co.md, d + 1)
        if coNext.dv == 0 and int(d) >= n.recLimit():
          coNext.dv = e.co.cc + 1
        coNext.cc = e.co.cc + 1
        go(s.out1)
      of nkPoss:
        if sc.nb < 0 or char(sc.nb) notin s.bytes: go(s.out1)
        else: dead()
      of nkBol:
        if not s.multi:
          if sc.pos0: go(s.out1)
          else: dead()
        elif sc.pos0 or (sc.ctx != cxEnd and wasNl(n.nl, sc.pc)):
          # OP_CIRCM: at the subject start, or after a newline that does
          # not end the subject.
          go(s.out1)
        else: dead()
      of nkEol:
        if not s.multi:
          if sc.ctx in {cxNll, cxEnd}: go(s.out1)
          else: dead()
        elif sc.ctx == cxEnd or sc.nls:
          go(s.out1)
        elif n.nl == nlCRLF and sc.nb == ord('\r'):
          # OP_DOLLM's IS_NEWLINE: a CR is one only with an LF after it.
          if sc.finCRLF: go(s.out1)
          elif e.cond != cdDieLF: go(s.out1, cdNeedLF)
          else: dead()
        else: dead()
      of nkEolAbs:
        if sc.ctx == cxEnd: go(s.out1)
        else: dead()
      of nkEnter:
        goWith(s.out1, e.frames, e.marks, e.cond, e.anc, e.ac, e.cap,
               e.ent or (1'u64 shl s.loop))
      of nkBack:
        if (e.ent and (1'u64 shl s.loop)) != 0:
          go(s.out2)    # an empty iteration: leave the loop
        else:
          go(s.out1)
      of nkSave:
        goWith(s.out1, e.frames, e.marks, e.cond, e.anc, e.ac,
               save(e.cap, s.slot, sc), e.ent)
      of nkMatch:
        if not sc.noEmpty:
          let m = Item[T](kind: ikMatch, cond: e.cond, tag: sc.tagNow,
                          stl: e.stl, co: e.co, cap: e.cap)
          result.add m
          if decided(m): cutting = true
        else: dead()
      of nkAlt:
        let id = markerCtr
        inc markerCtr
        stack.add Entry(kind: 1, st: id)
        goWith(s.out1, withFrame(e.frames, (int32(s.grp), int32(s.alt), id)),
               e.marks, e.cond, e.anc, e.ac, e.cap, e.ent)
      of nkVerb:
        case s.verb
        of vbMark:
          var mk = e.marks
          if s.name >= 0 and s.name < mk.len: mk[s.name] = sc.tagNow
          goWith(s.out1, e.frames, mk, e.cond, e.anc, e.ac, e.cap, e.ent)
        of vbCommit:
          emitAfter(Item[T](kind: ikTerm, term: tmCommit, cond: e.cond))
          go(s.out1)
        of vbPrune:
          emitAfter(Item[T](kind: ikTerm, term: tmBump, cond: e.cond))
          go(s.out1)
        of vbSkip:
          emitAfter(Item[T](kind: ikTerm, term: tmSkip, tag: sc.tagNow,
                            cond: e.cond))
          go(s.out1)
        of vbSkipName:
          if n.engine == peJit837:
            # RFC-0005 S8bt: the latest MARK of the name on this path, or
            # no effect.
            if e.marks[s.name] >= 0:
              emitAfter(Item[T](kind: ikTerm, term: tmSkip,
                                tag: e.marks[s.name], cond: e.cond))
            go(s.out1)
          elif e.marks[s.name] < 0 and sc.anchored:
            # No mark: an anchored call fails.
            emitAfter(Item[T](kind: ikTerm, term: tmBump, cond: e.cond))
            go(s.out1)
          else:
            # RFC-0005 S8bt: pcre_exec.c's OP_SKIP_ARG. Its terminal comes
            # after its continuation, linked to the SKIP:NAME terminal
            # before it on the path (`anc`), with its run number (`ac`;
            # whether `ignore_skip_arg` covers it is read at the front): a
            # SKIP:NAME without its MARK (a barrier) re-runs the attempt
            # ignoring every SKIP:NAME run so far -- itself and the ones
            # whose continuation holds it.
            let id = markerCtr
            inc markerCtr
            var run = 0'i8     # not counted (`countArgs` off): live
            if n.countArgs:
              run = sat(int(e.ac) + 1)
              countRun(e.anc, idx + 1)
            if e.marks[s.name] >= 0:
              emitAfter(Item[T](kind: ikTerm, term: tmArgSkip,
                                tag: e.marks[s.name], marker: id,
                                anc: e.anc, ac: run, soft: n.hasNeverSkip,
                                cond: e.cond))
            else:
              emitAfter(Item[T](kind: ikTerm, term: tmBarrier, marker: id,
                                anc: e.anc, ac: run, rerun: sc.eligAll,
                                cond: e.cond))
            goWith(s.out1, e.frames, e.marks, e.cond, id,
                   (if n.countArgs: run else: e.ac), e.cap, e.ent)
        of vbThen:
          var target = -1'i32
          for k in countdown(e.frames.high, 0):
            let f = e.frames[k]
            if s.address < n.altEnd[f.grp][f.alt]:
              target = f.marker
              break
          if target >= 0:
            emitAfter(Item[T](kind: ikThen, marker: target, cond: e.cond))
          else:
            emitAfter(Item[T](kind: ikTerm, term: tmBump, cond: e.cond))
          go(s.out1)

proc advance[T](n: Nfa; items: seq[Item[T]]; c: char): seq[Item[T]] =
  ## The agenda after the byte `c`: each consumer that reads it moves on.
  var seen = initHashSet[(int32, seq[Frame], seq[int32], Cond, int32, int8)]()
  for it in items:
    if it.kind != ikThread:
      result.add it
      continue
    let s = n.states[it.st]
    # RFC-0005 S8bt: a path that fails leaves its calls (`costs`).
    if c notin s.bytes or (c == '\r' and s.crlfDot and it.cond == cdNeedLF):
      if spent(it.co): result.add Item[T](kind: ikCost, co: it.co)
      continue
    var t = it
    t.st = int32(s.out1)
    if c == '\r' and s.crlfDot:
      t.cond = cdDieLF
    let k = ckey(t)
    if not n.costs:
      if k in seen and not exempt(n, t.st, t.ac): continue
      seen.incl k
    result.add t

proc resolve[T](items: seq[Item[T]]; nextLF: bool): seq[Item[T]] =
  ## The conditional items once the next byte is known (`nextLF`: an LF).
  ## RFC-0005 S8bt: one that dies leaves its calls.
  for it in items:
    case it.cond
    of cdNone: result.add it
    of cdDieLF:
      if not nextLF:
        var t = it
        t.cond = cdNone
        result.add t
      elif spent(it.co): result.add Item[T](kind: ikCost, co: it.co)
    of cdNeedLF:
      if nextLF:
        var t = it
        t.cond = cdNone
        result.add t
      elif spent(it.co): result.add Item[T](kind: ikCost, co: it.co)

proc dropThreads[T](items: seq[Item[T]]): seq[Item[T]] =
  ## The agenda at the end: no thread reads on (RFC-0005 S8bt: each leaves
  ## its calls).
  for it in items:
    if it.kind != ikThread: result.add it
    elif spent(it.co): result.add Item[T](kind: ikCost, co: it.co)

proc rerunCosts[T](cur: var seq[Item[T]]; f: Item[T]; recLimit: int): bool =
  ## RFC-0005 S8bt (`costs`). The re-run of a SKIP:NAME without its MARK
  ## (`f`, at the front): pcre_exec.c calls match() afresh, so the run so
  ## far is one of the call's runs (`pk`); the re-run takes the same paths
  ## up to here with one call fewer per SKIP:NAME it now ignores (those
  ## run since the last re-run: `f.ac - f.stl`), and every item after the
  ## front runs one frame higher per such SKIP:NAME whose continuation
  ## holds it (the chain's terminals after it). False when a depth past
  ## the recursion limit can no longer be placed.
  let c = f.co
  var chain = initHashSet[int]()
  var a = f.anc
  for k in 0 ..< cur.len:
    if a < 0: break
    let x = cur[k]
    if x.kind == ikTerm and x.term in {tmArgSkip, tmBarrier, tmArgOff} and
       x.marker == a:
      if x.ac > f.stl: chain.incl k
      a = x.anc
  var r = 0'i16
  for k in countdown(cur.high, 0):
    if r > 0:
      var co = cur[k].co
      co.dp -= r
      if co.md > 0:
        co.md = max(co.md - r, 1'i16)
        if co.dv > 0:
          if int(co.md) - 1 >= recLimit: return false
          co.dv = 0
      cur[k].co = co
    if k in chain: inc r
  let pre = Cost(cc: c.cc - int32(f.ac - f.stl), dp: c.dp, md: c.md,
                 pk: max(c.pk, c.cc))
  if cur.len > 0: cur[0].co = pre.then(cur[0].co)
  else: cur = @[Item[T](kind: ikCost, co: pre)]
  true

proc resolveBarrier[T](cur: var seq[Item[T]]; costs = false;
                       recLimit = high(int)): bool =
  ## RFC-0005 S8bt. A SKIP:NAME at the front: every path before it failed,
  ## so its run number is final. One `ignore_skip_arg` covers (`ac <= stl`)
  ## is a no-op (left as a link). Otherwise one without its MARK re-runs
  ## the attempt with `ignore_skip_arg` set to its number: the re-run takes
  ## the same paths up to here with it and the ones whose continuation
  ## holds it (its `anc` chain) ignored -- a SKIP:NAME with its MARK there
  ## no longer decides (tmArgOff) -- and the rest carries on with the count
  ## set (`stl`). If the attempt starts at a CRLF's LF past the start
  ## offset, the re-run's start moves past the LF instead: the attempt ends
  ## as a bump that keeps the count. A SKIP:NAME with its MARK decides
  ## (`decidesAtFront`). Past `argCap` the comparison is not modelled
  ## (tmStale). True when the agenda changed.
  if cur.len == 0 or cur[0].kind != ikTerm or cur[0].cond != cdNone:
    return false
  let f = cur[0]
  case f.term
  of tmArgOff:
    cur = cur[1 .. ^1]
    return true
  of tmArgSkip, tmBarrier:
    let counted = f.ac > 0     # 0: not counted, never ignored
    if counted and f.ac > argCap and f.stl > argCap or
       costs and f.ac > argCap:
      cur = @[Item[T](kind: ikTerm, term: tmStale)]
      return true
    if counted and f.ac <= f.stl:
      cur[0].term = tmArgOff
      return true
    if f.term == tmArgSkip: return false
    if f.rerun:
      cur = @[Item[T](kind: ikTerm, term: tmBump, rerun: true, stl: f.ac,
                      co: f.co)]
      return true
    var a = f.anc
    cur = cur[1 .. ^1]
    if costs and not rerunCosts(cur, f, recLimit):
      cur = @[Item[T](kind: ikTerm, term: tmStale)]
      return true
    for k in 0 ..< cur.len:
      if a < 0: break
      let x = cur[k]
      if x.kind == ikTerm and x.term in {tmArgSkip, tmBarrier, tmArgOff} and
         x.marker == a:
        if x.term == tmArgSkip: cur[k].term = tmArgOff
        a = x.anc
    if counted:
      for x in cur.mitems: x.stl = f.ac
    return true
  else:
    return false

proc normalize[T](items: seq[Item[T]]; costs = false;
                  recLimit = high(int)): seq[Item[T]] =
  ## See the module doc: the front decides or jumps, an unconditional
  ## decided item kills what follows it up to the next marker, and a marker
  ## nothing refers to goes. RFC-0005 S8bt: a SKIP:NAME at the front
  ## re-runs the attempt (`resolveBarrier`).
  var cur = items
  while true:
    var changed = false
    var i = 0
    # RFC-0005 S8bt: what the front passes over was explored (its calls
    # go to the new front); what a THEN jumps over was not.
    var carry: Cost
    while i < cur.len:
      let it = cur[i]
      if it.kind == ikMarker or it.kind == ikCost:
        carry = carry.then(it.co)
        inc i
      elif it.kind == ikThen and it.cond == cdNone:
        carry = carry.then(it.co)
        var j = i + 1
        while j < cur.len and
              not (cur[j].kind == ikMarker and cur[j].marker == it.marker):
          inc j
        if j < cur.len: carry = carry.then(cur[j].co)
        i = j + 1
      else:
        break
    if i > 0:
      if i >= cur.len:
        # Nothing left: no match, after these calls.
        if spent(carry): return @[Item[T](kind: ikCost, co: carry)]
        return @[]
      cur = cur[i .. ^1]
      if spent(carry): cur[0].co = carry.then(cur[0].co)
      changed = true
    if resolveBarrier(cur, costs, recLimit): continue
    if cur.len > 0 and decidesAtFront(cur[0]):
      return @[cur[0]]
    var nx: seq[Item[T]]
    var cutting = false
    for it in cur:
      if it.kind == ikMarker:
        cutting = false
        nx.add it
      elif cutting:
        changed = true
      else:
        nx.add it
        if decided(it): cutting = true
    # An unconditional THEN jumps over everything up to its marker: those
    # items never reach the front. A THEN right before its marker is a
    # no-op.
    block thens:
      var i = 0
      var pruned: seq[Item[T]]
      while i < nx.len:
        let it = nx[i]
        if it.kind == ikThen and it.cond == cdNone:
          var j = i + 1
          while j < nx.len and
                not (nx[j].kind == ikMarker and nx[j].marker == it.marker):
            inc j
          if j < nx.len:
            # Markers in between stay (a thread above may still refer to
            # one; an unreferenced one goes below).
            var kept: seq[Item[T]]
            for x in nx[i + 1 ..< j]:
              if x.kind == ikMarker: kept.add x
            if kept.len < j - i - 1: changed = true
            if kept.len == 0:
              changed = true      # THEN right before its marker: a no-op
            else:
              pruned.add it
              pruned.add kept
            i = j
            continue
        pruned.add it
        inc i
      nx = pruned
    var refs = initHashSet[int32]()
    for it in nx:
      if it.kind == ikThread:
        for f in it.frames: refs.incl f.marker
      elif it.kind == ikThen:
        refs.incl it.marker
    # RFC-0005 S8bt: an ignored SKIP:NAME's link no thread or SKIP:NAME
    # terminal reaches goes too.
    var links = initHashSet[int32]()
    for it in nx:
      if it.kind == ikThread or
         it.kind == ikTerm and it.term in {tmArgSkip, tmBarrier, tmArgOff}:
        if it.anc >= 0: links.incl it.anc
    cur = @[]
    for it in nx:
      if it.kind == ikMarker and it.marker notin refs:
        # RFC-0005 S8bt: its calls go to what follows it.
        if spent(it.co): cur.add Item[T](kind: ikCost, co: it.co)
        changed = true
      elif it.kind == ikTerm and it.term == tmArgOff and
           it.marker notin links:
        changed = true
      elif it.kind == ikCost and cur.len > 0 and cur[^1].kind == ikCost:
        cur[^1].co = cur[^1].co.then(it.co)
        changed = true
      else:
        cur.add it
    if not changed: return cur

proc outcome[T](items: seq[Item[T]]): OutcomeKind =
  ## A normalized agenda's outcome, if decided.
  if items.len == 0 or items[0].kind == ikCost: return okNoMatch
  let f = items[0]
  if f.cond != cdNone: return okUndecided
  case f.kind
  of ikMatch: okMatch
  of ikTerm:
    case f.term
    of tmBump: okBump
    of tmCommit: okCommit
    of tmSkip, tmArgSkip: okSkip
    of tmStale: okStale
    of tmBarrier, tmArgOff: okUndecided
  else: okUndecided

# ---- the concrete runs -----------------------------------------------------------

proc ctxAt(n: Nfa; u: string; j: int): Ctx =
  if j >= u.len: cxEnd
  elif j == u.len - 1 and u[j] in nlBytesOf(n): cxNll
  elif nlPair(n.nl) and j == u.len - 2 and u[j] == '\r' and
       u[j + 1] == '\n': cxNll
  elif uAny(n) and u[j] in {'\xC2', '\xE2'} and nlStartsAt(n, u, j) and
       j + (if u[j] == '\xC2': 2 else: 3) == u.len:
    # RFC-0005 S8bt: a final multi-byte newline.
    cxNll
  else: cxOther

proc initMarks(n: Nfa): seq[int32] =
  result = newSeq[int32](n.nameIdx.len)
  for x in result.mitems: x = -1

type AttemptResult*[T] = object
  kind*: OutcomeKind
  pos*: int        ## okMatch: the match's end; okSkip: the landing
  ign*: int8
    ## RFC-0005 S8bt: `ignore_skip_arg` after the attempt (`nextIgn`)
  calls*: int      ## RFC-0005 S8bt (`costs`): its `match()` calls
  depth*: int      ## RFC-0005 S8bt (`costs`): its deepest call's frame
                   ## depth, plus one
  cap*: T

proc limitHit[T](n: Nfa; items: seq[Item[T]]): OutcomeKind =
  ## RFC-0005 S8bt. Whether the calls before and on the front item pass a
  ## limit (`costs`): the error of the first call that does (pcre_exec.c
  ## checks the count before the depth), else okUndecided.
  if not n.costs or items.len == 0: return okUndecided
  let co = items[0].co
  let l = n.matchLimit
  let countHit = l >= 0 and co.cc > l
  let depthHit = co.dv > 0
  if countHit and depthHit:
    return (if l + 1 <= co.dv: okLimitM else: okLimitR)
  if countHit: return okLimitM
  if depthHit: return okLimitR
  okUndecided

proc nextIgn[T](oc: OutcomeKind; it: Item[T]; landed: bool): int8 =
  ## RFC-0005 S8bt. pcre_exec.c's `ignore_skip_arg` for the next attempt:
  ## kept by a SKIP's jump past the start and by a re-run past a CRLF's
  ## LF, reset by every other way on.
  if oc == okSkip and landed or oc == okBump and it.rerun: it.stl
  else: 0

proc runAttemptT[T](n: Nfa; s: string; x, s0: int; anchored, ne: bool;
                    cap0: T;
                    save: proc (t: T; slot: int; sc: StepCtx): T;
                    ign0 = 0'i8): AttemptResult[T] =
  ## RFC-0005 S8bj. The concrete attempt at `x` of `s` (the search's start
  ## offset `s0`): its outcome, with positions as tags.
  if n.costs and ign0 > 0:
    # RFC-0005 S8bt: not modelled (`costStaleWhy`).
    result.kind = okStale
    return
  var items = @[Item[T](kind: ikThread, st: int32(n.start),
                        marks: initMarks(n), anc: -1, stl: ign0, cap: cap0)]
  var ctr = 0'i32
  var pc = classAt(s, x, uAny(n))
  let elig = (not anchored) and x > s0 and x < s.len and s[x - 1] == '\r' and
             s[x] == '\n' and n.skipActive
  for j in x .. s.len:
    let atEnd = j >= s.len
    let nextLF = (not atEnd) and s[j] == '\n'
    items = resolve(items, nextLF)
    let sc = StepCtx(ctx: ctxAt(n, s, j), nb: (if atEnd: -1 else: ord(s[j])),
                     nls: nlStartsAt(n, s, j),
                     finCRLF: n.nl == nlCRLF and j == s.len - 2 and
                              s[j] == '\r' and s[j + 1] == '\n',
                     pc: pc, pos0: j == 0, atStart: j == x,
                     noEmpty: ne and j == x, crlfElig: j == x and elig,
                     eligAll: elig,
                     anchored: anchored, tagNow: int32(j))
    items = closure(n, items, sc, ctr, save)
    if atEnd: items = dropThreads(items)
    else: items = advance(n, items, s[j])
    items = normalize(items, n.costs, n.recLimit)
    var oc = outcome(items)
    let lim = limitHit(n, items)
    if lim != okUndecided: oc = lim
    if oc != okUndecided or atEnd:
      result.kind = oc
      if items.len > 0:
        result.calls = int(max(items[0].co.cc, items[0].co.pk))
        result.depth = int(items[0].co.md)
      if oc in {okMatch, okSkip}:
        result.pos = int(items[0].tag)
        result.cap = items[0].cap
      if items.len > 0:
        result.ign = nextIgn(oc, items[0], oc == okSkip and result.pos > x)
      return
    pc = nextClass(s[j], pc, uAny(n))

proc noSave(t: int8; slot: int; sc: StepCtx): int8 = t

proc runAttempt*(n: Nfa; s: string; x: int; s0 = -1; anchored = true;
                 ne = false; ign0 = 0'i8): (OutcomeKind, int, int8) =
  ## RFC-0005 S8bj. The concrete attempt at `x` of `s`: its outcome and
  ## (a match's end / a SKIP's landing) position. `s0`: the call's start
  ## offset (default `x`). RFC-0005 S8bt: `ign0` its `ignore_skip_arg`, and
  ## the next attempt's.
  let r = runAttemptT[int8](n, s, x, (if s0 < 0: x else: s0), anchored, ne,
                            0'i8, noSave, ign0)
  (r.kind, r.pos, r.ign)

proc chosenEnd*(n: Nfa; u: string; atStart: bool; noEmpty = false): int =
  ## RFC-0005 S8bb. The end offset in `u` of PCRE's (anchored) match at the
  ## start of `u`, or -1. `atStart`: `u` starts at subject position 0 (else
  ## an ordinary byte precedes it).
  let s = (if atStart: u else: "\x00" & u)
  let x = (if atStart: 0 else: 1)
  let r = runAttemptT[int8](n, s, x, x, true, noEmpty, 0'i8, noSave)
  if r.kind == okMatch: r.pos - x else: -1

proc created*(n: Nfa; s: string; x, s0: int): bool =
  ## RFC-0005 S8bj. Whether an unanchored search scanning forward stops at
  ## `x` (pcre_exec.c's start-of-match optimisation; the end always).
  if x >= s.len: return true
  case n.filter
  of fkNone: true
  of fkFirst: s[x] == n.fc1 or s[x] == n.fc2
  of fkBits: s[x] in n.bits
  of fkStartline:
    if x == s0: true
    else:
      let pc = classAt(s, x, uAny(n))
      wasNl(n.nl, pc) and
        not (pc == pcCR and s[x] == '\n' and n.nl in {nlANY, nlANYCRLF})

proc nextChar(n: Nfa; s: string; x: int; jit = false): int =
  result = x + 1
  if n.utf:
    if jit:
      # RFC-0005 S8bt: the JIT's bumpalong adds the lead byte's extra
      # length (pcre_jit_compile.c's `utf8_table4`); one byte from a
      # continuation byte, where its prefix scan can stop.
      if x >= s.len: return
      let c = ord(s[x])
      if c >= 0xF0: result += 3
      elif c >= 0xE0: result += 2
      elif c >= 0xC0: result += 1
      return min(result, s.len)
    while result < s.len and (ord(s[result]) and 0xC0) == 0x80: inc result

proc capSave(t: seq[int32]; slot: int; sc: StepCtx): seq[int32] =
  result = t
  result[slot] = sc.tagNow

proc chosenCapsAt*(n: Nfa; s: string; x: int; s0 = -1;
                   anchored = true; ign0 = 0'i8): (int, seq[(int, int)]) =
  ## RFC-0005 S8bj. The concrete attempt at `x` with captures: the match's
  ## end (-1: none) and each group's `(start, end)` in `s` (`(-1, -1)`:
  ## unset). RFC-0005 S8bt: `ign0` the attempt's `ignore_skip_arg`
  ## (`pcreExecIgn`'s for the found one).
  var cap0 = newSeq[int32](2 * n.groups + 2)
  for k in 0 ..< cap0.len: cap0[k] = -1
  let r = runAttemptT[seq[int32]](n, s, x, (if s0 < 0: x else: s0), anchored,
                                  false, cap0, capSave, ign0)
  if r.kind != okMatch: return (-1, @[])
  var caps: seq[(int, int)]
  for g in 1 .. n.groups:
    caps.add(if r.cap[2 * g + 1] < 0: (-1, -1)
             else: (int(r.cap[2 * g]), int(r.cap[2 * g + 1])))
  (r.pos, caps)

proc chosenCaps*(n: Nfa; u: string; atStart: bool): (int, seq[(int, int)]) =
  ## RFC-0005 S8bb. `chosenCapsAt` at the start of `u`, offsets in `u`.
  let s = (if atStart: u else: "\x00" & u)
  let x = (if atStart: 0 else: 1)
  let (e, caps) = chosenCapsAt(n, s, x)
  if e < 0: return (-1, @[])
  var cs: seq[(int, int)]
  for (a, b) in caps:
    cs.add(if a < 0: (-1, -1) else: (a - x, b - x))
  (e - x, cs)

# ---- deterministic automata ---------------------------------------------------

type Dfa = object
  trans: seq[array[nSyms, int32]]   ## -1: dead
  accept: seq[bool]
  sink: seq[bool]    ## an outcome decided and accepted: every well-formed
                     ## continuation is accepted
  ok: bool
  why: string        ## RFC-0005 S8bt: why not `ok` ("": the size cap)
  igns: set[int8]
    ## RFC-0005 S8bt: the `ignore_skip_arg` values the decided outcomes
    ## reached leave for the next attempt (`nextIgn`)

proc hash(f: Frame): Hash = !$(hash(f.grp) !& hash(f.alt) !& hash(f.marker))

proc hash[T](it: Item[T]): Hash =
  var h: Hash = 0
  h = h !& hash(ord(it.kind)) !& hash(ord(it.cond)) !& hash(it.st) !&
      hash(it.marker) !& hash(ord(it.term)) !& hash(it.tag) !&
      hash(it.anc) !& hash(it.ac) !& hash(it.stl) !& hash(it.soft) !&
      hash(it.rerun) !&
      hash(it.cap)
  for f in it.frames: h = h !& hash(f)
  for m in it.marks: h = h !& hash(m)
  !$h

proc capCosts[T](n: Nfa; items: seq[Item[T]]): seq[Item[T]] =
  ## RFC-0005 S8bt. The calls as far as the limits tell them apart (the
  ## automata's agendas are finitely many): counts past the match limit,
  ## depths past the recursion limit are one. Without THEN nothing jumps
  ## over an item, so what follows one whose calls already pass a limit is
  ## never reached (it decides once at the front).
  if not n.costs: return items
  let l = n.matchLimit
  let r = n.recLimit
  var pre = 0
  # RFC-0005 S8bt: depths keep `argCap + 2` above the limit, so a re-run's
  # lift (`rerunCosts`, at most one frame per counted SKIP:NAME) still
  # tells them apart.
  let top = int16(min(r, 30000) + argCap + 2)
  for it in items:
    var x = it
    x.co.pk = 0
    x.co.cc = (if l >= 0: min(x.co.cc, int32(l + 1)) else: 0'i32)
    x.co.dp = (if r < high(int): min(x.co.dp, top) else: 0'i16)
    x.co.md = (if r < high(int): min(x.co.md, top) else: 0'i16)
    if x.co.dv > 0:
      x.co.dv = (if l >= 0: min(x.co.dv, int32(l + 2)) else: 1'i32)
    result.add x
    pre += int(x.co.cc)
    if not n.hasThen and ((l >= 0 and pre > l) or x.co.dv > 0): break

proc canon[T](items: seq[Item[T]]): seq[Item[T]] =
  ## Marker ids renumbered by first appearance.
  var ren = initTable[int32, int32]()
  proc idOf(m: int32): int32 =
    if m notin ren: ren[m] = int32(ren.len)
    ren[m]
  result = items
  for it in result.mitems:
    case it.kind
    of ikThread:
      for f in it.frames.mitems: f.marker = idOf(f.marker)
      if it.anc >= 0: it.anc = idOf(it.anc)
    of ikMarker, ikThen:
      it.marker = idOf(it.marker)
    of ikTerm:
      # RFC-0005 S8bt: SKIP:NAME terminals' ids and links.
      if it.term in {tmArgSkip, tmBarrier, tmArgOff}:
        it.marker = idOf(it.marker)
        if it.anc >= 0: it.anc = idOf(it.anc)
    else: discard

type
  AcceptKind = enum
    acMarkT    ## a match tagged at the `#` event
    acNone     ## no match
    acEndsT    ## a match ending at the end
    acBump     ## unanchored: the attempt fails, the start moves one char
    acSkipT    ## unanchored: a SKIP landing at the LAND event
    acCommit   ## unanchored: the search ends
    acMatch    ## search: a match
    acMatchT   ## search: a match ending at the LAND event
    acCapSet   ## a match setting group `g`
    acCapMark  ## a match whose group `g` spans `#` .. `%`
    acErrM     ## RFC-0005 S8bt: PCRE_ERROR_MATCHLIMIT
    acErrR     ## RFC-0005 S8bt: PCRE_ERROR_RECURSIONLIMIT

  AttemptSpec = object
    acc: AcceptKind
    anchored: bool
    noEmpty: bool
    nonEmpty: bool     ## the empty word is not in the language
    pc0: PrevClass
    crlfElig: bool
    group: int
    ign0: int8         ## RFC-0005 S8bt: the attempt's `ignore_skip_arg`
    ign1: int8         ## RFC-0005 S8bt: acBump / acSkipT: the next one's
    tracksIgn: bool
      ## RFC-0005 S8bt: the consumer follows `ignore_skip_arg` across
      ## attempts (`ign0` / `ign1`); otherwise an outcome that leaves it set
      ## declines (`staleWhy`)

  AKey = object
    items: seq[Item[int8]]
    pc: PrevClass
    nl: int8
    ev: int8          ## events read: 1 `#`, 2 `%`, 4 LAND
    just: int8        ## events read at this position
    atStart: bool
    sink: int8        ## 1: accepted outcome (items then empty)

proc hash(k: AKey): Hash =
  var h: Hash = 0
  for it in k.items: h = h !& hash(it)
  h = h !& hash(ord(k.pc)) !& hash(k.nl) !& hash(k.ev) !& hash(k.just) !&
      hash(k.atStart) !& hash(k.sink)
  !$h

proc `==`(a, b: AKey): bool =
  a.items == b.items and a.pc == b.pc and a.nl == b.nl and a.ev == b.ev and
    a.just == b.just and a.atStart == b.atStart and a.sink == b.sink

proc requiredEvents(acc: AcceptKind): int8 =
  case acc
  of acMarkT: 1
  of acSkipT, acMatchT: 4
  of acCapMark: 3
  else: 0

proc capSaveDfa(g: int): proc (t: int8; slot: int; sc: StepCtx): int8 =
  ## RFC-0005 S8bb. Group `g`'s capture tag `3*s + e` (s / e: 0 unset, 1 at
  ## the marker, 2 elsewhere).
  result = proc (t: int8; slot: int; sc: StepCtx): int8 =
    if slot == 2 * g: int8(3 * (if sc.capStart: 1 else: 2) + int(t) mod 3)
    elif slot == 2 * g + 1: int8(3 * (int(t) div 3) + (if sc.capEnd: 1 else: 2))
    else: t

proc accepts(spec: AttemptSpec; oc: OutcomeKind; it: Item[int8];
             ev: int8; atStart: bool): bool =
  if (ev and requiredEvents(spec.acc)) != requiredEvents(spec.acc):
    return false
  case spec.acc
  of acMarkT: oc == okMatch and it.tag == 1
  of acNone: oc != okMatch
  of acEndsT: oc == okMatch and it.tag == 1 and not (spec.nonEmpty and atStart)
  of acBump:
    (oc in {okNoMatch, okBump} or (oc == okSkip and it.tag == 0)) and
      nextIgn(oc, it, false) == spec.ign1
  of acSkipT: oc == okSkip and it.tag == 1 and it.stl == spec.ign1
  of acCommit: oc == okCommit
  of acMatch: oc == okMatch
  of acMatchT: oc == okMatch and it.tag == 1
  of acCapSet: oc == okMatch and int(it.cap) mod 3 != 0
  of acCapMark: oc == okMatch and it.cap == 3 * 1 + 1
  of acErrM: oc == okLimitM
  of acErrR: oc == okLimitR

proc staleOutcome(n: Nfa; spec: AttemptSpec; oc: OutcomeKind;
                  it: Item[int8]): bool =
  ## RFC-0005 S8bt. An unanchored attempt's outcome that leaves
  ## `ignore_skip_arg` set for the next one where the consumer does not
  ## follow it (or the calls count, `costStaleWhy`), or past `argCap`
  ## (`staleWhy`).
  if spec.anchored: return oc == okStale
  let ig = nextIgn(oc, it, oc == okSkip and it.tag != 0)
  oc == okStale or ig > argCap or
    (ig != 0 and (not spec.tracksIgn or n.costs))

proc staleWhyOf(n: Nfa): string =
  (if n.costs: costStaleWhy else: staleWhy)

proc buildAttempt(n: Nfa; spec: AttemptSpec): Dfa =
  ## RFC-0005 S8bj. The deterministic attempt (the agenda machine) as a
  ## DFA accepting the words whose outcome `spec` asks for.
  var ids = initTable[AKey, int]()
  var keys: seq[AKey]
  proc intern(k: AKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  var save: proc (t: int8; slot: int; sc: StepCtx): int8 = noSave
  if spec.group > 0: save = capSaveDfa(spec.group)
  let pc0 = (if n.needPc or spec.pc0 == pcStart: spec.pc0 else: pcOther)
  discard intern(AKey(items: @[Item[int8](kind: ikThread, st: int32(n.start),
                                          marks: initMarks(n), anc: -1,
                                          stl: spec.ign0)],
                      pc: pc0, atStart: true))
  let evSyms = [(symMark, 1'i8), (symMark2, 2'i8), (symLand, 4'i8)]
  let need = requiredEvents(spec.acc)
  result.ok = true
  var i = 0
  while i < keys.len:
    if keys.len > maxDfaStates:
      result.ok = false
      return
    let k = keys[i]
    var row: array[nSyms, int32]
    for s in 0 ..< nSyms: row[s] = -1
    var acc = false
    var isSink = false
    if k.sink == 1:
      acc = nlCanEnd(k.nl)
      isSink = true
      for s in 0 ..< symMark:
        let nls = nlStepFor(n.nl, k.nl, s, uAny(n))
        if nls < 0: continue
        var k2 = k
        k2.nl = nls
        row[s] = int32 intern(k2)
    else:
      let tagNow = (proc (just: int8): int32 =
        if (just and (1 or 4)) != 0: 1'i32
        elif k.atStart: 0'i32
        else: 2'i32)
      proc mkCtx(ctx: Ctx; nb: int; finCRLF: bool; endEv: bool;
                 nls = false): StepCtx =
        var just = k.just
        if endEv: just = just or 1
        StepCtx(ctx: ctx, nb: nb, nls: nls, finCRLF: finCRLF, pc: k.pc,
                pos0: k.atStart and pc0 == pcStart, atStart: k.atStart,
                noEmpty: k.atStart and spec.noEmpty,
                crlfElig: k.atStart and spec.crlfElig,
                eligAll: spec.crlfElig,
                anchored: spec.anchored, tagNow: tagNow(just),
                capStart: (k.just and 1) != 0, capEnd: (k.just and 2) != 0)
      # The end of the subject.
      if nlCanEnd(k.nl):
        var ctr = 1_000_000'i32
        var items = resolve(k.items, false)
        items = closure(n, items, mkCtx(cxEnd, -1, false,
                                        spec.acc == acEndsT), ctr, save)
        items = normalize(dropThreads(items), n.costs, n.recLimit)
        var oc = outcome(items)
        let lim = limitHit(n, items)
        if lim != okUndecided: oc = lim
        let it = (if items.len > 0: items[0] else: Item[int8]())
        if staleOutcome(n, spec, oc, it):
          return Dfa(ok: false, why: staleWhyOf(n))
        result.igns.incl nextIgn(oc, it, oc == okSkip and it.tag != 0)
        acc = accepts(spec, oc, it, k.ev, k.atStart)
      # The events.
      for (sym, bit) in evSyms:
        if (need and bit) == 0 or (k.ev and bit) != 0: continue
        # `%` only after `#`.
        if bit == 2 and (k.ev and 1) == 0: continue
        var k2 = k
        k2.ev = k.ev or bit
        k2.just = k.just or bit
        row[sym] = int32 intern(k2)
      # A byte, or a final newline's.
      if (k.nl and nlFinal) == 0:
        var cache = initTable[(Ctx, int, bool, bool), seq[Item[int8]]]()
        for s in 0 ..< symMark:
          let nls = nlStepFor(n.nl, k.nl, s, uAny(n))
          if nls < 0: continue
          let c = symByte(s)
          let ctx = symCtx(s, uAny(n))
          let fin = s == symR2
          let here = symNls(n, s)
          # The closure depends on the byte only through these (RFC-0005
          # S8bt: and through a possessive exit's test, `costs`).
          let nbKey = (if n.costs or c in nlBytes(n.nl): ord(c)
                       elif c == '\r': ord(c)
                       else: -2)
          let ck = (ctx, nbKey * 2 + (if c == '\n': 1 else: 0), fin, here)
          var cl: seq[Item[int8]]
          if ck in cache:
            cl = cache[ck]
          else:
            var ctr = 1_000_000'i32
            cl = closure(n, resolve(k.items, c == '\n'),
                         mkCtx(ctx, ord(c), fin, false, here), ctr, save)
            cache[ck] = cl
          var items = capCosts(n, normalize(advance(n, cl, c), n.costs,
                                            n.recLimit))
          var oc = outcome(items)
          let lim = limitHit(n, items)
          if lim != okUndecided: oc = lim
          var k2 = AKey(nl: nls, ev: k.ev, just: 0, atStart: false)
          if oc != okUndecided:
            let it = (if items.len > 0: items[0] else: Item[int8]())
            if staleOutcome(n, spec, oc, it):
              return Dfa(ok: false, why: staleWhyOf(n))
            result.igns.incl nextIgn(oc, it, oc == okSkip and it.tag != 0)
            # Decided: accepted for good once the required events are read.
            if (k.ev and need) == need and
               accepts(spec, oc, it, k.ev, false):
              k2.sink = 1
            else:
              continue
          else:
            k2.items = canon(items)
            k2.pc = (if n.needPc: nextClass(c, k.pc, uAny(n)) else: pcOther)
          row[s] = int32 intern(k2)
    result.trans.add row
    result.accept.add acc
    result.sink.add isSink
    inc i

proc minimizeMap(d: Dfa): (seq[array[nSyms, int32]], seq[bool], seq[int]) =
  ## Moore's partition refinement, dead states (no path to acceptance)
  ## removed: transitions into them become -1. Also returns each state's
  ## class (-1: dead).
  let n = d.trans.len
  var rev = newSeq[seq[int]](n)
  for s in 0 ..< n:
    for t in d.trans[s]:
      if t >= 0: rev[t].add s
  var live = newSeq[bool](n)
  var work: seq[int]
  for s in 0 ..< n:
    if d.accept[s]:
      live[s] = true
      work.add s
  while work.len > 0:
    let t = work.pop()
    for s in rev[t]:
      if not live[s]:
        live[s] = true
        work.add s
  var cls = newSeq[int](n)
  for s in 0 ..< n:
    cls[s] = (if not live[s]: -1 elif d.accept[s]: 1 else: 0)
  var nCls = 0
  while true:
    var sigIds = initTable[seq[int], int]()
    var next = newSeq[int](n)
    for s in 0 ..< n:
      if cls[s] < 0:
        next[s] = -1
        continue
      var sig = @[cls[s]]
      for t in d.trans[s]:
        sig.add(if t < 0: -1 else: cls[t])
      if sig notin sigIds: sigIds[sig] = sigIds.len
      next[s] = sigIds[sig]
    let changed = sigIds.len != nCls
    nCls = sigIds.len
    cls = next
    if not changed: break
  var order = initTable[int, int]()
  var mapped = newSeq[int](n)
  proc idOf(c: int): int =
    if c < 0: return -1
    if c notin order: order[c] = order.len
    order[c]
  for s in 0 ..< n: mapped[s] = idOf(cls[s])
  var trans = newSeq[array[nSyms, int32]](order.len)
  var acc = newSeq[bool](order.len)
  for s in 0 ..< n:
    let m = mapped[s]
    if m < 0: continue
    acc[m] = d.accept[s]
    for sym in 0 ..< nSyms:
      let t = d.trans[s][sym]
      trans[m][sym] = (if t < 0: -1'i32 else: int32 mapped[t])
  (trans, acc, mapped)

proc minimize(d: Dfa): (seq[array[nSyms, int32]], seq[bool]) =
  let (t, a, _) = minimizeMap(d)
  (t, a)

# ---- regexes ------------------------------------------------------------------

type
  RKind* = enum rkEmpty, rkEps, rkSet, rkMark, rkMark2, rkCat, rkAlt, rkStar
  RNode* = ref object
    kind*: RKind
    bytes*: set[char]     ## rkSet
    kids*: seq[RNode]     ## rkCat, rkAlt, rkStar (one kid)
    size*: int
    id: int               ## hash-consed: equal regexes, equal ids

var rnIds {.threadvar.}: Table[string, int]
  ## A regex's structure (its kind and its children's ids) to its id, per
  ## thread (every language is built and cached per thread, `selCache`).
  ## 0 and 1 are the empty language and the empty word on every thread.

proc mk(kind: RKind; kids: seq[RNode] = @[]; bytes: set[char] = {}): RNode =
  result = RNode(kind: kind, kids: kids, bytes: bytes, size: 1)
  for k in kids: result.size += k.size
  var key: string
  case kind
  of rkEmpty:
    result.id = 0
    return
  of rkEps:
    result.id = 1
    return
  of rkMark: key = "#"
  of rkMark2: key = "%"
  of rkSet:
    key = "["
    for c in bytes: key.add $ord(c) & ","
  of rkStar, rkCat, rkAlt:
    key = $ord(kind) & ":"
    for k in kids: key.add $k.id & ","
  result.id = rnIds.getOrDefault(key, -1)
  if result.id < 0:
    result.id = rnIds.len + 2
    rnIds[key] = result.id

let rEmpty = mk(rkEmpty)
let rEps = mk(rkEps)

proc rCat(a, b: RNode): RNode =
  if a.kind == rkEmpty or b.kind == rkEmpty: return rEmpty
  if a.kind == rkEps: return b
  if b.kind == rkEps: return a
  var kids: seq[RNode]
  for x in [a, b]:
    if x.kind == rkCat: kids.add x.kids else: kids.add x
  mk(rkCat, kids)

proc rAlt(a, b: RNode): RNode =
  if a.kind == rkEmpty: return b
  if b.kind == rkEmpty: return a
  var kids: seq[RNode]
  var bytes: set[char]
  var hasSet = false
  var seen = initHashSet[int]()
  for x in [a, b]:
    for y in (if x.kind == rkAlt: x.kids else: @[x]):
      if y.kind == rkSet:
        bytes = bytes + y.bytes
        hasSet = true
      elif y.id notin seen:
        seen.incl y.id
        kids.add y
  if hasSet: kids.insert(mk(rkSet, bytes = bytes), 0)
  if kids.len == 1: kids[0] else: mk(rkAlt, kids)

proc rStar(a: RNode): RNode =
  if a.kind in {rkEmpty, rkEps}: return rEps
  if a.kind == rkStar: return a
  mk(rkStar, @[a])

proc toRegex(trans: seq[array[nSyms, int32]]; acc: seq[bool]): (bool, RNode) =
  ## State elimination over the minimized automaton (start: state 0).
  let n = trans.len
  if n == 0: return (true, rEmpty)
  var edges = newSeq[Table[int, RNode]](n + 1)
  for s in 0 ..< n:
    var bySet = initTable[int, set[char]]()
    for sym in 0 ..< symLand:
      let t = trans[s][sym]
      if t < 0: continue
      if sym in [symMark, symMark2]:
        let m = mk(if sym == symMark: rkMark else: rkMark2)
        edges[s][t] = (if t in edges[s]: rAlt(edges[s][t], m) else: m)
      else:
        let c = symByte(sym)
        var cs = bySet.getOrDefault(int t)
        cs.incl c
        bySet[int t] = cs
    for t, cs in bySet:
      let r = mk(rkSet, bytes = cs)
      edges[s][t] = (if t in edges[s]: rAlt(edges[s][t], r) else: r)
    if acc[s]:
      edges[s][n] = (if n in edges[s]: rAlt(edges[s][n], rEps) else: rEps)
  var alive = newSeq[bool](n + 1)
  for s in 0 .. n: alive[s] = true
  var remaining = n - 1
  while remaining > 0:
    var best = -1
    var bestCost = high(int)
    var ins = newSeq[int](n + 1)
    for s in 0 .. n:
      if not alive[s]: continue
      for t, _ in edges[s]:
        if t != s: inc ins[t]
    for s in 1 ..< n:
      if not alive[s]: continue
      var outs = 0
      for t, _ in edges[s]:
        if t != s: inc outs
      let cost = ins[s] * outs
      if cost < bestCost:
        bestCost = cost
        best = s
    let q = best
    let loopR = (if q in edges[q]: rStar(edges[q][q]) else: rEps)
    var outs: seq[(int, RNode)]
    for t, r in edges[q]:
      if t != q: outs.add (t, r)
    for p in 0 .. n:
      if not alive[p] or p == q or q notin edges[p]: continue
      let inR = edges[p][q]
      edges[p].del q
      for (t, outR) in outs:
        let r = rCat(rCat(inR, loopR), outR)
        if r.size > maxRegexSize: return (false, rEmpty)
        edges[p][t] = (if t in edges[p]: rAlt(edges[p][t], r) else: r)
        if edges[p][t].size > maxRegexSize: return (false, rEmpty)
    alive[q] = false
    edges[q].clear()
    dec remaining
  let loop0 = (if 0 in edges[0]: rStar(edges[0][0]) else: rEps)
  let fin = (if n in edges[0]: edges[0][n] else: rEmpty)
  (true, rCat(loop0, fin))

type SelLang* = object
  ok*: bool
  why*: string
  re*: RNode
  states*, minStates*: int
    ## RFC-0005 S8bt: the automaton's states, built and minimized (the
    ## size caps' measure)

var selCache {.threadvar.}: Table[string, SelLang]

proc utfStep(v: int8; b: char): int8 =
  ## RFC-0005 S8bj. A UTF-8 validator (RFC 3629, PCRE's `valid_utf`): 0
  ## at a character boundary, 1..3 continuation bytes left, 10..13 the
  ## first continuation byte of E0 / ED / F0 / F4 (a narrower range); -1
  ## invalid.
  let c = ord(b)
  case v
  of 0:
    if c < 0x80: 0
    elif c in 0xC2 .. 0xDF: 1
    elif c == 0xE0: 10
    elif c == 0xED: 11
    elif c in 0xE1 .. 0xEF: 2
    elif c == 0xF0: 12
    elif c == 0xF4: 13
    elif c in 0xF1 .. 0xF3: 3
    else: -1
  of 1, 2, 3: (if c in 0x80 .. 0xBF: v - 1 else: -1)
  of 10: (if c in 0xA0 .. 0xBF: 1 else: -1)
  of 11: (if c in 0x80 .. 0x9F: 1 else: -1)
  of 12: (if c in 0x90 .. 0xBF: 2 else: -1)
  of 13: (if c in 0x80 .. 0x8F: 2 else: -1)
  else: -1

proc utfProduct(d: Dfa; invalidAccepts: bool): Dfa =
  ## RFC-0005 S8bj. `d` on valid UTF-8 words; every invalid word accepted
  ## or rejected (`invalidAccepts`). The lowering decides an invalid
  ## subject by its error code (PCRE_ERROR_BADUTF8) before it reads a
  ## language, so either choice is exact where the language is read; the
  ## right one keeps the guarded definitions satisfiable (`lkNone`,
  ## `skNoOcc`: an invalid subject has no match) and the automaton small.
  if not d.ok or d.trans.len == 0: return d
  var ids = initTable[(int, int8), int]()
  var keys: seq[(int, int8)]
  proc intern(k: (int, int8)): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  discard intern((0, 0'i8))
  let bad = intern((-1, -1'i8))   # the invalid sink
  result.ok = true
  var i = 0
  while i < keys.len:
    let (q, v) = keys[i]
    var row: array[nSyms, int32]
    for sym in 0 ..< nSyms: row[sym] = -1
    if q == -1:
      if invalidAccepts:
        for sym in 0 ..< symMark: row[sym] = int32 bad
      result.trans.add row
      result.accept.add invalidAccepts
      result.sink.add invalidAccepts
      inc i
      continue
    if q == -2:
      # `d` rejects every continuation; an invalid word is still accepted.
      for sym in 0 ..< symMark:
        let v2 = utfStep(v, symByte(sym))
        row[sym] = int32(if v2 < 0: bad else: intern((-2, v2)))
      result.trans.add row
      result.accept.add v != 0
      result.sink.add false
      inc i
      continue
    for sym in 0 ..< nSyms:
      let t = d.trans[q][sym]
      if sym >= symMark:
        if t >= 0: row[sym] = int32 intern((int(t), v))
        continue
      let v2 = utfStep(v, symByte(sym))
      if v2 < 0:
        row[sym] = int32 bad
      elif t >= 0:
        row[sym] = int32 intern((int(t), v2))
      elif invalidAccepts:
        row[sym] = int32 intern((-2, v2))
    result.trans.add row
    result.accept.add(if v == 0: d.accept[q] else: invalidAccepts)
    result.sink.add d.sink[q]
    inc i

proc langOf(d: Dfa; what: string): SelLang =
  if not d.ok:
    if d.why.len > 0: return SelLang(ok: false, why: d.why)
    return SelLang(ok: false, why: "the pattern's " & what & " automaton " &
                   "is past its size cap (" & $maxDfaStates & " states)")
  let (trans, acc) = minimize(d)
  let (fine, r) = toRegex(trans, acc)
  if fine: SelLang(ok: true, re: r, states: d.trans.len, minStates: trans.len)
  else: SelLang(ok: false, why: "the pattern's " & what & " regex is past " &
                "its size cap (" & $maxRegexSize & " nodes)")

proc langOfU(n: Nfa; invalidAccepts: bool; d: Dfa; what: string): SelLang =
  ## `langOf`, on valid UTF-8 words in UTF mode (`utfProduct`).
  langOf((if n.utf: utfProduct(d, invalidAccepts) else: d), what)

# ---- start variants -----------------------------------------------------------

proc canonPc0*(n: Nfa; pc: PrevClass): PrevClass =
  ## RFC-0005 S8bj. The representative of what precedes a start, as far as
  ## the pattern can tell: subject position 0 (for `^` / `\A` / `(?m)^`),
  ## then whether a newline ends there (`(?m)^`), and a CR (a CRLF's halves
  ## under `(*CRLF)`).
  if pc == pcStart:
    return (if n.hasBol or n.hasBolMulti: pcStart else: canonPc0(n, pcOther))
  if not n.needPc: return pcOther
  let w = wasNl(n.nl, pc)
  if n.nl == nlCRLF:
    (if pc == pcCR: pcCR elif w: pcCRLF else: pcOther)
  elif not w: pcOther
  else:
    case n.nl
    of nlCR: pcCR
    else: pcLF

proc startClasses*(n: Nfa): seq[PrevClass] =
  ## RFC-0005 S8bj. The distinct representatives (`canonPc0`), the
  ## `pcStart` one first when it is one.
  for pc in PrevClass:
    let c = canonPc0(n, pc)
    if c notin result: result.add c

type
  LangKind* = enum
    lkMark   ## `u[0..k) # u[k..]`: the match at u's start ends at k
    lkNone   ## no match at u's start
    lkEnds   ## the match at u's start ends at u's end
    lkErrM   ## RFC-0005 S8bt: the attempt is PCRE_ERROR_MATCHLIMIT
    lkErrR   ## RFC-0005 S8bt: the attempt is PCRE_ERROR_RECURSIONLIMIT

proc selectionLangV*(n: Nfa; cacheKey: string; lang: LangKind;
                     pc0: PrevClass; anchored = true; crlfElig = false;
                     noEmpty = false; nonEmpty = false): SelLang =
  ## RFC-0005 S8bj. The language `lang` of the attempt at a start preceded
  ## by `pc0` (`anchored`: an anchored call; `crlfElig`: an unanchored
  ## attempt at a CRLF's LF past the start offset).
  let pc = canonPc0(n, pc0)
  let key = cacheKey & "|" & $n.engine & "|" & $lang & "|" & $pc & "|" &
            $anchored & "|" & $crlfElig & "|" & $noEmpty & "|" & $nonEmpty
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  else:
    let acc = (case lang
               of lkMark: acMarkT
               of lkNone: acNone
               of lkEnds: acEndsT
               of lkErrM: acErrM
               of lkErrR: acErrR)
    result = langOfU(n, false, buildAttempt(n, AttemptSpec(acc: acc, anchored: anchored,
      noEmpty: noEmpty, nonEmpty: nonEmpty, pc0: pc, crlfElig: crlfElig)),
      "selection")
  selCache[key] = result

proc selectionLang*(n: Nfa; cacheKey: string; lang: LangKind;
                    atStart: bool; noEmpty = false;
                    nonEmpty = false): SelLang =
  ## RFC-0005 S8bb. `selectionLangV` at subject position 0 (`atStart`) or
  ## after an ordinary byte.
  selectionLangV(n, cacheKey, lang, (if atStart: pcStart else: pcOther),
                 noEmpty = noEmpty, nonEmpty = nonEmpty)

# ---- the search ------------------------------------------------------------------

type
  SearchKind* = enum
    skNoOcc   ## `u` with no match found by the search
    skFirst   ## `u[0..q) # u[q..]`: the search finds its match at `q`
    skSpan    ## `u[0..q) # u[q..e) % u[e..]`: ... ending at `e`
    skErrM    ## RFC-0005 S8bt: `u` whose search ends in
              ## PCRE_ERROR_MATCHLIMIT (`Nfa.costs`), were every attempt
              ## made (pcre_exec.c's minimum-length and required-character
              ## checks are the caller's: `attemptMade`)
    skErrR    ## RFC-0005 S8bt: ... in PCRE_ERROR_RECURSIONLIMIT
    skErrMAt  ## RFC-0005 S8bt: `u[0..q) # u[q..]`: that error, in the
              ## attempt at `q`
    skErrRAt  ## RFC-0005 S8bt: ... PCRE_ERROR_RECURSIONLIMIT

  Expect = enum exBump, exSkipFlight, exSkip, exCommit, exMatch, exMatchT,
    exNoMatch, exErrM, exErrR
  Verifier = object
    trans: seq[array[nSyms, int32]]
    acc: seq[bool]
    univ: seq[set[0'u8 .. 127'u8]]
      ## per state, the (final-newline state, UTF-8 validator state) pairs
      ## (`univIdx`) from which it accepts every continuation the search
      ## can feed (well-formed, valid UTF-8 in UTF mode): a run there is
      ## decided for good and dropped

  Cursor = enum cuScan, cuLanded, cuMid, cuInFlight, cuDone
  SNode = object
    cursor: Cursor
    runs: seq[(int8, int8, int32)]   ## (expectation, variant, state)
    want: bool                       ## the attempt here is the found one
    wantEnd: bool                    ## ... and its match ends here
    pend: int8
      ## RFC-0005 S8bt: cuScan under the JIT's prefix scan: positions to
      ## pass before the next one the scan visits (a skip-table jump)
    obl: seq[(int8, int16)]
      ## RFC-0005 S8bt: what the scan's guesses require of the bytes ahead
      ## (distance, set id): the byte at that distance is in the set; set
      ## id -1: at most that many bytes remain
    ign: int8
      ## RFC-0005 S8bt: pcre_exec.c's `ignore_skip_arg` for the next
      ## attempt (`Nfa.countArgs`)
    err: int8
      ## RFC-0005 S8bt: the search ended in a limit error (1: the match
      ## limit, 2: the recursion limit)

  SKey = object
    nodes: seq[SNode]
    pc: PrevClass
    nl: int8
    atS0: bool
    phase: int8      ## skFirst: `#` read
    utf: int8        ## UTF mode: the validator state (`utfStep`); -1 the
                     ## invalid sink

proc hash(x: SNode): Hash =
  var h: Hash = hash(ord(x.cursor)) !& hash(x.want) !& hash(x.wantEnd) !&
                hash(x.pend) !& hash(x.ign) !& hash(x.err)
  for r in x.runs: h = h !& hash(r)
  for o in x.obl: h = h !& hash(o)
  !$h

proc `<`(a, b: SNode): bool =
  if a.cursor != b.cursor: return a.cursor < b.cursor
  if a.want != b.want: return a.want < b.want
  if a.wantEnd != b.wantEnd: return a.wantEnd < b.wantEnd
  if a.runs.len != b.runs.len: return a.runs.len < b.runs.len
  for i in 0 ..< a.runs.len:
    if a.runs[i] != b.runs[i]: return a.runs[i] < b.runs[i]
  if a.pend != b.pend: return a.pend < b.pend
  if a.ign != b.ign: return a.ign < b.ign
  if a.err != b.err: return a.err < b.err
  if a.obl.len != b.obl.len: return a.obl.len < b.obl.len
  for i in 0 ..< a.obl.len:
    if a.obl[i] != b.obl[i]: return a.obl[i] < b.obl[i]
  false

proc hash(k: SKey): Hash =
  var h: Hash = 0
  for x in k.nodes: h = h !& hash(x)
  h = h !& hash(ord(k.pc)) !& hash(k.nl) !& hash(k.atS0) !& hash(k.phase) !&
      hash(k.utf)
  !$h

proc univIdx(nl, u: int8): uint8 =
  ## A (final-newline state, UTF-8 validator state) pair as one index.
  uint8(nlSlot(nl) * 8 + (if u >= 10: int(u) - 6 else: int(u)))

proc jitScanObservable*(n: Nfa): bool =
  ## RFC-0005 S8bt. Whether PCRE 8.37's JIT prefix scan reads differently
  ## from the interpreter's start-of-match filter. `scan_prefix` stops at a
  ## verb, an assertion, (*ACCEPT) and every repeat it cannot count, so each
  ## path reads the scanned positions before anything with an effect: an
  ## attempt at a position either filter passes over fails, and the only
  ## trace of where the scan stops is the bumpalong's CRLF start skip after
  ## such an attempt (`skipActive`). The concrete reference (`pcreExec`)
  ## runs the scan everywhere; the JIT tests compare the two.
  n.engine == peJit837 and n.jit.on and n.skipActive

proc byteReps(n: Nfa; extra: seq[set[char]]): array[256, int] =
  ## RFC-0005 S8bt. Per byte, the least byte that every byte test of the
  ## search's construction reads alike: the automaton's byte sets, the
  ## newline bytes, CR and LF, `nextClass`'s classes, the UTF-8 ranges
  ## `utfStep` tells apart, the start-of-match filter's and `extra` (the
  ## JIT scan's sets). A row is computed once per class.
  var sets = extra
  for st in n.states:
    if st.kind == nkByte: sets.add st.bytes
  sets.add nlBytes(n.nl)
  # RFC-0005 S8bt: a possessive exit's test; `uAny`'s multi-byte newlines.
  for st in n.states:
    if st.kind == nkPoss: sets.add st.bytes
  if uAny(n):
    for b in ['\xC2', '\xE2', '\x80', '\x85']: sets.add {b}
    sets.add {'\xA8', '\xA9'}
  sets.add {'\r'}
  sets.add {'\n'}
  sets.add {'\v', '\f', '\x85'}
  for (lo, hi) in [(0x80, 0x8F), (0x90, 0x9F), (0xA0, 0xBF), (0xC0, 0xC1),
                   (0xC2, 0xDF), (0xE0, 0xE0), (0xE1, 0xEC), (0xED, 0xED),
                   (0xEE, 0xEF), (0xF0, 0xF0), (0xF1, 0xF3), (0xF4, 0xF4),
                   (0xF5, 0xFF)]:
    sets.add {char(lo) .. char(hi)}
  sets.add {n.fc1, n.fc2}
  sets.add n.bits
  var firstOf = initTable[seq[bool], int]()
  for b in 0 .. 255:
    var sig = newSeq[bool](sets.len)
    for i, cs in sets: sig[i] = char(b) in cs
    result[b] = firstOf.mgetOrPut(sig, b)

proc buildVerifier(n: Nfa; ex: Expect; pc: PrevClass; elig: bool;
                   ign0, ign1: int8; ok: var bool; why: var string;
                   igns: var set[int8]): Verifier =
  ## RFC-0005 S8bt: `ign0` the attempt's `ignore_skip_arg`, `ign1` (exBump,
  ## exSkipFlight) the next one's; `igns` the next ones the attempt can
  ## leave.
  let acc = (case ex
             of exBump: acBump
             of exSkipFlight, exSkip: acSkipT
             of exCommit: acCommit
             of exMatch: acMatch
             of exMatchT: acMatchT
             of exNoMatch: acNone
             of exErrM: acErrM
             of exErrR: acErrR)
  var d = buildAttempt(n, AttemptSpec(acc: acc, anchored: n.anchoredPat, pc0: pc,
                                      crlfElig: elig, ign0: ign0, ign1: ign1,
                                      tracksIgn: n.countArgs))
  if not d.ok:
    ok = false
    why = d.why
    return
  igns = d.igns
  let (t, a, _) = minimizeMap(d)
  result.trans = t
  result.acc = a
  # A state accepts every continuation the search can feed it from a
  # (final-newline, UTF-8) state when no well-formed, valid path reaches a
  # rejecting end or a missing transition: a fixpoint over the product.
  # Minimization merges states that differ only in that bookkeeping, so
  # this is computed on the minimized automaton, per bookkeeping state.
  let uStates = (if n.utf: @[0'i8, 1, 2, 3, 10, 11, 12, 13] else: @[0'i8])
  # RFC-0005 S8bt: one symbol per byte class (`byteReps`; the attempt's
  # rows agree on a class).
  let reps = byteReps(n, @[])
  var syms: seq[int]
  for sym in 0 ..< symMark:
    if sym >= 256 or reps[sym] == sym: syms.add sym
  var bad = newSeq[set[0'u8 .. 127'u8]](t.len)
  proc idx(sg: int; u: int8): uint8 = univIdx(int8(sg), u)
  let nlSts = nlStates(uAny(n))
  for c in 0 ..< t.len:
    for sg in nlSts:
      for u in uStates:
        var b = u == 0 and nlCanEnd(int8(sg)) and not a[c]
        if not b:
          for sym in syms:
            if nlStepFor(n.nl, int8(sg), sym, uAny(n)) >= 0 and
               t[c][sym] < 0 and
               (not n.utf or utfStep(u, symByte(sym)) >= 0):
              b = true
              break
        if b: bad[c].incl idx(sg, u)
  var changed = true
  while changed:
    changed = false
    for c in 0 ..< t.len:
      for sg in nlSts:
        for u in uStates:
          if idx(sg, u) in bad[c]: continue
          for sym in syms:
            let s2 = nlStepFor(n.nl, int8(sg), sym, uAny(n))
            if s2 < 0: continue
            let u2 = (if n.utf: utfStep(u, symByte(sym)) else: 0'i8)
            if u2 < 0: continue
            let c2 = t[c][sym]
            if c2 >= 0 and idx(int(s2), u2) in bad[c2]:
              bad[c].incl idx(sg, u)
              changed = true
              break
  result.univ = newSeq[set[0'u8 .. 127'u8]](t.len)
  for c in 0 ..< t.len:
    for sg in nlSts:
      for u in uStates:
        if idx(sg, u) notin bad[c]: result.univ[c].incl idx(sg, u)

var verCache {.threadvar.}: Table[(string, Expect, PrevClass, bool, int8,
                                    int8),
                                   (Verifier, bool, string, set[int8])]

proc searchDfa(n: Nfa; cacheKey: string; kind: SearchKind;
               pc0: PrevClass; foundIgn = -1'i8): Dfa =
  ## RFC-0005 S8bj. The search as a guess-and-verify automaton (see the
  ## module doc), determinized. RFC-0005 S8bt: the verifiers are shared by
  ## a pattern's searches (`cacheKey`: the pattern and engine).
  var vers = initTable[(Expect, PrevClass, bool, int8, int8), int]()
  var vlist: seq[Verifier]
  var vok = true
  var vwhy = ""
  var nextIgns = initTable[(PrevClass, bool, int8), set[int8]]()
  proc verifier(ex: Expect; pc: PrevClass; elig: bool; ign0 = 0'i8;
                ign1 = 0'i8): int =
    ## RFC-0005 S8bt: `ign0` the attempt's `ignore_skip_arg`, `ign1` the
    ## next one's (a bump or a SKIP's jump).
    let ex2 = (if ex == exSkip: exSkipFlight else: ex)
    let key = (ex2, canonPc0(n, pc), elig and n.hasNeverSkip, ign0,
               (if ex2 in {exBump, exSkipFlight}: ign1 else: 0'i8))
    if key notin vers:
      vers[key] = vlist.len
      let gk = (cacheKey, key[0], key[1], key[2], key[3], key[4])
      if gk notin verCache:
        var fine = true
        var why = ""
        var igns: set[int8]
        let v = buildVerifier(n, key[0], key[1], key[2], key[3], key[4],
                              fine, why, igns)
        verCache[gk] = (v, fine, why, igns)
      let (v, fine, why, igns) = verCache[gk]
      if not fine:
        vok = false
        if vwhy.len == 0: vwhy = why
      if key[0] == exBump: nextIgns[(key[1], key[2], key[3])] = igns
      vlist.add v
    vers[key]
  proc ignsAfter(pc: PrevClass; elig: bool; ign0: int8): set[int8] =
    ## RFC-0005 S8bt: the `ignore_skip_arg` values an attempt can leave.
    if not n.countArgs: return {0'i8}
    discard verifier(exBump, pc, elig, ign0, 0)
    nextIgns.getOrDefault((canonPc0(n, pc), elig and n.hasNeverSkip, ign0),
                          {0'i8})
  var ids = initTable[SKey, int]()
  var keys: seq[SKey]
  proc intern(k: SKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  let anchored = n.anchoredPat
  discard intern(SKey(nodes: @[SNode(cursor: cuScan)], pc: pc0, atS0: true))
  result.ok = true
  # RFC-0005 S8bt: the JIT's prefix scan (`pcre_jit.nim`) decides a start
  # from the bytes ahead of it: each guess records what it needs of them
  # (`SNode.obl`), checked as they are read. Every path reads the scan's
  # positions before any verb, so an attempt at a position the scan passes
  # over fails without effect: the scan is observable only through the
  # CRLF start skip after a bump (`jitScanObservable`).
  let jitOn = jitScanObservable(n) and not anchored
  var obSets: seq[set[char]]
  var obIds = initTable[set[char], int16]()
  proc sid(cs: set[char]): int16 =
    if cs notin obIds:
      obIds[cs] = int16(obSets.len)
      obSets.add cs
    obIds[cs]
  var anySid, emptySid: int16
  var tSid: seq[int16]
  var mSid, nmSid: seq[int16]
  if jitOn:
    anySid = sid({'\x00'..'\xFF'})
    emptySid = sid({})
    if n.jit.rangeRight >= 0:
      for t in 0 .. n.jit.rangeLen:
        var cs: set[char]
        for b in 0 .. 255:
          if n.jit.table[b] == t: cs.incl char(b)
        tSid.add sid(cs)
    for k in 0 ..< n.jit.offs.len:
      var cs: set[char]
      for b in 0 .. 255:
        if (uint32(b) or n.jit.cmp[k][1]) == n.jit.cmp[k][0]: cs.incl char(b)
      mSid.add sid(cs)
      nmSid.add sid({'\x00'..'\xFF'} - cs)
  let reps = byteReps(n, obSets)

  proc addObl(node: var SNode; d: int; sd: int16): bool =
    ## Requires the byte at distance `d` to be in set `sd` (-1: at most `d`
    ## bytes remain); false when that contradicts the node's requirements.
    if sd >= 0 and sd == emptySid: return false
    var o = node.obl
    var endBy = -1
    for (d2, s2) in o:
      if s2 < 0: endBy = d2
    if sd < 0:
      if endBy >= 0 and endBy <= d: return true
      endBy = d
      var nx: seq[(int8, int16)]
      for (d2, s2) in o:
        if s2 >= 0:
          if d2 >= endBy: return false
          nx.add (d2, s2)
      nx.add (int8(d), -1'i16)
      o = nx
    else:
      if endBy >= 0 and d >= endBy: return false
      var merged = false
      for e in o.mitems:
        if e[0] == int8(d) and e[1] >= 0:
          let cs = obSets[e[1]] * obSets[sd]
          if cs.card == 0: return false
          e[1] = sid(cs)
          merged = true
      if not merged: o.add (int8(d), sd)
    # Canonical: a byte at distance `d` exists when one at a further
    # distance is required, so "any byte" there says nothing more.
    var nx: seq[(int8, int16)]
    for (d2, s2) in o:
      if s2 == anySid:
        var later = false
        for (d3, s3) in o:
          if s3 >= 0 and s3 != anySid and d3 >= d2: later = true
          if s3 == anySid and d3 > d2: later = true
        if later: continue
      nx.add (d2, s2)
    nx.sort()
    node.obl = nx
    true

  proc discharge(node: var SNode; c: int): bool =
    ## The byte `c` (-1: the end) is read: the requirements at distance 0
    ## are checked, the others come one byte closer.
    if node.obl.len == 0: return true
    var nx: seq[(int8, int16)]
    for (d, sd) in node.obl:
      if c < 0:
        if sd >= 0: return false
      elif d == 0:
        if sd >= 0:
          if char(c) notin obSets[sd]: return false
        else:
          return false
      else:
        nx.add (d - 1, sd)
    node.obl = nx
    true

  proc jitVisit(node: SNode; c: int): seq[(SNode, bool)] =
    ## The JIT's scan at this position: (node, an attempt starts here).
    if node.pend > 0:
      var x = node
      dec x.pend
      return @[(x, false)]
    let j = n.jit
    # It gives up when at most `max - 1` bytes remain, and attempts here.
    var q = node
    if addObl(q, j.max - 1, -1): result.add (q, true)
    if c < 0: return
    var g = node
    if not addObl(g, j.max - 1, anySid): return
    if j.rangeRight >= 0:
      for t in 1 .. j.rangeLen:
        var x = g
        if addObl(x, j.rangeRight, tSid[t]):
          x.pend = int8(t - 1)
          result.add (x, false)
      if not addObl(g, j.rangeRight, tSid[0]): return
    var st = g
    var fine = true
    for k in 0 ..< j.offs.len:
      if not addObl(st, j.offs[k], mSid[k]):
        fine = false
        break
    if fine: result.add (st, true)
    # The generated code checks the offsets in order: the first that
    # fails moves the scan on (the branches are exclusive).
    var pre = g
    for k in 0 ..< j.offs.len:
      var x = pre
      if addObl(x, j.offs[k], nmSid[k]): result.add (x, false)
      if not addObl(pre, j.offs[k], mSid[k]): break

  proc byteClass(c: int): int =
    ## Under the JIT's scan: the byte as `startHere` reads it (a UTF-8
    ## continuation byte, LF, a lead byte, any other); -1: read it whole.
    if not jitOn: return -1
    if n.utf and (c and 0xC0) == 0x80: 1
    elif c == ord('\n'): 2
    elif c >= 0xC0: 3
    else: 0

  proc done(v: int8; t: int32; nl, u: int8): bool =
    univIdx(nl, u) in vlist[v].univ[t]

  proc feed(node: var SNode; sym: int; nl, u: int8): bool =
    ## Every run reads `sym` (`nl`, `u` the newline and UTF-8 states after
    ## it); false when one dies. Identical runs are one (the same
    ## automaton in the same state accepts the same continuations).
    var nr: seq[(int8, int8, int32)]
    for (ex, v, st) in node.runs:
      let t = vlist[v].trans[st][sym]
      if t < 0: return false
      if done(v, t, nl, u): continue
      nr.add (ex, v, t)
    nr.sort()
    node.runs = deduplicate(nr, isSorted = true)
    true

  proc land(node: SNode; nl, u: int8): (bool, SNode) =
    ## The in-flight SKIP lands here.
    ## Only the in-flight run reads the landing event (an earlier attempt's
    ## run, still undecided, read its own).
    var x = node
    var nr: seq[(int8, int8, int32)]
    for (ex, v, st) in x.runs:
      if Expect(ex) != exSkipFlight:
        nr.add (ex, v, st)
        continue
      let t = vlist[v].trans[st][symLand]
      if t < 0: return (false, x)
      if not done(v, t, nl, u): nr.add (int8(ord(exSkip)), v, t)
    nr.sort()
    x.runs = deduplicate(nr, isSorted = true)
    # RFC-0005 S8bt: the JIT resumes at the landing with its scan (no CRLF
    # start skip).
    x.cursor = (if n.engine == peJit837: cuScan else: cuLanded)
    (true, x)

  proc startHere(k: SKey; node: SNode; c: int): seq[SNode] =
    ## The node's possible attempts at this position (byte `c`, -1 at the
    ## end): the nodes after choosing whether / how an attempt starts.
    var cur = node.cursor
    if cur == cuMid:
      if c >= 0 and (c and 0xC0) == 0x80:
        return (if node.want: @[] else: @[node])
      cur = cuLanded
    if cur == cuLanded:
      if c == ord('\n') and k.pc == pcCR and n.skipActive and not k.atS0:
        var x = node
        x.cursor = cuScan
        if x.want: return @[]
        return @[x]
      cur = cuScan
    if cur != cuScan:
      if node.want: return @[]
      return @[node]
    # Scanning: does the filter stop here?
    var starts: seq[SNode]
    if jitOn:
      var y = node
      y.cursor = cuScan
      for (x, here) in jitVisit(y, c):
        if here: starts.add x
        elif not node.want: result.add x
    else:
      var here = true
      if not anchored and c >= 0:
        case n.filter
        of fkNone: discard
        of fkFirst: here = char(c) == n.fc1 or char(c) == n.fc2
        of fkBits: here = char(c) in n.bits
        of fkStartline:
          if not k.atS0:
            here = wasNl(n.nl, k.pc) and
                   not (k.pc == pcCR and c == ord('\n') and
                        n.nl in {nlANY, nlANYCRLF})
      if not here:
        if node.want: return @[]
        var x = node
        x.cursor = cuScan
        return @[x]
      starts.add node
    let elig = (not k.atS0) and k.pc == pcCR and c == ord('\n') and
               n.skipActive
    var exs: seq[Expect]
    if node.want:
      exs = @[(case kind
               of skSpan: exMatchT
               of skErrMAt: exErrM
               of skErrRAt: exErrR
               else: exMatch)]
    elif anchored: exs = @[exNoMatch]
    else: exs = @[exBump, exSkipFlight, exCommit]
    # RFC-0005 S8bt: an attempt can end the search in a limit error.
    if not node.want and countsLimits(n):
      exs.add [exErrM, exErrR]
    var plan: seq[(Expect, int8)]
    for ex in exs:
      if ex in {exBump, exSkipFlight}:
        for i1 in 0'i8 .. int8(argCap):
          if i1 in ignsAfter(k.pc, elig, node.ign): plan.add (ex, i1)
      else: plan.add (ex, 0'i8)
    for (ex, i1) in plan:
     for sn in starts:
      var x = sn
      x.want = false
      x.ign = i1
      let v = verifier(ex, k.pc, elig, node.ign, i1)
      # An empty verifier: no attempt here has that outcome.
      if vlist[v].trans.len == 0: continue
      var st0 = 0'i32
      if ex == exMatchT and node.wantEnd:
        # The match is empty: its end event comes first.
        st0 = vlist[v].trans[0][symLand]
        if st0 < 0: continue
        x.wantEnd = false
        if done(int8(v), st0, k.nl, max(k.utf, 0)):
          x.cursor = cuDone
          result.add x
          continue
      x.runs.add (int8(ord(ex)), int8(v), st0)
      x.runs.sort()
      x.runs = deduplicate(x.runs, isSorted = true)
      if ex == exErrM: x.err = 1
      if ex == exErrR: x.err = 2
      x.cursor =
        if anchored or ex in {exCommit, exMatch, exMatchT, exErrM, exErrR}:
          cuDone
        elif ex == exSkipFlight: cuInFlight
        elif n.utf and (n.engine == peInterp or c >= 0xC0): cuMid
        else: cuLanded
      # RFC-0005 S8bt: the JIT bumps along by the lead byte's length (one
      # byte from inside a character, where its scan can stop).
      result.add x

  var i = 0
  while i < keys.len:
    if keys.len > maxDfaStates or not vok:
      result.ok = false
      result.why = vwhy
      return
    let k = keys[i]
    var row: array[nSyms, int32]
    for s in 0 ..< nSyms: row[s] = -1
    if k.utf < 0:
      # The invalid sink: no match is found (PCRE_ERROR_BADUTF8 decides).
      for s in 0 ..< symMark: row[s] = int32 i
      result.trans.add row
      result.accept.add true
      result.sink.add true
      inc i
      continue
    # Landing options first: an in-flight node may land here.
    var landed: seq[SNode]
    for node in k.nodes:
      landed.add node
      if node.cursor == cuInFlight:
        let (fine, x) = land(node, k.nl, max(k.utf, 0))
        if fine: landed.add x
    # The end of the subject.
    var acc = false
    if n.utf and k.utf != 0:
      acc = false   # ends inside a character: invalid
    elif nlCanEnd(k.nl) and (kind in {skNoOcc, skErrM, skErrR} or
                           k.phase == (if kind == skSpan: 2 else: 1)):
      # RFC-0005 S8bt: a search that ends in an error finds no match.
      let wantErr = (case kind
                     of skErrM: 1'i8
                     of skErrR: 2'i8
                     else: -1'i8)
      for node in landed:
        for x0 in startHere(k, node, -1):
          var x = x0
          if x.want or x.cursor == cuInFlight: continue
          if wantErr >= 0 and x.err != wantErr: continue
          if not discharge(x, -1): continue
          var good = true
          for (ex, v, st) in x.runs:
            if not vlist[v].acc[st]: good = false
          if good:
            acc = true
            break
        if acc: break
    # The marker `#`: the found attempt starts here.
    if kind in {skFirst, skSpan, skErrMAt, skErrRAt} and k.phase == 0:
      var nodes: seq[SNode]
      for node in landed:
        if node.cursor in {cuDone, cuInFlight}: continue
        # RFC-0005 S8bt: only a found attempt starting with this
        # `ignore_skip_arg` (`foundIgn`, -1: any).
        if foundIgn >= 0 and node.ign != foundIgn: continue
        var x = node
        x.want = true
        if x notin nodes: nodes.add x
      if nodes.len > 0:
        nodes.sort()
        var k2 = k
        k2.nodes = nodes
        k2.phase = 1
        row[symMark] = int32 intern(k2)
    # The marker `%`: the found match ends here.
    if kind == skSpan and k.phase == 1:
      var nodes: seq[SNode]
      for node in landed:
        var x = node
        if x.want:
          x.wantEnd = true
        else:
          var nr: seq[(int8, int8, int32)]
          var alive = true
          for (ex, v, st) in x.runs:
            if Expect(ex) != exMatchT:
              nr.add (ex, v, st)
              continue
            let t = vlist[v].trans[st][symLand]
            if t < 0:
              alive = false
              break
            if not done(v, t, k.nl, max(k.utf, 0)): nr.add (ex, v, t)
          if not alive: continue
          nr.sort()
          x.runs = nr
        if x notin nodes: nodes.add x
      if nodes.len > 0:
        nodes.sort()
        var k2 = k
        k2.nodes = nodes
        k2.phase = 2
        row[symMark2] = int32 intern(k2)
    # A byte, or a final newline's.
    var starts = initTable[(int, int), seq[SNode]]()
    var startsNow: seq[SNode]
    if (k.nl and nlFinal) == 0:
      for s in 0 ..< symMark:
        if s < 256 and reps[s] != s:
          row[s] = row[reps[s]]
          continue
        let nls = nlStepFor(n.nl, k.nl, s, uAny(n))
        if nls < 0: continue
        let c = ord(symByte(s))
        var u2 = 0'i8
        if n.utf:
          u2 = utfStep(k.utf, char(c))
          if u2 < 0:
            continue
        var nodes: seq[SNode]
        var seen = initHashSet[SNode]()
        let cls = byteClass(c)
        for li, node in landed:
          # RFC-0005 S8bt: under the JIT's scan the attempts at a position
          # depend on the byte only through its class (`byteClass`).
          let sk = (li, cls)
          if cls < 0 or sk notin starts:
            let r = startHere(k, node, c)
            if cls < 0: startsNow = r
            else: starts[sk] = r
          for x0 in (if cls < 0: startsNow else: starts[sk]):
            var x = x0
            if not discharge(x, c): continue
            if not feed(x, s, nls, u2): continue
            if not seen.containsOrIncl(x): nodes.add x
        if nodes.len == 0: continue
        nodes.sort()
        row[s] = int32 intern(SKey(nodes: nodes,
          pc: (if n.needPc: nextClass(char(c), k.pc, uAny(n)) else: pcOther),
          nl: nls, atS0: false, phase: k.phase, utf: u2))
    result.trans.add row
    result.accept.add acc
    result.sink.add false
    inc i

proc searchLangV*(n: Nfa; cacheKey: string; kind: SearchKind;
                  pc0: PrevClass; foundIgn = -1'i8): SelLang =
  ## RFC-0005 S8bj. The occurrence-search language `kind` of an unanchored
  ## call whose start offset is preceded by `pc0`. RFC-0005 S8bt:
  ## `foundIgn` >= 0 (skFirst, skSpan): only where the found attempt starts
  ## with that `ignore_skip_arg` (`attemptIgns`).
  let pc = canonPc0(n, pc0)
  let key = cacheKey & "|" & $n.engine & "|search|" & $kind & "|" & $pc &
            "|" & $foundIgn
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  else:
    result = langOfU(n, false, searchDfa(n, cacheKey & "|" & $n.engine,
                                         kind, pc, foundIgn), "search")
  selCache[key] = result

proc searchLang*(n: Nfa; cacheKey: string; kind: SearchKind;
                 atStart: bool): SelLang =
  ## RFC-0005 S8bb. `searchLangV` at subject position 0 (`atStart`) or
  ## after an ordinary byte.
  searchLangV(n, cacheKey, kind, (if atStart: pcStart else: pcOther))

# ---- captures -------------------------------------------------------------------

proc captureLangV*(n: Nfa; cacheKey: string; g: int; pc0: PrevClass;
                   marked: bool; anchored = true;
                   crlfElig = false; ign0 = 0'i8): SelLang =
  ## RFC-0005 S8bb, S8bj. Group `g` of PCRE's chosen match at the start of
  ## `u`: `marked`: `u` with `#` before and `%` after the group's span
  ## (`#` first when the span is empty); otherwise `u` whose match sets it.
  ## RFC-0005 S8bt: `ign0` the attempt's `ignore_skip_arg` (an unanchored
  ## caller reads it off the search, `searchLangV`'s `foundIgn`, when
  ## `attemptIgns` has more than 0).
  let pc = canonPc0(n, pc0)
  let key = cacheKey & "|" & $n.engine & "|cap|" & $g & "|" & $pc & "|" &
            $marked & "|" & $anchored & "|" & $crlfElig & "|" & $ign0
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  else:
    result = langOfU(n, false, buildAttempt(n, AttemptSpec(
      acc: (if marked: acCapMark else: acCapSet), anchored: anchored,
      pc0: pc, crlfElig: crlfElig, group: g, ign0: ign0,
      tracksIgn: n.countArgs)), "capture")
  selCache[key] = result

proc attemptIgns*(n: Nfa): seq[int8] =
  ## RFC-0005 S8bt. The `ignore_skip_arg` values an unanchored attempt can
  ## start with: 0 (a call's first), and every value an attempt leaves
  ## for the next one (`nextIgn`) -- `[0]` unless `Nfa.countArgs`. Values
  ## past `argCap`, or an attempt past the caps, are the languages'
  ## declines.
  result = @[0'i8]
  if not n.ok or not n.countArgs or n.anchoredPat: return
  var i = 0
  let eligs = (if n.hasNeverSkip: @[false, true] else: @[false])
  while i < result.len:
    for pc in startClasses(n):
      for el in eligs:
        let d = buildAttempt(n, AttemptSpec(acc: acBump, pc0: pc,
          crlfElig: el, ign0: result[i], tracksIgn: true))
        for ig in d.igns:
          if ig notin result: result.add ig
    inc i

proc captureLang*(n: Nfa; cacheKey: string; g: int; atStart,
                  marked: bool): SelLang =
  ## RFC-0005 S8bb. `captureLangV` at subject position 0 (`atStart`) or
  ## after an ordinary byte.
  captureLangV(n, cacheKey, g, (if atStart: pcStart else: pcOther), marked)

# ---- the run as a step table (replace) ----------------------------------------
#
# RFC-0005 S8bb (item 6). Nim's `replace(s, re, by)` calls PCRE once per
# match, from the end of the previous one, with NOTEMPTY_ATSTART after an
# empty match. Its value is not a language of the subject, so the walker
# encodes the run itself as a Z3 recursive function over the subject's
# suffixes (`regex_parser.replaceRunZ3`), driven by a step table. The S8bb
# table (`RunTable`) holds the priority run of a pattern with no
# backtracking verb, no `(?m)` anchor and no UTF character, where the CRLF
# start skip is unobservable (`legacyRun`); RFC-0005 S8bj: every other
# pattern gets the agenda's table (`StepTable`), whose states hold the
# pending verbs and matches with their positions as registers.

const
  maxStepStates* {.intdefine: "nelliMaxStepStates".} = 512
    ## the step table's state cap (the Z3 term's size)
  maxRegs* {.intdefine: "nelliMaxRegs".} = 6
    ## RFC-0005 S8bj: the agenda table's register cap
  rcOther* = 0           ## `RunTable`'s context index
  rcNll* = 1
  rcEnd* = 2

type
  RunTable* = object
    ok*: bool
    why*: string
    start*: array[2, array[2, int]]
      ## [subject position 0][NOTEMPTY_ATSTART]: the start state
    matched*: seq[array[3, array[2, bool]]]
      ## [state][context][next byte is LF]: a thread reaches `Match`
    next*: seq[array[2, array[256, int32]]]
      ## [state][context: other / nll][byte]: the next state, -1 dead

proc startAgenda(n: Nfa; ign0 = 0'i8): seq[Item[int8]] =
  ## The attempt's agenda before its first position; RFC-0005 S8bt: `ign0`
  ## its `ignore_skip_arg`.
  @[Item[int8](kind: ikThread, st: int32(n.start), marks: initMarks(n),
               anc: -1, stl: ign0)]

proc crlfSkipObservable*(n: Nfa): bool =
  ## RFC-0005 S8bj. Whether the bumpalong's CRLF skip (pcre_exec.c: no start
  ## at a CRLF's LF after a failed attempt at its CR) can change a result:
  ## an attempt at that LF could match, read the LF, or end the search
  ## (`(*COMMIT)`) or jump (`(*SKIP)`) instead of bumping along.
  if not n.skipActive: return false
  if n.hasCommit or n.hasSkip or n.hasNeverSkip: return true
  for ctx in [cxOther, cxNll]:
    var ctr = 0'i32
    let sc = StepCtx(ctx: ctx, nb: ord('\n'), pc: pcCR, atStart: true,
                     crlfElig: true, tagNow: 0)
    let cl = closure(n, startAgenda(n), sc, ctr, noSave)
    for it in cl:
      if it.kind == ikMatch: return true
      if it.kind == ikThread and '\n' in n.states[it.st].bytes: return true
  false

proc legacyRun*(n: Nfa): bool =
  ## RFC-0005 S8bj. Whether the S8bb step table (`runTable`) reads the
  ## pattern's `replace` exactly: no verb but MARK, no `(?m)` anchor, no UTF
  ## character, and no observable CRLF start skip.
  n.ok and not n.costs and not n.utf and not n.hasBolMulti and
    not n.hasEolMulti and
    not (n.hasCommit or n.hasSkip or n.hasThen or n.hasPrune or
         n.hasNeverSkip) and
    not crlfSkipObservable(n)

proc runTable*(n: Nfa): RunTable =
  ## RFC-0005 S8bb. The step table of `n`'s priority run (see above), or
  ## `ok == false` past `maxStepStates` (only for `legacyRun` patterns).
  if not n.ok: return RunTable(ok: false, why: n.why)
  doAssert legacyRun(n), "runTable: not a legacy-run pattern"
  # A key: the threads (state, condition), NOTEMPTY_ATSTART, position 0.
  var ids = initTable[(seq[int], bool, bool), int]()
  var keys: seq[(seq[int], bool, bool)]
  proc intern(k: (seq[int], bool, bool)): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  proc toKey(items: seq[Item[int8]]): seq[int] =
    for it in items: result.add int(it.st) * 4 + ord(it.cond)
  proc fromKey(k: seq[int]): seq[Item[int8]] =
    for x in k:
      result.add Item[int8](kind: ikThread, st: int32(x div 4),
                            cond: Cond(x mod 4), marks: initMarks(n),
                            anc: -1)
  result.ok = true
  for bol in [false, true]:
    for ne in [false, true]:
      result.start[ord(bol)][ord(ne)] =
        intern((toKey(startAgenda(n)), ne, bol and n.hasBol))
  var i = 0
  while i < keys.len:
    if keys.len > maxStepStates:
      return RunTable(ok: false, why: "the pattern's run is past its " &
                      "step-table cap (" & $maxStepStates & " states)")
    let (threads, ne, bol) = keys[i]
    var m: array[3, array[2, bool]]
    var nx: array[2, array[256, int32]]
    for ci, ctx in [cxOther, cxNll, cxEnd]:
      for lf in [false, true]:
        var ctr = 0'i32
        let sc = StepCtx(ctx: ctx, nb: (if lf: ord('\n') else: -1),
                         pc: pcOther, pos0: bol, atStart: ne or bol,
                         noEmpty: ne)
        let cl = closure(n, resolve(fromKey(threads), lf), sc, ctr, noSave)
        var cons: seq[Item[int8]]
        for it in cl:
          if it.kind == ikMatch and it.cond == cdNone: m[ci][ord(lf)] = true
          elif it.kind == ikThread: cons.add it
        if ctx == cxEnd: continue
        for b in 0 .. 255:
          if (char(b) == '\n') != lf: continue
          let t = advance(n, cons, char(b))
          nx[ci][b] =
            (if t.len == 0: -1'i32 else: int32 intern((toKey(t), false, false)))
    result.matched.add m
    result.next.add nx
    inc i

type
  LeafKind* = enum
    lfNext    ## undecided: go on to `next`
    lfMatch   ## a match ending at register `reg`
    lfBump    ## no match here: the search moves on one character
    lfCommit  ## the search ends with no match
    lfSkip    ## a `(*SKIP)` landing at register `reg`
  Leaf* = object
    kind*: LeafKind
    next*: int32
    regMap*: seq[int8]  ## lfNext: register i of `next` is this state's
                        ## register `regMap[i]` (-1: this position)
    reg*: int8          ## lfMatch / lfSkip: the register (-1: here)
    ign*: int8
      ## RFC-0005 S8bt: lfBump: the next attempt's `ignore_skip_arg`;
      ## lfSkip: the next one's when the SKIP jumps past the start (0
      ## otherwise)
  StepRow* = object
    atEnd*: Leaf
    other*, nll*: seq[Leaf]   ## per byte (256): the rest is not / is a
                              ## final newline
    nlsU*: seq[Leaf]
      ## RFC-0005 S8bt (`uAny`): per byte, a multi-byte newline that is not
      ## final starts here (only C2 and E2 differ from `other`)
  StepTable* = object
    ## RFC-0005 S8bj. The agenda's attempt as a step table: a state is a
    ## normalized agenda whose positions are registers (the suffix where
    ## each was recorded); a step reads one byte.
    ok*: bool
    why*: string
    rows*: seq[StepRow]
    start*: Table[(PrevClass, bool, bool, int8), int]
      ## [the canonical class before the start, NOTEMPTY_ATSTART, a
      ## CRLF's LF past the start offset (`crlfElig`), RFC-0005 S8bt: the
      ## attempt's `ignore_skip_arg` (0 with NOTEMPTY_ATSTART, at the
      ## call's start)]: the start state
    igns*: seq[int8]
      ## RFC-0005 S8bt: the `ignore_skip_arg` values an attempt starts with
      ## (`[0]` unless `Nfa.countArgs`)

  TKey = object
    items: seq[Item[int8]]
    pc: PrevClass
    start: int8    ## 0 none; else 1 + 2*ne + 4*elig (+ 8 pos0)
    elig: bool     ## RFC-0005 S8bt: the attempt starts at a CRLF's LF (a
                   ## SKIP:NAME's re-run moves past it)

proc hash(k: TKey): Hash =
  var h: Hash = hash(ord(k.pc)) !& hash(k.start) !& hash(k.elig)
  for it in k.items: h = h !& hash(it)
  !$h

proc `==`(a, b: TKey): bool =
  a.items == b.items and a.pc == b.pc and a.start == b.start and
    a.elig == b.elig

proc tagsOf(items: seq[Item[int8]]): seq[int32] =
  ## The registers the agenda refers to, in order of first reference.
  for it in items:
    case it.kind
    of ikMatch:
      if it.tag notin result: result.add it.tag
    of ikTerm:
      if it.term == tmSkip and it.tag notin result: result.add it.tag
    of ikThread:
      for m in it.marks:
        if m >= 0 and m notin result: result.add m
    else: discard

proc retag(items: seq[Item[int8]]; order: seq[int32]): seq[Item[int8]] =
  result = items
  proc idx(t: int32): int32 = int32(order.find(t))
  for it in result.mitems:
    case it.kind
    of ikMatch: it.tag = idx(it.tag)
    of ikTerm:
      if it.term == tmSkip: it.tag = idx(it.tag)
    of ikThread:
      for m in it.marks.mitems:
        if m >= 0: m = idx(m)
    else: discard

proc stepTable*(n: Nfa): StepTable =
  ## RFC-0005 S8bj. The agenda table of `n` for unanchored attempts (see
  ## above), or `ok == false` past the caps.
  if not n.ok: return StepTable(ok: false, why: n.why)
  var stale = false
  var ids = initTable[TKey, int]()
  var igns: seq[int8]
  var keys: seq[TKey]
  proc intern(k: TKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  result.ok = true
  let eligs = (if n.hasNeverSkip: @[false, true] else: @[false])
  var starts: Table[(PrevClass, bool, bool, int8), int]
  proc addIgn(ig: int8) =
    ## RFC-0005 S8bt: the start states of the attempts that start with
    ## `ignore_skip_arg` = `ig` (a call's first attempt has 0).
    if ig in igns: return
    igns.add ig
    for pc in startClasses(n):
      for ne in [false, true]:
        if ne and ig != 0: continue
        for el in eligs:
          let st = int8(1 + 2 * ord(ne) + 4 * ord(el) +
                        8 * ord(pc == pcStart))
          starts[(pc, ne, el, ig)] =
            intern(TKey(items: startAgenda(n, ig), pc: pc, start: st,
                        elig: el))
  addIgn(0)
  var i = 0
  while i < keys.len:
    if keys.len > maxStepStates:
      return StepTable(ok: false, why: "the pattern's run is past its " &
                       "step-table cap (" & $maxStepStates & " states)")
    let k = keys[i]
    let regs = int32(tagsOf(k.items).len)
    let st = k.start
    proc mkCtx(ctx: Ctx; nb: int; fin: bool; nls = false): StepCtx =
      StepCtx(ctx: ctx, nb: nb, nls: nls, finCRLF: fin, pc: k.pc,
              pos0: (st and 8) != 0, atStart: st != 0,
              noEmpty: (st and 2) != 0, crlfElig: (st and 4) != 0,
              eligAll: k.elig, anchored: false, tagNow: regs)
    proc leafOf(items0: seq[Item[int8]]; pcNext: PrevClass;
                ok: var bool): Leaf =
      let items = capCosts(n, normalize(items0, n.costs, n.recLimit))
      var oc = outcome(items)
      let lim = limitHit(n, items)
      if lim != okUndecided: oc = lim
      proc reg(t: int32): int8 = (if t == regs: -1'i8 else: int8(t))
      # RFC-0005 S8bt: the `ignore_skip_arg` an outcome leaves for the next
      # attempt (a SKIP's jump, or a re-run past a CRLF's LF, after a
      # SKIP:NAME without its MARK): a start state per value, up to
      # `argCap`.
      var ig = 0'i8
      if oc != okUndecided and items.len > 0:
        ig = nextIgn(oc, items[0], true)
      if oc == okStale or ig > argCap or (n.costs and ig != 0):
        stale = true
        ok = false
        return Leaf(kind: lfBump)
      if ig != 0: addIgn(ig)
      case oc
      of okNoMatch, okBump: Leaf(kind: lfBump, ign: ig)
      # RFC-0005 S8bt: a limit error ends `replace` as a miss does.
      of okCommit, okLimitM, okLimitR: Leaf(kind: lfCommit)
      of okMatch: Leaf(kind: lfMatch, reg: reg(items[0].tag))
      of okSkip, okStale: Leaf(kind: lfSkip, reg: reg(items[0].tag), ign: ig)
      of okUndecided:
        let order = tagsOf(items)
        if order.len > maxRegs:
          ok = false
          return Leaf(kind: lfBump)
        var mp: seq[int8]
        for t in order: mp.add reg(t)
        let k2 = TKey(items: canon(retag(items, order)),
                      pc: (if n.needPc: pcNext else: pcOther), elig: k.elig)
        Leaf(kind: lfNext, next: int32 intern(k2), regMap: mp)
    var row: StepRow
    var fine = true
    block:
      var ctr = 1_000_000'i32
      let cl = closure(n, resolve(k.items, false), mkCtx(cxEnd, -1, false),
                       ctr, noSave)
      row.atEnd = leafOf(dropThreads(cl), pcOther, fine)
    row.other = newSeq[Leaf](256)
    row.nll = newSeq[Leaf](256)
    row.nlsU = newSeq[Leaf](256)
    let ua = uAny(n)
    var cache = initTable[(int, int), seq[Item[int8]]]()
    # RFC-0005 S8bt: under `uAny` a multi-byte newline's lead (C2, E2)
    # starts a final one (`nll`), one with more after it (`nlsU`), or none.
    for ci, ctx in [cxOther, cxNll, cxOther]:
      for b in 0 .. 255:
        let c = char(b)
        let lead = ua and c in {'\xC2', '\xE2'}
        if ci == 1 and c notin nlBytesOf(n) and
           not (nlPair(n.nl) and c == '\r') and not lead:
          continue
        if ci == 2 and not lead:
          row.nlsU[b] = row.other[b]
          continue
        let fin = ctx == cxNll and n.nl == nlCRLF and c == '\r'
        let here = c in nlBytesOf(n) or (lead and ci > 0)
        # The closure depends on the byte only as a newline byte or a CR
        # (RFC-0005 S8bt: or a possessive exit's test, `costs`).
        let ck = (ci, (if n.costs or here or c in {'\r', '\n'}: b else: -1))
        var cl: seq[Item[int8]]
        if ck in cache: cl = cache[ck]
        else:
          var ctr = 1_000_000'i32
          cl = closure(n, resolve(k.items, c == '\n'), mkCtx(ctx, b, fin, here),
                       ctr, noSave)
          cache[ck] = cl
        let lf = leafOf(advance(n, cl, c), nextClass(c, k.pc, ua), fine)
        case ci
        of 0: row.other[b] = lf
        of 1: row.nll[b] = lf
        else: row.nlsU[b] = lf
    if not fine:
      if stale: return StepTable(ok: false, why: staleWhyOf(n))
      return StepTable(ok: false, why: "the pattern's run holds more than " &
                       $maxRegs & " pending positions")
    result.rows.add row
    inc i
  result.start = starts
  result.igns = igns

# ---- the concrete call (the reference of every lowering) ----------------------

const
  pcreUnmodelled* = -1000
    ## RFC-0005 S8bt: `pcreExec`'s result where the model stops
    ## (`staleWhy`); never a libpcre code
  pcreErrBadOffset* = -24
  pcreErrBadUtf8* = -10
  pcreErrBadUtf8Offset* = -11
  pcreErrMatchLimit* = -8
  pcreErrRecursionLimit* = -21
  reqByteMax* = 1000   ## pcre_internal.h's REQ_BYTE_MAX

type LimitEffect* = enum
  leNone     ## no start-option limit below PCRE's default
  leZero     ## a limit of 0: the first attempt made is an error
  leUnknown  ## a limit between: its effect is not computed (a decline)
  leCounted  ## RFC-0005 S8bt: a limit between, read off the automaton's
             ## `match()` calls (`Nfa.costs`)

proc limitEffect*(n: Nfa): (LimitEffect, int) =
  ## RFC-0005 S8bj. What the `(*LIMIT_MATCH=)` / `(*LIMIT_RECURSION=)` start
  ## options do to `pcre_exec` (pcre_exec.c applies one only below its
  ## default, 10_000_000), with the error code of `leZero`.
  ## `match()` counts a call against LIMIT_MATCH before it checks the depth
  ## against LIMIT_RECURSION, so LIMIT_MATCH=0 wins over LIMIT_RECURSION=0.
  let m = n.limitMatch >= 0 and n.limitMatch < pcreDefaultLimit
  let r = n.limitRecursion >= 0 and n.limitRecursion < pcreDefaultLimit
  if countsLimits(n): return (leCounted, 0)
  if n.engine == peJit837:
    # RFC-0005 S8bt: the JIT ignores LIMIT_RECURSION, and counts
    # LIMIT_MATCH down from the limit, failing when the count reaches 0:
    # from 0 it never does (probed: `(*LIMIT_MATCH=0)a` matches "a").
    if m and n.limitMatch > 0: return (leUnknown, 0)
    return (leNone, 0)
  if m and n.limitMatch == 0: return (leZero, pcreErrMatchLimit)
  if m: return (leUnknown, 0)
  if r and n.limitRecursion == 0: return (leZero, pcreErrRecursionLimit)
  if r: return (leUnknown, 0)
  (leNone, 0)

proc otherCaseOf*(c: char): char =
  if c in {'a'..'z'}: char(ord(c) - 32)
  elif c in {'A'..'Z'}: char(ord(c) + 32)
  else: c

proc attemptMade*(n: Nfa; s: string; x: int; firstSet: bool;
                  jit = false): bool =
  ## RFC-0005 S8bj. pcre_exec.c's minimum-length and required-character
  ## checks at a start `x` the scan stopped at (`firstSet`: the first
  ## character was used): false when they end the search before `match()`.
  ## RFC-0005 S8bt: the JIT (`jit`) searches for the required character
  ## also when exactly REQ_BYTE_MAX bytes remain.
  if n.noStartOpt: return true
  let so = n.so
  if so.minLength > 0 and s.len - x < so.minLength: return false
  if so.reqChar >= 0 and (s.len - x < reqByteMax or
                          (jit and s.len - x == reqByteMax)):
    let r1 = char(so.reqChar)
    let r2 = (if so.reqCaseless: otherCaseOf(r1) else: r1)
    var p = x + (if firstSet: 1 else: 0)
    var found = false
    while p < s.len:
      if s[p] == r1 or s[p] == r2:
        found = true
        break
      inc p
    if not found: return false
  true

proc execCore(n: Nfa; s: string; start: int; anchoredCall: bool;
              ne: bool; maxCalls, maxDepth: var int): ((int, int, int), int8) =
  ## `pcreExecIgn`, with the most `match()` calls of an attempt it made and
  ## its deepest frame (`pcreLimits`).
  if start < 0 or start > s.len: return ((pcreErrBadOffset, 0, 0), 0)
  if n.utf:
    if utf8Error(s) >= 0: return ((pcreErrBadUtf8, 0, 0), 0)
    if start > 0 and start < s.len and (ord(s[start]) and 0xC0) == 0x80:
      return ((pcreErrBadUtf8Offset, 0, 0), 0)
  # RFC-0005 S8bt: an anchored call runs on the interpreter (its
  # automaton is `buildNfa(.., peInterp)`'s).
  doAssert not (anchoredCall and n.engine != peInterp),
    "pcreExec: an anchored call on a JIT automaton"
  let jit = n.engine == peJit837
  let (le, code) = limitEffect(n)
  doAssert le != leUnknown, "pcreExec: a limit whose effect is not computed"
  let anchored = anchoredCall or n.anchoredPat
  let filt = (if anchored or n.noStartOpt: fkNone else: n.filter)
  var x = start
  var ign = 0'i8
  while true:
    if jit and n.jit.on and not anchored:
      # RFC-0005 S8bt: the JIT's prefix scan.
      x = n.jit.scanFrom(s, x)
    elif filt != fkNone:
      while not created(n, s, x, start): inc x
    if not attemptMade(n, s, x, filt == fkFirst, jit): return ((-1, 0, 0), 0)
    if le == leZero: return ((code, 0, 0), 0)
    let r = runAttemptT[int8](n, s, x, start, anchored, ne and x == start,
                              0'i8, noSave, ign)
    maxCalls = max(maxCalls, r.calls)
    maxDepth = max(maxDepth, r.depth)
    var next: int
    var landed = false
    case r.kind
    of okLimitM: return ((pcreErrMatchLimit, 0, 0), 0)
    of okLimitR: return ((pcreErrRecursionLimit, 0, 0), 0)
    of okMatch: return ((1, x, r.pos), ign)
    of okCommit: return ((-1, 0, 0), 0)
    of okStale: return ((pcreUnmodelled, 0, 0), 0)
    of okSkip:
      landed = r.pos > x
      next = (if landed: r.pos else: n.nextChar(s, x, jit))
    else:
      next = n.nextChar(s, x, jit)
    # RFC-0005 S8bt: pcre_exec.c's `ignore_skip_arg` for the next attempt
    # (`nextIgn`); past `argCap` it is not modelled.
    ign = r.ign
    if ign > argCap: return ((pcreUnmodelled, 0, 0), 0)
    if anchored or next > s.len: return ((-1, 0, 0), 0)
    x = next
    # RFC-0005 S8bt: the JIT resumes at a SKIP's landing without the CRLF
    # start skip (pcre_jit_compile.c's `reset_match` jumps past the
    # bumpalong's newline check).
    if x > start and s[x - 1] == '\r' and x < s.len and s[x] == '\n' and
       n.skipActive and not (jit and landed):
      inc x

proc pcreExecIgn*(n: Nfa; s: string; start: int; anchoredCall: bool;
                  ne = false): ((int, int, int), int8) =
  ## RFC-0005 S8bj. The concrete `pcre_exec` (8.45, the interpreter) of the
  ## pattern on `s` from `start`: `(1, first, end)` for a match, `(-1, ..)`
  ## for none, `(code, ..)` for an error. `leUnknown` limits are asserted
  ## away (the lowering declines them). RFC-0005 S8bt: with the found
  ## attempt's `ignore_skip_arg`.
  var mc, md: int
  execCore(n, s, start, anchoredCall, ne, mc, md)

proc pcreExec*(n: Nfa; s: string; start: int; anchoredCall: bool;
               ne = false): (int, int, int) =
  ## `pcreExecIgn`'s call result.
  pcreExecIgn(n, s, start, anchoredCall, ne)[0]

proc pcreLimits*(n: Nfa; s: string; start: int;
                 anchoredCall: bool): (int, int) =
  ## RFC-0005 S8bt. The least `match_limit` and `match_limit_recursion`
  ## under which the call is not a limit error (`n.costs`, no limit in the
  ## pattern): its attempts' most `match()` calls, and their deepest call's
  ## frame depth plus one (pcre_exec.c resets the count per attempt).
  ## `(-1, -1)` where the model stops (`pcreUnmodelled`).
  doAssert n.costs
  var mc, md: int
  let r = execCore(n, s, start, anchoredCall, false, mc, md)
  if r[0][0] == pcreUnmodelled: return (-1, -1)
  (mc, md)

proc pcreReplace*(n: Nfa; s, by: string; unmodelled: var bool): string =
  ## RFC-0005 S8bj. Nim's `replace(s, re, by)` over `pcreExec` (std/re's
  ## loop: from the end of each match, NOTEMPTY_ATSTART after an empty one,
  ## the rest kept on the first miss or error). RFC-0005 S8bt:
  ## `unmodelled` when a call is (`pcreUnmodelled`).
  var prev = 0
  var ne = false
  while prev < s.len:
    let (rc, a, b) = pcreExec(n, s, prev, false, ne)
    ne = false
    if rc == pcreUnmodelled: unmodelled = true
    if rc < 0: break
    result.add s[prev ..< a]
    result.add by
    if a == b: ne = true
    prev = b
  result.add s[min(prev, s.len) .. ^1]

proc pcreReplace*(n: Nfa; s, by: string): string =
  ## `pcreReplace` where every call is modelled.
  var unmodelled = false
  result = pcreReplace(n, s, by, unmodelled)
  doAssert not unmodelled, "pcreReplace: a call the model does not read"
