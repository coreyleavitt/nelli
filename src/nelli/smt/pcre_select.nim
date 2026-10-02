## RFC-0005 S8bb. PCRE's match SELECTION as finite automata.
##
## `matchLen`, `endsWith` and `findBounds`'s `last` (and `replace`) depend
## on WHICH match PCRE returns at a position, not only on whether one
## exists. PCRE backtracks: it returns the first match in its priority
## order (an alternation tries its alternatives left to right, a greedy
## quantifier tries one more iteration before stopping, a lazy one the
## reverse). S8ay modelled that only where it coincides with the longest
## match (`regex_parser.selectionForm`); `a|ab`, `a*b` and `(ab)+` declined.
##
## Here the pattern is a priority NFA (Thompson's construction with ordered
## epsilon splits), run as a Pike VM: at each position the live threads are
## kept in priority order; the epsilon closure is walked depth-first in that
## order; a thread reaching `Match` RECORDS a match at the position and cuts
## every lower-priority thread. The last recorded position is the match
## PCRE returns. (The VM visits each NFA state once per position: a lower-
## priority thread in the same state has the same future and loses to the
## first.) PCRE's empty-iteration rule is kept: an unbounded repetition of a
## group whose iteration matched the empty string leaves the loop instead
## of iterating again (pcre_exec's `OP_KETRMAX` on an `OP_SBRA`); bounded
## repeats are PCRE's nested optional copies.
##
## The run is a deterministic automaton over the subject's bytes (states:
## the ordered thread lists), so each value is a regular language of the
## subject, converted to a regex by state elimination:
##   * `lkMark`:  `u[0..k) # u[k..]` such that PCRE's match at the start of
##                `u` ends at `k` (`#` the marker byte of `regex_parser`);
##   * `lkNone`:  `u` with no match at its start;
##   * `lkEnds`:  `u` whose match at its start ends at its end.
## Assertions read the subject around the position: `^` / `\A` hold at
## subject position 0 only (`atStart` says whether `u` starts there), `$` /
## `\Z` at the end or before a final newline, `\z` at the end. A final
## newline is its own input symbol so the automaton sees it: under the
## pattern's newline convention (RFC-0005 S8bb, `pcre_syntax.NlConv`) a
## final newline byte is `symFin + i` (`finBytes[i]`), and the CR of a
## final CRLF is `symR2`; each is its byte in the language. The `nl` state
## (`nlStep`) keeps the reading unique: a newline byte read as a plain
## byte must be followed by another, and a final CRLF must be read as one.
## A `(*CRLF)` dot that reads a CR leaves a FLAGGED thread (`flagCR`),
## dropped when an LF follows (`resolve`).
##
## Pure Nim (no Z3); `regex_parser.nim` turns the regex into Z3's. Every
## language is pinned against the concrete `std/re` by the exhaustive
## differential (`tests/tsymex_rfc0005_s8bb_selection.nim`), together
## with the concrete reference run `chosenEnd`.

import std/[tables, hashes, sets, algorithm]
import ./pcre_syntax

type
  NKind = enum
    nkByte    ## consume a byte of `bytes`, go to `out1`
    nkSplit   ## try `out1`, then `out2`
    nkBol     ## `^` / `\A`
    nkEol     ## `$` / `\Z`
    nkEolAbs  ## `\z`
    nkEnter   ## enter an iteration of loop `loop` (nullable body only)
    nkBack    ## end of an iteration: `out1` the loop head, `out2` the exit
    nkSave    ## capture slot `slot` (2*group or 2*group+1)
    nkMatch

  NState = object
    kind: NKind
    bytes: set[char]
    crlfDot: bool   ## RFC-0005 S8bb: nkByte of a `(*CRLF)` dot
    out1, out2: int
    loop: int
    slot: int

  Nfa* = object
    states: seq[NState]
    start*: int
    loops: int
    groups*: int     ## capturing groups
    hasBol*: bool    ## a `^` / `\A` anywhere: `atStart` matters
    nl*: NlConv      ## RFC-0005 S8bb: the newline convention
    skipCrlf*: bool  ## RFC-0005 S8bb: the bumpalong skips a CRLF's LF
    ok*: bool
    why*: string

const
  maxNfaStates = 4000
  maxLoops = 63
  maxDfaStates* = 4000
  maxRegexSize* = 40000
  symFin = 256       ## 256 ..< 261: a final newline byte `finBytes[i]`
  symR2 = 261        ## RFC-0005 S8bb: the CR of a final CRLF
  symMark = 262      ## the marker `#` (a capture's start, RFC-0005 S8bb)
  symMark2 = 263     ## RFC-0005 S8bb: a capture's end marker
  nSyms = 264
  finBytes = ['\n', '\r', '\v', '\f', '\x85']
  flagCR = 1 shl 24  ## RFC-0005 S8bb: a thread past a `(*CRLF)` dot's CR
  nlMust = 1'i8      ## a newline byte read plain: another byte follows
  nlFinal = 2'i8     ## the final newline was read: only markers follow
  nlCR = 4'i8        ## a CR read plain (CRLF a newline): no final LF next
  nlR2 = 8'i8        ## `symR2` read: the final LF is next

proc symByte(s: int): char =
  if s < 256: char(s)
  elif s < symR2: finBytes[s - symFin]
  else: '\r'

proc nlStep(n: Nfa; st: int8; s: int): int8 =
  ## RFC-0005 S8bb. The `nl` state after symbol `s` (not a marker), or -1
  ## when `s` cannot follow (the reading would not be unique).
  if (st and nlFinal) != 0: return -1
  let nl1 = nlBytes(n.nl)
  let b = symByte(s)
  if s >= symFin and s < symR2:
    if b notin nl1: return -1
    if (st and nlR2) != 0: return (if b == '\n': nlFinal else: -1'i8)
    if (st and nlCR) != 0 and b == '\n': return -1
    return nlFinal
  if s == symR2:
    if not nlPair(n.nl) or (st and nlR2) != 0: return -1
    return nlR2
  if (st and nlR2) != 0:
    # `(*CRLF)`: the pair's LF is no newline on its own.
    return (if b == '\n' and '\n' notin nl1: nlFinal else: -1'i8)
  result = 0
  if b in nl1: result = result or nlMust
  if (st and nlCR) != 0 and b == '\n': result = result or nlMust
  if nlPair(n.nl) and b == '\r': result = result or nlCR

proc nlCanEnd(st: int8): bool = (st and (nlMust or nlR2)) == 0

type Build = object
  n: Nfa
  overflow: bool
  match: int

proc add(b: var Build; s: NState): int =
  if b.n.states.len >= maxNfaStates:
    b.overflow = true
    return 0
  b.n.states.add s
  b.n.states.high

proc comp(b: var Build; x: Rx; next: int): int

proc compStar(b: var Build; sub: Rx; lazy: bool; next: int): int =
  let head = b.add NState(kind: nkSplit)
  var bodyIn: int
  if lenRange(sub)[0] == 0:
    # A body that can match the empty string: PCRE leaves the loop after
    # an empty iteration (`nkEnter` / `nkBack`).
    if b.n.loops >= maxLoops:
      b.overflow = true
      return 0
    let id = b.n.loops
    inc b.n.loops
    let back = b.add NState(kind: nkBack, loop: id, out1: head, out2: next)
    bodyIn = b.add NState(kind: nkEnter, loop: id, out1: b.comp(sub, back))
  else:
    bodyIn = b.comp(sub, head)
  if b.overflow: return 0
  if lazy:
    b.n.states[head].out1 = next
    b.n.states[head].out2 = bodyIn
  else:
    b.n.states[head].out1 = bodyIn
    b.n.states[head].out2 = next
  head

proc split(b: var Build; take, skip: int; lazy: bool): int =
  if lazy: b.add NState(kind: nkSplit, out1: skip, out2: take)
  else: b.add NState(kind: nkSplit, out1: take, out2: skip)

proc comp(b: var Build; x: Rx; next: int): int =
  if b.overflow: return 0
  var inner = next
  if x.cap > 0:
    inner = b.add NState(kind: nkSave, slot: 2 * x.cap + 1, out1: next)
  var e: int
  case x.kind
  of rxSet:
    e = b.add NState(kind: nkByte, bytes: x.bytes, crlfDot: x.crlfDot,
                     out1: inner)
  of rxAccept:
    # RFC-0005 S8bb: close the groups it is in, then Match.
    e = b.match
    for g in x.open:
      e = b.add NState(kind: nkSave, slot: 2 * g + 1, out1: e)
  of rxCat:
    e = inner
    for i in countdown(x.kids.high, 0):
      e = b.comp(x.kids[i], e)
  of rxAlt:
    e = b.comp(x.kids[^1], inner)
    for i in countdown(x.kids.high - 1, 0):
      let k = b.comp(x.kids[i], inner)
      e = b.add NState(kind: nkSplit, out1: k, out2: e)
  of rxBol:
    b.n.hasBol = true
    e = b.add NState(kind: nkBol, out1: inner)
  of rxEol:
    e = b.add NState(kind: nkEol, out1: inner)
  of rxEolAbs:
    e = b.add NState(kind: nkEolAbs, out1: inner)
  of rxRep:
    e = inner
    if x.hi < 0:
      e = b.compStar(x.sub, x.lazy, e)
    else:
      # PCRE's `x{lo,hi}`: `lo` copies, then `hi - lo` NESTED optional
      # copies (skipping one skips the rest).
      var o = e
      for _ in 1 .. x.hi - x.lo:
        o = b.split(b.comp(x.sub, o), e, x.lazy)
      e = o
    for _ in 1 .. x.lo:
      e = b.comp(x.sub, e)
  if x.cap > 0:
    e = b.add NState(kind: nkSave, slot: 2 * x.cap, out1: e)
  e

proc buildNfa*(root: Rx; groups = 0; nl = nlLF; hasCrLf = false): Nfa =
  ## RFC-0005 S8bb. The priority NFA of a `psOk` tree; `ok == false` past
  ## the size caps (`why` says which).
  var b = Build()
  b.n.groups = groups
  b.n.nl = nl
  b.n.skipCrlf = nlPair(nl) and not hasCrLf
  let m = b.add NState(kind: nkMatch)
  b.match = m
  b.n.start = b.comp(root, m)
  result = b.n
  result.ok = not b.overflow
  if b.overflow:
    result.why = "the pattern's priority automaton is past its size cap (" &
                 $maxNfaStates & " states, " & $maxLoops & " nullable loops)"

proc buildNfa*(pr: PcreParse): Nfa =
  ## RFC-0005 S8bb. The priority NFA of a `psOk` reading.
  buildNfa(pr.root, pr.groups, pr.nl, pr.hasCrLf)

# ---- the Pike step -------------------------------------------------------------

type
  Ctx* = enum
    cxOther   ## the rest of the subject is not a newline (nor empty)
    cxNll     ## the rest of the subject is a newline
    cxEnd     ## the subject ends here

  Closure = object
    consumers: seq[int]   ## byte states, in priority order
    matched: bool         ## a thread reached Match (lower ones are cut)
    matchSlots: seq[int]  ## captures of the matching thread (see `run`)

proc closure(n: Nfa; threads: seq[int]; ctx: Ctx; bolOk, noEmpty: bool): Closure =
  ## The epsilon closure of `threads` (in priority order) at one position.
  ## `bolOk`: the position is subject position 0. `noEmpty`: a match here
  ## is empty and NOTEMPTY_ATSTART forbids it (the thread fails, no cut).
  var seenC = initHashSet[int]()
  var visited = initHashSet[(int, uint64)]()
  var stack: seq[(int, uint64)]
  for i in countdown(threads.high, 0): stack.add (threads[i], 0'u64)
  while stack.len > 0:
    let (s, ent) = stack.pop()
    if (s, ent) in visited: continue
    visited.incl (s, ent)
    let st = n.states[s]
    case st.kind
    of nkByte:
      if s notin seenC:
        seenC.incl s
        result.consumers.add s
    of nkSplit:
      stack.add (st.out2, ent)
      stack.add (st.out1, ent)
    of nkBol:
      if bolOk: stack.add (st.out1, ent)
    of nkEol:
      if ctx in {cxNll, cxEnd}: stack.add (st.out1, ent)
    of nkEolAbs:
      if ctx == cxEnd: stack.add (st.out1, ent)
    of nkEnter:
      stack.add (st.out1, ent or (1'u64 shl st.loop))
    of nkBack:
      if (ent and (1'u64 shl st.loop)) != 0:
        stack.add (st.out2, ent)    # an empty iteration: leave the loop
      else:
        stack.add (st.out1, ent)
    of nkSave:
      stack.add (st.out1, ent)
    of nkMatch:
      if not noEmpty:
        result.matched = true
        return

proc advance(n: Nfa; consumers: seq[int]; c: char): seq[int] =
  var seen = initHashSet[int]()
  for s in consumers:
    if c in n.states[s].bytes:
      var t = n.states[s].out1
      if c == '\r' and n.states[s].crlfDot: t = t or flagCR
      if t notin seen:
        seen.incl t
        result.add t

proc resolve(threads: seq[int]; nextLF: bool): seq[int] =
  ## RFC-0005 S8bb. The threads at a position whose next byte is (`nextLF`)
  ## or is not an LF: a flagged one (a `(*CRLF)` dot read a CR) dies before
  ## an LF and is an ordinary thread otherwise.
  for t in threads:
    if (t and flagCR) != 0 and nextLF: continue
    let u = t and not flagCR
    if u notin result: result.add u

proc symCtx(s: int): Ctx =
  (if s < symFin: cxOther else: cxNll)

proc ctxAt(n: Nfa; u: string; j: int): Ctx =
  if j >= u.len: cxEnd
  elif j == u.len - 1 and u[j] in nlBytes(n.nl): cxNll
  elif nlPair(n.nl) and j == u.len - 2 and u[j] == '\r' and
       u[j + 1] == '\n': cxNll
  else: cxOther

proc chosenEnd*(n: Nfa; u: string; atStart: bool; noEmpty = false): int =
  ## RFC-0005 S8bb. The concrete run: the end offset in `u` of PCRE's match
  ## at the start of `u`, or -1. `atStart`: `u` starts at subject position
  ## 0. `noEmpty`: NOTEMPTY_ATSTART (an empty match is not one).
  result = -1
  var threads = @[n.start]
  for j in 0 .. u.len:
    threads = resolve(threads, j < u.len and u[j] == '\n')
    let cl = closure(n, threads, ctxAt(n, u, j), atStart and j == 0,
                     noEmpty and j == 0)
    if cl.matched: result = j
    if j == u.len or cl.consumers.len == 0: break
    threads = advance(n, cl.consumers, u[j])

# ---- the selection languages --------------------------------------------------

type
  LangKind* = enum
    lkMark   ## `u[0..k) # u[k..]`: the match at u's start ends at k
    lkNone   ## no match at u's start
    lkEnds   ## the match at u's start ends at u's end

  DKey = object
    threads: seq[int]
    pos0: bool
    phase: int    ## lkMark: 0 before `#`, 1 just after it, 2 confirmed
    nl: int8      ## `nlStep`'s state

proc hash(k: DKey): Hash =
  var h: Hash = 0
  h = h !& hash(k.threads) !& hash(k.pos0) !& hash(k.phase) !& hash(k.nl)
  !$h

type Dfa = object
  trans: seq[array[nSyms, int32]]   ## -1: dead
  accept: seq[bool]
  ok: bool

proc buildDfa(n: Nfa; lang: LangKind; atStart, noEmpty, nonEmpty: bool): Dfa =
  ## `nonEmpty`: the empty word is not in the language (lkEnds only).
  var ids = initTable[DKey, int]()
  var keys: seq[DKey]
  proc intern(k: DKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  discard intern(DKey(threads: @[n.start], pos0: true))
  result.ok = true
  var i = 0
  while i < keys.len:
    if keys.len > maxDfaStates:
      result.ok = false
      return
    let k = keys[i]
    var row: array[nSyms, int32]
    for s in 0 ..< nSyms: row[s] = -1
    let bolOk = atStart and k.pos0
    let ne = noEmpty and k.pos0
    # The end of the subject.
    var acc = false
    if nlCanEnd(k.nl):
      let cl = closure(n, resolve(k.threads, false), cxEnd, bolOk, ne)
      case lang
      of lkNone: acc = not cl.matched
      of lkEnds: acc = cl.matched and not (nonEmpty and k.pos0)
      of lkMark: acc = (k.phase == 1 and cl.matched) or
                       (k.phase == 2 and not cl.matched)
    # The marker.
    if lang == lkMark and k.phase == 0:
      var k2 = k
      k2.phase = 1
      row[symMark] = int32 intern(k2)
    # A byte, or a final newline's.
    if (k.nl and nlFinal) == 0:
      var cls: array[2, array[2, Closure]]   # [ctx is cxNll][next is LF]
      var have: array[2, array[2, bool]]
      for s in 0 ..< symMark:
        let nls = nlStep(n, k.nl, s)
        if nls < 0: continue
        let c = symByte(s)
        let ci = (if symCtx(s) == cxNll: 1 else: 0)
        let li = (if c == '\n': 1 else: 0)
        if not have[ci][li]:
          cls[ci][li] = closure(n, resolve(k.threads, li == 1), symCtx(s),
                                bolOk, ne)
          have[ci][li] = true
        let cl = cls[ci][li]
        var phase = k.phase
        case lang
        of lkNone:
          if cl.matched: continue
        of lkEnds: discard
        of lkMark:
          if k.phase == 1:
            if not cl.matched: continue
            phase = 2
          elif k.phase == 2 and cl.matched: continue
        let nx = advance(n, cl.consumers, c)
        row[s] = int32 intern(DKey(threads: nx, pos0: false, phase: phase,
                                   nl: nls))
    result.trans.add row
    result.accept.add acc
    inc i

proc minimize(d: Dfa): (seq[array[nSyms, int32]], seq[bool]) =
  ## Moore's partition refinement, dead states (no path to acceptance)
  ## removed: transitions into them become -1.
  let n = d.trans.len
  # Co-reachability.
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
  # State 0 is the start; renumber so its class is 0.
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
  (trans, acc)

# ---- regexes ------------------------------------------------------------------

type
  RKind* = enum rkEmpty, rkEps, rkSet, rkMark, rkMark2, rkCat, rkAlt, rkStar
  RNode* = ref object
    kind*: RKind
    bytes*: set[char]     ## rkSet
    kids*: seq[RNode]     ## rkCat, rkAlt, rkStar (one kid)
    size*: int
    key: string

proc keyOf(r: RNode): string = r.key

proc mk(kind: RKind; kids: seq[RNode] = @[]; bytes: set[char] = {}): RNode =
  result = RNode(kind: kind, kids: kids, bytes: bytes, size: 1)
  for k in kids: result.size += k.size
  case kind
  of rkEmpty: result.key = "0"
  of rkEps: result.key = "e"
  of rkMark: result.key = "#"
  of rkMark2: result.key = "%"
  of rkSet:
    var s = "["
    for c in bytes: s.add $ord(c) & ","
    result.key = s & "]"
  of rkStar: result.key = "(" & kids[0].key & ")*"
  of rkCat, rkAlt:
    var s = (if kind == rkCat: "C(" else: "A(")
    for k in kids: s.add k.key & ";"
    result.key = s & ")"

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
  var seen = initHashSet[string]()
  for x in [a, b]:
    for y in (if x.kind == rkAlt: x.kids else: @[x]):
      if y.kind == rkSet:
        bytes = bytes + y.bytes
        hasSet = true
      elif y.key notin seen:
        seen.incl y.key
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
  # Nodes 0 ..< n are the states, n the final state.
  var edges = newSeq[Table[int, RNode]](n + 1)
  for s in 0 ..< n:
    var bySet = initTable[int, set[char]]()
    for sym in 0 ..< nSyms:
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
  # Eliminate every state but the start (0) and the final (n).
  var remaining = n - 1
  while remaining > 0:
    # The cheapest state: fewest in * out edges.
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

var selCache {.threadvar.}: Table[string, SelLang]

# ---- occurrence search --------------------------------------------------------
#
# RFC-0005 S8bb. `contains`, `find` and `findBounds` ask for the LEFTMOST
# position with a match. With an anchor away from a top-level edge
# (`a(^|b)`) the edge-split reading of `regex_parser` cannot say whether a
# match starts at a position, so the search is built here from the
# minimized `lkNone` automata: one run per start position, all in step (a
# subset of the deterministic runs). A run that dies has found a match
# (every continuation matches).
#   * `skNoOcc`:  `u` with no match at any position `0 .. u.len`;
#   * `skFirst`:  `u[0..q) # u[q..]` such that a match starts at `q` and
#                 none starts before it.

type
  SearchKind* = enum skNoOcc, skFirst
  MinDfa = tuple[trans: seq[array[nSyms, int32]], acc: seq[bool]]
  SKey = object
    pending: seq[int32]   ## sorted: (variant shl 20) or state
    run: int32            ## the marked run: -2 none, -1 matched, else state
    phase: int8           ## 0 before the marker, 1 after
    nl: int8              ## as `DKey.nl`
    pos0: bool
    mark: int8            ## the marked run's variant

proc hash(k: SKey): Hash =
  var h: Hash = 0
  for x in k.pending: h = h !& hash(x)
  h = h !& hash(k.run) !& hash(k.phase) !& hash(k.nl) !& hash(k.pos0) !&
      hash(k.mark)
  !$h

proc minNone(n: Nfa; atStart: bool): (bool, MinDfa) =
  let d = buildDfa(n, lkNone, atStart, false, false)
  if not d.ok: return (false, (@[], @[]))
  (true, minimize(d))

proc searchDfa(n: Nfa; kind: SearchKind; atStart: bool): Dfa =
  let (okS, minS) = minNone(n, atStart)
  let (okN, minN) = minNone(n, false)
  if not (okS and okN):
    result.ok = false
    return
  let ds = [minN, minS]
  proc startOf(v: int): int32 =
    (if ds[v].trans.len == 0: -1'i32 else: 0'i32)
  proc accepts(v: int; st: int32): bool = st >= 0 and ds[v].acc[st]
  var ids = initTable[SKey, int]()
  var keys: seq[SKey]
  proc intern(k: SKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  discard intern(SKey(run: -2, pos0: true))
  result.ok = true
  var i = 0
  while i < keys.len:
    if keys.len > maxDfaStates:
      result.ok = false
      return
    let k = keys[i]
    var row: array[nSyms, int32]
    for s in 0 ..< nSyms: row[s] = -1
    # A run starts here (before the marker for skFirst).
    let v = (if atStart and k.pos0: 1 else: 0)
    var pend = k.pending
    var here = startOf(v)
    let starts = kind == skNoOcc or k.phase == 0
    var acc = false
    if nlCanEnd(k.nl):
      acc = true
      for x in pend:
        if not accepts(int(x shr 20), x and 0xFFFFF): acc = false
      if starts and not accepts(v, here): acc = false
      if kind == skFirst:
        acc = acc and k.phase == 1 and
              (k.run == -1 or (k.run >= 0 and not accepts(int(k.mark), k.run)))
    if starts and here >= 0:
      pend.add((int32(v) shl 20) or here)
    elif starts:
      pend = @[]   # a match starts here: no word extends this state
    if kind == skFirst and k.phase == 0:
      var k2 = SKey(pending: k.pending, run: startOf(v), phase: 1, nl: k.nl,
                    pos0: k.pos0, mark: int8 v)
      row[symMark] = int32 intern(k2)
    if (k.nl and nlFinal) == 0 and not (starts and here < 0):
      for s in 0 ..< symMark:
        let nls = nlStep(n, k.nl, s)
        if nls < 0: continue
        var nx: seq[int32]
        var dead = false
        for x in pend:
          let vv = int(x shr 20)
          let t = ds[vv].trans[x and 0xFFFFF][s]
          if t < 0:
            dead = true
            break
          let y = (int32(vv) shl 20) or t
          if y notin nx: nx.add y
        if dead: continue
        nx.sort()
        var run = k.run
        if run >= 0:
          let t = ds[k.mark].trans[run][s]
          run = (if t < 0: -1'i32 else: t)
        row[s] = int32 intern(SKey(pending: nx, run: run, phase: k.phase,
                                   nl: nls, pos0: false, mark: k.mark))
    result.trans.add row
    result.accept.add acc
    inc i

proc crlfSkipSeen*(n: Nfa): bool =
  ## RFC-0005 S8bb. Under a CRLF convention, with no explicit CR or LF in
  ## the pattern, PCRE's bumpalong does not try the LF of a CRLF after a
  ## failed attempt at its CR -- but its start-of-match optimisation (the
  ## first code unit, `pcre_study`'s start bits) can pass over the CR and
  ## try the LF after all (probed: `(*CRLF)[\x09-\x0b]\z` finds 1 in
  ## "\r\n", `(*CRLF)(?:[\x09-\x0b]\x00)?.` finds -1). Whether the LF
  ## is tried is then PCRE's optimiser's call. It matters only when a
  ## match can start at an LF: the start closure matches, or reads an LF.
  if not n.skipCrlf: return false
  for ctx in [cxOther, cxNll]:
    let cl = closure(n, @[n.start], ctx, false, false)
    if cl.matched: return true
    for s in cl.consumers:
      if '\n' in n.states[s].bytes: return true
  false

# ---- the run as a step table (replace) ----------------------------------------
#
# RFC-0005 S8bb (item 6). Nim's `replace(s, re, by)` calls PCRE once per
# match, from the end of the previous one, with NOTEMPTY_ATSTART after an
# empty match. Its value is not a language of the subject, so the walker
# encodes the Pike run itself as a Z3 recursive function over the subject's
# suffixes (`regex_parser.replaceRunZ3`), driven by this table: the
# run's states are its ordered thread lists; at a position, the closure
# depends on the state, the context (the rest is a final newline, or
# empty) and whether the next byte is an LF (`resolve`). A start state
# also says whether the position is subject position 0 (`^`) and whether
# NOTEMPTY_ATSTART holds there; every other state is past the start.

const
  maxStepStates* = 512   ## the step table's state cap (the Z3 term's size)
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

proc runTable*(n: Nfa): RunTable =
  ## RFC-0005 S8bb. The step table of `n`'s Pike run (see above), or
  ## `ok == false` past `maxStepStates` or where PCRE's CRLF bumpalong skip
  ## decides an occurrence (`crlfSkipSeen`).
  if not n.ok: return RunTable(ok: false, why: n.why)
  if crlfSkipSeen(n):
    return RunTable(ok: false, why: "a CRLF newline convention whose " &
                    "bumpalong skip over a CRLF's LF depends on PCRE's " &
                    "start-of-match optimisation (a match can start at an " &
                    "LF, and the pattern has no explicit CR or LF)")
  # A key: the threads, NOTEMPTY_ATSTART, subject position 0.
  var ids = initTable[(seq[int], bool, bool), int]()
  var keys: seq[(seq[int], bool, bool)]
  proc intern(k: (seq[int], bool, bool)): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  result.ok = true
  for bol in [false, true]:
    for ne in [false, true]:
      result.start[ord(bol)][ord(ne)] =
        intern((@[n.start], ne, bol and n.hasBol))
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
        let cl = closure(n, resolve(threads, lf), ctx, bol, ne)
        m[ci][ord(lf)] = cl.matched
        if ctx == cxEnd: continue
        for b in 0 .. 255:
          if (char(b) == '\n') != lf: continue
          let t = advance(n, cl.consumers, char(b))
          nx[ci][b] =
            (if t.len == 0: -1'i32 else: int32 intern((t, false, false)))
    result.matched.add m
    result.next.add nx
    inc i

proc searchLang*(n: Nfa; cacheKey: string; kind: SearchKind;
                 atStart: bool): SelLang =
  ## RFC-0005 S8bb. The occurrence-search language `kind` of `n` (see
  ## above), or `ok == false` past the size caps or where PCRE's CRLF
  ## bumpalong decides the occurrence (`crlfSkipSeen`; elsewhere the skip
  ## changes no result).
  let key = cacheKey & "|search|" & $kind & "|" & $atStart
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  elif crlfSkipSeen(n):
    result = SelLang(ok: false, why: "a CRLF newline convention whose " &
                     "bumpalong skip over a CRLF's LF depends on PCRE's " &
                     "start-of-match optimisation (a match can start at " &
                     "an LF, and the pattern has no explicit CR or LF)")
  else:
    let d = searchDfa(n, kind, atStart)
    if not d.ok:
      result = SelLang(ok: false, why: "the pattern's search automaton " &
                       "is past its size cap (" & $maxDfaStates & " states)")
    else:
      let (trans, acc) = minimize(d)
      let (fine, r) = toRegex(trans, acc)
      result =
        if fine: SelLang(ok: true, re: r)
        else: SelLang(ok: false, why: "the pattern's search regex is " &
                      "past its size cap (" & $maxRegexSize & " nodes)")
  selCache[key] = result


proc selectionLang*(n: Nfa; cacheKey: string; lang: LangKind;
                    atStart: bool; noEmpty = false;
                    nonEmpty = false): SelLang =
  ## RFC-0005 S8bb. The language `lang` of `n` (see the module doc), or
  ## `ok == false` past the automaton / regex size caps. `cacheKey`
  ## identifies `n` (its pattern and flag).
  let key = cacheKey & "|" & $lang & "|" & $atStart & "|" & $noEmpty & "|" &
            $nonEmpty
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  else:
    let d = buildDfa(n, lang, atStart, noEmpty, nonEmpty)
    if not d.ok:
      result = SelLang(ok: false, why: "the pattern's selection automaton " &
                       "is past its size cap (" & $maxDfaStates & " states)")
    else:
      let (trans, acc) = minimize(d)
      let (fine, r) = toRegex(trans, acc)
      result =
        if fine: SelLang(ok: true, re: r)
        else: SelLang(ok: false, why: "the pattern's selection regex is " &
                      "past its size cap (" & $maxRegexSize & " nodes)")
  selCache[key] = result

# ---- captures -----------------------------------------------------------------
#
# RFC-0005 S8bb. The captures overloads (`match(s, re, matches)`, `=~`,
# `find`, `contains`, `matchLen`, `findBounds`) write the capture groups of
# PCRE's chosen match. In the Pike run a thread carries its own captures
# (the last `nkSave` of each slot on its path); the chosen match's are the
# captures of the thread that recorded it. A group is SET when its closing
# slot was written on that path (a repeated group keeps its last
# iteration's span; one not entered on the path is unset -- probed).

proc closureT[T](n: Nfa; threads: seq[(int, T)]; ctx: Ctx; bolOk: bool;
                 save: proc (t: T; slot: int): T):
                 (seq[(int, T)], bool, T) =
  ## `closure` with a tag per thread: `save` updates it at an `nkSave`.
  ## Returns the byte-state threads in priority order, whether a thread
  ## reached Match, and that thread's tag.
  var seenC = initHashSet[int]()
  var visited = initHashSet[(int, uint64)]()
  var stack: seq[(int, uint64, T)]
  var cons: seq[(int, T)]
  for i in countdown(threads.high, 0): stack.add (threads[i][0], 0'u64, threads[i][1])
  while stack.len > 0:
    let (st0, ent, tag) = stack.pop()
    if (st0, ent) in visited: continue
    visited.incl (st0, ent)
    let st = n.states[st0]
    case st.kind
    of nkByte:
      if st0 notin seenC:
        seenC.incl st0
        cons.add (st0, tag)
    of nkSplit:
      stack.add (st.out2, ent, tag)
      stack.add (st.out1, ent, tag)
    of nkBol:
      if bolOk: stack.add (st.out1, ent, tag)
    of nkEol:
      if ctx in {cxNll, cxEnd}: stack.add (st.out1, ent, tag)
    of nkEolAbs:
      if ctx == cxEnd: stack.add (st.out1, ent, tag)
    of nkEnter:
      stack.add (st.out1, ent or (1'u64 shl st.loop), tag)
    of nkBack:
      if (ent and (1'u64 shl st.loop)) != 0:
        stack.add (st.out2, ent, tag)
      else:
        stack.add (st.out1, ent, tag)
    of nkSave:
      stack.add (st.out1, ent, save(tag, st.slot))
    of nkMatch:
      return (cons, true, tag)
  (cons, false, default(T))

proc advanceT[T](n: Nfa; consumers: seq[(int, T)]; c: char): seq[(int, T)] =
  var seen = initHashSet[int]()
  for (st, tag) in consumers:
    if c in n.states[st].bytes:
      var t = n.states[st].out1
      if c == '\r' and n.states[st].crlfDot: t = t or flagCR
      if t notin seen:
        seen.incl t
        result.add (t, tag)

proc resolveT[T](threads: seq[(int, T)]; nextLF: bool): seq[(int, T)] =
  ## `resolve` with a tag per thread.
  var seen = initHashSet[int]()
  for (t, tag) in threads:
    if (t and flagCR) != 0 and nextLF: continue
    let u = t and not flagCR
    if u notin seen:
      seen.incl u
      result.add (u, tag)

proc chosenCaps*(n: Nfa; u: string; atStart: bool): (int, seq[(int, int)]) =
  ## RFC-0005 S8bb. The concrete run with captures: the end of PCRE's match
  ## at the start of `u` (-1: none), and each group's `(start, end)` in it
  ## (`(-1, -1)`: unset).
  result = (-1, @[])
  var threads = @[(n.start, newSeq[int](2 * n.groups + 2))]
  for k in 0 ..< threads[0][1].len: threads[0][1][k] = -1
  var j = 0
  let save = proc (t: seq[int]; slot: int): seq[int] =
    result = t
    result[slot] = j
  while true:
    threads = resolveT(threads, j < u.len and u[j] == '\n')
    let (cons, matched, tag) = closureT(n, threads, ctxAt(n, u, j),
                                        atStart and j == 0, save)
    if matched:
      var caps: seq[(int, int)]
      for g in 1 .. n.groups:
        caps.add(if tag[2 * g + 1] < 0: (-1, -1) else: (tag[2 * g], tag[2 * g + 1]))
      result = (j, caps)
    if j == u.len or cons.len == 0: break
    threads = advanceT(n, cons, u[j])
    inc j

type
  CapKey = object
    threads: seq[(int, int8)]   ## tag: 3*s + e, s/e: 0 unset, 1 at the
                                ## marker, 2 elsewhere
    pos0: bool
    nl: int8
    sPh, ePh: int8              ## markers: 0 unread, 1 read here, 2 earlier
    best: int8                  ## the recorded match's tag, -1 none

proc hash(k: CapKey): Hash =
  var h: Hash = 0
  for (a, b) in k.threads: h = h !& hash(a) !& hash(b)
  h = h !& hash(k.pos0) !& hash(k.nl) !& hash(k.sPh) !& hash(k.ePh) !&
      hash(k.best)
  !$h

proc buildCapDfa(n: Nfa; g: int; atStart, marked: bool): Dfa =
  ## `marked`: `u` with `#` before and `%` after group `g`'s span in PCRE's
  ## match at `u`'s start (`#` first when the span is empty); otherwise `u`
  ## whose match sets group `g`.
  var ids = initTable[CapKey, int]()
  var keys: seq[CapKey]
  proc intern(k: CapKey): int =
    if k in ids: return ids[k]
    keys.add k
    ids[k] = keys.high
    keys.high
  discard intern(CapKey(threads: @[(n.start, 0'i8)], pos0: true, best: -1))
  result.ok = true
  var i = 0
  while i < keys.len:
    if keys.len > maxDfaStates:
      result.ok = false
      return
    let k = keys[i]
    var row: array[nSyms, int32]
    for x in 0 ..< nSyms: row[x] = -1
    let justS = k.sPh == 1
    let justE = k.ePh == 1
    let save = proc (t: int8; slot: int): int8 =
      if slot == 2 * g: int8(3 * (if justS: 1 else: 2) + int(t) mod 3)
      elif slot == 2 * g + 1: int8(3 * (int(t) div 3) + (if justE: 1 else: 2))
      else: t
    let bolOk = atStart and k.pos0
    proc bestAfter(matched: bool; tag: int8): int8 =
      (if matched: tag else: k.best)
    # The end of the subject.
    var acc = false
    if nlCanEnd(k.nl):
      let (_, m, tag) = closureT(n, resolveT(k.threads, false), cxEnd, bolOk,
                                 save)
      let b = bestAfter(m, tag)
      acc =
        if marked: b == 3 * 1 + 1 and k.sPh >= 1 and k.ePh >= 1
        else: b >= 0 and int(b) mod 3 != 0
    if marked:
      if k.sPh == 0:
        var k2 = k
        k2.sPh = 1
        row[symMark] = int32 intern(k2)
      if k.sPh >= 1 and k.ePh == 0:
        var k2 = k
        k2.ePh = 1
        row[symMark2] = int32 intern(k2)
    if (k.nl and nlFinal) == 0:
      type Cl = (seq[(int, int8)], bool, int8)
      var cls: array[2, array[2, Cl]]   # [ctx is cxNll][next is LF]
      var have: array[2, array[2, bool]]
      for x in 0 ..< symMark:
        let nls = nlStep(n, k.nl, x)
        if nls < 0: continue
        let c = symByte(x)
        let ci = (if symCtx(x) == cxNll: 1 else: 0)
        let li = (if c == '\n': 1 else: 0)
        if not have[ci][li]:
          cls[ci][li] = closureT(n, resolveT(k.threads, li == 1), symCtx(x),
                                 bolOk, save)
          have[ci][li] = true
        let (cons, m, tag) = cls[ci][li]
        let nx = advanceT(n, cons, c)
        let b = bestAfter(m, tag)
        if nx.len == 0 and b < 0: continue   # no match can follow
        row[x] = int32 intern(CapKey(threads: nx, pos0: false, nl: nls,
          sPh: (if k.sPh == 1: 2'i8 else: k.sPh),
          ePh: (if k.ePh == 1: 2'i8 else: k.ePh), best: b))
    result.trans.add row
    result.accept.add acc
    inc i

proc captureLang*(n: Nfa; cacheKey: string; g: int; atStart,
                  marked: bool): SelLang =
  ## RFC-0005 S8bb. Group `g`'s capture language (see `buildCapDfa`), or
  ## `ok == false` past the size caps.
  let key = cacheKey & "|cap|" & $g & "|" & $atStart & "|" & $marked
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
  else:
    let d = buildCapDfa(n, g, atStart, marked)
    if not d.ok:
      result = SelLang(ok: false, why: "the pattern's capture automaton " &
                       "is past its size cap (" & $maxDfaStates & " states)")
    else:
      let (trans, acc) = minimize(d)
      let (fine, r) = toRegex(trans, acc)
      result =
        if fine: SelLang(ok: true, re: r)
        else: SelLang(ok: false, why: "the pattern's capture regex is " &
                      "past its size cap (" & $maxRegexSize & " nodes)")
  selCache[key] = result
