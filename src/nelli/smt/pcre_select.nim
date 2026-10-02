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
## `\Z` at the end or before a final `\n`, `\z` at the end. A final `\n` is
## its own input symbol (`symNll`) so the automaton sees it; it is the byte
## `\n` in the language.
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
    out1, out2: int
    loop: int
    slot: int

  Nfa* = object
    states: seq[NState]
    start*: int
    loops: int
    groups*: int     ## capturing groups
    hasBol*: bool    ## a `^` / `\A` anywhere: `atStart` matters
    ok*: bool
    why*: string

const
  maxNfaStates = 4000
  maxLoops = 63
  maxDfaStates* = 4000
  maxRegexSize* = 40000
  symNll = 256       ## a final `\n`
  symMark = 257      ## the marker `#`
  nSyms = 258

type Build = object
  n: Nfa
  overflow: bool

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
    e = b.add NState(kind: nkByte, bytes: x.bytes, out1: inner)
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

proc buildNfa*(root: Rx; groups = 0): Nfa =
  ## RFC-0005 S8bb. The priority NFA of a `psOk` tree; `ok == false` past
  ## the size caps (`why` says which).
  var b = Build()
  b.n.groups = groups
  let m = b.add NState(kind: nkMatch)
  b.n.start = b.comp(root, m)
  result = b.n
  result.ok = not b.overflow
  if b.overflow:
    result.why = "the pattern's priority automaton is past its size cap (" &
                 $maxNfaStates & " states, " & $maxLoops & " nullable loops)"

# ---- the Pike step -------------------------------------------------------------

type
  Ctx* = enum
    cxOther   ## the next symbol is a byte that is not a final `\n`
    cxNll     ## the next symbol is a final `\n`
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
      let t = n.states[s].out1
      if t notin seen:
        seen.incl t
        result.add t

proc ctxAt(u: string; j: int): Ctx =
  if j >= u.len: cxEnd
  elif j == u.len - 1 and u[j] == '\n': cxNll
  else: cxOther

proc chosenEnd*(n: Nfa; u: string; atStart: bool; noEmpty = false): int =
  ## RFC-0005 S8bb. The concrete run: the end offset in `u` of PCRE's match
  ## at the start of `u`, or -1. `atStart`: `u` starts at subject position
  ## 0. `noEmpty`: NOTEMPTY_ATSTART (an empty match is not one).
  result = -1
  var threads = @[n.start]
  for j in 0 .. u.len:
    let cl = closure(n, threads, ctxAt(u, j), atStart and j == 0,
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
    nl: int       ## 1: a non-final `\n` was read (another byte must
                  ## follow); 2: a final `\n` was read (only `#` may follow)

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
    if k.nl != 1:
      let cl = closure(n, k.threads, cxEnd, bolOk, ne)
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
    # A byte, or a final `\n`.
    if k.nl != 2:
      var clOther, clNll: Closure
      clOther = closure(n, k.threads, cxOther, bolOk, ne)
      clNll = closure(n, k.threads, cxNll, bolOk, ne)
      for s in 0 .. symNll:
        let cl = (if s == symNll: clNll else: clOther)
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
        let c = (if s == symNll: '\n' else: char(s))
        let nx = advance(n, cl.consumers, c)
        let nl = (if s == symNll: 2 elif c == '\n': 1 else: 0)
        row[s] = int32 intern(DKey(threads: nx, pos0: false, phase: phase,
                                   nl: nl))
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
  RKind* = enum rkEmpty, rkEps, rkSet, rkMark, rkCat, rkAlt, rkStar
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
      if sym == symMark:
        edges[s][t] = (if t in edges[s]: rAlt(edges[s][t], mk(rkMark))
                       else: mk(rkMark))
      else:
        let c = (if sym == symNll: '\n' else: char(sym))
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
    if k.nl != 1:
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
    if k.nl != 2 and not (starts and here < 0):
      for s in 0 .. symNll:
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
        let nl = (if s == symNll: 2'i8 elif s == 10: 1'i8 else: 0'i8)
        row[s] = int32 intern(SKey(pending: nx, run: run, phase: k.phase,
                                   nl: nl, pos0: false, mark: k.mark))
    result.trans.add row
    result.accept.add acc
    inc i

proc searchLang*(n: Nfa; cacheKey: string; kind: SearchKind;
                 atStart: bool): SelLang =
  ## RFC-0005 S8bb. The occurrence-search language `kind` of `n` (see
  ## above), or `ok == false` past the size caps.
  let key = cacheKey & "|search|" & $kind & "|" & $atStart
  if key in selCache: return selCache[key]
  if not n.ok:
    result = SelLang(ok: false, why: n.why)
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
