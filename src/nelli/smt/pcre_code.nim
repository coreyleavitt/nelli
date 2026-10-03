## RFC-0005 S8bt. A pattern the reader (`pcre_syntax.nim`) reads, as the
## linear code pcre_compile.c emits for it: the opcodes the engine-specific
## analyses read, in pcre_compile.c's layout.
##   * a one-character item is one opcode (`coAtom`; its `atom.op` is the
##     PCRE opcode family: OP_CHAR(I), OP_NOT(I), OP_CLASS / OP_NCLASS /
##     OP_XCLASS, a character type, OP_ANY, ...);
##   * a repeated character, negated character or type replaces the item
##     with pcre_compile.c's repeat opcodes (`coRep`: OP_STAR, OP_PLUS,
##     OP_QUERY, OP_UPTO, OP_EXACT and their MIN / POS forms; `{n,}` is
##     OP_EXACT then OP_STAR, `{n,m}` OP_EXACT (or the item for n == 1) then
##     OP_UPTO / OP_QUERY); a repeated class keeps the class and adds an
##     OP_CR* opcode (`coCrRep`); `{0}` leaves nothing;
##   * a group is OP_BRA / OP_CBRA, its alternatives separated by OP_ALT,
##     closed by OP_KET; a repeated group is replicated as pcre_compile.c
##     does (the minimum's copies, then nested OP_BRAZERO copies, or the
##     last copy closed by OP_KETRMAX / OP_KETRMIN, and OP_SBRA / OP_SCBRA
##     when a branch could match the empty string); `{0}` is OP_SKIPZERO;
##   * the whole pattern is an OP_BRA ... OP_KET, then OP_END.
## Brackets link to their next OP_ALT / OP_KET (`link`), as GET(cc, 1)
## does. Pure Nim.

import ./pcre_syntax

type
  COp* = enum
    coEnd, coSod, coCirc, coCircm, coDoll, coDollm, coEod, coEodn,
    coAtom        ## a one-character item (`atom`)
    coRep         ## a repeat opcode of a character / negated character /
                  ## type (`rep`, `count`, `atom`)
    coCrRep       ## the OP_CR* opcode after a repeated class (`rep`,
                  ## `count`, `count2`)
    coBra, coCbra, coSbra, coScbra, coAlt, coKet, coKetRmax, coKetRmin,
    coBraZero, coBraMinZero, coSkipZero,
    coAccept, coFail, coVerb

  RepOp* = enum
    rpStar, rpMinStar, rpPlus, rpMinPlus, rpQuery, rpMinQuery, rpUpto,
    rpMinUpto, rpExact, rpPosStar, rpPosPlus, rpPosQuery, rpPosUpto

  Code* = object
    op*: COp
    atom*: Rx         ## coAtom / coRep / coCrRep: the item
    rep*: RepOp       ## coRep / coCrRep
    count*: int       ## rpExact / rpUpto: the count; coCrRep: the minimum
    count2*: int      ## coCrRep: the maximum (-1 unlimited)
    link*: int        ## coBra .. coAlt: the next OP_ALT / OP_KET
    cap*: int         ## coCbra / coScbra: the group
    lazy*: bool       ## coKetRmin, coBraMinZero
    verb*: VerbKind   ## coVerb
    name*: string     ## coVerb

  AtomFam* = enum
    afChar, afNot, afType, afClass

proc fam*(x: Rx): AtomFam =
  ## The repeat family of a one-character item: OP_CHAR(I) (a literal, or a
  ## class of one character), OP_NOT(I), a character type (`\d` .. `.`,
  ## `\h` / `\v`, `\p`), or a class (OP_CLASS / OP_NCLASS / OP_XCLASS).
  case x.op
  of aoChar: afChar
  of aoNot: afNot
  of aoClass, aoNClass, aoXClass: afClass
  else: afType

proc isGroup(x: Rx): bool = x.kind in {rxCat, rxAlt}
proc groupAlts(x: Rx): seq[Rx] = (if x.kind == rxAlt: x.kids else: @[x])
proc branchItems(x: Rx): seq[Rx] = (if x.kind == rxCat: x.kids else: @[x])

proc couldBeEmpty*(x: Rx): bool
proc branchCouldBeEmpty(items: seq[Rx]): bool =
  ## pcre_compile.c's `could_be_empty_branch` over a branch's items.
  for it in items:
    case it.kind
    of rxSet, rxChars: return false
    of rxCat, rxAlt:
      if not couldBeEmpty(it): return false
    of rxRep:
      if it.lo > 0 and not (it.sub.isGroup and couldBeEmpty(it.sub)):
        return false
    of rxAccept: return true
    of rxBol, rxEol, rxEolAbs, rxVerb: discard
  true

proc couldBeEmpty*(x: Rx): bool =
  ## Whether a branch of the group `x` could match the empty string.
  for br in groupAlts(x):
    if branchCouldBeEmpty(branchItems(br)): return true
  false

type Emitter = object
  code: seq[Code]

proc emit(e: var Emitter; c: Code): int =
  e.code.add c
  e.code.high

proc emitGroup(e: var Emitter; x: Rx; s: bool)
proc emitItem(e: var Emitter; x: Rx)

proc emitAtom(e: var Emitter; x: Rx) =
  discard e.emit Code(op: coAtom, atom: x)

proc emitRepAtom(e: var Emitter; x: Rx; lo, hi: int; lazy: bool) =
  ## A repeated one-character item (pcre_compile.c's OUTPUT_SINGLE_REPEAT,
  ## or the OP_CR* opcode after a class).
  if hi == 0: return
  if fam(x) == afClass:
    e.emitAtom(x)
    var c = Code(op: coCrRep, atom: x, count: lo, count2: hi)
    c.rep =
      if lo == 0 and hi < 0: (if lazy: rpMinStar else: rpStar)
      elif lo == 1 and hi < 0: (if lazy: rpMinPlus else: rpPlus)
      elif lo == 0 and hi == 1: (if lazy: rpMinQuery else: rpQuery)
      else: (if lazy: rpMinUpto else: rpUpto)
    discard e.emit c
    return
  template rep(r, rl: RepOp; n = 0) =
    discard e.emit Code(op: coRep, atom: x, rep: (if lazy: rl else: r),
                        count: n)
  if lo == 0:
    if hi < 0: rep(rpStar, rpMinStar)
    elif hi == 1: rep(rpQuery, rpMinQuery)
    else: rep(rpUpto, rpMinUpto, hi)
  elif lo == 1:
    if hi < 0: rep(rpPlus, rpMinPlus)
    else:
      e.emitAtom(x)
      if hi > 1: rep(rpUpto, rpMinUpto, hi - 1)
  else:
    discard e.emit Code(op: coRep, atom: x, rep: rpExact, count: lo)
    if hi < 0: rep(rpStar, rpMinStar)
    elif hi != lo:
      if hi - lo == 1: rep(rpQuery, rpMinQuery)
      else: rep(rpUpto, rpMinUpto, hi - lo)

proc emitGroupRep(e: var Emitter; x: Rx) =
  ## A repeated group, replicated as pcre_compile.c does.
  let sub = x.sub
  let lo = x.lo
  var hi = x.hi
  if lo == 0:
    if hi == 0:
      discard e.emit Code(op: coSkipZero)
      e.emitGroup(sub, false)
      return
    if hi == 1 or hi < 0:
      discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                          lazy: x.lazy)
      e.emitGroup(sub, hi < 0 and couldBeEmpty(sub))
      if hi < 0:
        e.code[^1].op = (if x.lazy: coKetRmin else: coKetRmax)
        e.code[^1].lazy = x.lazy
      return
    # Nested optional copies: BRAZERO BRA [copy BRAZERO BRA [...] KET] KET.
    var opens: seq[int]
    for i in 0 ..< hi:
      discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                          lazy: x.lazy)
      if i != hi - 1:
        opens.add e.emit Code(op: coBra)
      e.emitGroup(sub, false)
    for k in countdown(opens.high, 0):
      let ket = e.emit Code(op: coKet)
      e.code[opens[k]].link = ket
      e.code[ket].link = opens[k]
    return
  for i in 0 ..< lo:
    e.emitGroup(sub, hi < 0 and i == lo - 1 and couldBeEmpty(sub))
  if hi < 0:
    e.code[^1].op = (if x.lazy: coKetRmin else: coKetRmax)
    e.code[^1].lazy = x.lazy
    return
  let extra = hi - lo
  var opens: seq[int]
  for i in 0 ..< extra:
    discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                        lazy: x.lazy)
    if i != extra - 1:
      opens.add e.emit Code(op: coBra)
    e.emitGroup(sub, false)
  for k in countdown(opens.high, 0):
    let ket = e.emit Code(op: coKet)
    e.code[opens[k]].link = ket
    e.code[ket].link = opens[k]

proc emitItem(e: var Emitter; x: Rx) =
  case x.kind
  of rxSet, rxChars: e.emitAtom(x)
  of rxCat, rxAlt: e.emitGroup(x, false)
  of rxRep:
    if x.sub.isGroup: e.emitGroupRep(x)
    else: e.emitRepAtom(x.sub, x.lo, x.hi, x.lazy)
  of rxBol:
    discard e.emit Code(op: (if x.multi: coCircm else: coCirc))
  of rxEol:
    discard e.emit Code(op: (if x.multi: coDollm else: coDoll))
  of rxEolAbs: discard e.emit Code(op: coEod)
  of rxAccept: discard e.emit Code(op: coAccept)
  of rxVerb: discard e.emit Code(op: coVerb, verb: x.verb, name: x.name)

proc emitGroup(e: var Emitter; x: Rx; s: bool) =
  ## A bracket: OP_BRA / OP_CBRA (OP_SBRA / OP_SCBRA when `s`), its
  ## alternatives separated by OP_ALT, then OP_KET.
  let op =
    if x.cap > 0: (if s: coScbra else: coCbra)
    else: (if s: coSbra else: coBra)
  var prev = e.emit Code(op: op, cap: x.cap)
  let start = prev
  let alts = groupAlts(x)
  for i, br in alts:
    if i > 0:
      let a = e.emit Code(op: coAlt)
      e.code[prev].link = a
      prev = a
    for it in branchItems(br): e.emitItem(it)
  let ket = e.emit Code(op: coKet)
  e.code[prev].link = ket
  e.code[ket].link = start

proc compileCode*(pr: PcreParse): seq[Code] =
  ## RFC-0005 S8bt. The linear code of a `psOk` reading (see the module
  ## doc): the pattern's OP_BRA .. OP_KET, then OP_END.
  var e = Emitter()
  # The top-level bracket is never a repeated one, and a reader's root
  # group carries no capture of its own.
  e.emitGroup(Rx(kind: rxAlt, kids: groupAlts(pr.root)), false)
  discard e.emit Code(op: coEnd)
  e.code
