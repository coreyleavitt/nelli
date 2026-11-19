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

import std/tables
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
    count*: int       ## rpExact / rpUpto: the count; coCrRep: the minimum;
                      ## coAccept: the capturing groups it closes (OP_CLOSE)
    count2*: int      ## coCrRep: the maximum (-1 unlimited)
    link*: int        ## coBra .. coAlt: the next OP_ALT / OP_KET
    cap*: int         ## coCbra / coScbra: the group
    lazy*: bool       ## coKetRmin, coBraMinZero
    verb*: VerbKind   ## coVerb
    name*: string     ## coVerb
    address*: int
      ## RFC-0005 S8bt: coRep / coCrRep and a repeated class's coAtom: the
      ## repeat's code address in `codeSize`'s layout (`pcre_select`'s
      ## automaton reads the same address for that repeat). RFC-0016 S8co:
      ## coBraZero / coBraMinZero: the repeat's address on the outermost
      ## copy of a group repeat, -1 on a nested one

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

proc isGroup*(x: Rx): bool = x.kind in {rxCat, rxAlt}
proc groupAlts*(x: Rx): seq[Rx] = (if x.kind == rxAlt: x.kids else: @[x])
proc branchItems*(x: Rx): seq[Rx] = (if x.kind == rxCat: x.kids else: @[x])

proc codeSize*(x: Rx): int
proc branchSize*(br: Rx): int =
  for it in branchItems(br): result = satAdd(result, codeSize(it))

proc codeSize*(x: Rx): int =
  ## RFC-0005 S8bj. Code units in pcre_compile.c's layout, as addresses:
  ## only the order matters (THEN's catch test compares addresses;
  ## RFC-0005 S8bt: a repeat's address names it, `Code.address`).
  ## RFC-0005 R1-22: saturating (a reading the reader accepts is within
  ## PCRE's 65536 code units, which bound this count, but no caller may
  ## overflow on another tree).
  case x.kind
  of rxCat, rxAlt:
    result = 1
    for br in groupAlts(x): result = satAdd(result, satAdd(branchSize(br), 1))
  of rxRep:
    if x.sub.isGroup:
      let copies = (if x.hi == 0: 1 elif x.hi < 0: max(x.lo, 1) else: x.hi)
      result = satAdd(1, satMul(copies, codeSize(x.sub)))
    else:
      result = 1
  else:
    result = 1

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

proc emitGroup(e: var Emitter; x: Rx; s: bool; base: int)
proc emitItem(e: var Emitter; x: Rx; base: int)

proc emitAtom(e: var Emitter; x: Rx; address = -1) =
  discard e.emit Code(op: coAtom, atom: x, address: address)

proc emitRepAtom(e: var Emitter; x: Rx; lo, hi: int; lazy: bool;
                 address: int) =
  ## A repeated one-character item (pcre_compile.c's OUTPUT_SINGLE_REPEAT,
  ## or the OP_CR* opcode after a class).
  if hi == 0: return
  if fam(x) == afClass:
    e.emitAtom(x, address)
    var c = Code(op: coCrRep, atom: x, count: lo, count2: hi,
                 address: address)
    c.rep =
      if lo == 0 and hi < 0: (if lazy: rpMinStar else: rpStar)
      elif lo == 1 and hi < 0: (if lazy: rpMinPlus else: rpPlus)
      elif lo == 0 and hi == 1: (if lazy: rpMinQuery else: rpQuery)
      else: (if lazy: rpMinUpto else: rpUpto)
    discard e.emit c
    return
  template rep(r, rl: RepOp; n = 0) =
    discard e.emit Code(op: coRep, atom: x, rep: (if lazy: rl else: r),
                        count: n, address: address)
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
    discard e.emit Code(op: coRep, atom: x, rep: rpExact, count: lo,
                        address: address)
    if hi < 0: rep(rpStar, rpMinStar)
    elif hi != lo:
      if hi - lo == 1: rep(rpQuery, rpMinQuery)
      else: rep(rpUpto, rpMinUpto, hi - lo)

proc emitGroupRep(e: var Emitter; x: Rx; base: int) =
  ## A repeated group, replicated as pcre_compile.c does.
  let sub = x.sub
  let lo = x.lo
  var hi = x.hi
  let sz = codeSize(sub)
  let b0 = base + 1
  if lo == 0:
    if hi == 0:
      discard e.emit Code(op: coSkipZero)
      e.emitGroup(sub, false, b0)
      return
    if hi == 1 or hi < 0:
      discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                          lazy: x.lazy, address: base)
      e.emitGroup(sub, hi < 0 and couldBeEmpty(sub), b0)
      if hi < 0:
        e.code[^1].op = (if x.lazy: coKetRmin else: coKetRmax)
        e.code[^1].lazy = x.lazy
      return
    # Nested optional copies: BRAZERO BRA [copy BRAZERO BRA [...] KET] KET.
    var opens: seq[int]
    for i in 0 ..< hi:
      discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                          lazy: x.lazy, address: (if i == 0: base else: -1))
      if i != hi - 1:
        opens.add e.emit Code(op: coBra)
      e.emitGroup(sub, false, b0 + i * sz)
    for k in countdown(opens.high, 0):
      let ket = e.emit Code(op: coKet)
      e.code[opens[k]].link = ket
      e.code[ket].link = opens[k]
    return
  for i in 0 ..< lo:
    e.emitGroup(sub, hi < 0 and i == lo - 1 and couldBeEmpty(sub),
                b0 + i * sz)
  if hi < 0:
    e.code[^1].op = (if x.lazy: coKetRmin else: coKetRmax)
    e.code[^1].lazy = x.lazy
    return
  let extra = hi - lo
  var opens: seq[int]
  for i in 0 ..< extra:
    discard e.emit Code(op: (if x.lazy: coBraMinZero else: coBraZero),
                        lazy: x.lazy, address: (if i == 0: base else: -1))
    if i != extra - 1:
      opens.add e.emit Code(op: coBra)
    e.emitGroup(sub, false, b0 + (lo + i) * sz)
  for k in countdown(opens.high, 0):
    let ket = e.emit Code(op: coKet)
    e.code[opens[k]].link = ket
    e.code[ket].link = opens[k]

proc emitItem(e: var Emitter; x: Rx; base: int) =
  case x.kind
  of rxSet, rxChars: e.emitAtom(x)
  of rxCat, rxAlt: e.emitGroup(x, false, base)
  of rxRep:
    if x.sub.isGroup: e.emitGroupRep(x, base)
    else: e.emitRepAtom(x.sub, x.lo, x.hi, x.lazy, base)
  of rxBol:
    discard e.emit Code(op: (if x.multi: coCircm else: coCirc))
  of rxEol:
    discard e.emit Code(op: (if x.multi: coDollm else: coDoll))
  of rxEolAbs: discard e.emit Code(op: coEod)
  of rxAccept: discard e.emit Code(op: coAccept, count: x.open.len)
  of rxVerb: discard e.emit Code(op: coVerb, verb: x.verb, name: x.name)

proc emitGroup(e: var Emitter; x: Rx; s: bool; base: int) =
  ## A bracket: OP_BRA / OP_CBRA (OP_SBRA / OP_SCBRA when `s`), its
  ## alternatives separated by OP_ALT, then OP_KET.
  let op =
    if x.cap > 0: (if s: coScbra else: coCbra)
    else: (if s: coSbra else: coBra)
  var prev = e.emit Code(op: op, cap: x.cap)
  let start = prev
  let alts = groupAlts(x)
  var a0 = base + 1
  for i, br in alts:
    if i > 0:
      let a = e.emit Code(op: coAlt)
      e.code[prev].link = a
      prev = a
    var ab = a0
    for it in branchItems(br):
      e.emitItem(it, ab)
      ab += codeSize(it)
    a0 += branchSize(br) + 1
  let ket = e.emit Code(op: coKet)
  e.code[prev].link = ket
  e.code[ket].link = start

proc compileCode*(pr: PcreParse): seq[Code] =
  ## RFC-0005 S8bt. The linear code of a `psOk` reading (see the module
  ## doc): the pattern's OP_BRA .. OP_KET, then OP_END.
  var e = Emitter()
  # The top-level bracket is never a repeated one, and a reader's root
  # group carries no capture of its own.
  e.emitGroup(Rx(kind: rxAlt, kids: groupAlts(pr.root)), false, 0)
  discard e.emit Code(op: coEnd)
  e.code

const opAssertbackNot = 128
  ## 8.37's OP_ASSERTBACK_NOT (pcre_internal.h's opcode table)

proc unitBound(c: Code; utf: bool): int =
  ## RFC-0016 S8co. An upper bound on the code units pcre_compile.c emits for
  ## `c` (8-bit library, LINK_SIZE 2); -1 when no bound is read (OP_XCLASS).
  let chLen = (if utf: 6 else: 1)
  case c.op
  of coAtom:
    case c.atom.op
    of aoChar, aoNot: 1 + chLen
    of aoProp: 3
    of aoClass, aoNClass: 33
    of aoXClass: -1
    else: 1
  of coRep:
    if c.atom.op == aoXClass: -1 else: 3 + max(chLen, 3)
  of coCrRep: 5
  of coBra, coSbra, coAlt, coKet, coKetRmax, coKetRmin: 3
  of coCbra, coScbra: 5
  of coAccept: 1 + 3 * c.count
  of coVerb:
    if c.verb in {vbMark, vbSkipName}: 3 + c.name.len else: 1
  else: 1

proc spanBound(code: seq[Code]; a, b: int; utf: bool): int =
  ## The code units of `code[a ..< b]`, bounded; -1 when unbounded.
  for i in a ..< b:
    let u = unitBound(code[i], utf)
    if u < 0: return -1
    result += u

proc highOpcode(c: Code): bool =
  ## Whether the opcode `c` starts with is past OP_ASSERTBACK_NOT: a bracket,
  ## a zero bracket, OP_ACCEPT / OP_CLOSE, OP_FAIL or a verb.
  case c.op
  of coBra, coCbra, coSbra, coScbra, coBraZero, coBraMinZero, coSkipZero,
     coAccept, coFail, coVerb: true
  of coAtom: c.atom.op == aoFail
  else: false

proc unitPast(code: seq[Code]; x: int; utf: bool): int =
  ## RFC-0016 S8co. Whether the code unit after the opcode at `x` (`cc[1]`)
  ## is past OP_ASSERTBACK_NOT: 1 yes, 0 no, -1 not read.
  proc chUnit(ch: int32): int =
    if utf and ch >= 0x80: 1   # a UTF-8 lead unit, 0xC2 or more
    elif ch > opAssertbackNot: 1
    else: 0
  proc linkHigh(span: int): int =
    # GET(cc, 1)'s high unit: past OP_ASSERTBACK_NOT from 129 * 256 on.
    if span < 0 or span >= (opAssertbackNot + 1) * 256: -1 else: 0
  proc opAfter(): int =
    if x + 1 < code.len and highOpcode(code[x + 1]): 1 else: 0
  let c = code[x]
  case c.op
  of coEnd: -1
  of coAtom:
    case c.atom.op
    of aoChar, aoNot: chUnit(c.atom.ch)
    of aoProp: 0                        # the property's type
    of aoClass, aoNClass, aoXClass: -1  # a bitmap's or the data's first unit
    of aoFail: opAfter()
    else: opAfter()                     # an operand-less type
  of coRep:
    if c.rep in {rpExact, rpUpto, rpMinUpto, rpPosUpto}:
      (if c.count >= (opAssertbackNot + 1) * 256: 1 else: 0)
    elif fam(c.atom) in {afChar, afNot}: chUnit(c.atom.ch)
    else: 0                             # the type's opcode, or OP_PROP / OP_NOTPROP
  of coCrRep:
    if c.rep in {rpUpto, rpMinUpto}:
      (if c.count >= (opAssertbackNot + 1) * 256: 1 else: 0)
    else: opAfter()
  of coSod, coCirc, coCircm, coDoll, coDollm, coEod, coEodn, coBraZero,
     coBraMinZero, coSkipZero, coFail:
    opAfter()
  of coAccept:
    if c.count > 0: 0 else: opAfter()   # OP_CLOSE's group number
  of coVerb:
    if c.verb in {vbMark, vbSkipName}:
      (if c.name.len > opAssertbackNot: 1 else: 0)
    else: opAfter()
  of coBra, coCbra, coSbra, coScbra, coAlt:
    linkHigh(spanBound(code, x, c.link, utf))
  of coKet, coKetRmax, coKetRmin:
    linkHigh(spanBound(code, c.link, x, utf))

proc braMinZeroCounts*(code: seq[Code]; utf: bool): Table[int, int] =
  ## RFC-0016 S8co (PRC-33 item 4a). 8.37's JIT's OP_BRAMINZERO runs a
  ## `count_match` at the label where the rest after its group is tried
  ## (first, and after each iteration of the group) only when `cc[1]` is
  ## past OP_ASSERTBACK_NOT, and `cc` has by then moved past the group
  ## (pcre_jit_compile.c's compile_matchingpath, `bracketend`): the unit
  ## read is the one after the opcode that follows the group. Per group
  ## repeat (its address, on its outermost OP_BRAMINZERO): 1 it counts, 0 it
  ## does not, -1 the unit is not read. A nested copy's group is followed by
  ## its wrapper's OP_KET (a link's high unit).
  for i, c in code:
    if c.op != coBraMinZero or c.address < 0: continue
    var k = code[i + 1].link
    while code[k].op == coAlt: k = code[k].link
    result[c.address] = unitPast(code, k + 1, utf)
