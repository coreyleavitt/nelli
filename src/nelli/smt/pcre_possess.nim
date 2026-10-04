## RFC-0005 S8bt (item 3). pcre_compile.c's auto-possessification
## (`auto_possessify`, `compare_opcodes`, `get_chr_property_list`, PCRE
## 8.45) over the linear code of `pcre_code.nim`: which single-character
## repeats PCRE compiles possessive because what follows can never match a
## character they match. The language is the same either way; `match()`'s
## call accounting is not (a possessive repeat does not backtrack), so the
## automaton reads it when it counts the calls (`pcre_select.nim`).
##
## Character properties and extended classes (`\p`, OP_XCLASS) are not
## ported: a comparison that reads one leaves `unknown` set (the caller
## declines).
##
## Pure Nim.

import std/sets
import ./pcre_syntax
import ./pcre_code
import ./pcre_ucd

type
  PKind = enum
    pkChar, pkNot, pkClass, pkNClass, pkXClass,
    pkNotDigit, pkDigit, pkNotSpace, pkSpace, pkNotWord, pkWord,
    pkAny, pkAllAny, pkNotHSpace, pkHSpace, pkNotVSpace, pkVSpace,
    pkEodn, pkEod, pkDoll, pkDollM, pkProp

  PList = object
    kind: PKind
    empty: bool        ## list[1]: the item can match nothing (a base
                       ## repeat: it is greedy)
    chars: seq[int32]  ## pkChar / pkNot: the character, its other case
    bits: set[char]    ## pkClass / pkNClass: the bitmap

  Possess* = object
    addrs*: HashSet[int]   ## the possessive repeats (`Code.address`)
    unknown*: bool         ## a comparison read an unported item

const
  digitBits = {'0'..'9'}
  spaceBits = {'\t', '\n', '\v', '\f', '\r', ' '}
  wordBits = {'0'..'9', 'a'..'z', 'A'..'Z', '_'}

# The autoposstab rows (\D .. \X) and columns (\D .. $M) of pcre_compile.c,
# indexed by the PKind column of each opcode (-1: not in the table).
const autoposstab: array[17, array[21, uint8]] = [
  [0'u8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # \D
  [1'u8, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],  # \d
  [0'u8, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],  # \S
  [0'u8, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # \s
  [0'u8, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # \W
  [0'u8, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],  # \w
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # .
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # .+
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],  # \C
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # \P
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],  # \p
  [0'u8, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0],  # \R
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0],  # \H
  [0'u8, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0],  # \h
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0],  # \V
  [0'u8, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0],  # \v
  [0'u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]  # \X

proc column(k: PKind): int =
  case k
  of pkNotDigit: 0
  of pkDigit: 1
  of pkNotSpace: 2
  of pkSpace: 3
  of pkNotWord: 4
  of pkWord: 5
  of pkAny: 6
  of pkAllAny: 7
  of pkNotHSpace: 12
  of pkHSpace: 13
  of pkNotVSpace: 14
  of pkVSpace: 15
  of pkEodn: 17
  of pkEod: 18
  of pkDoll: 19
  of pkDollM: 20
  else: -1

proc otherCase(c: int32): int32 =
  ## pcre_chartables.c's `fcc` (the default tables): ASCII letters.
  if c >= int32(ord('a')) and c <= int32(ord('z')): c - 32
  elif c >= int32(ord('A')) and c <= int32(ord('Z')): c + 32
  else: c

proc classBits(x: Rx): set[char] =
  ## The bitmap of a class: its characters below 256.
  if x.kind == rxSet: return x.bytes
  for (lo, hi) in x.cps:
    for c in max(lo, 0) .. min(hi, 255): result.incl char(c)

proc anyKind(x: Rx; utf: bool): PKind =
  ## `.` / `\N` (OP_ANY) or a dot-all `.` (OP_ALLANY).
  if x.kind == rxSet: return (if x.bytes.card == 256: pkAllAny else: pkAny)
  var all = false
  for (lo, hi) in x.cps:
    if lo <= 0 and hi >= 0x10FFFF: all = true
  (if all: pkAllAny else: pkAny)

proc typeKind(x: Rx): PKind =
  let s = classBits(x)
  let pos = (if x.negType: {'\x00'..'\xFF'} - s else: s)
  if '0' in pos and 'a' notin pos: (if x.negType: pkNotDigit else: pkDigit)
  elif ' ' in pos: (if x.negType: pkNotSpace else: pkSpace)
  else: (if x.negType: pkNotWord else: pkWord)

proc atomList(x: Rx; utf: bool; l: var PList): bool =
  ## The item's property list (false: an item `get_chr_property_list`
  ## does not accept).
  # RFC-0005 S8bt: a caseless character's other case is `fcc`'s below 128
  # (below 256 without UTF), else UCD_OTHERCASE.
  let oc = (if x.ch < 128 or not utf: otherCase(x.ch) else: ucdOther(x.ch))
  case x.op
  of aoChar:
    l.kind = pkChar
    l.chars = @[x.ch]
    if x.ci and oc != x.ch: l.chars.add oc
  of aoNot:
    l.kind = pkNot
    l.chars = @[x.ch]
    if x.ci and oc != x.ch: l.chars.add oc
  of aoClass:
    l.kind = pkClass
    l.bits = classBits(x)
  of aoNClass:
    l.kind = pkNClass
    l.bits = classBits(x)
  of aoXClass: l.kind = pkXClass
  of aoType: l.kind = typeKind(x)
  of aoHSpace: l.kind = pkHSpace
  of aoVSpace: l.kind = pkVSpace
  of aoNotSpace:
    # `\H` leaves out the space, `\V` the LF.
    l.kind = (if ' ' notin classBits(x): pkNotHSpace else: pkNotVSpace)
  of aoAny: l.kind = anyKind(x, utf)
  of aoProp:
    if x.clist:
      # RFC-0005 S8bt: PT_CLIST becomes its caseless set's characters.
      l.kind = (if x.clistNot: pkNot else: pkChar)
      l.chars = ucdCaseSets[ucdCaseSet(x.ch)]
    else: l.kind = pkProp
  of aoFail: return false
  true

proc propertyList(code: seq[Code]; i: int; utf: bool; l: var PList): int =
  ## `get_chr_property_list` at `code[i]`: the index after the item, -1
  ## when it is not accepted.
  let c = code[i]
  l = PList()
  case c.op
  of coDoll:
    l.kind = pkDoll
    return i + 1
  of coDollm:
    l.kind = pkDollM
    return i + 1
  of coEod:
    l.kind = pkEod
    return i + 1
  of coEodn:
    l.kind = pkEodn
    return i + 1
  of coAtom:
    if not atomList(c.atom, utf, l): return -1
    if fam(c.atom) == afClass and i + 1 < code.len and
       code[i + 1].op == coCrRep:
      let r = code[i + 1]
      l.empty = r.rep in {rpStar, rpMinStar, rpPosStar, rpQuery, rpMinQuery,
                          rpPosQuery} or
                (r.rep in {rpUpto, rpMinUpto, rpPosUpto} and r.count == 0)
      return i + 2
    return i + 1
  of coRep:
    if not atomList(c.atom, utf, l): return -1
    l.empty = c.rep notin {rpPlus, rpMinPlus, rpExact, rpPosPlus}
    return i + 1
  else:
    return -1

proc compareOpcodes(code: seq[Code]; i0: int; utf: bool; base: PList;
                    recLimit: var int; p: var Possess): bool =
  ## `compare_opcodes`: true when nothing from `code[i0]` on can match a
  ## character the base repeat matches (it can then be possessive).
  if recLimit == 0: return false
  dec recLimit
  var i = i0
  var enteredGroup = false
  while true:
    var c = code[i].op
    if c == coAlt:
      while code[i].op == coAlt: i = code[i].link
      c = code[i].op
    case c
    of coEnd:
      return base.empty
    of coKet:
      if not base.empty: return false
      inc i
      continue
    of coBra, coCbra:
      var nextCode = code[i].link
      inc i
      while code[nextCode].op == coAlt:
        if not compareOpcodes(code, i, utf, base, recLimit, p): return false
        i = nextCode + 1
        nextCode = code[nextCode].link
      enteredGroup = true
      continue
    of coBraZero, coBraMinZero:
      var nx = i + 1
      if code[nx].op notin {coBra, coCbra}: return false
      nx = code[nx].link
      while code[nx].op == coAlt: nx = code[nx].link
      nx += 1
      if not compareOpcodes(code, nx, utf, base, recLimit, p): return false
      inc i
      continue
    else: discard
    var list: PList
    let after = propertyList(code, i, utf, list)
    if after < 0: return false
    i = after
    if base.kind in {pkProp, pkXClass} or list.kind in {pkProp, pkXClass}:
      p.unknown = true
      return false
    var chrSide, other: PList
    var charCase = true
    if base.kind == pkChar:
      chrSide = base
      other = list
    elif list.kind == pkChar:
      chrSide = list
      other = base
    elif base.kind == pkClass or list.kind == pkClass or
         (not utf and (base.kind == pkNClass or list.kind == pkNClass)):
      charCase = false
      let baseIsSet = base.kind == pkClass or
                      (not utf and base.kind == pkNClass)
      let set1 = (if baseIsSet: base.bits else: list.bits)
      let o = (if baseIsSet: list else: base)
      var set2: set[char]
      var invert = false
      case o.kind
      of pkClass, pkNClass: set2 = o.bits
      of pkNotDigit:
        invert = true
        set2 = digitBits
      of pkDigit: set2 = digitBits
      of pkNotSpace:
        invert = true
        set2 = spaceBits
      of pkSpace: set2 = spaceBits
      of pkNotWord:
        invert = true
        set2 = wordBits
      of pkWord: set2 = wordBits
      else: return false
      if invert:
        if (set1 - set2).card != 0: return false
      else:
        if (set1 * set2).card != 0: return false
      if not list.empty: return true
      continue
    else:
      charCase = false
      let l = column(base.kind)
      let r = column(list.kind)
      if l < 0 or l > 16 or r < 0 or autoposstab[l][r] == 0: return false
      if not list.empty: return true
      continue
    if charCase:
      for chr in chrSide.chars:
        case other.kind
        of pkChar:
          for o in other.chars:
            if chr == o: return false
        of pkNot:
          if chr notin other.chars: return false
        of pkDigit:
          if chr < 256 and char(chr) in digitBits: return false
        of pkNotDigit:
          if chr > 255 or char(chr) notin digitBits: return false
        of pkSpace:
          if chr < 256 and char(chr) in spaceBits: return false
        of pkNotSpace:
          if chr > 255 or char(chr) notin spaceBits: return false
        of pkWord:
          if chr < 255 and char(chr) in wordBits: return false
        of pkNotWord:
          if chr > 255 or char(chr) notin wordBits: return false
        of pkHSpace:
          if chr in [9'i32, 0x20, 0xa0, 0x1680, 0x180e, 0x2000, 0x2001,
                     0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007, 0x2008,
                     0x2009, 0x200A, 0x202f, 0x205f, 0x3000]: return false
        of pkNotHSpace:
          if chr notin [9'i32, 0x20, 0xa0, 0x1680, 0x180e, 0x2000, 0x2001,
                        0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007,
                        0x2008, 0x2009, 0x200A, 0x202f, 0x205f, 0x3000]:
            return false
        of pkVSpace:
          if chr in [10'i32, 11, 12, 13, 0x85, 0x2028, 0x2029]: return false
        of pkNotVSpace:
          if chr notin [10'i32, 11, 12, 13, 0x85, 0x2028, 0x2029]:
            return false
        of pkDoll, pkEodn:
          if chr in [13'i32, 10, 11, 12, 0x85, 0x2028, 0x2029]: return false
        of pkEod: discard
        of pkNClass:
          if chr > 255: return false
          if char(chr) in other.bits: return false
        of pkClass:
          if chr <= 255 and char(chr) in other.bits: return false
        else: return false
      if not list.empty: return true

proc autoPossess*(code: seq[Code]; utf: bool): Possess =
  ## RFC-0005 S8bt. `auto_possessify` over `code`: the addresses of the
  ## repeats pcre_compile.c makes possessive.
  for i, c in code:
    var base: PList
    var cand = false
    var after = -1
    if c.op == coRep and c.rep in {rpStar, rpMinStar, rpPlus, rpMinPlus,
                                   rpQuery, rpMinQuery, rpUpto, rpMinUpto}:
      after = propertyList(code, i, utf, base)
      base.empty = c.rep in {rpStar, rpPlus, rpQuery, rpUpto}
      cand = after >= 0
    elif c.op == coAtom and fam(c.atom) == afClass and i + 1 < code.len and
         code[i + 1].op == coCrRep and
         code[i + 1].rep notin {rpPosStar, rpPosPlus, rpPosQuery,
                                rpPosUpto}:
      after = propertyList(code, i, utf, base)
      base.empty = code[i + 1].rep in {rpStar, rpPlus, rpQuery, rpUpto}
      cand = after >= 0
    if not cand: continue
    if base.kind in {pkProp, pkXClass}:
      result.unknown = true
      continue
    var recLimit = 1000
    if compareOpcodes(code, after, utf, base, recLimit, result):
      result.addrs.incl c.address
