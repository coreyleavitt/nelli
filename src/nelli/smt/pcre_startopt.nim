## RFC-0005 S8bj. PCRE 8.45's start-of-match optimisation data for a
## pattern the reader (`pcre_syntax.nim`) reads, computed from its tree the
## way pcre_compile.c and pcre_study.c compute it from the compiled code:
##   * `anchored` (`is_anchored`): every top-level alternative starts with
##     `^` / `\A`, or `.*` under `(?s)` in a pattern without `(*PRUNE)` /
##     `(*SKIP)`;
##   * the first character (`compile_branch` / `compile_regex`'s firstchar
##     bookkeeping, a first byte in UTF mode) and the required character
##     (reqchar, kept for an anchored pattern only after a variable-length
##     item, and dropped after `(*ACCEPT)`);
##   * `startline` (`is_startline`): every alternative starts with `^` /
##     `(?m)^`, or `.*` without `(?s)` in a pattern without `(*PRUNE)` /
##     `(*SKIP)`;
##   * the start bits (`set_start_bits`), only when there is neither an
##     anchor nor a first character nor a line start;
##   * the minimum length (`find_minlength`; none after `(*ACCEPT)`).
##
## `pcre_exec` (the search loop, `pcre_select.nim`) reads them: an unanchored
## call moves its start to the first character / past a newline / to a byte
## of the start bits before each attempt, and with the minimum length and
## the required character stops searching early. The values are pinned
## against `pcre.fullinfo` (`tests/tsymex_rfc0005_s8bj_startopt.nim`).
##
## Pure Nim: the walker reads it at walk time, with no libpcre.

import ./pcre_syntax

type
  StartOpt* = object
    anchored*: bool        ## PCRE_ANCHORED from `is_anchored`
    firstChar*: int        ## the first byte, -1 when none
    firstCaseless*: bool   ## its other case matches too
    startline*: bool       ## PCRE_STARTLINE
    hasBits*: bool         ## study found start bits
    bits*: set[char]
    minLength*: int        ## study's minimum length, -1 when none
    reqChar*: int          ## the required byte, -1 when none
    reqCaseless*: bool

const
  reqUnset = -2'i32
  reqNone = -1'i32
  reqCaselessBit = 1'i32
  reqVaryBit = 2'i32

type
  Fc = object
    ## A branch's or group's first and required character (pcre_compile.c's
    ## firstchar / reqchar and their flags: REQ_UNSET, REQ_NONE, or
    ## REQ_CASELESS | REQ_VARY bits).
    fc, rc: uint32
    fcf, rcf: int32

  Comp = object
    utf: bool
    reqVaryOpt: int32    ## cd->req_varyopt
    hadAccept: bool      ## cd->had_accept

proc branchItems(x: Rx): seq[Rx] =
  ## A branch's items: a concatenation's kids, or the item itself.
  if x.kind == rxCat: x.kids else: @[x]

proc groupAlts(x: Rx): seq[Rx] =
  ## A group's alternatives.
  if x.kind == rxAlt: x.kids else: @[x]

proc isGroup(x: Rx): bool = x.kind in {rxCat, rxAlt}

proc charBytes(c: Comp; ch: int32): string =
  (if c.utf: utf8Encode(ch) else: $char(ch))

proc compileRegex(c: var Comp; alts: seq[Rx]): Fc

type Br = object
  ## `compile_branch`'s running values.
  fc, rc, zfc, zrc: uint32
  fcf, rcf, zfcf, zrcf: int32
  groupSet: bool       ## groupsetfirstchar

proc oneChar(c: Comp; b: var Br; ch: int32; ci: bool) =
  ## ONE_CHAR: a literal (OP_CHAR / OP_CHARI).
  let bs = c.charBytes(ch)
  let caseopt = (if ci: reqCaselessBit else: 0'i32)
  if b.fcf == reqUnset:
    b.zfcf = reqNone
    b.zrc = b.rc
    b.zrcf = b.rcf
    if bs.len == 1 or caseopt == 0:
      b.fc = uint32(ord(bs[0]))
      b.fcf = caseopt
      if bs.len != 1:
        b.rc = uint32(ord(bs[^1]))
        b.rcf = c.reqVaryOpt
    else:
      b.fcf = reqNone
      b.rcf = reqNone
  else:
    b.zfc = b.fc
    b.zfcf = b.fcf
    b.zrc = b.rc
    b.zrcf = b.rcf
    if bs.len == 1 or caseopt == 0:
      b.rc = uint32(ord(bs[^1]))
      b.rcf = caseopt or c.reqVaryOpt

proc noFirst(b: var Br) =
  ## `.`, a class, an escape class: no first character from here on.
  if b.fcf == reqUnset: b.fcf = reqNone
  b.zfc = b.fc
  b.zfcf = b.fcf
  b.zrc = b.rc
  b.zrcf = b.rcf

proc group(c: var Comp; b: var Br; x: Rx) =
  ## A bracket: its subpattern's values (the `(` case's tail).
  let tempReqVary = c.reqVaryOpt
  var sub = c.compileRegex(groupAlts(x))
  b.zrc = b.rc
  b.zrcf = b.rcf
  b.zfc = b.fc
  b.zfcf = b.fcf
  b.groupSet = false
  if b.fcf == reqUnset:
    if sub.fcf >= 0:
      b.fc = sub.fc
      b.fcf = sub.fcf
      b.groupSet = true
    else:
      b.fcf = reqNone
    b.zfcf = reqNone
  elif sub.fcf >= 0 and sub.rcf < 0:
    sub.rc = sub.fc
    sub.rcf = sub.fcf or tempReqVary
  if sub.rcf >= 0:
    b.rc = sub.rc
    b.rcf = sub.rcf

proc item(c: var Comp; b: var Br; x: Rx) =
  case x.kind
  of rxSet, rxChars:
    case x.op
    of aoChar: c.oneChar(b, x.ch, x.ci)
    of aoFail: discard   # OP_FAIL sets nothing
    of aoProp:
      if x.clist and not x.clistNot:
        # RFC-0005 S8bt: ONE_CHAR's OP_PROP PT_CLIST: no first character
        # from here on, and nothing else changes.
        if b.fcf == reqUnset:
          b.fcf = reqNone
          b.zfcf = reqNone
      else: b.noFirst()
    else: b.noFirst()
  of rxCat, rxAlt: c.group(b, x)
  of rxRep:
    c.item(b, x.sub)
    # REPEAT
    if x.lo == 0:
      b.fc = b.zfc
      b.fcf = b.zfcf
      b.rc = b.zrc
      b.rcf = b.zrcf
    let reqVary = (if x.lo == x.hi: 0'i32 else: reqVaryBit)
    let s = x.sub
    if s.kind in {rxSet, rxChars} and s.op == aoChar:
      if x.lo > 1 and c.charBytes(s.ch).len == 1:
        b.rc = uint32(ord(c.charBytes(s.ch)[0]))
        b.rcf = (if s.ci: reqCaselessBit else: 0'i32) or c.reqVaryOpt
    elif s.isGroup and x.lo > 1:
      if b.groupSet and b.rcf < 0:
        b.rc = b.fc
        b.rcf = b.fcf
    c.reqVaryOpt = c.reqVaryOpt or reqVary
  of rxBol:
    if x.multi and b.fcf == reqUnset:
      b.zfcf = reqNone
      b.fcf = reqNone
  of rxEol, rxEolAbs, rxVerb: discard
  of rxAccept:
    c.hadAccept = true
    if b.fcf == reqUnset: b.fcf = reqNone

proc compileBranch(c: var Comp; items: seq[Rx]): Fc =
  ## `compile_branch`'s firstchar / reqchar updates, item by item.
  var b = Br(fcf: reqUnset, rcf: reqUnset, zfcf: reqUnset, zrcf: reqUnset)
  for x in items: c.item(b, x)
  Fc(fc: b.fc, rc: b.rc, fcf: b.fcf, rcf: b.rcf)

proc compileRegex(c: var Comp; alts: seq[Rx]): Fc =
  ## `compile_regex`: the branches' first / required characters combined.
  result = Fc(fcf: reqUnset, rcf: reqUnset)
  for i, br in alts:
    let b = c.compileBranch(branchItems(br))
    if i == 0:
      result = b
      continue
    if result.fcf >= 0 and (result.fcf != b.fcf or result.fc != b.fc):
      if result.rcf < 0:
        result.rc = result.fc
        result.rcf = result.fcf
      result.fcf = reqNone
    var brc = b.rc
    var brcf = b.rcf
    if result.fcf < 0 and b.fcf >= 0 and brcf < 0:
      brc = b.fc
      brcf = b.fcf
    if (result.rcf and not reqVaryBit) != (brcf and not reqVaryBit) or
       result.rc != brc:
      result.rcf = reqNone
    else:
      result.rc = brc
      result.rcf = result.rcf or brcf

# ---- anchoring and line starts ------------------------------------------------

proc hasPruneOrSkip(x: Rx): bool =
  ## cd->had_pruneorskip.
  case x.kind
  of rxVerb: x.verb in {vbPrune, vbSkip, vbSkipName}
  of rxCat, rxAlt:
    for k in x.kids:
      if hasPruneOrSkip(k): return true
    false
  of rxRep: hasPruneOrSkip(x.sub)
  else: false

proc isAllAny(x: Rx): bool =
  ## OP_ALLANY: `.` under `(?s)`.
  x.kind in {rxSet, rxChars} and x.op == aoAny and not x.crlfDot and
    (if x.kind == rxSet: x.bytes == pcreAnyByte
     else: x.cps == @[(0'i32, maxCp)])

proc firstSignificant(items: seq[Rx]): Rx =
  ## `first_significant_code`: the branch's first item, past items `{0}`
  ## leaves out (a group `{0}` is OP_SKIPZERO, significant); nil at the
  ## branch's end.
  for x in items:
    if x.kind == rxRep and x.hi == 0 and not x.sub.isGroup: continue
    return x
  nil

proc isAnchored(x: Rx; pruneSkip: bool): bool =
  ## `is_anchored` over a group's alternatives.
  for br in groupAlts(x):
    let s = firstSignificant(branchItems(br))
    if s == nil: return false
    if s.isGroup:
      if not isAnchored(s, pruneSkip): return false
    elif s.kind == rxRep and s.sub.isGroup and s.lo >= 1:
      if not isAnchored(s.sub, pruneSkip): return false
    elif s.kind == rxRep and s.lo == 0 and s.hi == -1 and
         s.sub.kind in {rxSet, rxChars} and s.sub.op == aoAny:
      # OP_TYPESTAR: anchored only for OP_ALLANY.
      if not isAllAny(s.sub) or pruneSkip: return false
    elif s.kind != rxBol or s.multi:
      return false
  true

proc isStartline(x: Rx; pruneSkip: bool): bool =
  ## `is_startline` over a group's alternatives.
  for br in groupAlts(x):
    let s = firstSignificant(branchItems(br))
    if s == nil: return false
    if s.isGroup:
      if not isStartline(s, pruneSkip): return false
    elif s.kind == rxRep and s.sub.isGroup and s.lo >= 1:
      if not isStartline(s.sub, pruneSkip): return false
    elif s.kind == rxRep and s.lo == 0 and s.hi == -1 and
         s.sub.kind in {rxSet, rxChars} and s.sub.op == aoAny:
      # OP_TYPESTAR over OP_ANY (not OP_ALLANY).
      if isAllAny(s.sub) or pruneSkip: return false
    elif s.kind != rxBol:
      return false
  true

# ---- set_start_bits -------------------------------------------------------------

type Ssb = enum ssbFail, ssbDone, ssbContinue

proc isLetter(b: int): bool = char(b) in {'a'..'z', 'A'..'Z'}

proc otherCase(b: int): int =
  if char(b) in {'a'..'z'}: b - 32
  elif char(b) in {'A'..'Z'}: b + 32
  else: b

proc tableBit(bits: var set[char]; utf: bool; ch: int32; ci: bool) =
  ## `set_table_bit`: the first byte, and the other case of an ASCII
  ## letter when caseless.
  let b = (if utf: ord(utf8Encode(ch)[0]) else: int(ch))
  bits.incl char(b)
  if utf and ch > 127:
    # RFC-0005 S8bt: caseless, the lead byte of UCD_OTHERCASE too.
    if ci: bits.incl utf8Encode(ucdOther(ch))[0]
    return
  if ci and isLetter(b): bits.incl char(otherCase(b))

proc mapBits(bits: var set[char]; x: Rx; utf: bool) =
  ## A class bitmap (its members below 0x100) as start bytes: in UTF mode a
  ## member 0x80..0xFF is its lead byte 0xC2 / 0xC3.
  let m = (if x.kind == rxSet: x.bytes else: cpBytes(x.cps))
  for ch in m:
    let v = ord(ch)
    if utf and v >= 128: bits.incl char((v shr 6) or 0xC0)
    else: bits.incl ch

proc asciiOf(x: Rx): set[char] =
  ## The ASCII members of an atom.
  let m = (if x.kind == rxSet: x.bytes else: cpBytes(x.cps))
  m * {'\x00'..'\x7F'}

proc atomBits(bits: var set[char]; x: Rx; utf: bool): bool =
  ## The start bits of one atom (the repeat aside: the 8-bit library sets
  ## the same bits for a repeated type); false when `set_start_bits` fails
  ## on it.
  case x.op
  of aoChar: tableBit(bits, utf, x.ch, x.ci)
  of aoNot, aoNotSpace, aoAny, aoProp, aoFail: return false
  of aoClass: mapBits(bits, x, utf)
  of aoNClass, aoXClass:
    if x.op == aoXClass:
      if x.xProp: return false
      if not x.xMap and x.xNot: return false
    # OP_NCLASS (and OP_XCLASS, falling into it): in UTF mode, the leads
    # of the characters above 0xFF.
    if utf: bits = bits + {'\xC4'..'\xFF'}
    mapBits(bits, x, utf)
  of aoType:
    if not utf:
      bits = bits + (if x.kind == rxSet: x.bytes else: cpBytes(x.cps))
    else:
      bits = bits + asciiOf(x)
      if x.negType: bits = bits + {'\xC0'..'\xFF'}
  of aoHSpace:
    bits = bits + (if utf: {'\t', ' ', '\xC2', '\xE1', '\xE2', '\xE3'}
                   else: {'\t', ' ', '\xA0'})
  of aoVSpace:
    bits = bits + (if utf: {'\n', '\v', '\f', '\r', '\xC2', '\xE2'}
                   else: {'\n', '\v', '\f', '\r', '\x85'})
  true

proc startBits(bits: var set[char]; x: Rx; utf: bool): Ssb =
  ## `set_start_bits` over a group's alternatives.
  var yld = ssbDone
  let alts = groupAlts(x)
  for i, br in alts:
    let items = branchItems(br)
    var k = 0
    var stop = false
    while not stop:
      if k >= items.len:
        # OP_ALT ends a branch, OP_KET the last one.
        if i < alts.high:
          yld = ssbContinue
          break
        return ssbContinue
      let it = items[k]
      inc k
      case it.kind
      of rxSet, rxChars:
        if not atomBits(bits, it, utf): return ssbFail
        stop = true
      of rxCat, rxAlt:
        let r = startBits(bits, it, utf)
        if r == ssbFail: return ssbFail
        if r == ssbDone: stop = true
      of rxRep:
        if it.hi == 0: continue   # omitted, or OP_SKIPZERO
        let s = it.sub
        if s.isGroup:
          let r = startBits(bits, s, utf)
          if r == ssbFail: return ssbFail
          # OP_BRAZERO carries on; a first copy that is DONE stops.
          if it.lo >= 1 and r == ssbDone: stop = true
        else:
          if not atomBits(bits, s, utf): return ssbFail
          if it.lo >= 1: stop = true
      of rxBol, rxEol, rxEolAbs, rxVerb, rxAccept:
        return ssbFail
  yld

# ---- find_minlength -----------------------------------------------------------

proc minLen(x: Rx; count: var int): int =
  ## `find_minlength` over a group: -1 when an `(*ACCEPT)` is in it (or
  ## past PCRE's complexity count).
  if count > 1000:
    inc count
    return -1
  inc count
  result = -1
  for br in groupAlts(x):
    var bl = 0
    for it in branchItems(br):
      case it.kind
      of rxSet, rxChars:
        if it.op != aoFail: inc bl
      of rxCat, rxAlt:
        let d = minLen(it, count)
        if d < 0: return d
        bl += d
      of rxRep:
        if it.hi == 0: continue
        if it.sub.isGroup:
          for _ in 1 .. it.lo:
            let d = minLen(it.sub, count)
            if d < 0: return d
            bl += d
        else:
          bl += it.lo
      of rxAccept: return -1
      of rxBol, rxEol, rxEolAbs, rxVerb: discard
    if result < 0 or bl < result: result = bl

# ---- the whole ------------------------------------------------------------------

proc startOpt*(pr: PcreParse): StartOpt =
  ## RFC-0005 S8bj. The start-of-match data PCRE computes for `pr` (psOk).
  var c = Comp(utf: pr.utf)
  let top = c.compileRegex(groupAlts(pr.root))
  var rcf = top.rcf
  if c.hadAccept: rcf = reqNone
  let pruneSkip = hasPruneOrSkip(pr.root)
  result = StartOpt(firstChar: -1, minLength: -1, reqChar: -1)
  result.anchored = isAnchored(pr.root, pruneSkip)
  if not result.anchored:
    if top.fcf >= 0:
      result.firstChar = int(top.fc and 0xFF)
      result.firstCaseless = (top.fcf and reqCaselessBit) != 0 and
                             isLetter(result.firstChar)
    elif isStartline(pr.root, pruneSkip):
      result.startline = true
    else:
      var bits: set[char]
      if startBits(bits, pr.root, pr.utf) == ssbDone:
        result.hasBits = true
        result.bits = bits
  var count = 0
  let m = minLen(pr.root, count)
  if m > 0: result.minLength = m
  if rcf >= 0 and (not result.anchored or (rcf and reqVaryBit) != 0):
    result.reqChar = int(top.rc and 0xFF)
    result.reqCaseless = (rcf and reqCaselessBit) != 0 and
                         isLetter(result.reqChar)
