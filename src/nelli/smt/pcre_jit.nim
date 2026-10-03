## RFC-0005 S8bt. PCRE 8.37's JIT (pcre_jit_compile.c, the Windows legs'
## library) where it differs from the interpreter the walker models
## (`pcre_select.nim`): its start-of-match scan.
##
## An unanchored call on the JIT moves each start forward with
## `fast_forward_first_n_chars` when it applies (else with the first
## character, the line start or the start bits, as the interpreter does).
## `scan_prefix` reads, from the compiled code (`pcre_code.nim`), up to 16
## leading character positions: per position a compare value and mask
## (`chars`) and up to 7 bytes (`bytes`, 255 = any). From them the scan
## keeps:
##   * a RANGE: the longest run of at least 3 positions whose byte sets
##     are known, the last with at most 4 bytes. At a candidate start `x`
##     the byte at `x + rangeRight` indexes a skip table (the least `i`
##     such that the byte is in the set of position `rangeRight - i`,
##     `rangeLen` when none): a non-zero entry moves `x` on by that much;
##   * up to three OFFSETS of positions whose masks have at most two bits:
##     the byte there, or-ed with the mask, must equal the compare value,
##     else `x` moves on by one.
## The scan stops at the first such `x`, or at the first `x` past
## `len - max`, where it gives up (and an attempt is made there anyway).
## Unlike the interpreter's start-of-match data, the scan skips whole
## positions without an attempt, so the CRLF start skip of a failed
## attempt at a CR never arises for them.
##
## Pure Nim: the walker reads it at walk time.

import ./pcre_syntax
import ./pcre_code

type
  PcreEngine* = enum
    ## RFC-0005 S8bt. The engine an unanchored call runs on: the
    ## interpreter (pcre_exec.c, the model's reference), or PCRE 8.37's
    ## JIT. Anchored calls always run on the interpreter (PCRE_ANCHORED is
    ## not a JIT option).
    peInterp, peJit837

const
  maxNChars = 16
  maxNBytes = 8
  notAChar = 0xFFFFFFFF'u32

type
  PrefixPos = object
    chr, mask: uint32        ## chars[2i], chars[2i + 1]
    n: int                   ## bytes[i * 8]: 0..7, 255 = any
    bytes: array[7, uint8]

  JitScan* = object
    ## RFC-0005 S8bt. The JIT's `fast_forward_first_n_chars`, when it
    ## applies (`on`).
    on*: bool
    max*: int                ## `scan_prefix`'s positions
    rangeRight*: int         ## -1: no range
    rangeLen*: int
    table*: array[256, int]  ## the skip table (range only)
    offs*: seq[int]          ## the offsets checked, in check order
    cmp*: seq[(uint32, uint32)]   ## per offset: (compare value, mask)

proc addPrefixByte(b: uint8; p: var PrefixPos) =
  ## `add_prefix_byte`.
  if p.n == 255: return
  if p.n == 0:
    p.n = 1
    p.bytes[0] = b
    return
  for i in 0 ..< p.n:
    if p.bytes[i] == b: return
  if p.n >= maxNBytes - 1:
    p.n = 255
    return
  p.bytes[p.n] = b
  inc p.n

proc otherCaseByte(c: char): char =
  if c in {'a'..'z'}: char(ord(c) - 32)
  elif c in {'A'..'Z'}: char(ord(c) + 32)
  else: c

proc charBytes(x: Rx; utf: bool): string =
  if utf: utf8Encode(x.ch) else: $char(x.ch)

proc isChar7Set(s: set[char]): bool =
  ## `is_char7_bitset` (not negated): no member above 0x7F.
  for c in s:
    if ord(c) > 0x7F: return false
  true

proc atomSet(x: Rx): set[char] =
  (if x.kind == rxSet: x.bytes else: cpBytes(x.cps))

proc scanPrefix(code: seq[Code]; cc0: int; pos: var seq[PrefixPos];
                at: int; maxChars0: int; utf: bool): int =
  ## `scan_prefix` from code index `cc0`, filling `pos[at ..]`; returns
  ## the positions consumed. (The C code advances its arrays as it goes;
  ## `at` is that offset.)
  var cc = cc0
  var maxChars = maxChars0
  var consumed = 0
  var at = at
  var repeat = 1
  while true:
    var last = true
    var anyc = false
    var caseless = false
    var atom: Rx = nil
    let c = code[cc]
    case c.op
    of coAtom:
      atom = c.atom
      case atom.op
      of aoChar:
        caseless = atom.ci
        last = false
        inc cc
      of aoClass:
        if utf and not isChar7Set(atomSet(atom)): return consumed
        anyc = true
        inc cc
      of aoNClass, aoXClass:
        if utf: return consumed
        anyc = true
        inc cc
      of aoType:
        if not atom.negType:
          # OP_DIGIT / OP_WHITESPACE / OP_WORDCHAR: in UTF mode the
          # character-type table must be ASCII (it is, without UCP).
          anyc = true
          inc cc
        else:
          if utf: return consumed
          anyc = true
          inc cc
      of aoNot, aoAny:
        if utf: return consumed
        anyc = true
        inc cc
      of aoProp:
        if utf: return consumed
        anyc = true
        inc cc
      of aoHSpace, aoVSpace, aoNotSpace, aoFail:
        return consumed
    of coSod, coCirc, coCircm, coDoll, coDollm, coEod, coEodn:
      inc cc
      continue
    of coRep:
      atom = c.atom
      case fam(atom)
      of afChar:
        case c.rep
        of rpPlus, rpMinPlus, rpPosPlus:
          caseless = atom.ci
          inc cc
        of rpExact:
          caseless = atom.ci
          repeat = c.count
          last = false
          inc cc
        of rpQuery, rpMinQuery, rpPosQuery:
          caseless = atom.ci
          maxChars = scanPrefix(code, cc + 1, pos, at, maxChars, utf)
          if maxChars == 0: return consumed
          last = false
          inc cc
        else: return consumed
      of afType:
        if c.rep == rpExact:
          # OP_TYPEEXACT: the count, then the type read as an opcode.
          repeat = c.count
          case atom.op
          of aoType:
            if atom.negType and utf: return consumed
            anyc = true
          of aoAny, aoProp:
            if utf: return consumed
            anyc = true
          else:
            # OP_HSPACE .. as an opcode: the default case.
            return consumed
          inc cc
        else: return consumed
      of afNot:
        if c.rep == rpExact:
          if utf: return consumed
          anyc = true
          repeat = c.count
          inc cc
        else: return consumed
      of afClass: return consumed
    of coKet:
      inc cc
      continue
    of coAlt:
      cc = c.link
      continue
    of coBra, coCbra:
      var alt = c.link
      while code[alt].op == coAlt:
        maxChars = scanPrefix(code, alt + 1, pos, at, maxChars, utf)
        if maxChars == 0: return consumed
        alt = code[alt].link
      inc cc
      continue
    else:
      return consumed
    if anyc:
      while true:
        pos[at].chr = 0xFF
        pos[at].mask = 0xFF
        pos[at].n = 255
        inc consumed
        dec maxChars
        if maxChars == 0: return consumed
        inc at
        dec repeat
        if repeat <= 0: break
      repeat = 1
      continue
    # A literal (or its repeat): its bytes, and the other case's.
    let bs = charBytes(atom, utf)
    var oc = ""
    if caseless:
      if utf and atom.ch > 127:
        # A non-ASCII caseless character: not modelled here (the reader
        # declines Unicode case folding in UTF mode).
        caseless = false
      else:
        let o = otherCaseByte(char(atom.ch))
        if o != char(atom.ch): oc = $o
        else: caseless = false
    while true:
      for k in 0 ..< bs.len:
        var chr = uint32(ord(bs[k]))
        addPrefixByte(uint8(chr), pos[at])
        var mask = 0'u32
        if caseless:
          addPrefixByte(uint8(ord(oc[k])), pos[at])
          mask = chr xor uint32(ord(oc[k]))
          chr = chr or mask
        if pos[at].chr == notAChar:
          pos[at].chr = chr
          pos[at].mask = mask
        else:
          mask = mask or (pos[at].chr xor chr)
          chr = chr or mask
          pos[at].chr = chr
          pos[at].mask = pos[at].mask or mask
        inc consumed
        dec maxChars
        if maxChars == 0: return consumed
        inc at
      dec repeat
      if repeat <= 0: break
    repeat = 1
    if last: return consumed

proc ones(m: uint32): int =
  var v = m
  while v != 0:
    result += int(v and 1)
    v = v shr 1

proc jitScan*(code: seq[Code]; utf: bool): JitScan =
  ## RFC-0005 S8bt. `fast_forward_first_n_chars`' choice (`on == false`
  ## when it returns FALSE and the other start-of-match scans apply).
  var pos = newSeq[PrefixPos](maxNChars)
  for p in pos.mitems:
    p.chr = notAChar
    p.mask = 0
    p.n = 0
  let max = scanPrefix(code, 0, pos, 0, maxNChars, utf)
  if max <= 1: return
  var onesOf = newSeq[int](max)
  for i in 0 ..< max: onesOf[i] = ones(pos[i].mask)
  var rangeRight = -1
  var rangeLen = 3 - 1
  var inRange = false
  var frm = 0
  for i in 0 .. max:
    if inRange and (i - frm) > rangeLen and pos[i - 1].n <= 4:
      rangeLen = i - frm
      rangeRight = i - 1
    if i < max and pos[i].n < 255:
      if not inRange:
        inRange = true
        frm = i
    elif inRange:
      inRange = false
  var r = JitScan(on: true, max: max, rangeRight: rangeRight)
  if rangeRight >= 0:
    r.rangeLen = rangeLen
    for b in 0 .. 255: r.table[b] = rangeLen
    for i in 0 ..< rangeLen:
      let p = pos[rangeRight - i]
      for k in 0 ..< p.n:
        if r.table[p.bytes[k]] > i: r.table[p.bytes[k]] = i
  var offsets = [-1, -1, -1]
  for i in 0 ..< max:
    if onesOf[i] <= 2:
      offsets[0] = i
      break
  if offsets[0] < 0 and rangeRight < 0: return JitScan()
  if offsets[0] >= 0:
    for i in countdown(max - 1, offsets[0] + 1):
      if onesOf[i] <= 2 and i != rangeRight:
        offsets[1] = i
        break
    if offsets[1] == -1 and offsets[0] == 0 and rangeRight < 0:
      return JitScan()
    if offsets[1] >= 0 and rangeRight == -1:
      for i in (offsets[0] + offsets[1]) div 2 + 1 ..< offsets[1]:
        if onesOf[i] <= 2:
          offsets[2] = i
          break
      if offsets[2] == -1:
        for i in countdown((offsets[0] + offsets[1]) div 2, offsets[0] + 1):
          if onesOf[i] <= 2:
            offsets[2] = i
            break
    # The generated code checks offsets[0], then offsets[1], then
    # offsets[2]; each must hold.
    for k in [0, 1, 2]:
      if offsets[k] >= 0:
        r.offs.add offsets[k]
        r.cmp.add (pos[offsets[k]].chr, pos[offsets[k]].mask)
  r

proc stopsAt*(j: JitScan; s: string; x: int): bool =
  ## Whether the scan, visiting `x` (and not giving up there), stops: the
  ## range byte is in its position's set and every offset's byte matches.
  if j.rangeRight >= 0 and j.table[ord(s[x + j.rangeRight])] != 0:
    return false
  for k, o in j.offs:
    if (uint32(ord(s[x + o])) or j.cmp[k][1]) != j.cmp[k][0]: return false
  true

proc scanFrom*(j: JitScan; s: string; x0: int): int =
  ## RFC-0005 S8bt. The concrete scan from `x0`: where the next attempt is
  ## made.
  var x = x0
  let bound = s.len - (j.max - 1)
  while true:
    if x >= bound: return x
    if j.rangeRight >= 0:
      let t = j.table[ord(s[x + j.rangeRight])]
      if t != 0:
        x += t
        continue
    var fine = true
    for k, o in j.offs:
      if (uint32(ord(s[x + o])) or j.cmp[k][1]) != j.cmp[k][0]:
        fine = false
        break
    if fine: return x
    inc x
