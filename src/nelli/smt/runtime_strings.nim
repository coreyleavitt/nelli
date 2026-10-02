# runtime_strings.nim — Cluster S include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_strings.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents (CR-7-deeper Stage 8+):
#   mkConcreteStrSeq, joinStrSeq — Cluster S string-seq helpers (moved
#   from runtime.nim; only used by lowerStrArm).
#   `lowerStrArm(env, e)` — the `lower()` dispatch arm for
#   `iekStrLit` and `StrOpKinds` (Cluster S, Stage 7 / Stage 8, CR-7).
# Placement in runtime.nim: immediately after `coerceToBoolSV` and
# immediately before `lowerFloatArm`, between `lower`'s forward-decl
# and `lower`'s body.

template requireStr(sv: SymVal, opName: string) =
  ## v65: classified totality guard for the string-op operand sites. A
  ## non-svString operand here is a walker MODELING GAP (an unmodeled
  ## lowering upstream), not a program invariant — observed in the field on
  ## the real `parseTftpUri` (`hostPort.rfind(':')` arrived with a
  ## non-string receiver and the former bare `doAssert` died as an
  ## AssertionDefect into the Defect net). Raise the classified carrier
  ## instead: → sxUnknown + `seUnsupportedStringOp` (Invariant 3), and the
  ## msg records the actual kind so round-4 can chase the upstream lowering.
  if sv.kind != svString:
    raise (ref SymexUnsupportedStringOpError)(op: opName,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: opName & ": operand lowered to " & plainEnglishSymValKind(sv.kind) &
           " — not svString (→ sxUnknown, Invariant 3)")

proc needleAsStr(sv: SymVal, opName: string): Z3String =
  ## v65 (chapulin round-4 backlog, first Defect-net field catch): the
  ## needle argument of `find`/`rfind`/`contains`/`startsWith`/`endsWith`
  ## is CHAR-typed in half of the strutils overloads (`s.find(']')`,
  ## `hostPort.rfind(':')`, …) and a Nim `char` lowers as svBV8 (S3's char
  ## repr) — the former bare `doAssert sub.kind == svString` at these sites
  ## was an uncaught AssertionDefect (surfaced as `weInternalWalkerFault`
  ## through the round-3 net on the real `parseTftpUri`). Bridge: a BV8
  ## char becomes the 1-char string via `(str.from_code codepoint)` —
  ## exact under the ≤0xFF byte-faithful constraint (ADR-0006), where the
  ## codepoint IS the byte value. Any other kind raises the classified
  ## `SymexUnsupportedStringOpError` (this file's established carrier —
  ## runSymex maps it to sxUnknown + seUnsupportedStringOp, Invariant 3).
  case sv.kind
  of svString: sv.str
  of svBV8, svBV16, svBV32, svBV64, svInt:
    # svBV8 is S3's canonical char repr; a char LITERAL parses as an int
    # literal and can arrive at any int width (observed: svBV64 for
    # `s.rfind(':')`) — all carry the codepoint, so `fromCode` is exact
    # for every one of them under the ≤0xFF byte-faithful domain.
    fromCode(toZ3Int(sv))
  else:
    raise (ref SymexUnsupportedStringOpError)(op: opName,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: opName & ": needle lowered to " & plainEnglishSymValKind(sv.kind) &
           " — expected a string or char (→ sxUnknown, Invariant 3)")

proc mkConcreteStrSeq(parts: seq[string]): SymVal =
  ## Phase 15 S5. Build a fully-concrete `svSeq` whose element type is
  ## `string`: a `Z3Array[Z3Int, Z3String]` constant defaulting to the empty
  ## string, with `parts[i]` stored at index `i`, and `seqLen` pinned to the
  ## part count. No free variables and no quantifier — the `split` special
  ## cases (empty-sep / concrete-inline) compute the decomposition in Nim and
  ## hand the literal parts here, so the result is decidable with no string-
  ## solver hang risk. Unstored slots are never read (len-bounded access).
  var arr = mkConstArray[Z3Int, Z3String](mkString(""))
  for i, part in parts:
    arr = store(arr, mkInt(i), mkString(part))
  SymVal(kind: svSeq, seqLen: mkInt(parts.len),
         seqDataRaw: toAnyAst(arr), seqElemTy: tString())

proc joinStrSeq(parts: SymVal, sep: Z3String): Z3String =
  ## Phase 15 S5. Lower `xs.join(sep)` over a CONCRETE-length `svSeq[string]`
  ## to a Z3 concat chain with `sep` interleaved:
  ##   join(@[p0,p1,…,pn], sep) == p0 ++ sep ++ p1 ++ … ++ sep ++ pn
  ## The seq length must be a Z3 numeral (concrete) so the chain is finite;
  ## the split special cases guarantee that.
  doAssert parts.kind == svSeq and parts.seqElemTy.kind == itString,
    "joinStrSeq: not an svSeq[string]"
  let n = parseInt(getNumeralString(parts.seqLen)) # [placeholder-audited]
  let typed = wrap[Z3Array[Z3Int, Z3String]](
    parts.seqDataRaw.ctx, parts.seqDataRaw.raw) # [placeholder-audited]
  if n <= 0:
    return mkString("")
  result = select(typed, mkInt(0))
  for i in 1 ..< n:
    result = concat(result, sep)
    result = concat(result, select(typed, mkInt(i)))

proc runeToUtf8Sym(r: Z3Int): Z3String =
  ## Phase 16 A7-S2. Encode a Unicode codepoint r (Z3Int, pinned [0,0x10FFFF] by
  ## S1's range constraint) as its UTF-8 byte string, using a 4-branch ITE on the
  ## codepoint range. Every fromCode() call takes a BYTE VALUE in [0,0xFF] — never
  ## the raw codepoint — so all output chars are ≤0xFF (byte-faithful, ADR-0006).
  ##
  ## The byte-level approach is MANDATORY for two reasons (ADR-0017 §context):
  ##   1. `fromCode(codepoint)` is NOT a UTF-8 encoder: it creates a single Z3Char
  ##      (probe P3c: fromCode(0x20AC) ≠ "\xE2\x82\xAC").
  ##   2. Z3 chars are BV18 (max codepoint 0x3FFFF); fromCode(codepoint) overflows
  ##      for high-plane runes (probe P6d). Byte values ≤0xFF fit BV18 trivially.
  ##   The byte-level form recovered r=0x40000 correctly (probe P7c).
  ##
  ## Byte arithmetic (Z3Int integer div/mod with constant divisors, all non-negative
  ## since r ∈ [0,0x10FFFF] by the S1 pin):
  ##   1-byte (r < 0x80):    fromCode(r)
  ##   2-byte (r < 0x800):   lead=0xC0+r/64, cont=0x80+r mod 64
  ##   3-byte (r < 0x10000): lead=0xE0+r/4096, c1=0x80+(r/64) mod 64, c2=0x80+r mod 64
  ##   4-byte (else):        lead=0xF0+r/262144, c1=0x80+(r/4096) mod 64,
  ##                         c2=0x80+(r/64) mod 64, c3=0x80+r mod 64
  ## Hang-free (probes P5a–d, P7a–c incl. r=0x1F600 > 0x3FFFF).
  let byte1  = fromCode(r)
  let lead2  = fromCode(mkInt(0xC0) + r div 64)
  let cont2  = fromCode(mkInt(0x80) + r mod 64)
  let b2     = concat(lead2, cont2)
  let lead3  = fromCode(mkInt(0xE0) + r div 4096)
  let cont3a = fromCode(mkInt(0x80) + (r div 64) mod 64)
  let cont3b = fromCode(mkInt(0x80) + r mod 64)
  let b3     = concat(concat(lead3, cont3a), cont3b)
  let lead4  = fromCode(mkInt(0xF0) + r div 262144)
  let cont4a = fromCode(mkInt(0x80) + (r div 4096) mod 64)
  let cont4b = fromCode(mkInt(0x80) + (r div 64) mod 64)
  let cont4c = fromCode(mkInt(0x80) + r mod 64)
  let b4     = concat(concat(concat(lead4, cont4a), cont4b), cont4c)
  ite(r < mkInt(0x80), byte1,
    ite(r < mkInt(0x800), b2,
      ite(r < mkInt(0x10000), b3, b4)))

# ---- RFC-0005 S8aw: regex replace, the walker's own lowering ---------------
#
# `replace(s, re"p", by)` (std/re) appends `by` for EVERY leftmost,
# non-overlapping PCRE match, scanning on from the match's end. Z3's
# `str.replace_re` is first-match only and picks the SHORTEST leftmost match
# (PCRE's `+` is greedy), and Z3 answers `unknown` on it even for concrete
# operands, so it is not used. Three pattern shapes fix PCRE's match
# selection by the shape alone, and are lowered position by position:
#   * a fixed-length sequence of byte sets (a literal; one class): every
#     match has length m, so a window match at `k` is a match iff no earlier
#     match covers `k` -- leftmost-first, non-overlapping;
#   * one byte set and a greedy `+`: every maximal run is one match.
# Never matching the empty string, none of the three meets Nim's
# NOTEMPTY_ATSTART retry.
#
# RFC-0005 S8ay: the shape is read off `pcre_syntax`'s tree, not the
# pattern text, so the byte sets are PCRE's (`.` excludes `\n`, `\s` is
# {HT LF VT FF CR SP}, `\D \W \S` are complements, `\h \v`, POSIX
# classes, escapes) and `rex` ignores whitespace and `#` comments -- the
# IR now carries `re` vs `rex` (S8aw declined whitespace for want of it).

const
  regexReplaceMaxKnown = 256
    ## A receiver of known length up to this unrolls exactly, untainted
    ## (RFC-0005 S8aw); any other receiver takes `regexReplaceRec` (S8ay).

type RegexReplaceShape = object
  atoms: seq[set[char]]   ## one byte set per matched byte
  plus: bool              ## a single atom under a greedy `+`

proc regexDecline(sp: RegexSpec; why: string) {.noreturn.} =
  raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
    msg: "regex replace(s, " & sp.flag & "\"" & sp.pattern & "\", by) is " &
         "not modeled: " & why & " (RFC-0005 S8bb lowers every pattern " &
         "PCRE's priority run reads; the result is a fresh string, " &
         "replay-gated)")

proc regexReplaceShape(pr: PcreParse): (bool, RegexReplaceShape) =
  ## RFC-0005 S8aw; S8ay reads `pcre_syntax`'s tree. One of the shapes
  ## lowered by the unroll / `regexReplaceRec`, or `false`: RFC-0005 S8bb
  ## lowers every other pattern by the priority run
  ## (`regex_parser.replaceRunZ3`).
  var sh: RegexReplaceShape
  let (fine, edges, _) = splitEdges(pr.root)
  if not fine or edges.len != 1: return (false, sh)
  let e = edges[0]
  if e.bol or e.eol != rxCat or lenRange(e.body)[0] == 0: return (false, sh)
  let items = flattenCat(e.body)
  for it in items:
    let (isSet, cs) = asSet(it)
    if isSet:
      sh.atoms.add cs
      continue
    if it.kind == rxRep:
      let (subSet, ss) = asSet(it.sub)
      if subSet and it.lo == it.hi:
        for _ in 0 ..< it.lo: sh.atoms.add ss
        continue
      if subSet and items.len == 1 and it.lo == 1 and it.hi < 0 and
         not it.lazy:
        sh.atoms.add ss
        sh.plus = true
        continue
    return (false, sh)
  (true, sh)

proc inByteSet(code: Z3Int; cs: set[char]): Z3Bool =
  ## `code` (a `toCode(at(s, k))`: -1 past the end) is a byte in `cs`, as a
  ## disjunction over the set's runs.
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

proc regexReplaceUnrolled(s, by: Z3String; sh: RegexReplaceShape;
                          n: int): Z3String =
  ## RFC-0005 S8aw. Nim's `replace(s, re, by)` for a receiver of at most `n`
  ## bytes, as the concatenation of one piece per position `k < n`. Past
  ## `len(s)`, `toCode(at(s, k))` is -1, in no byte set, so every piece there
  ## is "". Fixed length m: `start(k)` is a window match at `k` that no
  ## earlier start within `m - 1` covers; the piece is `by` at a start, ""
  ## inside a match, the byte elsewhere. `+`: the piece is `by` at the first
  ## byte of a run of the set, "" at the rest of the run.
  let empty = mkString("")
  let lenS = len(s)
  var codes: seq[Z3Int]
  for k in 0 ..< n: codes.add toCode(at(s, mkInt(k)))
  result = empty
  if sh.plus:
    var prevIn = mkBool(false)
    for k in 0 ..< n:
      let inK = inByteSet(codes[k], sh.atoms[0])
      let piece = ite(mkInt(k) < lenS,
                      ite(inK, ite(prevIn, empty, by), at(s, mkInt(k))), empty)
      result = if k == 0: piece else: concat(result, piece)
      prevIn = inK
  else:
    let m = sh.atoms.len
    var starts: seq[Z3Bool]
    for k in 0 ..< n:
      var covered = mkBool(false)
      for j in max(0, k - m + 1) ..< k: covered = covered or starts[j]
      var start = mkBool(false)
      if k + m <= n:
        start = inByteSet(codes[k], sh.atoms[0])
        for j in 1 ..< m: start = start and inByteSet(codes[k + j], sh.atoms[j])
        start = start and not covered
      starts.add start
      let piece = ite(mkInt(k) < lenS,
                      ite(start, by, ite(covered, empty, at(s, mkInt(k)))), empty)
      result = if k == 0: piece else: concat(result, piece)

proc regexFreshName(tag: string): string =
  ## RFC-0005 S8ay. A per-run-unique name for a constant the regex lowering
  ## fixes by definitional constraints (`stripDecompConds`; the
  ## `stripSynthCounter` precedent -- two sites must never share one).
  inc stripSynthCounter
  tag & "#" & $stripSynthCounter

proc regexReplaceRec(s, by: Z3String; sh: RegexReplaceShape): Z3String =
  ## RFC-0005 S8ay (item 5). Nim's `replace(s, re, by)` for a receiver of
  ## any length, as a recursive function of the remaining suffix `u` (a
  ## fresh `define-fun-rec` per lowering; its body reads `by` as a free
  ## term). Fixed length m: a window match at the head of `u` emits `by`
  ## and skips m bytes, else the head byte is kept and the scan moves one
  ## byte -- leftmost-first, non-overlapping, exactly the unroll's `start` /
  ## `covered`. `+`: `prevIn` is "the previous byte was in the set", so a
  ## run emits `by` once at its first byte. Measured against index
  ## recursion, a hybrid with the 16-byte unroll and `seq.foldli` (which
  ## crashes Z3 5.1 in `Z3_mk_seq_foldli`); this decided the most.
  let ctx = s.ctx
  let empty = mkString("")
  if sh.plus:
    let cs = sh.atoms[0]
    let f = defineRecFun[Z3String, Z3Bool, Z3String](ctx,
      regexFreshName("__regexReplaceRun"),
      proc (self: Z3FuncDecl[(Z3String, Z3Bool), Z3String]; u: Z3String;
            prevIn: Z3Bool): Z3String =
        let h = at(u, mkInt(0))
        let inH = inByteSet(toCode(h), cs)
        let rest = substr(u, mkInt(1), len(u) - mkInt(1))
        ite(len(u) == mkInt(0), empty,
            concat(ite(inH, ite(prevIn, empty, by), h), self(rest, inH))))
    return f(s, mkBool(false))
  let atoms = sh.atoms
  let m = atoms.len
  let f = defineRecFun[Z3String, Z3String](ctx,
    regexFreshName("__regexReplaceFixed"),
    proc (self: Z3FuncDecl[(Z3String,), Z3String]; u: Z3String): Z3String =
      var win = len(u) >= mkInt(m)
      for j in 0 ..< m: win = win and inByteSet(toCode(at(u, mkInt(j))), atoms[j])
      ite(len(u) == mkInt(0), empty,
        ite(win, concat(by, self(substr(u, mkInt(m), len(u) - mkInt(m)))),
                 concat(at(u, mkInt(0)),
                        self(substr(u, mkInt(1), len(u) - mkInt(1)))))))
  f(s)

# ---- RFC-0005 S8ay: the `std/re` entry points --------------------------------

proc regexRejected(msg: string; kind: SVKind): SymVal =
  ## RFC-0005 S8ay. A pattern PCRE rejects: `re` raises `RegexError` with
  ## `msg` (Nim's exact message) whenever the call runs. Deposited in the
  ## `regexRaiseMsgs` sink -- `drainRegexRaises` routes it and ends the
  ## path -- and the call's value is a placeholder of its sort, never
  ## observed (no continuation survives the raise).
  regexRaiseMsgs.add msg
  syncRegexRaiseMsg(msg)
  case kind
  of svBool: SymVal(kind: svBool, bo: mkBool(false))
  of svInt: SymVal(kind: svInt, zi: mkInt(0))
  else: SymVal(kind: svString, str: mkString(""))

proc regexOutcomeGate(sp: RegexSpec; pr: PcreParse) =
  ## RFC-0005 S8ay. A pattern whose validity the reader leaves undecided
  ## (an escape or construct it does not read) is ⊤ -- whether `re` even
  ## raises is unknown (`seUnsupportedRegex`); a valid pattern holding an
  ## unmodelled construct (a lookaround, a back-reference) has a value the
  ## walker cannot compute, a fresh one (`seZ3StringIncomplete`).
  case pr.status
  of psUnknown:
    raise (ref SymexUnsupportedRegexError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: "regex " & sp.entry & "(s, " & sp.flag & "\"" & sp.pattern &
           "\"): " & pr.reason & " (seUnsupportedRegex: whether PCRE " &
           "accepts the pattern is not decided)")
  of psUnmodelled:
    raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: "regex " & sp.entry & "(s, " & sp.flag & "\"" & sp.pattern &
           "\") is not modeled: " & pr.reason & " (RFC-0005 S8ay; the " &
           "value is a fresh one, replay-gated)")
  else: discard

proc lowerRegexCall(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8ay. `match` / `contains` / `startsWith` / `endsWith`
  ## (`iekStrMatch`, svBool) and `find` / `matchLen` / `findBounds`'s two
  ## halves (`iekStrFindRe`, svInt), per `regex_parser.lowerRegexEntry`.
  ## Before S8ay `match` and `contains` were both full-string membership
  ## with `start` dropped, and `find` declined.
  let sp = decodeRegexSpec(e.strOp)
  let kind =
    case e.kind
    of iekStrMatch: svBool
    of iekStrCaptureRe: svString   # RFC-0005 S8bb: a capture group
    else: svInt
  let recv = lower(env, e.strArgs[0])
  requireStr(recv, $e.kind)
  let pr = parseSpec(sp)
  if pr.status == psRejected:
    return regexRejected(pr.errMsg, kind)
  var start = mkInt(0)
  if e.strArgs.len >= 2:
    start = toZ3Int(lower(env, e.strArgs[1]))
  # RFC-0005 S8bb: a captures overload's group reads the call's own
  # operands (atoms the parser bound) after the call: the call's
  # `RangeDefect` is already forked, so the group adds none.
  if e.strArgs.len >= 2 and not sp.entry.startsWith("capture"):
    # Nim passes `start.cint` to PCRE: outside int32 it raises RangeDefect
    # (`findBounds` first clamps to `MaxReBufSize`, high(cint), so only
    # below). Gated with every range check by `drainRangeRaises`.
    let below = start < mkInt(-2147483648'i64)
    let outside =
      if sp.entry in ["findBoundsFirst", "findBoundsFirstCap",
                      "findBoundsLast"]: below
      else: below or (start > mkInt(2147483647'i64))
    rangeDefectConds.add outside
    syncRangeDefectCond(outside)
  regexOutcomeGate(sp, pr)
  # RFC-0005 S8bb: a captures overload's group carries the length of its
  # `matches` argument and the element's value before the call.
  # (`findBounds`' bounds overload: an svInt field, `iekStrFindRe`.)
  let capture = sp.entry.startsWith("capture")
  var arrLen = mkInt(0)
  var old = mkString("")
  var oldI = mkInt(0)
  if capture:
    arrLen = toZ3Int(lower(env, e.strArgs[2]))
    let o = lower(env, e.strArgs[3])
    if e.kind == iekStrCaptureRe:
      requireStr(o, $e.kind)
      old = o.str
    else:
      oldI = toZ3Int(o)
  let r = lowerRegexEntry(sp, pr, recv.str, start, regexFreshName, arrLen,
                          old, oldI)
  case r.outcome
  of roValue:
    for d in r.defs: stripDecompConds.add d
    case kind
    of svBool: SymVal(kind: svBool, bo: r.b)
    of svString: SymVal(kind: svString, str: r.s)
    else: SymVal(kind: svInt, zi: r.i)
  of roRejected: regexRejected(r.msg, kind)
  of roUnknown:
    raise (ref SymexUnsupportedRegexError)(msg: r.msg)  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
  of roUnmodelled:
    raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: "regex " & sp.entry & "(s, " & sp.flag & "\"" & sp.pattern &
           "\") is not modeled: " & r.msg & " (RFC-0005 S8ay; the value " &
           "is a fresh one, replay-gated)")

proc lowerRegexDecline(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8ay. A `std/re` call the walker declines (findAll, split,
  ## replacef, multiReplace, the captures overloads; RFC-0005 S8bb: no
  ## longer findBounds over a compound operand, which the parser binds to a
  ## temporary). The receiver is lowered first, keeping its raise
  ## forks; a rejected pattern is still the `RegexError` raise. The
  ## captures overloads write their `matches` argument, which no fresh
  ## value covers, so they are ⊤ (`seUnsupportedRegex`); the rest return
  ## a fresh value of the call's type (`seZ3StringIncomplete`).
  let sp = decodeRegexSpec(e.strOp[6 .. ^1])
  let recv = lower(env, e.strArgs[0])
  requireStr(recv, "regex " & sp.entry)
  let pr = parseSpec(sp)
  if pr.status == psRejected:
    regexRaiseMsgs.add pr.errMsg
    syncRegexRaiseMsg(pr.errMsg)
    var unused: seq[Z3Bool]
    return allocateSym(e.strRetTy, freshDegradeName("__regexRejected"), unused)
  regexOutcomeGate(sp, pr)
  let what = "regex " & sp.entry & "(s, " & sp.flag & "\"" & sp.pattern & "\")"
  if not sp.entry.endsWith("Captures"):
    raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: what & " is not modeled (RFC-0005 S8ay: " & sp.entry & " needs " &
           "every match; the value is a fresh one, replay-gated)")
  raise (ref SymexUnsupportedRegexError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
    msg: what & " with a captures array is not modeled: the call writes " &
         "its `matches` argument (RFC-0005 S8ay, seUnsupportedRegex)")

proc lowerStrArm(env: Env, e: IRExpr): SymVal =
  ## Stage 7 (CR-7) Cluster S extraction. Called from `lower`'s case arm for
  ## `iekStrLit` and `StrOpKinds`. Params: `env` and `e` are the same as
  ## `lower`'s; `proto` is NOT used by any string arm. Calls `lower`
  ## recursively (forward-declared above).
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   mkString, mkInt, at, toCode, substr, contains, startsWith, endsWith,
  ##   indexOf, replaceAll, joinStrSeq, mkConcreteStrSeq,
  ##   parseNimRegexToZ3Regex, intToBv, mkConstArray, store, toStr, toInt,
  ##   ite, len, concat, liftBV, toZ3Int, syncParseIntRaiseCond,
  ##   parseIntRaiseConds,
  ##   syncStrIndexOobCond, strIndexOobConds,
  ##   SymexUnsupportedStringOpError, SymexZ3StringIncompleteError,
  ##   SymexZ3VersionMissingError, SymexUnsupportedRegexError, StrOpKinds
  case e.kind
  of iekStrLit:
    SymVal(kind: svString, str: mkString(e.sval))
  of iekStrLen:
    # Phase 15 S3. `s.len` → Z3 `(str.len s)`. Under the ≤0xFF byte-faithful
    # constraint (asserted at allocation, ADR-0006) the Z3 character count
    # equals the Nim byte length, so this is exact.
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrLen")
    SymVal(kind: svInt, zi: len(recv.str))
  of iekStrAt:
    # Phase 15 S3 / RFC-chapulin-hardening SND-4 (ADR-0024). `s[i]` (read) → a
    # Nim `char` (svBV8 unsigned). The Z3 bridge: `at(s, i)` is a 1-char
    # Z3String; `toCode(.)` is its codepoint as Z3Int, which under ≤0xFF is
    # exactly the byte value 0..255 (== Nim byte index == Z3 position). We
    # narrow that Z3Int to a BV8 char. `char` classifies (Z3c) to unranged
    # tInt(8, unsigned), i.e. svBV8 — so `s[i] == 'c'` compares two svBV8
    # values via the existing path.
    #
    # SND-4: an out-of-range `i` (< 0 or >= s.len) is a REAL Nim `IndexDefect`
    # — deposit the OOB predicate into `strIndexOobConds` (mirroring the
    # `parseIntRaiseConds`/`divByZeroConds`/`overflowConds` lowering-sink →
    # drain-fork pattern; `drainStrIndexRaises`, folded into
    # `drainScalarRaiseForks`, forks the raise at the statement boundary).
    # The value computed below (`toCode(at(...))` — which, per Z3 spec,
    # degenerates an OOB `i` to the empty string / -1 → BV8 0xFF) is left
    # UNCHANGED and is only ever OBSERVED on the in-bounds survivor path (the
    # OOB predicate's negation is asserted there via `defectSurvivorPc`).
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrAt")
    let idx = lower(env, e.strArgs[1])
    let idxZi = toZ3Int(idx)
    let strLenZi = len(recv.str)
    let inLoCond = idxZi >= mkInt(0)
    let inHiCond = idxZi < strLenZi
    let oob = not (inLoCond and inHiCond)
    strIndexOobConds.add oob
    syncStrIndexOobCond(oob)
    let code = toCode(at(recv.str, idxZi))
    liftBV(intToBv[8](code, Z3BitVec[8]), false)
  of iekStrSubstr:
    # Phase 15 S3. `s[a..b]` → Z3 `(seq.extract s a (b-a+1))` (substr's
    # (offset, length) convention). Byte-offset slice. The parser already
    # adjusted `..<` to an inclusive `b`. strArgs = [recv, lo, hi] (`substr`'s
    # one-bound overload: [recv, lo]). RFC-0005 S8g: the slice forks its
    # IndexDefect / RangeDefect, and `substr` clamps (below).
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrSubstr")
    # v66 (round-4 Slice A, CR-17 class): a slice BOUND that lowered as a
    # BITVECTOR (a free int param — BV64-allocated) would bridge via bv2int
    # into a String+Int+BV mixed query — EMPIRICALLY a Z3 non-terminator on
    # the UNSAT side (bisected while landing v66: `len(s[0 ..< i]) == i + 1`
    # with a BV-sorted `i` hung > 3 h; the identical query with an
    # Int-sorted bound decides instantly). Field-realistic bounds — `find`
    # results, `len` arithmetic, int literals — are Int-sorted and PROVE.
    # Decline the BV shape classified (Invariant 3); the Int-representation
    # pre-pass for string-adjacent int params is the recorded round-5 lift.
    # Bounds are lowered with an svInt PROTO so int LITERALS (and any
    # proto-adaptable expression) arrive Int-sorted; only a genuinely
    # BV-allocated variable ignores the proto and reaches the decline.
    #
    # Round-6 N31 (walker v100): the decline USED TO `raise` a
    # `SymexUnsupportedStringOpError` directly, which is exactly the
    # C-backend goto-exception hazard ADR-0023/SND-3 was written to ban from
    # `lower()` (see `loweringDidDegrade`'s doc comment and the CR-17(a)
    # ordering-comparison guard a few hundred lines up in runtime.nim, which
    # already uses the in-band pattern for the identical reason). A `raise`
    # reached from inside two or more nested `walkBlock` frames (e.g. this
    # closed form built for a scan loop sitting inside an explicit `block:`,
    # itself inside the proc body's own top-level block) is silently LOST by
    # Nim's C-backend goto-based unwind — `lower()` returns as if nothing
    # happened, no `SymexErrorInfo` is recorded, `w.sawUnknown` is never set,
    # and the caller's `seq[Path]` ends up with zero survivors for that
    # branch, which the walker then reports as genuine UNSAT rather than the
    # honest decline (container-verified: a two-hop literal-seeded local
    # feeding this closed form's counter, wrapped in a `block:`, made a
    # concretely-reachable post-block target report false `sxUnsat` on the
    # `c` backend). Fixed by degrading IN-BAND: record the classified error,
    # set the SND-1 taint signal, and return a fresh unconstrained `svString`
    # so the walk continues soundly — `drainPendingLowerEffects` (the
    # mandatory drain at every `lower()` call site inside `walk`) forks the
    # path `uncertain` and sets `w.sawUnknown` regardless of nesting depth,
    # so the verdict is now `sxUnknown` + `seUnsupportedStringOp` at ANY
    # nesting depth, exactly matching the shallow (unnested) case this
    # already worked for.
    #
    # CORRECTION (Round-6 N36, walker v101): the claim two lines above this
    # comment's PRIOR wording made — "degrading IN-BAND like every other
    # `lower()` site in this class" — was FALSE when N31 landed: this
    # `iekStrSubstr` site (and the unrelated CR-17(a) ordering-comparison
    # guard/`cmpString` fallback it drew the analogy from) were the ONLY
    # in-band string-family degrades at the time; every OTHER raw raise in
    # this file (`requireStr`, `needleAsStr`, the join/split/regex/bytes/
    # radix/case-fold arms, the "not modeled" catch-all — enumerated in
    # N36's handoff) was still a raw, unconverted `raise` carrying the exact
    # same hazard this comment describes. N36 (walker v101) closes that gap
    # for the WHOLE class at once — NOT by converting each of those sites
    # in-band the way this one is, but by catching every classified carrier
    # `lowerStrArm` can raise at the SINGLE call site in `lower`'s dispatch
    # (`degradeStrArm`, `runtime.nim`, immediately above `lower`'s
    # definition) — so the claim is now actually true, file-wide, though by
    # a different (chokepoint, not per-site) mechanism than this comment
    # originally implied.
    let intProto = some(SymVal(kind: svInt, zi: mkInt(0)))
    let loSV = lower(env, e.strArgs[1], intProto)
    # RFC-0005 S8g: `substr(s, first)` (the one-bound overload) has no
    # `last`; it is `high(s)`.
    let hiSV = if e.strArgs.len >= 3: lower(env, e.strArgs[2], intProto)
               else: SymVal(kind: svInt, zi: len(recv.str) - mkInt(1))
    if loSV.kind != svInt or hiSV.kind != svInt:
      lowerDegrade(seUnsupportedStringOp,
        "iekStrSubstr: slice bound lowered as " & plainEnglishSymValKind(loSV.kind) & "/" &
             plainEnglishSymValKind(hiSV.kind) & " — a bitvector-represented bound would bv2int-" &
             "bridge into Sequence theory, a Z3 non-termination shape " &
             "(CR-17 class; bounds from find/len/literals prove) " &
             "(→ sxUnknown, Invariant 3)")
      var fresh: seq[Z3Bool]
      return allocateSym(tString(), "__strSubstrBoundDegrade", fresh)
    let lo = loSV.zi
    let hi = hiSV.zi
    let lenS = len(recv.str)
    if e.strOp == "substr":
      # RFC-0005 S8g: `substr` CLAMPS (system.nim: `first = max(first, 0)`,
      # `L = max(min(last, high(s)) - first + 1, 0)`) and never raises:
      # `substr("abc", -2, 1) == "ab"`, `substr("abc", 1, 9) == "bc"`. It
      # was the raw Z3 extract, whose negative offset gives "" -- a false
      # `sxUnsat` for every target reachable through a clamped bound.
      let first = ite(lo < mkInt(0), mkInt(0), lo)
      let last = ite(hi < lenS - mkInt(1), hi, lenS - mkInt(1))
      let l0 = (last - first) + mkInt(1)
      let length = ite(l0 < mkInt(0), mkInt(0), l0)
      SymVal(kind: svString, str: substr(recv.str, first, length))
    else:
      # RFC-0005 S8g: `s[a .. b]` (system's `[]`(s, HSlice)) builds
      # `newString(L)` with `L = b - a + 1` a `Natural` -- `L < 0` raises
      # `RangeDefect` -- then copies `s[i + a]` for `i in 0 ..< L`, so an
      # out-of-bounds bound raises `IndexDefect` only when `L > 0` (an
      # empty slice reads nothing). It raised nothing at all: the Z3
      # extract clamped, so `s[1 .. 7]` of a 3-byte string was "bc".
      let length = (hi - lo) + mkInt(1)
      let idxOob = (length > mkInt(0)) and ((lo < mkInt(0)) or (hi >= lenS))
      strIndexOobConds.add idxOob
      syncStrIndexOobCond(idxOob)
      let negLen = length < mkInt(0)
      rangeDefectConds.add negLen
      syncRangeDefectCond(negLen)
      SymVal(kind: svString, str: substr(recv.str, lo, length))
  of iekStrContains:
    # Phase 15 S4. `s.contains(sub)` / `sub in s` → Z3 `(seq.contains s sub)`.
    # `sub in s` semchecks to `contains(s, sub)`; the parser's itString call-guard
    # routes BOTH to iekStrContains (NOT iekContains, the seq/table/set path).
    # strArgs = [recv, sub].
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrContains")
    # v65: char needle bridged via needleAsStr (s.contains('x') lowers svBV8).
    let sub = needleAsStr(lower(env, e.strArgs[1]), "iekStrContains")
    SymVal(kind: svBool, bo: contains(recv.str, sub))
  of iekStrStartsWith:
    # Phase 15 S4. `s.startsWith(prefix)` → Z3 `(seq.prefixof prefix s)`. nim-z3's
    # `startsWith(a, prefix)` arg order already matches Nim's `(s, prefix)`.
    # strArgs = [recv, prefix].
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrStartsWith")
    # v65: char needle bridged via needleAsStr (strutils has a char overload).
    let prefix = needleAsStr(lower(env, e.strArgs[1]), "iekStrStartsWith")
    SymVal(kind: svBool, bo: startsWith(recv.str, prefix))
  of iekStrEndsWith:
    # Phase 15 S4. `s.endsWith(suffix)` → Z3 `(seq.suffixof suffix s)`. nim-z3's
    # `endsWith(a, suffix)` arg order matches Nim's `(s, suffix)`.
    # strArgs = [recv, suffix].
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrEndsWith")
    # v65: char needle bridged via needleAsStr (strutils has a char overload).
    let suffix = needleAsStr(lower(env, e.strArgs[1]), "iekStrEndsWith")
    SymVal(kind: svBool, bo: endsWith(recv.str, suffix))
  of iekStrFind:
    # Phase 15 S4 (+ RFC-chapulin-hardening Q1, ADR-0025: optional 3rd `start`
    # operand). `s.find(sub)` / `s.find(sub, start)` (strutils.find) → Z3
    # `indexOf(s, sub[, start])` (`Z3_mk_seq_index`), the BYTE offset of the
    # first occurrence AT OR AFTER `start` (default 0), or -1 when absent.
    # Under the ≤0xFF byte-faithful constraint (ADR-0006) a Z3 position offset
    # equals a Nim byte index, so no codepoint adjustment is needed. The
    # absent case (-1) is a valid SMT integer, never a crash.
    # strArgs = [recv, sub] (2-arg form, offset-0 `indexOf` overload) OR
    # [recv, sub, start] (3-arg form, `start` toZ3Int'd — Q1's dependent-scan
    # closed form emits this arity to encode `find(s, delim, currentIndex)`).
    # Before Q1, a caller-written 3-arg `s.find(sub, start)` already parsed
    # (the strArgs-collection loop is arity-agnostic) but `start` was
    # SILENTLY DROPPED here — a latent unsoundness (wrong verdict, not even a
    # clean degrade) fixed as part of this same slice.
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrFind")
    # v65: char needle bridged via needleAsStr — `rest.find(']')` was the
    # first walker-backlog entry the round-3 Defect net caught in the field
    # (the real parseTftpUri).
    let sub = needleAsStr(lower(env, e.strArgs[1]), "iekStrFind")
    # RFC-0005 S8ag: a one-character literal needle -- every closed form
    # of the scan idiom (Q1's `tryRecognizeScanIdiom`, B3's
    # `tryRecognizeScanPairIdiom`, B4's `tryRecognizeAccumulatingScan`)
    # finds one, as does a caller's `s.find(':')` -- lowers to a fresh Int
    # with the split axioms (`lowerIndexSplit`, `indexSplitAxioms`), which
    # every query reaching it asserts (`indexSplitRoots`). The same value
    # in every model; Z3's own `str.indexof` ran out of 20M units on a
    # five-deep readCString chain the split decides in under 5M.
    # RFC-0005 S8au: every needle splits -- a literal of any length and a
    # computed one (`splitNeedle`; the axioms cover the empty needle and
    # the overlap of a longer one, `indexSplitAxioms`).
    let start = if e.strArgs.len >= 3: toZ3Int(lower(env, e.strArgs[2]))
                else: mkInt(0)
    SymVal(kind: svInt, zi: lowerIndexSplit(recv.str, splitNeedle(sub), start))
  of iekStrRfind:
    # RFC Cluster 3 M3. `s.rfind(sub)` (strutils.rfind) → Z3 `lastIndexOf(s,
    # sub)` (`Z3_mk_seq_last_index`), the BYTE offset of the LAST occurrence, or
    # -1 when absent — a near-clone of `iekStrFind` above, but native
    # `lastIndexOf` instead of `indexOf` (nim-z3 `src/z3/sequence.nim:199`, a
    # Sequence-theory primitive, not a bounded scan). Same byte-faithful
    # (ADR-0006) offset convention as `find`; strArgs = [recv, sub].
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrRfind")
    # v65: char needle bridged via needleAsStr (`hostPort.rfind(':')`).
    let sub = needleAsStr(lower(env, e.strArgs[1]), "iekStrRfind")
    # RFC-0005 S8au: split like `find` (`lowerIndexSplit`, `last`): the
    # last occurrence `s = pre ++ c ++ post` with no `c` past it. Z3's
    # `seq.last_indexof` and Nim's `rfind` agree, the empty needle
    # included (`len(s)`, probed on both Z3 versions).
    SymVal(kind: svInt, zi: lowerIndexSplit(recv.str, splitNeedle(sub),
                                            mkInt(0), last = true))
  of iekStrReplaceAll:
    # Phase 15 S5 / RFC-0005 S8c. `strutils.replace(s, sub, by)` replaces
    # EVERY occurrence (both overloads: `string` and `char` sub/by), so it is
    # Z3 `(seq.replace_all s sub by)` (`Z3_mk_seq_replace_all`). S8c deleted
    # the first-occurrence model the stdlib call used to reach (a false
    # verdict: `"foofoo".replace("foo","bar")` is `"barbar"`, not
    # `"barfoo"`) and the name-only `replaceAll` entry that reached this one
    # (Nim's stdlib has no `replaceAll`). strArgs = [recv, sub, by]; a `char`
    # sub/by is bridged to its 1-char string by `needleAsStr` (exact under
    # the byte-faithful domain), exactly as the `char` overload behaves.
    #
    # Operands are lowered BEFORE the version gate on both builds (RFC-0005
    # S5): `seZ3VersionMissing` is `dcFreshSymbol`, sound only if the decline
    # drops no operand raise fork.
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrReplaceAll")
    let old = needleAsStr(lower(env, e.strArgs[1]), "iekStrReplaceAll")
    let neu = needleAsStr(lower(env, e.strArgs[2]), "iekStrReplaceAll")
    if e.strArgs[1].kind == iekStrLit and e.strArgs[1].sval.len == 0:
      # strutils: `if subLen == 0: result = s` -- an empty `sub` returns the
      # receiver unchanged. Exact, and needs no Z3 op (so no version gate).
      # (SMT-LIB's `str.replace_all` agrees; Z3's first-occurrence `replace`
      # would PREPEND `by`.)
      recv
    else:
      when defined(z3WithSeqReplaceAll):
        SymVal(kind: svString, str: replaceAll(recv.str, old, neu))
      else:
        # The gate is absent (Z3 < 4.15.5 lacks `Z3_mk_seq_replace_all`):
        # raise SymexZ3VersionMissingError -> degradeStrArm -> a fresh,
        # per-read string + `seZ3VersionMissing` (Invariant 3 -- recorded,
        # never a silent first-occurrence fallback, never a crash).
        raise (ref SymexZ3VersionMissingError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
          msg: "strutils.replace (all occurrences) requires Z3 >= 4.15.5 " &
               "(Z3_mk_seq_replace_all absent without -d:z3WithSeqReplaceAll)")
  of iekStrJoin:
    # Phase 15 S5. `xs.join(sep)` → Z3 concat of `xs` with `sep` interleaved.
    # strArgs = [recv(seq[string]), sep]. Tractable only over a CONCRETE-length
    # seq (the split special cases produce one); a symbolic-length join would
    # need an unbounded fold — classified seZ3StringIncomplete.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svSeq and recv.seqElemTy.kind == itString,
      "iekStrJoin: receiver not svSeq[string]"
    let sep = lower(env, e.strArgs[1])
    requireStr(sep, "iekStrJoin")
    if getAstKind(recv.seqLen) != akNumeral: # [placeholder-audited]
      raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
        msg: "join over a symbolic-length seq[string] is not bounded-encodable " &
             "(general path → sxUnknown)")
    SymVal(kind: svString, str: joinStrSeq(recv, sep.str))
  of iekStrSplit:
    # Phase 15 S5. `s.split(sep)` → `seq[string]`. Two TRACTABLE special cases
    # only (the general symbolic path is a universal quantifier over a symbolic
    # seq — a Z3 string-solver hang risk — so it is classified, not encoded):
    #   (a) empty-sep: sep is the literal "" → `@[s]`, for ANY receiver.
    #       RFC-0005 S8g: this was a byte-wise split (`@["a","b","c"]`) and a
    #       decline for a symbolic receiver; Nim's `split` never matches an
    #       empty separator (`substrEq` of "" is false, strutils.nim:509-538),
    #       so the result is one part (probe: `"abc".split("") ==
    #       @["abc"]`, `"".split("") == @[""]`).
    #   (b) concrete-inline: receiver AND sep are string LITERALS → compute the
    #       Nim split and emit a concrete `svSeq` of literal parts. No quantifier.
    # Anything else (symbolic receiver or symbolic sep) → seZ3StringIncomplete.
    let recvIR = e.strArgs[0]
    let sepIR  = e.strArgs[1]
    if sepIR.kind == iekStrLit and sepIR.sval.len == 0:
      # (a) empty-sep: the one-element seq holding the receiver itself.
      let recvSym = lower(env, recvIR)
      requireStr(recvSym, "iekStrSplit")
      let arr = store(mkConstArray[Z3Int, Z3String](mkString("")), mkInt(0),
                      recvSym.str)
      SymVal(kind: svSeq, seqLen: mkInt(1), seqDataRaw: toAnyAst(arr),
             seqElemTy: tString())
    elif recvIR.kind == iekStrLit and sepIR.kind == iekStrLit:
      # (b) concrete-inline. Both sides literal → split in Nim, emit literals.
      let parts = recvIR.sval.split(sepIR.sval)
      # CR-11/CR-18: same cap guard as (a). A separator that appears rarely in a
      # large literal can still produce O(literal_len) parts — same DoS risk.
      let splitCap = currentMaxSplitParts
      if splitCap > 0 and parts.len > splitCap:
        raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
          msg: "concrete split produces " & $parts.len & " parts (cap=" &
               $splitCap & " maxSplitParts); classify sxUnknown to prevent " &
               "compile-time DoS from huge-literal Z3 store chain")
      mkConcreteStrSeq(parts)
    else:
      # (c) general symbolic path. The RFC's join(parts,sep)==s + universal
      # `not contains(parts[i],sep)` + seqLen<=maxSplitParts encoding is a
      # universal quantifier over a symbolic seq[string] — the biggest hang
      # risk in Cluster S. Conservatively classified rather than encoded
      # (ADR-0006, Invariant 3 — structured sxUnknown, never a hang).
      # RFC-0005 S5: lower receiver AND separator BEFORE declining -- the
      # kind is `dcFreshSymbol`, so neither operand's raise forks may be
      # dropped with the op (`s.split($(a div b))`).
      let recvSym = lower(env, recvIR)
      requireStr(recvSym, "iekStrSplit")
      let sepSym = lower(env, sepIR)
      requireStr(sepSym, "iekStrSplit")
      raise (ref SymexZ3StringIncompleteError)(  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
        msg: "general symbolic string.split is not bounded-encodable " &
             "(universal-quantifier hang risk; general path → sxUnknown)")
  of iekStrMatch, iekStrFindRe, iekStrCaptureRe:
    # Phase 15 S6b; RFC-0005 S8ay. Every `std/re` entry point but replace
    # (see `lowerRegexCall`); RFC-0005 S8bb: and a captures overload's
    # groups.
    lowerRegexCall(env, e)
  of iekStrReplaceRe:
    # Phase 15 S6b; RFC-0005 S8aw, S8ay. `s.replace(re"…", repl)`: every
    # leftmost non-overlapping PCRE match replaced, lowered by the walker
    # for the shapes `regexReplaceShape` accepts (see the S8aw block above
    # `lowerStrArm`), and RFC-0005 S8bb for every other pattern PCRE's
    # priority run reads (`regex_parser.replaceRunZ3`).
    #
    # RFC-0005 S5: operands lowered and the pattern parsed BEFORE any
    # decline -- `seZ3StringIncomplete` is `dcFreshSymbol`, so the decline
    # must drop no operand raise fork. RFC-0005 S8ay: a pattern PCRE
    # rejects is a `RegexError` raise (`regexRejected`), and the parser
    # lowers no `by` for it (`re` raises before `by` is evaluated).
    let sp = decodeRegexSpec(e.strOp)
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrReplaceRe")
    let pr = parseSpec(sp)
    if pr.status == psRejected:
      return regexRejected(pr.errMsg, svString)
    let repl = lower(env, e.strArgs[1])
    requireStr(repl, "iekStrReplaceRe")
    regexOutcomeGate(sp, pr)
    # RFC-0005 S8bb (item 6): every pattern the priority run reads. The
    # S8aw / S8ay shapes keep their lowering; any other (an alternation, an
    # anchor, a pattern that matches empty, a newline convention's dot) is
    # the run's (`regex_parser.replaceRunZ3`). Under a CRLF convention whose
    # bumpalong skip a match could observe, the occurrence is PCRE's
    # optimiser's call (`pcre_select.crlfSkipSeen`): a decline.
    let n = buildNfa(pr)
    let (isShape, sh) = regexReplaceShape(pr)
    if not isShape or crlfSkipSeen(n):
      let t = runTable(n)
      if not t.ok: regexDecline(sp, t.why)
      return SymVal(kind: svString,
                    str: replaceRunZ3(recv.str, repl.str, t, pr.nl,
                                      regexFreshName))
    let lenS = simplify(len(recv.str))
    if isNumeralAst(lenS.ctx, lenS.raw):
      let n = parseInt(getNumeralString(lenS))
      if n <= regexReplaceMaxKnown:
        return SymVal(kind: svString,
                      str: regexReplaceUnrolled(recv.str, repl.str, sh, n))
    # RFC-0005 S8ay (item 5): length not a known numeral -- the exact value
    # by structural recursion over the receiver's suffixes
    # (`regexReplaceRec`), untainted. S8aw unrolled 16 positions and gave a
    # receiver longer than that a fresh string (`seZ3StringIncomplete`), so
    # every claim past 16 bytes was a replay-gated candidate and no UNSAT
    # there was possible. Measured on both pinned Z3 builds (the S8ay
    # "As landed" table); a query Z3 leaves undecided is `beSolverUndef`,
    # never a wrong verdict.
    SymVal(kind: svString, str: regexReplaceRec(recv.str, repl.str, sh))
  of iekStrConcat:
    # Phase 15 S8. `a & b` → Z3 `(seq.++ a b)` (`Z3_mk_seq_concat`), exposed by
    # nim-z3 as `concat` on `Z3String`. Both operands lower to svString (a string
    # literal operand lowers via the iekStrLit → mkString path). Byte-faithful
    # (ADR-0006): concat is byte-wise, so the result length is additive.
    # strArgs = [lhs, rhs].
    let l = lower(env, e.strArgs[0])
    requireStr(l, "iekStrConcat")
    # RFC-0005 S8p: the right operand may be a char (`s.add('z')`), the
    # 1-byte string with that byte (`needleAsStr`, exact under ADR-0006).
    let r = lower(env, e.strArgs[1])
    SymVal(kind: svString, str: concat(l.str, needleAsStr(r, "iekStrConcat")))
  of iekIntToStr:
    # Phase 15 S10a. `$n` (system.`$` on an int) → Z3 `(str.from-int n)`
    # (`Z3_mk_int_to_str`), exposed by nim-z3 as `toStr` on `Z3Int`. Result is a
    # decimal-string svString. (Z3's `int.to.str` is the empty string for a
    # negative `n`; the digits-path SUTs use non-negative `n`.) strArgs = [n].
    let operand = lower(env, e.strArgs[0])
    # An int param is a BV under the abstraction layer (ADR-0001), so coerce to
    # Z3Int via `toZ3Int` (svInt passes through; a BV lifts via bv2int). The
    # surrounding `$n == "lit"` is an equality goal (low F5 mixed-theory hang
    # risk — F5's pathology was ORDERING goals over int2bv(bv2int(x))).
    SymVal(kind: svString, str: toStr(toZ3Int(operand)))
  of iekStrToInt:
    # Phase 15 S10a + S10b. `parseInt(s)` — both the DIGITS-PATH (S10a) and the
    # RAISES-PATH (S10b, now that E1–E6 shipped the exception walker).
    #
    # nim-z3 `toInt` (Z3 `Z3_mk_str_to_int`) returns the NON-NEGATIVE integer the
    # digits of `s` represent, or **−1** for a non-digit string (VERIFIED against
    # `_deps/z3/src/z3/strings.nim:126-128` — this CORRECTS the RFC/recon premise
    # that `str.to_int` is "unconstrained for non-digit"; it is the fixed value
    # −1). A Nim sign (`-` or, since RFC-0005 S8b, `+`) is non-digit, so the
    # sign is stripped first (`startsWith`, nim-z3's `Z3_mk_seq_prefix`):
    #   digitsVal = toInt(substr(s, signLen, len(s)-signLen))
    #   result    = ite(startsWith(s,"-"), -digitsVal, digitsVal)
    #
    # RAISES-PATH (S10b; RFC-0005 S7 completed it). `parseInt(s)` is an
    # EXPRESSION (→ int), but Nim's runtime RAISES `ValueError` when `s` is not
    # a valid integer. `lower` cannot itself route a raise (it has no
    # WalkCtx/Path), so the predicate is surfaced to the enclosing statement
    # walk via the `parseIntRaiseConds` sink; the statement arm drains it and
    # forks a RAISES sub-path (routed via E3's `routeRaise`) and a DIGITS
    # sub-path (constrained by the negation, continuing with this int value).
    # Before RFC-0005 S7 part of the predicate was a "digits gate" pushed into
    # a pool asserted into EVERY solver check (both false `sxUnsat`s). strArgs
    # = [s].
    #
    # RFC-0005 S8b: the model is now `parseutils.rawParseInt` + strutils'
    # `L == s.len` check, verbatim, for every string with no `_`:
    #   * ONE optional sign, `+` or `-` (a `+` was treated as a non-digit,
    #     so the digits continuation dropped every `"+5"` -- a false
    #     `sxUnsat` for a target reachable only through the sign);
    #   * then one or more digits and nothing else (no whitespace, no second
    #     sign: `str.to_int` of the unsigned remainder is -1 otherwise, and
    #     of "" too, so a lone sign raises);
    #   * the value must fit `int` (= `BiggestInt`, 64-bit) with Nim's
    #     asymmetric bound -- `-9223372036854775808` parses,
    #     `9223372036854775808` raises ("Parsed integer outside of valid
    #     range"; it was an unbounded Int that never raised).
    # A `_` is a digit separator after the first digit. Its VALUE needs
    # `str.replace_all`, which not every supported Z3 has (`replaceAll`'s
    # version gate), so a `_`-string is the `lax` half: it both raises and
    # continues, each on a `seParseIntLaxSyntax`-tainted path, and the
    # continuation's value is a FRESH Int (`dcFreshSymbol`: every value Nim
    # can produce is a model of it) -- a replay-gated candidate, never a
    # dropped input.
    let s = lower(env, e.strArgs[0])
    requireStr(s, "iekStrToInt")
    let sLen = len(s.str)
    let isNeg = startsWith(s.str, mkString("-"))
    let isPlus = startsWith(s.str, mkString("+"))
    let signLen = ite(isNeg or isPlus, mkInt(1), mkInt(0))
    let digitsVal = toInt(substr(s.str, signLen, sLen - signLen))
    # `mkInt` is `cint`-ranged; the 64-bit bounds need `mkBigInt`.
    let outOfRange = ite(isNeg, digitsVal > mkBigInt("9223372036854775808"),
                         digitsVal > mkBigInt($high(int64)))
    let parseIntRaiseCond = (digitsVal < mkInt(0)) or outOfRange
    let laxSyntax = contains(s.str, mkString("_"))
    let laxValue = mkIntVar(freshDegradeName("__parseIntLaxValue"))
    let resultInt = ite(laxSyntax, laxValue,
                        ite(isNeg, -digitsVal, digitsVal))
    # RFC-0005 S10 / S8b: split by where the model is Nim's (`ParseIntRaise`).
    let parseIntRaise = ParseIntRaise(exact: parseIntRaiseCond and not laxSyntax,
                                      lax: laxSyntax)
    parseIntRaiseConds.add parseIntRaise              # threadvar fallback
    syncParseIntRaiseCond(parseIntRaise)              # CR-9 Stage 6 Group-2
    SymVal(kind: svInt, zi: resultInt)
  of iekRadixFmt:
    # Phase 16 A8. `toHex(x)` / `toBin(x, len)` for fixed-width BV int operands.
    # The strOp field is "<name>:<base>:<numDigits>", e.g. "toHex:16:2" (uint8
    # full-width hex) or "toBin:2:8" (8-bit binary). MS digit first. Raw
    # two's-complement bits (toHex(-1'i8) == "FF" — no sign handling, unsigned BV
    # interpretation). Invariant 3: non-BV operands degrade soundly.
    #
    # ENCODING: per digit position, extract a radix-slice via lshr+and, widen
    # to BV18 (Z3's Unicode char width = UnicodeCharWidth = 18), compute the
    # ASCII codepoint via a SINGLE 2-way ITE, wrap as a Z3Char, then produce a
    # length-1 Z3String via mkSeqUnit. Concat all positions.
    #
    #   hex: ite(bvult(nibble18, 10), nibble18+48, nibble18+55)
    #         48 = ord('0'), 55 = ord('A')-10 → maps 10..15 → 'A'..'F'
    #   bin: nibble18 + 48  (no ITE; nibble ∈ {0,1} so only '0' or '1')
    #
    # Advantage over a 16-way ITE table: only 1 ITE per digit (4 for uint16 hex
    # vs 64 in the previous design). Z3 trivially decomposes
    #   concat(unit(c0), unit(c1), …) == "00FF"
    # into cI == char_literal_I, then cI == mkChar(BV18_I), then BV18_I == ascii,
    # then BV nibble constraint — all decidable in BV theory with no String-theory
    # search over ITE branches.
    let colonPos1 = e.strOp.find(':')
    let colonPos2 = e.strOp.rfind(':')
    let base         = parseInt(e.strOp[colonPos1 + 1 ..< colonPos2])
    let numDigits    = parseInt(e.strOp[colonPos2 + 1 ..< e.strOp.len])
    let bitsPerDigit = if base == 16: 4 else: 1
    let operand = lower(env, e.strArgs[0])
    if operand.kind notin {svBV8, svBV16, svBV32, svBV64}:
      raise (ref SymexUnsupportedStringOpError)(op: e.strOp,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
        msg: "iekRadixFmt: operand must lower to a fixed-width BV; " &
             "got kind=" & plainEnglishSymValKind(operand.kind) & " (→ sxUnknown, Invariant 3)")
    var acc: Z3String
    var accInit = false
    for i in 0 ..< numDigits:
      let shift   = (numDigits - 1 - i) * bitsPerDigit
      let maskVal = if base == 16: 0xF else: 1
      # Extract the i-th radix slice and widen to BV18 (Z3 Unicode char width).
      # lshr shifts the target slice to the LSB; `and mask` zeroes higher bits.
      let nibble18 = case operand.kind
        of svBV8:
          let n = lshr(operand.bv8,  mkBitVec[8](shift))  and mkBitVec[8](maskVal)
          zeroExtend(n, 10)              # BV8  + 10 zero bits = BV18
        of svBV16:
          let n = lshr(operand.bv16, mkBitVec[16](shift)) and mkBitVec[16](maskVal)
          zeroExtend(n, 2)               # BV16 + 2  zero bits = BV18
        of svBV32:
          let n = lshr(operand.bv32, mkBitVec[32](shift)) and mkBitVec[32](maskVal)
          extract(n, 17, 0)              # take low 18 bits of BV32 = BV18
        of svBV64:
          let n = lshr(operand.bv64, mkBitVec[64](shift)) and mkBitVec[64](maskVal)
          extract(n, 17, 0)              # take low 18 bits of BV64 = BV18
        else: mkBitVec[18](0)            # unreachable (guard above)
      # ASCII codepoint as BV18.
      let ascii18 =
        if base == 2:
          # Binary: nibble ∈ {0,1} → '0'/'1' — no branch needed.
          nibble18 + 48
        else:
          # Hex: nibble ∈ [0..15] → '0'..'9' or 'A'..'F'.
          ite(bvult(nibble18, mkBitVec[18](10)),
              nibble18 + 48,             # '0'..'9': 48+0..48+9
              nibble18 + 55)             # 'A'..'F': 55+10=65..55+15=70
      let charStr = mkSeqUnit(mkChar(ascii18))
      if not accInit:
        acc = charStr
        accInit = true
      else:
        acc = concat(acc, charStr)
    SymVal(kind: svString, str: acc)
  of iekStrToLower, iekStrToUpper:
    # Phase 16 A9. `toLowerAscii(s)` / `toUpperAscii(s)` via a direct-body
    # seqMap over the Z3Seq[Z3Char] (ADR-0015). Each char element x is bridged
    # to a BV18, transformed by a 2-way ITE (the exact ASCII fold rule), then
    # wrapped back as a Z3Char. The lambda body is quantifier-free: no ∀, no
    # uninterpreted function, no hang (proven by the A9 feasibility probe).
    #
    # toLower: ite( 65 ≤ x ≤ 90,  x+32, x )  ('A'..'Z' → 'a'..'z')
    # toUpper: ite( 97 ≤ x ≤ 122, x-32, x )  ('a'..'z' → 'A'..'Z')
    #
    # Bytes ≥ 0x80 and non-letter bytes pass through unchanged (ITE else branch).
    # Non-svString operand → classified seUnsupportedStringOp (Invariant 3).
    let recv = lower(env, e.strArgs[0])
    if recv.kind != svString:
      raise (ref SymexUnsupportedStringOpError)(op: e.strOp,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
        msg: e.strOp & ": operand must lower to svString; " &
             "got kind=" & plainEnglishSymValKind(recv.kind) & " (→ sxUnknown, Invariant 3)")
    # Build bound variable x: Z3Char (fresh zero-arity constant for seqMapBody).
    let x = mkCharVar("casefold_x")
    let xBv = x.toBitVec          # Z3BitVec[18] (UnicodeCharWidth = 18)
    let body =
      if e.kind == iekStrToLower:
        # ASCII 65..90 → 'A'..'Z'; add 32 to fold to lowercase 'a'..'z'.
        let inRange = bvuge(xBv, 65) and bvule(xBv, 90)
        mkChar(ite(inRange, xBv + 32, xBv))
      else:
        # ASCII 97..122 → 'a'..'z'; subtract 32 to fold to uppercase 'A'..'Z'.
        let inRange = bvuge(xBv, 97) and bvule(xBv, 122)
        mkChar(ite(inRange, xBv - 32, xBv))
    SymVal(kind: svString, str: seqMapBody(x, body, recv.str))
  of iekRuneToStr:
    # Phase 16 A7-S2. `$r` where r: Rune → UTF-8 byte string via runeToUtf8Sym.
    # The operand is normally svInt (Z3Int codepoint, pinned [0,0x10FFFF] by S1).
    # However, when `r` appears in an expression containing a `bAnd`/`bOr` node
    # (e.g. `$r == "A" and r.ord > 0x42`), the abstraction layer's
    # collectBanFromExpr fires on the boolean `and` (bAnd ∈ BitTwiddlingOps) and
    # marks `r` as BV-only. In that case the operand lowers to svBV32/svBV64.
    # toZ3Int handles both svInt (identity) and svBV (bv2int unsigned) correctly.
    # runeToUtf8Sym only uses Z3Int arithmetic (div/mod), so the conversion is
    # semantics-preserving for the non-negative Rune range.
    let operand = lower(env, e.strArgs[0])
    SymVal(kind: svString, str: runeToUtf8Sym(toZ3Int(operand)))
  of iekStrStrip:
    # Round-4 Slice B (ADR-0026): `strip(s, leading, trailing, chars)` as
    # quantifier-free DECOMPOSITION constraints over fresh strings — see
    # `stripDecompConds`' doc (runtime.nim) for the full soundness/
    # completeness/uniqueness argument. `e.strOp` = "<flags>:<chars>" with
    # flags ⊆ {L, T} ("-" when both false) and `chars` the literal
    # stripped-char set, both extracted at parse time.
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrStrip")
    let colonIx = e.strOp.find(':')
    doAssert colonIx >= 0, "iekStrStrip: malformed spec (parser bug)"
    let flags = e.strOp[0 ..< colonIx]
    let chars = e.strOp[colonIx + 1 .. ^1]
    let leading = 'L' in flags
    let trailing = 'T' in flags
    if (not leading and not trailing) or chars.len == 0:
      recv                       # strip(false, false, …) / empty set = identity
    else:
      inc stripSynthCounter
      let tag = "__strip" & $stripSynthCounter
      # Fresh byte-faithful strings (allocateSym's itString arm adds the
      # ADR-0006 ≤0xFF char-range membership into `alloc`).
      var alloc: seq[Z3Bool]
      let coreSV = allocateSym(tString(), tag & "_core", alloc)
      let preSV  = allocateSym(tString(), tag & "_pre",  alloc)
      let sufSV  = allocateSym(tString(), tag & "_suf",  alloc)
      let (core, pre, suf) = (coreSV.str, preSV.str, sufSV.str)
      # (union chars)* — a finite union of single-char literal regexes.
      var charRes: seq[Z3Regex[Z3String]]
      for c in chars:
        charRes.add mkRegex(mkString($c))
      let charsStar = star(if charRes.len == 1: charRes[0]
                           else: union(charRes))
      var conds = alloc
      conds.add recv.str == concat(pre, concat(core, suf))
      if leading: conds.add matches(pre, charsStar)
      else:       conds.add pre == mkString("")
      if trailing: conds.add matches(suf, charsStar)
      else:        conds.add suf == mkString("")
      # Maximality: core is empty, or its stripped-side boundary chars are
      # NOT in the stripped set (finite conjunction over the literal set).
      var boundaryOk = mkBool(true)
      for c in chars:
        if leading:
          boundaryOk = boundaryOk and (not startsWith(core, mkString($c)))
        if trailing:
          boundaryOk = boundaryOk and (not endsWith(core, mkString($c)))
      conds.add (core == mkString("")) or boundaryOk
      for c in conds:
        stripDecompConds.add c
      coreSV
  of iekStrInOptionRegion:
    # Round-6 N21 fix (walker v95 — CRITICAL soundness correction of the B6
    # region grammar). Boolean predicate `s[start .. bound-1] ∈ REGION`
    # where REGION is the pair-loop's ACTUAL clean-termination language, not
    # bare segment-star membership:
    #   PAIR   = (nonzero)+ "\0" (nonzero)* "\0"
    #   REGION = PAIR* ( "\0" anybyte* )?
    # i.e. zero or more complete (non-empty-key, possibly-empty-value) pairs,
    # OPTIONALLY followed by a lone empty-key terminator NUL with everything
    # after it unconstrained (the loop never reads past a `break`). The OLD
    # grammar here (pre-v95) was `((nonzero)* "\0")*` — plain NUL-delimited
    # segment-star with NO parity tie to how the real loop consumes the
    # region two segments (key, value) at a time. That let an ODD number of
    # segments with a non-empty final segment (e.g. `"aa\x00bb\x00cc\x00"`)
    # wrongly certify as a member: the real SUT reads key "cc" at the top of
    # an incomplete third pair, landing the offset exactly at `bound`, and
    # the VALUE read that follows immediately raises `ScanError`
    # ("unterminated") — a real, container-confirmed defect the old grammar
    # asserted was impossible (N21, `tests/tsymex_r6_n21_pairloop_member.nim`).
    #
    # Both of the real loop's clean-exit shapes are represented, neither
    # privileged: (a) the counter lands EXACTLY on `bound` after a whole
    # number of complete pairs — the `while i < bound` guard itself goes
    # false, no `break`/terminator needed (`PAIR*` alone, the OPTIONAL
    # suffix matching zero-width); (b) an empty-key segment triggers `break`
    # before `bound` is necessarily reached — `PAIR*` followed by the
    # optional lone terminator NUL, with the unconsumed remainder (never
    # read by the real loop) matched by an unconstrained `anybyte*` tail.
    # STAR (not PLUS) for a PAIR's own inner value segment, same round-2
    # depth reasoning the old grammar already established: `readCString`
    # returns "" freely, so a pair's VALUE may be empty — only the KEY half
    # of a pair must be non-empty (an empty key is precisely what routes to
    # the terminator alternative instead of forming another pair).
    #
    # Built from the SAME nim-z3 regex primitives the old grammar used
    # (`range`/`star`/`concat`/`matches`, `z3/regex` — the machinery
    # `iekStrStrip` already uses for `(union chars)*`), plus `plus` (the
    # key's non-emptiness) and `option` (the trailing terminator+tail is
    # OPTIONAL). `strArgs = [recv, start, bound]`; `strOp` unused. Only
    # emitted by `tryRecognizePairLoopIdiom`'s closed-form replacement —
    # never from ordinary Nim source — so `start`/`bound` are always the
    # SAME `boundIsScannedLen`-checked pair B0/B3/B4 already require (a
    # syntactic `<s>`'s own `.len` and the loop's own index symbol),
    # reusing `iekStrSubstr`'s CR-17 Int-sortedness discipline: a
    # BV-represented operand declines classified rather than bv2int-
    # bridging into a Sequence-theory query (the CR-17 hang class).
    let recv = lower(env, e.strArgs[0])
    requireStr(recv, "iekStrInOptionRegion")
    let intProto = some(SymVal(kind: svInt, zi: mkInt(0)))
    let startSV = lower(env, e.strArgs[1], intProto)
    let boundSV = lower(env, e.strArgs[2], intProto)
    if startSV.kind != svInt or boundSV.kind != svInt:
      raise (ref SymexUnsupportedStringOpError)(op: "iekStrInOptionRegion",  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
        msg: "iekStrInOptionRegion: start/bound lowered as " &
             plainEnglishSymValKind(startSV.kind) & "/" & plainEnglishSymValKind(boundSV.kind) & " — a bitvector-" &
             "represented operand would bv2int-bridge into Sequence " &
             "theory, a Z3 non-termination shape (CR-17 class) " &
             "(→ sxUnknown, Invariant 3)")
    let tail = substr(recv.str, startSV.zi, boundSV.zi - startSV.zi)
    let nonzero = range(mkString("\x01"), mkString("\xff"))
    let anybyte = range(mkString("\x00"), mkString("\xff"))
    let terminator = mkRegex(mkString("\x00"))
    let pair = concat(plus(nonzero), terminator, star(nonzero), terminator)
    let region = concat(star(pair), option(concat(terminator, star(anybyte))))
    # RFC-0005 S8aa: membership needs `start >= 0`. Z3's `str.substr` at a
    # negative offset is "", which `region` accepts (zero pairs), so a
    # negative start certified the loop defect-free -- while the real first
    # iteration reads `s[start]` and raises `IndexDefect` whenever
    # `start < s.len`. The member branch swallowed that raise, and the
    # fallback k-unroll never saw a negative start: `tIndexError` was
    # `sxUnknown` when the unroll budget ran out on the other fallback
    # paths, and a false `sxUnsat` when it did not (a bounded `s.len`). A
    # negative start now takes the fallback, whose first scan raises.
    SymVal(kind: svBool,
           bo: (startSV.zi >= mkInt(0)) and matches(tail, region))
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrRfind, iekStrReplaceAll,
                   iekStrSplit, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe, iekStrCaptureRe,
                   iekStrConcat,
                   iekIntToStr, iekStrToInt, iekRadixFmt,
                   iekStrToLower, iekStrToUpper, iekRuneToStr, iekStrStrip,
                   iekStrInOptionRegion}:
    # Phase 15: string ops not modeled in this cycle. Raise a classified
    # SymexUnsupportedStringOpError; the runSymex boundary maps it to sxUnknown +
    # seUnsupportedStringOp (ADR-0006, Invariant 3 — never a crash/silent UNSAT).
    # S6–S11 replace these with the real Z3 String/Seq/Regex lowering.
    if e.kind == iekStrUnsupported and e.strOp.startsWith("regex:"):
      return lowerRegexDecline(env, e)   # RFC-0005 S8ay
    let opName = if e.strOp.len > 0: e.strOp else: $e.kind
    raise (ref SymexUnsupportedStringOpError)(op: opName,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36)]
      msg: "string op `" & opName & "` is not modeled until its Cluster-S cycle")
  else:
    # N46 (round-6 re-review, ADR-0023/SND-3 class widening): was a bare
    # `raise newException(ValueError, ...)` -- category (c) TODAY (`lower`'s
    # own dispatch only calls `lowerStrArm` for `e.kind` values already
    # inside `{iekStrLit} + StrOpKinds`, a caller-contract invariant this
    # arm cannot violate given that contract), but fragile: unlike its two
    # siblings in this same proc (immediately above), a bare `ValueError`
    # is NOT one of the six carrier types `degradeStrArm`'s catch chain
    # (runtime.nim) actually catches -- if `StrOpKinds`/`lower()`'s
    # dispatch set ever drift out of sync, this site would silently regain
    # live-hazard status with no test signal from the chokepoint mechanism.
    # Hardened for defense-in-depth: route through the SAME classified
    # carrier + chokepoint its siblings use, rather than a bare exception
    # type the chokepoint does not recognize.
    raise (ref SymexUnsupportedStringOpError)(op: $e.kind,  # [raise-audited: converted-at-chokepoint -- caught by degradeStrArm at lower()'s lowerStrArm(env, e) call site (runtime.nim, N36); hardened N46 from a bare ValueError the chokepoint's catch list did not cover]
      msg: "lowerStrArm: unexpected e.kind=" & $e.kind &
           " (not iekStrLit or StrOpKinds)")
