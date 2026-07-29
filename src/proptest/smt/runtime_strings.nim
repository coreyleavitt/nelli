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
  let n = parseInt(getNumeralString(parts.seqLen))
  let typed = wrap[Z3Array[Z3Int, Z3String]](
    parts.seqDataRaw.ctx, parts.seqDataRaw.raw)
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

proc lowerStrArm(env: Env, e: IRExpr): SymVal =
  ## Stage 7 (CR-7) Cluster S extraction. Called from `lower`'s case arm for
  ## `iekStrLit` and `StrOpKinds`. Params: `env` and `e` are the same as
  ## `lower`'s; `proto` is NOT used by any string arm. Calls `lower`
  ## recursively (forward-declared above).
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   mkString, mkInt, at, toCode, substr, contains, startsWith, endsWith,
  ##   indexOf, replace, replaceAll, joinStrSeq, mkConcreteStrSeq,
  ##   parseNimRegexToZ3Regex, intToBv, mkConstArray, store, toStr, toInt,
  ##   ite, len, concat, liftBV, toZ3Int, syncParseIntRaiseCond,
  ##   syncParseIntGateConstraint, parseIntGateConstraints, parseIntRaiseConds,
  ##   syncStrIndexOobCond, strIndexOobConds,
  ##   currentMaxBytesEncodingLen,
  ##   SymexUnsupportedStringOpError, SymexZ3StringIncompleteError,
  ##   SymexZ3VersionMissingError, SymexBytesSymbolicLengthError,
  ##   SymexBytesLengthTooLargeError, SymexUnsupportedRegexError, StrOpKinds
  case e.kind
  of iekStrLit:
    SymVal(kind: svString, str: mkString(e.sval))
  of iekStrLen:
    # Phase 15 S3. `s.len` → Z3 `(str.len s)`. Under the ≤0xFF byte-faithful
    # constraint (asserted at allocation, ADR-0006) the Z3 character count
    # equals the Nim byte length, so this is exact.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrLen: receiver not svString"
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
    doAssert recv.kind == svString, "iekStrAt: receiver not svString"
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
    # (offset, length) convention). Byte-offset slice; out-of-range yields the
    # empty string (Z3 spec). The parser already adjusted `..<` to an inclusive
    # `b`. strArgs = [recv, lo, hi].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrSubstr: receiver not svString"
    let lo = toZ3Int(lower(env, e.strArgs[1]))
    let hi = toZ3Int(lower(env, e.strArgs[2]))
    let length = (hi - lo) + mkInt(1)
    SymVal(kind: svString, str: substr(recv.str, lo, length))
  of iekStrContains:
    # Phase 15 S4. `s.contains(sub)` / `sub in s` → Z3 `(seq.contains s sub)`.
    # `sub in s` semchecks to `contains(s, sub)`; the parser's itString call-guard
    # routes BOTH to iekStrContains (NOT iekContains, the seq/table/set path).
    # strArgs = [recv, sub].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrContains: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrContains: arg not svString"
    SymVal(kind: svBool, bo: contains(recv.str, sub.str))
  of iekStrStartsWith:
    # Phase 15 S4. `s.startsWith(prefix)` → Z3 `(seq.prefixof prefix s)`. nim-z3's
    # `startsWith(a, prefix)` arg order already matches Nim's `(s, prefix)`.
    # strArgs = [recv, prefix].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrStartsWith: receiver not svString"
    let prefix = lower(env, e.strArgs[1])
    doAssert prefix.kind == svString, "iekStrStartsWith: arg not svString"
    SymVal(kind: svBool, bo: startsWith(recv.str, prefix.str))
  of iekStrEndsWith:
    # Phase 15 S4. `s.endsWith(suffix)` → Z3 `(seq.suffixof suffix s)`. nim-z3's
    # `endsWith(a, suffix)` arg order matches Nim's `(s, suffix)`.
    # strArgs = [recv, suffix].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrEndsWith: receiver not svString"
    let suffix = lower(env, e.strArgs[1])
    doAssert suffix.kind == svString, "iekStrEndsWith: arg not svString"
    SymVal(kind: svBool, bo: endsWith(recv.str, suffix.str))
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
    doAssert recv.kind == svString, "iekStrFind: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrFind: arg not svString"
    if e.strArgs.len >= 3:
      let start = lower(env, e.strArgs[2])
      SymVal(kind: svInt, zi: indexOf(recv.str, sub.str, toZ3Int(start)))
    else:
      SymVal(kind: svInt, zi: indexOf(recv.str, sub.str))
  of iekStrRfind:
    # RFC Cluster 3 M3. `s.rfind(sub)` (strutils.rfind) → Z3 `lastIndexOf(s,
    # sub)` (`Z3_mk_seq_last_index`), the BYTE offset of the LAST occurrence, or
    # -1 when absent — a near-clone of `iekStrFind` above, but native
    # `lastIndexOf` instead of `indexOf` (nim-z3 `src/z3/sequence.nim:199`, a
    # Sequence-theory primitive, not a bounded scan). Same byte-faithful
    # (ADR-0006) offset convention as `find`; strArgs = [recv, sub].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrRfind: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrRfind: arg not svString"
    SymVal(kind: svInt, zi: lastIndexOf(recv.str, sub.str))
  of iekStrReplace:
    # Phase 15 S5. `s.replace(old, new)` → Z3 `(seq.replace s old new)`
    # (`Z3_mk_seq_replace`), FIRST-occurrence semantics. strArgs = [recv, old,
    # new]. (Nim's `strutils.replace` is global, but the byte-faithful Z3 op
    # this cycle models is the first-occurrence primitive per the S5 spec.)
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrReplace: receiver not svString"
    let old = lower(env, e.strArgs[1])
    doAssert old.kind == svString, "iekStrReplace: `old` not svString"
    let neu = lower(env, e.strArgs[2])
    doAssert neu.kind == svString, "iekStrReplace: `new` not svString"
    SymVal(kind: svString, str: replace(recv.str, old.str, neu.str))
  of iekStrReplaceAll:
    # Phase 15 S5. `s.replaceAll(old, new)` → Z3 `(seq.replace_all s old new)`
    # (`Z3_mk_seq_replace_all`) — VERSION-GATED behind `-d:z3WithSeqReplaceAll`
    # (absent on Z3 < 4.15.5). The `replaceAll` proc only EXISTS when the gate
    # is defined, so the call MUST sit inside the `when` (an unguarded call
    # won't compile on a build without the symbol). On a build lacking the
    # gate, raise SymexZ3VersionMissingError → sxUnknown + seZ3VersionMissing
    # (Invariant 3 — classified, never a crash, never a silent UNSAT).
    when defined(z3WithSeqReplaceAll):
      let recv = lower(env, e.strArgs[0])
      doAssert recv.kind == svString, "iekStrReplaceAll: receiver not svString"
      let old = lower(env, e.strArgs[1])
      doAssert old.kind == svString, "iekStrReplaceAll: `old` not svString"
      let neu = lower(env, e.strArgs[2])
      doAssert neu.kind == svString, "iekStrReplaceAll: `new` not svString"
      SymVal(kind: svString, str: replaceAll(recv.str, old.str, neu.str))
    else:
      raise (ref SymexZ3VersionMissingError)(
        msg: "replaceAll requires Z3 >= 4.15.5 (Z3_mk_seq_replace_all absent " &
             "without -d:z3WithSeqReplaceAll)")
  of iekStrJoin:
    # Phase 15 S5. `xs.join(sep)` → Z3 concat of `xs` with `sep` interleaved.
    # strArgs = [recv(seq[string]), sep]. Tractable only over a CONCRETE-length
    # seq (the split special cases produce one); a symbolic-length join would
    # need an unbounded fold — classified seZ3StringIncomplete.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svSeq and recv.seqElemTy.kind == itString,
      "iekStrJoin: receiver not svSeq[string]"
    let sep = lower(env, e.strArgs[1])
    doAssert sep.kind == svString, "iekStrJoin: sep not svString"
    if getAstKind(recv.seqLen) != akNumeral:
      raise (ref SymexZ3StringIncompleteError)(
        msg: "join over a symbolic-length seq[string] is not bounded-encodable " &
             "(general path → sxUnknown)")
    SymVal(kind: svString, str: joinStrSeq(recv, sep.str))
  of iekStrSplit:
    # Phase 15 S5. `s.split(sep)` → `seq[string]`. Two TRACTABLE special cases
    # only (the general symbolic path is a universal quantifier over a symbolic
    # seq — a Z3 string-solver hang risk — so it is classified, not encoded):
    #   (a) empty-sep: sep is the literal "" → byte-faithful single-BYTE parts
    #       (`split("abc","") == @["a","b","c"]`), computed in Nim.
    #   (b) concrete-inline: receiver AND sep are string LITERALS → compute the
    #       Nim split and emit a concrete `svSeq` of literal parts. No quantifier.
    # Anything else (symbolic receiver or symbolic sep) → seZ3StringIncomplete.
    let recvIR = e.strArgs[0]
    let sepIR  = e.strArgs[1]
    if sepIR.kind == iekStrLit and sepIR.sval.len == 0:
      # (a) empty-sep. Byte-faithful: each Nim byte is one part. Requires the
      # receiver to be concrete so the byte list is known.
      if recvIR.kind != iekStrLit:
        raise (ref SymexZ3StringIncompleteError)(
          msg: "split with empty sep over a symbolic string is not bounded " &
               "(receiver is not a string literal; general path → sxUnknown)")
      var parts: seq[string]
      for b in recvIR.sval:           # iterate bytes
        parts.add $b
      # CR-11/CR-18: cap parts count. A huge literal (e.g. "x".repeat(10_000).split(""))
      # would emit 10_000+ Z3 store calls — compile-time DoS against the developer's
      # build. If the cap is set (>0) and exceeded, classify sxUnknown (seZ3StringIncomplete)
      # before emitting any Z3 stores. The cap now GATES the concrete-inline path.
      let splitCap = currentMaxSplitParts
      if splitCap > 0 and parts.len > splitCap:
        raise (ref SymexZ3StringIncompleteError)(
          msg: "split with empty sep produces " & $parts.len & " parts (cap=" &
               $splitCap & " maxSplitParts); classify sxUnknown to prevent " &
               "compile-time DoS from huge-literal Z3 store chain")
      mkConcreteStrSeq(parts)
    elif recvIR.kind == iekStrLit and sepIR.kind == iekStrLit:
      # (b) concrete-inline. Both sides literal → split in Nim, emit literals.
      let parts = recvIR.sval.split(sepIR.sval)
      # CR-11/CR-18: same cap guard as (a). A separator that appears rarely in a
      # large literal can still produce O(literal_len) parts — same DoS risk.
      let splitCap = currentMaxSplitParts
      if splitCap > 0 and parts.len > splitCap:
        raise (ref SymexZ3StringIncompleteError)(
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
      raise (ref SymexZ3StringIncompleteError)(
        msg: "general symbolic string.split is not bounded-encodable " &
             "(universal-quantifier hang risk; general path → sxUnknown)")
  of iekStrMatch:
    # Phase 15 S6b. `s.match(re"…")` / `s.contains(re"…")` → byte-faithful Z3
    # regex membership `matches(s, r)` (`Z3_mk_seq_in_re`) → svBool. The raw
    # `re"…"` pattern rides in `strOp`; S6a's parser translates it against the
    # CURRENT Z3 context (set in runSymexImpl). On a parser Err (backreference /
    # lookahead / named group / malformed) raise SymexUnsupportedRegexError →
    # sxUnknown + seUnsupportedRegex (Invariant 3 — never a silent UNSAT). The
    # ≤0xFF free-string constraint (S3) keeps membership in the byte alphabet,
    # so witnesses round-trip to Nim bytes; it did NOT hang (see S6b notes).
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrMatch: receiver not svString"
    let pr = parseNimRegexToZ3Regex(e.strOp)
    if not pr.isOk:
      raise (ref SymexUnsupportedRegexError)(msg: pr.error)
    SymVal(kind: svBool, bo: matches(recv.str, pr.regex))
  of iekStrFindRe:
    # Phase 15 S6b — DEFERRED. nim-z3 exposes no `indexOf`-on-regex API (only a
    # substring `indexOf`); a regex `find` byte-index has no direct Z3 primitive.
    # Classify seUnsupportedRegex (sxUnknown) rather than guess an unsound
    # encoding. The pattern is still parsed first so a malformed/rejected pattern
    # reports the precise S6a reason; a VALID pattern reports the deferral.
    let pr = parseNimRegexToZ3Regex(e.strOp)
    if not pr.isOk:
      raise (ref SymexUnsupportedRegexError)(msg: pr.error)
    raise (ref SymexUnsupportedRegexError)(
      msg: "regex find(s, re\"…\") is not modeled: nim-z3 has no " &
           "indexOf-on-regex API (documented S6b deferral)")
  of iekStrReplaceRe:
    # Phase 15 S6b. `s.replace(re"…", repl)` → Z3 `(seq.replace_re s r repl)`
    # (`Z3_mk_seq_replace_re`) — VERSION-GATED behind `-d:z3WithSeqReplaceRe`
    # (absent on this Z3 4.15.0 build). Identical gate shape to S5's replaceAll:
    # the `replaceRe` proc only EXISTS when the gate is defined, so the call MUST
    # sit inside the `when`. Without the gate → SymexZ3VersionMissingError →
    # sxUnknown + seZ3VersionMissing (Invariant 3 — classified, never a crash).
    when defined(z3WithSeqReplaceRe):
      let recv = lower(env, e.strArgs[0])
      doAssert recv.kind == svString, "iekStrReplaceRe: receiver not svString"
      let repl = lower(env, e.strArgs[1])
      doAssert repl.kind == svString, "iekStrReplaceRe: replacement not svString"
      let pr = parseNimRegexToZ3Regex(e.strOp)
      if not pr.isOk:
        raise (ref SymexUnsupportedRegexError)(msg: pr.error)
      SymVal(kind: svString, str: replaceRe(recv.str, pr.regex, repl.str))
    else:
      raise (ref SymexZ3VersionMissingError)(
        msg: "regex replace requires Z3 >= 4.15.5 (Z3_mk_seq_replace_re absent " &
             "without -d:z3WithSeqReplaceRe)")
  of iekStrBytes:
    # Phase 15 S7a. `bytes(s)` byte-faithful byte-view. Under the byte-faithful
    # model (ADR-0006), every Z3 string character is ALREADY a single byte (≤0xFF
    # constrained at allocation, S3), so the byte count == char count and this is
    # the TRIVIAL identity view — NOT a multi-byte UTF-8 decode. We materialise a
    # concrete-length `svSeq` of `svBV8`, one element per character position,
    # reusing S3's exact at→toCode→BV8 bridge:
    #   bytes[i] == intToBv[8](toCode(at(s, i)))
    # `seBytesBeyondBMP` is UNREACHABLE here: a free char is ≤0xFF by construction
    # and a literal char is a raw byte 0..255, so toCode always fits BV8 — no
    # multi-byte branch is ever needed. (Omitted as an error kind for that reason.)
    #
    # Concreteness is detected at the IR level (mirroring S5's split): a string
    # LITERAL receiver (`iekStrLit`) has a statically-known byte count; anything
    # else (a bare `string` parameter, a symbolic result) has a symbolic length
    # with no bounded element chain → seBytesSymbolicLength (Invariant 3).
    let recvIR = e.strArgs[0]
    if recvIR.kind != iekStrLit:
      raise (ref SymexBytesSymbolicLengthError)(
        msg: "bytes() over a symbolic-length string is not bounded-encodable " &
             "(receiver is not a string literal; general path → sxUnknown)")
    let concreteLen = recvIR.sval.len   # byte count == char count (byte-faithful)
    if concreteLen > currentMaxBytesEncodingLen:
      raise (ref SymexBytesLengthTooLargeError)(
        msg: "bytes() concrete length " & $concreteLen & " exceeds " &
             "maxBytesEncodingLen=" & $currentMaxBytesEncodingLen &
             " (general path → sxUnknown)")
    # Build the svSeq of BV8 via the at→toCode→BV8 bridge over the literal's Z3
    # string. A const array defaulting to 0 (unstored slots are never read —
    # access is len-bounded), `store`ing each byte at its index; seqLen pinned to
    # concreteLen (EQUAL to len(s), not >=).
    let recvStr = mkString(recvIR.sval)
    var arr = mkConstArray[Z3Int, Z3BitVec[8]](mkBitVec[8](0))
    for i in 0 ..< concreteLen:
      let b = intToBv[8](toCode(at(recvStr, mkInt(i))), Z3BitVec[8])
      arr = store(arr, mkInt(i), b)
    SymVal(kind: svSeq, seqLen: mkInt(concreteLen),
           seqDataRaw: toAnyAst(arr),
           seqElemTy: tInt(8, signed = false))
  of iekStrConcat:
    # Phase 15 S8. `a & b` → Z3 `(seq.++ a b)` (`Z3_mk_seq_concat`), exposed by
    # nim-z3 as `concat` on `Z3String`. Both operands lower to svString (a string
    # literal operand lowers via the iekStrLit → mkString path). Byte-faithful
    # (ADR-0006): concat is byte-wise, so the result length is additive.
    # strArgs = [lhs, rhs].
    let l = lower(env, e.strArgs[0])
    doAssert l.kind == svString, "iekStrConcat: lhs not svString"
    let r = lower(env, e.strArgs[1])
    doAssert r.kind == svString, "iekStrConcat: rhs not svString"
    SymVal(kind: svString, str: concat(l.str, r.str))
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
    # −1). Nim negatives have a leading `-`, which is non-digit (so bare `toInt`
    # gives −1), so we fork on `startsWith(s, "-")` (nim-z3's `Z3_mk_seq_prefix`;
    # the RFC named this `prefixOf` — the real proc is `startsWith(a, prefix)`):
    #   posVal   = toInt(s)                          (no leading '-')
    #   negInner = toInt(substr(s, 1, len(s)-1))     (digits after the '-')
    #   result   = ite(startsWith(s,"-"), -negInner, posVal)
    #
    # DIGITS GATE — negative branch ONLY. The positive branch needs NO gate: Z3's
    # `toInt` already returns the faithful value (true digits, or −1 for non-digit
    # — exactly Z3's honest model). The negative branch DOES need a gate: if the
    # suffix after `-` is non-digit, `negInner` is −1 and `-negInner` would be a
    # FALSE `+1`. So gate `isNeg ⇒ negInner >= 0` (`(not isNeg) or negInner>=0`),
    # threaded into `parseIntGateConstraints` (drained in `trySolve`).
    #
    # S10b RAISES-PATH. `parseInt(s)` is an EXPRESSION (→ int), but Nim's runtime
    # RAISES `ValueError` when `s` is not a valid integer. The raise condition is
    # exactly the non-`-`-prefixed non-digit case: `(not isNeg) and (posVal < 0)`
    # (Z3's `toInt` returns −1 there). [The `-`-prefixed non-digit case is handled
    # by the S10a digits gate above, which makes the negative branch UNSAT for a
    # non-digit suffix; modelling its raise too is left to that gate — the spec
    # scopes the S10b raise to the non-`-`-prefixed case, matching
    # `not (toInt(s) >= 0) and not startsWith(s, "-")`.] `lower` cannot itself
    # route a raise (it has no WalkCtx/Path), so we surface the raise predicate to
    # the enclosing statement walk via the `parseIntRaiseConds` threadvar; the
    # statement arm (`isLet`/`isAssign`/`isIf`/`isAssert`) drains it and forks: a
    # RAISES sub-path (constrained by the predicate, routed via E3's `routeRaise`
    # and terminated) and a DIGITS sub-path (constrained by the negation,
    # continuing with this int value). This CLOSES the S10a unsoundness window, so
    # the `seParseIntPreE` hint is NO LONGER emitted. strArgs = [s].
    let s = lower(env, e.strArgs[0])
    doAssert s.kind == svString, "iekStrToInt: operand not svString"
    let dash = mkString("-")
    let isNeg = startsWith(s.str, dash)
    let posVal = toInt(s.str)
    let sLen = len(s.str)
    let negInner = toInt(substr(s.str, mkInt(1), sLen - mkInt(1)))
    let resultInt = ite(isNeg, -negInner, posVal)
    # Digits gate on the NEGATIVE branch only (positive branch is already faithful).
    let parseIntGateCond = (not isNeg) or (negInner >= mkInt(0))
    parseIntGateConstraints.add parseIntGateCond    # threadvar fallback
    syncParseIntGateConstraint(parseIntGateCond)    # CR-9 A0: LIVE WalkCtx field
    # S10b: surface the raise predicate (non-digit, non-`-`-prefixed) for the
    # enclosing statement walk to fork into a routed `ValueError` raise.
    let parseIntRaiseCond = (not isNeg) and (posVal < mkInt(0))
    parseIntRaiseConds.add parseIntRaiseCond          # threadvar fallback
    syncParseIntRaiseCond(parseIntRaiseCond)          # CR-9 Stage 6 Group-2
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
      raise (ref SymexUnsupportedStringOpError)(op: e.strOp,
        msg: "iekRadixFmt: operand must lower to a fixed-width BV; " &
             "got svKind=" & $operand.kind & " (→ sxUnknown, Invariant 3)")
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
      raise (ref SymexUnsupportedStringOpError)(op: e.strOp,
        msg: e.strOp & ": operand must lower to svString; " &
             "got svKind=" & $recv.kind & " (→ sxUnknown, Invariant 3)")
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
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrRfind, iekStrReplace, iekStrReplaceAll,
                   iekStrSplit, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe,
                   iekStrBytes, iekStrConcat,
                   iekIntToStr, iekStrToInt, iekRadixFmt,
                   iekStrToLower, iekStrToUpper, iekRuneToStr}:
    # Phase 15: string ops not modeled in this cycle. Raise a classified
    # SymexUnsupportedStringOpError; the runSymex boundary maps it to sxUnknown +
    # seUnsupportedStringOp (ADR-0006, Invariant 3 — never a crash/silent UNSAT).
    # S6–S11 replace these with the real Z3 String/Seq/Regex lowering.
    let opName = if e.strOp.len > 0: e.strOp else: $e.kind
    raise (ref SymexUnsupportedStringOpError)(op: opName,
      msg: "string op `" & opName & "` is not modeled until its Cluster-S cycle")
  else:
    raise newException(ValueError,
      "lowerStrArm: unexpected e.kind=" & $e.kind &
      " (not iekStrLit or StrOpKinds)")
