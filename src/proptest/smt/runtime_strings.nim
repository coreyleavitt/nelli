# runtime_strings.nim — Cluster S include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_strings.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents: `lowerStrArm(env, e)` — the `lower()` dispatch arm for
# `iekStrLit` and `StrOpKinds` (Cluster S, Stage 7 / Stage 8, CR-7).
# Placement in runtime.nim: immediately after `coerceToBoolSV` and
# immediately before `lowerFloatArm`, between `lower`'s forward-decl
# and `lower`'s body.

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
  ##   parseIntGateConstraints, parseIntRaiseConds, currentMaxBytesEncodingLen,
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
    # Phase 15 S3. `s[i]` (read) → a Nim `char` (svBV8 unsigned). The Z3 bridge:
    # `at(s, i)` is a 1-char Z3String; `toCode(.)` is its codepoint as Z3Int,
    # which under ≤0xFF is exactly the byte value 0..255 (== Nim byte index ==
    # Z3 position). We narrow that Z3Int to a BV8 char. Out-of-range `i` makes
    # `at` the empty string and `toCode` returns -1 (→ BV8 0xFF); per Z3 spec we
    # do not crash. `char` classifies (Z3c) to unranged tInt(8, unsigned), i.e.
    # svBV8 — so `s[i] == 'c'` compares two svBV8 values via the existing path.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrAt: receiver not svString"
    let idx = lower(env, e.strArgs[1])
    let idxZi = toZ3Int(idx)
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
    # Phase 15 S4. `s.find(sub)` (strutils.find) → Z3 `indexOf(s, sub)`
    # (`Z3_mk_seq_index`), the BYTE offset of the first occurrence, or -1 when
    # absent. Under the ≤0xFF byte-faithful constraint (ADR-0006) a Z3 position
    # offset equals a Nim byte index, so no codepoint adjustment is needed.
    # The absent case (-1) is a valid SMT integer, never a crash. strArgs =
    # [recv, sub]; nim-z3's no-start `indexOf` overload starts at position 0.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrFind: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrFind: arg not svString"
    SymVal(kind: svInt, zi: indexOf(recv.str, sub.str))
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
      mkConcreteStrSeq(parts)
    elif recvIR.kind == iekStrLit and sepIR.kind == iekStrLit:
      # (b) concrete-inline. Both sides literal → split in Nim, emit literals.
      let parts = recvIR.sval.split(sepIR.sval)
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
    parseIntGateConstraints.add ((not isNeg) or (negInner >= mkInt(0)))
    # S10b: surface the raise predicate (non-digit, non-`-`-prefixed) for the
    # enclosing statement walk to fork into a routed `ValueError` raise.
    let parseIntRaiseCond = (not isNeg) and (posVal < mkInt(0))
    parseIntRaiseConds.add parseIntRaiseCond          # threadvar fallback
    syncParseIntRaiseCond(parseIntRaiseCond)          # CR-9 Stage 6 Group-2
    SymVal(kind: svInt, zi: resultInt)
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrReplace, iekStrReplaceAll,
                   iekStrSplit, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe,
                   iekStrBytes, iekStrConcat,
                   iekIntToStr, iekStrToInt}:
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
