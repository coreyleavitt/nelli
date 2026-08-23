## Round-6 B7-rider (ADR-0028 Leg 1 + Leg 2) — closes the B7 exit-gate
## BLOCKER A ("B3/B4/B5/B6's closed-form recognizers hard-gate the
## receiver on `classifyType(...).ty.kind != itString` and never consult
## `ctx.stringBackedParams`") and the companion char-widening witness bug
## the handoff's B7-attempt bullet flags. See
## `docs/RFC-chapulin-hardening.md`'s B7-rider row and
## `docs/RFC-chapulin-hardening.handoff.md`'s round-6 grind log for the
## full charter.
##
## LEG 1: `tryRecognizeScanIdiom`/`tryRecognizeScanPairIdiom`/
## `tryRecognizeAccumulatingScan`/`tryRecognizePairLoopIdiom` widened to
## accept a string-backed `seq[byte]` receiver (`ctx.stringBackedParams`,
## B1's shared classifier) alongside the original itString gate, via the
## new shared `scanReceiverOk`/`scanDelimiterChar` (`dsl_parser.nim`). A
## real gap closed ALONGSIDE the four recognizer gates: B1's own
## classifier (`collectStringBackedByteSeqParams`) previously only
## detected a Q1-SHAPED (and-guard) consuming loop when deciding whether a
## `seq[byte]` param qualifies as string-backed — chapulin's actual
## corpus shapes (`readCString`/`readOptions`) are B4/B6-shaped, never
## Q1-shaped, so those params would never have been classified
## string-backed at all regardless of how far the four recognizer gates
## were individually widened. The classifier's candidate walk now tries
## all four shape predicates per loop.
##
## LEG 2: see the dedicated section below.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# =============================================================================
# LEG 1 -- receiver-gate widening
# =============================================================================

# -----------------------------------------------------------------------------
# 1. B0/Q1 shape on a seq[byte] receiver -- SAT + UNSAT (bound-safety)
#    companion, mirroring tsymex_r6_b0_scanlift_bound.nim's own style.
# -----------------------------------------------------------------------------

proc byteScanQ1(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if i == 3:
    symexTarget("byte_q1_sat")

proc byteScanQ1BoundProof(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  symexAssert(i <= data.len)

suite "symex round-6 B7-rider -- B0/Q1 widened to a seq[byte] receiver":

  test "B7R-1: byte-backed Q1 scan reaches i==3 -> sxSat":
    let r = symexFind(byteScanQ1, tLabel("byte_q1_sat"))
    check r.status == sxSat

  test "B7R-1b UNSAT companion: the byte-backed scan-lift clamp never exceeds data.len":
    let r = symexFind(byteScanQ1BoundProof, tAssertionViolation())
    check r.status == sxUnsat

# -----------------------------------------------------------------------------
# 2. Byte-literal delimiter mapping -- the three spellings the rider's
#    charter names (`0'u8`, `byte(0)`, `0x00`), including the REAL chapulin
#    terminator value, all recognized and proving the SAME closed form.
# -----------------------------------------------------------------------------

proc byteScanDelimU8Suffix(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if i == 2:
    symexTarget("delim_u8_suffix")

proc byteScanDelimByteCall(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != byte(0):
    inc i
  if i == 2:
    symexTarget("delim_byte_call")

proc byteScanDelimHexLit(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0x00:
    inc i
  if i == 2:
    symexTarget("delim_hex_lit")

suite "symex round-6 B7-rider -- byte-literal delimiter spellings map to the real 0x00":

  test "B7R-2a: 0'u8 delimiter spelling is recognized -> sxSat":
    let r = symexFind(byteScanDelimU8Suffix, tLabel("delim_u8_suffix"))
    check r.status == sxSat

  test "B7R-2b: byte(0) delimiter spelling is recognized -> sxSat":
    let r = symexFind(byteScanDelimByteCall, tLabel("delim_byte_call"))
    check r.status == sxSat

  test "B7R-2c: 0x00 plain-int-literal delimiter spelling is recognized -> sxSat":
    let r = symexFind(byteScanDelimHexLit, tLabel("delim_hex_lit"))
    check r.status == sxSat

# -----------------------------------------------------------------------------
# 3. B3 shape (early-return int result) on a seq[byte] receiver -- SAT +
#    UNSAT companion, mirroring tsymex_r6_b3_scanpair.nim's own style.
# -----------------------------------------------------------------------------

proc byteScanPairTracer(data: seq[byte], start: int): (int, int) =
  var i = start
  while i < data.len:
    if data[i] == 0'u8:
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "unterminated")

proc sutByteScanPairFound(data: seq[byte], start: int) =
  let (p, q) = byteScanPairTracer(data, start)
  if p == start + 4 and q == start + 5:
    symexTarget("byte_pair_hit")

proc sutByteScanPairNotFoundImpossible(data: seq[byte], start: int) =
  symexAssume(start >= 0 and start <= data.len)
  var i = start
  while i < data.len:
    if data[i] == 0'u8:
      return
    i.inc
  if i > data.len:
    symexTarget("byte_pair_impossible")

suite "symex round-6 B7-rider -- B3 widened to a seq[byte] receiver":

  test "B7R-3: byte-backed B3 scan finds start+4 -> sxSat":
    let r = symexFind(sutByteScanPairFound, tLabel("byte_pair_hit"))
    check r.status == sxSat

  test "B7R-3b UNSAT companion: the byte-backed B3 not-found clamp never exceeds data.len":
    let r = symexFind(sutByteScanPairNotFoundImpossible, tLabel("byte_pair_impossible"))
    check r.status == sxUnsat

# -----------------------------------------------------------------------------
# 4. B4 shape (accumulating scan) on a seq[byte] receiver -- the
#    chapulin-real `readCString(data: seq[byte], offset: int): (string, int)`
#    shape verbatim (protocol.nim), real '\0' delimiter, content + cross-check.
#    The accumulator stays itString (a THIRD gate this slice does NOT widen
#    -- the payload is always a genuine `string` regardless of the scanned
#    receiver's own representation).
# -----------------------------------------------------------------------------

proc readCStringByteSeq(data: seq[byte], offset: int): (string, int) =
  var s = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (s, i + 1)
    s.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutByteAccPayloadAB(data: seq[byte], start: int) =
  let (payload, q) = readCStringByteSeq(data, start)
  if payload == "AB" and q == start + 3:
    symexTarget("byte_acc_ab")

suite "symex round-6 B7-rider -- B4 widened to a seq[byte] receiver (chapulin's real readCString shape)":

  test "B7R-4: byte-backed readCString finds payload==\"AB\" -> sxSat":
    let r = symexFind(sutByteAccPayloadAB, tLabel("byte_acc_ab"))
    check r.status == sxSat

  test "B7R-4-content: the witness's real seq[byte] receiver and real NUL terminator are exact":
    let r = symexFind(sutByteAccPayloadAB, tLabel("byte_acc_ab"))
    check r.status == sxSat
    let (data, start) = r.witness
    check start >= 0 and start <= data.len
    check data.len == start + 3
    check data[start] == ord('A').byte
    check data[start + 1] == ord('B').byte
    check data[start + 2] == 0'u8

  test "B7R-4-cross: the witness, replayed through the real function, reproduces the exact found outcome":
    let r = symexFind(sutByteAccPayloadAB, tLabel("byte_acc_ab"))
    check r.status == sxSat
    let (data, start) = r.witness
    let (payload, q) = readCStringByteSeq(data, start)
    check payload == "AB"
    check q == start + 3

  test "B7R-4-notfound: no NUL terminator present -> the modeled ScanError raise is reachable (sxRaised)":
    proc discardSut(data: seq[byte], start: int) =
      discard readCStringByteSeq(data, start)
    let r = symexFind(discardSut, tRaisedExn("ScanError"))
    check r.status == sxRaised

  test "B7R-4-oob: negative symbolic start -> the entry-read probe deposits a real IndexDefect (sxRaised)":
    proc discardSut(data: seq[byte], start: int) =
      discard readCStringByteSeq(data, start)
    let r = symexFind(discardSut, tIndexError())
    check r.status == sxRaised

# -----------------------------------------------------------------------------
# 5. B5-shape composition: a call-boundary chained scan on a seq[byte]
#    receiver -- mind B5's calleeIntOffsetReturnPositions/IRParam.isIntOffset
#    machinery, which is receiver-type-agnostic BY CONSTRUCTION (it traces
#    the scan's OWN index symbol, never the receiver's type), so it composes
#    for free once the receiver gate itself is widened; this pin confirms
#    that composition actually holds for a byte-backed receiver, not just
#    for itString.
# -----------------------------------------------------------------------------

proc sutByteChainedTwoPayloads(data: seq[byte]) =
  let (payload1, p1) = readCStringByteSeq(data, 0)
  let (payload2, p2) = readCStringByteSeq(data, p1)
  if payload1 == "filename" and payload2 == "mode" and p2 == p1 + 5:
    symexTarget("byte_chained_hit")

suite "symex round-6 B7-rider -- B5 call-boundary composition on a seq[byte] receiver":

  test "B7R-5: two chained readCString calls (byte-backed) -- both payloads reachable -> sxSat":
    let r = symexFind(sutByteChainedTwoPayloads, tLabel("byte_chained_hit"))
    check r.status == sxSat

  test "B7R-5-cross: the witness, replayed through the real function twice, reproduces both payloads":
    let r = symexFind(sutByteChainedTwoPayloads, tLabel("byte_chained_hit"))
    check r.status == sxSat
    let data = r.witness[0]
    let (payload1, p1) = readCStringByteSeq(data, 0)
    check payload1 == "filename"
    let (payload2, p2) = readCStringByteSeq(data, p1)
    check payload2 == "mode"
    check p2 == p1 + 5

# -----------------------------------------------------------------------------
# 6. B6 shape (pair-loop / readOptions) on a seq[byte] receiver -- the
#    option-region membership fast path fires for a byte-backed receiver,
#    mirroring tsymex_r6_b6_optionregion.nim's own main defect proof.
# -----------------------------------------------------------------------------

proc readOptionsByteSeqSut(data: seq[byte], start: int) =
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < data.len:
    let (key, p1) = readCStringByteSeq(data, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringByteSeq(data, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("byte_options_done")

suite "symex round-6 B7-rider -- B6 widened to a seq[byte] receiver":

  test "B7R-6: five-pair option region over a seq[byte] receiver (6 real outer iterations, past the default maxLoopUnwind=5 horizon) -> sxSat via region-membership fast path":
    proc sut(data: seq[byte]) =
      ## Per-index literal assumes (not a whole-seq `==`, which Nim's own
      ## type checker rejects here anyway — `data: seq[byte]` cannot compare
      ## against a `string` literal) — mirrors tsymex_r6_b1_stringbacked.nim's
      ## own idiom for an array-modeled seq[byte] receiver; `data`'s OWN
      ## classification here is NOT decided by a loop textually in THIS
      ## proc's own body (there is none) but by the Round-6 B7-rider
      ## one-level CALL TRACE (see `collectStringBackedByteSeqParamsImpl`'s
      ## own doc comment): `readOptionsByteSeqSut`'s OWN `data` is marked
      ## string-backed by its internal pair-loop, and this proc passes `data`
      ## straight through as that call's first argument, so it is traced back
      ## and marked string-backed here too — every one of the `iekStrAt`
      ## element assumes below lowers as a real Sequence-theory constraint,
      ## not an Array `select`.
      ##
      ## Five pairs sized DELIBERATELY smaller than
      ## tsymex_r6_b6_optionregion.nim's own eight-pair string-receiver pin:
      ## an equivalent 25-byte case built from 25 individual per-index
      ## `iekStrAt` conjuncts (rather than ONE Z3 string-literal equality, as
      ## the string-receiver pin uses) was empirically far more expensive for
      ## the solver — confirmed via an isolated scratch probe while landing
      ## this rider, not a correctness question (the SAME shape at this
      ## smaller size proves quickly and correctly). Six real outer
      ## iterations (five pairs, then the empty-key terminator) is still
      ## comfortably past the default `maxLoopUnwind` (5), so this remains a
      ## genuine past-the-horizon pin, not merely a within-budget one.
      symexAssume(data.len == 16)
      symexAssume(
        data[0] == byte('a') and data[1] == byte('a') and data[2] == 0'u8 and
        data[3] == byte('b') and data[4] == byte('b') and data[5] == 0'u8 and
        data[6] == byte('c') and data[7] == byte('c') and data[8] == 0'u8 and
        data[9] == byte('d') and data[10] == byte('d') and data[11] == 0'u8 and
        data[12] == byte('e') and data[13] == byte('e') and data[14] == 0'u8 and
        data[15] == 0'u8)
      readOptionsByteSeqSut(data, 0)
    let r = symexFind(sut, tLabel("byte_options_done"))
    check r.status == sxSat

# -----------------------------------------------------------------------------
# 7. Mutation-fallback veto still applies to a byte-backed receiver -- B1's
#    scanShapeReceiverMutated must still exclude a mutated seq[byte] param
#    from string-backing regardless of how many recognizers now consult
#    ctx.stringBackedParams; mirrors tsymex_r6_b1_stringbacked.nim's own
#    SUT 3/diagnostic pair verbatim.
# -----------------------------------------------------------------------------

proc mutatedByteReceiverStaysArray(data: var seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  data.add(9'u8)
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("b7r_mutated_stays_array")

proc addMutationNoLoopDiagnostic(data: var seq[byte]) =
  data.add(9'u8)
  if data.len > 0 and data[0] == 42'u8:
    symexTarget("b7r_add_no_loop_sat")

suite "symex round-6 B7-rider -- mutation-fallback veto (B1's scanShapeReceiverMutated still applies)":

  test "B7R-7: a mutated seq[byte] receiver (with an otherwise-qualifying B0 scan) still declines to array-model, not the string-mismatch fault":
    ## N47-followup (walker v110, diagnosis round after bea6921) -- same fix
    ## and same rationale as `tsymex_r6_b1_stringbacked.nim`'s B1-4 pin
    ## (mirrors that SUT verbatim): the degraded `.add` receiver no longer
    ## leaks a placeholder that fabricates cascading, misclassified
    ## `seNestedSeqUnsupported` errors off `data.len`/`data[0]`; `errors[0]`
    ## is not pinned exactly here either, since this SUT's own scan loop
    ## independently surfaces a genuine, unrelated `beBudgetExhausted` once
    ## the run is no longer whole-run-poisoned by a raw raise. See B1-4's
    ## own comment for the full writeup.
    let r = symexFind(mutatedByteReceiverStaysArray, tLabel("b7r_mutated_stays_array"))
    check r.status == sxUnknown
    check r.errors.len > 0
    var sawWidthDecline = false
    for e in r.errors:
      check "nested seq element type is not supported" notin e.msg
      check "receiver not svSeq" notin e.msg
      if e.kind == weInternalWalkerFault and "unsupported width" in e.msg:
        sawWidthDecline = true
    check sawWidthDecline

  test "B7R-7 diagnostic: the no-loop ground truth hits the IDENTICAL pre-existing gap":
    let r = symexFind(addMutationNoLoopDiagnostic, tLabel("b7r_add_no_loop_sat"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == weInternalWalkerFault
    check "unsupported width" in r.errors[0].msg
    var sawWidthDecline = false
    for e in r.errors:
      check "nested seq element type is not supported" notin e.msg
      check "receiver not svSeq" notin e.msg
      if e.kind == weInternalWalkerFault and "unsupported width" in e.msg:
        sawWidthDecline = true
    check sawWidthDecline

# -----------------------------------------------------------------------------
# 8. Trip-wire: a byte-backed receiver whose bound is NOT syntactically its
#    own `.len` still k-unrolls, unrecognized -- proving the widening did not
#    loosen the family's other structural gates for byte receivers.
# -----------------------------------------------------------------------------

proc sutByteNonLenBoundImpossible(data: seq[byte]) =
  let n = data.len
  var i = 0
  while i < n and data[i] != 0'u8:
    inc i
  if i > data.len:
    symexTarget("b7r_impossible")

suite "symex round-6 B7-rider -- trip wire (byte receiver, non-.len bound stays unrecognized)":

  test "B7R-8: non-.len bound over a seq[byte] receiver is NOT recognized -> sxUnknown":
    let r = symexFind(sutByteNonLenBoundImpossible, tLabel("b7r_impossible"))
    check r.status == sxUnknown

# -----------------------------------------------------------------------------
# 9. Exclusivity: the widening must not let siblings cross-fire on a
#    seq[byte] receiver -- mirrors B3's own "B3-5" migrated pin (a
#    3-statement body is B4's shape, never B3's, by construction: B3's body
#    check is `!= 2`, B4's is `!= 3`). Reused here specifically for a
#    byte-backed receiver.
# -----------------------------------------------------------------------------

proc sutByteAccPositionHonoredImpossible(data: seq[byte], start: int) =
  let (_, q) = readCStringByteSeq(data, start)
  if q < start:
    symexTarget("b7r_exclusive_impossible")

suite "symex round-6 B7-rider -- exclusivity (siblings do not cross-fire on a byte receiver)":

  test "B7R-9: the 3-statement accumulating body over a byte receiver is B4's shape alone, never B3's -> sxRaised (only the not-found raise survives, mirroring B3-5's migrated verdict)":
    let r = symexFind(sutByteAccPositionHonoredImpossible, tLabel("b7r_exclusive_impossible"))
    check r.status == sxRaised

# =============================================================================
# LEG 2 -- char-widening witness corruption (companion bug, TFTP
# opcode-dispatch shape: two char-sourced B2-widened values combined and
# compared in one expression)
#
# Root-caused while landing this rider (see `symexWalkerVersion`'s own doc
# comment, `canonicalize.nim`, for the full writeup) -- the chapulin
# handoff's own hypothesis ("witness EXTRACTION corrupts") was investigated
# and found INCORRECT. `evalStrBytes`/`getStringContents` (the B4-rider
# extraction chokepoint) faithfully reported whatever Z3's model actually
# contained; the real defect was a PARSE-TIME MODELING GAP one call site
# removed from extraction entirely: `char` was never a member of
# `intTyNames`/`normalizeIntTyName`'s alias map the way `byte` is, so
# `uint16(<charExpr>)` silently fell through `dsl_parser.nim`'s `nnkConv`
# arm to a bare identity pass-through -- DROPPING the widening conversion
# entirely. `hi`/`lo`/`combined` all stayed 8-bit despite their DECLARED
# 16-bit Nim type; comparing the 8-bit `combined` to a 16-bit literal
# truncated the literal to its low byte at the literal-shaping step, so the
# checked property silently degenerated to "the LOW byte alone equals the
# literal's low byte", leaving the HIGH byte totally unconstrained. `sxSat`
# was technically correct (the real property genuinely IS reachable) but
# the reported witness reflected Z3's free (don't-care) choice for the
# unconstrained high byte, not the value the property actually depends on.
# Fix: `normalizeIntTyName` now maps `char` to `"uint8"`, exactly like
# `byte` -- semantically exact, since `char` is ordinally an 8-bit
# UNSIGNED value (never sign-extends) under a distinct (non-alias) name.
# =============================================================================

proc twoCharWidenCombine(s: string) =
  ## Chapulin's own opcode-dispatch header-read shape verbatim:
  ## `uint16(data[0]) shl 8 or uint16(data[1])`, here over a genuine
  ## `string` receiver (`s[i]: char`) since LEG 2 is specifically about
  ## CHAR-sourced widening, not byte-sourced (byte-sourced widening was
  ## already sound -- B2's own rider, `tsymex_r6_b2_intwidth.nim`'s
  ## `widenCallSyntaxByteSource`).
  if s.len == 2:
    let hi = uint16(s[0])
    let lo = uint16(s[1])
    let combined = (hi shl 8) or lo
    if combined == 0x4142'u16:
      symexTarget("leg2_hit")

proc twoCharWidenCombineTwin(s: string): uint16 =
  ## A "real function" twin of the widen+shl+or expression above, used
  ## ONLY for the cross-check pin below (replaying the reported witness
  ## through independently-written Nim code, mirroring B4/B5's own
  ## witness-replay cross-check convention) -- not itself passed to
  ## `symexFind`.
  (uint16(s[0]) shl 8) or uint16(s[1])

suite "symex round-6 B7-rider -- LEG 2 (char-widening witness-corruption fix)":

  test "B7R-LEG2-1: two char-sourced widened values combined and compared -> sxSat":
    let r = symexFind(twoCharWidenCombine, tLabel("leg2_hit"))
    check r.status == sxSat

  test "B7R-LEG2-1-content: the witness is the exact 2 bytes the property depends on, not Z3's free don't-care choice for the (pre-fix, spuriously unconstrained) high byte":
    let r = symexFind(twoCharWidenCombine, tLabel("leg2_hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 2
    check s == "AB"
    check ord(s[0]) == 0x41
    check ord(s[1]) == 0x42

  test "B7R-LEG2-1-cross: the witness, replayed through a real-code twin of the widen+shl+or expression, reproduces the exact target value":
    let r = symexFind(twoCharWidenCombine, tLabel("leg2_hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check twoCharWidenCombineTwin(s) == 0x4142'u16

  test "B7R-LEG2-2: combined reaches a value NEEDING the full 16-bit width (>255) -- pre-fix this was UNREACHABLE (the property silently degenerated to a low-byte-only, <=255 check)":
    ## `0xFF00` requires `hi == 0xFF` (255) contributing at the SHIFTED
    ## (high-byte) position -- impossible if `hi shl 8` were still
    ## evaluating at the pre-fix 8-bit width (an 8-bit `shl 8` is
    ## UNCONDITIONALLY zero, per SMT-LIB bvshl semantics: every bit shifts
    ## out of an operand shifted by its own full width), which would leave
    ## `combined` capped at 255 and this target permanently sxUnsat/
    ## sxUnknown regardless of `lo`. A genuine positive existence proof
    ## that the fix operates at the REAL (16-bit) width, not merely that
    ## SOME witness now happens to look plausible.
    proc sut(s: string) =
      if s.len == 2:
        let hi = uint16(s[0])
        let lo = uint16(s[1])
        let combined = (hi shl 8) or lo
        if combined == 0xFF00'u16:
          symexTarget("leg2_highbyte_hit")
    let r = symexFind(sut, tLabel("leg2_highbyte_hit"))
    check r.status == sxSat

  test "B7R-LEG2-3: char(<a wider int>) narrowing declines cleanly (classified sxUnknown, not a crash or a silent mis-model)":
    ## Regression pin for `normalizeIntTyName`'s widened `char` mapping's
    ## OTHER branch: `char` as a NARROWING target is a NEW REACHABLE INPUT
    ## for `declineIntWidthConv` -- an EXISTING B2 decline site (already
    ## covered by TOT-1's own "B2: narrowing int conversion" corpus row, per
    ## its SITE, not its exact input-type combination) -- not a new site.
    ## Pre-fix this shape silently fell to the bare identity pass-through
    ## (no narrowing check at all, an unmasked, unsound value) rather than
    ## declining; post-fix it declines exactly like `byte`'s own narrowing
    ## case (B2-9/B2-13, `tsymex_r6_b2_intwidth.nim`).
    proc charNarrowingDecline(x: int32) =
      let c = char(x)
      if c == 'A':
        symexTarget("char_narrow_decline_target")
    let r = symexFind(charNarrowingDecline, tLabel("char_narrow_decline_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("narrowing" in it.msg)

suite "symex round-6 B7-rider -- version pins":

  test "walker version floor >= 87 (LEG 1 receiver-gate widening + LEG 2 char-widening fix)":
    check parseInt(symexWalkerVersion) >= 87

  test "renderAsChoicesVersion floor >= 11 (LEG 2's char-widening witness-content fix, lockstep with the walker bump)":
    check parseInt(renderAsChoicesVersion) >= 11
