## Round-6 B2 (ADR-0028 Leg 2) — int-family WIDTH-CONVERSION modeling,
## WIDENING ONLY.
##
## `iekConvIntWidth` recognizes a conversion between two DIFFERENT
## `intTyNames` members (`uint16(b)` call syntax and `b.uint16` method-call
## syntax both desugar to the identical `nnkConv` shape). WIDENING
## (`tgtWidth > srcWidth`) lowers to a `zeroExtend`/`signExtend` keyed on the
## SOURCE value's OWN signedness (`uint8→int32` zero-extends; a signed
## source sign-extends), regardless of the TARGET's signedness — header math
## then rides plain `binBV` at the widened width. `probeProto` mirrors the
## `iekConvFloatToInt` stale-proto crash precedent: it must return a proto
## at the WIDENED width/signedness, not the pre-conversion one, or a literal
## sibling (e.g. the `shl 8` amount, or an equality RHS) lowers at the wrong
## width and either trips `binBV`'s width-mismatch `doAssert` or silently
## reintroduces the narrower representation.
##
## NARROWING (`uint8(x)` truncation) is a RECORDED DECLINE (RFC-chapulin-
## hardening B2, round-2 scope lock): no truncate primitive is modeled, and
## the pre-B2 identity pass-through was silently UNSOUND (the value left
## unmasked) — now a classified `sxUnknown`, never a crash and never a
## silently-wrong verdict.
##
## Walker version: 78 -> 79 (verdict-changing: a widening int conversion
## between two differently-widthed fixed-width int types now resolves to a
## real verdict instead of the pre-B2 wrong-width identity pass-through;
## narrowing upgrades from silently-unsound to classified decline).
##
## Round-6 B2 rider (control-loop review, same day; walker 79 -> 80): `byte`
## is a plain (non-distinct) alias for `uint8` in `system`, but Nim's typed
## AST preserves the ALIAS SPELLING — the RFC's own PRIMARY consumer shape,
## `uint16(b) shl 8` with `b: byte` (chapulin `protocol.nim:93`, `b` off a
## `seq[byte]`), was missed by the v79 `intTyNames`-only recognizer and fell
## through to the untouched identity pass-through. `normalizeIntTyName`
## (`dsl_parser.nim`) now maps `byte` -> `uint8` before every width/
## signedness lookup in the `nnkConv` B2 arm.
##
## A1 adjudication (walker v116): SAME-WIDTH signedness REINTERPRET
## (`uint32(x)` from an `int32`) was ALSO originally a B2 recorded decline
## ("no reinterpret primitive is modeled") — but this was mis-scoped: B2's
## own soundness finding was that the pre-B2 identity pass-through left a
## STALE `signed` flag on the result (steering signed-vs-unsigned compares
## downstream), not that the conversion itself was unrepresentable. Every
## fixed-width Nim int already allocates as an svBV* whose raw Z3 bit
## pattern is signedness-agnostic, so a same-width reinterpret needs no new
## primitive — `iekConvIntReinterpret` (`dsl_parser.nim`/`runtime.nim`) just
## corrects the `signed` tag on the SAME bits. Discovered when this same-
## width-reinterpret decline turned out to be occluding a genuinely provable
## `sxUnsat` cell in `tsymex_phase15_A1_bitwise.nim` (cell 6, chronos
## `slotIndex`/`capMask` — `uint(cap - 1)` off an `int`). B2-10 below is
## RETIRED as a decline pin and replaced with B2-14/B2-15 (a real SAT +
## soundness-UNSAT proof pair, mirroring the widening groups above).
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

type ScanErrorB2Reinterpret = object of CatchableError

# ---------------------------------------------------------------------------
# Widening — call syntax. The RFC's own consumer spelling (chapulin
# protocol.nim:93): `uint16(b) shl 8`, `b` a `uint8` header byte.
# ---------------------------------------------------------------------------

proc widenCallSyntax(b: uint8) =
  let v = uint16(b) shl 8
  if v == 0x1200'u16:
    symexTarget("widen_call_sat")

proc widenCallSyntaxBoundProof(b: uint8) =
  ## UNSAT companion: header math stays honest at 16 bits for EVERY `b` —
  ## `v == b * 256`, so `v` can never exceed `0xFF00`. A wrong width here
  ## (still 8-bit, or a stale proto reintroducing 8-bit literals) would
  ## either crash (`binBV` width-mismatch) or let this assertion falsely
  ## fail for some `b`.
  let v = uint16(b) shl 8
  symexAssert(v <= 0xFF00'u16)

# ---------------------------------------------------------------------------
# Widening — method-call syntax. `b.uint16` desugars to the SAME `nnkConv`
# shape `uint16(b)` does; must prove identically.
# ---------------------------------------------------------------------------

proc widenMethodSyntax(b: uint8) =
  let v = b.uint16 shl 8
  if v == 0x1200'u16:
    symexTarget("widen_method_sat")

proc widenMethodSyntaxBoundProof(b: uint8) =
  let v = b.uint16 shl 8
  symexAssert(v <= 0xFF00'u16)

# ---------------------------------------------------------------------------
# Widening — `byte`-typed SOURCE. This is the RFC's ACTUAL primary consumer
# shape (chapulin `protocol.nim:93`: `b` comes off a `seq[byte]`, so its
# declared type is `byte`, not `uint8`). `byte` is a plain alias, but Nim's
# typed AST preserves the alias spelling — `normalizeIntTyName` must map it
# to `uint8` before the width/signedness lookup, or this shape silently
# falls through to the pre-B2 identity pass-through.
# ---------------------------------------------------------------------------

proc widenCallSyntaxByteSource(b: byte) =
  let v = uint16(b) shl 8
  if v == 0x1200'u16:
    symexTarget("widen_byte_source_sat")

proc widenCallSyntaxByteSourceBoundProof(b: byte) =
  let v = uint16(b) shl 8
  symexAssert(v <= 0xFF00'u16)

# ---------------------------------------------------------------------------
# probeProto literal-sibling pin — the exact `iekConvFloatToInt` stale-proto
# crash precedent, mirrored: an equality comparison directly against the
# conversion (no intermediate `let`), forcing `probeProto` to hand the
# literal RHS the WIDENED proto so it lowers at 16 bits, not 8.
# ---------------------------------------------------------------------------

proc probeProtoLiteralSibling(b: uint8) =
  if uint16(b) == 0x0042'u16:
    symexTarget("proto_literal_sibling_sat")

# ---------------------------------------------------------------------------
# Signedness — keyed on the SOURCE value, per the RFC's explicit rule,
# independent of the TARGET's own signedness.
# ---------------------------------------------------------------------------

proc widenZeroExtendUnsignedSource(x: uint8) =
  ## Unsigned source (`uint8`) widened to a signed target (`int32`) must
  ## ZERO-extend: 255 (0xFF, MSB set) stays 255, never sign-extends to -1.
  symexAssume(x == 255'u8)
  let v = int32(x)
  symexAssert(v == 255'i32)

proc widenSignExtendSignedSource(x: int8) =
  ## Signed source (`int8`) widened to a signed target (`int32`) must
  ## SIGN-extend: -1 stays -1, never zero-extends to 255.
  symexAssume(x == -1'i8)
  let v = int32(x)
  symexAssert(v == -1'i32)

proc widenSignExtendToUnsignedTarget(x: int8) =
  ## Signed source (`int8`) widened to an UNSIGNED target (`uint32`) still
  ## sign-extends (keyed on the SOURCE, not the target): -1's bit pattern
  ## (0xFF) becomes 0xFFFFFFFF, read back as the uint32 value
  ## 4294967295 — never the zero-extended 255. This is the pin that
  ## distinguishes "keyed on source signedness" from the (wrong) "keyed on
  ## target signedness" alternative.
  symexAssume(x == -1'i8)
  let v = uint32(x)
  symexAssert(v == 0xFFFFFFFF'u32)

# ---------------------------------------------------------------------------
# Recorded declines — narrowing and same-width signedness reinterpret.
# ---------------------------------------------------------------------------

proc narrowingDecline(x: int32) =
  let b = uint8(x)
  if b == 42'u8:
    symexTarget("narrow_decline_target")

proc narrowingDeclineByteTarget(x: int32) =
  ## The `byte`-spelled twin of `narrowingDecline`: `byte(x)` must decline
  ## exactly like `uint8(x)` (same normalized target) — the pre-B2 identity
  ## pass-through was UNMASKED-unsound for this spelling too, and the RFC's
  ## rider explicitly calls it out alongside the widening consumer shape.
  let b = byte(x)
  if b == 42'u8:
    symexTarget("narrow_decline_byte_target")

proc reinterpretSat(x: int32) =
  ## A1 adjudication: reachable (x == 42 reinterprets to the same bit
  ## pattern 42'u32) — was formerly the B2-10 decline pin.
  let u = uint32(x)
  if u == 42'u32:
    symexTarget("reinterpret_sat_target")

proc reinterpretBoundProof(x: int32) =
  ## Soundness pin, mirrors `widenSignExtendToUnsignedTarget`: a same-width
  ## `int32 -> uint32` reinterpret is a pure bit-pattern relabeling, never a
  ## value transformation — `x == -1'i32` (all bits set) MUST reinterpret to
  ## `0xFFFFFFFF'u32`, never wrap/clamp/zero. This is exactly the shape a
  ## stale `signed` flag (B2's original unsoundness finding) or an
  ## accidental sign-extend-then-truncate implementation would get wrong.
  symexAssume(x == -1'i32)
  let u = uint32(x)
  symexAssert(u == 0xFFFFFFFF'u32)

suite "symex round-6 B2 — widening, call syntax":

  test "B2-1: uint16(b) shl 8 reaches the target value (SAT)":
    let r = symexFind(widenCallSyntax, tLabel("widen_call_sat"))
    check r.status == sxSat

  test "B2-2: uint16(b) shl 8 never exceeds 0xFF00 for any b (UNSAT companion)":
    let r = symexFind(widenCallSyntaxBoundProof, tAssertionViolation())
    check r.status == sxUnsat

suite "symex round-6 B2 — widening, method-call syntax":

  test "B2-3: b.uint16 shl 8 reaches the target value (SAT)":
    let r = symexFind(widenMethodSyntax, tLabel("widen_method_sat"))
    check r.status == sxSat

  test "B2-4: b.uint16 shl 8 never exceeds 0xFF00 for any b (UNSAT companion)":
    let r = symexFind(widenMethodSyntaxBoundProof, tAssertionViolation())
    check r.status == sxUnsat

suite "symex round-6 B2 — widening, byte-typed source (rider)":

  test "B2-11: uint16(b) shl 8 with b: byte reaches the target value (SAT — the RFC's actual protocol.nim:93 shape)":
    let r = symexFind(widenCallSyntaxByteSource, tLabel("widen_byte_source_sat"))
    check r.status == sxSat

  test "B2-12: uint16(b) shl 8 with b: byte never exceeds 0xFF00 (UNSAT companion)":
    let r = symexFind(widenCallSyntaxByteSourceBoundProof, tAssertionViolation())
    check r.status == sxUnsat

suite "symex round-6 B2 — probeProto literal-sibling pin":

  test "B2-5: uint16(b) == <literal> lowers the literal at the widened width (SAT)":
    let r = symexFind(probeProtoLiteralSibling, tLabel("proto_literal_sibling_sat"))
    check r.status == sxSat

suite "symex round-6 B2 — signedness keyed on the SOURCE value":

  test "B2-6: unsigned source zero-extends into a signed target (UNSAT companion, no false verdict)":
    let r = symexFind(widenZeroExtendUnsignedSource, tAssertionViolation())
    check r.status == sxUnsat

  test "B2-7: signed source sign-extends into a signed target (UNSAT companion, no false verdict)":
    let r = symexFind(widenSignExtendSignedSource, tAssertionViolation())
    check r.status == sxUnsat

  test "B2-8: signed source sign-extends even into an UNSIGNED target (UNSAT companion)":
    let r = symexFind(widenSignExtendToUnsignedTarget, tAssertionViolation())
    check r.status == sxUnsat

suite "symex round-6 B2 — recorded declines (narrowing)":

  test "B2-9: narrowing int conversion declines cleanly (classified sxUnknown, not a crash)":
    let r = symexFind(narrowingDecline, tLabel("narrow_decline_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("narrowing" in it.msg)

  test "B2-13: byte(x) narrowing declines cleanly (classified sxUnknown, not a crash — rider)":
    let r = symexFind(narrowingDeclineByteTarget, tLabel("narrow_decline_byte_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("narrowing" in it.msg)

suite "symex round-6 A1 — same-width signedness reinterpret (formerly B2-10 decline, now modeled)":

  test "B2-14: uint32(x) from int32 reaches the reinterpreted value (SAT)":
    let r = symexFind(reinterpretSat, tLabel("reinterpret_sat_target"))
    check r.status == sxSat

  test "B2-15: -1'i32 reinterprets to 0xFFFFFFFF'u32, not zero/wrap (UNSAT companion, soundness)":
    let r = symexFind(reinterpretBoundProof, tAssertionViolation())
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Fix-slice item 2 (round-6 re-review, High) — lowerConvIntReinterpret had
# no svInt arm. A width-64 isIntOffset-promoted value (B5's own
# retIntOffsetPositions mechanism, allocateSym's itInt arm ~2176-2188)
# allocates svInt (a Z3 Int-sorted value, no bit pattern) rather than a BV —
# reinterpreting it (`uint(x)`) reached lowerConvIntReinterpret's `else`
# raiseAssert, crashing the whole run. Fixed: classified decline via
# degradeAlloc (a signedness retag has no sound meaning on a Z3 Int sort).
# ---------------------------------------------------------------------------

proc readCStringB2Reinterpret(s: string, offset: int): (string, int) =
  ## Identical canonical B4 accumulating-scan shape to
  ## `tsymex_r6_r3_svint_overflow.nim`'s own `readCStringR3` — proven to
  ## promote its return-tuple position-0 `int` via B5's
  ## `retIntOffsetPositions` mechanism, giving the CALLER's bound value a
  ## fresh `svInt` (not a BV), width-64, no `ziWidth` stamp (R3's own SCOPE
  ## NOTE, this same file's `reinterpretSat` neighbourhood applies to a
  ## plain BV32 param instead — THIS repro is specifically the svInt shape).
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanErrorB2Reinterpret, "unterminated")

proc sutReinterpretIntOffsetReturn(s: string, start: int) =
  ## RED (pre-fix): `uint(q)` on the isIntOffset-promoted svInt `q` reaches
  ## `lowerConvIntReinterpret`'s `else` arm — `raiseAssert`, crashing the
  ## whole run (uncaught past the top-level catch-all).
  ## GREEN (post-fix): classified decline (`feUnsupportedOp`, `sxUnknown`),
  ## never a crash.
  symexAssume(start >= 0 and start <= s.len)
  let (_, q) = readCStringB2Reinterpret(s, start)
  let u = uint(q)
  if u == 5'u:
    symexTarget("reinterpret_intoffset_return_reached")

suite "symex round-6 B2 fix-slice item 2 — lowerConvIntReinterpret's svInt arm":

  test "item2-1 RED->GREEN: uint(q) on an isIntOffset-promoted svInt reports classified sxUnknown (feUnsupportedOp), never a crash":
    let r = symexFind(sutReinterpretIntOffsetReturn, tLabel("reinterpret_intoffset_return_reached"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedOp)
    check r.errors.anyIt("lowerConvIntReinterpret" in it.msg)

  test "item2-2: the classified decline never falsely reports sxSat/sxUnsat":
    let r = symexFind(sutReinterpretIntOffsetReturn, tLabel("reinterpret_intoffset_return_reached"))
    check r.status != sxSat
    check r.status != sxUnsat

suite "symex round-6 B2 — walker version pin":

  test "walker version floor >= 116 (A1: same-width reinterpret now modeled, not declined)":
    check parseInt(symexWalkerVersion) >= 116

  test "walker version floor >= 119 (fix-slice item 2: lowerConvIntReinterpret's svInt arm, classified decline not a crash)":
    check parseInt(symexWalkerVersion) >= 119
