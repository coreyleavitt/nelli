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
## NARROWING (`uint8(x)` truncation) and SAME-WIDTH signedness REINTERPRET
## (`uint32(x)` from an `int32`) are RECORDED DECLINES (RFC-chapulin-
## hardening B2, round-2 scope lock): no truncate/reinterpret primitive is
## modeled, and the pre-B2 identity pass-through was silently UNSOUND for
## both (the value left unmasked / a stale `signed` flag steering
## signed-vs-unsigned compares) — now a classified `sxUnknown`, never a
## crash and never a silently-wrong verdict.
##
## Walker version: 78 -> 79 (verdict-changing: a widening int conversion
## between two differently-widthed fixed-width int types now resolves to a
## real verdict instead of the pre-B2 wrong-width identity pass-through;
## narrowing/reinterpret upgrade from silently-unsound to classified decline).
##
## Round-6 B2 rider (control-loop review, same day; walker 79 -> 80): `byte`
## is a plain (non-distinct) alias for `uint8` in `system`, but Nim's typed
## AST preserves the ALIAS SPELLING — the RFC's own PRIMARY consumer shape,
## `uint16(b) shl 8` with `b: byte` (chapulin `protocol.nim:93`, `b` off a
## `seq[byte]`), was missed by the v79 `intTyNames`-only recognizer and fell
## through to the untouched identity pass-through. `normalizeIntTyName`
## (`dsl_parser.nim`) now maps `byte` -> `uint8` before every width/
## signedness lookup in the `nnkConv` B2 arm.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

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

proc reinterpretDecline(x: int32) =
  let u = uint32(x)
  if u == 42'u32:
    symexTarget("reinterpret_decline_target")

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

suite "symex round-6 B2 — recorded declines (narrowing, same-width reinterpret)":

  test "B2-9: narrowing int conversion declines cleanly (classified sxUnknown, not a crash)":
    let r = symexFind(narrowingDecline, tLabel("narrow_decline_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("narrowing" in it.msg)

  test "B2-10: same-width signedness reinterpret declines cleanly (classified sxUnknown, not a crash)":
    let r = symexFind(reinterpretDecline, tLabel("reinterpret_decline_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("reinterpret" in it.msg)

  test "B2-13: byte(x) narrowing declines cleanly (classified sxUnknown, not a crash — rider)":
    let r = symexFind(narrowingDeclineByteTarget, tLabel("narrow_decline_byte_target"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == feUnsupportedExprKind)
    check r.errors.anyIt("narrowing" in it.msg)

suite "symex round-6 B2 — walker version pin":

  test "walker version floor >= 80 (byte-alias recognition + typeKind decline guard)":
    check parseInt(symexWalkerVersion) >= 80
