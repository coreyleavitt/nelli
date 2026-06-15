## Phase 15 — Cluster S, cycle S7a: `bytes(s)` byte-faithful byte-view.
##
## Under the byte-faithful string model (ADR-0006), every Z3 string character is
## ALREADY a single byte (constrained ≤0xFF at allocation, S3). So `bytes(s)` is
## the TRIVIAL identity byte-view — NOT a multi-byte UTF-8 decoding subsystem:
##
##   * `bytes(s)` → an `svSeq` of `svBV8`, one element per character position.
##   * `seqLen(bytes(s)) == len(s)` — EQUAL (byte count == char count under
##     byte-faithful), NOT `>=`.
##   * `bytes(s)[i] == intToBv[8](toCode(at(s, i)))` — reuses S3's exact
##     at→toCode→BV8 bridge.
##
## A multi-byte literal like `"é"` is already its raw 2 bytes `[0xC3, 0xA9]`
## (length 2) under byte-faithful `mkString`/`Z3_mk_lstring` — so `bytes("é")`
## is a length-2 seq of those byte values, NOT a "2-byte UTF-8 codepoint".
## `seBytesBeyondBMP` is UNREACHABLE (a char is ≤0xFF by construction; toCode
## always fits BV8), so there is NO multi-byte-rune test here.
##
## Concrete vs symbolic length is detected at the IR level (mirroring S5 split):
## a string LITERAL receiver (`iekStrLit`) has a known byte count; a bare
## `string` parameter does not → seBytesSymbolicLength (sxUnknown, Invariant 3).
## So the concrete cases call `bytes` on a LITERAL while the `string` parameter
## is present only so the witness has a parameter (the S5 split idiom).
import std/unittest
import proptest/symex

# `bytes` is not a Nim stdlib proc; the symex parser intercepts it by NAME on an
# `itString` receiver (smkStrBytes → iekStrBytes). The body never runs under
# symex (the walker models the call, not its source). A local shim returning
# `seq[byte]` lets Nim typecheck and `classifyType` see `seq[byte]` so the `[]`
# index path lowers to the BV8 element. (Mirrors S5's `replaceAll` shim.)
proc bytes(s: string): seq[byte] =
  for c in s: result.add byte(c)

# --- length-1 literal: bytes("A")[0] == 65 ('A') ---
# Index inline (no `let` of a `byte`-typed local — the seq index path classifies
# the SEQ and uses its BV8 element type, no `byte`-name lookup needed).
proc bytesAIs65(s: string) =
  if s == "x":
    if bytes("A").len == 1 and bytes("A")[0] == 65'u8:
      symexTarget("hit")

# --- multi-byte literal: bytes("é") is the raw 2 bytes [0xC3, 0xA9] ---
# byte-faithful: "é" is ALREADY 2 byte-chars, so bytes is length-2 with those
# raw byte values — NOT a single 2-byte UTF-8 codepoint.
proc bytesEacuteIs2(s: string) =
  if s == "x":
    if bytes("é").len == 2 and bytes("é")[0] == 0xC3'u8 and
       bytes("é")[1] == 0xA9'u8:
      symexTarget("hit")

# --- len(bytes(s)) == len(s): EQUAL under byte-faithful ---
# Concrete s pinned to a literal; bytes over the same literal. Both are 5.
proc bytesLenEqualsStrLen(s: string) =
  if s == "hello" and bytes("hello").len == s.len:
    symexTarget("hit")

# --- symbolic length: bytes(s) on a bare parameter → seBytesSymbolicLength ---
proc bytesSymbolicLen(s: string) =
  if bytes(s).len == 3:
    symexTarget("hit")

# --- concrete length > maxBytesEncodingLen (default 32) → seBytesLengthTooLarge ---
# A 33-byte literal exceeds the cap.
proc bytesTooLong(s: string) =
  if s == "x":
    if bytes("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa").len == 33:  # 33 'a's
      symexTarget("hit")

suite "symex Phase 15 S7a — bytes(s) byte-faithful byte-view":
  test "bytes(\"A\") is length-1 with bytes[0] == 65 (sat)":
    let r = symexFind(bytesAIs65, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "bytes(\"é\") is the raw 2 bytes @[0xC3, 0xA9] (byte-faithful, sat)":
    let r = symexFind(bytesEacuteIs2, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "x"

  test "len(bytes(s)) == len(s) — EQUAL under byte-faithful (sat)":
    let r = symexFind(bytesLenEqualsStrLen, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "symbolic-length bytes(s) → sxUnknown + seBytesSymbolicLength":
    let r = symexFind(bytesSymbolicLen, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seBytesSymbolicLength

  test "concrete length > maxBytesEncodingLen → sxUnknown + seBytesLengthTooLarge":
    let r = symexFind(bytesTooLong, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seBytesLengthTooLarge
