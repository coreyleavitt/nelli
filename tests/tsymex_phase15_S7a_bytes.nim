## Phase 15 — Cluster S, cycle S7a: byte-faithful byte view.
##
## RFC-0005 S8c rewrite. S7a shipped a `bytes(s)` model (`smkStrBytes` ->
## `iekStrBytes`) that the parser reached BY NAME on a string receiver. Nim's
## stdlib has no `bytes(string)`, so the only way to reach that model was a
## USER proc named `bytes` -- the silent-substitution class S8c removes (the
## user's body was never walked; the model stood in for it). S8c deleted the
## model, its `seBytesSymbolicLength` / `seBytesLengthTooLarge` kinds (retired)
## and the `maxBytesEncodingLen` budget that capped it. This file now pins:
##
##   * a user `bytes` helper is WALKED as an ordinary user call. Its body
##     iterates a string (`for c in s`), which the walker declines at parse
##     time with a recorded `seByteIterUnsupported` -- so every SUT through it
##     is `sxUnknown`, never a verdict borrowed from the deleted model;
##   * the byte-faithful facts the model asserted (ADR-0006: a Z3 string
##     character IS one Nim byte; `"é"` is its raw 2 bytes `[0xC3, 0xA9]`)
##     still hold through real code: `s[i]` / `ord(s[i])` / `s.len`.
import std/unittest
import nelli/symex
import nelli/smt/types

proc bytes(s: string): seq[byte] =
  ## A user helper. NOT a model entry point: walked like any user routine.
  for c in s: result.add byte(c)

# --- through the user helper: walked, declined, recorded ---------------------

proc bytesAIs65(s: string) =
  if s == "x":
    if bytes("A").len == 1 and bytes("A")[0] == 65'u8:
      symexTarget("hit")

proc bytesSymbolicLen(s: string) =
  if bytes(s).len == 3:
    symexTarget("hit")

# --- the byte-faithful facts, through real code --------------------------------

proc eacuteIsTwoRawBytes(s: string) =
  ## byte-faithful: "é" is ALREADY 2 byte-chars -- NOT one 2-byte codepoint.
  if s == "é" and s.len == 2 and ord(s[0]) == 0xC3 and ord(s[1]) == 0xA9:
    symexTarget("hit")

proc eacuteIsNotOneChar(s: string) =
  if s == "é" and s.len == 1:
    symexTarget("hit")

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

suite "symex Phase 15 S7a — byte view (RFC-0005 S8c: no name-matched bytes model)":
  test "a user `bytes` helper over a literal is walked: sxUnknown, seByteIterUnsupported":
    let r = symexFind(bytesAIs65, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.hasKind(seByteIterUnsupported)
    check not r.errors.hasKind(seBytesLengthTooLarge)

  test "a user `bytes` helper over a parameter is walked: sxUnknown, seByteIterUnsupported":
    let r = symexFind(bytesSymbolicLen, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.hasKind(seByteIterUnsupported)
    check not r.errors.hasKind(seBytesSymbolicLength)

  test "\"é\" is the raw 2 bytes [0xC3, 0xA9] through s[i] (byte-faithful, sat)":
    let r = symexFind(eacuteIsTwoRawBytes, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "é"

  test "\"é\" is not one character (byte-faithful, unsat)":
    let r = symexFind(eacuteIsNotOneChar, tLabel("hit"))
    check r.status == sxUnsat
