## Phase 16 A8 — `toHex` / `toBin` fixed-width radix formatting.
##
## Implements BV-nibble-extract + ITE digit-table encoding for fixed-width int
## types (int8/16/32/64, uint8/16/32/64 under ADR-0001 BV abstraction).
## Result is an svString so `toHex(x) == "FF"` dispatches to string-eq
## (cmpString), not BV-eq (eqBV) — the critical dispatch property.
##
## Supported:
##   toHex(x: uint8)         → 2-char uppercase hex (raw two's-complement bits)
##   toHex(x: uint16)        → 4-char hex (same)
##   toBin(x: uint8, 8)      → 8-char binary with literal-len arg
##
## Degraded → sxUnknown (Invariant 3 — never a crash/silent UNSAT):
##   toOct(...)              → iekStrUnsupported (no Z3 oct primitive)
##   toHex(x, n)             → iekStrUnsupported when n is symbolic
##
## Walker version pin: "35" (A7-S1 Rune codepoint model bumped 34→35; A8 landed at 33).

import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---- SUT 1: toHex(x: uint8) full-width, 2 hex chars -------------------------
# toHex(255'u8) == "FF" under Nim std/strutils (raw bits, uppercase, no sign)
proc hexU8(x: uint8) =
  if toHex(x) == "FF":
    symexTarget("hex8")

# ---- SUT 2: toHex(x: uint16) full-width, 4 hex chars ------------------------
# Use "0000" (x=0) — all nibbles = 0, the simplest possible 4-digit constraint.
# This validates the 4-digit zero-padded format for uint16 without complex multi-theory.
proc hexU16(x: uint16) =
  if toHex(x) == "0000":
    symexTarget("hex16")

# ---- SUT 3: toBin(x: int64, 8) → 8-char binary ------------------------------
# toBin takes BiggestInt (= int64 on 64-bit). Use int64 directly to avoid the
# Nim implicit coercion that confuses classifyType. int64 = BV64 under ADR-0001.
# toBin(10'i64, 8) == "00001010": base-2 with 8 literal digits, MS bit first.
proc binLow(x: int64) =
  if toBin(x, 8) == "00001010":
    symexTarget("bin8")

# ---- SUT 4a: toOct → sxUnknown (no Z3 oct primitive, sound degrade) ---------
# toOct takes BiggestInt (= int64). Use int64 to avoid implicit coercion confusion.
proc octDegrade(x: int64) =
  if toOct(x, 3) == "377":
    symexTarget("oct")

# ---- SUT 4b: toHex with symbolic (non-literal) len → sxUnknown --------------
# Passes `n` as a runtime param so the parser sees a non-literal len and degrades.
# toHex is generic (SomeInteger), so uint8 works here.
proc hexDynLen(x: uint8, n: int) =
  if toHex(x, n) == "FF":
    symexTarget("hexDyn")

suite "symex Phase 16 A8 — toHex/toBin BV-nibble radix formatting":

  test "toHex(x: uint8) == \"FF\" → sxSat, witness x == 255":
    ## toHex(-1'u8) / toHex(255'u8) produces "FF" — raw two's-complement bits,
    ## uppercase, no sign. The BV-nibble-extract + ITE digit table picks x=255.
    let r = symexFind(hexU8, tLabel("hex8"))
    check r.status == sxSat
    # Witness: x == 255 (the unique uint8 with toHex == "FF")
    check r.witness[0] == 255

  test "toHex(x: uint16) == \"0000\" → sxSat, witness x == 0":
    ## Full-width 4-char hex for uint16: toHex(0'u16) == "0000".
    ## Validates 4-digit zero-padding; all nibbles are 0, simplest 4-char case.
    let r = symexFind(hexU16, tLabel("hex16"))
    check r.status == sxSat
    check r.witness[0] == 0

  test "toBin(x: int64, 8) == \"00001010\" → sxSat, witness x == 10":
    ## toBin takes BiggestInt (= int64); BV64 under ADR-0001.
    ## toBin(10, 8) == "00001010" (binary with literal len=8, MS bit first).
    ## The 1-bit ITE chain covers 8 positions; bits 3 and 1 are set for 10 = 0b1010.
    let r = symexFind(binLow, tLabel("bin8"))
    check r.status == sxSat
    check r.witness[0] == 10

  test "toOct → sxUnknown (no Z3 oct primitive, Invariant 3 sound degrade)":
    ## toOct is not modeled (iekStrUnsupported → seUnsupportedStringOp).
    ## Must never crash or produce a silent UNSAT.
    let r = symexFind(octDegrade, tLabel("oct"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

  test "toHex with symbolic (dynamic) len → sxUnknown (non-literal len degrades)":
    ## toHex(x, n) where n is a runtime parameter is not encodable (the digit
    ## chain length would be symbolic → unbounded). Parser routes to
    ## iekStrUnsupported; boundary maps to seUnsupportedStringOp → sxUnknown.
    let r = symexFind(hexDynLen, tLabel("hexDyn"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedStringOp

suite "symex Phase 16 A8 — walker version pin":

  test "walker version is now 35 (A7-S1 Rune codepoint model, 34→35; A8 iekRadixFmt landed at 33)":
    ## A7-S1 (Rune as tInt(64,true) pinned [0,0x10FFFF], ADR-0017 Path B) bumped to v35.
    ## A9 ASCII case-fold bumped to v34; A8's iekRadixFmt landed at v33.
    check symexWalkerVersion == "35"
