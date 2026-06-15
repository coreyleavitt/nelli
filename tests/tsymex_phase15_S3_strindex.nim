## Phase 15 — Cluster S, cycle S3: string len / index / slice (byte-faithful).
##
## This is the cycle where the byte-faithful model (ADR-0006) becomes
## load-bearing. Under the ≤0xFF char-range constraint asserted on every free
## `string` variable at allocation, **Z3 position == Nim byte index**, so:
##   * `s.len`   → Z3 `(str.len s)`          == Nim byte length
##   * `s[i]`    → char from `toCode(at s i)` (the byte value at byte index i)
##   * `s[a..b]` → Z3 `(seq.extract s a (b-a+1))` byte-offset slice
##   * `s.high`  → `len(s) - 1`               (byte index of last byte)
##
## The ≤0xFF constraint is the soundness mechanism: without it Z3 could pick
## full-Unicode codepoints that don't round-trip to Nim bytes. A free `s` with
## `s.len == 1` must extract a single Nim byte (no multi-byte blowup).
##
## `s[i] == 'c'` (char comparison) is supported via the at→toCode→BV8 char
## bridge. `for c in s` (symbolic iteration over an unknown-length string) stays
## unsupported — NOT for a byte/codepoint reason but because the iteration count
## is unbounded; it classifies honestly as a string-unsupported op (sxUnknown).
import std/unittest
import proptest/symex

# --- s.len ---
proc lenIs5(s: string) =
  if s.len == 5:
    symexTarget("hit")

# --- s == lit AND substr ---
proc substrBcd(s: string) =
  if s == "abcde" and s[1..3] == "bcd":
    symexTarget("hit")

# --- single index read, char bridge: s[i] == 'c' ---
proc charAt1IsB(s: string) =
  if s == "abcde" and s[1] == 'b':
    symexTarget("hit")

# --- s.high (byte-faithful supported) ---
proc highIs4(s: string) =
  if s == "hello" and s.high == 4:
    symexTarget("hit")

# --- out-of-bounds index must not crash ---
proc oobIndex(s: string) =
  if s == "ab" and s[5] == '\0':
    symexTarget("hit")

# --- free var, len == 1: witness must be a single Nim byte (≤0xFF round-trip) ---
proc freeLen1(s: string) =
  if s.len == 1:
    symexTarget("hit")

# --- for c in s : honestly classified unsupported (unbounded iteration) ---
proc forCInS(s: string) =
  var n = 0
  for c in s:
    n.inc
  if n == 3:
    symexTarget("hit")

suite "symex Phase 15 S3 — string len/index/slice (byte-faithful)":
  test "s.len == 5 is SAT":
    let r = symexFind(lenIs5, tLabel("hit"))
    check r.status == sxSat

  test "s == \"abcde\" and s[1..3] == \"bcd\" is SAT (substr)":
    let r = symexFind(substrBcd, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abcde"

  test "s[1] == 'b' single-index char read is SAT (at->toCode->BV8 bridge)":
    let r = symexFind(charAt1IsB, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "abcde"

  test "s.high == 4 byte-faithful is SAT (len-1)":
    let r = symexFind(highIs4, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

  test "out-of-bounds s[5] does not crash":
    let r = symexFind(oobIndex, tLabel("hit"))
    # Z3 returns empty string for an out-of-range `at`; toCode -> -1. The point
    # is only that the engine does NOT crash. The status may be sat or unsat
    # depending on Z3's underspecified choice; assert it is a clean verdict.
    check r.status in {sxSat, sxUnsat}

  test "free s with s.len == 1 round-trips to a single Nim byte (<=0xFF)":
    let r = symexFind(freeLen1, tLabel("hit"))
    check r.status == sxSat
    # byte-faithful soundness: exactly one Nim byte, no multi-byte blowup.
    check r.witness[0].len == 1

  test "for c in s is honestly classified unsupported (unbounded iteration)":
    let r = symexFind(forCInS, tLabel("hit"))
    # NOT a byte/codepoint objection — symbolic unbounded iteration. sxUnknown
    # with a classified error, never a silent UNSAT (Invariant 3).
    check r.status == sxUnknown
