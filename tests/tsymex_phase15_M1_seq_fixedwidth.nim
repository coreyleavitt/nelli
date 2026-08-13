## RFC-chapulin-hardening M1 — seq[byte]/fixed-width-int witness readers
## (Cluster 3 — Model/stdlib gaps).
##
## `emitTyAndReader`'s `itSeq` arm (`symex.nim`) previously rendered a
## witness only for `seq[int64]`/`seq[float32]`/`seq[float64]`/`seq[ref T]`;
## every other seq element type — including `seq[byte]` and the rest of the
## fixed-width-int family — was gated OUT before the reader was ever reached
## by CR-2c's `isRenderableSeqElemTy` predicate (`smt/types.nim`), demoting
## the WHOLE run to a classified `sxUnknown`. M1 widens both the reader (new
## `byte`/`uint8..uint64`/`int8..int32` cases, calling new
## `readSeq{Int,UInt}{8,16,32}`/`readSeqUInt64` helpers in `smt/runtime.nim`)
## and the predicate it must stay in lockstep with, so these SUTs now
## resolve to a REAL `sxSat`/`sxUnsat` verdict with a correct witness.
##
## The walker's allocation/extraction/indexing paths (`allocateSeqDataRaw`,
## `extractSeqElements`, `seqElemAt` — `smt/runtime.nim`) already dispatched
## on every `(signed, width)` combination via typed `Z3Array[Z3Int,
## Z3BitVec[W]]` backing arrays (Phase 15 C4's seq-index/HOF plumbing); only
## the post-solve reader and its renderability gate were missing cases, so
## this slice is reader-codegen + predicate-widening only — no walker change.
##
## Walker version: 46 -> 47 (sxUnknown -> real sxSat/sxUnsat is a verdict
## change). renderAsChoicesVersion: 4 -> 5 (new witness shape).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type
  Widget = object
    a: int

# ---------------------------------------------------------------------------
# SAT SUTs — one representative per width class named in the RFC bullet.
# ---------------------------------------------------------------------------

proc sutByteSat(xs: seq[byte]) =
  ## `byte` (== `uint8`) — the RFC's headline shape (chapulin's `atByte` mask
  ## workaround target).
  if xs.len > 0 and xs[0] == 200'u8:
    symexTarget("byte_sat")

proc sutByteMaxSat(xs: seq[byte]) =
  ## Boundary value: the top of byte's range (255) — proves no truncation/
  ## wraparound bug in the width-8 unsigned round-trip.
  if xs.len > 0 and xs[0] == 255'u8:
    symexTarget("byte_max_sat")

proc sutUInt32Sat(xs: seq[uint32]) =
  ## Representative `uint32` — a value that does not fit in 8 or 16 bits,
  ## proving the width-32 unsigned reader is genuinely wired (not just
  ## reusing the byte reader under a wider declared type).
  if xs.len > 0 and xs[0] == 70000'u32:
    symexTarget("uint32_sat")

proc sutUInt64Sat(xs: seq[uint64]) =
  ## Representative `uint64` — value exceeds int32 range entirely.
  if xs.len > 0 and xs[0] == 5_000_000_000'u64:
    symexTarget("uint64_sat")

proc sutInt16Sat(xs: seq[int16]) =
  ## Representative signed fixed-width (`int16`, N<64) — a NEGATIVE witness
  ## value, proving the signed-width reader sign-extends correctly rather
  ## than reading back an unsigned bit pattern.
  if xs.len > 0 and xs[0] == -1'i16:
    symexTarget("int16_sat")

proc sutInt8Sat(xs: seq[int8]) =
  if xs.len > 0 and xs[0] == -100'i8:
    symexTarget("int8_sat")

proc sutInt32Sat(xs: seq[int32]) =
  if xs.len > 0 and xs[0] == -70000'i32:
    symexTarget("int32_sat")

# ---------------------------------------------------------------------------
# UNSAT SUT — load-bearing: proves the model actually BOUNDS a byte element
# to 0..255 (not an "always-sat" stub, not a silently-unbounded int).
# ---------------------------------------------------------------------------

proc sutByteImpossible(xs: seq[byte], n: int) =
  ## `xs[0].int == n` with `n > 300` can NEVER hold: a byte's max value is
  ## 255. (A raw literal comparison like `xs[0].int > 300` is deliberately
  ## NOT used here: the literal-lowering path steers an `iekIntLit`'s Z3
  ## representation to match a same-expression BV proto — `coerceIntLit`
  ## truncates an out-of-range literal into the operand's bit width rather
  ## than raising, an existing, unrelated quirk of literal comparisons
  ## against any fixed-width value, not something M1 touches. Comparing
  ## against a second `int` PARAMETER instead forces the genuine
  ## `reconcileInt`/`bv2int` cross-representation path: `n`'s existing
  ## `svInt` is never re-coerced by the byte's BV8 proto — `iekVar` lowering
  ## ignores proto entirely.) If the walker instead modeled a `seq[byte]`
  ## element as an unranged int (a plausible bug — e.g. wiring the wrong
  ## reader/allocator), this would be satisfiable. It must be sxUnsat.
  if xs.len > 0 and n > 300 and xs[0].int == n:
    symexTarget("byte_impossible")

# ---------------------------------------------------------------------------
# Nested-renderable guard — proves the isRenderableSeqElemTy widening
# composes through the RECURSIVE isRenderableWitnessTy (a seq[byte] nested
# inside a tuple was ALSO demoted to sxUnknown pre-M1, since
# demoteUnrenderableWitnessTy runs isRenderableWitnessTy over the whole
# top-level parameter's type tree, not just a bare seq[byte] parameter).
# ---------------------------------------------------------------------------

proc sutNestedByteTuple(x: tuple[a: seq[byte], n: int]) =
  if x.a.len > 0 and x.a[0] == 42'u8 and x.n == 7:
    symexTarget("nested_byte_tuple")

# ---------------------------------------------------------------------------
# Still-unrenderable regression guard — M1 widens the renderable set, it
# does NOT make every seq element type renderable. A genuinely-unsupported
# element type (string, or a plain object) must still degrade to sxUnknown
# via CR-2c's demoteUnrenderableWitnessTy.
# ---------------------------------------------------------------------------

proc sutSeqStringStillUnknown(xs: seq[string], y: int) =
  if y == 42:
    symexTarget("seq_string_still_unknown")

proc sutSeqWidgetStillUnknown(xs: seq[Widget], y: int) =
  if y == 42:
    symexTarget("seq_widget_still_unknown")

suite "symex RFC-chapulin-hardening M1 — seq[byte]/fixed-width-int witness readers":

  test "M1-1: seq[byte] resolves sxSat with exact witness (was sxUnknown pre-M1)":
    let r = symexFind(sutByteSat, tLabel("byte_sat"))
    check r.status == sxSat
    check r.witness[0] == @[200'u8]

  test "M1-2: seq[byte] renders the boundary value 255 exactly (no truncation)":
    let r = symexFind(sutByteMaxSat, tLabel("byte_max_sat"))
    check r.status == sxSat
    check r.witness[0] == @[255'u8]

  test "M1-3: seq[uint32] resolves sxSat with exact witness":
    let r = symexFind(sutUInt32Sat, tLabel("uint32_sat"))
    check r.status == sxSat
    check r.witness[0] == @[70000'u32]

  test "M1-4: seq[uint64] resolves sxSat with exact witness":
    let r = symexFind(sutUInt64Sat, tLabel("uint64_sat"))
    check r.status == sxSat
    check r.witness[0] == @[5_000_000_000'u64]

  test "M1-5: seq[int16] resolves sxSat with a correctly sign-extended negative witness":
    let r = symexFind(sutInt16Sat, tLabel("int16_sat"))
    check r.status == sxSat
    check r.witness[0] == @[-1'i16]

  test "M1-6: seq[int8] resolves sxSat with exact witness":
    let r = symexFind(sutInt8Sat, tLabel("int8_sat"))
    check r.status == sxSat
    check r.witness[0] == @[-100'i8]

  test "M1-7: seq[int32] resolves sxSat with exact witness":
    let r = symexFind(sutInt32Sat, tLabel("int32_sat"))
    check r.status == sxSat
    check r.witness[0] == @[-70000'i32]

  test "M1-8 (load-bearing UNSAT): seq[byte] element can never exceed 255":
    let r = symexFind(sutByteImpossible, tLabel("byte_impossible"))
    check r.status == sxUnsat

  test "M1-9 (nested-renderable guard): tuple[a: seq[byte], n: int] resolves sxSat (was sxUnknown pre-M1)":
    let r = symexFind(sutNestedByteTuple, tLabel("nested_byte_tuple"))
    check r.status == sxSat
    check r.witness[0].a == @[42'u8]
    check r.witness[0].n == 7

  test "M1-10 (regression): seq[string] element type still degrades to sxUnknown":
    let r = symexFind(sutSeqStringStillUnknown, tLabel("seq_string_still_unknown"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

  test "M1-11 (regression): seq[Widget] (object element) still degrades to sxUnknown":
    let r = symexFind(sutSeqWidgetStillUnknown, tLabel("seq_widget_still_unknown"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex RFC-chapulin-hardening M1 — version pins":

  test "walker version floor >= 47 (M1 landed at 47)":
    check parseInt(symexWalkerVersion) >= 47

  test "renderAsChoicesVersion floor >= 5 (M1 landed at 5)":
    check parseInt(renderAsChoicesVersion) >= 5
