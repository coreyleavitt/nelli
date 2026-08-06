## Chapulin 0.1.0 re-test triage — catalog #3 residual (CRASH class), walker
## v64. A BITWISE `and`/`or` spelled with Nim's shared `and`/`or` identifiers
## used to enter the D1c short-circuit lift whenever its RHS carried a
## defect-forking op (e.g. an index access): the guarded path bound the
## BV-valued LHS into a `tBool()` temp and emitted `uNot(temp)`, crashing at
## the walker's `doAssert inner.kind == svBool` (uncaught AssertionDefect,
## reported by chapulin at runtime.nim:3155 via lowerBoolInExpr/lowerBool).
##
## Empirical repro (this exact file's `readU16Inline` + guard composition)
## crash-verified against v63 on 2026-08-06 before the fix landed; the twin
## with the combine's operands pre-bound to `let`s (fast path — empty RHS
## preamble) never crashed, which is why chapulin's re-test bisected it to
## "bitwise combine + later boolean guard" — the guard was D1c's own
## synthetic or-guard, not the user's.
##
## The UNSAT-side tests are load-bearing soundness pins: a stub that merely
## avoided the crash by fabricating an unconstrained result would report
## them sxSat.
import std/unittest
import std/sets
import std/strutils
import proptest/symex
import proptest/smt/canonicalize

type DecodeError = object of CatchableError

# ---- the chapulin decode composition: inline big-endian combine ------------

proc readU16Inline(data: seq[byte], offset: int): uint16 =
  ## `uint16(data[offset + 1])` in the RHS is the defect-forking op that
  ## used to trip the D1c guarded path on a BITWISE `or`.
  if offset + 2 > data.len:
    raise newException(DecodeError, "Truncated at " & $offset)
  result = (uint16(data[offset]) shl 8) or uint16(data[offset + 1])

proc bitGuardCombo(data: seq[byte]) =
  if data.len < 2:
    raise newException(DecodeError, "Packet too short")
  let wireOp = readU16Inline(data, 0)
  if wireOp < 1 or wireOp > 6:
    raise newException(DecodeError, "Invalid opcode")

# ---- direct bitwise-or with a defect-forking RHS ---------------------------

proc orBothZeroSat(data: seq[byte]) =
  if data.len < 2:
    raise newException(DecodeError, "short")
  if (uint16(data[0]) or uint16(data[1])) == 0'u16:
    symexTarget("both-zero")

proc orImpossibleUnsat(data: seq[byte]) =
  ## `(3 or y) == 4` is impossible — bits 0..1 are always set in the result.
  if data.len < 2:
    raise newException(DecodeError, "short")
  if (3'u16 or uint16(data[1])) == 4'u16:
    symexTarget("impossible-or")

# ---- prefix `not` on a BV operand (the uNot arm's bitwise-complement fix) --

proc notComplementSat(data: seq[byte]) =
  if data.len < 1:
    raise newException(DecodeError, "short")
  if (not data[0]) == 0xFF'u8:
    symexTarget("complement-hit")

proc notSelfUnsat(data: seq[byte]) =
  ## `(not x) == x` is impossible at any BV width.
  if data.len < 1:
    raise newException(DecodeError, "short")
  if (not data[0]) == data[0]:
    symexTarget("impossible-not")

# ---- HashSet membership keyed by an svInt-producing expression -------------

proc lenInSet(s: string, hs: HashSet[int]) =
  ## `.len` lowers unconditionally to svInt (CR-1a); the membership key
  ## doAssert used to native-crash on it — now bridged via svIntToBV.
  if s.len in hs:
    symexTarget("len-member")

suite "symex re-test C3 — bitwise and/or vs the D1c short-circuit lift":

  test "inline shl/or combine + boolean guard (decode's own shape) no longer crashes; sxUnsat":
    let r = symexFind(bitGuardCombo, tIndexError())
    check r.status == sxUnsat

  test "bitwise or with defect-forking RHS: SAT witness has both bytes zero":
    let r = symexFind(orBothZeroSat, tLabel("both-zero"))
    check r.status == sxSat
    check r.witness[0].len >= 2
    check (r.witness[0][0] or r.witness[0][1]) == 0'u8

  test "(3 or y) == 4 is UNSAT (soundness — a fabricated result would be SAT)":
    let r = symexFind(orImpossibleUnsat, tLabel("impossible-or"))
    check r.status == sxUnsat

suite "symex re-test C3 — prefix `not` on a BV operand (uNot arm)":

  test "bitwise complement models correctly: SAT witness byte is 0":
    let r = symexFind(notComplementSat, tLabel("complement-hit"))
    check r.status == sxSat
    check r.witness[0].len >= 1
    check r.witness[0][0] == 0'u8

  test "(not x) == x is UNSAT (soundness)":
    let r = symexFind(notSelfUnsat, tLabel("impossible-not"))
    check r.status == sxUnsat

suite "symex re-test C3 — HashSet membership keyed by svInt":

  test "s.len in HashSet[int]: sxSat with a CONSISTENT witness":
    ## v64 fixed the crash (svBV64 key assert → svIntToBV bridge) but the
    ## extracted witness still missed symbolically-keyed members (`s = ""`,
    ## `hs = {}` — the literal-candidate scan cannot see an `int2bv(len(s))`
    ## key). v65 harvests the model's own store chain
    ## (`harvestSetStoreKeys`), so the witness must now be consistent.
    let r = symexFind(lenInSet, tLabel("len-member"))
    check r.status == sxSat
    check r.witness[0].len in r.witness[1]

suite "symex re-test C3 — walker version pin":

  test "walker version floor >= 64 (bitwise/short-circuit split + uNot/lowerBool/set-key degrades)":
    check parseInt(symexWalkerVersion) >= 64
