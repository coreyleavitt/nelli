## Round-6 A6-rider (walker v86), required precursor to Track B's B7.
##
## Chapulin's BLOCKER #12 ("`seq[byte]` witness extraction loses fidelity
## through a helper-proc read — an otherwise-genuine `sxSat` reports an
## all-zero witness", `docs/proptest-findings.md`, and the doc comment above
## `decodeFixedArmsTwin` in chapulin's `tests/t_symex_decode.nim`) turned out,
## on isolated bisection in THIS file, to be the visible SYMPTOM of a deeper
## SOUNDNESS gap, not a pure witness-rendering issue.
##
## ---- Root cause -------------------------------------------------------
## `runtime.nim`'s `isCall` arm allocates one fresh, unconstrained `retSym`
## per call and binds it to the caller's `stmt.retName`. A callee exits its
## body one of two ways:
##   (a) an explicit `return expr` — `isReturn`'s handler correctly ties
##       `retSym` to the returned value via `retBindEq`.
##   (b) an IMPLICIT fallthrough (body runs off the end) after a
##       CONDITIONAL, multi-statement `result = expr` assignment.
##       `parseCalleeImpl`'s own comment documents this as the "general
##       parser path" (a proc body that isn't a single bare `result = expr`
##       expression) and flags it as needing further work to model `result`
##       as a mutable binding. Pre-fix, THIS PATH NEVER BOUND `retSym` TO
##       ANYTHING — it reached the caller totally free. Z3 was then free to
##       satisfy any downstream comparison against it independent of what
##       the callee's body actually computed from its arguments.
##
## This is confirmed (R5 below) to be a genuine FALSE-POSITIVE generator,
## not merely cosmetic: a deliberately UNREACHABLE target (whose
## impossibility depends structurally on the callee's own `seq[byte]`
## argument content) proved a false `sxSat` pre-fix, with the reported
## witness floating completely free of the solver's actual (nonexistent)
## justification — exactly explaining chapulin's "all-zero witness on an
## otherwise sxSat target" symptom: Z3 satisfies the target directly through
## the free `retSym` and defaults every untouched `data` array cell to 0.
##
## `runtime.nim`'s closure-call path (`applyClosureGround`) already handles
## this exact shape correctly, via `retBindEq(funcApp, cp.env["result"])`.
## The fix mirrors that established idiom into the ordinary call-inlining
## `isCall` arm.
##
## ---- Version discipline -------------------------------------------------
## Because the fix changes VERDICTS (a previously-false `sxSat` now
## correctly reports `sxUnsat`), this is NOT an extraction-only rider like
## the B4-rider precedent — `symexWalkerVersion` bumps 85→86 (not just
## `renderAsChoicesVersion`, which also bumps 9→10 in lockstep since
## witness CONTENT for the affected shape genuinely changes too). See
## `canonicalize.nim`'s own doc comments on both constants for the full
## writeup, and `tests/tsymex_phase15_CR2_cachekey.nim`'s updated exact
## pins.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type DecodeError = object of CatchableError

# ---------------------------------------------------------------------------
# 1. Minimal RED repro (confirmed pre-fix): a callee whose body has a
#    CONDITIONAL guard (raise) before an explicit `result = expr`
#    assignment, called through a helper-proc boundary. Pre-fix this
#    reported witness `@[0, 0]` for a target requiring `@[1, 3]`.
# ---------------------------------------------------------------------------

proc readU16Helper(data: seq[byte], offset: int): uint16 =
  ## The BLOCKER #12 shape: a bounds-checked helper computing a 2-byte
  ## big-endian value, mirroring chapulin's real `readUint16BE`
  ## (`protocol.nim`) almost verbatim — including its own truncation guard
  ## BEFORE the value computation, the exact "conditional guard, then
  ## result assignment, implicit fallthrough" shape that left `retSym`
  ## unconstrained pre-fix.
  if offset + 2 > data.len:
    raise newException(DecodeError,
      "Truncated packet: need 2 bytes at offset " & $offset)
  result = uint16(data[offset]) shl 8 or uint16(data[offset + 1])

proc sutHeaderViaHelper(data: seq[byte]) =
  let wireOp = readU16Helper(data, 0)
  if wireOp == 259'u16:   # 0x0103 -- hi=1, lo=3 (both bytes nonzero: a
                          # zero witness cannot masquerade as "coincidentally
                          # correct" the way an all-zero wireOp target would)
    symexTarget("wireop_259_helper")

# ---------------------------------------------------------------------------
# 2. Control: the IDENTICAL read, inlined (no helper) -- must already report
#    a correct witness both before and after the fix, isolating the call
#    boundary as the variable under test.
# ---------------------------------------------------------------------------

proc sutHeaderInline(data: seq[byte]) =
  if data.len < 2:
    raise newException(DecodeError, "too short")
  let wireOp = (uint16(data[0]) shl 8) or uint16(data[1])
  if wireOp == 259'u16:
    symexTarget("wireop_259_inline")

suite "symex round-6 A6-rider -- seq[byte] witness fidelity through a helper-proc read":

  test "R1: proof is sound -- wireOp==259 genuinely reachable through the helper (sxSat)":
    let r = symexFind(sutHeaderViaHelper, tLabel("wireop_259_helper"))
    check r.status == sxSat

  test "R2: witness CONTENT matches the solved model, not an all-zero default (BLOCKER #12)":
    let r = symexFind(sutHeaderViaHelper, tLabel("wireop_259_helper"))
    check r.status == sxSat
    let data = r.witness[0]
    check data.len >= 2
    check data[0] == 1'u8
    check data[1] == 3'u8

  test "R3: witness, replayed through the real helper proc, reproduces the exact found outcome":
    let r = symexFind(sutHeaderViaHelper, tLabel("wireop_259_helper"))
    check r.status == sxSat
    let data = r.witness[0]
    check readU16Helper(data, 0) == 259'u16

  test "R4 control: the inline (no-helper) sibling already reports correct witness content":
    let r = symexFind(sutHeaderInline, tLabel("wireop_259_inline"))
    check r.status == sxSat
    let data = r.witness[0]
    check data.len >= 2
    check data[0] == 1'u8
    check data[1] == 3'u8

# ---------------------------------------------------------------------------
# 3. Soundness pin: the actual bug class. A target that is UNREACHABLE under
#    real Nim semantics -- by construction, `readU16Helper`'s low byte is
#    ALWAYS exactly `data[offset + 1]` -- proved a FALSE sxSat pre-fix (the
#    unconstrained retSym let Z3 pick a value with no relationship to
#    `data` at all). This is the pin that distinguishes "extraction
#    cosmetic issue" from "the proof itself was unsound", and is the reason
#    this rider bumps `symexWalkerVersion`, not just `renderAsChoicesVersion`.
# ---------------------------------------------------------------------------

proc sutImpossibleLowByteMismatch(data: seq[byte]) =
  let wireOp = readU16Helper(data, 0)
  if (int(wireOp) mod 256) != int(data[1]):
    symexTarget("impossible_low_byte_mismatch")

suite "symex round-6 A6-rider -- soundness pin (the real bug class)":

  test "R5: a target impossible under real semantics is sxUnsat, not a false sxSat":
    let r = symexFind(sutImpossibleLowByteMismatch, tLabel("impossible_low_byte_mismatch"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# 4. Composition: TWO call hops (a helper calling a helper), and a MIXED
#    inlined + helper read within the same SUT -- both required compositions
#    per the rider's scope.
# ---------------------------------------------------------------------------

proc atByteHelper(data: seq[byte], i: int): byte =
  if i >= data.len:
    raise newException(DecodeError, "out of range")
  data[i]

proc readU16TwoHop(data: seq[byte], offset: int): uint16 =
  ## Two call hops from the SUT: sut -> readU16TwoHop -> atByteHelper.
  let hi = atByteHelper(data, offset)
  let lo = atByteHelper(data, offset + 1)
  result = (uint16(hi) shl 8) or uint16(lo)

proc sutTwoCallHops(data: seq[byte]) =
  let wireOp = readU16TwoHop(data, 0)
  if wireOp == 259'u16:
    symexTarget("wireop_259_twohop")

suite "symex round-6 A6-rider -- composition: two call hops":

  test "R6: witness content survives a helper calling ANOTHER helper":
    let r = symexFind(sutTwoCallHops, tLabel("wireop_259_twohop"))
    check r.status == sxSat
    let data = r.witness[0]
    check data.len >= 2
    check data[0] == 1'u8
    check data[1] == 3'u8

  test "R7: replayed through the real two-hop helper, reproduces the exact found outcome":
    let r = symexFind(sutTwoCallHops, tLabel("wireop_259_twohop"))
    check r.status == sxSat
    let data = r.witness[0]
    check readU16TwoHop(data, 0) == 259'u16

proc sutMixedInlineAndHelper(data: seq[byte]) =
  ## One field read INLINE (wireOp, this proc's own body) and one read
  ## ONLY through a helper (blockNum) -- the exact composition
  ## `decodeFixedArmsTwin` itself exercises (BLOCKER #11's inline header
  ## read alongside a helper-mediated field elsewhere in the real file).
  if data.len < 4:
    raise newException(DecodeError, "too short")
  let wireOp = (uint16(data[0]) shl 8) or uint16(data[1])
  if wireOp == 3'u16:
    let blockNum = readU16Helper(data, 2)
    if blockNum == 5'u16:
      symexTarget("mixed_inline_and_helper")

suite "symex round-6 A6-rider -- composition: mixed inlined + helper reads":

  test "R8: witness content is correct for BOTH the inline field and the helper-read field":
    let r = symexFind(sutMixedInlineAndHelper, tLabel("mixed_inline_and_helper"))
    check r.status == sxSat
    let data = r.witness[0]
    check data.len >= 4
    check ((uint16(data[0]) shl 8) or uint16(data[1])) == 3'u16
    check readU16Helper(data, 2) == 5'u16

  test "R9: replayed through both the inline arithmetic and the real helper, reproduces the outcome":
    let r = symexFind(sutMixedInlineAndHelper, tLabel("mixed_inline_and_helper"))
    check r.status == sxSat
    let data = r.witness[0]
    let wireOp = (uint16(data[0]) shl 8) or uint16(data[1])
    check wireOp == 3'u16
    check readU16Helper(data, 2) == 5'u16

# ---------------------------------------------------------------------------
# 5. Constructor-omitting-seq[byte]-field finding (BLOCKER #11's companion,
#    docs/proptest-findings.md) stays OUT of scope -- pinned here only to
#    confirm the current honest degrade is unchanged by this rider (a
#    regression guard, not a fix).
# ---------------------------------------------------------------------------

type PktOp = enum
  pkData, pkAck

type Pkt = object
  case opcode: PktOp
  of pkData:
    blockNum: uint16
    payload: seq[byte]
  of pkAck:
    ackBlockNum: uint16

proc sutOmittedSeqField(data: seq[byte]) =
  let wireOp = readU16Helper(data, 0)
  if wireOp == 3'u16:
    # `payload` deliberately OMITTED (relies on Nim's implicit zero-init) --
    # the recorded, out-of-scope BLOCKER #11 companion finding.
    let pkt = Pkt(opcode: pkData, blockNum: 5'u16)
    if pkt.blockNum == 5'u16:
      symexTarget("omitted_seq_field")

suite "symex round-6 A6-rider -- constructor-omitting-seq[byte]-field stays out of scope":

  test "R10: unchanged honest degrade (sxUnknown), not newly broken by this rider's fix":
    let r = symexFind(sutOmittedSeqField, tLabel("omitted_seq_field"))
    check r.status == sxUnknown

suite "symex round-6 A6-rider -- version pins":

  test "walker version floor >= 86 (soundness fix -- implicit-result-fallthrough call-boundary binding)":
    check parseInt(symexWalkerVersion) >= 86

  test "renderAsChoicesVersion floor >= 10 (lockstep bump -- witness content changes alongside the verdict fix)":
    check parseInt(renderAsChoicesVersion) >= 10
