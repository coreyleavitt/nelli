## RFC-0005 S8cr (DoD §6 item 3): the checked justification §4.3 asks for, for
## pins that flipped to `sxUnsat` in the structural slices, without one.
##
## `scripts/rfc0005-flips.py` regenerates the flip list and reads the
## `# flip: <sha> <file>` markers below, so each flip stays tied to its commit.
## The SUTs are copies: a test file cannot import another without running its
## suites. Each check runs `checkUnsatOverTaintOnly`, which asserts `sxUnsat`
## and that no drained decline carries `scIncomplete`. The regex and pair-loop
## flips are in `tsymex_rfc0005_s8cr_flips_str.nim`.
##
## Most of these flips are exact-model flips: the run drains no decline, and the
## helper accepts it as the degenerate over-taint-only run. Two families do drain
## one, and `justifyOver` names it: `feConvFloatToIntUndefined` and
## `seParseIntLaxSyntax`. It also names the `hePtrFamily` hint on the kept pointer.
import std/[unittest, math, sequtils, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    result.add $e.kind & "/" & $e.severity & " "

template justify(sut: untyped; tgt: untyped) =
  let r = symexFind(sut, tgt)
  checkpoint $r.status & " " & show(r.errors)
  checkUnsatOverTaintOnly(r)

template justifyOver(sut: untyped; tgt: untyped; drained: SymexErrorKind) =
  ## The run drains `drained`, so the helper is what separates this from a run
  ## that lost executions: the entry is present and carries no `scIncomplete`.
  let r = symexFind(sut, tgt)
  checkpoint $r.status & " " & show(r.errors)
  check r.errors.anyIt(it.kind == drained)
  checkUnsatOverTaintOnly(r)

template justifyWith(sut: untyped; tgt: untyped; settings: untyped) =
  let r = symexFind(sut, tgt, settings)
  checkpoint $r.status & " " & show(r.errors)
  checkUnsatOverTaintOnly(r)

# ---- by-reference and heap ----------------------------------------------------

var gFlipP: ptr int

proc flKeepPtr[T](p: ptr T, k: T) =
  gFlipP = p
  p[] = k

proc flGenericEscape(k: int) =
  var x = 0
  flKeepPtr(addr x, k)
  gFlipP[] = 7
  if x != 7: symexTarget("ge_dead")

type FlAugPoint = object
  x, y: int

proc flSeqElemAug(p: FlAugPoint, b: int) =
  if b > 0 and b < 1000 and p.x > 0 and p.x < 1000 and p.y > 0 and p.y < 1000:
    var q = @[p.x, p.y]
    q[b and 1] += b
    if q[b and 1] == p.x + p.y + b + 1:
      symexTarget("seq_elem_aug_dead")

suite "flips to sxUnsat: by-reference and heap":
  # flip: 7e9797b2 tsymex_rfc0005_s8bd_remainder
  test "S8ax's address cell holds the kept pointer's write (was a heUnsafeCast decline)":
    justifyOver(flGenericEscape, tLabel("ge_dead"), hePtrFamily)
  # flip: 2bc6831c tsymex_augmented_assign
  test "S8am models a seq element's += (was a decline)":
    justify(flSeqElemAug, tLabel("seq_elem_aug_dead"))

# ---- construction and zero values ---------------------------------------------

type
  FlDecodeError = object of CatchableError
  FlPktOp = enum pkData, pkAck
  FlPkt = object
    case opcode: FlPktOp
    of pkData:
      blockNum: uint16
      payload: seq[byte]
    of pkAck:
      ackBlockNum: uint16
  FlBag = object
    tag: int
    xs: seq[int]
  FlOp = enum opRrq, opWrq
  FlTwoTag = object
    tag: int
    case opcode: FlOp
    of opRrq: rq: int
    of opWrq: wq: int
  FlKa = enum kaX, kaY
  FlKb = enum kbP, kbQ
  FlTwoAxis = object
    case axis1: FlKa
    of kaX: a1: int
    of kaY: a2: int
    case axis2: FlKb
    of kbP: b1: int
    of kbQ: b2: int
  FlVK = enum svkA, svkB
  FlV = object
    case k: FlVK
    of svkA: a: int
    of svkB: b: int

proc flReadU16(data: seq[byte], offset: int): uint16 =
  if offset + 2 > data.len:
    raise newException(FlDecodeError, "truncated")
  result = uint16(data[offset]) shl 8 or uint16(data[offset + 1])

proc flOmittedSeqField(data: seq[byte]) =
  let wireOp = flReadU16(data, 0)
  if wireOp == 3'u16:
    let pkt = FlPkt(opcode: pkData, blockNum: 5'u16)
    if pkt.payload.len != 0 or pkt.blockNum != 5'u16:
      symexTarget("omitted_seq_field_dead")

proc flBagOmitted(x: int) =
  let b = FlBag(tag: x)
  if b.tag == 5 and b.xs.len != 0:
    symexTarget("bag_omitted_seq_dead")

proc flMultiVariant(x: int) =
  let t = FlTwoAxis(axis1: kaX, a1: x, axis2: kbP, b1: x)
  if t.a1 != t.b1 or t.axis2 != kbP:
    symexTarget("multivariant_dead")

proc flClosureStringZero(x: int) =
  let f = proc(y: int): string =
    if y > 0:
      result = "hit"
  let r = f(x)
  if x <= 0 and r != "":
    symexTarget("closure_string_zero_nonempty")

proc flClosureVariantZero(x: int) =
  let g = proc (y: int): FlV =
    if y > 0: return
    result = FlV(k: svkB, b: 3)
  let v = g(x)
  discard v
  if x == 5 and x == 6: symexTarget("s8m_closret_variant_dead")

proc flFreshNonzero(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = FlTwoTag(opcode: op, tag: n)
  if p.opcode == opRrq and p.rq == 777:
    symexTarget("fresh_rq_777")

proc flFreshOtherFork(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = FlTwoTag(opcode: op, tag: n)
  if p.opcode == opWrq and p.wq == 555:
    symexTarget("fresh_wq_555")

suite "flips to sxUnsat: construction and zero values":
  # flip: 460c51e1 tsymex_r6_a6r_callwitness
  test "S8at: a case object's omitted seq field is Nim's zero":
    justify(flOmittedSeqField, tLabel("omitted_seq_field_dead"))
  # flip: d248772e tsymex_r8_omitted_field_degrade
  test "S8aj: an object's omitted seq field is Nim's zero":
    justify(flBagOmitted, tLabel("bag_omitted_seq_dead"))
  # flip: fd18b2f5 tsymex_r6_a1_variantlit
  test "S8p: a multi-case-object constructor constructs":
    justify(flMultiVariant, tLabel("multivariant_dead"))
  # flip: fd18b2f5 tsymex_r6_n16_closure_zerodefault
  test "S8p: a string closure's untouched result is empty":
    justify(flClosureStringZero, tLabel("closure_string_zero_nonempty"))
  # flip: 54cb9f0c tsymex_rfc0005_s8m_exits
  test "S8n: a variant closure's bare return is its zero value":
    justify(flClosureVariantZero, tLabel("s8m_closret_variant_dead"))
  # flip: f5e618a5 tsymex_r6_a3_variantconstruct_sym
  test "S8f: an arm field of a runtime-discriminator constructor is its default (was a false sxSat)":
    justify(flFreshNonzero, tLabel("fresh_rq_777"))
    justify(flFreshOtherFork, tLabel("fresh_wq_555"))

# ---- numeric models -----------------------------------------------------------

proc flF2iUnbound(x: float) =
  if int(x) == 3: symexTarget("f2i_unbound")

proc flF2iNan(x: float) =
  if isNaN(x) and int(x) == 3: symexTarget("f2i_nan")

proc flF2iInf(x: float) =
  if x == Inf and int(x) == 3: symexTarget("f2i_inf")

proc flI32Conv(x: float) =
  if int32(x) == 5'i32: symexTarget("i32conv")

proc flF2iLet(x: float) =
  let v = int(x)
  if v == 7: symexTarget("cr9_floatIntLet_hit")

proc flInt32Width(f: float) =
  let i = int32(f)
  discard i
  symexTarget("rdInt32Hit")

proc flSplitEmptySep(s: string) =
  if s == "x":
    let parts = "abcde".split("")
    if parts.len == 5:
      symexTarget("hit")

proc flParsePlusDigit(s: string) =
  if s == "+5":
    discard parseInt(s)

proc flEacuteOneChar(s: string) =
  if s == "é" and s.len == 1:
    symexTarget("hit")

const flCap3 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxSplitParts = 3

suite "flips to sxUnsat: numeric and string models":
  # flip: b744fcde tsymex_phase15_CR3_CR4_CR6_float
  test "S8g: a float -> int conversion has no RangeDefect (was a false sxRaised)":
    justifyOver(flF2iUnbound, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
    justifyOver(flF2iNan, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
    justifyOver(flF2iInf, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
    justifyOver(flI32Conv, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
  # flip: b744fcde tsymex_phase15_F5_float_conv
  test "S8g: the same, on F5's SUT":
    justifyOver(flF2iUnbound, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
  # flip: b744fcde tsymex_phase15_cr9_lowerInExpr
  test "S8g: the same, in a let":
    justifyOver(flF2iLet, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
  # flip: b744fcde tsymex_phase16_R16_2_rangedefect
  test "S8g: the same, at width 32":
    justifyOver(flInt32Width, tRaisedExn("RangeDefect"), feConvFloatToIntUndefined)
  # flip: b744fcde tsymex_phase15_CR11_CR18_splitcap
  test "S8g: split on an empty separator is one part under any cap":
    justifyWith(flSplitEmptySep, tLabel("hit"), flCap3)
  # flip: 60048323 tsymex_rfc0005_s10_replay_verdict
  test "S8b: parseInt(\"+5\") parses, so no ValueError":
    justifyOver(flParsePlusDigit, tRaisedExn("ValueError"), seParseIntLaxSyntax)
  # flip: 3a958448 tsymex_phase15_S7a_bytes
  test "S8c: \"é\" is two bytes, through real code rather than the deleted model":
    justify(flEacuteOneChar, tLabel("hit"))

suite "RFC-0005 S8cr (flips): walker version":
  test "symexWalkerVersion >= 245 (no walker change: this slice adds pins)":
    check parseInt(symexWalkerVersion) >= 245
