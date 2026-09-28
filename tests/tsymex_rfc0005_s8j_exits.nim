## RFC-0005 (soundness channels) slice S8j -- S8i's unlowered exits.
## Walker 157 -> 158.
##
## S8i reported four defects whose mechanism lay outside its design. Each
## is a claim the real SUT contradicts. Every expected value was probed
## against the real compiler (Nim 2.2.10, c and cpp identical, debug build:
## rangeChecks and overflowChecks on); the probe output is quoted beside the
## test.
##   (1) the SUT's own top-level `return <expr>` is lowered and its raises
##       drained, as a callee's `return` is (R1);
##   (2) an inline `ref <case object>` field reached through a ref;
##   (3) a narrowing integer conversion range-checks into a signed target
##       and truncates into an unsigned one;
##   (4) a plain assignment to a range-typed variable checks once;
##   (5) the walker version floor.
import std/[unittest, macros, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/dsl_parser
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn`.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`)

# ---- (1) the SUT's own top-level return ---------------------------------------
#
# Probe (c and cpp identical):
#   retDiv(0)    -> DivByZeroDefect "division by zero"
#   retNat(-1)   -> RangeDefect "value out of range: -1 notin 0 .. 9223372036854775807"
#   retCaught(0) -> the handler runs (the raise is inside the `try`)
#   retFin(5)    -> the `finally` sees result == 10

proc retDiv(x: int): int =
  return 100 div x

proc resDiv(x: int): int =
  result = 100 div x

proc retNat(x: int): Natural =
  return x

proc retBranch(x: int): int =
  if x > 5:
    return 100 div (x - 10)
  result = 1

proc retCaught(x: int): int =
  try:
    return 100 div x
  except DivByZeroDefect:
    symexTarget("s8j_ret_caught")
    result = -1

proc retNoRaise(x: int): int =
  if x != 0:
    return 100 div x
  result = 0

suite "S8j (1) a top-level return lowers and drains its expression":
  test "oracle: return 100 div 0 raises DivByZeroDefect":
    expect DivByZeroDefect:
      discard retDiv(0)
    expect RangeDefect:
      discard retNat(-1)

  test "the result = form raises (control)":
    let r = symexFind(resDiv, tRaisedExn("DivByZeroDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised

  test "return 100 div x raises DivByZeroDefect (was a false sxUnsat)":
    let r = symexFind(retDiv, tRaisedExn("DivByZeroDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"
      check r.raisedWitness[0] == 0

  test "return x from a Natural proc raises RangeDefect (was a false sxUnsat)":
    let r = symexFind(retNat, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"
      check r.raisedWitness[0] < 0

  test "a return inside a branch raises on its own input":
    let r = symexFind(retBranch, tRaisedExn("DivByZeroDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] == 10

  test "a raise in a returned expression reaches its handler (was a false sxUnsat)":
    let r = symexFind(retCaught, tLabel("s8j_ret_caught"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces((discard retCaught(r.witness[0])), "s8j_ret_caught")

  test "a guarded division never raises":
    let r = symexFind(retNoRaise, tRaisedExn("DivByZeroDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

# The concolic walker follows the same arm. Real Nim: with x == 0 the
# returned `100 div x` raises, the handler runs, and `y > 3` is its one
# decision; with x == 4 it returns 25 and no handler runs.

proc concRet(x, y: int): int =
  try:
    return 100 div x
  except DivByZeroDefect:
    if y > 3: result = 1

suite "S8j (1b) the concolic walker drains a top-level return":
  test "oracle":
    check concRet(0, 5) == 1
    check concRet(4, 5) == 25

  test "a raising return enters the handler (was dropped: no handler decision)":
    let trace = @[integerChoice(0, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concRet, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

  test "a returning path makes no handler decision":
    let trace = @[integerChoice(4, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concRet, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 0

# ---- (2) an inline ref case-object field through a ref -----------------------
#
# Probe: `inlineRefCase(Holder(v: VObj(kind: vkB, b: 5)))` hits the label.

type
  S8jK = enum vkA, vkB
  S8jV = object
    case kind: S8jK
    of vkA: a: int
    of vkB: b: int
  S8jHolder = ref object
    tag: int
    v: ref S8jV

proc inlineRefCase(h: S8jHolder) =
  if h != nil and h.v != nil and h.v.kind == vkB and h.v.b == 5:
    symexTarget("s8j_inline_ref_case")

proc inlineRefAlias(h: S8jHolder; v: ref S8jV) =
  ## The field and a `ref S8jV` param are one address: a write of the
  ## discriminator through one is read through the other.
  if h != nil and v != nil and h.v == v and v.kind == vkB and h.v.b == 5:
    symexTarget("s8j_inline_ref_alias")

proc inlineRefAliasClash(h: S8jHolder; v: ref S8jV) =
  if h != nil and v != nil and h.v == v and v.kind == vkB and h.v.kind == vkA:
    symexTarget("s8j_inline_ref_clash")

proc inlineRefWrongArm(h: S8jHolder) =
  if h != nil and h.v != nil and h.v.kind == vkA:
    discard h.v.b

suite "S8j (2) an inline ref case-object field reached through a ref":
  test "oracle":
    symexCaptureBegin()
    let v = new S8jV
    v[] = S8jV(kind: vkB, b: 5)
    inlineRefCase(S8jHolder(v: v))
    check "s8j_inline_ref_case" in symexCaptureEnd()

  test "h.v.kind == vkB and h.v.b == 5 is reachable (was a false sxUnsat)":
    let r = symexFind(inlineRefCase, tLabel("s8j_inline_ref_case"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] != nil and r.witness[0].v != nil
      check reproduces(inlineRefCase(r.witness[0]), "s8j_inline_ref_case")

  test "the field and a ref param at one address are one object":
    let r = symexFind(inlineRefAlias, tLabel("s8j_inline_ref_alias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] != nil and r.witness[0].v == r.witness[1]
      check reproduces(inlineRefAlias(r.witness[0], r.witness[1]), "s8j_inline_ref_alias")

  test "one address has one discriminator":
    let r = symexFind(inlineRefAliasClash, tLabel("s8j_inline_ref_clash"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "an arm field of the wrong arm raises FieldDefect":
    let r = symexFind(inlineRefWrongArm, tFieldDefect())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "FieldDefect"
      check r.raisedWitness[0].v[].kind == vkA
      expect FieldDefect:
        inlineRefWrongArm(r.raisedWitness[0])

# ---- (3) narrowing integer conversions ---------------------------------------
#
# Probe (c and cpp identical; operands through a noinline identity):
#   int8(200)  -> RangeDefect "value out of range: 200 notin -128 .. 127"
#   int8(-200) -> RangeDefect;  int8(127) == 127;  int8(-128) == -128
#   int8(300'i16) -> RangeDefect;  int16(70000) -> RangeDefect
#   int32(1 shl 40) -> RangeDefect;  int8(-1'i64) == -1
#   uint8(-1) == 255;  uint8(300) == 44;  uint16(-1) == 65535;
#   uint32(-1) == 4294967295  -- an unsigned target never checks, it truncates
#   int8(200'u8) -> RangeDefect;  int32(high(uint32)) -> RangeDefect;
#   int(2^63'u64) -> RangeDefect  -- unsigned -> signed checks at the SAME
#   width too;  uint32(-1'i32) == 4294967295 (no check)
#   char(300) -> RangeDefect;  char(-1'i8) -> RangeDefect;  char(65) == 'A'
#   byte(300) == 44 (byte is uint8: no check)
#   int8('\xff') -> RangeDefect

proc narrow8(x: int) =
  let b = int8(x)
  discard b

proc narrow8Ok(x: int) =
  if x > 100 and x < 200:
    let b = int8(x)
    if b == 127: symexTarget("s8j_narrow8_ok")

proc narrow8Neg(x: int) =
  if x < -100:
    let b = int8(x)
    if b == -128: symexTarget("s8j_narrow8_neg")

proc narrow16From32(x: int32) =
  let s = int16(x)
  discard s

proc narrow32(x: int) =
  let s = int32(x)
  discard s

proc narrowCaught(x: int) =
  try:
    let b = int8(x)
    discard b
  except RangeDefect:
    if x == 1000: symexTarget("s8j_narrow_caught")

proc truncU8(x: int) =
  let b = uint8(x)
  if b == 44'u8 and x > 255: symexTarget("s8j_trunc_u8")

proc truncU8NoRaise(x: int) =
  let b = uint8(x)
  discard b

proc truncU16Neg(x: int) =
  if x == -1:
    let b = uint16(x)
    if b == 65535'u16: symexTarget("s8j_trunc_u16")

proc sameWidthU2S(x: uint64) =
  let i = int(x)
  discard i

proc sameWidthU32(x: uint32) =
  let i = int32(x)
  discard i

proc sameWidthS2U(x: int32) =
  let u = uint32(x)
  discard u

proc charConv(x: int) =
  let c = char(x)
  discard c

proc charConvOk(x: int) =
  if x >= 60 and x <= 70:
    let c = char(x)
    if c == 'A': symexTarget("s8j_char_ok")

proc charFromI8(x: int8) =
  let c = char(x)
  discard c

proc byteConv(x: int) =
  let b = byte(x)
  discard b

proc narrowPromoted(x: range[0..1000]) =
  ## `x` is a promoted (Int-sorted) param: the check reads its value.
  let b = int8(x)
  discard b

proc truncPromoted(x: range[0..1000]) =
  ## ... and the truncation is its value modulo 256 (744 and 1000 give 232).
  let b = uint8(x)
  if b == 232'u8 and x > 500: symexTarget("s8j_trunc_promoted")

suite "S8j (3) a narrowing int conversion range-checks into a signed target":
  test "oracle":
    proc id[T](x: T): T {.noinline.} = x
    expect RangeDefect: discard int8(id(200))
    expect RangeDefect: discard int8(id(200'u8))
    expect RangeDefect: discard int(id(9223372036854775808'u64))
    expect RangeDefect: discard char(id(300))
    check uint8(id(300)) == 44'u8
    check uint16(id(-1)) == 65535'u16
    check byte(id(300)) == 44'u8

  test "int8(x) raises RangeDefect out of range (was a recorded decline)":
    let r = symexFind(narrow8, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"
      check r.raisedWitness[0] < -128 or r.raisedWitness[0] > 127

  test "an in-range int8(x) is the value (high end)":
    let r = symexFind(narrow8Ok, tLabel("s8j_narrow8_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 127
      check reproduces(narrow8Ok(r.witness[0]), "s8j_narrow8_ok")

  test "an in-range int8(x) is the value (low end)":
    let r = symexFind(narrow8Neg, tLabel("s8j_narrow8_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == -128
      check reproduces(narrow8Neg(r.witness[0]), "s8j_narrow8_neg")

  test "int16(x) of an int32 raises RangeDefect":
    let r = symexFind(narrow16From32, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < -32768 or r.raisedWitness[0] > 32767

  test "int32(x) of an int raises RangeDefect":
    let r = symexFind(narrow32, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < int(low(int32)) or r.raisedWitness[0] > int(high(int32))

  test "except RangeDefect around a narrowing conversion is live":
    let r = symexFind(narrowCaught, tLabel("s8j_narrow_caught"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(narrowCaught(r.witness[0]), "s8j_narrow_caught")

  test "same-width unsigned -> signed checks: int(x) of a uint64":
    let r = symexFind(sameWidthU2S, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] >= 9223372036854775808'u64

  test "same-width unsigned -> signed checks: int32(x) of a uint32":
    let r = symexFind(sameWidthU32, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] > uint32(high(int32))

  test "int8(x) of a promoted range param raises above 127":
    let r = symexFind(narrowPromoted, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] > 127

suite "S8j (3b) a narrowing int conversion into an unsigned target truncates":
  test "uint8(x) of a promoted range param is its value modulo 256":
    let r = symexFind(truncPromoted, tLabel("s8j_trunc_promoted"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] in [744, 1000]
      check reproduces(truncPromoted(r.witness[0]), "s8j_trunc_promoted")

  test "uint8(x) truncates: x > 255 reaches uint8(x) == 44 (was a recorded decline)":
    let r = symexFind(truncU8, tLabel("s8j_trunc_u8"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(truncU8(r.witness[0]), "s8j_trunc_u8")

  test "uint8(x) never raises":
    let r = symexFind(truncU8NoRaise, tRaisedExn(""))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "uint16(-1) == 65535":
    let r = symexFind(truncU16Neg, tLabel("s8j_trunc_u16"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

  test "same-width signed -> unsigned never raises":
    let r = symexFind(sameWidthS2U, tRaisedExn(""))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

  test "byte(x) truncates and never raises":
    let r = symexFind(byteConv, tRaisedExn(""))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat

suite "S8j (3c) a char target range-checks 0 .. 255":
  test "char(x) raises RangeDefect out of 0 .. 255 (was a recorded decline)":
    let r = symexFind(charConv, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 0 or r.raisedWitness[0] > 255

  test "an in-range char(x) is the byte":
    let r = symexFind(charConvOk, tLabel("s8j_char_ok"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 65

  test "char(x) of an int8 raises for x < 0 (was an unchecked reinterpret)":
    let r = symexFind(charFromI8, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 0

# ---- (4) one range check on a plain assignment ------------------------------
#
# Probe: `q = x` with `q: range[0..10]` and x == 11 raises RangeDefect
# "value out of range: 11 notin 0 .. 10" once; with x == 5 it assigns.

proc assignRange(x: int) =
  var q: range[0..10] = 0
  q = x
  if q == 10: symexTarget("s8j_assign_range")

proc assignRangeExplicit(x: int) =
  var q: range[0..10] = 0
  q = range[0..10](x)
  discard q

proc assignRangeInc(x: range[0..10]) =
  var q: range[0..10] = x
  q += 1
  discard q

type S8jBox = ref object
  v: range[1..100]

proc fieldWrite(p: S8jBox; x: int) =
  if p != nil:
    p.v = x
    if p.v == 100: symexTarget("s8j_field_write")

proc seqWrite(s: var seq[range[1..100]]; x: int) =
  if s.len > 0:
    s[0] = x
    if s[0] == 100: symexTarget("s8j_seq_write")

proc rangeChecks(canon: string): int =
  ## Range checks in a canonical program: every range-carrying int
  ## conversion (`Ex<CIW:...:lo..hi:`) plus every range-typed assignment
  ## target (`;aty=` other than nil).
  var i = 0
  while true:
    let j = canon.find("Ex<CIW:", i)
    if j < 0: break
    # CIW:<sw>:<ss>:<tw>:<ts>:[<lo>..<hi>:]<operand>
    var k = j + "Ex<CIW:".len
    for _ in 0 ..< 4: k = canon.find(':', k) + 1
    let colon = canon.find(':', k)
    if colon > 0 and ".." in canon[k ..< colon]: inc result
    i = j + 1
  result += canon.count(";aty=") - canon.count(";aty=Ty<nil>")

suite "S8j (4) a plain assignment to a range variable checks once":
  test "oracle":
    expect RangeDefect: assignRange(11)
    symexCaptureBegin()
    assignRange(10)
    check "s8j_assign_range" in symexCaptureEnd()

  test "q = x carries one range check, not two":
    let canon = canonicalize(progOf(assignRange))
    checkpoint(canon)
    check rangeChecks(canon) == 1

  test "q = R(x) carries one range check, not two":
    let canon = canonicalize(progOf(assignRangeExplicit))
    checkpoint(canon)
    check rangeChecks(canon) == 1

  test "q += 1 keeps its assignment check":
    let canon = canonicalize(progOf(assignRangeInc))
    checkpoint(canon)
    check rangeChecks(canon) == 1

  test "the verdicts are unchanged":
    let r = symexFind(assignRange, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] < 0 or r.raisedWitness[0] > 10
    let s = symexFind(assignRange, tLabel("s8j_assign_range"))
    check s.status == sxSat
    if s.status == sxSat:
      check reproduces(assignRange(s.witness[0]), "s8j_assign_range")

# A field write and a seq element write carry the same hidden conversion;
# the walker's site check (`forkAssignRangeCheck`) skips a value that
# already carries it (`carriesRangeCheck`). Probe: `p.v = 0` and
# `s[0] = 101` each raise one RangeDefect.

suite "S8j (4b) a field or seq element write checks once, verdicts unchanged":
  test "oracle":
    expect RangeDefect: fieldWrite(S8jBox(v: 1), 0)
    var s = @[range[1..100](1)]
    expect RangeDefect: seqWrite(s, 101)

  test "a field write out of range raises RangeDefect":
    let r = symexFind(fieldWrite, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[1] < 1 or r.raisedWitness[1] > 100

  test "a field write in range stores the value":
    let r = symexFind(fieldWrite, tLabel("s8j_field_write"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 100

  test "a seq element write out of range raises RangeDefect":
    let r = symexFind(seqWrite, tRaisedExn("RangeDefect"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[1] < 1 or r.raisedWitness[1] > 100

  test "a seq element write in range stores the value":
    let r = symexFind(seqWrite, tLabel("s8j_seq_write"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

# ---- (5) walker version floor -------------------------------------------------

suite "S8j (5) walker version":
  test "walker version is at least 158":
    check parseInt(symexWalkerVersion) >= 158
