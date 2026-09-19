## Issue #163 item 1 (rev) -- `symexFind` failed to COMPILE for a proc taking
## an object with a plain enum field.
##
## Root cause (`docs/issue-0163-opaque-call-taint.handoff.md:~525-533`):
## witness reconstruction (`symex.emitTyAndReader`, `symex.nim`) emits a
## reader per FIELD TYPE. An enum field's `IRType` is a lifted `itInt` (see
## `dsl_typebridge.classifyType`'s enum arm), so the reader emitted was
## `readUInt8`/`readUInt16` -- a raw unsigned value. The generated witness
## constructor builds the object via a REAL `nnkObjConstr`, which Nim checks
## strictly against the object's DECLARED field types; a raw `uint8`/`uint16`
## does not implicitly convert to an enum-typed field, so the whole macro
## expansion failed to COMPILE. Not a degrade to `sxUnknown` -- strictly
## worse: `symexFind` could not even be CALLED on such a proc.
##
## Array/seq/top-level-param positions never hit this (R21a/R21b,
## `tsymex_163rev_enum_positions.nim`): `emitTyAndReader`'s returned type node
## for those positions only has to be a SELF-CONSISTENT Nim type (e.g.
## `array[2, uint8]`), and callers explicitly cast back
## (`Ordering(r.witness[0][0])`) -- Nim's own `EnumType(ordinalValue)`
## conversion accepts any ordinal-compatible value. `symexFind` never actually
## CALLS the SUT with the reconstructed tuple either (`SymexResult[tupleTy]`
## is a pure data carrier), so nothing there ever needed the tuple's element
## type to match the SUT's real declared type. An OBJECT FIELD is the one
## position where Nim itself enforces an exact-type (or genuinely
## enum-convertible) match at the constructor site.
##
## THE FIX: `IRType` gained `enumName` (analogous to `itTuple.nominalId` --
## nominal identity carried for witness-rendering, not a structural/verdict
## property; excluded from `IRType.==` the same way, but rendered by
## `canonicalize` by default, mirroring `itTuple.objectName`). Populated by
## `dsl_typebridge.classifyType`'s enum arm; round-tripped through
## `dsl_parser.emitIRType`'s `itInt` arm (`withEnumName`) the same way
## `hasRange`/`rangeLo`/`rangeHi` already are; consumed by
## `symex.emitTyAndReader`'s `itInt` arm to wrap the raw reader in
## `EnumName(...)` -- Nim's own ordinal-to-enum conversion, sound regardless
## of signedness or a negative/sparse domain (R2/R18 already put the correct
## width/signed/range on the underlying `itInt` before this ever runs).
##
## This test is WITNESS REPLAY, not merely "the call compiles": every SAT
## test reads the returned witness's enum field back and checks it against
## the expected enum VALUE, per the House Rule (an oracle computed by real
## Nim execution alongside every symbolic expectation).
##
## Also covers the object-field position for the enum DOMAIN R21 could not
## reach (`tsymex_163rev_enum_positions.nim`'s own docstring: "OUT OF SCOPE:
## enum as a plain OBJECT FIELD cannot reach `symexFind` at all... Not
## attempted here") -- a negative-ordinal enum and a sparse (large explicit
## ordinal) enum, both as object fields, now that item 1 unblocks the
## position entirely.

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

# =============================================================================
# Half 1 -- the flagship: a plain (dense, zero-based) enum object field.
# =============================================================================

type
  Color = enum
    cRed, cGreen, cBlue

  Box = object
    tag: Color
    n: int

proc reachGreen(b: Box) =
  if b.tag == cGreen and b.n == 7:
    symexTarget("hit")

proc excludesOutOfDomain(b: Box) =
  ## No real `Color` ordinal is outside [0, 2] -- if the field were left
  ## unconstrained (the pre-fix worry, now moot since the fix never even
  ## COMPILED, but a genuine regression guard once it does), this would be
  ## falsely satisfiable.
  if ord(b.tag) < 0 or ord(b.tag) > 2:
    symexTarget("oob")

suite "#163 item 1 -- symexFind COMPILES for an object with a plain enum field":

  test "oracle -- Box(tag: cGreen, n: 7) is a real, constructible value":
    let b = Box(tag: cGreen, n: 7)
    check b.tag == cGreen
    check b.n == 7
    for c in Color:
      check ord(c) >= 0 and ord(c) <= 2

  test "the call compiles and finds the target: sxSat":
    let r = symexFind(reachGreen, tLabel("hit"))
    check r.status == sxSat

  test "WITNESS REPLAY: the returned witness's enum field genuinely equals cGreen":
    let r = symexFind(reachGreen, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].tag == cGreen
    check r.witness[0].n == 7
    # Re-run the real Nim computation against the replayed witness -- the
    # House Rule oracle, applied to the WITNESS itself, not just the type.
    var hit = false
    if r.witness[0].tag == cGreen and r.witness[0].n == 7:
      hit = true
    check hit

  test "an out-of-domain field ordinal stays excluded: sxUnsat":
    check symexFind(excludesOutOfDomain, tLabel("oob")).status == sxUnsat

# =============================================================================
# Half 2 -- the enum DOMAIN positions R21 documented as unreachable at the
# object-field position: negative ordinals and a sparse (large explicit
# ordinal) domain.
# =============================================================================

type
  Ordering = enum
    roLess = -1
    roEqual = 0
    roGreater = 1

  OrderBox = object
    cmp: Ordering
    payload: int

  BigOrd = enum
    boA
    boB
    boC = 300

  BigBox = object
    kind: BigOrd
    payload: int

proc reachNegOrdinalField(b: OrderBox) =
  if b.cmp == roLess and b.payload == 42:
    symexTarget("neg-hit")

proc excludesOutOfDomainOrdering(b: OrderBox) =
  if ord(b.cmp) < -1 or ord(b.cmp) > 1:
    symexTarget("oob")

proc reachHoleAbove44Field(b: BigBox) =
  ## 100 is not a declared `BigOrd` member (a documented sparse-domain
  ## imprecision, `tsymex_163rev_enum_domain.nim`) but must stay reachable:
  ## it is inside [0, 300].
  if ord(b.kind) == 100 and b.payload == 1:
    symexTarget("hole100")

proc reachDeclaredBigField(b: BigBox) =
  if b.kind == boC and b.payload == 9:
    symexTarget("is-boc")

proc excludesGenuineOOBField(b: BigBox) =
  if ord(b.kind) > 300:
    symexTarget("oob")

suite "#163 item 1 -- object-field enum DOMAIN: negative ordinals":

  test "oracle -- roLess really is ordinal -1, in a real OrderBox":
    check ord(roLess) == -1
    let ob = OrderBox(cmp: roLess, payload: 42)
    check ob.cmp == roLess and ob.payload == 42

  test "the negative-ordinal field is reachable, with a genuine matching witness":
    let r = symexFind(reachNegOrdinalField, tLabel("neg-hit"))
    check r.status == sxSat
    check r.witness[0].cmp == roLess
    check r.witness[0].payload == 42

  test "an out-of-domain field ordinal stays excluded (would be unsound if unconstrained)":
    check symexFind(excludesOutOfDomainOrdering, tLabel("oob")).status == sxUnsat

suite "#163 item 1 -- object-field enum DOMAIN: sparse, large explicit ordinal":

  test "oracle -- boC really is ordinal 300, in a real BigBox":
    check ord(boC) == 300
    let bb = BigBox(kind: boC, payload: 9)
    check bb.kind == boC and bb.payload == 9

  test "a legal value beyond a truncated 8-bit bound is still reachable, with witness replay":
    let r = symexFind(reachHoleAbove44Field, tLabel("hole100"))
    check r.status == sxSat
    check ord(r.witness[0].kind) == 100
    check r.witness[0].payload == 1

  test "the declared large ordinal itself is reachable, with witness replay":
    let r = symexFind(reachDeclaredBigField, tLabel("is-boc"))
    check r.status == sxSat
    check r.witness[0].kind == boC
    check r.witness[0].payload == 9

  test "a genuinely out-of-domain ordinal is still excluded":
    check symexFind(excludesGenuineOOBField, tLabel("oob")).status == sxUnsat


suite "#163 item 1 -- walker version pin":

  test "walker version floor >= 138 (the round this fix lands in)":
    check parseInt(symexWalkerVersion) >= 138
