## Round-6 A4 -- `isVariantReassign`/`isVariantReassignSymbolic` interaction
## with the new construction paths (A1's `iekVariantLit`, A3's
## `isVariantConstructSym`), plus witness read-back of constructed
## NON-PARAM variants.
##
## ADR-0029 (`docs/SYMEX_PLAN.md`). A1 (walker v75) and A3 (walker v77)
## landed the two construction paths; both build an ordinary `svVariant`
## into the env under a local name, indistinguishable from a param- or
## reassign-origin `svVariant` to any statement that reads it afterward.
## A4 has no `Ver` (no `symexWalkerVersion`/`renderAsChoicesVersion`
## bump) because the pre-existing `isVariantReassign`/
## `isVariantReassignSymbolic` walker arms and the witness-extraction
## pipeline (`extractFromSymVal`'s `svVariant` case, `emitTyAndReader`'s
## `itVariant` case) already operate purely on the `svVariant` SHAPE, not
## on how it was produced -- so this file is INTERACTION PINS, not new
## machinery.
##
## Witness scope note: `extractWitness` (`runtime.nim`) walks
## `prog.params` only -- a locally-constructed (non-param) variant has no
## witness leaf under its own name. This is by design (the witness is
## "the SUT inputs that trigger the finding", not a program-state dump)
## and pre-dates this slice; A4's witness pins therefore assert that the
## INPUT PARAMS driving a constructed variant's discriminant and
## active-arm field are rendered faithfully in `res.witness`, which is
## the only read-back surface that exists -- matching the RFC's own hedge
## ("plain value-variant locals may already flow or may be absent") and
## its `Ver: --` (no format change needed or made).
##
## Bumps `symexWalkerVersion`: NONE. No new `iek*`/`is*` IR kind, no new
## classified-decline site, no cache-key change.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types

# ---------------------------------------------------------------------------
# SUTs -- two-tag shape shared by the A1-construct + reassign pins (mirrors
# A3's `TwoTagPkt` convention: a plain shared field alongside the case arms).
# ---------------------------------------------------------------------------

type
  IOp = enum ioA, ioB
  IPkt = object
    tag: int                       ## plain field, shared across arms
    case opcode: IOp
    of ioA: fa: int
    of ioB: fb: int

# --- Test 1: A1 literal-disc construction, then a LITERAL-tag reassign
# (`isVariantReassign` -- static, unconditional, no fork). The post-
# reassign arm's field is zero-init'd (`isVariantReassign`'s `defaultZero`
# policy applies uniformly regardless of how the object reached its
# pre-reassign state); the stale pre-reassign arm is provably unreachable
# afterward -- the reassign is unconditional, not a fork, so there is no
# path where the old tag survives. ---------------------------------------
proc sutConstructLitThenReassignLit(n: int) =
  var p = IPkt(opcode: ioA, tag: n, fa: 111)
  p.opcode = ioB
  if p.opcode == ioB and p.fb == 0:
    symexTarget("lit_reassign_zero_init")

proc sutConstructLitThenReassignLitStaleUnsat(n: int) =
  var p = IPkt(opcode: ioA, tag: n, fa: 111)
  p.opcode = ioB
  if p.opcode == ioA:
    symexTarget("lit_reassign_stale_unreachable")

# --- Test 2: A1 literal-disc construction, then a SYMBOLIC reassign
# (`isVariantReassignSymbolic` -- fork-per-tag). Both post-reassign tags
# are independently reachable; the plain `tag` field (shared, preserved
# across both the construction and the reassign) still equals the
# original constructor argument on every fork. ----------------------------
proc sutConstructLitThenReassignSymA(b: byte, n: int) =
  var p = IPkt(opcode: ioA, tag: n, fa: 111)
  let newOp = if b == 1'u8: ioA else: ioB
  p.opcode = newOp
  if p.opcode == ioA and p.tag == n:
    symexTarget("sym_reassign_hit_ioA")

proc sutConstructLitThenReassignSymB(b: byte, n: int) =
  var p = IPkt(opcode: ioA, tag: n, fa: 111)
  let newOp = if b == 1'u8: ioA else: ioB
  p.opcode = newOp
  if p.opcode == ioB and p.tag == n:
    symexTarget("sym_reassign_hit_ioB")

# ---------------------------------------------------------------------------
# SUTs -- wide (10-tag) shape for the A3-construct-then-reassign
# composition pin (mirrors A3's `WideObj`).
# ---------------------------------------------------------------------------

type
  CTag = enum ct0, ct1, ct2, ct3, ct4, ct5, ct6, ct7, ct8, ct9
  CObj = object
    tag: int
    case kind: CTag
    of ct0: f0: int
    of ct1: f1: int
    of ct2: f2: int
    of ct3: f3: int
    of ct4: f4: int
    of ct5: f5: int
    of ct6: f6: int
    of ct7: f7: int
    of ct8: f8: int
    of ct9: f9: int

# --- Test 3: A3 symbolic-disc construction, parse-time NARROWED to a
# 2-tag branch (`{ct0, ct1}`, well under `maxVariantConstructorForks`'s
# default budget of 8), then a SYMBOLIC reassign whose target tag
# (`ct5`) is OUTSIDE the construction's narrowed set. `isVariantReassign-
# Symbolic` forks over the CONSTRUCTED value's full declared arm table
# (`isVariantConstructSym` populates every declared arm's fields in every
# fork, regardless of narrowing -- see its walker doc comment), not the
# construction's narrowed tag subset -- composing without unsoundness
# (real Nim allows reassigning to any of the type's declared tags,
# irrespective of what a prior CONSTRUCTION happened to be narrowed to)
# and without the construct's OWN budget check (structural, against
# `stmt.vcsTagSet.len` only) being affected by what a later statement
# forks over. ---------------------------------------------------------------
proc sutComposeNarrowedConstructThenWideReassign(b1, b2: byte, n: int) =
  let op1 = if b1 == 1'u8: ct0 else: ct1
  case op1
  of ct0, ct1:
    var p = CObj(kind: op1, tag: n)
    let op2 = if b2 == 1'u8: ct5 else: ct0
    p.kind = op2
    if p.kind == ct5 and p.tag == 99:
      symexTarget("compose_reassign_to_ct5")
  else:
    discard

proc sutComposeNarrowedConstructThenWideReassignUnsat(b1, b2: byte, n: int) =
  let op1 = if b1 == 1'u8: ct0 else: ct1
  case op1
  of ct0, ct1:
    var p = CObj(kind: op1, tag: n)
    let op2 = if b2 == 1'u8: ct5 else: ct0
    p.kind = op2
    if p.kind == ct5 and b2 != 1'u8:
      symexTarget("compose_reassign_unsat")
  else:
    discard

# ---------------------------------------------------------------------------
# Witness read-back -- non-param constructed variants (Ver: -- ; the
# existing param-witness pipeline already covers this, see the file doc
# comment).
# ---------------------------------------------------------------------------

# --- Test 4: A1 literal-disc construction -- the failure witness pins the
# input param driving the constructed (non-param) variant's ACTIVE-ARM
# field faithfully. ---------------------------------------------------------
proc sutWitnessConstructLitField(n: int) =
  let p = IPkt(opcode: ioA, tag: n, fa: n + 1)
  if p.opcode == ioA and p.fa == 43 and p.tag == 42:
    symexTarget("witness_construct_lit_field")

# --- Test 5: A3 symbolic-disc construction -- the failure witness shows
# which tag the solver chose, via the input byte that drove it (the disc
# itself has no witness leaf of its own -- `p` is a local, not a param --
# but the witness of the driving param faithfully identifies the chosen
# fork). ---------------------------------------------------------------------
proc sutWitnessConstructSymDisc(b: byte, n: int) =
  let op = if b == 1'u8: ioA else: ioB
  let p = IPkt(opcode: op, tag: n)
  if p.opcode == ioB and p.tag == 77:
    symexTarget("witness_construct_sym_disc")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 A4 -- A1 construction then literal-tag reassign":

  test "A4-1a: post-reassign arm's field is zero-init'd (isVariantReassign's defaultZero policy applies after A1 construction)":
    let res = symexFind(sutConstructLitThenReassignLit, tLabel("lit_reassign_zero_init"))
    check res.status == sxSat

  test "A4-1b: the stale PRE-reassign arm is provably unreachable afterward (unconditional reassign, no fork)":
    let res = symexFind(sutConstructLitThenReassignLitStaleUnsat, tLabel("lit_reassign_stale_unreachable"))
    check res.status == sxUnsat

suite "symex round-6 A4 -- A1 construction then symbolic reassign (isVariantReassignSymbolic interaction)":

  test "A4-2a: post-reassign ioA fork is reachable; plain `tag` field preserved through both construct and reassign":
    let res = symexFind(sutConstructLitThenReassignSymA, tLabel("sym_reassign_hit_ioA"))
    check res.status == sxSat
    check res.witness[0] == 1'u8

  test "A4-2b: the OTHER post-reassign fork (ioB) is independently reachable too":
    let res = symexFind(sutConstructLitThenReassignSymB, tLabel("sym_reassign_hit_ioB"))
    check res.status == sxSat
    check res.witness[0] != 1'u8

suite "symex round-6 A4 -- A3 construction then reassign: forks compose without unsoundness":

  test "A4-3a: a narrowed (2-tag) A3 construction, reassigned to a tag OUTSIDE the narrowed set, still reaches it -- reassign forks over the full declared arm set, not the construction's narrowed subset":
    let res = symexFind(sutComposeNarrowedConstructThenWideReassign, tLabel("compose_reassign_to_ct5"))
    check res.status == sxSat
    check res.witness[1] == 1'u8

  test "A4-3b: soundness companion -- reaching ct5 forces b2==1'u8, so ct5 with b2!=1'u8 in the same conjunction is impossible":
    let res = symexFind(sutComposeNarrowedConstructThenWideReassignUnsat, tLabel("compose_reassign_unsat"))
    check res.status == sxUnsat

suite "symex round-6 A4 -- witness read-back of constructed non-param variants":

  test "A4-4: A1 literal-disc construction -- witness pins the input driving the constructed variant's active-arm field":
    let res = symexFind(sutWitnessConstructLitField, tLabel("witness_construct_lit_field"))
    check res.status == sxSat
    check res.witness[0] == 42

  test "A4-5: A3 symbolic-disc construction -- witness shows which tag the solver chose, via the driving input":
    let res = symexFind(sutWitnessConstructSymDisc, tLabel("witness_construct_sym_disc"))
    check res.status == sxSat
    check res.witness[0] != 1'u8
    check res.witness[1] == 77

suite "symex round-6 A4 -- walker version floor":

  test "walker version floor >= 77 (depends on A1's iekVariantLit and A3's isVariantConstructSym semantics)":
    check parseInt(symexWalkerVersion) >= 77
