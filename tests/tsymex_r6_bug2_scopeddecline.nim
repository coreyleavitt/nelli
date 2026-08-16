## Round-6 Bug #2 — per-field SCOPED DECLINE with read-taint.
##
## Escalated + design-resolved in `docs/RFC-chapulin-hardening.handoff.md`
## (the A6-ATTEMPTED "⛔" bullet + "FORK RESOLUTION" bullet). Root cause:
## `classifyObjectRecordFields` (`dsl_typebridge.nim`) was EAGER and
## WHOLE-TYPE — every declared variant arm's fields classified (and, via
## `allocateSym`, ALLOCATED) unconditionally, so a field like
## `options: seq[(string,string)]` on an UNTOUCHED arm poisoned `symexFind`
## for EVERY proc merely ALLOCATING the object type (a parameter, a
## call-return placeholder, a local), discarding any already-found
## `sxSat`/`sxUnsat` verdict for the WHOLE run — confirmed minimally: adding
## a third UNUSED arm carrying `seq[(string,string)]` alone flipped a clean
## `sxUnsat` to `sxUnknown`. Related: `itSeq[itTuple]` had NO backing at all
## in `allocateSym` (the B6 flag) — same `seq[(string,string)]` cluster,
## this slice covers both.
##
## Fix (the approved design, "FORK RESOLUTION" bullet): a field whose type
## is structurally unsupported for allocation backing (mirrors
## `allocateSeqDataRaw`'s backed element set via the new
## `isBackedSeqElemTy`) classifies to a KIND-MARKED placeholder
## (`isUnsupportedFieldPlaceholder`, `types.nim` — extends R8's
## `unsupportedFieldPlaceholder` precedent from "omitted constructor field"
## to "declared field type" scope). `allocateSym` allocates it as a FRESH
## OPAQUE value (never raises — the object as a whole allocates cleanly).
## READ sites (`dsl_parser.nim`'s `nnkDotExpr` field-access arms) detect the
## placeholder and deposit an SND-1 `isUnsupported` taint on THAT READ's own
## statement instead of building a real accessor — so only paths that
## actually READ the poisoned field degrade to a classified `sxUnknown`.
## `retBindEq`'s new `svUninterpRef` arm SKIPS the eq constraint on such a
## field (no-constraint = sound over-approximation; the read-taint owns
## honesty).
##
## Non-goals (recorded, unchanged by this slice): modeling
## `seq[(string,string)]` CONTENT stays out of scope; lazy per-arm
## classification was considered and rejected (strictly dominated by the
## scoped-decline design — see the handoff's FORK RESOLUTION bullet).
##
## Bumps `symexWalkerVersion` 84->85: verdict-surface change (previously
## `sxUnknown` verdicts for procs allocating — but not reading — a poisoned
## field now honestly TIGHTEN to their real `sxSat`/`sxUnsat`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs — three-arm shape mirroring chapulin's `TftpPacket`: one arm carries
# the unmodeled `seq[(string,string)]` field, the other two do not.
# ---------------------------------------------------------------------------

type
  PKind = enum pkRrq, pkData, pkAck
  Packet = object
    tag: int                            ## plain field, shared across arms
    case kind: PKind
    of pkRrq: options: seq[(string, string)]   ## the poisoned field
    of pkData: blockNum: int
    of pkAck: ackNum: int

# --- POISON-GONE (bare parameter — the most direct form of the bug: mere
# ALLOCATION of the type, via `allocateSym`, used to raise unconditionally
# because of pkRrq's `options` field, regardless of which arm's fields this
# proc actually touches). --------------------------------------------------
proc sutParamOtherArmHit(p: Packet) =
  if p.kind == pkData and p.blockNum == 7:
    symexTarget("param_other_arm_hit")

proc sutParamOtherArmUnsat(p: Packet) =
  ## Soundness companion: a genuine contradiction on the SAME (untouched-
  ## options-arm) fields must still resolve `sxUnsat`, not degrade.
  if p.kind == pkData and p.blockNum == 7 and p.blockNum == 8:
    symexTarget("param_other_arm_unsat")

# --- POISON-GONE (return-binding twin — a proc RETURNING the poisoned type,
# the RFC's own literal framing "poisons symexFind for EVERY proc returning
# that object type"). --------------------------------------------------
proc makeDataPacket(n: int): Packet =
  Packet(kind: pkData, blockNum: n, tag: 1)

proc sutReturnDataHit(n: int) =
  let p = makeDataPacket(n)
  if p.blockNum == 7:
    symexTarget("return_data_blocknum_7")

proc sutReturnDataUnsat(n: range[0 .. 1000]) =
  let p = makeDataPacket(n + 1)
  if p.blockNum == n:
    symexTarget("return_data_blocknum_unsat")

# --- HONEST DEGRADE — a READ of the placeholder field classifies to
# `sxUnknown` with the decline reason surfaced (assert the classification,
# not just the status). ------------------------------------------------
proc sutReadOptionsField(p: Packet) =
  if p.kind == pkRrq:
    let opts = p.options
    discard opts
    symexTarget("read_options_field")

# --- retBindEq path — call-return binding of an object carrying the
# placeholder on an INACTIVE arm skips the eq constraint there and still
# proves properties over the SUPPORTED fields (kind, blockNum, tag — the
# active arm plus the shared plain field). -------------------------------
proc sutRetBindSupportedFieldsHit(n: int) =
  let p = makeDataPacket(n)
  if p.kind == pkData and p.blockNum == 7 and p.tag == 1:
    symexTarget("retbind_supported_fields_hit")

proc sutRetBindSupportedFieldsUnsat(n: range[0 .. 1000]) =
  let p = makeDataPacket(n + 1)
  if p.kind == pkData and p.blockNum == n and p.tag == 1:
    symexTarget("retbind_supported_fields_unsat")

# --- Variant construction (A3 fork-per-tag) with a placeholder-carrying
# arm — untouched-tag queries unaffected. --------------------------------
type
  SymOp = enum symRrq, symData
  SymPkt = object
    tag: int                       ## the ONLY field kind Nim itself accepts
                                    ## alongside a non-constant discriminant
    case kind: SymOp
    of symRrq: options: seq[(string, string)]   ## the poisoned field
    of symData: blockNum: int

proc sutSymConstructUntouchedTag(b: byte, n: int) =
  let k = if b == 1'u8: symRrq else: symData
  let p = SymPkt(kind: k, tag: n)
  if p.kind == symData and p.tag == 42:
    symexTarget("sym_construct_data_tag42")

proc sutSymConstructTouchedArmDegrades(b: byte, n: int) =
  ## Companion: the fork that DOES select the poisoned arm still degrades
  ## classified (not a crash) the moment it actually READS `options` —
  ## the fork-per-tag machinery allocates every arm's fields fresh
  ## regardless of tag (A3), so this exercises `allocateSym`'s placeholder
  ## branch under path-forked construction specifically, not just
  ## `iekVariantLit`'s literal-pinned construction.
  let k = if b == 1'u8: symRrq else: symData
  let p = SymPkt(kind: k, tag: n)
  if p.kind == symRrq:
    let opts = p.options
    discard opts
    symexTarget("sym_construct_rrq_touch_degrades")

# --- Direct `var x: seq[(string,string)] = @[]` / local touch shape —
# degrades classified, no crash (verifies composition with the B6
# empty-literal rider; this is a LOCAL variable, not an object field, so it
# is untouched by this slice's classify-time change and exercises the
# PRE-EXISTING `allocateSeqDataRaw` degrade path). ------------------------
proc sutLocalEmptySeqNoCrash(n: int) =
  var pairs: seq[(string, string)] = @[]
  discard pairs
  if n == 5:
    symexTarget("local_empty_seq_no_crash")

proc sutLocalSeqTouchDegrades(n: int) =
  var pairs: seq[(string, string)] = @[]
  pairs.add(("a", "b"))
  if n == 5:
    symexTarget("local_seq_touch_degrades")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 Bug #2 — POISON-GONE (bare parameter)":

  test "Bug2-1a: proc taking a Packet param, touching only the pkData arm, proves sxSat (options never allocated-poisoned)":
    let r = symexFind(sutParamOtherArmHit, tLabel("param_other_arm_hit"))
    check r.status == sxSat
    check r.witness[0].kind == pkData
    check r.witness[0].blockNum == 7

  test "Bug2-1b: UNSAT companion — a genuine contradiction on the same untouched-options-arm fields still resolves sxUnsat":
    let r = symexFind(sutParamOtherArmUnsat, tLabel("param_other_arm_unsat"))
    check r.status == sxUnsat

suite "symex round-6 Bug #2 — POISON-GONE (return-binding twin)":

  test "Bug2-2a: proc RETURNING a Packet built on the pkData arm proves sxSat, witness n==7":
    let r = symexFind(sutReturnDataHit, tLabel("return_data_blocknum_7"))
    check r.status == sxSat
    check r.witness[0] == 7

  test "Bug2-2b: UNSAT companion — the callee's returned blockNum is always n+1, blockNum==n is impossible":
    let r = symexFind(sutReturnDataUnsat, tLabel("return_data_blocknum_unsat"))
    check r.status == sxUnsat

suite "symex round-6 Bug #2 — HONEST DEGRADE":

  test "Bug2-3: reading the placeholder field classifies to sxUnknown with the decline reason surfaced":
    let r = symexFind(sutReadOptionsField, tLabel("read_options_field"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        check "options" in e.msg
        sawKind = true
    check sawKind

suite "symex round-6 Bug #2 — retBindEq skips eq on the placeholder field":

  test "Bug2-4a: call-return binding proves a property over the SUPPORTED fields (kind, blockNum, tag) -> sxSat":
    let r = symexFind(sutRetBindSupportedFieldsHit, tLabel("retbind_supported_fields_hit"))
    check r.status == sxSat
    check r.witness[0] == 7

  test "Bug2-4b: UNSAT companion — soundness over the same supported fields":
    let r = symexFind(sutRetBindSupportedFieldsUnsat, tLabel("retbind_supported_fields_unsat"))
    check r.status == sxUnsat

suite "symex round-6 Bug #2 — variant construction (A3 fork-per-tag) with a placeholder-carrying arm":

  test "Bug2-5a: the untouched (symData) fork's query is unaffected -> sxSat, witness tag==42":
    let r = symexFind(sutSymConstructUntouchedTag, tLabel("sym_construct_data_tag42"))
    check r.status == sxSat
    check r.witness[1] == 42

  test "Bug2-5b: the touched (symRrq) fork's own options READ still degrades classified, not a crash":
    let r = symexFind(sutSymConstructTouchedArmDegrades, tLabel("sym_construct_rrq_touch_degrades"))
    check r.status == sxUnknown

suite "symex round-6 Bug #2 — local seq[(string,string)] composition (regression, not new capability)":

  test "Bug2-6a: an untouched local seq[(string,string)] (empty literal) still proves sxSat":
    let r = symexFind(sutLocalEmptySeqNoCrash, tLabel("local_empty_seq_no_crash"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "Bug2-6b: a MUTATED local seq[(string,string)] still degrades classified, never a crash":
    let r = symexFind(sutLocalSeqTouchDegrades, tLabel("local_seq_touch_degrades"))
    check r.status == sxUnknown

suite "symex round-6 Bug #2 — walker version pin":

  test "walker version floor >= 85 (scoped decline with read-taint)":
    check parseInt(symexWalkerVersion) >= 85
