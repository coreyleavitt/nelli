## Round-6 review N13 -- discriminator reassignment through the placeholder
## `itSeq` arm.
##
## Finding (round-6 review, adjudicated statically): does `defaultZero`'s
## `itSeq` placeholder arm (runtime.nim ~2761, hoisted to module scope by
## R2/walker-v90; originally Phase 14 cycle A5, ADR-0003 D5) actually serve
## the VARIANT DISCRIMINATOR-REASSIGNMENT path? Answer: YES -- `runtime.nim`'s
## `isVariantReassign` arm (~7084, `newFields.add defaultZero(tyOf(f),
## basePath)`) is the ONLY call site left after R2's hoist deleted the old
## nested copy that used to live inside `isVariantReassign`'s own scope. The
## itSeq arm's guard (`t.seqUnsupportedFieldReason.len > 0 or not
## isBackedSeqElemTy(t.seqElemTy)`) is type-driven and therefore reached
## correctly on this path even though `tyOf` (used to recover `t` from the
## already-allocated prior-arm SymVal) drops the original
## `seqUnsupportedFieldReason` STRING -- the second disjunct
## (`isBackedSeqElemTy`) catches an unbacked element type on its own,
## independent of that string surviving the round-trip.
##
## The gap this slice closes is COVERAGE, not behavior: no existing test
## pinned a static-tag reassignment into an arm carrying an unbacked-elem-type
## seq field. The only existing reassignment test
## (`tsymex_phase14_arm_field_zero_init.nim`) uses a tuple arm; R2's own pin
## (`tsymex_r6_r2_zerodefault_result.nim`, T5i) covers the itSeq placeholder
## arm only through the `isCall`/`retBindEq` return-binding path, not
## `isVariantReassign`.
##
## TEST-ONLY slice: no production code changes. `symexWalkerVersion` stays
## "98"; `renderAsChoicesVersion` stays "11" -- every pin below matched the
## engine's ACTUAL observed behavior on first run (confirmed while writing
## this file; see the per-suite notes).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# 1. Primary shape: reassignment into an arm with BOTH a backed scalar field
#    (`count`) and an unbacked-elem seq field (`opts`, elemTy == itTuple,
#    outside `isBackedSeqElemTy`'s {itBool, itFloat32, itFloat64, itString,
#    itRef, itPtr, itInt} set).
# =============================================================================

type
  RKind = enum rkA, rkB
  Rec = object
    case kind: RKind
    of rkA: a: int
    of rkB:
      count: int
      opts: seq[(string, string)]   ## unbacked elem (itTuple) -> placeholder

proc reassignToB(v: var Rec) =
  v.kind = rkB

# --- (i) the reassignment itself must not crash or poison the whole run ---

proc sutReassignNoCrash(v: var Rec) =
  reassignToB(v)
  symexTarget("reassign_no_crash")

suite "symex N13 -- reassignment into a placeholder-seq-carrying arm does not crash":

  test "N13-1: reassigning into the opts-carrying arm reaches the target (sxSat), no crash":
    let r = symexFind(sutReassignNoCrash, tLabel("reassign_no_crash"))
    check r.status == sxSat

# --- (ii) the arm's OTHER (backed) field remains fully modeled: exactly
#     zero, both directions pinned for soundness. -----------------------

proc sutCountZeroSat(v: var Rec) =
  reassignToB(v)
  if v.count == 0:
    symexTarget("count_zero_sat")

proc sutCountNonzeroUnreachable(v: var Rec) =
  reassignToB(v)
  if v.count != 0:
    symexTarget("count_nonzero_unreachable")

suite "symex N13 -- sibling backed field (count) unaffected by the placeholder sibling":

  test "N13-2a: count == 0 after reassignment is reachable (sxSat)":
    let r = symexFind(sutCountZeroSat, tLabel("count_zero_sat"))
    check r.status == sxSat

  test "N13-2b: soundness -- count != 0 after reassignment is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutCountNonzeroUnreachable, tLabel("count_nonzero_unreachable"))
    check r.status == sxUnsat

# --- (iii) a READ of the placeholder field after reassignment classifies
#     decline -- never a crash, never a wrong verdict. ---------------------

proc sutReadOptsAfterReassign(v: var Rec) =
  reassignToB(v)
  let o = v.opts
  discard o
  symexTarget("read_opts_after_reassign")

suite "symex N13 -- reading the reassigned-in placeholder field classifies decline":

  test "N13-3: reading opts after reassignment classifies sxUnknown via seNestedSeqUnsupported, not a crash":
    let r = symexFind(sutReadOptsAfterReassign, tLabel("read_opts_after_reassign"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        check "opts" in e.msg
        sawKind = true
    check sawKind

# =============================================================================
# 2. Control: a BACKED-elem seq field (seq[byte], itInt elem -- inside
#    `isBackedSeqElemTy`'s set) reassigned the same way gets normal
#    zero-init semantics (length provably 0), full verdicts -- no decline.
# =============================================================================

type
  CKind = enum ckA, ckB
  Ctl = object
    case kind: CKind
    of ckA: a: int
    of ckB: bytes: seq[byte]        ## backed elem (itInt) -> real zero-init

proc reassignCtlToB(v: var Ctl) =
  v.kind = ckB

proc sutCtlLenZeroSat(v: var Ctl) =
  reassignCtlToB(v)
  if v.bytes.len == 0:
    symexTarget("ctl_len_zero_sat")

proc sutCtlLenNonzeroUnreachable(v: var Ctl) =
  reassignCtlToB(v)
  if v.bytes.len != 0:
    symexTarget("ctl_len_nonzero_unreachable")

suite "symex N13 -- control: backed-elem seq field reassignment gets real zero-init":

  test "N13-4a: bytes.len == 0 after reassignment is reachable (sxSat)":
    let r = symexFind(sutCtlLenZeroSat, tLabel("ctl_len_zero_sat"))
    check r.status == sxSat

  test "N13-4b: soundness -- bytes.len != 0 after reassignment is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutCtlLenNonzeroUnreachable, tLabel("ctl_len_nonzero_unreachable"))
    check r.status == sxUnsat

# =============================================================================
# Version pin
# =============================================================================

suite "symex N13 -- walker version pin":

  test "walker version floor >= 98 (N13: test-only coverage closure, no verdict change)":
    check parseInt(symexWalkerVersion) >= 98
