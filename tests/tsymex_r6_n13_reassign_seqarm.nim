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
##
## RFC-0005 S8f (walker 154) removed the premise: Nim never zero-initialises
## an arm on a discriminator assignment. It raises `FieldDefect` when the
## assignment changes the object's branch and keeps the fields when it does
## not (probed on the pinned toolchain), and `isVariantReassign` now models
## exactly that -- `defaultZero` is no longer called from it. The pins below
## that encoded the zero-init ("count != 0 after reassignment is
## unreachable") are restated to what Nim does, each with a run of the real
## code as its oracle; the no-crash and decline pins keep their purpose.
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

  test "N13-2b: count != 0 after a same-branch reassignment is reachable (S8f)":
    ## Nim keeps `count` from an input already on `rkB` (and raises on
    ## `rkA`), so the label IS reachable -- the old `sxUnsat` pinned the
    ## zero-init Nim does not do.
    let r = symexFind(sutCountNonzeroUnreachable, tLabel("count_nonzero_unreachable"))
    check r.status == sxSat
    var v = Rec(kind: rkB, count: 3)
    reassignToB(v)
    check v.count == 3
    var w = Rec(kind: rkA, a: 1)
    expect FieldDefect:
      reassignToB(w)

# --- (iii) a READ of the placeholder field after reassignment classifies
#     decline -- never a crash, never a wrong verdict. ---------------------

proc sutReadOptsAfterReassign(v: var Rec) =
  ## RFC-0005 S8f: guarded onto `rkB`, so the assignment cannot raise and
  ## the run's only question is the decline this suite pins (unguarded, an
  ## `rkA` input raises `FieldDefect` -- a real `sxRaised`).
  if v.kind == rkB:
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
#    `isBackedSeqElemTy`'s set) reassigned the same way: full verdicts, no
#    decline (S8f: the field is kept on a same-branch assignment).
# =============================================================================

type
  CKind = enum ckA, ckB
  Ctl = object
    case kind: CKind
    of ckA: a: int
    of ckB: bytes: seq[byte]        ## backed elem (itInt)

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

suite "symex N13 -- control: backed-elem seq field reassignment is fully modelled":

  test "N13-4a: bytes.len == 0 after reassignment is reachable (sxSat)":
    let r = symexFind(sutCtlLenZeroSat, tLabel("ctl_len_zero_sat"))
    check r.status == sxSat

  test "N13-4b: bytes.len != 0 after a same-branch reassignment is reachable (S8f)":
    let r = symexFind(sutCtlLenNonzeroUnreachable, tLabel("ctl_len_nonzero_unreachable"))
    check r.status == sxSat
    var v = Ctl(kind: ckB, bytes: @[1'u8])
    reassignCtlToB(v)
    check v.bytes.len == 1

# =============================================================================
# Version pin
# =============================================================================

suite "symex N13 -- walker version pin":

  test "walker version floor >= 98 (N13: test-only coverage closure, no verdict change)":
    check parseInt(symexWalkerVersion) >= 98
