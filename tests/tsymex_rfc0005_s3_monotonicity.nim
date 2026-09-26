## RFC-0005 (soundness channels) slice S3 -- the taint-monotonicity harness
## (§4.1): a test-support macro (`withPoisonedArm`) plus a curated SUT
## battery, run through `symexFind` -- the real public entry point.
##
## §4.1 restates the draft's property in two families the current design can
## actually carry:
##
##   Family 1 (witness monotonicity). Grafting a DISJOINT tainted arm onto a
##   SUT with a clean witness must not change an `sxSat`/`sxRaised` verdict.
##   This is the honest form of the draft's property (it encodes path
##   SCOPING) and it is also the pin that catches the `shouldStop` regression
##   of §2.3 when the tainted arm is discovered BEFORE the clean witness
##   (`withPoisonedArm(paBefore, ...)` below) -- a candidate that wrongly
##   entered `w.found` would halt the walk before the later clean witness was
##   ever solved, and the verdict would wrongly become `sxUnknown`.
##
##   The OTHER ordering (`paAfter`, poison textually follows the witness) is
##   NOT a symmetric mirror of `paBefore` -- this slice's own RED found that
##   out empirically. `shouldStop` (`runtime.nim:8445`) halts the ENTIRE walk
##   the instant a clean answer lands in `w.found`, so when the witness is
##   satisfiable and discovered first (the natural case when the poison
##   follows it), the walker never even VISITS the poison arm -- the taint
##   provably never fires. Every `paAfter` test below therefore asserts the
##   verdict is unchanged (trivially -- nothing ran) AND that the poison's
##   kind is ABSENT from `r.errors`, with a comment naming `shouldStop` as
##   the reason. This is itself a useful, load-bearing confirmation: it is
##   the empirical proof that `shouldStop`'s eager-halt optimization cannot
##   lose a verdict to code sequenced after an already-discovered witness.
##
##   Family 2 (classification pins), the half buildable today:
##     2a. A SUT whose ONLY witness lies ON a tainted path (the degrade sits
##         between every path and the target, not on a disjoint branch) must
##         NOT report `sxSat` via `symexFind` -- today (§2.3 rule 4): the
##         candidate pool holds the candidate, but the verdict stays
##         `sxUnknown` until S10's replay confirms it.
##     2b. An over-taint-only run that proves the target UNREACHABLE must
##         report `sxUnsat` -- but that flip needs S4/S5/S6 to reclassify a
##         funnel out of the conservative `dcNoAnswer` default first. These
##         pins characterize the CURRENT verdict, each naming the slice
##         expected to flip it (mirrors `tsymex_rfc0005_s0_exhibit.nim`'s
##         pin style); F1 flipped at S4 and is asserted via
##         `checkUnsatOverTaintOnly`.
##
## The battery deliberately routes through four LIVE, DISTINCT degrade
## funnels (S0b's own measurement categories) so S4/S5/S6/S7's later work
## each has pre-existing coverage in this file to extend, not invent:
##   F1 -- `allocDegrade`/`heUnresolvedRef`  (heap ref-to-string field deref;
##         the exact S0-pin-1 shape) -- classified at **S4**: the site split
##         off as `heUnsupportedPointeeRead` (`dcFreshSymbol`); F1 now fires
##         that kind, not `heUnresolvedRef`
##   F2 -- `degradeStrArm`/`seUnsupportedStringOp` (`toOct`, no Z3 oct
##         primitive; the `tsymex_a8_radix` precedent) -- AUDITED at **S5**
##         and NOT reclassified: `toOct`'s own decline is a fresh symbol, but
##         the kind's other sites drop behaviour (`requireStr` failures ahead
##         of an `IndexDefect`/`ValueError` fork, a catch-all carrying
##         raising ops like `parseFloat`, a shared-name substr bound decline,
##         the `strip` parse site's forced `""`), so it stays `dcNoAnswer`
##         and F2 does NOT flip. No RFC-0005 slice schedules a flip: it would
##         need a §3.2 split of the total-op declines (radix/case-fold) out
##         of `seUnsupportedStringOp` first, which §5 does not plan.
##   F3 -- `mkUnsupported` statement / `feUnsupportedStmtKind` (a field
##         augmented-assignment through a value copy; the S1c
##         `s1cTaintedCaught` precedent) -- a generic Class-A/B catch-all
##         kind. RFC-0005 §5 does not name a slice that reclassifies THIS
##         kind out of `dcNoAnswer` (S8 unifies Class-A/B's REPRESENTATION
##         but explicitly makes "no verdict change" its own DoD item), so
##         this funnel gets NO family-2b pin -- there is nothing to name.
##   F4 -- heap-arm degrade / `heRefVariantUnsupported` (an inline `ref` to a
##         variant-fielded object; the `tsymex_phase15_r6_refobj` precedent)
##         -- routes `heapArmDegrade` -> `allocDegrade`, so S4 AUDITED it (not
##         S6, as this comment said at S3): both its sites SUBSTITUTE (the
##         read skips `nilDerefFork`, dropping the NilAccessDefect raise; the
##         write is dropped), so it stays `dcNoAnswer` and does NOT flip. Any
##         later flip needs a slice that restructures those sites first.
##
## No product code. At S3 all four kinds classified `dcNoAnswer` (verified by
## `types.nim`'s `classOf` table); S4 reclassified F1's kind only (F1's
## family-2b pin flips; its family-1 pins are unaffected because the clean
## witness wins by rule 1 regardless of taint). Walker version floor: 141
## (S1c) at S3; S4 bumped the walker to 142 (pinned in
## `tsymex_rfc0005_s4_alloc.nim`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# =============================================================================
# The test-support macro (§4.1's "buildable form"): `withPoisonedArm`
# =============================================================================

type
  PoisonPlacement* = enum
    paBefore  ## The poisoned arm's `if` precedes the witness code -- the
              ## walker (which visits statements top-to-bottom) discovers
              ## and solves the tainted arm FIRST. This is the §2.3
              ## `shouldStop`-regression pin: the tainted SAT must land in
              ## `w.candidates` (never halting the walk), so the clean
              ## witness discovered afterward still wins.
    paAfter   ## The poisoned arm's `if` follows the witness code -- the
              ## walker discovers the clean witness first (the case the
              ## draft's original property implicitly assumed). When the
              ## witness IS satisfiable, `shouldStop` (`runtime.nim:8445`)
              ## halts the whole walk right there, so the poison arm is
              ## never even visited -- see the file header for why that is
              ## itself the pin's point, not a design flaw.

template withPoisonedArm*(placement: static PoisonPlacement; poisonOn: bool;
                          poisonBody, witnessBody: untyped) =
  ## RFC-0005 S3 (§4.1). Grafts a DISJOINT poisoned arm onto a SUT:
  ## `poisonBody` runs under `if poisonOn:` -- `poisonOn` is a fresh
  ## parameter the witness logic never reads, so the two arms never share a
  ## guard. `runtime.nim:9472-9474` forks BOTH arms of an `if` with no
  ## feasibility check, so the grafted arm IS walked and DOES taint,
  ## regardless of whether `poisonOn` could ever be true in a real caller.
  ## `placement` controls SOURCE order, which is DISCOVERY order for the
  ## walker -- see `PoisonPlacement`'s two members above for what each
  ## ordering pins.
  when placement == paBefore:
    if poisonOn:
      poisonBody
    witnessBody
  else:
    witnessBody
    if poisonOn:
      poisonBody

# =============================================================================
# Poison sources -- one degrade site per funnel, reused across the battery
# =============================================================================

# ---- F1: allocDegrade / heUnsupportedPointeeRead (heUnresolvedRef pre-S4) --
# Identical shape to `tsymex_rfc0005_s0_exhibit.nim`'s `s0DeadFreshSymbol`:
# `liftHeapValue`'s unsupported-pointee `else` arm does not yet model a
# `string` field read through a heap-deref'd `ref` (Cluster R1 covers only
# PRIMITIVE pointees). Guarded `p != nil` so the poison body itself never
# nil-derefs.
type S3F1Node = ref object
  s: string

# ---- F2: degradeStrArm / seUnsupportedStringOp (toOct, no Z3 oct prim) -----
# Identical trigger to `tsymex_a8_radix.nim`'s `octDegrade`: unconditional,
# no guard needed -- `toOct` is simply not modeled.

# ---- F3: mkUnsupported statement / feUnsupportedStmtKind -------------------
# Identical shape to `tsymex_rfc0005_s1c_verdict.nim`'s `s1cTaintedCaught`:
# a field AUGMENTED assignment (`+=`) through a local value copy is a
# Class-B `isUnsupported` statement the parser has no arm for.
type S3F3Point = object
  x, y: int

# ---- F4: heap-arm degrade / heRefVariantUnsupported ------------------------
# Identical shape to `tsymex_r6_heap_raise_totality.nim`'s
# `heapMultiVariantFieldRead` (`HeapMultiVariantObj`): a MULTI-axis variant
# (two independent `case` discriminators), referenced via an INLINE `ref`
# at each parameter -- NOT a named ref-alias type. Two things verified by
# this slice's own probe, both confirming stale assumptions:
##   - A SINGLE-axis variant's field access through a ref is fully modelled
##     since ADR-0013 Slice 1 (`tsymex_phase15_r6_refobj.nim`'s `variantRef`
##     reports `sxSat` for a discriminator read today) -- a multi-axis
##     variant is required to still hit the decline.
##   - A NAMED `type X = ref Object` alias "unwraps to a plain in-memory
##     variant" (`tsymex_phase15_r6_refobj.nim`'s own DoD-5 comment) and
##     bypasses the heap-arm decline entirely (observed: `feUnsupportedExprKind`
##     / `weInternalWalkerFault`, never `heRefVariantUnsupported`) -- the
##     INLINE `ref S3F4Obj` spelling at the parameter is load-bearing.
type
  S3F4KindA = enum s3f4KindA1, s3f4KindA2
  S3F4KindB = enum s3f4KindB1, s3f4KindB2
  S3F4Obj = object
    case kindA: S3F4KindA
    of s3f4KindA1: a1: int
    of s3f4KindA2: a2: int
    case kindB: S3F4KindB
    of s3f4KindB1: b1: int
    of s3f4KindB2: b2: int

# =============================================================================
# Family 1 -- witness monotonicity battery (§4.1 family 1)
# =============================================================================
# Each witness family: an unpoisoned BASELINE (asserts the plain verdict),
# then the SAME witness with a poisoned arm grafted from >=2 distinct
# funnels, in BOTH placements -- 4 grafted variants per witness family.
# Every grafted test asserts (a) the verdict equals the baseline verdict
# (the monotonicity claim itself) and (b) the poisoned arm's kind actually
# appears in `r.errors` (a graft that never taints proves nothing).

# ---- W1: sxSat, plain (funnels F1, F2) --------------------------------------

proc s3w1Base(x: int) =
  if x == 42:
    symexTarget("s3_w1_base")

proc s3w1F1Before(p: S3F1Node, x: int, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    if p != nil: discard p.s
  do:
    if x == 42:
      symexTarget("s3_w1_f1_before")

proc s3w1F1After(p: S3F1Node, x: int, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    if p != nil: discard p.s
  do:
    if x == 42:
      symexTarget("s3_w1_f1_after")

proc s3w1F2Before(x: int, y: int64, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    discard toOct(y, 3)
  do:
    if x == 42:
      symexTarget("s3_w1_f2_before")

proc s3w1F2After(x: int, y: int64, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    discard toOct(y, 3)
  do:
    if x == 42:
      symexTarget("s3_w1_f2_after")

suite "RFC-0005 S3 -- W1 (sxSat, plain), witness monotonicity":

  test "baseline: x == 42 -> sxSat":
    let r = symexFind(s3w1Base, tLabel("s3_w1_base"))
    check r.status == sxSat

  test "F1 before (shouldStop pin): graft does not change sxSat; heUnsupportedPointeeRead fired":
    let base = symexFind(s3w1Base, tLabel("s3_w1_base"))
    let r = symexFind(s3w1F1Before, tLabel("s3_w1_f1_before"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check r.errors.hasKind(heUnsupportedPointeeRead)

  test "F1 after (shouldStop eager-halt): graft does not change sxSat; the poison NEVER fires":
    ## `shouldStop` (`runtime.nim:8445`) halts the ENTIRE walk the instant a
    ## clean `sxSat` lands in `w.found` -- discovered here BEFORE the walker
    ## ever reaches the poison arm textually following it, so the graft is
    ## never even visited. Verdict equality is therefore trivial (nothing
    ## ran), but the non-firing itself is worth pinning: it is the empirical
    ## confirmation that `shouldStop`'s eager halt is safe -- code sequenced
    ## strictly after an eagerly-discovered clean witness cannot contribute
    ## taint that would ever reach a verdict.
    let base = symexFind(s3w1Base, tLabel("s3_w1_base"))
    let r = symexFind(s3w1F1After, tLabel("s3_w1_f1_after"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)

  test "F2 before (shouldStop pin): graft does not change sxSat; seUnsupportedStringOp fired":
    let base = symexFind(s3w1Base, tLabel("s3_w1_base"))
    let r = symexFind(s3w1F2Before, tLabel("s3_w1_f2_before"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check r.errors.hasKind(seUnsupportedStringOp)

  test "F2 after (shouldStop eager-halt): graft does not change sxSat; the poison NEVER fires":
    let base = symexFind(s3w1Base, tLabel("s3_w1_base"))
    let r = symexFind(s3w1F2After, tLabel("s3_w1_f2_after"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check not r.errors.hasKind(seUnsupportedStringOp)

# ---- W2: sxRaised (funnels F3, F4) ------------------------------------------

proc s3w2Base(x: int) =
  if x == 7:
    raise newException(ValueError, "s3 w2 base")

proc s3w2F3Before(p: S3F3Point, b: int, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    var q = p
    q.x += b
  do:
    if b == 7:
      raise newException(ValueError, "s3 w2 f3 before")

proc s3w2F3After(p: S3F3Point, b: int, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    var q = p
    q.x += b
  do:
    if b == 7:
      raise newException(ValueError, "s3 w2 f3 after")

proc s3w2F4Before(p: ref S3F4Obj, b: int, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    if p != nil: discard p.a1
  do:
    if b == 7:
      raise newException(ValueError, "s3 w2 f4 before")

proc s3w2F4After(p: ref S3F4Obj, b: int, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    if p != nil: discard p.a1
  do:
    if b == 7:
      raise newException(ValueError, "s3 w2 f4 after")

suite "RFC-0005 S3 -- W2 (sxRaised), witness monotonicity":

  test "baseline: x == 7 raises ValueError -> sxRaised":
    let r = symexFind(s3w2Base, tRaisedExn())
    check r.status == sxRaised

  test "F3 before (shouldStop pin): graft does not change sxRaised; feUnsupportedStmtKind fired":
    let base = symexFind(s3w2Base, tRaisedExn())
    let r = symexFind(s3w2F3Before, tRaisedExn())
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxRaised
    check r.errors.hasKind(feUnsupportedStmtKind)

  test "F3 after (shouldStop eager-halt): graft does not change sxRaised; the poison NEVER fires":
    ## `shouldStop` also halts on a clean `sxRaised` for a non-label target
    ## (`w.target.kind != stkLabel`, `runtime.nim:8445`) -- same eager-halt
    ## as W1/W3's `sxSat` case, verified here for the raise-flavoured rule.
    let base = symexFind(s3w2Base, tRaisedExn())
    let r = symexFind(s3w2F3After, tRaisedExn())
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxRaised
    check not r.errors.hasKind(feUnsupportedStmtKind)

  test "F4 before (shouldStop pin): graft does not change sxRaised; heRefVariantUnsupported fired":
    let base = symexFind(s3w2Base, tRaisedExn())
    let r = symexFind(s3w2F4Before, tRaisedExn())
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxRaised
    check r.errors.hasKind(heRefVariantUnsupported)

  test "F4 after (shouldStop eager-halt): graft does not change sxRaised; the poison NEVER fires":
    let base = symexFind(s3w2Base, tRaisedExn())
    let r = symexFind(s3w2F4After, tRaisedExn())
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxRaised
    check not r.errors.hasKind(heRefVariantUnsupported)

# ---- W3: sxSat behind a loop and a call (funnels F1, F3) -------------------

proc s3w3Helper(n: int): int =
  var acc = 0
  var i = 0
  while i < n:
    acc += i
    i.inc
  acc

proc s3w3Base(n: int) =
  let r = s3w3Helper(n)
  if r == 6:
    symexTarget("s3_w3_base")

proc s3w3F1Before(p: S3F1Node, n: int, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    if p != nil: discard p.s
  do:
    let r = s3w3Helper(n)
    if r == 6:
      symexTarget("s3_w3_f1_before")

proc s3w3F1After(p: S3F1Node, n: int, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    if p != nil: discard p.s
  do:
    let r = s3w3Helper(n)
    if r == 6:
      symexTarget("s3_w3_f1_after")

proc s3w3F3Before(p: S3F3Point, b, n: int, poisonOn: bool) =
  withPoisonedArm(paBefore, poisonOn):
    var q = p
    q.x += b
  do:
    let r = s3w3Helper(n)
    if r == 6:
      symexTarget("s3_w3_f3_before")

proc s3w3F3After(p: S3F3Point, b, n: int, poisonOn: bool) =
  withPoisonedArm(paAfter, poisonOn):
    var q = p
    q.x += b
  do:
    let r = s3w3Helper(n)
    if r == 6:
      symexTarget("s3_w3_f3_after")

suite "RFC-0005 S3 -- W3 (sxSat behind a loop + a call), witness monotonicity":

  test "baseline: sum(0..<4) == 6 via a helper call over a bounded loop -> sxSat":
    let r = symexFind(s3w3Base, tLabel("s3_w3_base"))
    check r.status == sxSat

  test "F1 before (shouldStop pin): graft does not change sxSat; heUnsupportedPointeeRead fired":
    let base = symexFind(s3w3Base, tLabel("s3_w3_base"))
    let r = symexFind(s3w3F1Before, tLabel("s3_w3_f1_before"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check r.errors.hasKind(heUnsupportedPointeeRead)

  test "F1 after (shouldStop eager-halt): graft does not change sxSat; the poison NEVER fires":
    let base = symexFind(s3w3Base, tLabel("s3_w3_base"))
    let r = symexFind(s3w3F1After, tLabel("s3_w3_f1_after"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)

  test "F3 before (shouldStop pin): graft does not change sxSat; feUnsupportedStmtKind fired":
    let base = symexFind(s3w3Base, tLabel("s3_w3_base"))
    let r = symexFind(s3w3F3Before, tLabel("s3_w3_f3_before"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check r.errors.hasKind(feUnsupportedStmtKind)

  test "F3 after (shouldStop eager-halt): graft does not change sxSat; the poison NEVER fires":
    let base = symexFind(s3w3Base, tLabel("s3_w3_base"))
    let r = symexFind(s3w3F3After, tLabel("s3_w3_f3_after"))
    checkpoint($kindNames(r.errors))
    check r.status == base.status
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedStmtKind)

# =============================================================================
# Family 2a -- classification pins: the ONLY witness lies ON a tainted path
# =============================================================================
# Not a graft: the degrade sits BETWEEN every path and the target (nested
# inside the same guard, or simply unconditional before the target check),
# so there is no clean path to the target at all. §2.3 rule 4: a solved SAT
# -- candidate included -- terminally blocks `sxUnsat`, and a candidate never
# wins by itself, so the verdict must be `sxUnknown`, never `sxSat`.

proc s3ClassifyF1(p: S3F1Node, x: int) =
  if p != nil:
    discard p.s
    if x == 42:
      symexTarget("s3_classify_f1")

proc s3ClassifyF2(x: int64) =
  discard toOct(x, 3)
  if x == 42:
    symexTarget("s3_classify_f2")

proc s3ClassifyF3(p: S3F3Point, b: int) =
  var q = p
  q.x += b
  if b == 42:
    symexTarget("s3_classify_f3")

proc s3ClassifyF4(p: ref S3F4Obj, y: int) =
  if p != nil:
    discard p.a1
    if y == 42:
      symexTarget("s3_classify_f4")

suite "RFC-0005 S3 -- family 2a: a witness reachable ONLY through a tainted path never reports sxSat":

  test "F1: heUnsupportedPointeeRead sits between every path and the target -> sxSat only via a confirmed replay":
    ## RFC-0005 S10: `heUnsupportedPointeeRead` is `dcFreshSymbol` (S4), so
    ## the tainted path's model is a replay-eligible CANDIDATE. Reality
    ## reaches the label (any non-nil `p`, x == 42), the replay confirms it
    ## (the ref witness is lossy: it may confirm, never refute) -> sxSat.
    ## Family 2a's invariant still holds: the TAINTED path alone never
    ## reports sxSat -- rules 1-2 decide sxUnknown, pinned below.
    let r = symexFind(s3ClassifyF1, tLabel("s3_classify_f1"))
    checkpoint($kindNames(r.errors))
    check r.status == sxSat
    check rfc0005UnvetoedStatus == sxUnknown
    check r.witness[1] == 42
    check r.errors.hasKind(heUnsupportedPointeeRead)

  test "F2: seUnsupportedStringOp sits before every path's target check -> sxUnknown, never sxSat":
    let r = symexFind(s3ClassifyF2, tLabel("s3_classify_f2"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.errors.hasKind(seUnsupportedStringOp)

  test "F3: feUnsupportedStmtKind sits before every path's target check -> sxUnknown, never sxSat":
    let r = symexFind(s3ClassifyF3, tLabel("s3_classify_f3"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.errors.hasKind(feUnsupportedStmtKind)

  test "F4: heRefVariantUnsupported sits between every path and the target -> sxUnknown, never sxSat":
    let r = symexFind(s3ClassifyF4, tLabel("s3_classify_f4"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.errors.hasKind(heRefVariantUnsupported)

# =============================================================================
# Family 2b -- over-taint-only unreachable-target pins (S4/S5/S6's own RED)
# =============================================================================
# Same shape as `tsymex_rfc0005_s0_exhibit.nim`'s pin 1: the target is a
# genuine, value-independent contradiction (`n == 5 and n == 6`), reached (if
# at all) only through the funnel's degrade, and the drained sevError kind
# set is asserted EXACT -- over-taint-only is checked, not assumed. Today the
# conservative `classOf` default (`dcNoAnswer`, verified below) makes every
# one of these `sxUnknown`; each comment names the slice expected to flip it
# to `sxUnsat` and why. F1 flipped at S4 (rewritten in place through
# `checkUnsatOverTaintOnly`); F4 was audited at S4 and F2 at S5, and both stay
# `dcNoAnswer`. F3 (feUnsupportedStmtKind) has no entry here -- see
# this file's header comment for why RFC-0005 §5 names no flipping slice for
# that funnel.

proc s3OverTaintF1(p: S3F1Node, n: int) =
  if p != nil:
    discard p.s
  if n == 5 and n == 6:
    symexTarget("s3_overtaint_f1")

proc s3OverTaintF2(x: int64, n: int) =
  discard toOct(x, 3)
  if n == 5 and n == 6:
    symexTarget("s3_overtaint_f2")

proc s3OverTaintF4(p: ref S3F4Obj, n: int) =
  if p != nil:
    discard p.a1
  if n == 5 and n == 6:
    symexTarget("s3_overtaint_f4")

suite "RFC-0005 S3 -- family 2b: over-taint-only unreachable target (S4/S5/S6's own RED)":

  test "F1: classOf(heUnsupportedPointeeRead) is dcFreshSymbol (RFC-0005 S4)":
    check classOf(heUnsupportedPointeeRead) == dcFreshSymbol

  test "F1: sxUnsat, over-taint-only -- flipped at S4":
    # RFC-0005 S4: was sxUnknown at S3; the site now records the split
    # dcFreshSymbol kind, whose runTaint lacks scIncomplete (§2.3 -> sxUnsat).
    let r = symexFind(s3OverTaintF1, tLabel("s3_overtaint_f1"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError: sevErrorKinds.add e.kind
    check sevErrorKinds == @[heUnsupportedPointeeRead]

  test "F2: classOf(seUnsupportedStringOp) is dcNoAnswer (audited at S5: its sites substitute)":
    check classOf(seUnsupportedStringOp) == dcNoAnswer

  test "F2: sxUnknown, over-taint-only -- stays ⊤ (S5 audit: substituting sites; no RFC-0005 slice flips it)":
    let r = symexFind(s3OverTaintF2, tLabel("s3_overtaint_f2"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.status != sxSat
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError: sevErrorKinds.add e.kind
    check sevErrorKinds == @[seUnsupportedStringOp]

  test "F4: classOf(heRefVariantUnsupported) is dcNoAnswer (audited at S4: its sites substitute)":
    check classOf(heRefVariantUnsupported) == dcNoAnswer

  test "F4: sxUnknown, over-taint-only -- stays ⊤ (S4 audit: substituting sites, no flip)":
    let r = symexFind(s3OverTaintF4, tLabel("s3_overtaint_f4"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.status != sxSat
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError: sevErrorKinds.add e.kind
    check sevErrorKinds == @[heRefVariantUnsupported]

# =============================================================================
# decideVerdict monotonicity (§4.1 family 1, the pure-function form)
# =============================================================================
# "Adding a candidate or taint never demotes a clean found witness." Rule 1/2
# of `decideVerdict` (`runtime.nim`) scan ONLY `found` and `vetoed` -- neither
# `candidates` nor `runTaint` is consulted before a clean winner is found --
# so the property is that the verdict (status AND winnerIdx) is INVARIANT
# under arbitrary changes to `candidates`/`runTaint` as long as `found` and
## `vetoed` are held fixed and `found` already contains a clean winner. The
# state space is small and exactly enumerable (`Taint` has 4 values; a
# handful of representative `found`/`candidates` shapes covers every rule
# interaction), so this is a full exhaustive check, not a sampled one --
# stronger than a `forAll` over the same domain would be, which is why
# nelli's own PBT is not used here (§4.1's "otherwise a small exhaustive
# enumeration" case).

proc sat(t: Taint): RawResult = RawResult(status: sxSat, pathTaint: t)
proc raised(t: Taint): RawResult =
  RawResult(status: sxRaised, raisedTypeId: "ValueError", pathTaint: t)
const fresh = {scSpurious}
const allTop = {scSpurious, scIncomplete}

suite "RFC-0005 S3 -- decideVerdict monotonicity: a clean found witness is never demoted":

  test "adding candidates/taint never changes the status or winnerIdx of a clean found witness":
    let foundShapes = @[
      ("clean sat alone", @[sat({})], sxSat, 0),
      ("clean sat first, spurious raised after", @[sat({}), raised(fresh)], sxSat, 0),
      ("spurious sat first, clean raised second", @[sat(fresh), raised({})], sxRaised, 1),
      ("clean raised alone", @[raised({})], sxRaised, 0),
      ("clean raised first, clean sat second (rule 1 beats rule 2 out of discovery order)",
       @[raised({}), sat({})], sxSat, 1),
    ]
    let candidatePools = @[
      newSeq[RawResult](),
      @[sat(fresh)],
      @[sat(fresh), raised(allTop)],
      @[raised(fresh), raised(fresh)],
    ]
    let taintAdditions = @[Taint({}), {scSpurious}, {scIncomplete}, allTop]

    for (label, found, expStatus, expIdx) in foundShapes:
      for cands in candidatePools:
        for rt in taintAdditions:
          let d = decideVerdict(found, cands, rt, vetoed = false)
          checkpoint(label & " | candidates=" & $cands.len & " runTaint=" & $rt &
                     " -> " & $d.status & "/" & $d.winnerIdx)
          check d.status == expStatus
          check d.winnerIdx == expIdx

suite "RFC-0005 S3 -- walker version pin":

  test "walker version floor >= 141 (S3 is test-only -- no walker-semantics change)":
    check parseInt(symexWalkerVersion) >= 141
