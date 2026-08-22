## N28 (round-6 fix round 3) -- collector root/receiver acceptance by
## SYMBOL identity, not printed name.
##
## ---- Root cause ---------------------------------------------------------
## `markSymOrRootParam` (`dsl_parser.nim`) is the Q3-shared helper both
## param collectors (`collectStringBackedByteSeqParamsImpl` and
## `collectIntOffsetParamsImpl`) use to decide whether a symbol -- or the
## root a local rebinds to, via `findRootParam`'s single-rebind trace -- IS
## one of the proc's own formal parameters:
##   if sym.strVal in paramNames: into.incl sym.strVal          # check 1
##   else:
##     let root = findRootParam(procBody, sym)
##     if root != nil and root.strVal in paramNames:            # check 2
##       into.incl root.strVal
## Both checks compared the candidate's PRINTED NAME against the proc's own
## formal-name set, even though `sym`/`root` are true `nnkSym` nodes with
## real binding identity available (the house `sameSym`/`containsSym`
## primitives, R6/R4). A nested-scope SHADOW local sharing a formal's name
## defeats both checks: `findRootParam` correctly traces a rebind's root to
## the SHADOW's own symbol (check 2), or the scan's own loop-index symbol IS
## itself declared with a formal's name (check 1) -- either way the
## UNRELATED formal (never touched by the scan) gets promoted by name.
## `collectStringBackedByteSeqParamsImpl`'s own direct receiver check
## (`considerCandidate`, no root-tracing at all) has the same check-1-style
## hole.
##
## ---- Confirmed live (section 1) -----------------------------------------
## For the int-offset collector this IS a live, verdict-flipping soundness
## bug, not merely latent: `runtime.nim`'s top-level param-allocation loop
## promotes an `isIntOffset`-marked param to `svInt` UNCONDITIONALLY (no
## declared range) and -- per R3 (S2)'s own deliberate scope note -- does
## NOT stamp `ziWidth`/`ziSigned` at that specific site (to avoid a perf
## regression across the B4/B5/B6 corpus). An unconstrained,
## width-unstamped `svInt` never forks `OverflowDefect` (`overflowCondInt`
## skips when `ziWidth == 0`), so a formal wrongly promoted this way
## silently loses its REAL fixed-width int64 wraparound semantics: a
## `symexFind` reachability search for an overflow that Nim really WOULD
## raise reports a false `sxUnsat` instead of `sxRaised`. Section 1 pins
## exactly this flip, empirically confirmed pre-fix (RED, see below).
##
## ---- A construction note (unrelated pre-existing gap, discovered while
## building this pin) -------------------------------------------------
## The obvious repro shape -- shadow-collision block/scan FIRST, real
## formal's overflow check textually AFTER it -- turned out to hit a
## SEPARATE, pre-existing walker gap: reasoning about code positioned
## textually after a `block:` statement that itself contains (inline, or
## via a call to a callee) a recognized accumulating-scan closed form
## reliably produces a spurious `sxUnsat`/`sxUnknown` regardless of any
## name collision at all (confirmed with zero-collision control shapes).
## This is orthogonal to N28 (not touched by this fix, not investigated
## further here -- out of this slice's scope) and would have produced a
## FALSE "confirmed bug" reading (`sxUnsat` pre-fix) had it not been
## isolated: the SAME `sxUnsat` appeared with a genuinely-unmarked shadow
## name, proving name collision was not the cause. Every SUT below instead
## places its own observable BEFORE the shadow-collision block (mirroring
## `tsymex_r6_r4_collector_scoping.nim`'s own N2 pattern) -- classification
## is a static, whole-proc pre-pass independent of program order, so the
## collector still sees the collision regardless of where the observable
## sits, and this ordering cleanly avoids the unrelated gap.
##
## ---- Section 3 (string-backed sibling) is HARDENING, not a live flip ----
## The `considerCandidate` direct-name-check analog was probed the same
## way (a shadow local, same name as an unrelated `seq[byte]` formal,
## driving the ACTUAL Q1 scan), using the SAME target-before-block
## construction to control for the gap above. Empirically (both pre- and
## post-fix, this file's own runs), the misclassification does NOT flip any
## verdict or witness here: `allocateSym`'s `itString` arm (byte-range-
## matching regex over the FULL 0x00-0xFF alphabet, `len <= 1024`) and its
## `itSeq` arm (BV8 element cells, `0 <= len <= 1024`) impose IDENTICAL
## effective bounds for non-mutating reads/`.len` -- the two representations
## are behaviorally equivalent from outside for exactly the operations this
## shape can reach without also tripping the PRE-EXISTING, independent,
## name-scoped `scanShapeReceiverMutated` veto (any `.add`/`.del`/
## `.insert`/var-mode-arg use of that same name anywhere in the body --
## which would ALSO incidentally suppress the wrong marking regardless of
## this fix, since it scans by NAME too). Section 3 is still fixed
## (symbol-based acceptance, closing the hole by construction, in lockstep
## with section 1's fix -- same helper, same class of bug, deliberately
## not left inconsistent), but it is HARDENING for this specific check:
## the walker-version bump decision below is driven entirely by section
## 1's confirmed live flip.
##
## ---- Version discipline --------------------------------------------------
## VERDICT-AFFECTING (section 1's int-offset collector flip: a previously
## false `sxUnsat` now correctly reports `sxRaised`): `symexWalkerVersion`
## bumps 97->98.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# =============================================================================
# 1. THE BUG -- int-offset collector, `markSymOrRootParam` check 2 (a
#    rebind's traced ROOT is a shadow, not the formal it happens to share a
#    name with). `offset` (the real formal) is NEVER the scan's own root --
#    a nested-block SHADOW local of the SAME name seeds the accumulating
#    scan's counter instead. The overflow check on the real formal is
#    placed BEFORE the shadow-collision block (see the file header's
#    construction note) -- classification is a static pre-pass, so the
#    collector still sees the shadow/scan below regardless.
# =============================================================================

proc sutN28ShadowedOffsetOverflow(data: seq[byte], offset: int) =
  # The REAL formal `offset`, in ordinary overflow-reachable arithmetic
  # (verbatim `tsymex_r6_r3_svint_overflow` shape) -- real int64 genuinely
  # overflows for any `offset >= 1`.
  if offset + high(int) < offset:
    symexTarget("n28_shadow_offset_overflow")
  block:
    var offset = 3       ## SHADOW -- shadows the formal `offset` above,
                          ## DIFFERENT binding, drives the loop below.
    var acc = ""
    var i = offset
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc

suite "symex N28 -- int-offset collector: shadow-collision root acceptance":

  test "N28-1: the real formal's overflow is reachable (sxRaised) -- pre-fix this was the false sxUnsat":
    let r = symexFind(sutN28ShadowedOffsetOverflow,
                       tLabel("n28_shadow_offset_overflow"))
    # PRE-FIX (verified RED): `offset` was wrongly traced to the shadow's
    # root by NAME, unconditionally svInt-promoted with no width stamp
    # (R3's own top-level-promotion scope note) -> the overflow fork never
    # fires -> false sxUnsat. POST-FIX: `offset` fails the symbol-identity
    # check against the shadow's root (different binding), stays
    # BV-modeled -> `overflowCond`'s existing BV fork fires correctly ->
    # sxRaised, matching real Nim int64 semantics.
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

# =============================================================================
# 2. REGRESSION COMPANION -- the formal genuinely IS the scan's own root
#    (no shadow at all): must stay traced/marked exactly as before this fix
#    (same acceptance test, now by symbol identity instead of name, but a
#    genuine match passes either way). Uses the call-RETURN promotion path
#    (`intOffsetPositions`, verbatim `tsymex_r6_r3_svint_overflow`'s R3-1
#    shape) since that mechanism -- unlike the bare top-level promotion --
#    IS width-stamped, so a correct trace gives a genuinely CORRECT,
#    positively-verifiable sxRaised, not merely "unchanged from before".
# =============================================================================

proc readCStringN28(data: seq[byte], offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutN28LegitOffsetCallReturn(data: seq[byte], start: int) =
  ## `start` genuinely IS `readCStringN28`'s own scan root (direct rebind,
  ## no shadow) -- the one-level call trace must still promote it, and the
  ## call-return `q` must still fork overflow correctly, both pre- and
  ## post-fix.
  symexAssume(start >= 0 and start <= data.len)
  let (_, q) = readCStringN28(data, start)
  if q + high(int) < q:
    symexTarget("n28_legit_call_return_overflow")

suite "symex N28 -- regression: genuine (non-shadowed) root tracing unaffected":

  test "N28-2: a genuinely-traced call-return offset still forks OverflowDefect (sxRaised, unchanged by this fix)":
    let r = symexFind(sutN28LegitOffsetCallReturn,
                       tLabel("n28_legit_call_return_overflow"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"

# =============================================================================
# 3. String-backed sibling -- `considerCandidate`'s direct name check
#    (collectStringBackedByteSeqParamsImpl), exercised both ways. See the
#    file header for why this sub-part empirically turned out to be
#    HARDENING (no observable verdict/witness divergence, confirmed with
#    the SAME target-before-block construction that isolated the unrelated
#    gap in section 1) rather than a second live flip -- still fixed, for
#    the same symbol-identity reason as section 1.
# =============================================================================

proc sutN28StringBackedShadowCollision(data: seq[byte], src: seq[byte]) =
  ## `data` (the real formal) is NEVER itself scanned -- a shadow local
  ## also named `data`, copied from `src`, drives the ACTUAL Q1-shaped scan
  ## `considerCandidate` recognizes. The real formal is read independently,
  ## as an ordinary byte array, BEFORE the shadow-collision block.
  if data.len == 3 and data[0] == 10'u8 and data[1] == 20'u8 and data[2] == 30'u8:
    symexTarget("n28_stringbacked_shadow_read")
  block:
    var data = src
    var i = 0
    while i < data.len and data[i] != 0'u8:
      inc i

suite "symex N28 -- string-backed collector: shadow-collision receiver acceptance":

  test "N28-3: the real formal's honest array read is unaffected either way (already-GREEN both pre- and post-fix -- see file header, hardening only)":
    let r = symexFind(sutN28StringBackedShadowCollision,
                       tLabel("n28_stringbacked_shadow_read"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0][0] == 10'u8
    check r.witness[0][1] == 20'u8
    check r.witness[0][2] == 30'u8

proc sutN28StringBackedLegitScan(data: seq[byte]) =
  ## Regression companion -- `data` genuinely IS the scan's own receiver
  ## (no shadow at all): must stay marked string-backed exactly as before.
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  if i == 2:
    symexTarget("n28_stringbacked_legit_scan")

suite "symex N28 -- regression: genuine (non-shadowed) string-backed receiver unaffected":

  test "N28-4: a genuinely string-backed receiver is still classified and scanned correctly (sxSat)":
    let r = symexFind(sutN28StringBackedLegitScan,
                       tLabel("n28_stringbacked_legit_scan"))
    check r.status == sxSat

# =============================================================================
# Version pin
# =============================================================================

suite "symex N28 -- walker version pin":

  test "walker version floor >= 98 (N28: int-offset collector shadow-collision fix, verdict-affecting)":
    check parseInt(symexWalkerVersion) >= 98
