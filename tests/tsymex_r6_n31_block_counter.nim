## N31 (round-6 fix round 3) -- spurious sxUnsat after a `block:` containing
## a two-hop literal-seeded scan-loop counter -- walker v100.
##
## ---- Root cause ----------------------------------------------------------
## `tryRecognizeAccumulatingScan` (`dsl_parser.nim`) lifts a recognized
## `readCString`-shaped scan loop to a closed form built on `iekStrFind`/
## `iekStrSubstr` (B4, `dsl_parser.nim` ~4893). `iekStrSubstr` (Cluster S,
## `runtime_strings.nim`) requires its `lo`/`hi` slice bounds to lower as
## Z3 Int (never a bitvector) -- a BV-represented bound would bv2int-bridge
## into Z3's Sequence theory, an empirically-confirmed non-termination shape
## (the pre-existing v66 "CR-17" guard). The loop counter in this repro
## (`var i = localOffset` where `localOffset` is itself seeded by an int
## LITERAL, `var localOffset = 3`) is a TWO-HOP chain neither pre-pass
## collector covers: `collectIntOffsetParams` only traces to a FORMAL
## parameter root (`localOffset` is a local, not a formal); the B7r2
## companion `collectIntOffsetLiteralLocals` only checks whether the
## counter's OWN declaration is a bare literal (`i`'s own init is the
## symbol `localOffset`, not a literal -- it does not trace one hop
## further back through `localOffset`'s own declaration). So `i` gets no
## `isIntOffset` stamp and is allocated the type-driven BV64 default
## (`intLitProto`) -- confirmed by direct instrumentation of the `isLet`
## walker arm (`runtime.nim` ~6702) during this slice's probe.
##
## `iekStrSubstr` then sees a BV-sorted bound and hits its CR-17 guard --
## which, PRE-FIX, was a raw `raise (ref SymexUnsupportedStringOpError)`.
## That is exactly the C-backend goto-exception hazard ADR-0023/SND-3 exists
## to ban from `lower()`: "a `raise` here would unwind through the enclosing
## loop's live `seq[Path]` and be silently lost on the C backend's
## goto-exception model (b7258f7/CR-1c class)" -- the EXACT comment already
## present at the sibling CR-17(a) ordering-comparison guard in
## `runtime.nim`, which was already fixed to degrade in-band for this same
## reason. `iekStrSubstr`'s CR-17 guard (added later, v66) was never
## migrated to that discipline.
##
## Direct instrumentation (this slice's probe, reverted before landing)
## confirmed the mechanism precisely: with the scan loop wrapped in an
## explicit `block:` (two nested `walkBlock` frames: the block's own body,
## nested inside the proc's top-level body), the `raise` statement executes
## (`stderr` trace immediately before the `raise` fires) but the SAME query
## against the UNWRAPPED (no-`block:`) shape reaches the specific-typed
## `except SymexUnsupportedStringOpError` handler at `runSymex`'s boundary
## and correctly returns `sxUnknown`. In the `block:`-wrapped shape, no
## `except` handler is ever entered, `walk()` returns as if it completed
## normally (`w.found.len == 0`, `w.sawUnknown == false`, zero errors), and
## the walker's default-to-UNSAT fallback fires -- a wrong verdict for a
## concretely reachable target (Invariant 3 violation: this is a spurious
## sxUnsat, not merely an imprecise one).
##
## ---- Fix ------------------------------------------------------------------
## `iekStrSubstr`'s CR-17 decline (`runtime_strings.nim`) now degrades
## IN-BAND exactly like every other `lower()` site in this class
## (`loweringDegradeErrors.add` + `loweringDidDegrade = true` + a fresh
## unconstrained `svString` via `allocateSym`), mirroring the CR-17(a)
## ordering-comparison guard and `cmpString`'s S3 ordering fallback verbatim.
## `drainPendingLowerEffects` -- the mandatory drain at every `lower()` call
## site inside `walk`, already unconditionally invoked by `lowerInExpr` for
## this call site -- forks the path `uncertain = true` and sets
## `w.sawUnknown` regardless of nesting depth, so the decline is now honest
## at ANY nesting depth. This is a mechanism-level fix (the raise itself was
## unsound to use here, independent of any particular shape), not a
## shape-specific decline: it also INCIDENTALLY upgrades the previously
## `sxUnknown`-declining unwrapped (no-`block:`) shape to a correct `sxSat`
## in cases where a legitimate sibling path (the loop-not-entered branch)
## proves the target reachable without ever touching the degraded branch --
## see section 4 below, pinned as an upgrade, not assumed.
##
## ---- Version discipline ----------------------------------------------------
## VERDICT-AFFECTING (a previously false `sxUnsat` now correctly reports
## `sxSat`; the unwrapped companion is upgraded `sxUnknown` -> `sxSat` too):
## `symexWalkerVersion` bumps 99->100.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# 1. THE BUG -- two-hop literal-seeded counter, scan loop wrapped in a
#    `block:`, target AFTER the block. Concretely reachable: `data = @[]`
#    never enters the loop (`i = 3 >= data.len = 0`), so the block completes
#    trivially and "after" is reached with `acc`/`i` unchanged.
# =============================================================================

proc sutN31BlockAfter(data: seq[byte]) =
  block:
    var localOffset = 3
    var acc = ""
    var i = localOffset       ## two-hop: seeded from a literal-seeded LOCAL,
                               ## not a literal or a formal param directly.
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc
  symexTarget("n31_block_after")

suite "symex N31 -- two-hop literal-seeded counter inside a block:":

  test "N31-1: post-block target is reachable (sxSat) -- pre-fix this was the false sxUnsat":
    let r = symexFind(sutN31BlockAfter, tLabel("n31_block_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    # Ground truth: reachable both via the loop-skipped path (data.len <= 3)
    # and via a loop-entered "not found" path (data.len > 3, no NUL byte at
    # or after index 3) -- either witness shape is a legitimate replaying
    # input, so no further shape assertion on the witness content itself.

# =============================================================================
# 2. Target BEFORE the block -- companion, must stay correct (unaffected by
#    anything after the block; matches N28's own isolation precedent).
# =============================================================================

proc sutN31BlockBefore(data: seq[byte]) =
  symexTarget("n31_block_before")
  block:
    var localOffset = 3
    var acc = ""
    var i = localOffset
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc

suite "symex N31 -- regression: target before the block stays correct":

  test "N31-2: pre-block target is unconditionally reachable (sxSat)":
    let r = symexFind(sutN31BlockBefore, tLabel("n31_block_before"))
    check r.status == sxSat

# =============================================================================
# 3. Direct literal seed (`var i = 3`, no two-hop), still inside a block,
#    target after -- companion, must stay correct. `i`'s OWN declaration is
#    a bare literal, so `collectIntOffsetLiteralLocals` marks it directly;
#    no BV/CR-17 mismatch ever occurs on this shape, pre- or post-fix.
# =============================================================================

proc sutN31DirectLiteralBlockAfter(data: seq[byte]) =
  block:
    var acc = ""
    var i = 3                 ## direct literal seed -- NOT two-hop.
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc
  symexTarget("n31_directlit_after")

suite "symex N31 -- regression: direct literal-seeded counter in a block stays correct":

  test "N31-3: post-block target reachable (sxSat), unaffected by the fix (no CR-17 mismatch here)":
    let r = symexFind(sutN31DirectLiteralBlockAfter, tLabel("n31_directlit_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# 4. The SAME two-hop shape WITHOUT the `block:` wrapper. Pre-fix this
#    honestly declined `sxUnknown` (the raise reached `runSymex`'s specific
#    `except` handler directly, one nesting level shallower than the
#    `block:`-wrapped shape). The fix is a MECHANISM change (raise ->
#    in-band per-path degrade), not a block-shape-specific patch, so it
#    ALSO applies here: the loop-skipped sibling path (`i >= data.len`) is
#    no longer discarded by an all-or-nothing raise, and legitimately proves
#    the target reachable on its own. This is an intentional, justified
#    UPGRADE (sxUnknown -> sxSat), not a regression -- confirmed by
#    concrete run this slice, not assumed.
# =============================================================================

proc sutN31NoBlockAfter(data: seq[byte]) =
  var localOffset = 3
  var acc = ""
  var i = localOffset
  while i < data.len:
    if data[i] == 0'u8:
      return
    acc.add char(data[i])
    i.inc
  symexTarget("n31_noblock_after")

suite "symex N31 -- no-block two-hop shape: honest decline upgraded to sxSat by the same fix":

  test "N31-4: post-loop target reachable (sxSat) -- UPGRADED from the pre-fix sxUnknown decline":
    let r = symexFind(sutN31NoBlockAfter, tLabel("n31_noblock_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# 5. UNSAT companion -- a genuinely-unreachable post-block target, proving
#    the fix does not over-correct into false sxSat. Uses the direct-literal
#    (non-degrading) shape from section 3 so the verdict is unambiguous: no
#    degraded/tainted branch is ever involved, so a genuinely-impossible
#    condition after the block must cleanly prove sxUnsat. The guard is
#    `data.len < 0` (always false -- `seq.len` is modeled non-negative), NOT
#    a bare literal-vs-literal comparison (`1 == 2`): a literal `1 == 2`
#    guard was tried first and hit a DIFFERENT, orthogonal walker gap
#    (`lowerBool: expected Bool, got svBV64`) with an IDENTICAL block body to
#    section 3's SUT (which passes cleanly with no guard at all) -- i.e. a
#    pre-existing gap in lowering a constant-folded `if` condition, not
#    anything this slice's fix touches (the fix is scoped to `iekStrSubstr`
#    alone). Not this slice's finding to root-cause or fix; avoided rather
#    than worked around, so this companion tests exactly what it claims to.
# =============================================================================

proc sutN31DirectLiteralBlockAfterUnsat(data: seq[byte]) =
  block:
    var acc = ""
    var i = 3
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc
  if data.len < 0:
    symexTarget("n31_directlit_unreachable_after")

suite "symex N31 -- UNSAT companion: no over-correction":

  test "N31-5: a data-independent false condition after the block still proves sxUnsat":
    let r = symexFind(sutN31DirectLiteralBlockAfterUnsat,
                       tLabel("n31_directlit_unreachable_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat

# =============================================================================
# 6. Raise-path companion -- the loop's `data[i]` read genuinely CAN raise
#    IndexDefect for suitable data (a negative-seeded two-hop counter: `i`
#    starts at -1, `i < data.len` is true for essentially any `data`, and
#    the closed form's own entry-read probe reads `data[-1]`, a real Nim
#    IndexDefect). Verdict established by concrete run this slice, per the
#    ADR-0012 D2 target-independent precedence (sxSat > sxRaised > sxUnsat/
#    sxUnknown): the "after" label is never reached on ANY path once the
#    only way in is a starting index that is always out of range, so the
#    engine reports the escaped defect rather than sxUnsat/sxUnknown.
# =============================================================================

proc sutN31BlockAfterRaisePath(data: seq[byte]) =
  block:
    var localOffset = -1
    var acc = ""
    var i = localOffset
    while i < data.len:
      if data[i] == 0'u8:
        return
      acc.add char(data[i])
      i.inc
  symexTarget("n31_raisepath_after")

suite "symex N31 -- raise-path companion: real IndexDefect is reported honestly":

  test "N31-6: the only entry into the loop is a real out-of-range read (sxRaised IndexDefect)":
    let r = symexFind(sutN31BlockAfterRaisePath, tLabel("n31_raisepath_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

# =============================================================================
# Version pin
# =============================================================================

suite "symex N31 -- walker version pin":

  test "walker version floor >= 100 (N31: iekStrSubstr CR-17 decline now degrades in-band, verdict-affecting)":
    check parseInt(symexWalkerVersion) >= 100
