## RFC-chapulin-hardening SND-3 (ADR-0023, walker v58) — Cluster 1 (Soundness).
##
## Fixes a HIGH-severity C-backend-divergent false `sxUnsat`: a relational
## char/string-ordering comparison (or non-int64 `HashSet`/`set` membership
## test) evaluated inside a LOOP GUARD previously `raise`d a classified
## `Symex*Error` from deep inside expression lowering (the CR-17(a) defensive
## guard, `runtime.nim`). OUTSIDE a loop that raise propagates cleanly to the
## `runSymex` boundary catch -> sound `sxUnknown` on BOTH backends. INSIDE a
## loop guard, the raise unwinds through the walk's live `seq[Path]` and is
## SILENTLY LOST on the C backend's goto-exception model (the b7258f7/CR-1c
## divergence class) -> the walk continues with a mis-lowered guard -> false
## `sxUnsat` on c, while cpp's native exceptions propagate cleanly -> honest
## `sxUnknown`. A backend-divergent verdict is itself a soundness violation
## (one of the two backends must be wrong).
##
## THE FIX (never re-derive; this suite pins it): the lowering-time raise is
## replaced with an IN-BAND degrade — a fresh unconstrained bool, classified
## via the `loweringDegradeErrors`/`loweringDidDegrade` threadvar sinks, folded
## into SND-1's per-path `Path.uncertain` taint at `drainPendingLowerEffects`
## (the single choke-point every `lower()`/`lowerBool()` call site in `walk`
## already drains through). Critically, `w.sawUnknown = true` ALONE would be
## UNSOUND: a fresh unconstrained bool on the tainted path could let that path
## reach the target and fabricate a FALSE `sxSat` — trading a false `sxUnsat`
## for a WORSE false `sxSat`. Tainting the PATH's `uncertain` (demoted at the
## `isTargetLabel`/`routeRaise` chokepoints) is what prevents that.
##
## Every test in this file asserts the SAME verdict is expected on BOTH the
## `c` and `cpp` backends (run via `scripts/dt-bounded.sh c|cpp`) — pinning
## `c == cpp` is the entire point of a backend-divergence fix.
##
## Bumps `symexWalkerVersion` 57->58 (verdict-surface change: a c-backend loop
## guard over an unmodeled char/string-ordering or set-membership compare
## moves from a false `sxUnsat` to the sound `sxUnknown` both backends already
## gave outside a loop). `renderAsChoicesVersion` STAYS "7" — the fresh
## degrade symbol is never solved-for/rendered; the degrade always demotes to
## `sxUnknown`, never produces a new witness shape.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# 1. Tracer/headline — the RFC's exact repro shape. `s.len == 0` is excluded
# so every surviving path evaluates `s[0] >= '0'` on iteration 0 (short-circuit
# `and` means an empty string would exit the loop WITHOUT ever touching the
# degraded comparison, which would let a clean sxSat witness (s="") slip
# through and defeat the point of this test) — every non-empty string taints
# `uncertain` on its very first guard evaluation, so `after_loop` is reached
# ONLY on a tainted path.
proc sutDigitScanLoop(s: string) =
  if s.len == 0:
    return
  var i = 0
  while i < s.len and s[i] >= '0' and s[i] <= '9':
    inc i
  symexTarget("after_loop")

# 2. Per-path soundness — the ONLY route to the target is THROUGH the
# degraded char-ordering compare, and the compare sits inside a loop (the
# exact hazard class this slice fixes). If the fix were unsound (a bare
# `w.sawUnknown = true` with no per-path taint), the fresh unconstrained bool
# could be solved `true` and this would report a fabricated `sxSat` with a
# bogus witness — the "worse-than-before" trap this test exists to catch.
proc sutOnlyViaDegradedCompareInLoop(s: string) =
  var i = 0
  while i < s.len:
    if s[i] >= '0':
      symexTarget("only_via_degrade")
    inc i

# 3. No over-degrade — an independent, completely CLEAN branch (`x == 42`)
# reaches its own target with no unmodeled op anywhere on that path, while the
# SIBLING branch (`x != 42`) contains the degrading loop. Proves the taint is
# per-path (SND-1), not a blunt whole-run kill: the clean branch's witness
# must still surface.
proc sutIndependentCleanPath(x: int, s: string) =
  if x == 42:
    symexTarget("clean_hit")
  else:
    var i = 0
    while i < s.len and s[i] >= '0':
      inc i

# 4. Non-loop regression — the identical char-ordering compare OUTSIDE any
# loop. This was ALREADY sound pre-fix (the raise propagates cleanly to the
# `runSymex` boundary when there's no loop to lose it in) and must remain
# unchanged: still `sxUnknown` on both backends.
proc sutCharOrderingOutsideLoop(s: string) =
  if s.len > 0 and s[0] >= '0':
    symexTarget("outside_loop_degrade")

# 6. Equality regression — `s[i] == 'a'` in a loop guard is NOT an ordering
# comparison (CR-17(a) only guards `<`/`<=`/`>`/`>=`) and must keep resolving
# to a REAL verdict; the fix must not touch this non-raising path at all.
proc sutEqualityLoopGuard(s: string) =
  var i = 0
  while i < s.len and s[i] == 'a':
    inc i
  if i == 3:
    symexTarget("equality_loop_hit")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex RFC-chapulin-hardening SND-3 — loop-guard lowering degrade (c==cpp)":

  test "SND-3-1 (tracer): digit-scan while-guard char-ordering compare -> sxUnknown (was c=sxUnsat)":
    let r = symexFind(sutDigitScanLoop, tLabel("after_loop"))
    check r.status == sxUnknown

  test "SND-3-2: target reachable ONLY via the degraded compare inside a loop -> sxUnknown, NEVER a fabricated sxSat":
    let r = symexFind(sutOnlyViaDegradedCompareInLoop, tLabel("only_via_degrade"))
    check r.status == sxUnknown
    check r.status != sxSat

  test "SND-3-3: independent clean sibling path still yields real sxSat (per-path taint, not blunt kill)":
    let r = symexFind(sutIndependentCleanPath, tLabel("clean_hit"))
    check r.status == sxSat
    check r.witness[0] == 42

  test "SND-3-4 (non-loop regression): same char-ordering compare outside any loop -> sxUnknown (unchanged)":
    let r = symexFind(sutCharOrderingOutsideLoop, tLabel("outside_loop_degrade"))
    check r.status == sxUnknown

  test "SND-3-5: degraded result carries the classified seUnsupportedStringOp kind (Invariant 3)":
    let r = symexFind(sutDigitScanLoop, tLabel("after_loop"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seUnsupportedStringOp and e.severity == sevError:
        sawKind = true
    check sawKind

  test "SND-3-6 (equality regression): s[i]=='a' loop guard still resolves to a real sxSat verdict":
    let r = symexFind(sutEqualityLoopGuard, tLabel("equality_loop_hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check r.witness[0][0] == 'a'
    check r.witness[0][1] == 'a'
    check r.witness[0][2] == 'a'

suite "symex RFC-chapulin-hardening SND-3 — version pins":

  test "walker version floor >= 58 (SND-3 introduced at 58)":
    check parseInt(symexWalkerVersion) >= 58

  test "renderAsChoicesVersion floor >= 7 (SND-3 does NOT bump RC — no new witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
