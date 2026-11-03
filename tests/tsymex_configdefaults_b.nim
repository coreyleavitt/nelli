## RFC-0010 — the definition of done, symex half.
##
## `SymexSettings` and `ResourceBudget`: the documented construction idiom run
## through the real entry point (`symexFind`, whose `settings` parameter is a
## `static SymexSettings`), asserting that the fields the caller did not list
## carry the defaults rather than zeros.
##
## Separate from `tests/tconfigdefaults.nim` on purpose. Covering all five
## surfaces in one file would import the SMT stack and make the whole
## definition of done Z3-linked, undoing for it what RFC-0004 made true of
## `import nelli`. This half is the one that legitimately needs Z3.
##
## Named `tsymex_configdefaults` rather than the RFC's `tsymexconfigdefaults`
## because `scripts/derive-ci-suites.ps1` builds the symex-mingw corpus by
## matching `tsymex_*` **with the underscore**. Without it this file would be
## invisible to the only CI leg that runs the symex corpus — which is exactly
## the registration gap slice B1 exists to close for four other files.
##
## Slice ownership: B2 owns the defaults; B3 adds the merge pins.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with `tsymex_configdefaults`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 64 s).

import std/unittest
import nelli/symex

# ---------------------------------------------------------------------------
# RFC-0010 B3 — regression pins for the deprecated merge.
#
# `+` is deprecated, not deleted: it is public, and round 2 established it has
# zero production callers (its only calls in the tree are these tests of
# itself). Round 1 proposed replacing both hand-written bodies with a generic
# recursive `merged` plus a generative algebraic-law suite — investment in an
# operator with no users, and a naive `fields()` rewrite would have silently
# broken nested composition. So the bodies stay and two cheap pins stop a
# deprecated-but-live operator from rotting silently.
#
# These are GREEN today by design. They are regression pins, not acceptance
# tests — both bodies currently cover every field.
# ---------------------------------------------------------------------------
{.push warning[Deprecated]: off.}

{.pop.}

# ---------------------------------------------------------------------------
# RFC-0010 B4 — the "0 = unlimited" promise, verified per field.
#
# `ResourceBudget`'s doc comment (`smt/types.nim`) promises 0 = unlimited for
# every field except three documented exceptions. Round 1 found three
# enforcement sites with no `> 0` guard, so an explicit 0 exhausted the
# budget on the FIRST use instead of behaving as unlimited: `maxCallDepth`,
# `maxClosureInlineCount`, `maxBytesEncodingLen` (`maxLoopUnwind`'s two sites
# were never touched — its own field doc already said ">= 1", the false
# promise lived only in the umbrella comment). Round 1 added a `cap > 0 and`
# guard for all three.
#
# Round 2 found the `maxCallDepth` guard WRONG and reverted it: two
# independent reviewers reproduced a SIGSEGV (native stack exhausted in
# under a second) against ordinary linear recursion under `maxCallDepth: 0`
# — disabling the depth cap does not make the search "unlimited," it removes
# the only thing standing between the walker and the host's native call
# stack, and `w.activeCalls`'s cycle-breaking does not catch this (it only
# fires for recursion with IDENTICAL argument shapes across levels).
# `maxCallDepth` is therefore promoted to a THIRD documented "0 does NOT mean
# unlimited" exception, alongside `maxLoopUnwind`/`seqInlineThreshold` (see
# `ResourceBudget`'s umbrella doc comment, `smt/types.nim`). The other two
# guards stay fixed and correct: `maxClosureInlineCount` (the walker declines
# a forward-declared self-referencing closure with `ceClosureUnknownCallee`
# before it could ever recurse, so there is no equivalent crash to trade for)
# and `maxBytesEncodingLen` (never recursive at all) -- the latter since
# deleted with the name-matched `bytes(s)` model it capped (RFC-0005 S8c:
# Nim has no stdlib `bytes`; the model was reachable only through a user
# proc of that name, which S8c walks instead). Each SUT below only
# reaches its target by actually exercising the guarded machinery, so a
# wrongly-firing budget degrades the whole run to `sxUnknown` instead of the
# definite verdict the default budget reaches — the same shape as this
# file's pre-existing `maxHeapDepth`/`maxSplitParts` zero-survival pins
# above.
# ---------------------------------------------------------------------------

# --- maxCallDepth: the target lives one call deep -------------------------
proc b4CallDepthHelper() =
  symexTarget("call_depth_hit")

proc b4CallDepth(x: int) =
  if x == 7:
    b4CallDepthHelper()

# --- maxClosureInlineCount: a single-level closure call -- mirrors C6's
# `c6Capture` (tsymex_phase15_C6_smoke.nim), the simplest shape that needs a
# real lambda-body descent (not just a funcApp placeholder) to prove sat. ---
proc b4ClosureInline(x: int) =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  if f(3) == 13:
    symexTarget("closure_inline_hit")

suite "RFC-0010 B4 — explicit zero means unlimited (the fixed field)":

  test "maxClosureInlineCount: 0 must not block the first closure application":
    let viaDefault = symexFind(b4ClosureInline, tLabel("closure_inline_hit"))
    check viaDefault.status == sxSat
    let viaZero = symexFind(b4ClosureInline, tLabel("closure_inline_hit"),
        SymexSettings(budget: ResourceBudget(maxClosureInlineCount: 0)))
    check viaZero.status == sxSat

# ---------------------------------------------------------------------------
# RFC-0010 B4 round 2 — maxCallDepth joins maxLoopUnwind as a documented
# "0 does NOT mean unlimited" exception. Unlike `maxLoopUnwind`, observing
# the exhaustion needs no recursion at all: `b4CallDepth` above is a single
# non-recursive call, so probing it with `maxCallDepth: 0` cannot
# native-stack-overflow even with the cap disabled -- it only proves the
# guard fires on the very first call, the honest contract. Whether an
# explicit LARGE bound genuinely reaches deeper recursion (not merely holds
# the right integer) is checked separately below with real recursion, bounded
# by `symexAssume` so the SUT stays decidable regardless of the cap.
# ---------------------------------------------------------------------------
proc boundedRecursion(n: int): int =
  if n > 0:
    result = boundedRecursion(n - 1) + 1
  else:
    result = 0

proc boundedRecursionSut(n: int) =
  # Bounded via symexAssume so the SUT is decidable in principle; the only
  # question a passing/failing verdict answers is whether the CONFIGURED
  # maxCallDepth is deep enough to reach the witness. Needs recursion depth
  # up to 9 -- well past the default cap of 3 and past `maxCallDepth: 0`'s
  # immediate exhaustion, but comfortably under an explicit large bound.
  symexAssume(n >= 0 and n < 10)
  if boundedRecursion(n) == 7:
    symexTarget("bounded_recursion_hit")

suite "RFC-0010 B4 round 2 — maxCallDepth is a documented exception, not unlimited":

  test "the default budget reaches a definite verdict for a shallow call":
    let r = symexFind(b4CallDepth, tLabel("call_depth_hit"))
    check r.status == sxSat

  test "an explicit 0 is NOT unlimited -- it exhausts immediately, by design":
    let r = symexFind(b4CallDepth, tLabel("call_depth_hit"),
        SymexSettings(budget: ResourceBudget(maxCallDepth: 0)))
    check r.status == sxUnknown

  test "an explicit large bound genuinely reaches deeper recursion":
    # The default cap (3) is too shallow for this SUT's needed depth (up to
    # 9) and declined; an explicit large bound must actually let the walker
    # descend that far and find the real witness. RFC-0005 S8ax: `n < 10`
    # bounds the recursion, so the adaptive depth follows it past the
    # default cap and the default now finds the witness too (`n == 7`).
    let viaDefault = symexFind(boundedRecursionSut, tLabel("bounded_recursion_hit"))
    check viaDefault.status == sxSat
    let viaLargeBound = symexFind(boundedRecursionSut,
        tLabel("bounded_recursion_hit"),
        SymexSettings(budget: ResourceBudget(maxCallDepth: 20)))
    check viaLargeBound.status == sxSat

# --- maxLoopUnwind: probed under the SAME "0 = unlimited" hypothesis as the
# three fields above -- and REFUTED. `boundedLoopZero` mirrors
# tsymex_r6_n20_boundedloop.nim's `boundedLoopSat`: `symexAssume` bounds `n`
# to [0,3), so only 2 concrete iterations are ever needed -- well inside the
# default budget of 5.
#
# RED-first, as instructed: with the naive hypothesis (0 == unlimited, same
# as the three fields above), `ResourceBudget(maxLoopUnwind: 0)` against this
# SUT was RED -- `sxUnknown`, budget-exhausted, for the identical reason the
# other three fields failed. But unlike those three, the fix here is NOT a
# missing `> 0` guard. Investigated and REJECTED making `unwind = 0` mean
# "no bound" at either k-unroll site (`runtime.nim`'s `isWhile` wmExplore arm
# and `walkWhileFollowConcrete`), for two independent reasons — each is
# sufficient on its own, and both are argued in full at the guard sites
# themselves:
#
#   1. wmExplore forks BOTH the continue and exit branch at EVERY iteration
#      with no per-iteration feasibility check (deliberate, per N20's
#      seeded-future-work note) -- `active` never shrinks on its own for an
#      ORDINARY loop body, so `unwind = 0` would not terminate for
#      essentially any while loop reaching this arm, not just pathological
#      ones. That is a direct Invariant-3 (never hang) violation.
#   2. `walkWhileFollowConcrete`'s own pre-existing doc comment already says
#      the bound is kept as "a safety backstop" specifically because a
#      malformed/adversarial `concreteEq` must not hang the walker -- i.e.
#      even the concrete-replay side never claimed safety without SOME
#      finite bound.
#
# `maxLoopUnwind`'s OWN per-field doc comment already said ">= 1" before this
# slice touched anything -- the false "0 = unlimited for every field" promise
# lived entirely in the ResourceBudget UMBRELLA comment (corrected in
# smt/types.nim to name this one exception), not in this field's own doc.
# So: no code guard changes here, and this sub-test pins the honest, CORRECT
# contract instead of a wrong one -- an explicit 0 exhausts immediately, by
# design, the same as any other implausibly-tight budget.
proc boundedLoopZero(n: int) =
  symexAssume(n >= 0 and n < 3)
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc == n:
    symexTarget("loop_zero_hit")

suite "RFC-0010 B4 — maxLoopUnwind, a documented exception (see also maxCallDepth above)":

  test "the default budget reaches a definite verdict":
    let r = symexFind(boundedLoopZero, tLabel("loop_zero_hit"))
    check r.status == sxSat

  test "an explicit 0 is NOT unlimited -- it exhausts immediately, by design":
    let r = symexFind(boundedLoopZero, tLabel("loop_zero_hit"),
        SymexSettings(budget: ResourceBudget(maxLoopUnwind: 0)))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# RFC-0010 B4 — review finding #7: the FINITE default must actually bound a
# runaway search, not merely hold the right integer. The suite above only
# ever asserts the cap structurally; these two SUTs are genuinely unbounded
# under a free `n` and must decline (not hang) under `ResourceBudget()`'s
# defaults.
# ---------------------------------------------------------------------------
proc runawayLoop(n: int) =
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc > 1_000_000:
    symexTarget("runaway_loop_never")

proc runawayRecursion(n: int): int =
  if n > 0:
    result = runawayRecursion(n - 1) + 1
  else:
    result = 0

proc runawayRecursionSut(n: int) =
  if runawayRecursion(n) > 1_000_000:
    symexTarget("runaway_recursion_never")

suite "RFC-0010 B4 — the default budget actually bounds a runaway search":

  test "an unbounded while loop declines under the default maxLoopUnwind":
    let r = symexFind(runawayLoop, tLabel("runaway_loop_never"))
    check r.status == sxUnknown

  test "unbounded recursion declines under the default maxCallDepth":
    let r = symexFind(runawayRecursionSut, tLabel("runaway_recursion_never"))
    check r.status == sxUnknown

  # The explicit finite `maxCallDepth` pin, the one test of this file that
  # takes a minute, is `tsymex_configdefaults_depth`.
