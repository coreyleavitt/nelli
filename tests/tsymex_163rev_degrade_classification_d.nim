## Issues #161/#163 handoff follow-up -- two "unclassified degrade" defects,
## both about the engine's Invariant 3 contract: when the walker cannot
## model something it must DECLINE AND NAME IT (a classified
## `SymexErrorKind`), never report a silent wrong verdict and never let a
## raw internal exception escape as if the engine itself had a bug.
## `weInternalWalkerFault` is the last-resort backstop meaning "the engine
## has a bug"; using it for "this program uses a feature we don't model"
## misattributes a product limitation as an engine fault.
##
## ----------------------------------------------------------------------------
## Item 1 -- a module-level global read (LANDED)
## ----------------------------------------------------------------------------
## `lower`'s `iekVar` arm (`runtime.nim`) reaches a name absent from `env` --
## the walker does not model module-level globals AT ALL, and the parser
## deliberately lets a free/global name through as a bare `iekVar` (there is
## no other route by which an unbound name reaches `lower`: every local/param
## the parser emits is bound before its first read -- confirmed live via
## `scratchpad/bench/probe_163_globals.nim`, which reported, PRE-FIX:
##
##   readsGlobal          status=sxUnknown
##       weInternalWalkerFault [sevError] KeyError: key not found: gLimit
##
## `types.nim` gained a new tail member, `feGlobalReadUnmodelled` (see its own
## doc comment, `types.nim`, for the full writeup) naming exactly this gap.
##
## IMPLEMENTATION CORRECTION vs. the original proposal: the proposal above
## (this file's prior revision) called for RAISING the existing
## `SymexClassifiedDegradeError` carrier at the `iekVar` site, matching the
## textually-nearest precedent (`iekSeqLen`'s `else` arm, a few hundred lines
## below in `runtime.nim`). That precedent is marked `verified-unreachable`
## -- a defensive backstop, never actually triggered by a live walk. `iekVar`
## is the OPPOSITE: it fires on every ordinary global read, and `lower()` is
## called recursively from arbitrarily deep inside `walkBlock` frames (any
## global read inside a loop body or branch). Per this file's own extensively
## documented ADR-0023/SND-3 invariant -- see `allocDegrade`'s and
## `degradeStrArm`'s doc comments -- a raw `raise` reached from inside nested
## `walkBlock` frames is silently LOST by Nim's C-backend goto-exception
## unwind: `lower()` returns as if nothing happened, `w.sawUnknown` is never
## set, and the walker's default-to-UNSAT fallback can report a false
## `sxUnsat` for a concretely reachable target -- N31's original bug,
## reintroduced for global reads specifically. The landed fix instead
## degrades IN-BAND: it records `feGlobalReadUnmodelled` via the same
## `loweringDegradeErrors`/`loweringDidDegrade` threadvar sink every other
## `lower()`-internal degrade in this file uses, then hands back a fresh
## unconstrained symbol of the best-known type (mirroring the existing
## `wmFollowConcrete` havoc construction immediately below it in the same
## `iekVar` arm) -- no `raise`, no new marked site in the raw-raise-in-lower
## audit (`tsymex_r6_n36_raise_class_audit.nim`; confirmed unchanged, see
## that file's own re-run for this fix). See `runtime.nim`'s `iekVar` arm for
## the landed code and its own doc comment for the full mechanism writeup.
##
## ----------------------------------------------------------------------------
## Item 2 -- the maxCallDepth bail degrades unclassified (FIXED here)
## ----------------------------------------------------------------------------
## `runtime.nim`'s `isCall` dispatch bails once `w.callStack.len >=
## settings.budget.maxCallDepth`, tainting the surviving paths so any target
## reached downstream degrades to `sxUnknown` -- correct verdict behaviour,
## but the bail used to set `w.sawUnknown = true` bare, with no entry in
## `w.walkDegradeErrors`. The run-level Invariant-7 backstop
## (`runSymexImpl`) then reports the SAME `weInternalWalkerFault` bare-
## unknown message item 1 does, from an entirely different, ordinary-
## configuration cause ("your call nesting exceeded the budget, raise
## maxCallDepth" vs. "the engine could not model something"). Confirmed
## live via `scratchpad/bench/probe_maxcalldepth.nim`, pre-fix:
##
##   countdown-capped     status=sxUnknown nerrors=1
##       weInternalWalkerFault [sevError] sxUnknown produced with no
##       classified reason -- an unclassified degrade site set sawUnknown
##       bare (walker classification gap; weInternalWalkerFault)
##
## `beBudgetExhausted` (chapulin catalog #5(b)) already names exactly this
## shape -- "a walk budget ran out with paths still live" -- for
## `maxLoopUnwind`/`maxFrontierSize`; this call-inlining depth cap is a
## sibling of the SAME budget family, so the fix reuses the existing kind
## rather than adding a near-duplicate, and the message names the exhausted
## budget (`maxCallDepth=N`) and the actionable remedy (raise
## `settings.budget.maxCallDepth`).
##
## This is an ERROR-REPORTING fix, not a verdict change: the affected paths
## already tainted to `sxUnknown` before this commit; only the attribution
## (which classified kind rides that verdict) changed. `symexWalkerVersion`
## is NOT bumped for either item.
##
## House rule: every symbolic expectation below is paired with an ORACLE --
## the same computation executed for real in Nim, in this file.
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_163rev_degrade_classification`,
## `tsymex_163rev_degrade_classification_b`,
## `tsymex_163rev_degrade_classification_c`. Split so that each part compiles
## and runs in under 60 s on the Windows legs (the whole file took 89 s).

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

suite "#161/#163 handoff -- walker version pin":

  test "walker version floor >= 138 (no bump owed by this fix -- error reporting only)":
    check parseInt(symexWalkerVersion) >= 138
