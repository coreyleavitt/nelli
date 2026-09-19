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
## Item 1 -- a module-level global read (DEFERRED, not implemented here)
## ----------------------------------------------------------------------------
## `lower`'s `iekVar` arm (`runtime.nim`) reaches a name absent from `env` --
## the walker does not model module-level globals AT ALL, and the parser
## deliberately lets a free/global name through as a bare `iekVar` (there is
## no other route by which an unbound name reaches `lower`: every local/param
## the parser emits is bound before its first read -- confirmed live via
## `scratchpad/bench/probe_163_globals.nim`, which reports:
##
##   readsGlobal          status=sxUnknown
##       weInternalWalkerFault [sevError] KeyError: key not found: gLimit
##
## No existing `SymexErrorKind` names this ("a module-level global is read
## and not modelled"); `types.nim` is owned by a sibling agent this session,
## so the fix is NOT implemented here. Proposed new tail member (to be added
## by whoever next owns `types.nim`):
##
##   feGlobalReadUnmodelled ## `lower`'s `iekVar` arm (runtime.nim) reached a
##                         ## name absent from the current `env` -- the
##                         ## walker does not model module-level globals AT
##                         ## ALL, and the parser deliberately passes a
##                         ## free/global name through as a bare `iekVar`
##                         ## (every local/param the parser emits is bound
##                         ## before its first read, so an unbound name here
##                         ## is never a parser bug). Before this kind, the
##                         ## resulting `KeyError` escaped to the top-level
##                         ## catch-all and reported `weInternalWalkerFault`
##                         ## -- an internal-bug attribution for an ordinary,
##                         ## everywhere-applicable modeling gap. The message
##                         ## carries the unbound name so the user knows
##                         ## which global to remove from the reachable
##                         ## computation (or thread through as an explicit
##                         ## parameter). sevError -> sxUnknown (Invariant 3);
##                         ## the soundness argument this unblocks: #163
##                         ## slice 4's opaque-call inertness proof relies on
##                         ## this decline being real and classified -- see
##                         ## `isInertOpaqueCall`'s doc, dsl_parser.nim.
##                         ## Appended at enum tail (ordinal stability).
##
## Once that member lands, the fix is: in `lower`'s `iekVar` arm
## (`runtime.nim`, the `wmExplore`/default branch currently doing a bare
## `env[e.vname]`), raise the existing `SymexClassifiedDegradeError` carrier
## with `feGlobalReadUnmodelled` and a message naming `e.vname`, instead of
## letting the `Table.[]` KeyError escape uncaught. Not done in this commit.
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

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

# =============================================================================
# Item 2 -- maxCallDepth bail classification
# =============================================================================

proc countdown(n: int): int =
  ## Genuine linear recursion: `countdown(12)` needs 13 nested call frames
  ## (n=12 down through n=0) to resolve in real Nim.
  if n <= 0: 0
  else: 1 + countdown(n - 1)

proc probeBottom(n: int) =
  ## The ONLY way to reach the target is a witness with `n == 12`, which
  ## requires the walker to inline `countdown` 13 levels deep.
  if countdown(n) == 12:
    symexTarget("bottom12")

const cappedShallow = SymexSettings(budget: ResourceBudget(maxCallDepth: 3))
const roomyDeep = SymexSettings(budget: ResourceBudget(maxCallDepth: 20))

suite "#161/#163 handoff -- maxCallDepth bail names its own budget":

  test "oracle: countdown(12) really resolves via 13-deep real recursion":
    check countdown(12) == 12
    check countdown(3) == 3
    check countdown(0) == 0

  test "a call-depth cap below the SUT's real recursion degrades to sxUnknown, never sxUnsat":
    ## The witness needs 13 call frames; capped at 3, the walker cannot
    ## soundly confirm or deny the target -- it must fail SAFE (sxUnknown),
    ## never claim the target is unreachable (sxUnsat would be a wrong
    ## verdict: `countdown(12) == 12` truly holds in real Nim).
    let r = symexFind(probeBottom, tLabel("bottom12"), cappedShallow)
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

  test "the depth-cap bail degrades classified, naming the budget and the remedy":
    let r = symexFind(probeBottom, tLabel("bottom12"), cappedShallow)
    var classified = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == beBudgetExhausted and "maxCallDepth" in e.msg and
         "raise" in e.msg and "settings.budget.maxCallDepth" in e.msg:
        classified = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
    check r.status == sxUnknown
    check classified
    check not internalFault

  test "non-regression: a budget wide enough for the SUT's real depth reaches the target":
    ## Raising `maxCallDepth` is the actionable remedy the classified
    ## message names -- confirm it actually resolves the situation: with
    ## room for the full 13-frame recursion the target is found (`sxSat`).
    ## `n` is otherwise unconstrained, so OTHER (irrelevant, larger-`n`)
    ## paths may still exhaust even a generous cap and contribute their own
    ## `beBudgetExhausted` entry alongside the winning witness -- that is
    ## expected (same "riding exnWarnings on whichever branch is taken"
    ## shape as `heDepthExhausted`'s doc comment) and not asserted against
    ## here; what matters is the VERDICT is the real sxSat, never masked by
    ## an unrelated exhausted path, and never misattributed as an internal
    ## fault.
    let r = symexFind(probeBottom, tLabel("bottom12"), roomyDeep)
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == weInternalWalkerFault: internalFault = true
    check r.status == sxSat
    check not internalFault

suite "#161/#163 handoff -- walker version pin":

  test "walker version floor >= 138 (no bump owed by this fix -- error reporting only)":
    check parseInt(symexWalkerVersion) >= 138
