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

# =============================================================================
# Item 1 -- module-level global read classification
# =============================================================================

var gLimit163rev = 10

proc readsGlobal163(x: int) =
  ## No opaque call anywhere -- purely a global READ. The ONLY way to reach
  ## the target is a witness with `x > gLimit163rev`; the walker cannot
  ## soundly decide this without modelling the global.
  if x > gLimit163rev:
    symexTarget("overLimit")

suite "#161/#163 handoff -- module-level global read names itself, not weInternalWalkerFault":

  test "oracle: gLimit163rev genuinely gates the target's condition in real Nim":
    ## Pairs with the house rule: the global is not incidental -- it really
    ## changes the answer, so declining is necessary, not pessimism.
    check gLimit163rev == 10
    check 11 > gLimit163rev
    check not (5 > gLimit163rev)

  test "a module-level global read degrades to sxUnknown, never a silent wrong verdict":
    let r = symexFind(readsGlobal163, tLabel("overLimit"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown

  test "the global-read decline is classified feGlobalReadUnmodelled, names the global, and is never weInternalWalkerFault":
    let r = symexFind(readsGlobal163, tLabel("overLimit"))
    var classified = false
    var internalFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feGlobalReadUnmodelled and "gLimit163rev" in e.msg:
        classified = true
      if e.kind == weInternalWalkerFault:
        internalFault = true
    check r.status == sxUnknown
    check classified
    check not internalFault

suite "#161/#163 handoff -- walker version pin":

  test "walker version floor >= 138 (no bump owed by this fix -- error reporting only)":
    check parseInt(symexWalkerVersion) >= 138
