## RFC-chapulin-hardening R14 (CRITICAL soundness fix).
##
## THE BUG (fully root-caused; this suite pins the fix): the R1B-era
## `mkGuardedWhile` do-while rotation (`guardPre; while cond: (body;
## guardPre)`) re-ran a short-circuit while-guard's hoisted preamble as a
## TRAILING statement in the loop body, to keep the guard temp `sc` (and its
## inline `s[i]`/`parseInt` defect fork) fresh every real iteration. But
## `walkBlock` (runtime.nim) stops processing a block's remaining statements
## once a statement returns zero paths — exactly what `continue` does
## (siphons the path into `continuePaths`, returns `@[]`). So a `continue` in
## the loop body SKIPPED the trailing guard-refresh: `sc` went stale, and the
## NEXT guard check ran against OLD loop-variable state — a false verdict.
##
## THE FIX: `mkGuardedWhile` is DELETED, replaced by `mkShortCircuitWhile`
## (`dsl_parser.nim`), which desugars the short-circuit `and` at the LOOP
## level instead of hoisting a guard temp. `while (A and B): body` (B
## carrying the inline defect fork, e.g. `s[i]`) becomes:
##   while A:                 # A is the REAL loop guard
##     <B's preamble>         # B's hoisted stmts (re-run every real pass)
##     if not B: break        # short-circuit exit when B is false
##     body
## B is lowered INSIDE the body, entered only when guard A holds, so B's
## inline fault forks with A already in the path condition — sound "for
## free" by loop semantics. `continue` jumps to the top of `while A`,
## re-evaluating A and re-running B's preamble at the body top — exactly
## Nim's re-evaluation, so it is continue-safe BY CONSTRUCTION (no temp to
## go stale).
##
## A guard that is NOT a clean `and`-split (a plain guard whose parse hoists
## a preamble for any reason, a top-level `or` with a fault, or a fault
## nested inside the `and`'s own LHS) falls back to the PRE-R14 do-while
## rotation (`mkRotatedGuardWhile`) whenever the loop body provably contains
## no `continue` (`hasContinueShallow`) — the rotation is only unsound when a
## `continue` can skip its trailing refresh, so it is safe to keep as a
## fallback once that is ruled out. A bare non-empty guard preamble is NOT
## itself evidence of a short-circuit fault: e.g. `(a div b) > i` semchecks
## to a trivial `nnkStmtListExpr(Empty, ...)` wrapper whose lone `Empty`
## child alone hoists a no-op preamble statement — treating that as
## "must split or degrade" would over-degrade ordinary arithmetic guards to
## `sxUnknown` (a real regression this suite's R14-5/R1-while-3-companion
## design guards against). Only when the body DOES contain a `continue` AND
## no clean and-split is available does this SOUND-DEGRADE to a classified
## `feUnsupportedOp` `sxUnknown`, instead of ever risking a stale-guard false
## verdict (Invariant 3).
##
## See `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
## full writeup (62->63).
##
## Every test in this file is checked on BOTH the `c` and `cpp` backends
## (`scripts/dt-bounded.sh c|cpp`) per project convention.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# Reduced loop-unwind budget for the for-NESTED while case (mirrors
# tsymex_r1b_shortcircuit_oob.nim's `nestedLoopBudget`) — a defect-guarded
# scan nested inside another k-unrolled loop has an inherent path-frontier
# cost; a small unwind keeps the verdict decidable and the test fast.
const nestedLoopBudget = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxLoopUnwind = 3

# ---------------------------------------------------------------------------
# 1. The load-bearing continue repro (RED under the old mkGuardedWhile
#    rotation: gave sxUnknown; GREEN under mkShortCircuitWhile: sxSat).
# ---------------------------------------------------------------------------

proc fCont(s: string) =
  var i = 0
  while i < s.len and s[i] != 'z':
    inc i
    continue
  if i == 3:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# 2. A guard component mutated immediately before `continue`. The `while A:`
#    split's guard (`active and i < s.len`) must be freshly re-evaluated at
#    the top of the NEXT real iteration, not read from a stale pre-mutation
#    snapshot — exactly the shape the old rotation got wrong (the `active =
#    false` mutation immediately precedes the `continue` that used to skip
#    the guard refresh).
# ---------------------------------------------------------------------------

proc fContFlagGuard(s: string) =
  var i = 0
  var active = true
  while active and i < s.len and s[i] != 'z':
    if i >= 2:
      active = false
      continue
    inc i
  if not active:
    symexTarget("stopped")

# ---------------------------------------------------------------------------
# 3. `break` inside a guarded (and-split) while must still exit the loop
#    exactly like real Nim `break` — proves the split doesn't disturb normal
#    break semantics.
# ---------------------------------------------------------------------------

proc fBreakGuard(s: string) =
  var i = 0
  while i < s.len and s[i] != 'z':
    if s[i] == 'y':
      break
    inc i
  if i < s.len and s[i] == 'y':
    symexTarget("brokeOnY")

# ---------------------------------------------------------------------------
# 4. Guarded while NESTED inside a for loop (parseIterBodyStmt's own
#    nnkWhileStmt arm — the SECOND while-arm `mkShortCircuitWhile` call
#    site), with a `continue` in the inner body. Must: (a) never false-raise
#    IndexDefect, (b) still reach a real, satisfiable target, and (c) not
#    hang at a small maxLoopUnwind (the split keeps a real per-level guard,
#    so no path-frontier blowup under nesting).
# ---------------------------------------------------------------------------

proc sutForNestedContinueOob(s: string) =
  var i = 0
  for k in 0 .. 0:
    while i < s.len and s[i] == ' ':
      inc i
      continue
  if i > s.len:
    symexTarget("forNestImpossible")

proc sutForNestedContinueFindX(s: string) =
  var i = 0
  for k in 0 .. 0:
    while i < s.len and s[i] != 'x':
      inc i
      continue
  if i < s.len:
    symexTarget("forNestFoundX")

# ---------------------------------------------------------------------------
# 5. `or`-guard with a fault (`i >= s.len or s[i] == 'x'`) has no
#    structurally-clean loop-level split (the LHS of `or` does not gate loop
#    entry the way `and`'s LHS does). This body has NO `continue`, so the
#    guard's hoisted preamble is safe to re-run via the pre-R14 rotation
#    fallback (`mkRotatedGuardWhile`) — the correct REAL verdict is computed,
#    not a degrade. (A bare non-empty preamble is NOT itself evidence of an
#    unsafe shape — only a `continue` that could skip the refresh is; see
#    `mkShortCircuitWhile`'s doc comment. This is also what keeps
#    `tsymex_r1_draingap.nim`'s `whileDivZero` — a plain, non-and/or guard
#    whose parse hoists an unrelated no-op preamble artifact — correctly
#    `sxRaised` instead of over-degrading to `sxUnknown`.)
# ---------------------------------------------------------------------------

proc sutOrGuardFaultWhile(s: string) =
  var i = 0
  while i >= s.len or s[i] == 'x':
    inc i
  symexTarget("afterOrGuard")

# ---------------------------------------------------------------------------
# 6. The SAME `or`-guard-with-fault shape, but this body DOES contain a
#    `continue` — now the rotation fallback would be unsafe (the exact hazard
#    this fix eliminates), and there is no clean and-split for an `or` guard,
#    so this SOUND-DEGRADES to sxUnknown, never a false verdict.
# ---------------------------------------------------------------------------

proc sutOrGuardFaultContinueWhile(s: string) =
  var i = 0
  while i >= s.len or s[i] == 'x':
    inc i
    continue
  symexTarget("afterOrGuardContinue")

# ---------------------------------------------------------------------------
suite "symex R14 — continue-safety of the and-split short-circuit while guard":

  test "R14-1 (load-bearing): while i<s.len and s[i]!='z': inc i; continue -> i==3 IS sxSat":
    ## RED (pre-fix, old mkGuardedWhile do-while rotation): sxUnknown — the
    ## guard temp `sc` is set once and never refreshed (the `continue`
    ## unconditionally skips the trailing guardPre refresh every single
    ## iteration), so the walker can never form a path where the loop exits
    ## normally after exactly 3 real iterations.
    ## GREEN (post-fix, mkShortCircuitWhile and-split): sxSat — `while i <
    ## s.len` is a REAL guard re-checked fresh after every `continue`.
    let r = symexFind(fCont, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check 'z' notin r.witness[0][0 .. 2]

  test "R14-2: guard-flag mutated immediately before continue is re-evaluated fresh next pass":
    let r = symexFind(fContFlagGuard, tLabel("stopped"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check 'z' notin r.witness[0][0 .. 2]

  test "R14-3: break inside a guarded (and-split) while still exits exactly like real Nim":
    let r = symexFind(fBreakGuard, tLabel("brokeOnY"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check 'y' in r.witness[0]

  test "R14-4a: for-nested guarded while with continue -> IndexDefect NOT reachable":
    let r = symexFind(sutForNestedContinueOob, tRaisedExn("IndexDefect"), nestedLoopBudget)
    check r.status != sxRaised

  test "R14-4b: for-nested guarded while with continue -> \"forNestImpossible\" degrades to sxUnknown, never a false sxRaised":
    let r = symexFind(sutForNestedContinueOob, tLabel("forNestImpossible"), nestedLoopBudget)
    check r.status == sxUnknown

  test "R14-4c (reachable companion): for-nested guarded while with continue still finds a real target":
    let r = symexFind(sutForNestedContinueFindX, tLabel("forNestFoundX"), nestedLoopBudget)
    check r.status == sxSat
    check r.witness[0].len > 0
    check 'x' in r.witness[0]

  test "R14-5: continue-free or-guard with a fault (i>=s.len or s[i]=='x') gets the correct real verdict, not a degrade":
    ## No `continue` in the body -> the rotation fallback is safe -> the
    ## walker computes the actual reachable verdict (real Nim: the loop exits
    ## with 0 iterations whenever s.len>0 and s[0]!='x', e.g. s=="a").
    let r = symexFind(sutOrGuardFaultWhile, tLabel("afterOrGuard"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] != 'x'

  test "R14-6: or-guard with a fault AND a continue sound-degrades to sxUnknown, never a false verdict":
    ## The `continue` makes the rotation fallback unsafe, and there is no
    ## clean and-split for an `or` guard -> sound-degrade (Invariant 3).
    let r = symexFind(sutOrGuardFaultContinueWhile, tLabel("afterOrGuardContinue"))
    check r.status == sxUnknown

suite "symex R14 — version pins":

  test "walker version at least 63 (R14 CRITICAL soundness fix: 62->63)":
    ## `tsymex_phase15_CR2_cachekey.nim`'s "CR-2 sub-test 5" is the SOLE exact
    ## `==` pin on `symexWalkerVersion` by convention; every other file
    ## (including this one) uses a `>=` floor so it auto-tracks future bumps.
    check parseInt(symexWalkerVersion) >= 63

  test "renderAsChoicesVersion stays 7 (no new witness shape, only a verdict-correctness fix)":
    check renderAsChoicesVersion == "7"
