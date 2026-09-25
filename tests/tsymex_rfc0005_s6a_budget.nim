## RFC-0005 (soundness channels) slice S6a -- classify the BUDGET family
## (§5 row S6, first half; §3.1's substitution rule; §3.2's split
## discipline and its "most dangerous row in the RFC" paragraph).
## Walker 143 -> 144.
##
## What the site-by-site audit found (every row is pinned in suite (a)):
##
## `beBudgetExhausted` was ONE kind emitted at SIX walk sites spanning THREE
## substitution classes -- merged deliberately ("a sibling of the SAME budget
## family, so it reuses the kind"), which is exactly what §3.2's standing
## rule forbids once `classOf` reads one word per kind:
##   - `maxLoopUnwind` k-unroll exhaustion, BOTH walk modes (`isWhile`'s
##     `wmExplore` arm and `walkWhileFollowConcrete`): every still-active
##     path is forked onto the post-loop continuation with the guard STILL
##     TRUE on its pc -- a continuation reality never takes there (the
##     survivor is fiction) -- and iterations k+1.. are never walked (the
##     omission is real). `dcFabricated`: ⊤ on the path, `{scIncomplete}`
##     on the run. The majority funnel: it KEEPS `beBudgetExhausted`.
##   - `maxFrontierSize` prune (`walkBlock`): evicted paths are DROPPED, the
##     kept paths are untouched and the token is discarded -- a pure
##     under-approximation. `dcOmitted`: `{}` on the path (inert: no path
##     survives the act) and `{scIncomplete}` on the run. Minority sibling
##     `beBudgetExhaustedPrune`.
##   - `maxCallDepth` bail (`isCall`): the callee is not walked; its result
##     is a FRESH havoc `retSym`, but its var-param writes, heap writes and
##     raises are DROPPED (a stale env) and its actuals are never lowered
##     (their raise forks dropped). `maxVariantConstructorForks` /
##     `maxVariantConstructorFieldAllocs` (`isVariantConstructSym`): the
##     construction is not modelled, the destination is left UNBOUND and
##     the discriminant / plain-field operands are never lowered.
##     `dcSubstituted`: ⊤ on both coordinates. Minority sibling
##     `beBudgetExhaustedUnmodelled`.
## `beBudgetExhaustedAssumedBound` is the `isWhile` k-unroll site's other
## branch (one site, identical survivor shape): `dcFabricated`.
## `ceInlineBudgetExceeded` (two sites in `applyClosureGround`: the budget
## guard and the no-walk-context guard) returns the closure's uninterpreted
## `funcApp` WITHOUT descending the body -- the body's captured-variable
## writes and raises are dropped and `funcApp` is correlated across equal
## arguments where reality need not be: `dcSubstituted`, both sites alike,
## so no split.
##
## The RFC's warning is the reason this file exists: classifying the MERGED
## kind by its prune site (`dcOmitted`) would have given the `maxCallDepth`
## survivors `pathTaint = {}` -- a witness through the havoc `retSym` would
## have reported a clean `sxSat`. Suite (c) pins that it does not.
##
## NO VERDICT CAN FLIP IN THIS SLICE, and that is derived, not observed:
## every class the budget family maps to (`dcFabricated`, `dcSubstituted`,
## `dcOmitted`) carries `scIncomplete` on the run, so none can license
## `sxUnsat` (§2.3 rule 5); every FORKED site's class carries `scSpurious`
## on the path exactly as the ⊤ default did, and the one class with an empty
## path coordinate (`dcOmitted`) is emitted only at a halt whose token is
## discarded. The run coordinate changes from ⊤ to `{scIncomplete}` for the
## fabricated and omitted kinds -- `run.scSpurious` is diagnostics-only
## (§2.1). The payoff is attribution (S11's `gaps()`) and replay
## eligibility (S10: a fabricated/substituted path is ⊤, never eligible).
## The RED is therefore the kind-at-site and class pins, plus the
## must-not-flip guards in suites (b) and (c).
import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import audit_scan_utils

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc sevErrorKinds(errs: seq[SymexErrorInfo]): seq[SymexErrorKind] =
  for e in errs:
    if e.severity == sevError and e.kind notin result: result.add e.kind

const budgetFamily = [beBudgetExhausted, beBudgetExhaustedAssumedBound,
                      beBudgetExhaustedPrune, beBudgetExhaustedUnmodelled,
                      ceInlineBudgetExceeded]

# ---- settings ---------------------------------------------------------------

const depthZero = block:
  var s = defaultSymexSettings()
  s.budget.maxCallDepth = 0        ## exhausts on the very first call, by design
  s

const frontierOne = block:
  var s = defaultSymexSettings()
  s.budget.maxFrontierSize = 1
  s

const inlineOne = block:
  var s = defaultSymexSettings()
  s.budget.maxClosureInlineCount = 1
  s

# ---- SUTs: k-unroll (beBudgetExhausted / beBudgetExhaustedAssumedBound) -----

proc s6aLoopDead(n: int) =
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if n == 5 and n == 6:
    symexTarget("s6a_loop_dead")

proc s6aLoopPastBound(n: int) =
  ## Reachable in reality at n == 7; the k-unroll (default 5) walks at most 5
  ## iterations, so every modelled path has `acc <= 5`: the target lives
  ## ONLY in the omitted iterations.
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if acc == 7:
    symexTarget("s6a_loop_past_bound")

proc s6aLoopFabricated(n: int) =
  ## Reachable in the MODEL only: the fabricated survivor leaves the loop
  ## with `i < n` still on its pc -- a state reality never exits in.
  var i = 0
  while i < n:
    i = i + 1
  if i < n:
    symexTarget("s6a_loop_fabricated")

proc s6aAssumedDead(n: int) =
  symexAssume(n >= 0 and n < 1_000_000)
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if n == 5 and n == 6:
    symexTarget("s6a_assumed_dead")

# ---- SUTs: frontier prune (beBudgetExhaustedPrune) --------------------------

proc s6aPruneDead(x: int) =
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x == 1 and x == 2:
        symexTarget("s6a_prune_dead")

proc s6aPruneOnlyOneArm(x: int) =
  ## Reachable in reality (x <= 0); under a frontier of 1 one arm of the
  ## `if` is evicted, so the target may live only on a DROPPED path.
  var a = 0
  if x > 0:
    a = 1
  else:
    a = 2
  if a == 2:
    symexTarget("s6a_prune_one_arm")

# ---- SUTs: maxCallDepth bail (beBudgetExhaustedUnmodelled) ------------------

proc s6aSetSeven(x: var int) =
  x = 7

proc s6aDepthVarParam(n: int) =
  ## Reachable in reality for EVERY n: the callee writes 7 through the var
  ## param. The bail drops that write (a stale env), so in the model `v`
  ## stays 0 and the target is unreachable -- the substitution that makes
  ## `dcOmitted`/`dcFreshSymbol` unsound here.
  var v = 0
  s6aSetSeven(v)
  if v == 7:
    symexTarget("s6a_depth_varparam")

proc s6aZero(n: int): int =
  result = 0

proc s6aDepthHavocRet(n: int) =
  ## Unreachable in reality (`s6aZero` returns 0); reachable in the model
  ## ONLY through the bail's fresh havoc `retSym`.
  if s6aZero(n) == 12345:
    symexTarget("s6a_depth_havoc_ret")

proc s6aDepthDead(n: int) =
  discard s6aZero(n)
  if n == 5 and n == 6:
    symexTarget("s6a_depth_dead")

# ---- SUTs: variant-constructor budget (beBudgetExhaustedUnmodelled) ---------

type
  S6aTag = enum s6t0, s6t1, s6t2, s6t3, s6t4, s6t5, s6t6, s6t7
  S6aWide = object
    tag: int
    case kind: S6aTag
    of s6t0: a00, a01, a02, a03, a04, a05, a06, a07: int
    of s6t1: a10, a11, a12, a13, a14, a15, a16, a17: int
    of s6t2: a20, a21, a22, a23, a24, a25, a26, a27: int
    of s6t3: a30, a31, a32, a33, a34, a35, a36, a37: int
    of s6t4: a40, a41, a42, a43, a44, a45, a46, a47: int
    of s6t5: a50, a51, a52, a53, a54, a55, a56, a57: int
    of s6t6: a60, a61, a62, a63, a64, a65, a66, a67: int
    of s6t7: a70, a71, a72, a73, a74, a75, a76, a77: int

proc s6aVariantDead(b: byte, n: int) =
  let op = if b == 1'u8: s6t0 else: s6t1
  let p = S6aWide(kind: op, tag: n)
  if n == 5 and n == 6:
    symexTarget("s6a_variant_dead")

proc s6aVariantDroppedOperand(b: byte, a, d: int) =
  ## Reachable in reality (d == 0 raises DivByZeroDefect while evaluating
  ## the plain field). The budget decline fires BEFORE the operands are
  ## lowered, so the raise fork is dropped with the construction.
  let op = if b == 1'u8: s6t0 else: s6t1
  try:
    let p = S6aWide(kind: op, tag: a div d)
  except DivByZeroDefect:
    symexTarget("s6a_variant_dropped_operand")

# ---- SUTs: closure inline budget (ceInlineBudgetExceeded) -------------------

proc s6aInlineDead(x: int) =
  let f = proc(y: int): int = y + 1
  let g = proc(y: int): int = f(y) + 1
  discard g(x)
  if x == 5 and x == 6:
    symexTarget("s6a_inline_dead")

# =============================================================================
# oracles
# =============================================================================

suite "RFC-0005 S6a -- oracles":

  test "oracle: n == 5 and n == 6 is a genuine contradiction":
    for n in [-1, 0, 5, 6, 7]:
      check not (n == 5 and n == 6)

  test "oracle: the past-bound loop target is reachable (n == 7)":
    var i = 0
    var acc = 0
    while i < 7:
      acc = acc + 1
      i = i + 1
    check acc == 7

  test "oracle: a real loop never exits with its guard true":
    for n in [-3, 0, 1, 6, 40]:
      var i = 0
      while i < n: i = i + 1
      check not (i < n)

  test "oracle: the var-param write reaches the caller":
    var v = 0
    s6aSetSeven(v)
    check v == 7

  test "oracle: s6aZero is 0, so 12345 is unreachable":
    for n in [-9, 0, 9]: check s6aZero(n) != 12345

  test "oracle: the variant plain-field operand raises on d == 0":
    var raised = false
    try:
      let p = S6aWide(kind: s6t0, tag: 1 div 0)
      discard p
    except DivByZeroDefect:
      raised = true
    check raised

# =============================================================================
# (a) the classification: one word per kind, each derived from the site
# =============================================================================

suite "RFC-0005 S6a (a) -- the budget family's classOf rows":

  test "beBudgetExhausted (k-unroll survivor) is dcFabricated: ⊤ on the path, {scIncomplete} on the run":
    check classOf(beBudgetExhausted) == dcFabricated
    check channels(beBudgetExhausted) ==
      (path: {scSpurious, scIncomplete}, run: {scIncomplete})

  test "beBudgetExhaustedAssumedBound (the same k-unroll site's other branch) is dcFabricated":
    check classOf(beBudgetExhaustedAssumedBound) == dcFabricated

  test "beBudgetExhaustedPrune (frontier eviction) is dcOmitted: {} on the path, {scIncomplete} on the run":
    check classOf(beBudgetExhaustedPrune) == dcOmitted
    check channels(beBudgetExhaustedPrune) == (path: {}, run: {scIncomplete})

  test "beBudgetExhaustedUnmodelled (maxCallDepth / variant-ctor bail) is dcSubstituted: ⊤ on both":
    check classOf(beBudgetExhaustedUnmodelled) == dcSubstituted
    check channels(beBudgetExhaustedUnmodelled) ==
      (path: {scSpurious, scIncomplete}, run: {scSpurious, scIncomplete})

  test "ceInlineBudgetExceeded (funcApp without descent) is dcSubstituted":
    check classOf(ceInlineBudgetExceeded) == dcSubstituted

  test "NO budget-family kind can license sxUnsat: every class carries scIncomplete on the run":
    for k in budgetFamily:
      checkpoint($k)
      check scIncomplete in runTaint(classOf(k))

  test "every budget kind whose token is FORKED keeps scSpurious on the path (the RFC's warning)":
    ## Only `beBudgetExhaustedPrune` has an empty path coordinate, and its
    ## one site is a halt (pinned structurally in suite (d)).
    for k in budgetFamily:
      checkpoint($k)
      if k != beBudgetExhaustedPrune:
        check scSpurious in pathTaint(classOf(k))

  test "the splits are TAIL appends (ordinal stability, §3.2)":
    ## Ordinal adjacency, not `.high`, so later splits keep the pin.
    check ord(beBudgetExhaustedPrune) == ord(seRuneDecodeSymbolic) + 1
    check ord(beBudgetExhaustedUnmodelled) == ord(beBudgetExhaustedPrune) + 1

  test "checkUnsatOverTaintOnly rejects every budget kind":
    for k in budgetFamily:
      checkpoint($k)
      let r = SymexResult[int](status: sxUnsat,
        errors: @[SymexErrorInfo(kind: k, severity: sevError, msg: "m")])
      expect AssertionDefect:
        checkUnsatOverTaintOnly(r)

# =============================================================================
# (b) each kind at exactly its site, through symexFind; must-not-flip guards
# =============================================================================

suite "RFC-0005 S6a (b) -- each kind at its site, and no sxUnsat through it":

  test "k-unroll exhaustion records beBudgetExhausted; a dead target stays sxUnknown":
    let r = symexFind(s6aLoopDead, tLabel("s6a_loop_dead"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhausted)
    check not r.errors.hasKind(beBudgetExhaustedPrune)
    check not r.errors.hasKind(beBudgetExhaustedUnmodelled)
    check r.status == sxUnknown

  test "k-unroll: a target live only in the omitted iterations is sxUnknown, never sxUnsat":
    let r = symexFind(s6aLoopPastBound, tLabel("s6a_loop_past_bound"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.sevErrorKinds == @[beBudgetExhausted]
    check r.status == sxUnknown

  test "k-unroll: a target live only on the fabricated survivor is sxUnknown, never sxSat":
    let r = symexFind(s6aLoopFabricated, tLabel("s6a_loop_fabricated"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhausted)
    check r.status == sxUnknown

  test "assumed-bound k-unroll records beBudgetExhaustedAssumedBound; dead target stays sxUnknown":
    let r = symexFind(s6aAssumedDead, tLabel("s6a_assumed_dead"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhaustedAssumedBound)
    check not r.errors.hasKind(beBudgetExhausted)
    check r.status == sxUnknown

  test "frontier prune records beBudgetExhaustedPrune (not beBudgetExhausted); dead target stays sxUnknown":
    let r = symexFind(s6aPruneDead, tLabel("s6a_prune_dead"), frontierOne)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhaustedPrune)
    check not r.errors.hasKind(beBudgetExhausted)
    check r.status == sxUnknown

  test "frontier prune: a target that may live only on an evicted path is never sxUnsat":
    let r = symexFind(s6aPruneOnlyOneArm, tLabel("s6a_prune_one_arm"), frontierOne)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.sevErrorKinds == @[beBudgetExhaustedPrune]
    check r.status != sxUnsat

  test "control: the prune SUT without a cap is sxUnsat (the dead target is genuinely dead)":
    let r = symexFind(s6aPruneDead, tLabel("s6a_prune_dead"))
    check r.status == sxUnsat

  test "maxCallDepth bail records beBudgetExhaustedUnmodelled (not beBudgetExhausted); dead target stays sxUnknown":
    let r = symexFind(s6aDepthDead, tLabel("s6a_depth_dead"), depthZero)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
    check not r.errors.hasKind(beBudgetExhausted)
    check r.status == sxUnknown

  test "variant-ctor field budget records beBudgetExhaustedUnmodelled; dead target stays sxUnknown":
    let r = symexFind(s6aVariantDead, tLabel("s6a_variant_dead"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
    check not r.errors.hasKind(beBudgetExhausted)
    check r.status == sxUnknown

  test "closure inline budget records ceInlineBudgetExceeded; dead target stays sxUnknown":
    let r = symexFind(s6aInlineDead, tLabel("s6a_inline_dead"), inlineOne)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.hasKind(ceInlineBudgetExceeded)
    check r.status == sxUnknown

# =============================================================================
# (c) the substitution the split exists for: never a false verdict
# =============================================================================

suite "RFC-0005 S6a (c) -- the maxCallDepth / variant-ctor bail substitutes":

  test "a dropped var-param write: the real target (every n) is never sxUnsat":
    let r = symexFind(s6aDepthVarParam, tLabel("s6a_depth_varparam"), depthZero)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.sevErrorKinds == @[beBudgetExhaustedUnmodelled]
    check r.status != sxUnsat

  test "a witness only through the havoc retSym is a candidate: sxUnknown, never sxSat":
    ## The RFC's warning: under the merged kind classified dcOmitted this
    ## path would carry {} and report a clean sxSat.
    let r = symexFind(s6aDepthHavocRet, tLabel("s6a_depth_havoc_ret"), depthZero)
    checkpoint($r.status & " " & $kindNames(r.errors))
    check r.errors.sevErrorKinds == @[beBudgetExhaustedUnmodelled]
    check r.status == sxUnknown

  test "a dropped variant-ctor operand raise: the real handler is never sxUnsat":
    let r = symexFind(s6aVariantDroppedOperand,
                      tLabel("s6a_variant_dropped_operand"))
    checkpoint($r.status & " " & $kindNames(r.errors))
    ## The parser A-normalises the construction into a temp
    ## (`__sym_<proc>VariantConstruct_N`) and binds `p` from it, so the
    ## decline's UNBOUND destination is always read at once and declines as
    ## `feGlobalReadUnmodelled` (⊤). This site's runs therefore never carry
    ## the budget kind alone; its own class is pinned in suite (a).
    check r.errors.sevErrorKinds ==
      @[beBudgetExhaustedUnmodelled, feGlobalReadUnmodelled]
    check r.status != sxUnsat

# =============================================================================
# (d) structural: the site-audit table, pinned against the source
# =============================================================================

const rtSrc = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
              "smt" / "runtime.nim"

proc degradeSites(src: string; k: SymexErrorKind): seq[string] =
  ## Every non-comment line of `src` that calls `degrade(<k>,` or (RFC-0005
  ## S7) `closureDegrade(<k>,` -- the two funnels are the only emission
  ## paths for these kinds.
  for raw in src.splitLines():
    let t = raw.strip()
    if t.len == 0 or isCommentLine(t): continue
    if ("degrade(" & $k & ",") in t or ("closureDegrade(" & $k & ",") in t:
      result.add t

suite "RFC-0005 S6a (d) -- structural: the audited emission sites":

  test "site counts per kind match the S6a audit (a new site must re-audit its class)":
    ## STANDING RULE (§3.2): reusing a kind at a new site asserts its class.
    ## This pin makes that assertion a reviewed edit instead of a silent one.
    let src = readFile(rtSrc)
    for (k, n) in [(beBudgetExhausted, 2),            # k-unroll, both modes
                   (beBudgetExhaustedAssumedBound, 1),
                   (beBudgetExhaustedPrune, 1),        # walkBlock
                   (beBudgetExhaustedUnmodelled, 3),   # maxCallDepth + 2 vcs
                   # budget guard + no-walk guard (both `closureDegrade`
                   # since RFC-0005 S7; the no-walk guard was a hand-written
                   # sink add before) + S1 probe
                   (ceInlineBudgetExceeded, 3)]:
      let sites = degradeSites(src, k)
      checkpoint($k & ": " & $sites)
      check sites.len == n

  test "every dcOmitted kind's degrade is a HALT: its token is discarded, never forked":
    ## `pathTaint(dcOmitted) == {}` is sound only where no path survives the
    ## act. A dcOmitted token handed to `forkPathTainted`/`taintInPlace`
    ## would launder the omission into a clean survivor.
    let src = readFile(rtSrc)
    var omitted = 0
    for k in SymexErrorKind:
      if classOf(k) != dcOmitted: continue
      for t in degradeSites(src, k):
        inc omitted
        checkpoint($k & ": " & t)
        check t.startsWith("discard w.degrade(")
    check omitted >= 1

suite "RFC-0005 S6a -- walker version pin":

  test "walker version floor >= 144 (S6a classifies the budget family)":
    check parseInt(symexWalkerVersion) >= 144
