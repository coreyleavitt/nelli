## RFC-chapulin-hardening R1 (CRITICAL soundness fix).
##
## `lowerInExpr`/`lowerBoolInExpr` RESET the scalar-raise-fork sinks
## (`strIndexOobConds`/`parseIntRaiseConds`/`divByZeroConds`/`overflowConds`)
## at their own entry. Any statement arm that lowers an expression through one
## of those procs but never calls `drainScalarRaiseForks` afterward silently
## DISCARDS whatever raise predicate that expression deposited (e.g. `s[i]`
## OOB, `x div 0`): the defect fork never happens, so a target reachable only
## PAST a real `IndexDefect`/`DivByZeroDefect` is falsely reported `sxSat`
## with an unsound (impossible-in-real-Nim) witness — an Invariant-3
## soundness violation.
##
## FIVE statement arms had this gap: `isWhile` (the loop guard), `isIndex`
## (both the dynamic seq[T] index expr and the static array index expr),
## `isVariantReassignSymbolic` (the symbolic-RHS disc expr), and `isReturn`
## (the return-value expr). The fix drains `drainScalarRaiseForks` right
## after each site's `lowerInExpr`/`lowerBoolInExpr` call and threads the
## returned survivor(s) forward — mirroring the already-correct `isLet`/
## `isAssign`/`isIf` arms exactly.
##
## This suite pins the two arms called out as mandatory by the fix (isWhile,
## isReturn) against BOTH scalar-raise families (string-index OOB — SND-4's
## sink — and div-by-zero — R16-3's sink), plus lighter-weight coverage of
## the other three arms (isIndex/seq, isIndex/array, isVariantReassignSymbolic)
## to confirm the same pattern lands correctly at every site touched.
##
## Bumps `symexWalkerVersion` 60->61 (verdict-surface change: these five arms
## now correctly fork raises / narrow bounds that were previously silently
## dropped — a soundness correction, not a new witness shape).
## `renderAsChoicesVersion` STAYS "7".

import std/[unittest, strutils]
import proptest/symex

# ---------------------------------------------------------------------------
# isWhile — loop guard lowering
# ---------------------------------------------------------------------------

proc whileStrOob(s: string) =
  ## The guard `s[i] == chr(255)` deposits an IndexDefect OOB predicate on
  ## every evaluation (i starts at 0). Real Nim: for s == "" this raises
  ## IndexDefect immediately at the first guard check.
  var i = 0
  while s[i] == chr(255):
    inc i
  symexTarget("after")

proc whileStrGuardedInBounds(s: string) =
  ## Precision companion: `i < 3` short-circuits before `s[i]` is ever
  ## evaluated OOB (guarded by the outer `s.len > 3`), so a genuinely
  ## in-bounds target reached through the loop must still be sxSat with a
  ## valid witness — proves the drain's bounds-narrowing does not
  ## over-degrade legitimate in-bounds continuations.
  if s.len > 3:
    var i = 0
    while i < 3 and s[i] != 'x':
      inc i
    if i < 3:
      symexTarget("foundX")

proc whileDivZero(a, b: int) =
  ## `a div b` in the loop guard deposits a div-by-zero predicate on every
  ## evaluation. Real Nim: b == 0 raises DivByZeroDefect at the first guard
  ## check. Proves the fix covers the pre-existing R16-3 scalar sink too,
  ## not just SND-4's string-index sink.
  var i = 0
  while (a div b) > i:
    inc i
  symexTarget("afterDiv")

suite "symex R1 — isWhile guard drains scalar-raise forks":

  test "R1-while-1: s[i]==chr(255) guard on unconstrained s -> sxRaised(IndexDefect)":
    ## RED (pre-fix): sxUnsat — the OOB predicate from lowering the guard is
    ## discarded every iteration; no raise fork is ever opened.
    ## GREEN (post-fix): sxRaised(IndexDefect) — e.g. witness s == "".
    let r = symexFind(whileStrOob, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"

  test "R1-while-2 (precision companion): in-bounds loop target stays real sxSat":
    let r = symexFind(whileStrGuardedInBounds, tLabel("foundX"))
    check r.status == sxSat
    check r.witness[0].len > 3

  test "R1-while-3: (a div b) > i guard on unconstrained b -> sxRaised(DivByZeroDefect)":
    ## RED (pre-fix): sxUnsat — same drain gap, div-by-zero family.
    ## GREEN (post-fix): sxRaised(DivByZeroDefect).
    let r = symexFind(whileDivZero, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# isReturn — return-value expr lowering (needs a non-empty callStack, so the
# raise-bearing read must happen inside a helper the SUT calls).
# ---------------------------------------------------------------------------

proc helperAt(s: string, i: int): char =
  return s[i]

proc retOobUnreachable(s: string, i: int) =
  ## The guard forces `i` OUT of bounds unconditionally, so `helperAt`'s
  ## `return s[i]` ALWAYS raises IndexDefect in real Nim — the `if c ==
  ## chr(255)` line can never be reached. Pre-fix, `isReturn` never drains
  ## the OOB predicate deposited by `return s[i]`, so `c` is bound to the
  ## OOB-degrade value (always chr(255)) UNCONDITIONALLY on this guard,
  ## making "hitOob" trivially, falsely sxSat.
  if i < 0 or i >= s.len:
    let c = helperAt(s, i)
    if c == chr(255):
      symexTarget("hitOob")

proc retInBoundsReachable(s: string, i: int) =
  ## Companion: `i` forced IN bounds — a real, reachable target requiring the
  ## actual character at a real position to equal chr(255). Proves the drain's
  ## `not oob` narrowing does not corrupt the survivor's real value semantics.
  if i >= 0 and i < s.len:
    let c = helperAt(s, i)
    if c == chr(255):
      symexTarget("hitInBounds")

suite "symex R1 — isReturn retExpr drains scalar-raise forks":

  test "R1-return-1: return s[i] with i forced OOB -> \"hitOob\" is NOT a false sxSat":
    ## RED (pre-fix): sxSat with a witness where i is OOB — a FALSE positive,
    ## since real Nim raises IndexDefect inside helperAt before `if c == ...`
    ## is ever reached.
    ## GREEN (post-fix): NOT sxSat — the OOB path is routed to a raise instead
    ## of ever reaching "hitOob". Per Phase 15 E6, a reachable Defect raise
    ## always dominates and surfaces as the overall verdict regardless of the
    ## search target, so the concrete post-fix status is `sxRaised` (not
    ## `sxUnsat`) — confirmed directly via `tRaisedExn` in R1-return-1b below.
    ## The soundness-relevant assertion here is simply that "hitOob" is never
    ## reported reachable.
    let r = symexFind(retOobUnreachable, tLabel("hitOob"))
    check r.status != sxSat

  test "R1-return-1b: return s[i] with i forced OOB -> sxRaised(IndexDefect)":
    let r = symexFind(retOobUnreachable, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"

  test "R1-return-2 (in-bounds companion): real sxSat with a valid in-bounds witness":
    let r = symexFind(retInBoundsReachable, tLabel("hitInBounds"))
    check r.status == sxSat
    check r.witness[1] >= 0
    check r.witness[1] < r.witness[0].len
    check r.witness[0][r.witness[1]] == chr(255)

# ---------------------------------------------------------------------------
# isIndex — dynamic seq[T] index expr
# ---------------------------------------------------------------------------

proc seqIdxDivZero(xs: seq[int], b: int) =
  ## `xs.len > 0` pins the index (`0 div b`, always 0 whenever b != 0) to a
  ## PROVABLY in-bounds position independent of b, so `IndexDefect` is never
  ## reachable here and cannot masquerade as the raise this test is
  ## isolating — the only reachable defect is DivByZeroDefect from `0 div b`
  ## when b == 0. (Both IndexDefect and DivByZeroDefect are Nim `Defect`
  ## subtypes and per Phase 15 E6 ALWAYS surface as `sxRaised` regardless of
  ## a `tRaisedExn` search's type filter — so an unconstrained index would
  ## let a coincidental IndexDefect dominate and mask the very drain gap
  ## this test targets.)
  if xs.len > 0:
    let v = xs[0 div b]
    discard v
    symexTarget("afterSeqIdx")

suite "symex R1 — isIndex (dynamic seq) drains scalar-raise forks":

  test "R1-seqidx-1: xs[0 div b] with unconstrained b, xs.len>0 -> sxRaised(DivByZeroDefect)":
    ## RED (pre-fix): sxUnsat (no raise ever forked; the div-by-zero
    ## predicate deposited by `stmt.ixIdx`'s lowering is silently discarded).
    ## GREEN (post-fix): sxRaised(DivByZeroDefect).
    let r = symexFind(seqIdxDivZero, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# isIndex — static array index expr
# ---------------------------------------------------------------------------

proc arrIdxDivZero(xs: array[5, int], b: int) =
  ## `array[5, int]` has a STATIC size, so `0 div b` (always 0 whenever
  ## b != 0) is unconditionally in-bounds — same IndexDefect-isolation
  ## rationale as `seqIdxDivZero` above, without needing a length guard.
  let v = xs[0 div b]
  discard v
  symexTarget("afterArrIdx")

suite "symex R1 — isIndex (static array) drains scalar-raise forks":

  test "R1-arridx-1: xs[0 div b] with unconstrained b -> sxRaised(DivByZeroDefect)":
    ## RED (pre-fix): sxUnsat. GREEN (post-fix): sxRaised(DivByZeroDefect).
    let r = symexFind(arrIdxDivZero, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

# ---------------------------------------------------------------------------
# isVariantReassignSymbolic — symbolic-RHS disc expr
# ---------------------------------------------------------------------------

type
  R1K = enum r1kA, r1kB, r1kC
  R1Box = object
    case kind: R1K
    of r1kA: fa: int
    of r1kB: fb: int
    of r1kC: fc: int

proc reassignDivZero(box: var R1Box, a, b: int) =
  box.kind = R1K(a div b)
  if box.kind == r1kB:
    symexTarget("vrsHitDiv")

suite "symex R1 — isVariantReassignSymbolic drains scalar-raise forks":

  test "R1-vrs-1: box.kind = K(a div b) with unconstrained b -> sxRaised(DivByZeroDefect)":
    ## RED (pre-fix): sxUnsat. GREEN (post-fix): sxRaised.
    let r = symexFind(reassignDivZero, tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "DivByZeroDefect"

suite "symex R1 — version pins":

  test "walker version floor >= 61 (R1 introduced at 61)":
    check parseInt(symexWalkerVersion) >= 61

  test "renderAsChoicesVersion floor >= 7 (R1 does NOT bump RC — raises, not a new witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
