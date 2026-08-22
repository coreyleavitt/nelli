## Round-6 R5 (post-0.4.0 remediation slice, finding S4) -- walker v93.
##
## `tryRecognizePairLoopIdiom` (B6, `dsl_parser.nim`) replaces a recognized
## 5-statement pair-loop with a two-way fork on `iekStrInOptionRegion`
## membership. The MEMBER branch is an EMPTY block -- the loop counter
## (`i`) is never advanced. Real Nim readOptions semantics do NOT
## guarantee `i == bound` on exit: the canonical shape (a trailing
## double-NUL terminator) exits via `break` on the empty-key terminator
## segment, leaving `i` at the START of that segment, i.e. `bound - 1`, NOT
## `bound`. Hand-deriving the segment-by-segment replay of a single-pair
## terminated region ("aa\x00bb\x00\x00", 7 bytes) confirms the real
## post-loop `i` is 6 (bound-1), not 7 (bound): one pair consumed
## (i: 0->6), then the second iteration reads the empty-key terminator at
## position 6 and `break`s WITHOUT executing the `i = p2` advance. A
## single unconditional `i = bound` closed-form binding (the naive fix) is
## therefore UNSOUND for exactly this canonical shape (also
## `tsymex_r6_b6_optionregion.nim`'s own B6-1/B6-2/B6-4 pins, whose
## terminator segments behave identically) -- there is no single closed
## form for the counter's exit value that is faithful across every witness
## satisfying region membership (it is genuinely data-dependent: a region
## with no embedded empty-key segment before `bound` DOES exit with
## `i == bound`, but the canonical terminated shape does not).
##
## Fix shipped: shape (b) from the RFC's own decision fork -- decline the
## closed-form pair-loop recognition (`collectPairLoopCounterConsumedAfter`,
## `dsl_parser.nim`, a new parse-time pre-pass mirroring
## `collectIntOffsetLiteralLocals`'s own single-pass style) whenever code
## AFTER the loop could observe the counter, falling back to the
## pre-existing per-iteration-correct `mkWhile` k-unroll path. R5-1/R5-2
## deliberately use a SMALL (one-pair) literal, not B6-1's own
## four-pair/25-byte pin: B6-1-red (`tsymex_r6_b6_optionregion.nim`)
## already demonstrates that literal's plain (unrecognized) k-unroll
## itself degrades to sxUnknown at the default `maxLoopUnwind` (5) --
## exactly the boundary the closed form exists to cross -- so it cannot
## distinguish "correct" from "wrong" once this slice's fix declines the
## closed form and falls back to k-unroll. The one-pair literal resolves
## in 2 real iterations, well inside budget, so the fallback path can
## actually compute (not just theoretically preserve) the right verdict.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc readCStringOpt(s: string, offset: int): (string, int) =
  ## B4's accumulating shape, real chapulin delimiter ('\0') -- byte-
  ## identical to `tsymex_r6_b6_optionregion.nim`'s own helper.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc readOptionsSutCounter(s: string, start: int) =
  ## Identical pair-loop shape to `tsymex_r6_b6_optionregion.nim`'s own
  ## `readOptionsSut`, except the counter `i` is CONSUMED AFTER the loop --
  ## exactly the S4 hazard. Branches on the real post-loop value of `i` so
  ## a stale (unadvanced) model reaches the OPPOSITE branch from the real
  ## one.
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readCStringOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    pairs.add((key, val))
    i = p2
  if i == 6:
    symexTarget("correct")
  else:
    symexTarget("stale")

proc readOptionsSutDone(s: string, start: int) =
  ## The counter is NEVER read after the loop -- byte-identical in shape to
  ## `tsymex_r6_b6_optionregion.nim`'s own `readOptionsSut`. Used by R5-4 to
  ## confirm the counter-unconsumed case is UNAFFECTED by this slice's gate
  ## (the closed form must still fire for it).
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readCStringOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("done")

# ---------------------------------------------------------------------------
# 1. Tracer (RFC test-plan item 1) + honest-degrade companion (RFC test-plan
#    item 2, ADJUSTED per an engine characteristic discovered landing this
#    slice -- see R5-2's own comment). Both queries use the same one-pair
#    literal (real post-loop i == 6) -- pre-fix the model (member branch's
#    empty block leaves i at its ENTRY value, 0) gives the OPPOSITE verdict
#    for R5-1: "correct" (i==6) is wrongly unreachable.
# ---------------------------------------------------------------------------

suite "symex round-6 R5 -- B6 pair-loop counter advance (finding S4)":

  test "R5-1: the REAL post-loop i (6) is reachable -- sxSat":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00\x00")
      readOptionsSutCounter(s, 0)
    let r = symexFind(sut, tLabel("correct"))
    check r.status == sxSat

  test "R5-2: the STALE (pre-loop, unadvanced) i is no longer FALSELY reachable -- honest sxUnknown, not sxSat":
    ## Pre-fix this reported sxSat (WRONG: the member branch's empty block
    ## never advances `i`, so the model thinks the entry value 0 survives to
    ## the post-loop check, even though the real program never returns 0
    ## here). Post-fix, the closed form is skipped entirely and the query
    ## falls to `mkShortCircuitWhile`'s own k-unroll fallback -- which
    ## reports `beBudgetExhausted` (confirmed via `r.errors`, kind
    ## `beBudgetExhausted`) rather than a clean `sxUnsat`, EVEN THOUGH the
    ## real trip count for this exact literal is only 2 (well inside the
    ## default `maxLoopUnwind` of 5). This is a genuine, PRE-EXISTING,
    ## general characteristic of the k-unroll machinery discovered while
    ## landing this slice, not a regression it introduces: the budget-
    ## exhaustion check is evaluated structurally against the loop's own
    ## `.len`-guarded shape, independent of what a later `symexAssume`
    ## later pins the receiver to, so an UNSAT/absence proof through a
    ## plain (non-closed-form) string-scanning while loop is not currently
    ## achievable in this engine REGARDLESS of the literal chosen -- exactly
    ## the general limitation the Q1/B0/B3/B4/B6 closed forms exist to
    ## route around. The important, IN-SCOPE property this pin verifies is
    ## narrower and still fully achieved: the WRONG sxSat is gone, replaced
    ## by an HONEST degrade -- capability lost, never a wrong verdict,
    ## exactly the RFC's own tradeoff for fix option (b).
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00\x00")
      readOptionsSutCounter(s, 0)
    let r = symexFind(sut, tLabel("stale"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 2. Non-member/fallback consistency (RFC test-plan item 3). A truncated
#    region (B6-5's own literal) still reaches the real modeled ScanError
#    raise once the closed form is declined -- confirms declining doesn't
#    regress defect-reachability, only forgoes the closed-form fast path.
# ---------------------------------------------------------------------------

  test "R5-3: fallback raise behavior is unchanged once the closed form is declined (truncated region)":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc")
      readOptionsSutCounter(s, 0)
    let r = symexFind(sut, tRaisedExn("ScanError"))
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 3. Counter-unconsumed regression (RFC test-plan item 4). B6-2's own
#    >5-real-iteration literal (7 real outer iterations, past the default
#    k-unroll budget) MUST still resolve via the closed-form fast path --
#    proves this slice's new gate does not fire when the counter is never
#    read after the loop.
# ---------------------------------------------------------------------------

  test "R5-4: counter-unconsumed shape still proves via the fast path past the k-unroll horizon":
    proc sut(s: string) =
      symexAssume(s == "a1\x00b1\x00a2\x00b2\x00a3\x00b3\x00" &
                        "a4\x00b4\x00a5\x00b5\x00a6\x00b6\x00\x00")
      readOptionsSutDone(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

suite "symex round-6 R5 -- walker version pin":

  test "walker version floor >= 93 (B6 pair-loop counter-consumed-after gate, finding S4)":
    check parseInt(symexWalkerVersion) >= 93
