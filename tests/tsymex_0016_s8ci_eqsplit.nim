## RFC-0016 S8ci (PRC-31). Z3 spends wall time its step counter does not
## see: with `smt.arith.propagate_eqs` on (Z3's default), every LP bound
## propagation runs `lp_bound_propagator::cheap_eq_on_nbase` over the
## touched rows and explains each equality it finds by walking its row
## (`lar_solver::explain_fixed_in_row`); none of that advances `rlimit`.
## Stack-sampled on a RelWithDebInfo build of Z3 5.1.0, `r4_strip`'s
## budget-out step 3 spent 228 of 300 samples there, and how much depends
## on the order the query's terms were made in.
##
## `ownContextCheck` splits each own-context search's bound: Z3's defaults
## under the first share (`eqsSplitShare`, seven eighths), and only a
## search that share ran out on goes on, on the same solver, without the
## equality search, under what is left. Pinned here through `symexFind`: a
## query decided within its first share never reaches the rest; a
## budget-bounded walk does, and spends the same units as one search under
## the whole bound would (both parts are counted).
##
## Decided by S8ci's pre-registered rule over 54 (suite, Z3) cells:
## 1,468.7M Z3 units against 1,527.2M without the split, no cell worse by
## more than 25% and 1M, `r4_strip` 77.9 s / 62.9 s against S8bm's 113.0 s /
## 88.4 s side by side (eos, Z3 5.1). Turning the search off everywhere
## (1,562.5M; `s8bb_replace_d` 3.8M to 26.5M and red) and the reverse split
## (off first: 1,504.8M, the same three cells past the gate) were rejected.
##
## The share (walker 389): at one half, two pinned UNSATs that Z3's
## defaults decide only past half the bound were lost
## (`tsymex_rfc0005_s8aq_remainder`'s `s8aq_rfind_before_piece`,
## `tsymex_rfc0005_s8cn_step1d`'s `grow_stale_dead`); at three quarters the
## first still was; at seven eighths both hold. See PRC-31's note for the
## seven-eighths measurements.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/runtime
import nelli/smt/canonicalize
import nelli/smt/types
import nelli/smt/admission
import ./s8cu_helpers

proc chainStrip(s: string) =
  if s.strip().endsWith("x"):
    symexTarget("s8ci_chain_strip")

proc lengthsTied(s, t: string) =
  if s.len == 5 and t.len == s.len + 2 and (s & t).len == 12:
    symexTarget("s8ci_lengths_tied")

proc stripIdempotent(s: string) =
  ## `r4_strip`'s budget-out SUT, under a small bound.
  let t = s.strip()
  let u = t.strip()
  if t != u:
    symexTarget("s8ci_strip_nonidem")

const smallBound = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(queryRLimit: 2_000_000'u, maxFrontierSize: 0,
                         maxCallDepth: 3, maxLoopUnwind: 5))

template splits(body: untyped): int =
  let before = symexEqsSplits
  body
  symexEqsSplits - before

suite "S8ci: Z3's defaults get the first share of a search's bound":

  test "a query decided within its first share is never split":
    let n = splits:
      check symexFind(chainStrip, tLabel("s8ci_chain_strip")).status == sxSat
      # The K9 record: the tied-lengths query is decided exactly (its witness
      # hits natively) through the split's first share.
      check pinExact(lengthsTied, cellKey(axMagic, "LengthStr"),
                     tLabel("s8ci_lengths_tied"),
                     domain = sampled(["", "ab"])).status == sxSat
    echo "s8ci_eqsplit: decided-early splits=", n
    check n == 0

  test "a search that runs out of its first share goes on without the equality search":
    let unitsBefore = ownContextUnits
    let n = splits:
      let r = symexFind(stripIdempotent, tLabel("s8ci_strip_nonidem"),
                        smallBound)
      check r.status in {sxUnsat, sxUnknown, sxRaised}
    let spent = ownContextUnits - unitsBefore
    echo "s8ci_eqsplit: stripIdempotent splits=", n, " units=", spent
    check n > 0
    # Both parts are counted: every split search spent past its first share.
    check spent >= n * 1_000_000

suite "S8ci: walker version pin":
  test "walker version floor >= 389":
    check parseInt(symexWalkerVersion) >= 389
