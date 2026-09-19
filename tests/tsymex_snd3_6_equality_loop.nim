## SND-3-6, split out of `tsymex_snd3_loopdegrade.nim` — and SKIP-LISTED.
##
## This is the equality-regression half of RFC-chapulin-hardening SND-3: an
## `s[i] == 'a'` loop guard is NOT an ordering comparison (CR-17(a) guards only
## `<`/`<=`/`>`/`>=`), so the SND-3 degrade must not touch it and the verdict
## must stay a REAL `sxSat`. That is a live, load-bearing pin and it is why
## this file still exists rather than being deleted.
##
## WHY IT IS IN `scripts/sweep.sh`'s skip list
##
## It does not terminate. Diagnosed by measurement in round 10 of the #163
## review, NOT guessed:
##
##   * `VmRSS` holds flat (43228 -> 43612 -> 43740 KB) across 2+ minutes of
##     sustained single-thread CPU. That rules out the obvious hypothesis
##     (unbounded path/frontier growth, which would show 2^k memory growth);
##     a `maxFrontierSize` cap would have nothing to cap here.
##   * `maxLoopUnwind = 1` still hangs, ruling out unbounded loop unrolling.
##   * BOTH the `c` and `cpp` backends hang identically, so this is NOT the
##     backend-divergence class the parent file exists to pin.
##   * `queryRLimit = 1` terminates promptly with `sxUnknown`, proving Z3 IS
##     reached and that rlimit enforcement works — so this is not a Nim-level
##     infinite loop ahead of the solver.
##   * `queryRLimit = 20_000_000` (this repo's own `defaultConcreteBranchRLimit`
##     precedent for hard queries) still fails to conclude. So it is ONE Z3
##     query genuinely grinding through millions of logical steps on the
##     "string-equality loop must run to an exact iteration count" shape.
##
## That evidence is rlimit-based — Z3 logical steps, not wall clock — so it is
## unaffected by host load.
##
## WHY NOT JUST SET A BUDGET HERE
##
## Because any `queryRLimit` tight enough to guarantee termination also forces
## `sxUnknown`, and this test's entire assertion is that the verdict is a real
## `sxSat`. A budget would make the file green by deleting what it pins.
##
## WHY THE PARENT FILE IS **NOT** SKIP-LISTED
##
## Only this SUT hangs. SND-3-1 through SND-3-5 pass in seconds and are live
## pins for a real false-`sxUnsat` soundness fix. Skip-listing the whole parent
## file would have retired those five silently — and a skip-list entry quietly
## covering more than it claims is exactly how the `trequiresinit` defect
## stayed hidden (a stale ledger entry told maintainers to skip-list a real
## bug). Hence the split: one entry, one SUT, one documented reason.
##
## CROSS-REFERENCE, and why this is probably not a defect in THIS source
##
## The byte-identical SUT already exists as a PASSING test — `R1B-while-4`
## (`sutWhileConcreteBound` / "allThreeA") in
## `tests/tsymex_r1b_shortcircuit_oob.nim`, confirmed `[OK]` when run inside
## that file's full suite, while hanging reliably when isolated into a fresh
## single-test binary. That points at Z3 solver runtime variance tied to
## incidental per-process state (term/symbol numbering, warm solver state)
## rather than anything unique to the code here. Whoever picks this up should
## start from that asymmetry: two binaries, same query, different outcomes.
##
## To run it anyway: `scripts/dt-bounded.sh c tests/tsymex_snd3_6_equality_loop.nim`
## invokes it directly and bypasses the sweep's skip list.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# Equality regression — `s[i] == 'a'` in a loop guard is NOT an ordering
# comparison (CR-17(a) only guards `<`/`<=`/`>`/`>=`) and must keep resolving
# to a REAL verdict; the fix must not touch this non-raising path at all.
proc sutEqualityLoopGuard(s: string) =
  var i = 0
  while i < s.len and s[i] == 'a':
    inc i
  if i == 3:
    symexTarget("equality_loop_hit")

suite "symex RFC-chapulin-hardening SND-3 — equality-guard regression (known hanger)":

  test "SND-3-6 (equality regression): s[i]=='a' loop guard still resolves to a real sxSat verdict":
    let r = symexFind(sutEqualityLoopGuard, tLabel("equality_loop_hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3
    check r.witness[0][0] == 'a'
    check r.witness[0][1] == 'a'
    check r.witness[0][2] == 'a'

suite "symex RFC-chapulin-hardening SND-3-6 — version pins":

  test "walker version floor >= 58 (SND-3 introduced at 58)":
    ## Mirrors the parent file's pin. Kept here so the split file carries its
    ## own floor rather than depending on a sibling that no longer contains it.
    check parseInt(symexWalkerVersion) >= 58

  test "renderAsChoicesVersion floor >= 7 (SND-3 does NOT bump RC — no new witness shape)":
    check parseInt(renderAsChoicesVersion) >= 7
