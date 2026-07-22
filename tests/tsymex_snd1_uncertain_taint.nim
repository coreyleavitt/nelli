## RFC-chapulin-hardening.md, Cluster 1 (Soundness), SND-1 — "unmodeled statement
## silently mis-mutates → false sxSat" (CRIT).
##
## The `isUnsupported` STATEMENT arm (runtime.nim, `walk`'s top-level `case`)
## used to set `w.sawUnknown = true` and then continue the path with STALE
## `env` (the dropped mutation was never applied). ADR-0012 D2's verdict
## precedence ("first sxSat wins; sawUnknown consulted only when no
## sxSat/sxRaised exists anywhere") would then report a target reached AFTER
## the dropped mutation as a false `sxSat`, with a silently-wrong witness and
## empty `errors` — a silent-wrong-answer soundness bug.
##
## Fix: the `isUnsupported` arm now mirrors the `maxCallDepth`-exceeded bail
## arm in `isCall` — it taints every path in its batch `uncertain = true` (via
## `forkPath`'s 4th positional arg) and CONTINUES the path (taint-and-continue,
## not halt-the-path). The existing `Path.uncertain` chokepoints
## (`isTargetLabel`, `routeRaise`) then demote any sxSat/sxRaised found
## downstream on that same path to `sxUnknown` — so a dropped mutation can
## never surface a silently-wrong witness.
##
## `&=` and `/=` are NOT in the augmented-assign supported set ({+=, -=, *=})
## in `dsl_parser.nim`'s catch-all, so both land as a BARE `mkUnsupported`
## (Class B: no accompanying `sevError` parseError — the vulnerable class per
## the RFC; Class A sites are already immune via `capForcedUnknown`).
##
## Walker version pin: "38" (SND-1 bumped 37→38 — this slice changes verdicts
## sxSat→sxUnknown for programs that drop a mutation via a bare
## `mkUnsupported`, so cached results must rotate out).
##
## UPDATE (Phase 16 M4, RFC-chapulin-hardening): `&=` on a STRING LHS is no
## longer in this unsupported class — M4 added a type-classify branch that
## models it as the in-place concat-assign `s := s & x` (`iekStrConcat`, walker
## v49→50). SUT 1 below (`concatMutate`) is this exact SND-1 Class-B `&=`
## repro; its expectation is updated to the now-CORRECT `sxSat` (M4 closes
## this case). SUTs 3/4 (which use a still-unrelated dropped mutation purely
## to exercise the generic `Path.uncertain` taint-and-continue mechanism
## around a target) are retargeted from `&=` to `/=` (still outside the
## augmented-assign supported set, unaffected by M4) so they keep genuinely
## demonstrating the `isUnsupported` chokepoint rather than an op M4 now
## models correctly. `/=` itself (SUT 2) remains untouched by M4 and continues
## to prove the taint mechanism is intact for ops M4 did not touch.
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---- SUT 1: `t &= "x"` (string concat-assign) then compare -----------------
# This is SND-1's original `&=` Class-B repro. Phase 16 M4 (RFC-chapulin-
# hardening) now MODELS `&=` on a string LHS as the in-place concat-assign
# `t := t & "x"` (`iekStrConcat`) instead of dropping it — so this is no
# longer an unsupported statement at all. Real Nim: starting from `t=="a"`,
# `"a" & "x" == "ax"`, so the ONLY satisfying free value for the symbolic
# parameter `t` is `"a"`. (Pre-SND-1: a naive continued-with-stale-`t` walk
# would falsely accept `t=="ax"` directly. Post-SND-1/pre-M4: this degraded
# to `sxUnknown`. Post-M4: a real, correctly-constrained `sxSat`.)
proc concatMutate(t: var string) =
  t &= "x"
  if t == "ax":
    symexTarget("concat")

# ---- SUT 2: `acc /= 2.0` (float div-assign) then compare -------------------
# `/=` is likewise not in {+=, -=, *=, &=} → bare `mkUnsupported`, dropping the
# division. Real Nim needs acc==10.0 for acc/2.0==5.0; a naively-continued
# path would falsely accept acc==5.0 directly (comparing the STALE value).
# Untouched by M4 — still demonstrates the generic taint-and-continue
# mechanism for an op M4 did not model.
proc divMutate(acc: var float) =
  acc /= 2.0
  if acc == 5.0:
    symexTarget("div")

# ---- SUT 3: target reached BEFORE the drop, same straight-line path --------
# The target fires (and records its witness) BEFORE the drop occurs further
# down the same path. Per ADR-0012 D2, `w.found` already holds a valid
# witness at the time of recording — a LATER taint on the same path must not
# retroactively invalidate a witness that was already sound at the point of
# recording... but per SND-1's chokepoint design, `isTargetLabel` checks
# `p.uncertain` AT THE TIME OF THE TARGET, so a target reached before any
# taint is unaffected by a drop that happens strictly afterward.
# Uses `/=` (not `&=`, per M4 — see file header) to keep genuinely exercising
# a still-unsupported drop.
proc targetBeforeDrop(x: int, acc: var float) =
  if x == 5:
    symexTarget("before")
  acc /= 2.0  # unrelated-drop-after-target

# ---- SUT 4: branch isolation across an `isIf` merge -------------------------
# Only the x==1 branch executes the unsupported `/=` drop; the x==5 branch
# (mutually exclusive) never does. `Path.uncertain` must not leak across the
# `isIf` fork/merge — the x==5 path must remain non-uncertain and still
# produce a valid sxSat.
# Uses `/=` (not `&=`, per M4 — see file header) to keep genuinely exercising
# a still-unsupported drop.
proc branchIsolation(x: int, acc: var float) =
  if x == 1:
    acc /= 2.0  # drop-only-on-this-branch
  else:
    if x == 5:
      symexTarget("branch_clean")

suite "symex SND-1 — isUnsupported taints Path.uncertain (walker v38)":

  test "M4 CLOSES this case: `t &= \"x\"; if t == \"ax\"` now a real sxSat (was sxUnknown pre-M4, false sxSat pre-SND-1)":
    let r = symexFind(concatMutate, tLabel("concat"))
    check r.status == sxSat
    check r.witness[0] == "a"
    check r.witness[0] & "x" == "ax"  ## round-trips against real Nim `&`

  test "SND-1: `acc /= 2.0; if acc == 5.0` degrades to sxUnknown (no false sxSat)":
    let r = symexFind(divMutate, tLabel("div"))
    check r.status == sxUnknown

  test "SND-1 regression: target reached BEFORE the drop still yields a valid sxSat":
    let r = symexFind(targetBeforeDrop, tLabel("before"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "SND-1 regression: a clean sibling branch (isIf merge) stays non-uncertain, still sxSat":
    let r = symexFind(branchIsolation, tLabel("branch_clean"))
    check r.status == sxSat
    check r.witness[0] == 5

  test "walker version floor: symexWalkerVersion >= 38 (SND-1 landed at 38)":
    # Floor-idiom pin (RFC §Version-pin discipline, Corey-decided synthesis):
    # incidental feature-test pins use a `>=` floor so they auto-track future
    # bumps; only the canonical tsymex_phase15_CR2_cachekey.nim keeps the
    # brittle `==` conscious-bump gate.
    check parseInt(symexWalkerVersion) >= 38
