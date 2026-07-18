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
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---- SUT 1: `t &= "x"` (string concat-assign) then compare -----------------
# `&=` is not in the augmented-assign supported set → bare `mkUnsupported`,
# dropping the concatenation. Real Nim: starting from t=="a", "a" & "x" ==
# "ax" would need `t=="a"` — but the WALKER never applies the `&=`, so a
# naively-continued path would compare the STALE `t` against "ax" and find a
# (false) satisfying assignment t=="ax" directly. Post-fix this path is
# tainted `uncertain` and must degrade to sxUnknown, not a false sxSat.
proc concatMutate(t: var string) =
  t &= "x"
  if t == "ax":
    symexTarget("concat")

# ---- SUT 2: `acc /= 2.0` (float div-assign) then compare -------------------
# `/=` is likewise not in {+=, -=, *=} → bare `mkUnsupported`, dropping the
# division. Real Nim needs acc==10.0 for acc/2.0==5.0; a naively-continued
# path would falsely accept acc==5.0 directly (comparing the STALE value).
proc divMutate(acc: var float) =
  acc /= 2.0
  if acc == 5.0:
    symexTarget("div")

# ---- SUT 3: target reached BEFORE the drop, same straight-line path --------
# The target fires (and records its witness) BEFORE the `&=` drop occurs
# further down the same path. Per ADR-0012 D2, `w.found` already holds a
# valid witness at the time of recording — a LATER taint on the same path
# must not retroactively invalidate a witness that was already sound at the
# point of recording... but per SND-1's chokepoint design, `isTargetLabel`
# checks `p.uncertain` AT THE TIME OF THE TARGET, so a target reached before
# any taint is unaffected by a drop that happens strictly afterward.
proc targetBeforeDrop(x: int, t: var string) =
  if x == 5:
    symexTarget("before")
  t &= "unrelated-drop-after-target"

# ---- SUT 4: branch isolation across an `isIf` merge -------------------------
# Only the x==1 branch executes the unsupported `&=` drop; the x==5 branch
# (mutually exclusive) never does. `Path.uncertain` must not leak across the
# `isIf` fork/merge — the x==5 path must remain non-uncertain and still
# produce a valid sxSat.
proc branchIsolation(x: int, t: var string) =
  if x == 1:
    t &= "drop-only-on-this-branch"
  else:
    if x == 5:
      symexTarget("branch_clean")

suite "symex SND-1 — isUnsupported taints Path.uncertain (walker v38)":

  test "SND-1: `t &= \"x\"; if t == \"ax\"` degrades to sxUnknown (no false sxSat)":
    let r = symexFind(concatMutate, tLabel("concat"))
    check r.status == sxUnknown

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
