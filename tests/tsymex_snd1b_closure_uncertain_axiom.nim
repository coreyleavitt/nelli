## RFC-chapulin-hardening.md, Cluster 1 (Soundness), SND-1b — "closure body
## drops uncertain axioms → whole-run degrade" (CRIT).
##
## SND-1 taints every path `uncertain = true` when it crosses an unmodeled
## `isUnsupported` statement (or a `maxCallDepth` bail), and the existing
## `Path.uncertain` chokepoints (`isTargetLabel`, `routeRaise`) demote a
## downstream sxSat/sxRaised reached on that SAME path to sxUnknown. But the
## closure ground-axiom path (`applyClosureGround`) is a SEPARATE,
## parallel verdict-influencing mechanism: it descends a closure body ONCE via
## a raw (non-`forkPath`) `Path(...)` and folds the body's returned sub-paths
## into GROUND Z3 axioms pushed into the GLOBAL `currentClosureCallAxioms`
## threadvar — drained into EVERY subsequent `trySolve` for the rest of the
## run. `assertArm` (the axiom emitter) never consulted `cp.uncertain`, so a
## closure body that dropped a mutation (or bailed on `maxCallDepth`) still had
## its possibly-wrong return value asserted as an UNCONDITIONAL, PERMANENT
## fact — SND-1's own repro shape placed INSIDE a closure body still yielded a
## false sxSat.
##
## Fix (mirrors the call-cache's existing `not
## frame.returnedPaths[0].uncertain` gate, ~runtime.nim:5850):
## `applyClosureGround` now SKIPS `assertArm` for any returned sub-path whose
## `cp.uncertain` is true, and pushes a NEW `ceClosureBodyUncertain` error into
## `closureCallErrorsLive` so the EXISTING whole-run `closureForcedUnknown`
## degrade (already fed by `ceClosureUnknownCallee`/`ceInlineBudgetExceeded`)
## fires. Coarse (whole-run, not per-occurrence — there is no live `Path` at
## the `lower()` call site to taint per-occurrence, the same reason SND-1 uses
## chokepoints instead of threading a Path there) but sound.
##
## Walker version pin: "39" (SND-1b bumped 38→39 — this slice changes verdicts
## sxSat→sxUnknown for closure applications whose body drops a mutation or
## bails on maxCallDepth, so cached results must rotate out).
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/canonicalize

# ---- SUT 1: SND-1's `&=` repro, wrapped INSIDE a closure body --------------
# `f` is a closure taking the free string parameter `t`; its body copies `t`
# into `r`, then does `r &= "x"` — `&=` is not in the augmented-assign
# supported set, so this is a bare `mkUnsupported` (Class B), which taints the
# closure's OWN descent path `uncertain = true` (SND-1) and continues with `r`
# UNMODIFIED (the mutation is silently dropped). The closure returns an `int`
# flag from comparing `r` against "ax" (a `string`-typed closure RETURN hits
# an unrelated, pre-existing `symValFromRawAst` gap — `itString` is not a
# supported ground closure-return kind — so the flag keeps this test isolated
# to the SND-1b mechanism). Pre-fix: `applyClosureGround` asserted BOTH ground
# axiom arms (`implies(r=="ax", funcApp==1)`, `implies(not r=="ax",
# funcApp==0)`) unconditionally, so `f(t) == 1` reduced to the STALE
# comparison `t == "ax"` — directly satisfiable by choosing t=="ax" as the
# input, a false sxSat with a silently-wrong witness (real Nim needs
# `t == "a"` for `t & "x" == "ax"`). Post-fix: both uncertain sub-paths are
# dropped from axiomatization and `ceClosureBodyUncertain` forces the whole
# run to `sxUnknown`.
proc closureConcatMutate(t: var string) =
  let f = proc(s: string): int =
    var r = s
    r &= "x"
    if r == "ax":
      return 1
    return 0
  if f(t) == 1:
    symexTarget("closure_concat")

# ---- SUT 2: a closure body whose internal call bails on maxCallDepth -------
# `alwaysRecurse` has NO base case — every call recurses unconditionally, so
# ANY call to it, at ANY depth, eventually hits `maxCallDepth` and bails,
# tainting that path `uncertain = true` with a fresh UNCONSTRAINED retSym
# (Phase 3 mechanism). The closure `f` just forwards to `alwaysRecurse`, so
# its own (single, unconditional) returned sub-path is uncertain too. Pre-fix:
# `applyClosureGround` asserted `funcApp == <fresh unconstrained sym>`
# unconditionally — a tautological equality between two free values that
# leaves `funcApp` itself completely unconstrained, so Z3 can freely pick
# `funcApp == 999999` to satisfy the target regardless of `x` (false sxSat,
# an arbitrary/meaningless witness). Post-fix: the arm is dropped and
# `ceClosureBodyUncertain` forces `sxUnknown`.
proc alwaysRecurse(n: int): int =
  return alwaysRecurse(n) + 1

proc closureDepthBail(x: int) =
  let f = proc(n: int): int = alwaysRecurse(n)
  if f(x) == 999999:
    symexTarget("closure_depth")

# ---- SUT 3 (regression): a FULLY MODELED (clean) closure application -------
# No unmodeled statement, no depth bail — every returned sub-path is certain.
# The fix must NOT over-degrade this: it should still axiomatize normally and
# yield a valid sxSat with the correct witness.
proc closureCleanCapture(x: int) =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  if f(3) == 13:
    symexTarget("closure_clean")

suite "symex SND-1b — closure ground-axiom path drops uncertain sub-paths (walker v39)":

  test "SND-1b: `&=` dropped INSIDE a closure body degrades to sxUnknown (no false sxSat)":
    let r = symexFind(closureConcatMutate, tLabel("closure_concat"))
    check r.status == sxUnknown
    var sawBodyUncertain = false
    for e in r.errors:
      if e.kind == ceClosureBodyUncertain: sawBodyUncertain = true
    check sawBodyUncertain

  test "SND-1b: closure body's internal call bails on maxCallDepth degrades to sxUnknown":
    let r = symexFind(closureDepthBail, tLabel("closure_depth"))
    check r.status == sxUnknown
    var sawBodyUncertain = false
    for e in r.errors:
      if e.kind == ceClosureBodyUncertain: sawBodyUncertain = true
    check sawBodyUncertain

  test "SND-1b regression: a clean (fully-modeled) closure application still yields valid sxSat":
    let r = symexFind(closureCleanCapture, tLabel("closure_clean"))
    check r.status == sxSat
    check r.witness[0] == 5    ## x : 3 + x*2 == 13 ⇒ x == 5

  test "walker version floor: symexWalkerVersion >= 39 (SND-1b landed at 39)":
    # Floor-idiom pin (RFC §Version-pin discipline, Corey-decided synthesis):
    # incidental feature-test pins use a `>=` floor so they auto-track future
    # bumps; only the canonical tsymex_phase15_CR2_cachekey.nim keeps the
    # brittle `==` conscious-bump gate.
    check parseInt(symexWalkerVersion) >= 39
