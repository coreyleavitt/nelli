import std/unittest
import std/sequtils
import proptest/symex

# Phase 15 CR-9 Stage 1 — lowerInExpr / lowerBoolInExpr wrapper compile+green gate.
#
# This test file exists to confirm:
#   (a) the two new wrappers (lowerInExpr, lowerBoolInExpr) compile without error;
#   (b) the engine still produces correct verdicts after the wrappers are added
#       (no call site has been migrated yet — this is a PURE ADDITION gate);
#   (c) the drain path that the wrappers encapsulate continues to work correctly
#       via the existing call sites (isLet / isDerefWrite / isAssert / isWhile).
#
# SUTs deliberately exercise the two scenarios the wrappers are designed to
# encapsulate:
#   S1: float→int in a let-binding expression (deposits convFloatToIntBoundConds,
#       which the existing isLet arm drains; the wrapper would drain it the same way)
#   S2: normal arithmetic in a let-binding expression (no bound deposited; drain
#       is a no-op — wrapper returns identity path)
#   S3: float→int inside an assert predicate (lowerBool-style path; exercises the
#       drain on the bool-expression side)
#
# Since no arm has been migrated to use lowerInExpr / lowerBoolInExpr yet, the
# real test is:
#   1. The module compiles (wrappers type-check, WalkCtx param accepted, etc.)
#   2. Verdicts produced by the existing arms are unchanged (zero verdict change)

# ---------------------------------------------------------------------------
# S1 SUT: float→int in a let-binding (drain of convFloatToIntBoundConds)
# ---------------------------------------------------------------------------

proc cr9_floatIntLet(x: float) =
  ## int(x) == 7 with x assigned via let: exercises the isLet arm's drain path.
  ## The domain-bound hint confirms the float→int bound was correctly drained.
  let v = int(x)
  if v == 7: symexTarget("cr9_floatIntLet_hit")

# ---------------------------------------------------------------------------
# S2 SUT: arithmetic in a let-binding (no float bound; drain is identity)
# ---------------------------------------------------------------------------

proc cr9_arithLet(a: int, b: int) =
  ## a + b == 42: a plain arithmetic let — no float→int or closure involved.
  ## The wrapper drain must be a no-op and the verdict sxSat.
  let s = a + b
  if s == 42: symexTarget("cr9_arithLet_hit")

# ---------------------------------------------------------------------------
# S3 SUT: float→int in a while-guard (lowerBool-style drain path via isWhile)
# ---------------------------------------------------------------------------

proc cr9_floatIntWhile(x: float, k: int) =
  ## while int(x) > k: exercises the isWhile arm's lowerBool drain path for
  ## convFloatToIntBoundConds in a boolean position.
  ## This confirms the lowerBoolInExpr wrapper matches the isWhile / isAssert
  ## drain sequence (the domain-bound hint is deposited by lowerBool and must
  ## be drained into the path condition before the guard is evaluated).
  var i = 0
  while int(x) > k:
    i = i + 1
    if i >= 1: break
  if int(x) == 5: symexTarget("cr9_floatIntWhile_hit")

# ---------------------------------------------------------------------------
# Suites
# ---------------------------------------------------------------------------

suite "symex Phase 15 CR-9 Stage 1 — lowerInExpr/lowerBoolInExpr wrapper gate":

  test "CR-9 S1: float→int in let → sxRaised (R16-2: raise is primary finding)":
    ## R16-2: unconstrained int(x) in a let-binding forks a RangeDefect raise
    ## (drain fires at isLet site). The raise is the primary w.found[0] entry
    ## even for tLabel searches; the sat path (v==7 for x=7.0) is found second.
    let r = symexFind(cr9_floatIntLet, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "CR-9 S1: float→int let — tLabel search also returns sxRaised (defect surfaces first)":
    ## Defects surface as w.found[0] even for tLabel searches (E6 semantics:
    ## wantsRaise=true for defects regardless of target kind). The RangeDefect
    ## raise is discovered at the isLet drain site before the arm continuation
    ## walks to the label. Confirms R16-2's E6 precedence for the let pattern.
    let r = symexFind(cr9_floatIntLet, tLabel("cr9_floatIntLet_hit"))
    check r.status == sxRaised

  test "CR-9 S2: arithmetic let: sxSat (no drain side-effects; identity path)":
    ## Plain a + b == 42.  No float bounds, no closure.  The drain (and future
    ## wrapper) must be a no-op: path is returned unchanged, verdict is sxSat.
    let r = symexFind(cr9_arithLet, tLabel("cr9_arithLet_hit"))
    check r.status == sxSat

  test "CR-9 S2: arithmetic let witness round-trips (a + b == 42 at runtime)":
    ## The witness (a, b) must satisfy a + b == 42.
    let r = symexFind(cr9_arithLet, tLabel("cr9_arithLet_hit"))
    check r.status == sxSat
    let a = r.witness[0]
    let b = r.witness[1]
    check a + b == 42

  test "CR-9 S3: float→int in while-guard: sxSat (domain-bound hint retired by R16-2)":
    ## R16-2 replaced the feConvDomainExcluded hint with a real RangeDefect
    ## raise fork. The sat verdict remains; the hint assertion is retired.
    let r = symexFind(cr9_floatIntWhile, tLabel("cr9_floatIntWhile_hit"))
    check r.status == sxSat

  test "CR-9 S3: float→int while-guard witness round-trips (int(x) == 5 at runtime)":
    ## The witness (x, k) must produce int(x) == 5 at the target.
    let r = symexFind(cr9_floatIntWhile, tLabel("cr9_floatIntWhile_hit"))
    check r.status == sxSat
    let x = r.witness[0]
    check int(x) == 5
