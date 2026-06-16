## Phase 15 — Cluster C, cycle C2b: closure CALL dispatch (the cluster CORE).
##
## When the walker lowers an `iekClosureCall`, it (ADR-0009 D6):
##   1. resolves the callee variable to an `svClosure` in the current env (a
##      lambda bound by C2a construction, OR a proc-valued PARAMETER also bound
##      as an svClosure); an unresolved callee → `ceClosureUnknownCallee` /
##      sxUnknown (Invariant 3),
##   2. descends the lambda BODY ONCE (reached via the site→body map that
##      `buildClosure` stashes — `svClosure` carries the site, not the body IR),
##      binding the params to the concrete call args and the captures from the
##      closure's env tuple,
##   3. applies the per-site `funcSym` at the GROUND `(env, args)` of THIS
##      occurrence (raw `Z3_mk_app`), and for EACH body return sub-path
##      `(pc_i, v_i)` asserts the GROUND implication
##         implies(branch_conds_i, funcSym(env, args) == v_i)
##      — NEVER a `∀env,args` axiom (the G4 hang). The call RESULT is the funcSym
##      application the axioms constrain.
##
## C2b is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/[unittest, strutils]
import proptest/symex
import proptest/smt/runtime  ## C2b: introspect the ground closure-call axioms

# --- Sub-test 1: a closure call observes a captured value. -------------------
#
#   proc sut(x: int): int =
#     let offset = x * 2
#     let f = proc(y: int): int = y + offset
#     f(3)
#
# `f(3)` evaluates to `3 + offset == 3 + x*2`. Gate the SUT result at 13 ⇒ the
# witness must be x == 5 (3 + 5*2 == 13).
proc sutCapture(x: int) =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  if f(3) == 13:
    symexTarget("captured")

# --- Sub-test 2: a proc-valued PARAMETER (resolved via svClosure, not a
# ceClosureUnknownCallee), exercising Cluster G generics (applyTwice[T]). ------
#
#   proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))
#   proc sut(n: int): int = applyTwice(proc(x: int): int = x + 1, n)
#
# `applyTwice` applies `f` twice: (n+1)+1 == n+2. Gate at 42 ⇒ witness n == 40.
proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))

proc sutProcParam(n: int) =
  if applyTwice(proc(x: int): int = x + 1, n) == 42:
    symexTarget("twice")

# --- Sub-test 3: a 2-branch lambda body — both axiom arms must be present. ----
#
#   let f = proc(x: bool, p: int, q: int): int = (if x: return p; return q)
#   f(cond, a, b)  ⇒  cond ? a : b
#
# Gate at a == 7 path: with cond=true the result is `a`; introspect that BOTH
# arms `implies(cond, fs==a)` and `implies(not cond, fs==b)` were asserted.
proc sutTwoBranch(cond: bool, a: int, b: int) =
  let f = proc(x: bool, p: int, q: int): int =
    if x: return p
    return q
  if f(cond, a, b) == 7:
    symexTarget("branch")

suite "symex Phase 15 C2b — closure call dispatch (ground multi-return-path axiom)":

  test "C2b-1: closure call observes captured value (f(3) == 3 + x*2)":
    let r = symexFind(sutCapture, tLabel("captured"))
    check r.status == sxSat
    check r.witness[0] == 5    ## x : 3 + x*2 == 13 ⇒ x == 5

  test "C2b-2: proc-valued param resolves via svClosure (applyTwice ⇒ n+2)":
    let r = symexFind(sutProcParam, tLabel("twice"))
    check r.status == sxSat
    check r.witness[0] == 40   ## n : (n+1)+1 == 42 ⇒ n == 40

  test "C2b-3: 2-branch lambda body — both ground axiom arms present":
    let r = symexFind(sutTwoBranch, tLabel("branch"))
    check r.status == sxSat
    # The result `f(cond, a, b) == 7` is reachable via EITHER arm (a==7 with
    # cond, or b==7 with not-cond), so the witness alone does not pin a branch.
    # Introspect the GROUND closure-call axioms the run asserted: there must be
    # TWO arms, one guarded by `cond` and one by `(not cond)` — and BOTH are
    # ground IMPLICATIONS (`=>`), never a universal quantifier (`forall`). This
    # is the D6 multi-return-path encoding (and the proof there is no hang-prone
    # `∀env,args` axiom).
    # `currentClosureCallAxiomStrs` holds the SMT-LIB rendering of each asserted
    # axiom (captured while the Z3 context was live). The 2-branch body yields
    # one arm guarded by `cond` and one by `(not cond)`.
    let axStrs = currentClosureCallAxiomStrs
    let allAx = axStrs.join(" || ")
    check axStrs.len >= 2                        ## two (or more) return sub-paths
    check "=>" in allAx                          ## GROUND implications, not bare
    check "forall" notin allAx.toLowerAscii      ## NEVER a quantifier (G4 lesson)
    # One arm guarded by the bare cond, the other by its negation (`(not cond)`).
    var sawPos, sawNeg = false
    for s in axStrs:
      if "not" in s: sawNeg = true
      else:          sawPos = true
    check sawPos                                 ## the `=> cond (= fs a)` arm
    check sawNeg                                 ## the `=> (not cond) (= fs b)` arm
