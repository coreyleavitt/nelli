## RFC-0005 (soundness channels) slice S8by -- S8bp's remainder, all
## precision.
##
## Pinned here (the RFC's "As landed (S8by)" note has the mechanism and
## the measurements):
##   (1) concolic collection's scratch solves (`concreteBranchOutcome`,
##       `concretelyInfeasible`, the concrete-inputs check) check in
##       contexts of their own: with 300 unrelated Int constants live in
##       the context, a factoring branch condition took 72,126 units
##       against 72,162 (Z3 5.1; 26,695 against 26,726 on 4.13.4), and
##       under a bound between such spends one context decided it and the
##       other did not. Now its spend, so its outcome, is the query's;
##   (2) after a facts-first SAT, `checkCapped` runs neither (1b) nor
##       (1c)'s uncapped half: the facts-first check is (1c)'s query under
##       a smaller budget, and (1b)'s is a subset of it, so both are known
##       SAT. Where the facts-first model also satisfies the caps, (1c)'s
##       capped half is known SAT too and is skipped. Verdicts are
##       unchanged; `lastNl` spends about 607k units less (Z3 5.1).
##   (4) a regex membership below the top level -- under a disjunction
##       (`a or not s.contains(re"b")`), in an `ite` branch, under a `not`
##       -- is merged with the memberships of the same string that hold
##       where it is read, as S8bp merges top-level ones: S8bp's empty
##       `s.endsWith(re"b+") and not s.contains(re"b")` with the negated
##       membership inside a disjunction was `sxUnknown` on Z3 4.13.4.
##       Pinned against native Nim.
import std/[unittest, strutils, re, options]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8by_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc lastNl(s, t: string; x, y: int) =
  ## S8bp's `rfind` query refuted only by the cap (step 1 UNSAT), so step
  ## 3 decides it; the facts-first check is SAT.
  if t.len > 10 and s.rfind("bc") == 1 and x > 1 and y > 1 and x < 2000 and
     y < 2000 and x * y == 1022117:
    symexTarget("s8by_lastnl")

proc preSufNl(s: string; x, y: int) =
  ## S8bp's: UNSAT on its own, decided by step 2's core after a
  ## facts-first SAT whose model has `s.len == 2`, inside the cap.
  if x > 1 and y > 1 and x < 2000 and y < 2000 and x * y == 1022117 and
     s.startsWith("ab") and s.endsWith("ba") and s.len == 2:
    symexTarget("s8by_presuf")

proc pastCap(t: string) =
  ## SAT only past the cap of 8: the facts-first model (`t.len > 10`)
  ## breaks the cap, so (1c)'s capped half still runs and declines.
  if t.len > 10:
    symexTarget("s8by_pastcap")

const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))

proc recorded(): seq[string] =
  ## `symexStepStats` as `step/status=units`.
  for s in symexStepStats: result.add s.step & "/" & s.status & "=" & $s.units

proc names(steps: seq[string]): seq[string] =
  for x in steps: result.add x.split('/')[0]

template walk(sut: untyped; lbl: string; settings: SymexSettings):
    tuple[status: SymexStatusKind, steps: seq[string], units: int] =
  symexStepStats = @[]
  symexQueryStats = @[]
  let r = symexFind(sut, tLabel(lbl), settings)
  var u = 0
  for q in symexQueryStats: u += q.rlimitDelta
  let st = recorded()
  checkpoint $r.status & " units=" & $u & ": " & st.join(" ")
  symexStepStats = @[]
  symexQueryStats = @[]
  (r.status, st, u)

let z351 = z3FullVersion().startsWith("5.")

# ---- (1) the concolic scratch solves -----------------------------------------

var scratch: array[2, tuple[outcome: Option[bool], infeasible: bool,
                            units, infeasibleUnits: int]]

proc ctxCount(ctx: Z3Context): int =
  ## The step count of `ctx` itself (an empty check there reads it).
  let s = newSolver(ctx)
  discard s.check()
  let st = s.getStatistics()
  if st.contains("rlimit count"): st.getInt("rlimit count") else: 0

proc scratchSolves(arg: tuple[slot, unrelated: int; bound: uint]) {.thread.} =
  ## On a fresh thread (no walk's state in its threadvars): a branch
  ## condition `x > 1` beside a factoring search, decided by
  ## `concreteBranchOutcome` under `bound`, and the same facts with `x <=
  ## 1` by `concretelyInfeasible`, in a context holding `unrelated` Int
  ## constants no query mentions. `units` and `infeasibleUnits` are what
  ## each spent, in contexts of their own or in this one.
  {.cast(gcsafe).}:
    let ctx = newContext()
    var keep: seq[Z3Int]
    for k in 0 ..< arg.unrelated:
      keep.add mkIntVar(ctx, "s8by_unrelated_" & $k)
    let x = mkIntVar(ctx, "x")
    let y = mkIntVar(ctx, "y")
    let one = mkInt(ctx, 1)
    let lim = mkInt(ctx, 2000)
    let facts = @[x > one, y > one, x < lim, y < lim,
                  x * y == mkInt(ctx, 1_022_117)]
    let settings = SymexSettings(budget: ResourceBudget(queryRLimit: arg.bound))
    var own = ownContextUnits
    var here = ctxCount(ctx)
    let o = concreteBranchOutcome(ctx, @[], x > one, settings, facts)
    let units = ownContextUnits - own + ctxCount(ctx) - here
    own = ownContextUnits
    here = ctxCount(ctx)
    let inf = concretelyInfeasible(ctx, @[], facts & @[x <= one], settings)
    scratch[arg.slot] = (o, inf, units,
                         ownContextUnits - own + ctxCount(ctx) - here)

proc solveBoth(bound: uint) =
  ## The scratch solves as is (`scratch[0]`) and with 300 unrelated
  ## constants in the context (`scratch[1]`).
  for slot in 0 .. 1:
    var th: Thread[tuple[slot, unrelated: int; bound: uint]]
    createThread(th, scratchSolves, (slot, slot * 300, bound))
    joinThread(th)
  checkpoint "bound " & $bound & ": as is " & $scratch[0] & ", perturbed " &
    $scratch[1]

suite "S8by (1): a concolic scratch solve is the same in any context":

  test "unrelated constants in the context move no scratch solve":
    # Bounded loosely enough to finish: what each spends.
    solveBoth(50_000_000'u)
    let spent = (scratch[0].units, scratch[1].units)
    let finished = scratch[0].outcome
    check scratch[0].infeasibleUnits > 0
    check scratch[0].infeasibleUnits == scratch[1].infeasibleUnits
    # Under a bound between the two spends (or at the one spend).
    solveBoth(uint((spent[0] + spent[1]) div 2))
    check finished == some(true)
    check spent[0] > 0
    # The same spend, so both contexts decide alike under any bound.
    check spent[0] == spent[1]
    check scratch[0].outcome == scratch[1].outcome
    check scratch[0].infeasible and scratch[1].infeasible

suite "S8by (2): no (1b) or (1c) after a facts-first SAT":

  test "lastNl: the facts-first SAT, step 1, step 3; no 1b or 1c":
    let w = walk(lastNl, "s8by_lastnl", smallCap)
    check w.status == sxSat
    let n = names(w.steps)
    check "factsFirst" in n
    check "1b" notin n
    check "1c" notin n
    ## Before S8by (S8bp): 1,106,184 units on Z3 5.1, of which (1b)
    ## 295,900 and (1c) 311,463; 1,499,189 on 4.13.4.
    if z351: check w.units <= 1_106_184 - 600_000
    else: check w.units < 1_499_189

  test "preSufNl: still UNSAT by step 2, with no 1b, 1c or 1c-capped":
    let w = walk(preSufNl, "s8by_presuf", defaultSymexSettings())
    check w.status == sxUnsat
    let n = names(w.steps)
    check "2" in n
    check "1b" notin n
    check "1c" notin n
    # The facts-first model has `s.len == 2`: the caps hold in it.
    check "1c-capped" notin n

  test "pastCap: the model breaks the cap, so (1c)'s capped half declines":
    let w = walk(pastCap, "s8by_pastcap", smallCap)
    check w.status == sxUnknown
    let n = names(w.steps)
    check "1c-capped" in n
    check "1b" notin n
    check "1c" notin n

# ---- (4) memberships below the top level -------------------------------------

proc orRun(s: string; a: bool) =
  ## Empty: with `a` false the disjunction needs `s` to hold no `b`, but
  ## it ends in a run of them.
  if s.endsWith(re"b+") and not a and (a or not s.contains(re"b")):
    symexTarget("s8by_or")

proc orSat(s: string; a: bool) =
  ## SAT, with `a` true or with no `b` at all -- not both.
  if s.endsWith(re"b+") and (a or not s.contains(re"b")):
    symexTarget("s8by_or_sat")

proc iteRun(s: string; i: int) =
  ## Empty: `flags[i]` is an `ite` on `i`; index 1 is never false, and at
  ## index 0 `s` holds no `b` but ends in a run of them.
  let flags = [s.contains(re"b"), true]
  if i >= 0 and i <= 1 and s.endsWith(re"b+") and not flags[i]:
    symexTarget("s8by_ite")

proc iteSat(s: string; i: int) =
  ## SAT only at index 1, with a string of at most three characters.
  let flags = [s.contains(re"b"), s.len > 3]
  if i >= 0 and i <= 1 and s.endsWith(re"b+") and not flags[i]:
    symexTarget("s8by_ite_sat")

proc twoNeg(s: string) =
  ## Empty, at the top level: two negated memberships and a plain one on
  ## one string. `mergeMemberships` complements both negated ones into one
  ## intersection (each complement is now referenced as it is made).
  if s.endsWith(re"b+") and not s.contains(re"a") and not s.contains(re"b"):
    symexTarget("s8by_twoneg")

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT natively in a capture frame.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

proc words(n: int): seq[string] =
  ## Every string over `a`, `b` and `c` of at most `n` characters.
  result = @[""]
  var last = @[""]
  for k in 1 .. n:
    var next: seq[string]
    for w in last:
      for c in "abc": next.add w & c
    result.add next
    last = next

template verdict4(sut: untyped; lbl: string): untyped =
  ## `sut`'s walk to `lbl`, with the units its queries spent.
  block:
    symexQueryStats = @[]
    let r = symexFind(sut, tLabel(lbl))
    var u = 0
    for q in symexQueryStats: u += q.rlimitDelta
    checkpoint $r.status & " units=" & $u & "\n" & symexQueryStatsSummary()
    for e in r.errors: checkpoint $e.kind & ": " & e.msg
    symexQueryStats = @[]
    (status: r.status, units: u, r: r)

suite "S8by (4): a membership under a disjunction or an ite is merged":

  test "native: the empty ones reach their label on no short string":
    for w in words(6):
      for a in [false, true]:
        check not reproduces(orRun(w, a), "s8by_or")
      for i in -1 .. 2:
        check not reproduces(iteRun(w, i), "s8by_ite")
      check not reproduces(twoNeg(w), "s8by_twoneg")

  test "a or not s.contains(re\"b\"), beside s.endsWith(re\"b+\"): UNSAT":
    ## Before S8by: `sxUnknown` on Z3 4.13.4, 8,524,640 units (step 1
    ## 5,139,708, step 2 3,383,088, the cap in its core).
    let v = verdict4(orRun, "s8by_or")
    check v.status == sxUnsat
    check v.units <= 20_000

  test "the same disjunction, SAT: the witness reaches the label natively":
    let v = verdict4(orSat, "s8by_or_sat")
    check v.status == sxSat
    if v.status == sxSat:
      check reproduces(orSat(v.r.witness[0], v.r.witness[1]), "s8by_or_sat")

  test "not flags[i], an ite over a membership: UNSAT":
    let v = verdict4(iteRun, "s8by_ite")
    check v.status == sxUnsat
    check v.units <= 20_000

  test "two negated memberships and a plain one at the top level: UNSAT":
    let v = verdict4(twoNeg, "s8by_twoneg")
    check v.status == sxUnsat
    check v.units <= 20_000

  test "the same ite, SAT: the witness reaches the label natively":
    let v = verdict4(iteSat, "s8by_ite_sat")
    check v.status == sxSat
    if v.status == sxSat:
      check reproduces(iteSat(v.r.witness[0], v.r.witness[1]), "s8by_ite_sat")

suite "S8by: walker version floor":

  test "symexWalkerVersion >= 231":
    check parseInt(symexWalkerVersion) >= 231
