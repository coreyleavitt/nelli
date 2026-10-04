## RFC-0005 (soundness channels) slice S8by -- S8bp's remainder, all
## precision.
##
## Pinned here (the RFC's "As landed (S8by)" note has the mechanism and
## the measurements):
##   (2) after a facts-first SAT, `checkCapped` runs neither (1b) nor
##       (1c)'s uncapped half: the facts-first check is (1c)'s query under
##       a smaller budget, and (1b)'s is a subset of it, so both are known
##       SAT. Where the facts-first model also satisfies the caps, (1c)'s
##       capped half is known SAT too and is skipped. Verdicts are
##       unchanged; `lastNl` spends about 607k units less (Z3 5.1).
import std/[unittest, strutils]
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
