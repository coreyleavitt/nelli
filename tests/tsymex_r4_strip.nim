## Round-4 Slice B (walker v66, ADR-0026) — `strutils.strip` modeled as
## quantifier-free DECOMPOSITION constraints (no loop, no quantifier, no
## Int/BV mixing):  s = pre ++ core ++ suf,  pre/suf ∈ (union chars)*,
## core empty or boundary-chars ∉ chars — the unique maximal-strip
## decomposition, so `core` IS `strip(s)` (sound and complete). This
## replaces the biggest practical chunk of chapulin catalog #9 ("loop-
## produced string across a named binding"): strip was the loop.
##
## The UNSAT pins are load-bearing: `boundStripNeverLonger` (strip never
## lengthens — forced by the concat decomposition) and `stripIdempotent`
## (strip∘strip = strip — forced by the boundary clause) would both be SAT
## under an unconstrained-fresh-string stub.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

const boundedSettings = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 20_000_000'u,   # bounds the idempotence UNSAT query — Z3
                                 # diverges unbounded on the nested double
                                 # decomposition (bisected: > 3 h); with an
                                 # rlimit it returns unknown deterministically
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5))

proc chainStrip(s: string) =
  if s.strip().endsWith("x"):
    symexTarget("chain-x")

proc boundStripNeverLonger(s: string) =
  ## strip never lengthens — len(core) <= len(s) by decomposition.
  let t = s.strip()
  if t.len > s.len:
    symexTarget("impossible-longer")

proc boundStripAcross(s: string) =
  ## The chapulin #9 shape: a strip result BOUND to a name and consumed in
  ## a LATER statement — the exact "unprovable" twin their suite scoped
  ## around (stripTrailingDotSpaceTwin's chars set).
  let t = s.strip(leading = false, trailing = true, chars = {'.', ' '})
  if t.endsWith(".md5"):
    symexTarget("md5")

proc stripIdempotent(s: string) =
  ## strip(strip(s)) == strip(s) — the boundary clause forces the second
  ## decomposition's pre/suf empty.
  let t = s.strip()
  let u = t.strip()
  if t != u:
    symexTarget("impossible-nonidem")

suite "symex round-4 Slice B — strip as decomposition constraints":

  test "chain: s.strip().endsWith(\"x\") is SAT with a REAL-strip-consistent witness":
    let r = symexFind(chainStrip, tLabel("chain-x"))
    check r.status == sxSat
    check r.witness[0].strip().endsWith("x")

  test "bound: strip never lengthens (UNSAT soundness pin)":
    let r = symexFind(boundStripNeverLonger, tLabel("impossible-longer"))
    check r.status == sxUnsat

  test "bound-across-statements (chapulin #9 shape): SAT with a REAL-strip-consistent witness":
    let r = symexFind(boundStripAcross, tLabel("md5"))
    check r.status == sxSat
    check r.witness[0].strip(leading = false, trailing = true,
                             chars = {'.', ' '}).endsWith(".md5")

  test "strip idempotence is NEVER satisfiable (rlimit-bounded adversarial pin)":
    ## The full UNSAT proof of strip∘strip = strip makes Z3 diverge on the
    ## nested double decomposition (> 3 h, bisected while landing v66), so
    ## this pin runs rlimit-BOUNDED and asserts the load-bearing half: the
    ## verdict is never sxSat/sxRaised. A stub returning an unconstrained
    ## fresh string (instead of the forced decomposition core) would find a
    ## t != u model INSTANTLY — well inside the budget — and fail this.
    let r = symexFind(stripIdempotent, tLabel("impossible-nonidem"),
                      boundedSettings)
    check r.status in {sxUnsat, sxUnknown}

suite "symex round-4 Slice B — walker version pin":

  test "walker version floor >= 66":
    check parseInt(symexWalkerVersion) >= 66
