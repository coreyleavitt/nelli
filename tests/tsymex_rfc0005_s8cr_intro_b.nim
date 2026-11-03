## RFC-0005 S8cr (DoD §6 item 5): the §2.1 introduction invariant for the six
## `dcFreshSymbol` kinds that had no pin of their own.
##
## §2.1: "a `{scSpurious}` site's symbol carries no constraints at
## introduction". Each suite below fires one kind through `symexFind` and asks
## for a value the concrete code cannot produce. Two facts together show the
## symbol took that value:
##
##   * replay off: the status is `sxUnknown`, `scIncomplete` is not in
##     `runTaint` and no decline is unplaced. Under §2.3 that status then has
##     one source, rule 4, a candidate: the solver found a model that reaches
##     the target. Were the symbol constrained to what the concrete code
##     computes, the query would be UNSAT and the verdict `sxUnsat`.
##   * replay on: the same search records `feReplayRefuted`, so the candidate
##     really was a model the native run does not follow. `sxUnsat` would be
##     the introduction invariant's failure, and `sxSat` a replay failure.
##
## Native oracles confirm that the value is out of reach.
##
## `feGlobalHavoc` carries a second question, the suite at the end of this
## file: does its symbol cover every later write to the global? That is the
## §2.1 coverage invariant this slice writes down.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with `tsymex_rfc0005_s8cr_intro`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 64 s).

import std/[unittest, math, strutils, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

const noReplay = SymexSettings(replay: false)
const outOfReach = 123456

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    result.add $e.kind & "/" & $e.severity & " "

template pinFree(sut: untyped; label: string; kind: SymexErrorKind) =
  ## The two-sided pin described in the header.
  let off = symexFind(sut, tLabel(label), noReplay)
  checkpoint "replay off: " & $off.status & " " & show(off.errors)
  check off.status == sxUnknown
  check off.errors.hasKind(kind)
  check scIncomplete notin off.soundness.runTaint
  check unplacedDeclines(off.errors).len == 0
  let on = symexFind(sut, tLabel(label))
  checkpoint "replay on: " & $on.status & " " & show(on.errors)
  check on.status == sxUnknown
  check on.errors.hasKind(kind)
  check on.errors.hasKind(feReplayRefuted)

# ---- feGlobalHavoc ------------------------------------------------------------

var gIntroEntry = 5        # never written after this line
var gIntroOpaque = 0

proc introGlobalEntry(x: int) =
  ## A read before any write: the entry value, any value of the type.
  if gIntroEntry == outOfReach and x == 1:
    symexTarget("intro_global_entry")

proc introGlobalEntryNeg(x: int) =
  if not (gIntroEntry == 5) and x == 1:
    symexTarget("intro_global_entry_neg")

proc introOpaqueSet() {.symexOpaque.} =
  gIntroOpaque = 1

proc introGlobalOpaque(x: int) =
  ## The other mint site: an opaque call's summary says it may write it.
  gIntroOpaque = 0
  introOpaqueSet()
  if gIntroOpaque == outOfReach and x == 1:
    symexTarget("intro_global_opaque")

suite "introduction invariant: feGlobalHavoc":
  test "oracle: the entry value is 5":
    check gIntroEntry == 5
  test "the entry value is free":
    pinFree(introGlobalEntry, "intro_global_entry", feGlobalHavoc)
  test "both polarities":
    pinFree(introGlobalEntryNeg, "intro_global_entry_neg", feGlobalHavoc)
  test "an opaque call's fresh value is free of what the body writes":
    pinFree(introGlobalOpaque, "intro_global_opaque", feGlobalHavoc)

# ---- feGlobalHavoc: the coverage invariant ------------------------------------
#
# The introduction invariant asks about one moment. A location's fresh symbol
# also needs every later write to that location to reach the model, or an
# `sxUnsat` that "holds for every entry value" is a claim about a program with
# a store removed. §2.1 states this as the coverage invariant. Each route
# below writes the global after the first read, and the label is reachable in
# Nim, so `sxUnsat` is false on all of them.

var gCovDirect, gCovCallee, gCovVar, gCovAddr, gCovLocalPtr, gCovClosure = 1
var gCovOpaque, gCovParam, gCovParamCallee, gCovParamValue = 1

proc covSet(v: var int; x: int) = v = x
proc covSetPtr(p: ptr int; x: int) = p[] = x
proc covWriteCallee(x: int) = gCovCallee = x
proc covOpaqueWrite() {.symexOpaque.} = gCovOpaque = gCovOpaque + 1

proc covDirect(x: int) =
  let a = gCovDirect
  if a > 1000: return      # no OverflowDefect beside the labels
  gCovDirect = a + 1
  if gCovDirect == a and x == 1: symexTarget("cov_direct_dead")
  if gCovDirect != a and x == 1: symexTarget("cov_direct")

proc covCallee(x: int) =
  let a = gCovCallee
  if a > 1000: return
  covWriteCallee(a + 1)
  if gCovCallee != a and x == 1: symexTarget("cov_callee")

proc covVar(x: int) =
  let a = gCovVar
  if a > 1000: return
  covSet(gCovVar, a + 1)
  if gCovVar != a and x == 1: symexTarget("cov_var")

proc covAddr(x: int) =
  let a = gCovAddr
  if a > 1000: return
  covSetPtr(addr gCovAddr, a + 1)
  if gCovAddr != a and x == 1: symexTarget("cov_addr")

proc covOpaque(x: int) =
  let a = gCovOpaque
  if a > 1000: return
  covOpaqueWrite()
  if gCovOpaque != a and x == 1: symexTarget("cov_opaque")

proc covLocalPtr(x: int) =
  ## Declined or havocked, but never `sxUnsat`.
  let a = gCovLocalPtr
  if a > 1000: return
  let p = addr gCovLocalPtr
  p[] = a + 1
  if gCovLocalPtr != a and x == 1: symexTarget("cov_local_ptr")

proc covClosure(x: int) =
  let a = gCovClosure
  if a > 1000: return
  let f = proc() = gCovClosure = a + 1
  f()
  if gCovClosure != a and x == 1: symexTarget("cov_closure")

proc covParam(p: ptr int) =
  ## The store through `p` reaches the global only when `p` addresses it. The
  ## walk's target scan misses a global it has only read.
  if p == nil: return
  let a = gCovParam
  p[] = 7
  if gCovParam != a: symexTarget("cov_param")

proc covParamCallee(p: ptr int) =
  if p == nil: return
  let a = gCovParamCallee
  covSetPtr(p, 7)
  if gCovParamCallee != a: symexTarget("cov_param_callee")

proc covParamValue(p: ptr int) =
  if p == nil: return
  let a = gCovParamValue
  let f = covSetPtr
  f(p, 7)
  if gCovParamValue != a: symexTarget("cov_param_value")

template reachedNatively(call: untyped; label: string): bool =
  symexCaptureBegin()
  call
  label in symexCaptureEnd()

template pinCovered(sut: untyped; label: string) =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  check r.status != sxUnsat

template pinParamStore(sut: untyped; label: string) =
  ## A store through a `ptr` parameter that may address a global only read.
  ## The walk binds the global at its entry value (S8cd's `ptrTargets`), so the
  ## candidate is `feGlobalHavoc`. It was a false `sxUnsat` before S8cd. The
  ## replay's witness pointer does not address the global, so the run misses
  ## and refutes the candidate: exactly `sxUnknown`, where Nim reaches the label
  ## (the oracle above). A replay that aims a pointer at a global would make
  ## this `sxSat`, and this pin then moves with it.
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  check r.errors.hasKind(feGlobalHavoc)
  check r.errors.hasKind(feReplayRefuted)
  check r.status == sxUnknown

suite "coverage invariant: a write the walk models reaches the global":
  test "a direct write":
    pinCovered(covDirect, "cov_direct")
    let d = symexFind(covDirect, tLabel("cov_direct_dead"))
    checkpoint $d.status & " " & show(d.errors)
    checkUnsatOverTaintOnly(d)
  test "a callee's write":
    pinCovered(covCallee, "cov_callee")
  test "a var argument":
    pinCovered(covVar, "cov_var")
  test "an addr argument":
    pinCovered(covAddr, "cov_addr")
  test "an opaque call's write":
    pinCovered(covOpaque, "cov_opaque")
  test "a local pointer to it":
    pinCovered(covLocalPtr, "cov_local_ptr")
  test "a closure's write":
    pinCovered(covClosure, "cov_closure")

suite "coverage invariant: a store through a ptr parameter":
  test "oracle: Nim reaches every label":
    gCovParam = 1
    check reachedNatively(covParam(addr gCovParam), "cov_param")
    gCovParamCallee = 1
    check reachedNatively(covParamCallee(addr gCovParamCallee), "cov_param_callee")
    gCovParamValue = 1
    check reachedNatively(covParamValue(addr gCovParamValue), "cov_param_value")
  test "the store is direct":
    pinParamStore(covParam, "cov_param")
  test "the store is in a callee":
    pinParamStore(covParamCallee, "cov_param_callee")
  test "the store is in a proc value":
    pinParamStore(covParamValue, "cov_param_value")

suite "RFC-0005 S8cr: walker version":
  test "symexWalkerVersion >= 245 (no walker change: this slice adds pins)":
    check parseInt(symexWalkerVersion) >= 245
