## RFC-0016 K8b -- the `faGeneric` fuzzer family (§8.1 "Not axes", §10):
## form {plain, `static` parameter, `when T is`, nested instance, proc-typed
## formal} x type argument {int, int16, int64, distinct int} x un-instantiated
## generic {none, a sibling never instantiated, one referenced only under
## `when false`}, generated through K8a-gen's generator, run through
## `symexFind` and the native differential, with the family's metamorphic
## relations: dead code under a false guard, extract-to-proc, `let` -> `var`,
## the call monomorphised by hand, and an un-instantiated generic added.
## AUD-07 (a generic never instantiated in the scope's unit) is the `uninst`
## dimension and the `twUninst` relation, pinned by the AUD-07 test below.
##   -d:k8bSeed=N -d:k8bCount=N -d:k8bFirst=N   (as K8a-gen's k8a* defines)
import std/[unittest, os, strutils, sets]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const
  k8bSeed {.intdefine.} = 20261117
  k8bCount {.intdefine.} = 26
  gateCount = 26  ## the count the floor is measured at
  k8bFirst {.intdefine.} = 0

let realPins = pinDir()
let pinTmp = getTempDir() / ("k8b_generic_" & $getCurrentProcessId())
createDir(pinTmp)
putEnv("NELLI_PIN_DIR", pinTmp)

const progs = genFamily(faGeneric, k8bSeed, k8bCount, k8bFirst)
genFamilyBatch(progs, "ge")

suite "K8b faGeneric":
  test "the stream is deterministic, prefix-stable, one value per dimension":
    check genFamily(faGeneric, 7, 5) == genFamily(faGeneric, 7, 9)[0 ..< 5]
    check genFamily(faGeneric, 7, 3, 4) == genFamily(faGeneric, 7, 7)[4 ..< 7]
    for p in progs:
      check p.shape == shGeneric
      check p.fam.len == famDims[faGeneric].len

  test "every relation is a different source, and the batch runs each one":
    var ran: set[Twin]
    var all: set[Twin]
    for p in progs:
      let o = render(p, "g", twNone)
      for tw in applicable(p):
        check render(p, "g", tw) != o
        all.incl tw
    for c in familyCases(progs): ran.incl c.tw
    if k8bCount == gateCount: check ran == all + {twNone}

  test "generated programs and their relations agree with native, figure at its floor":
    let outs = runBatch_ge()
    let r = runFamily(faGeneric, progs, outs, k8bSeed,
                      "tsymex_0016_k8b_generic.nim", realPins)
    echo report(faGeneric, k8bSeed, k8bCount, r, outs)
    check r.findings.len == 0
    check r.exact > 0
    # the ratchet: at the gate's count the figure is at or above the floor
    # (a nightly's larger or shifted batch is not compared)
    if k8bFirst == 0 and k8bCount == gateCount:
      checkpoint r.floorProblems.join("\n")
      check r.floorProblems.len == 0

# AUD-07: a generic never instantiated in the SUT's compilation unit. Two
# fixed programs, one per `uninst` value (a sibling never instantiated, one
# referenced only under `when false`), each under every relation, including
# `twUninst` (a second un-instantiated generic added).
const aud07 = @[
  Prog(id: 900, shape: shGeneric, ty: "int8", fam: @[0, 0, 1], cmp: ">",
       k: Lit(kind: lkNum, n: 7)),
  Prog(id: 901, shape: shGeneric, ty: "int8", fam: @[2, 3, 2], cmp: "==",
       k: Lit(kind: lkNum, n: 1))]
genBatch(aud07, false, "aud07")

suite "K8b faGeneric: AUD-07":
  test "an un-instantiated generic beside the SUT leaves its verdict exact":
    let outs = runBatch_aud07()
    for o in outs:
      checkpoint $o.progId & " " & o.variant & " " & o.msg
      check o.kind == okExact
      check o.status == "sxSat"
    check outs.len == 2 * (1 + applicable(aud07[0]).len)
    check findings(aud07, outs, 0).len == 0
    for p in aud07:
      check "_u[T]" in render(p, "g", twNone)
      check "_v[T]" in render(p, "g", twUninst)
    check "when false: discard g_u(a)" in render(aud07[1], "g", twNone)

# AUD-07's own pins: a hand-written SUT whose unit holds a generic never
# instantiated (referenced only under `when false`), pinned sat and, over the
# exhaustive int8 domain, unsat.
proc aud07Never[T](x: T): T = x div T(0)
proc aud07Twice[T](x: T): T = x * T(2) + T(1)
proc aud07Sat(a: int8) =
  when false: discard aud07Never(a)
  if aud07Twice(int(a)) == 15: symexTarget("hit")
proc aud07Unsat(a: int8) =
  when false: discard aud07Never(a)
  if aud07Twice(int(a)) == 0: symexTarget("hit")

suite "K8b faGeneric: AUD-07 pins":
  test "the un-instantiated generic's SUT is exact, sat and unsat":
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    let s = pinExact(aud07Sat, cellKey(faGeneric, "k8b/uninst/whenFalse"),
                     tLabel("hit"), all)
    check s.status == sxSat
    let u = pinExact(aud07Unsat, cellKey(faGeneric, "k8b/uninst/whenFalse"),
                     tLabel("hit"), all)
    check u.status == sxUnsat
