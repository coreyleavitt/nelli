## RFC-0016 K8b -- the `faGeneric` fuzzer family (§8.1 "Not axes", §10):
## form {plain, `static` parameter, `when T is`, nested instance, proc-typed
## formal} x type argument {int, int16, int64, distinct int} x un-instantiated
## generic {none, a sibling never instantiated, one referenced only under
## `when false`}, generated through K8a-gen's generator, run through
## `symexFind` and the native differential, with the family's metamorphic
## relations: dead code under a false guard, extract-to-proc, `let` -> `var`,
## the call monomorphised by hand, and an un-instantiated generic added.
## AUD-07 (a generic never instantiated in the scope's unit) is the `uninst`
## dimension and the `twUninst` relation, pinned in the second half.
##
## The family's batch is 26 programs in two suites (`familyFiles`), so
## each fits the per-test time ceiling: this one runs programs 13..25.
## K1 judges the pairwise floor on the union of both halves' records.
##   -d:k8bSeed=N -d:k8bFirst=N -d:k8bCount=N   (this half's slice)
import std/[unittest, os, strutils, sets]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const
  k8bSeed {.intdefine.} = 20261117
  k8bFirst {.intdefine.} = 13
  k8bCount {.intdefine.} = 13

familyHalf(faGeneric, "geb", runBatch_geb, "tsymex_0016_k8b_generic_b.nim",
           k8bSeed, k8bFirst, k8bCount, 26)

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
