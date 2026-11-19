## RFC-0016 K8b -- the `faCallShape` fuzzer family (§8.1 "Not axes", §10):
## callee kind {proc, func, template, closure, nested proc} x parameter mode
## {value, `var`, `openArray`} x call site {`let`, argument, condition,
## arithmetic operand, assignment}, generated through K8a-gen's generator,
## run through `symexFind` and the native differential, with the family's
## metamorphic relations: dead code under a false guard, extract-to-proc,
## wrap-in-template, `let` -> `var`, and the call hoisted into a temporary
## (the evaluation-order neighbour, §6).
##
## The family's batch is 30 programs in two suites (`familyFiles`), so
## each fits the per-test time ceiling: this one runs programs 15..29.
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
  k8bFirst {.intdefine.} = 15
  k8bCount {.intdefine.} = 15

familyHalf(faCallShape, "csb", runBatch_csb, "tsymex_0016_k8b_callshape_b.nim",
           k8bSeed, k8bFirst, k8bCount, 30)
