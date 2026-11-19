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
## each fits the per-test time ceiling: this one runs programs 0..12.
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
  k8bFirst {.intdefine.} = 0
  k8bCount {.intdefine.} = 13

familyHalf(faGeneric, "gea", runBatch_gea, "tsymex_0016_k8b_generic_a.nim",
           k8bSeed, k8bFirst, k8bCount, 26)
