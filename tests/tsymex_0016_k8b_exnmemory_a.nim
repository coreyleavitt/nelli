## RFC-0016 K8b -- the `faExnMemory` fuzzer family (§8.1 "Not axes", §10):
## memory {local, seq element, object field, ref-object field, array element}
## x write point {before the raise, in the handler, in `finally`} x handler
## {`except ValueError`, bare `except`, `try`/`finally` inside an outer
## `except`} x raise {direct, through a call}, generated through K8a-gen's
## generator, run through `symexFind` and the native differential, with the
## family's metamorphic relations: dead code under a false guard,
## extract-to-proc, the whole `try` wrapped in a template, and every write
## routed through a `var` parameter (the shared-memory neighbour, §6; INT-55
## was found there).
##
## The family's batch is 24 programs in two suites (`familyFiles`), so
## each fits the per-test time ceiling: this one runs programs 0..11.
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
  k8bCount {.intdefine.} = 12

familyHalf(faExnMemory, "ema", runBatch_ema, "tsymex_0016_k8b_exnmemory_a.nim",
           k8bSeed, k8bFirst, k8bCount, 24)
