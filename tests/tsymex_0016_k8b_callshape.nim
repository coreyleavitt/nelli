## RFC-0016 K8b -- the `faCallShape` fuzzer family (§8.1 "Not axes", §10):
## callee kind {proc, func, template, closure, nested proc} x parameter mode
## {value, `var`, `openArray`} x call site {`let`, argument, condition,
## arithmetic operand, assignment}, generated through K8a-gen's generator,
## run through `symexFind` and the native differential, with the family's
## metamorphic relations: dead code under a false guard, extract-to-proc,
## wrap-in-template, `let` -> `var`, and the call hoisted into a temporary
## (the evaluation-order neighbour, §6).
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
  k8bCount {.intdefine.} = 22
  gateCount = 22  ## the count the floor is measured at
  k8bFirst {.intdefine.} = 0

let realPins = pinDir()
let pinTmp = getTempDir() / ("k8b_callshape_" & $getCurrentProcessId())
createDir(pinTmp)
putEnv("NELLI_PIN_DIR", pinTmp)

const progs = genFamily(faCallShape, k8bSeed, k8bCount, k8bFirst)
genFamilyBatch(progs, "cs")

suite "K8b faCallShape":
  test "the stream is deterministic, prefix-stable, one value per dimension":
    check genFamily(faCallShape, 7, 5) == genFamily(faCallShape, 7, 9)[0 ..< 5]
    check genFamily(faCallShape, 7, 3, 4) == genFamily(faCallShape, 7, 7)[4 ..< 7]
    for p in progs:
      check p.shape == shCallShape
      check p.fam.len == famDims[faCallShape].len

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
    let outs = runBatch_cs()
    let r = runFamily(faCallShape, progs, outs, k8bSeed,
                      "tsymex_0016_k8b_callshape.nim", realPins)
    echo report(faCallShape, k8bSeed, k8bCount, r, outs)
    check r.findings.len == 0
    check r.exact > 0
    # the ratchet: at the gate's count the figure is at or above the floor
    # (a nightly's larger or shifted batch is not compared)
    if k8bFirst == 0 and k8bCount == gateCount:
      checkpoint r.floorProblems.join("\n")
      check r.floorProblems.len == 0
