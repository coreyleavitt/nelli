## RFC-0016 K8a-gen -- the differential generator and its metamorphic twins
## (§10), bounded smoke. Seed and program count are parameters:
##   -d:k8aSeed=N -d:k8aCount=N   (K8a-job runs larger budgets nightly)
## A disagreement fails the test and is reported with its seed and program.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s0016_k8a_gen

const
  k8aSeed {.intdefine.} = 20261108
  k8aCount {.intdefine.} = 6

let pinTmp = getTempDir() / ("k8a_gen_" & $getCurrentProcessId())
createDir(pinTmp)
putEnv("NELLI_PIN_DIR", pinTmp)

# RED fixtures: hand-built programs with a known walker verdict, run with a
# planted lie. Program 0 is unsat (`a mod 1 != 0`), program 1 is sat
# (`a mod 2 == 0`); the plant flips each verdict.
const redProgs = @[
  Prog(id: 0, shape: shDivLit, ty: "uint", op: "mod",
       lit: Lit(kind: lkNum, n: 1), cmp: "!=", k: Lit(kind: lkNum, n: 0)),
  Prog(id: 1, shape: shDivLit, ty: "int", op: "mod",
       lit: Lit(kind: lkNum, n: 2), cmp: "==", k: Lit(kind: lkNum, n: 0))]
genBatch(redProgs, true, "red")

const progs = genPrograms(k8aSeed, k8aCount)
genBatch(progs, false, "run")

suite "K8a-gen":
  test "generation is deterministic and prefix-stable":
    check genPrograms(7, 5) == genPrograms(7, 5)
    check genPrograms(7, 5) == genPrograms(7, 9)[0 ..< 5]
    check genPrograms(7, 5) != genPrograms(8, 5)

  test "every twin is a different source from its original":
    for p in progs:
      let o = render(p, "g", twNone)
      for tw in applicable(p):
        check render(p, "g", tw) != o

  test "RED: a planted wrong verdict is caught, with seed and program":
    let outs = runBatch_red()
    let fs = findings(redProgs, outs, 424242)
    var native = 0
    for o in outs:
      if o.variant == "orig": check o.kind == okDisagree
      if o.kind == okDisagree: inc native
    check native >= 2
    check fs.len >= 2
    for f in fs[0 .. 1]:
      check "seed=424242" in f
      check "proc g" in f
      check "prog=" in f

  test "RED: a twin whose verdict differs from the original is reported":
    let a = GenOutcome(progId: 0, variant: "orig", kind: okExact,
                    status: "sxSat", trusted: true)
    var b = a
    b.variant = "dead"
    b.status = "sxUnsat"
    let fs = findings(redProgs, @[a, b], 1)
    check fs.len == 1
    check "metamorphic" in fs[0]
    # a declined twin is never a disagreement
    b.trusted = false
    check findings(redProgs, @[a, b], 1).len == 0

  test "smoke: generated programs and their twins agree with native":
    let outs = runBatch_run()
    let d = distribution(outs)
    echo "k8a-gen seed=", k8aSeed, " programs=", k8aCount,
      " runs=", outs.len, " exact=", d.exact, " sampled-unsat=", d.sampledExact,
      " declined=", d.declined, " disagree=", d.disagree
    echo "k8a-gen by shape: ", d.byShape
    echo "k8a-gen declines:\n", declineSummary(outs)
    for f in findings(progs, outs, k8aSeed):
      echo "FINDING ", f
    check findings(progs, outs, k8aSeed).len == 0
    check d.exact + d.sampledExact > 0
    # Programs take shapes round-robin (`id mod` the shape count), so a run of
    # at least one program per shape must reach every shape; a smaller
    # -d:k8aCount covers only the first k8aCount shapes.
    for sh in Shape:
      if ord(sh) < k8aCount: check d.byShape[sh] > 0
