## RFC-0016 K8a-gen -- the differential generator and its metamorphic twins
## (§10), bounded smoke. Seed and program count are parameters:
##   -d:k8aSeed=N -d:k8aCount=N   (K8a-job runs larger budgets nightly)
##   -d:k8aFirst=N                programs [N, N+k8aCount) of the seed's stream
## The nightly splits its budget into batches with k8aFirst: one compile holds
## every program's source and its walks at once (about 0.2 GB per program), so
## a single 250-program build outgrows a 16 GB runner. Ids stay absolute.
## A disagreement fails the test and is reported with its seed and program.
import std/[unittest, os, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s0016_k8a_gen

const
  k8aSeed {.intdefine.} = 20261108
  k8aCount {.intdefine.} = 6
  k8aFirst {.intdefine.} = 0

let realPins = pinDir()   ## the leg's record directory, before the redirect
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

const progs = genPrograms(k8aSeed, k8aCount, k8aFirst)
genBatch(progs, false, "run")

suite "K8a-gen":
  test "generation is deterministic and prefix-stable":
    check genPrograms(7, 5) == genPrograms(7, 5)
    check genPrograms(7, 5) == genPrograms(7, 9)[0 ..< 5]
    check genPrograms(7, 5) != genPrograms(8, 5)

  test "a batch is the same slice of the stream, with absolute ids":
    check genPrograms(7, 3, 3) == genPrograms(7, 6)[3 ..< 6]
    check genPrograms(7, 4, 0) == genPrograms(7, 4)
    check genPrograms(7, 2, 40) == genPrograms(7, 50)[40 ..< 42]
    check genPrograms(7, 0, 5).len == 0
    for i, p in genPrograms(7, 3, 11): check p.id == 11 + i

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
    echo "k8a-gen seed=", k8aSeed, " first=", k8aFirst, " programs=", k8aCount,
      " runs=", outs.len, " exact=", d.exact, " sampled-unsat=", d.sampledExact,
      " declined=", d.declined, " disagree=", d.disagree
    # One line per run, keyed by the absolute program id: the batch-equivalence
    # check (scripts/k8a-batch-equiv.sh) diffs these between a single run and
    # its batches. Not `k8a-gen`-prefixed, so the step summary stays short.
    for o in outs:
      echo "k8a-verdict prog=", o.progId, " variant=", o.variant, " kind=", o.kind,
        " status=", o.status, " trusted=", o.trusted, " raised=", o.raised
    echo "k8a-gen by shape: ", d.byShape
    echo "k8a-gen declines:\n", declineSummary(outs)
    for f in findings(progs, outs, k8aSeed):
      echo "FINDING ", f
    check findings(progs, outs, k8aSeed).len == 0
    check d.exact + d.sampledExact > 0
    # W3-z E2b: the probes pin into a private directory (the red fixtures and
    # a nightly's thousands of programs must not flood the leg's records), so
    # the cells `construct:k8a-gen/<Shape>` would have no record on the leg.
    # Ship one exact record per shape that proved a sat witness, the verdict
    # the cell's evidence rule accepts (a sampled unsat evidences nothing).
    var shipped: seq[string]
    for r in pinRecords(pinTmp):
      if r.cell.scope == axConstruct and r.cell.key.startsWith("k8a-gen/") and
         r.verdict == pvExact and r.walker == "sxSat" and
         r.cell.key notin shipped:
        shipped.add r.cell.key
        appendPinRecordTo(realPins, r)
    # Programs take shapes round-robin (`id mod` the shape count), so a run of
    # at least one program per shape must reach every shape; a smaller batch
    # covers only the shapes of the ids it holds.
    for sh in Shape:
      var held = false
      for p in progs: held = held or p.shape == sh
      if held: check d.byShape[sh] > 0
