## RFC-0016 K8b: what the family suites (`tsymex_0016_k8b_<family>_<half>`,
## `familyFiles`) share: each runs one slice of its family's seeded stream
## (`familyHalf`), reports the findings (native differential and metamorphic,
## K8a-gen's `findings`), and writes the cells-exercised records. The pairwise
## figure is judged against the floor by K1 (`tsymex_0016_universe`), over
## the union of the family's halves (`exercisedJoinProblems`); a half reports
## its own share.
import std/[os, unittest, sets]
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen

func outcomeName*(k: OutKind): string =
  case k
  of okExact: "exact"
  of okDecline: "declined"
  of okDisagree: "disagree"

proc exercisedOf*(progs: seq[Prog]; outs: seq[GenOutcome]; seed: int;
                  file: string): seq[ExercisedRecord] =
  ## One record per run (a program under one variant): the family, the
  ## program's dimension cells, and how it ended. A run whose verdict differs
  ## from its original's (a metamorphic finding) is a disagreement too.
  for o in outs:
    var p: Prog
    for q in progs:
      if q.id == o.progId: p = q
    var outcome = outcomeName(o.kind)
    if o.variant != "orig" and o.kind == okExact:
      for q in outs:
        if q.progId == o.progId and q.variant == "orig" and q.trusted and
           (q.status != o.status or q.raised != o.raised):
          outcome = "disagree"
    result.add ExercisedRecord(testFile: file, variant: o.variant,
      outcome: outcome, family: familyOf(o.shape), seed: seed,
      progId: o.progId, cells: cellsOf(FamilyScope(familyOf(o.shape)), p.fam))

type FamilyRun* = object
  findings*: seq[string]
  figure*: PairFigure   ## this half's share; the floor is on the union (K1)
  exact*, declined*, disagree*: int

proc runFamily*(fam: FamilyScope; progs: seq[Prog]; outs: seq[GenOutcome];
                seed: int; file, realPins: string): FamilyRun =
  ## Writes the cells-exercised records to the leg's record directory (where
  ## K1 reads them) and to a private one, and computes this family's figure
  ## from the private copy, so a stale record elsewhere cannot raise it.
  result.findings = findings(progs, outs, seed)
  let recs = exercisedOf(progs, outs, seed, file)
  for r in recs:
    case r.outcome
    of "exact": inc result.exact
    of "declined": inc result.declined
    else: inc result.disagree
  writeExercisedTo(realPins, recs)
  let priv = getTempDir() / ("k8b_" & $fam & "_" & $getCurrentProcessId())
  removeDir(priv)
  writeExercisedTo(priv, recs)
  let back = loadExercised(priv)
  removeDir(priv)
  doAssert back.len == recs.len, "the records read back are the records written"
  result.figure = pairwiseFigure(back)

proc report*(fam: FamilyScope; seed, count: int; r: FamilyRun;
             outs: seq[GenOutcome]): string =
  result = "k8b " & scopePrefix[fam] & " seed=" & $seed & " programs=" &
    $count & " runs=" & $outs.len & " exact=" & $r.exact & " declined=" &
    $r.declined & " disagree=" & $r.disagree & " pairwise=" &
    $r.figure[fam].covered & "/" & $r.figure[fam].total & "\n" &
    "k8b declines:\n" & declineSummary(outs)
  for f in r.findings: result.add "FINDING " & f & "\n"

template familyHalf*(family: static FamilyScope; tag: static string;
                     runBatch: untyped; file: static string;
                     seed, first, count, streamLen: static int) =
  ## One half of a family's batch: programs `[first, first + count)` of the
  ## family's stream (seed `seed`), each with one rotating relation, through
  ## `symexFind` and the native differential. `streamLen` is the whole
  ## stream both halves cover at the gate's counts. `runBatch` is
  ## `runBatch_<tag>`, the proc `genFamilyBatch` emits.
  let realPins = pinDir()
  let pinTmp = getTempDir() / ("k8b_" & tag & "_" & $getCurrentProcessId())
  createDir(pinTmp)
  putEnv("NELLI_PIN_DIR", pinTmp)

  const progs = genFamily(family, seed, count, first)
  genFamilyBatch(progs, tag)

  suite "K8b " & scopePrefix[family] & " programs " & $first & ".." &
        $(first + count - 1):
    test "the stream is deterministic, prefix-stable, one value per dimension":
      check genFamily(family, 7, 5) == genFamily(family, 7, 9)[0 ..< 5]
      check genFamily(family, 7, 3, 4) == genFamily(family, 7, 7)[4 ..< 7]
      check progs == genFamily(family, seed, first + count)[first ..< first + count]
      for p in progs:
        check familyOf(p.shape) == family
        check p.fam.len == famDims[family].len

    test "every relation is a different source, and the halves run each one":
      for p in progs:
        let o = render(p, "g", twNone)
        for tw in applicable(p):
          check render(p, "g", tw) != o
      let whole = genFamily(family, seed, streamLen)
      var ran, all: set[Twin]
      for p in whole:
        for tw in applicable(p): all.incl tw
      for c in familyCases(whole): ran.incl c.tw
      check ran == all + {twNone}

    test "generated programs and their relations agree with native":
      let outs = runBatch()
      let r = runFamily(family, progs, outs, seed, file, realPins)
      echo report(family, seed, count, r, outs)
      check r.findings.len == 0
      check r.exact > 0

# --- RFC-0016 K8b (INT-56): the admission-axis suites -------------------------

proc axisExercisedOf*(progs: seq[Prog]; outs: seq[GenOutcome]; seed: int;
                      file: string): seq[ExercisedRecord] =
  ## One record per run: the axis, the rows the program packs, and how it
  ## ended (a metamorphic difference is a disagreement, as for a family).
  for o in outs:
    var p: Prog
    for q in progs:
      if q.id == o.progId: p = q
    var outcome = outcomeName(o.kind)
    if o.variant != "orig" and o.kind == okExact:
      for q in outs:
        if q.progId == o.progId and q.variant == "orig" and q.trusted and
           (q.status != o.status or q.raised != o.raised):
          outcome = "disagree"
    var cells: seq[CellKey]
    for k in p.rows: cells.add CellKey(scope: p.axis, key: k)
    result.add ExercisedRecord(testFile: file, variant: o.variant,
      outcome: outcome, family: p.axis, seed: seed, progId: o.progId,
      cells: cells)

template axisBatch*(axis: static AxisScope; tag: static string;
                    runBatch: untyped; file: static string;
                    seed, first, count, per: static int) =
  ## Programs `[first, first + count)` of the axis's stream (`genAxis`), each
  ## packing `per` rows, with one rotating relation, through `symexFind` and
  ## the native differential; the cells-exercised records go to the leg's
  ## record directory, where K1 judges the axis figure (`axisJoinProblems`).
  let realPins = pinDir()
  let pinTmp = getTempDir() / ("k8b_" & tag & "_" & $getCurrentProcessId())
  createDir(pinTmp)
  putEnv("NELLI_PIN_DIR", pinTmp)

  const progs = genAxis(axis, seed, count, per, first)
  genFamilyBatch(progs, tag)

  suite "K8b axis " & scopePrefix[axis] & " programs " & $first & ".." &
        $(first + count - 1):
    test "the axis stream is deterministic and every relation is a new source":
      check genAxis(axis, 7, 3, per) == genAxis(axis, 7, 5, per)[0 ..< 3]
      for p in progs:
        check p.rows.len == min(per, axisSnippets[axis].len)
        let o = render(p, "g", twNone)
        for tw in applicable(p):
          check render(p, "g", tw) != o

    test "generated programs and their relations agree with native":
      let outs = runBatch()
      let fs = findings(progs, outs, seed)
      let recs = axisExercisedOf(progs, outs, seed, file)
      writeExercisedTo(realPins, recs)
      var exact, declined, disagree: int
      var rowsOk: HashSet[string]
      for r in recs:
        case r.outcome
        of "exact":
          inc exact
          for c in r.cells: rowsOk.incl c.key
        of "declined": inc declined
        else: inc disagree
      echo "k8b axis ", scopePrefix[axis], " seed=", seed, " programs=", count,
        " runs=", outs.len, " exact=", exact, " declined=", declined,
        " disagree=", disagree, " rows exercised here=", rowsOk.len, "\n",
        "k8b declines:\n", declineSummary(outs)
      for f in fs: echo "FINDING ", f
      check fs.len == 0
      check exact > 0
