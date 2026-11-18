## RFC-0016 K8b: what the three family suites (`tsymex_0016_k8b_<family>`)
## share after their batch has run: the findings (native differential and
## metamorphic, K8a-gen's `findings`), the cells-exercised records, and the
## pairwise figure read back from those records against the floor.
import std/os
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
  figure*: PairFigure
  floorProblems*: seq[string]
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
  result.floorProblems = floorProblems(result.figure, loadFloor(), {fam})

proc report*(fam: FamilyScope; seed, count: int; r: FamilyRun;
             outs: seq[GenOutcome]): string =
  result = "k8b " & scopePrefix[fam] & " seed=" & $seed & " programs=" &
    $count & " runs=" & $outs.len & " exact=" & $r.exact & " declined=" &
    $r.declined & " disagree=" & $r.disagree & " pairwise=" &
    $r.figure[fam].covered & "/" & $r.figure[fam].total & "\n" &
    "k8b declines:\n" & declineSummary(outs)
  for f in r.findings: result.add "FINDING " & f & "\n"
