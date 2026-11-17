## nelli/smt/run_replayed -- the entry macros' replayed-search body: the code
## `emitRunSymexReplayed` emits to run symex, replay each candidate witness
## and settle the winner (RFC-0005 S10).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The generated code names
## the settle helpers (`replay_settle`) and the lift (`proc_lift`) by
## `bindSym`, so they are resolved from this module's scope.

import std/[macros, sets, tables, options]
import ../choice
import ./dsl
import ./replayresult
import ./replayproc
import ./replay_settle
import ./proc_lift
import ./witness_emit
import ./witness_fidelity
import ./replay_emit

proc emitRunSymexReplayed*(fn: NimNode; params: seq[IRParam];
                          prog, target, settings: NimNode;
                          replayOn: bool;
                          procValueKeys: seq[string] = @[]): NimNode =
  ## RFC-0005 S10. THE `runSymex` call of every entry macro (`symexFind`,
  ## and `symexFindAllWitnesses` -- hence `symexForAll`): emits a block
  ## expression of type `RawResult` that runs the walker and then settles
  ## its candidates by replay (rule 3), so neither consumer can see a raw
  ## result that skipped the settle. `prog`/`target`/`settings` are the
  ## `SymexProgram`, `SymexTarget` and `SymexSettings` expressions the
  ## caller would have passed to `runSymex`.
  ##
  ## `replayOn` is the caller's STATIC `SymexSettings.replay`. Off, the
  ## emitted expression is the bare `runSymex` call: no reference to `fn` is
  ## generated at all, so `fn` and its callees need not link or load (the
  ## opt-out for a SUT that is analysable but not executable in the test
  ## binary), and every candidate stays `sxUnknown` -- the pre-S10 verdict.
  ##
  ## Settles an `sxUnknown` (rules 1-2 already produced any clean
  ## verdict; `sxUnsat` has no candidates), and (RFC-0005 0.9.1, WA-9) a clean
  ## winner with a lossy witness (`winnerLossy`, `settleWinner`). For each
  ## candidate, in
  ## discovery order, `sxSat` claims first: renders its model through the
  ## same `emitTyAndReader` readers the verdict uses, replays it
  ## (`emitReplayWitness`) against the search target (an `sxSat` claim) or
  ## `tRaisedExn(<its raised type>)` (an `sxRaised` claim -- the claim that
  ## exact type escapes `fn`), and hands the `ReplayResult` it returns to
  ## `settleCandidate`; stops at the first confirmation. RFC-0016 W4 perf:
  ## the candidates' replays run inside the run, through the
  ## `CandidateReplay` this body hands `runSymex`, so the run walks the tail
  ## of the confirmed one only (W3-z R2); the settle folds their recorded
  ## outcomes, in the order they ran, once the run returns. Nothing about a
  ## replay is read off the thread (review R1-06): what the settle and a
  ## later save need of it, the run-dependence included, is on the value.
  let rawId     = genSym(nskLet, "rawPreReplay")
  # RFC-0005 0.9.1 (WA-9): whether every witness of `fn` renders lossily.
  let staticLossy = newLit(paramsFidelity(params) == wfLossy)
  # RFC-0016 K10b: a lossy witness cannot be followed past the label, so under
  # the whole-run gate it fails closed (`ubTailUnverified`) before any replay.
  let gateLossySym = bindSym"gateLossyWinner"
  # RFC-0016 W4 perf: with replay on, the run is handed the candidates'
  # replay (`CandidateReplay`, below) as its fourth argument.
  let cbId = genSym(nskLet, "candidateReplay")
  var runCall = quote do:
    runSymex(`prog`, `target`, `settings`)
  if runCall.kind == nnkStmtList: runCall = runCall[0]
  if not replayOn:
    let markSym = bindSym"markLossyWinnerUnreplayed"
    return quote do:
      `markSym`(`gateLossySym`(`runCall`, `staticLossy`, `settings`),
                `staticLossy`)
  runCall.add cbId
  let witId  = genSym(nskLet, "candRawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(params, witId)
  let settledId = genSym(nskVar, "settled")
  let tgtId     = genSym(nskLet, "searchTarget")
  let candId    = genSym(nskParam, "cand")
  let idxId     = genSym(nskParam, "candIdx")
  let replayOneId = genSym(nskProc, "replayOne")
  let recordsId = genSym(nskVar, "replays")
  let recId     = genSym(nskForVar, "rec")
  let cbTy      = bindSym"CandidateReplay"
  let typedId   = genSym(nskLet, "candWitness")
  let replayedId = genSym(nskLet, "replayed")
  let replayTgt = genSym(nskLet, "replayTarget")
  let inputSym  = bindSym"candidateInput"
  let settleSym = bindSym"settleCandidate"
  let winnerSettleSym = bindSym"settleWinner"
  let lossyWinSym = bindSym"winnerLossy"
  let winnerCandSym = bindSym"winnerCandidate"
  let liftId = genSym(nskLet, "procValueLift")   # RFC-0016 W3-z R7
  let liftExpr = emitProcValueLift(fn, procValueKeys,
                                   newDotExpr(rawId, ident"procValueSites"))
  # A zero-param `fn` has the empty tuple `()` as its witness, which is a
  # value but not a type annotation -- so annotate only a non-empty one.
  let typedDecl =
    if params.len == 0:
      quote do:
        let `typedId` {.used.} = `witnessTup`
    else:
      quote do:
        let `typedId` {.used.}: `tupleTy` = `witnessTup`
  # RFC-0005 S8ct: a re-executed child is handed the solver's model, and renders
  # it as this process does, with no aliasing to carry across.
  var child = ChildWitness()
  when replayReexecs:
    let childRaw = genSym(nskVar, "childRaw")
    let childWit = genSym(nskLet, "childWitness")
    let (childTy, childTup) = emitWitnessTuple(params, childRaw)
    child = ChildWitness(blob: witId, blobTy: newCall(bindSym"typeof", witId),
                         blobId: childRaw, witId: childWit,
                         decl:
                           if params.len == 0:
                             quote do:
                               let `childWit` {.used.} = `childTup`
                           else:
                             quote do:
                               let `childWit` {.used.}: `childTy` = `childTup`)
  let replay = emitReplayWitness(fn, params, typedId, replayTgt,
    newDotExpr(candId, ident"pathTaint"),
    newCall(bindSym"candidateLossy", candId),
    newDotExpr(candId, ident"nilDerefOnPath"),
    newDotExpr(settings, ident"replayTimeoutMs"),   # RFC-0005 S8be
    child)
  # RFC-0016 W4 perf: the candidates are replayed inside the run
  # (`CandidateReplay`), which walks the tail of the one a replay confirms
  # while its context is live, and settled here, in the order they ran, once
  # it returns. A lossy clean winner is replayed after the run, as before.
  result = quote do:
    block:
      let `tgtId`: SymexTarget = `target`
      proc `replayOneId`(`candId`: SatCandidate):
          tuple[replayed: ReplayResult; shown: string] =
        let `replayTgt`: SymexTarget =
          if `candId`.status == sxSat: `tgtId`
          else: tRaisedExn(`candId`.raisedTypeId)
        let `witId` {.used.} = `inputSym`(`candId`)
        `typedDecl`
        let `replayedId` = `replay`
        (replayed: `replayedId`,
         shown: (when compiles($`typedId`): $`typedId` else: ""))
      var `recordsId`: seq[tuple[i: int; replayed: ReplayResult; shown: string]]
      let `cbId`: `cbTy` = proc (`idxId`: int; c: SatCandidate): bool =
        let one = `replayOneId`(c)
        `recordsId`.add (i: `idxId`, replayed: one.replayed, shown: one.shown)
        one.replayed.outcome == roConfirmed
      let `rawId` = `gateLossySym`(`runCall`, `staticLossy`, `settings`)
      var `settledId` = `rawId`
      # RFC-0005 0.9.1 (WA-9): a lossy clean winner is the pass's one job.
      if `lossyWinSym`(`rawId`, `staticLossy`):
        let one = `replayOneId`(`winnerCandSym`(`rawId`))
        `settledId` = `winnerSettleSym`(`settledId`, one.replayed, one.shown)
      elif `rawId`.status == sxUnknown and `rawId`.candidates.len > 0 and
           `recordsId`.len > 0:
        let `liftId` = `liftExpr`
        for `recId` in `recordsId`:
          `settledId` = `settleSym`(`settledId`, `rawId`.candidates[`recId`.i],
                                    `recId`.replayed, `recId`.shown, `liftId`)
      `settledId`
