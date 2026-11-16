## nelli/smt/replay_settle -- the verdict-side settle of replay results
## (RFC-0005 S10): the candidate accessors, `settleCandidate`,
## `settleWinner`, the lossy-winner gates and the `ProcValueLift` record the
## settle reads. Generated code names these by `bindSym`.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. `candidateLossy` is
## re-exported by `symex.nim`.

import std/[macros, sets, tables, algorithm, options, strutils, importutils]
import ../choice
import ./dsl
import ./replayresult

# ---- Replay wired into the verdict (RFC-0005 S10, §2.3 rule 3) ---------------
#
# `runSymex` ends at `decideVerdict`, which cannot apply rule 3 (replay needs
# `fn`, and `runSymex` is runtime code with none -- §4.2 "Plumbing"). So a run
# whose only SAT lies on an `scSpurious`-tainted path returns `sxUnknown` with
# its SOLVED models in `RawResult.candidates` (`SatCandidate`), and the entry
# macro settles them here, after `runSymex` returns and BEFORE any
# `SymexResult`/`SymexFinding` is built or anything is persisted.
#
# CANDIDACY IS UNSPELLABLE AS SAT. A `SatCandidate` is not a `RawResult` and
# has no witness branch; its model is the private `input` field. This module
# alone reads it (`privateAccess`), through the two procs below, both
# private and reached from generated code only via `bindSym` inside
# `emitRunSymexReplayed`:
#   * `candidateInput` -- the model, for rendering the witness to REPLAY;
#   * `settleCandidate` -- the ONLY constructor of a `sxSat`/`sxRaised`
#     `RawResult` from a candidate, and only on `roConfirmed`.
# And `emitRunSymexReplayed` is the only place in this module that emits a
# `runSymex` call (pinned by `tsymex_rfc0005_s10_replay_verdict`), so an entry
# macro cannot obtain a `RawResult` that skipped the settle: forgetting replay
# is not expressible, and even a hand-rolled caller of `runSymex` elsewhere
# can only ever see a candidate's metadata, never a witness to report.
#
# REPLAY HAZARDS (§4.2), as contained here:
#   * Contract change -- `symexFind`/`symexFindAllWitnesses`/`symexForAll` now
#     EXECUTE `fn` at verdict time, on solver-chosen inputs, whenever a run's
#     only SAT is a replay-eligible candidate. Its side effects happen for
#     real, in the caller's process (a `scSpurious` path is tainted precisely
#     because it ran through something unmodelled, often an effect). Nothing
#     runs for a clean verdict, an `sxUnsat`, or an ineligible candidate.
#   * Link/load -- because the settle references `fn`, `fn` and its callees
#     are code-generated, linked and loaded into the caller's binary even
#     when no candidate is ever replayed (an undefined `importc`, a missing
#     `dynlib` such as `std/re`'s PCRE, now fails the build or start-up).
#     Not containable at runtime; `SymexSettings.replay = false` (static)
#     emits no reference to `fn` at all -- the pre-S10 verdict.
#   * Non-termination -- bounded by the eligibility gate, which never runs a
#     `dcFabricated` (k-unroll survivor) witness, and by `replayTimeoutMs`: the
#     replay's child is killed past it (`roTimedOut`).
#   * Defects -- caught by the replay frame and classified; under
#     `--panics:on` nothing is replayed (`replayInScope`); a raw-`ptr`
#     witness is never executed (`witnessFidelity`); a candidate whose path
#     went through the walker's nil-dereference edge, escaping or caught,
#     is never executed (RFC-0005 S8k: `nilDerefOnPath`, and a
#     `NilAccessDefect` raise target is out of `replayInScope`) -- the
#     walker models that edge as a raise, the default build SIGSEGVs.
#   * Crashes -- RFC-0005 S8ct: whatever else the real `fn` does on the witness
#     (SIGSEGV, stack overflow, `quit`, `abort`, memory corruption) ends its
#     child and is reported (`roCrashed`, `feReplayCrashed`), never `sxUnsat`.
#   * Capture reentrancy -- each replay runs in its own nested capture frame
#     (`engine/markers.nim`), so a user's enclosing `assertCoveredBy`
#     capture neither loses hits nor sees replay's.
#   * Bounded replays -- candidates are replayed in discovery order, `sxSat`
#     claims before `sxRaised` claims (ADR-0012 D2's precedence, as rules
#     1-2), and the settle STOPS at the first `roConfirmed`: at most one
#     confirming execution, plus one per earlier refuted/declined candidate.
#
# THE TWO BLANKET VETOES (§2.5) are not consulted: they distrust the MODEL
# (a cap or closure decline anywhere), and a confirmed replay is a fact about
# the REAL `fn` -- it reached the target on a concrete input -- that no model
# defect can make false. Rules 1-2 still precede rule 3 (a clean winner means
# the raw status is already `sxSat`/`sxRaised`, and the settle is skipped).
#
# RFC-0005 0.9.1 (WA-9) -- ONE exception: a clean winner whose witness renders
# lossily (`winnerLossy`). Its path reaches the target, but the witness it
# reports is not the model's, so it is replayed as the pass's one job and
# settled by `settleWinner`: `rsConfirmed` on a confirmation, else
# `rsUnconfirmed` (status unchanged, not `trusted()`, with a hint).

privateAccess(SatCandidate)

proc candidateInput*(c: SatCandidate): auto =
  ## RFC-0005 S10. The candidate's model, for the replay codegen to render
  ## into `fn`'s parameter tuple. Private: see the section comment.
  c.input

func candidateLossy*(c: SatCandidate): bool =
  ## RFC-0005 S10. True when the candidate's own extraction substituted a
  ## value (`feExtractionFailed`: a float leaf that did not resolve to a
  ## numeral was rendered `0.0`), so the rendered witness is not the model
  ## even where its shape is faithful -- replay's `extraLossy`.
  for e in c.errors:
    if e.kind == feExtractionFailed: return true
  false

type ProcValueLift* = object
  ## RFC-0016 W3-z R7. What the replayed run's proc-valued variables held
  ## (`emitProcValueLift`): `named`, every variable the walk reported
  ## (`RawResult.procValueSites`) held, when the run started, a routine of
  ## the replay's footprint, and no code the run may execute writes it but
  ## with a routine named there, while every proc value the run's state holds
  ## is one of the footprint's routines (so no code the scan did not read can
  ## run); `kinds`, what those routines' bodies may reach
  ## (`routineUndefinedKinds`). Not `named`: nothing is replaced.
  named*: bool
  kinds*: set[UbKind]
  why*: string
    ## RFC-0016 W3-z R10. Not `named`: why, naming what (the hint a confirmed
    ## claim whose kinds stay carries, `procValueUnliftedHint`).

func liftedUndefined(c: SatCandidate; lift: ProcValueLift): set[UbOrdinal] =
  ## RFC-0016 W3-z R7. The confirmed claim's `witnessUndefined`: the kinds only
  ## a call through a proc-valued variable put there
  ## (`witnessUndefinedViaOnly`, "may be undefined": the variable may hold any
  ## routine of its type) are replaced by what the routines the replayed run's
  ## variables held reach. Run-dependent by construction: it reads the state
  ## the replay ran from.
  if not lift.named or c.witnessUndefinedViaOnly == {}:
    return c.witnessUndefined
  (c.witnessUndefined - c.witnessUndefinedViaOnly) + ubOrdinals(lift.kinds)

func procValueUnliftedHint(c: SatCandidate; lift: ProcValueLift): SymexErrorInfo =
  ## RFC-0016 W3-z R10. A confirmed claim whose kinds a call through a
  ## module-level proc-valued variable put there (`witnessUndefinedViaOnly`)
  ## stay: the settle could not name the routine the variable held
  ## (`ProcValueLift.why`). The re-executed child's decline is the same kind.
  var kinds: seq[string]
  for o in c.witnessUndefinedViaOnly: kinds.add $UbKind(ord(low(UbKind)) + int(o))
  let why = if lift.why.len > 0: lift.why else: "no reason was recorded"
  SymexErrorInfo(kind: feReplayDeclined, severity: sevHint,
    msg: "replay confirmed the claim, but did not name the routine a " &
         "proc-valued variable held, so what the call through it may reach " &
         "stays (" & kinds.join(", ") & "): " & why & " (" &
         $feReplayDeclined & ")")

proc settleCandidate*(raw: RawResult; c: SatCandidate;
                     replayed: ReplayResult; input: string;
                     lift: ProcValueLift): RawResult =
  ## RFC-0005 S10 (§2.3 rule 3). Applies ONE candidate's replay to the
  ## `sxUnknown` result `raw`, by its `outcome`:
  ##   * `roConfirmed` -- the verdict becomes the candidate's claim
  ##     (`sxSat`/`sxRaised`) carrying its model as the witness, its
  ##     `pathTaint` (still `scSpurious`, with RFC-0005 S11's `replay =
  ##     rsConfirmed` beside it -- the one writer of `rsConfirmed`) and its
  ##     own extraction errors after the run's. RFC-0005 0.9.1 (WA-2): a child
  ##     that ended or hung after the target sets `witnessUnsafe`, with a
  ##     `feReplayCrashed`/`feReplayTimedOut` hint (`confirmedEnding`). No
  ##     `diagnostics`: every other finding is either a candidate nobody
  ##     confirmed or a clean one an unplaced decline suppressed
  ##     (`decideVerdict`'s `reachUnknown`, RFC-0005 S9).
  ##   * any other -- stays `sxUnknown` (a refuted candidate too, by rule 4:
  ##     the enlarged program reaches the target; never `sxUnsat`), with the
  ##     replay's hint (`candidateHint`): none for `roInconclusive`.
  ## Either way the replay's run-dependence joins the verdict's (WA-7).
  ## Private (the only candidate -> verdict constructor); see the section
  ## comment.
  result = raw
  if replayed.outcome != roConfirmed:
    result.errors.add candidateHint(replayed, c.status, c.raisedTypeId, input)
    result.soundness.runDependence.incl replayed.runDependence
    return
  case c.status
  of sxSat:
    result = RawResult(status: sxSat, witness: c.input)
  of sxRaised:
    result = RawResult(status: sxRaised, raisedTypeId: c.raisedTypeId,
                       isDefect: c.isDefect, raisedMsg: c.raisedMsg,
                       raisedWitness: c.input)
  of sxUnsat, sxUnknown:
    return raw    ## not a claim; `toCandidate` never builds one
  result.abstractions = raw.abstractions
  result.obligations  = raw.obligations
  result.callStats    = raw.callStats
  let ended = confirmedEnding(replayed, c.status, c.raisedTypeId, input)
  result.errors       = raw.errors & c.errors & ended   # RFC-0005 0.9.1 WA-2
  # RFC-0016 W3-z R10: kinds a call through a proc-valued variable put there,
  # which the settle could not replace, say why (never a bare kind).
  if not lift.named and c.witnessUndefinedViaOnly != {}:
    result.errors.add procValueUnliftedHint(c, lift)
  # RFC-0005 S11: the claim's soundness -- its own path, the run's
  # coordinate (re-derived: the candidate's extraction errors are now part
  # of this result's error list), and the replay that confirmed it.
  result.soundness    = Soundness(pathTaint: c.pathTaint,
                                  buildSegment: raw.soundness.buildSegment,   # RFC-0016 K5a
                                  buildRow: raw.soundness.buildRow,
                                  witnessUndefined: liftedUndefined(c, lift),   # RFC-0016 W1-d3, W3-z R7
                                  runTaint: runTaintOf(result.errors),
                                  replay: replayed.replayStatus,
                                  witnessUnsafe: c.witnessUnsafe or replayed.endsChild,   # RFC-0016 WA-B (S4)
                                  runDependence: raw.soundness.runDependence +
                                                 replayed.runDependence)
  result.bounds       = raw.bounds
  result.undefined    = raw.undefined   # RFC-0016 W3-z R3: the run's own findings
  result.candidates   = raw.candidates
  result.annotationViolations = raw.annotationViolations   # RFC-0005 S8

func winnerLossy*(raw: RawResult; staticLossy: bool): bool =
  ## RFC-0005 0.9.1 (WA-9). A clean winner (rules 1-2 decided `sxSat` or
  ## `sxRaised` without replay) whose witness renders lossily: the shape is
  ## `wfLossy` (`staticLossy`, decided at macro time), or the run's extraction
  ## substituted a value (`feExtractionFailed`). The winner's path reaches the
  ## target, but the witness reported for it is not the model's, so nothing
  ## yet says that witness reaches it.
  if raw.status notin {sxSat, sxRaised} or raw.soundness.replay != rsNotNeeded or
     scSpurious in raw.soundness.pathTaint:
    return false
  if staticLossy: return true
  for e in raw.errors:
    if e.kind == feExtractionFailed: return true
  false

proc winnerCandidate*(raw: RawResult): SatCandidate =
  ## RFC-0005 0.9.1 (WA-9). A lossy clean winner as the one job of the replay
  ## pass, so it is replayed by the same codegen a candidate is. Its path is
  ## clean (replay-eligible); its extraction errors make `candidateLossy` true
  ## where the run substituted a value. Settled by `settleWinner`, never by
  ## `settleCandidate`.
  result = SatCandidate(status: raw.status, pathTaint: {},
                        nilDerefOnPath: raw.nilDerefOnPath)
  for e in raw.errors:
    if e.kind == feExtractionFailed: result.errors.add e
  case raw.status
  of sxSat: result.input = raw.witness
  of sxRaised:
    result.input = raw.raisedWitness
    result.raisedTypeId = raw.raisedTypeId
    result.isDefect = raw.isDefect
    result.raisedMsg = raw.raisedMsg
  of sxUnsat, sxUnknown: discard

func rawClaimText(raw: RawResult): string =
  claimText(raw.status, (if raw.status == sxRaised: raw.raisedTypeId else: ""))

proc settleWinner*(raw: RawResult; replayed: ReplayResult;
                  input: string): RawResult =
  ## RFC-0005 0.9.1 (WA-9). Applies the replay of a lossy clean winner's
  ## witness. The status stands either way: the clean path reaches the
  ## target. `roConfirmed` makes it `rsConfirmed` (with WA-2's ending); any
  ## other outcome leaves it `rsUnconfirmed`, not `trusted()`, with a hint
  ## saying why (`winnerHint`). The replay's run-dependence joins the
  ## verdict's (WA-7).
  result = raw
  result.soundness.replay = replayed.replayStatus
  result.soundness.runDependence.incl replayed.runDependence
  # Review R2 (DD1): a child that did not finish makes the witness unsafe to
  # run in the host, confirmed or not, as a typed fact the cache stores.
  # RFC-0016 WA-B (S4): the claim's own flag (a crash claim's) is not the
  # replay's to clear.
  result.soundness.witnessUnsafe = raw.soundness.witnessUnsafe or replayed.endsChild
  if replayed.outcome == roConfirmed:
    let tid = if raw.status == sxRaised: raw.raisedTypeId else: ""
    result.errors.add confirmedEnding(replayed, raw.status, tid, input)
  else:
    result.errors.add winnerHint(replayed, rawClaimText(raw), input)

proc gateLossyWinner*(raw: RawResult; staticLossy: bool;
                     settings: SymexSettings): RawResult =
  ## RFC-0016 K10b (section 9.1 item 3). The second walk needs the model's
  ## pins, not the rendered value, so a lossy winner (`winnerLossy`: the
  ## shape renders lossily, or the run substituted a value) is tail-checked
  ## like any other (`verifyTailDefined`) and stays trusted when its tail is
  ## defined. It "cannot be followed" only where a pin is genuinely missing
  ## (`RawWitness.pinsComplete` false: a parameter or leaf the pins skipped),
  ## and then it fails closed: `ubTailUnverified` joins `witnessUndefined`,
  ## the status stands, the verdict is not `trusted()` and the replay that
  ## follows cannot lift it. Gate off: `raw` unchanged.
  result = raw
  if settings.wholeRunDefinedness and raw.status == sxSat and
     not raw.witness.pinsComplete and winnerLossy(raw, staticLossy):
    result.soundness.witnessUndefined.incl ubOrdinals({UbKind(ubTailUnverified)})

proc markLossyWinnerUnreplayed*(raw: RawResult; staticLossy: bool): RawResult =
  ## RFC-0005 0.9.1 (WA-9). `SymexSettings.replay = false`: a lossy clean
  ## winner cannot be confirmed, so it is `rsUnconfirmed`.
  result = raw
  if winnerLossy(raw, staticLossy):
    result.soundness.replay = rsUnconfirmed
    result.errors.add winnerUnreplayedHint(rawClaimText(raw))
