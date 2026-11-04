## RFC-0005 0.9.1 (review R1-06, R1-14). What one witness replay settled, as a
## value, and everything the verdict reads off it.
##
## A replay's child reports how it ended (`ReplayChild`, `replayproc.nim`).
## What that means for a claim needs one fact the child does not have, whether
## the witness rendered faithfully (`lossy`), and is a `ReplayOutcome`. The
## settle (`settleCandidate`, `settleWinner` in `symex.nim`) is handed both,
## as one `ReplayResult` returned by the replay itself: nothing about a replay
## is left on the thread for a later call to read, so no read depends on what
## ran in between.
##
## This module also owns what the result maps to: the `ReplayStatus` a claim
## carries, the `RunDependence` it adds to the verdict, and the `feReplay*`
## hints, whose kind names are taken from the kind, never retyped.

import ./replayproc
import ./types

type
  ReplayOutcome* = enum
    ## RFC-0005 §4.2. The result of executing a witness against the real `fn`.
    ## Not a `bool`, because "refuted" and "could not run" are different facts
    ## with different downstream reporting, and neither is "ran past its bound"
    ## or "ended its process".
    ##
    ## DISTINCT from `SymexFindingStatus.sfReplayMiss` (Phase 14 B5,
    ## `engine/types.nim`): that status diagnoses a persisted REGRESSION SEED
    ## whose choice sequence no longer drives the test runtime onto its marker
    ## (strategy/generator skew, found by `assertCoveredBy` in the seed phase).
    ## `ReplayOutcome` is a VERDICT-TIME fact about a fresh solver witness from
    ## this run. A seed miss says the harness drifted; `roRefuted` says the
    ## model did.
    ##
    ## Review R3 (E1): the zero value is `roDeclined`, so a `ReplayResult`
    ## nothing produced is the replay that did not run (what
    ## `replayResultOf` makes of the zero `ReplayChild`, `reRefused`): never
    ## a confirmation, never trusted.
    roDeclined      ## RFC-0005 S8ct: no child could run this replay, so it did
                    ## not run: the candidate stays sxUnknown, with a
                    ## `feReplayDeclined` hint
    roConfirmed     ## the real fn reached the target on this witness -- the
                    ## target is reachable in reality, whatever the model's taint
    roRefuted       ## the real fn ran to completion (returned, or raised
                    ## something other than the target) on a FAITHFULLY rendered
                    ## witness and did not reach the target: this witness is
                    ## proven spurious (a confirmed model gap). It says nothing
                    ## about OTHER inputs -- the model's havoc symbols (an opaque
                    ## call's return, …) are not part of the witness, so the
                    ## verdict for a refuted candidate is sxUnknown, never sxUnsat
                    ## (§2.3 rule 4)
    roInconclusive  ## replay declined or not faithfully executable: an
                    ## ineligible taint, a witness outside the renderable
                    ## fragment, a target kind outside replay scope, or a lossy
                    ## witness that did not reach the target. The candidate
                    ## stays sxUnknown
    roTimedOut      ## RFC-0005 S8be: the real fn ran past
                    ## `SymexSettings.replayTimeoutMs` on this witness and the
                    ## replay was abandoned -- it may be looping, or only slow.
                    ## Neither confirmed nor refuted: the candidate stays
                    ## sxUnknown, with a `feReplayTimedOut` hint
    roCrashed       ## RFC-0005 S8ct: the real fn ended its child process (an
                    ## exit, a signal, a system exception) on this witness before
                    ## it reached the target. A real fact about a real input, and
                    ## neither a confirmation nor a refutation of the target: the
                    ## candidate stays sxUnknown, with a `feReplayCrashed` hint
                    ## saying how it ended and on what input

  ReplayResult* = object
    ## RFC-0005 0.9.1 (review R1-06). One replay, as the settle reads it: what
    ## it means for the claim, and how its child ended. Returned by the replay
    ## (`replayWitness`, the entry macros' replay pass) and handed to the
    ## settle as an argument. Review R2 (DD6): built only by `replayNotRun`
    ## and `replayResultOf`, so the outcome is always the one the child's
    ## ending means. Review R3 (E1): its zero value (`ReplayResult()`, a
    ## `var` left unset) is `roDeclined` over a child that did not run, the
    ## same value `replayResultOf(ReplayChild(), _)` builds: a replay that
    ## settled nothing, which no settle confirms or marks host-safe by
    ## default.
    fOutcome: ReplayOutcome
    fChild: ReplayChild
      ## The child's report. A replay that ran no child (the witness or target
      ## is outside replay, `replayNotRun`) reports `reRefused` with no reason
      ## and is not run-dependent.

func outcome*(r: ReplayResult): ReplayOutcome = r.fOutcome
func child*(r: ReplayResult): ReplayChild = r.fChild

func replayNotRun*(): ReplayResult =
  ## A replay decided without running anything: `roInconclusive`. Not
  ## `roDeclined` (no child COULD run, which leaves a `feReplayDeclined`
  ## hint): here nothing was to run (an ineligible taint or an out-of-scope
  ## witness or target), so nothing was learned and no hint is left.
  ReplayResult(fOutcome: roInconclusive,
               fChild: ReplayChild(ending: reRefused))

func replayResultOf*(c: ReplayChild; lossy: bool): ReplayResult =
  ## RFC-0005 S8ct. What one child's ending means. A target reached is reached,
  ## whatever happened to the process afterwards (`confirmedEnding` says how it
  ## did). `lossy`: the rendered witness is not the model's, so a miss proves
  ## nothing. Review R2 (LV1): a child whose status was lost (`reLost`) ran,
  ## so a hit it wrote confirms, as any reach does (the hit is written as it
  ## happens, by the real `fn`), and a miss is a crash: it did not finish.
  let outcome =
    if c.ending == reRefused: roDeclined
    elif c.reached: roConfirmed
    else:
      case c.ending
      of reFinished:
        if not c.bound or lossy: roInconclusive else: roRefuted
      of reTimedOut: roTimedOut
      of reExited, reSignalled, reLost: roCrashed
      of reRefused: roDeclined   # unreachable: handled above
  ReplayResult(fOutcome: outcome, fChild: c)

func endsChild*(r: ReplayResult): bool =
  ## Review R2 (DD1). The replay's child did not finish: it exited, was ended
  ## by a signal or a system exception, was killed, or ended with its status
  ## lost. Running the same witness in a process does that to the process,
  ## so a claim whose witness this was carries `Soundness.witnessUnsafe`.
  r.child.ending in {reExited, reSignalled, reTimedOut, reLost}

func killedWhy(r: ReplayResult; fallback: string): string =
  ## Review R2 (LV2). Why a `reTimedOut` child was killed: the reason it
  ## carries (a report flood, `stopped`), or `fallback` (the bound).
  if r.child.why.len > 0: r.child.why else: fallback

func detail*(r: ReplayResult): string =
  ## How the child ended, in words.
  describe(r.child)

func runDependence*(r: ReplayResult): set[RunDependence] =
  ## RFC-0005 0.9.1 (WA-7). What this replay adds to its verdict's
  ## `Soundness.runDependence`. Review R5 (D4b): a pure function of the child:
  ## a `reTimedOut` or `reLost` ending is run-dependent by construction, so no
  ## producer can forget it; `ReplayChild.runDependent` adds the causes an
  ## ending cannot express (see its doc, the one place both are described).
  if r.child.ending in {reTimedOut, reLost} or r.child.runDependent: {rdReplay}
  else: {}

func replayStatus*(r: ReplayResult): ReplayStatus =
  ## The `ReplayStatus` a claim this replay settled carries: only a
  ## confirmation is `rsConfirmed`.
  if r.outcome == roConfirmed: rsConfirmed else: rsUnconfirmed

func hintKind*(o: ReplayOutcome): SymexErrorKind =
  ## The `feReplay*` kind a hint about an unconfirmed replay carries. A
  ## replay that decided nothing (`roInconclusive`) is a decline.
  case o
  of roRefuted: feReplayRefuted
  of roTimedOut: feReplayTimedOut
  of roCrashed: feReplayCrashed
  of roDeclined, roInconclusive, roConfirmed: feReplayDeclined

func tagged(kind: SymexErrorKind; msg: string): SymexErrorInfo =
  ## A replay hint, its text ending with the kind's own name.
  SymexErrorInfo(kind: kind, severity: sevHint,
                 msg: msg & " (" & $kind & ")")

func onInput(input: string): string =
  if input.len > 0: ", on the input " & input else: ""

func claimText*(status: SymexStatusKind; raisedTypeId: string): string =
  "a " & $status & " " & (if status == sxRaised: "claim (raise " & raisedTypeId
                          else: "claim (target hit") & ")"

func confirmedEnding*(r: ReplayResult; status: SymexStatusKind;
                      raisedTypeId: string; input: string): seq[SymexErrorInfo] =
  ## RFC-0005 0.9.1 (WA-2). A confirming replay's child reached the target; this
  ## is how it ended afterwards. A target reached is reached (§5a), so the
  ## verdict stands; but a child that did not finish (`quit`, a raw `exit`, a
  ## signal, the bound) says the witness ends or hangs whatever runs it, so
  ## the claim carries `Soundness.witnessUnsafe` (`endsChild`, which the
  ## settle reads) and the hint this returns, saying how.
  case r.child.ending
  of reFinished, reRefused:
    discard
  of reExited, reSignalled, reLost:
    result.add tagged(feReplayCrashed,
      "replay confirmed " & claimText(status, raisedTypeId) &
      ", then ended its process after reaching the target: " & r.detail &
      onInput(input) &
      ". The target is reached; the witness ends any process that " &
      "runs it, so it is never run in the host (no assertCoveredBy " &
      "splat, no symexForAll seed)")
  of reTimedOut:
    result.add tagged(feReplayTimedOut,
      "replay confirmed " & claimText(status, raisedTypeId) &
      ", then was killed after reaching the target: " &
      r.killedWhy("it ran past replayTimeoutMs") & onInput(input) &
      ". The target is reached; the witness may not terminate, so it " &
      "is never run in the host (no assertCoveredBy splat, no " &
      "symexForAll seed)")

func candidateHint*(r: ReplayResult; status: SymexStatusKind;
                    raisedTypeId: string; input: string): seq[SymexErrorInfo] =
  ## RFC-0005 S10/S8be/S8ct. The hint an unconfirmed candidate's replay leaves
  ## on its `sxUnknown` verdict; none for `roInconclusive` (nothing was
  ## learned) or `roConfirmed` (the claim stands, `confirmedEnding`).
  let candidate = "a " & $status & " candidate (" &
    (if status == sxRaised: "raise " & raisedTypeId else: "target hit") & ")"
  let kind = hintKind(r.outcome)
  case r.outcome
  of roInconclusive, roConfirmed: discard
  of roCrashed:
    result.add tagged(kind,
      "replay of " & candidate &
      " ended its process before reaching the target: " & r.detail &
      onInput(input) &
      ". The real fn crashes on that input; this says nothing of the " &
      "target on any other; neither confirmed nor refuted")
  of roDeclined:
    result.add tagged(kind,
      "replay of " & candidate & " did not run: " & r.detail)
  of roTimedOut:
    result.add tagged(kind,
      "replay of " & candidate & " was killed: " &
      r.killedWhy("the real fn ran past replayTimeoutMs on the " &
                  "solver's witness -- it may not terminate there, or is " &
                  "only slow") & "; neither confirmed nor refuted")
  of roRefuted:
    result.add tagged(kind,
      "replay refuted " & candidate &
      ": the real fn ran on the solver's witness without reaching " &
      "the target -- a confirmed model gap on a scSpurious path")

const lossyWhy = "its witness is lossy (a rendered value is not the " &
  "solver's model: a substituted float or integer, feExtractionFailed, or a " &
  "ref cell, variant or seq field the render cannot reproduce)"

func winnerHint*(r: ReplayResult; claim: string;
                 input: string): seq[SymexErrorInfo] =
  ## RFC-0005 0.9.1 (WA-9). The hint a lossy clean winner's unconfirmed replay
  ## leaves (`claim` is its `claimText`); none on a confirmation.
  if r.outcome == roConfirmed: return
  let why =
    case r.outcome
    of roRefuted:
      "the real fn ran on it without reaching the target"
    of roTimedOut:
      "it was killed: " &
        r.killedWhy("the real fn ran past replayTimeoutMs on it")
    of roCrashed:
      "the real fn ended its process before reaching the target: " &
        r.detail & onInput(input)
    of roDeclined:
      "it did not run: " & r.detail
    of roInconclusive, roConfirmed:
      "replay did not decide it: the real fn ran without reaching the " &
        "target on a render that is not the model, or it was not run (a " &
        "witness shape or target replay does not run, a nil dereference " &
        "on the path, or --panics:on)"
  result.add tagged(hintKind(r.outcome),
    "the clean winner, " & claim & ", reaches the target, but " & lossyWhy &
    ", and its replay did not confirm it: " & why &
    ". Not trusted (rsUnconfirmed)")

func winnerUnreplayedHint*(claim: string): SymexErrorInfo =
  ## RFC-0005 0.9.1 (WA-9). `SymexSettings.replay = false`: a lossy clean
  ## winner nothing could confirm.
  tagged(feReplayDeclined,
    "the clean winner, " & claim & ", reaches the target, but " & lossyWhy &
    ", and replay is off (SymexSettings.replay = false), so nothing " &
    "confirmed it. Not trusted (rsUnconfirmed)")
