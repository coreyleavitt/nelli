## RFC-0005 S11 (§8.1, §8.2). The soundness vocabulary of a symex verdict,
## in a leaf module that imports nothing: the lattice (`SoundnessChannel`,
## `Taint`, `DegradeClass`), the per-result record (`ReplayStatus`,
## `Soundness`) and the annotation-violation channel.
##
## Why a leaf. RFC-0005 §8.2 pins a placement constraint: the lattice lives
## where no z3 is imported, so RFC-0007's trace engine can share it. S1 met
## that by declaring it in `smt/types.nim`. S11 has to put the same values on
## `SymexFinding` (`engine/types.nim`), the Z3-free record the terminal report
## and its renderers read -- and `engine/types.nim` is documented to stay free
## of the `smt/types` dependency (the IR, 5k lines). So the types moved here;
## `smt/types.nim` imports and re-exports this module, so every name is still
## reachable exactly where it was, and the module is still Z3-free.

type
  SymexAnnotation* = enum
    ## RFC-0005 S8 (§13.3, i3 -- Corey 2026-09-26). A user annotation symex
    ## honours on the strength of the user's promise.
    saSymexTransparent  ## `{.symexTransparent.}`: "this call is void and
                        ## observably inert -- drop it"

  AnnotationViolationKind* = enum
    ## RFC-0005 S8 (§13.3). WHICH promise of the annotation the call site
    ## contradicts.
    avResultUsed    ## the call's RESULT is used (expression position), but
                    ## the pragma is honoured only in statement position
                    ## (was `feTransparentResultUsed`, issue #163 review R10)
    avArgNotInert   ## statement position, but an argument is not provably
                    ## inert -- a `var`/`ref`/`ptr`/possibly-ref-carrying
                    ## argument the callee could write through (was
                    ## `feTransparentArgNotInert`, issue #163 review R7)

  AnnotationViolation* = object
    ## RFC-0005 S8 (§13.3, i3 resolved by Corey 2026-09-26). A user's
    ## annotation claim that the parser found to be FALSE at a call site.
    ## NOT a decline: nothing is approximated because of it -- the call falls
    ## back to opaque handling, whose walk-time `feOpaqueCallUnmodelled`
    ## degrade taints every path through it (the soundness), so this record
    ## is verdict-NEUTRAL by construction: no `classOf`, no `DeclineScope`,
    ## no taint, never read by the verdict. It is
    ## error-severity in spirit -- the user's code carries a wrong promise --
    ## and rides its own channel (`SymexProgram.annotationViolations` ->
    ## `RawResult`/`SymexResult.annotationViolations`) so it stays loud
    ## without masquerading as a modelling gap. S11 renders it.
    pragma*: SymexAnnotation         ## the annotation that was violated
    kind*:   AnnotationViolationKind ## which of its promises broke
    callee*: string                  ## the annotated callee's name
    site*:   string                  ## `file:line:col` of the call site
    msg*:    string                  ## the human-readable explanation

  # ---- RFC-0005 S1: soundness channels (§2.1) ------------------------------
  # Z3-free (RFC-0005 §8.2 -- RFC-0007's trace engine shares it). Declared in
  # `smt/types.nim` by S1; moved to this leaf by S11 (see the module doc).
  SoundnessChannel* = enum
    ## RFC-0005 §2.1. The two structurally opposite ways the walker can be
    ## wrong about a program, named for the FAILURE MODE they license rather
    ## than the approximation direction (so the verdict rule reads
    ## `scSpurious notin winnerTaint` / `scIncomplete notin runTaint`).
    scSpurious    ## over-approximating: modelled ⊇ real. A witness on such a
                  ## path may be spurious. Blocks sxSat for THIS path.
    scIncomplete  ## under-approximating: modelled ⊆ real. A proof over such a
                  ## run may have missed behaviours. Blocks sxUnsat RUN-WIDE.

  Taint* = set[SoundnessChannel]
    ## RFC-0005 §2.1. The powerset lattice on two elements: `⊥ = {}` (clean,
    ## the identity of join), `⊤ = {scSpurious, scIncomplete}` (the
    ## incomparable/"wrong, not merely coarse" class of §0.2); join is set
    ## union. Carried per PATH (`Path.taint`, written at degrade sites) and
    ## per RUN (`WalkCtx.runTaint`, DERIVED at drain from the error seqs --
    ## §2.2 "The run coordinate is derived, not written").

  DegradeClass* = enum
    ## RFC-0005 §2.2. What a degrade site SUBSTITUTES, named -- the five
    ## meaningful points of the four-coordinate (path, run) product. A
    ## `classOf` row is a reviewable judgment ("kind K is dcFabricated"),
    ## and the coordinates are derived once, in `pathTaint`/`runTaint`.
    dcFreshSymbol   ## substitutes a fresh unconstrained symbol: modelled ⊇ real
    dcSubstituted   ## forced value / stale env: modelled neither ⊇ nor ⊆ real
    dcFabricated    ## the survivor path is fiction, but the omission is real:
                    ## ⊤ on the path, {scIncomplete} on the run (k-unroll survivor)
    dcOmitted       ## path drop / halt / prune: modelled ⊆ real
    dcNoAnswer      ## Z3 unknown / walker fault: no modelled program exists


  ReplayStatus* = enum
    ## RFC-0005 §8.1. How a `sxSat`/`sxRaised` claim was settled.
    ## Refuted and inconclusive replays of a CANDIDATE never ship on a winner
    ## (they leave the run `sxUnknown`), so they have no member here.
    rsUnsettled    ## RFC-0005 0.9.1 (review R1-16). The zero value: no producer
                   ## settled this record, so nothing about it is trusted. Every
                   ## real verdict leaves the run boundary (`runSymex`) with one
                   ## of the members below; a record still `rsUnsettled` was
                   ## built by hand, or by a constructor that forgot the field,
                   ## and fails closed rather than open
    rsNotNeeded    ## a clean path whose witness is the model's -- the claim
                   ## stood without replay (and the value on every `sxUnsat` /
                   ## `sxUnknown`)
    rsConfirmed    ## an `scSpurious`-tainted path, or a clean one whose witness
                   ## renders lossily, whose witness the REAL `fn` was run on
                   ## and confirmed (`roConfirmed`, §2.3 rule 3)
    rsUnconfirmed  ## RFC-0005 0.9.1 (WA-9). A clean winner whose witness is
                   ## lossy (`feExtractionFailed`, `wfLossy`: the rendered value
                   ## is not the model's), which no replay confirmed: it was
                   ## refuted, timed out, crashed, declined or did not run. The
                   ## clean path still reaches the target, so the status stands,
                   ## but nothing has run the reported witness: not `trusted()`.
                   ## A `feReplay*` hint says why

  RunDependence* = enum
    ## RFC-0005 0.9.1 (WA-7; review R1-07). Why a verdict is this run's and not
    ## only the program's: another run, on another machine or at another
    ## moment, may decide what this one left undecided. Set where the run
    ## ends (`runSymex`) and where its replays settle, and read off the
    ## result at save time, never off the thread: a verdict the save is
    ## handed carries its own.
    rdQueryTimeout  ## RFC-0005 S8bu. A solve the wall clock cut off
                    ## (`queryTimeoutMs`)
    rdNativeStack   ## RFC-0005 S8ca. A call declined for want of native stack
                    ## (or of Nim's call depth): a thread with more goes deeper
    rdReplay        ## RFC-0005 0.9.1 (WA-7). A replay's child ended in a way
                    ## another run may not: killed at `replayTimeoutMs`, ended
                    ## at the replay's memory limit, or not started or not
                    ## handed its state for a reason of the moment
                    ## (`ReplayChild.runDependent`)

  Soundness* = object
    ## RFC-0005 §8.1. One common-section field on `RawResult`, `SymexResult`
    ## and `SymexFinding`, so a generic consumer reads the taint without
    ## splitting on the status.
    pathTaint*: Taint
      ## The winning path's taint (`sxSat` / `sxRaised`); `{}` otherwise. A
      ## clean winner is `{}`; a replay-confirmed one keeps its
      ## `scSpurious` beside `replay = rsConfirmed`.
    runTaint*:  Taint
      ## The run coordinate: `runTaintOf` over the result's final error
      ## list. On `sxUnknown` this is round 1's `forcedBy`, never `{}`
      ## (Invariant-7 extension). It is the join over every decline, so on
      ## a real SUT it is often ⊤; the per-cause view is `gaps()`.
    replay*:    ReplayStatus
      ## How the claim was settled; `rsUnsettled` (the zero value) until a
      ## producer settles it, and then never trusted (review R1-16).
    witnessUnsafe*: bool
      ## RFC-0005 0.9.1 (WA-2). A replay of this claim's witness did not
      ## finish: its child exited (`quit`, a raw `exit`), was ended by a
      ## signal or a system exception, ran past `replayTimeoutMs`, or ended
      ## with its status lost. Running the witness in a process ends or hangs
      ## that process, so no consumer runs it in the host (`hostRunnable`):
      ## `assertCoveredBy` does not splat it and `symexForAll` does not seed
      ## it. On an `rsConfirmed` claim the child reached the target first, and
      ## the target is reached all the same (§5a); review R2 (DD1): on an
      ## `rsUnconfirmed` one it ended before the target. Only a replay sets
      ## it; a witness nothing ran is `false`. Stored with the verdict, so a
      ## cache hit reads it as the cold run did.
    runDependence*: set[RunDependence]
      ## RFC-0005 0.9.1 (WA-7; review R1-07). What of this verdict depends on
      ## the run (`RunDependence`); `{}` for one any run would reach. An
      ## `sxUnknown` with any is not cached, and an `rsUnconfirmed` witness
      ## with `rdReplay` is not stored as unconfirmed for good. Verdict-neutral:
      ## `trusted()` does not read it.

func trustedSat*(s: Soundness): bool =
  ## RFC-0005 §8.1 `trusted()`'s `sxSat` / `sxRaised` arm: a clean winning
  ## path with a faithful witness, or one the real `fn` confirmed (a spurious
  ## path, or since 0.9.1 a lossy witness, WA-9).
  ## An `rsUnsettled` record (the zero value) is never trusted (R1-16).
  case s.replay
  of rsConfirmed: true
  of rsUnconfirmed, rsUnsettled: false
  of rsNotNeeded: scSpurious notin s.pathTaint

func hostRunnable*(s: Soundness): bool =
  ## Review R1-15, R2 (DD1, DD2). Whether a consumer may run a claim's witness
  ## in its own process, from typed data only: never one a replay saw end or
  ## hang its child (`witnessUnsafe`), and never an unsettled record (R1-16).
  ## Untrusted claims (`rsUnconfirmed`) are runnable otherwise: running one
  ## is how a consumer learns whether it reaches the target.
  s.replay != rsUnsettled and not s.witnessUnsafe

func cacheable*(s: Soundness): bool =
  ## Review R2 (DD7). Whether a claim (`sxSat` / `sxRaised`) settled under
  ## `s` may be stored for good. Not a lossy winner the replay left
  ## unconfirmed for a reason of the run (`rdReplay`, WA-7, WA-9): the next
  ## run replays it again.
  not (s.replay == rsUnconfirmed and rdReplay in s.runDependence)

func trustedUnsat*(s: Soundness): bool =
  ## RFC-0005 §8.1 `trusted()`'s `sxUnsat` arm: nothing under-approximated.
  ## An `rsUnsettled` record (the zero value) is never trusted (R1-16): a
  ## `runTaint` of `{}` there means only that no producer wrote one.
  s.replay != rsUnsettled and scIncomplete notin s.runTaint
