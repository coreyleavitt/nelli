## RFC-0016 INT-34 B2. The walker's types: a leaf cut out of `runtime.nim`.
##
## Every type declaration of `runtime.nim`'s regions R0..R4 (the regions of
## `scripts/int34-deps.py`) lives here, in the order it had there: `Path` and
## its heap-state records, `Degrade` and `Survivors`, `CapKind`, the `Raw*`
## results and `SatCandidate`, the loop/call/handler frames, `CallFrameCtx`,
## `WalkCtx` and its exit groups, and the small records the solving and
## drain code keeps. With them is the compile-time walk over `WalkCtx`'s exit
## groups (`forEachExitGroup`, `collectExitGroupFields`), so the field list
## and the check that it is whole stay together. Nothing else: no threadvar,
## no walk logic.
##
## Visibility. A type `runtime.nim` exported before keeps its fields exactly
## as they were, and so does `RawWitness` (private, but reachable through the
## public `RawResult.witness`): a private field of one of those stays private
## to this module, and `runtime.nim` reads it under `privateAccess`
## (`RawWitness`, `SatCandidate.input`). The module-level grant does not reach
## a generic body instantiated in a caller's module (`readSeqAs[T]` from the
## DSL's `symexFind`), so each public generic witness reader that touches a
## private `RawWitness` field repeats `privateAccess(RawWitness)` in its own
## body. Every other type, and every field of
## it, is exported, so the modules cut out of `runtime.nim` after this one can
## use them. `runtime.nim` re-exports exactly the type names it exported
## before (`export walk_types.<name>`), never the module: a name it kept
## private (`WalkCtx`, `Path`, `Degrade`, ...) is not reachable through
## `import nelli/symex`.
##
## `Degrade` and `Survivors`. Before the move they were private to
## `runtime.nim`, and that privacy was nominal there too: what pins their
## constructors is the K2 census (`tsymex_0016_k2a_census`), which counts
## every `Degrade(`/`Survivors(` literal in `src/nelli` outside the
## sanctioned constructors, whatever module it is in. A module that imports
## this leaf can name `Degrade`; a literal it writes is an unlisted census
## site, and the census fails.
##
## Imports only std, `z3` and leaves; the census
## (`tests/tsymex_0016_d3_include_census.nim`) pins the list.
import std/tables
import std/options
import std/sets
import z3
import ./types
import ./symval
import ./walk_state
import ./exits
import ./concolictaxonomy

type
  ElemCell* = object
    ## RFC-0005 S8be. The address cell of element `idx` of the seq variable
    ## `root` of frame `frame` (`addr root[idx]`, the index as `addr`
    ## evaluated it): the walk keeps the heap at `refAst` and the element
    ## equal statement by statement (`syncElemCells`) until the seq is
    ## resized or assigned whole, when Nim may free its elements' memory
    ## and the cell is `dead` (a dereference that may reach it declines).
    refAst*: Z3AnyAst
    frame*:  int
    root*:   string
    ty*:     IRType
    idx*:    Z3Int
    dead*:   bool
    field*:  string
      ## RFC-0005 S8bo. Non-empty for a field cell (`walkFieldCell`): the
      ## cell of arm field `field` of the case-object variable `root`
      ## (`addr root.field`), declared by the arms `tags`; `idx` is unused.
      ## It dies when the object may have changed arm.
    tags*:   seq[int]

  PtrStore* = object
    ## RFC-0005 S8bz. A store through a pointer: what later candidates of the
    ## pointer, unknown to it then, must still see (`ptrApplyMissed`).
    typeId*: string
    ptrAst*, val*: Z3AnyAst
    reached*: seq[int64]   ## the candidates' codes it has been applied to

  HeapTerm* = tuple[ast: Z3AnyAst; input: string]
    ## RFC-0005 S8ca. A heap array's term on a path: the array the path
    ## holds (`Path.heaps`), or, while it holds none, the name of the free
    ## input constant it reads (`heapInputName`), which an opaque call's
    ## havoc renames.

  ViewMark* = object
    ## RFC-0005 S8ca. A by-value seq formal sharing the memory of an
    ## address-taken variable (a `view` cell entry, `bindVarLocs`): the
    ## heap arrays its value is read from (`keys`) and their terms when the
    ## formal last took the cell's value (`at`). It follows the cell only
    ## while every change of those arrays since is an in-place step
    ## (`Path.inPlaceSteps`, `viewInPlace`).
    local*: string
    frame*: int
    keys*:  seq[string]
    at*:    seq[HeapTerm]

  InPlaceStep* = tuple[key: string; before, after: HeapTerm]
    ## RFC-0005 S8ca. One store into the heap array `key` that wrote a
    ## seq's element in its memory (`dwInPlace`, or a `view`'s sync of an
    ## element written by name): the array's term before and after it.

  Path* = ref object
    ptrStores*: seq[PtrStore]
      ## RFC-0005 S8bz. Every store through a pointer on this path, in order.
    pc*:        seq[Z3Bool]
    defectSurvivorPc*: seq[Z3Bool]
      ## Phase 16 ADR-0012. HARD path constraints that are NOT branch selectors:
      ## the `not overflow_pred`/`not divisorIsZero`/`not parseIntRaise` negations
      ## a defect drain conjoins onto the SURVIVING (non-raising) continuation.
      ## Kept SEPARATE from `pc` so `applyClosureGround` can use `pc` (genuine
      ## intra-body branch conditions only) as the closure return-axiom implication
      ## GUARD, while these feasibility facts are threaded onto the CALLER path
      ## caller-locally (never demoted into the guard — that was the C3 soundness
      ## bug — and never lifted into the global closure axioms, which would make
      ## the in-body defect RAISE path UNSAT and mask the defect). `trySolve`
      ## asserts pc ++ defectSurvivorPc together, so the effective path condition
      ## is unchanged for every non-closure path; `forkPath` inherits the field so
      ## the named-proc return-merge propagates it to the caller for free.
    env*:       Env
    undefinedViaOnly*: set[UbKind]
                      ## RFC-0016 W3-z R7. The kinds of `undefined` that only
                      ## an opaque call through a module-level proc-valued
                      ## variable put there (`IRStmt.opaqueUndefinedVia`): a
                      ## replay that names the routine the variable held may
                      ## replace them (`symex.nim`'s `procValueLift`). Empty
                      ## (the default) claims nothing: every kind is fixed.
    undefined*: set[UbKind]
                      ## RFC-0016 W1-d3 (section 9.1 item 4). The undefined
                      ## behaviours this path has read through (today the
                      ## `{.noinit.}` read of an unwritten slot,
                      ## `ubIndeterminateRead`). Joined by every carrier that
                      ## joins `taint` (`forkPath` propagates, `forkPathTainted`
                      ## joins a `Degrade`'s `ub`, `forkPathMerged` unions,
                      ## `taintInPlace` joins), pinned by the lattice test's
                      ## carrier probe. Derived at the hit into
                      ## `Soundness.witnessUndefined`, which replay cannot
                      ## lift. Invariant: non-empty implies `taint != {}`.
    taint*: Taint      ## RFC-0005 S1 (was SND-1's `uncertain: bool`). The
                      ## soundness channels this path has picked up from a
                      ## degrade (a bailed call, an unmodelled statement, an
                      ## in-band lowering decline, ...). WRITTEN only through
                      ## the sanctioned primitives -- `forkPath` (propagate),
                      ## `forkPathTainted` (join a `Degrade` token),
                      ## `forkPathMerged` (return-merge union),
                      ## `taintInPlace` -- and pinned by the writer grep-pin
                      ## (`tests/tsymex_rfc0005_s1_lattice.nim`). S1 reads it
                      ## only as `taint != {}` (any channel ⇒ today's
                      ## "uncertain"); S1c re-derives the reads per channel.
    # ---- Phase 15 H1: logical-heap state (ADR-0010) ----
    # These three fields are PURE SCAFFOLDING for Cluster R. They are
    # empty/zero on every path today and the walker never reads or writes
    # them — H1 ships only the field shape so Cluster E (E3/E5/E7) and
    # Cluster R can compile against `path.heaps`. Heap SEMANTICS (alloc /
    # deref / nil-fork / alias / witness) land in Cluster R, not here.
    # The deep-copy-at-fork contract (deepCopyHeapState) is wired NOW so
    # that R does not have to re-audit every fork site.
    heaps*:         Table[string, Z3AnyAst]  ## per-path symbolic heap, keyed
                                            ## by Z3 sort name (Cluster R fills)
    heapDepth*:     int                      ## current heap-descent depth
                                            ## (bounded by maxHeapDepth in R)
    allocCounters*: Table[string, int]       ## per-type fresh-ref counter,
                                            ## keyed by type-ID string
    # ---- Phase 15 R2: per-path live fresh-ref tracking (ADR-0010) ----
    liveRefs*:      Table[string, seq[Z3AnyAst]]
      ## Phase 15 R2. Per-pointee-type list of the fresh `Ref_T` consts minted
      ## by `new T` on THIS path (keyed by the same `refPointeeTypeId` as
      ## `heaps`/`allocCounters`). `assertFreshness` reads it to emit the GROUND
      ## `newRef != prior` distinctness inequalities, then appends the new ref.
      ## Deep-copied at every fork (`deepCopyHeapState`), so DISJOINT forked
      ## paths do NOT share prior refs — a `new T` on a forked branch restarts
      ## from the fork snapshot's list (no cross-path `ref_T_i != ref_T_j`).
    freshnessAssertCount*: int
      ## Phase 15 R2. Count of fresh-ref distinctness inequalities already
      ## emitted on this path; compared against `settings.maxFreshnessAssertions`
      ## (the cap). Threaded by value at every fork like `heapDepth`.
    nilDeref*: bool
      ## RFC-0005 S8k. This path took `nilDerefFork`'s NIL edge: it models a
      ## `p[]` read or write with `p == nil` as a `NilAccessDefect` raise
      ## (escaping, or caught by a handler and continued). The real program
      ## does not raise there: a nil dereference is a SIGSEGV in the default
      ## build of the pinned toolchain (probed: `--nilchecks:on` changes
      ## nothing, and no `except` arm runs). Set once at the fork, inherited
      ## by every fork below it, and carried to the finding
      ## (`RawResult.nilDerefOnPath`), so replay never executes a witness
      ## whose real run would dereference nil and kill the host process.
    addrOwners*: seq[tuple[refAst: Z3AnyAst; frame: int]]
      ## RFC-0005 S8ax. Each address cell this path allocated
      ## (`CallFrameCtx.addrCells`) and the frame whose variable it holds.
      ## Once that frame has returned, the pointer dangles: a dereference
      ## that may reach it declines (`danglingFork`). Inherited by every
      ## fork, and by the caller on a return.
    elemCells*: seq[ElemCell]
      ## RFC-0005 S8be. The element cells this path allocated (`addr s[i]`,
      ## `walkElemCell`), each a frame's view of one: the caller's entry and
      ## a callee's (a `var` formal, a capture) share the cell. Inherited by
      ## every fork, and by the caller on a return.
    loopIters*: seq[tuple[loop: int, iters: int]]
      ## RFC-0005 S8y. For each `while` this path has run through (`loop`,
      ## the statement's identity within the walk), how many times its body
      ## was entered in the loop's latest execution: set at each of the
      ## loop's forks (`atIteration`), inherited by every fork below.
      ## `solveTargetHit` compares it with the depth of a tainted hit that
      ## ran out of budget (`WalkCtx.budgetOutDepths`).
    viewMarks*: seq[ViewMark]
      ## RFC-0005 S8ca. The by-value seq formals on this path that share an
      ## address-taken variable's memory. Inherited by every fork, and by
      ## the caller on a return; a returned frame's are dropped as read.
    inPlaceSteps*: seq[InPlaceStep]
      ## RFC-0005 S8ca. The in-place element writes this path made while it
      ## had a `viewMarks` entry, in order. Inherited as `viewMarks` is.

  Degrade* = object
    ## RFC-0005 S1 (§2.2 "One funnel performs all three acts"). The token a
    ## degrade site obtains from `degrade(w, kind, msg)` (or `queueDegrade`'s
    ## pending-taint drain) and hands to `forkPathTainted`/`taintInPlace`. It
    ## carries ONLY the path coordinate `pathTaint(classOf(kind))` of the one
    ## kind mention that also recorded the `SymexErrorInfo` -- so recording
    ## and classification cannot disagree, and one token serves every
    ## survivor of a one-error-many-survivors site. The run coordinate is not
    ## in it: `WalkCtx.runTaint` is DERIVED at drain from the recorded errors.
    ## Construct a `Degrade(...)` ONLY inside the sanctioned funnels (pinned by
    ## the writer grep-pin); a site never builds one by hand.
    path*: Taint
    ub*: set[UbKind]
      ## RFC-0016 W1-d3. The undefined behaviours the same degrade site read
      ## through; joined into `Path.undefined` beside `path`.

  Survivors* = object
    ## RFC-0016 K7a (section 8.4, K7). The paths an arm leaves live, typed
    ## by HOW it left them, so a degrade can no longer be discarded in
    ## place. A layer over `Degrade`/`forkPathTainted`/`taintInPlace`, not
    ## beside them. There is no "admitted" constructor: an `Admit` is the
    ## parser's fact and proves nothing at walk time, so the untainted exit
    ## is plain `exact`, and what keeps it honest is K2's census of
    ## `Survivors(`, `exact(` and `Degrade(` sites (type privacy never
    ## pinned them; see this module's header). Constructors: `halted`,
    ## `surviving`, `continued`, `exact`.
    live*: seq[Path]

  CapKind* = enum
    ## RFC-0016 K7a (section 8.4, "Caps are halts"). One member per cap-cut
    ## PRODUCING SITE, named at that site by `cap = <member>`; a cap cut at
    ## two sites has two members. K1 derives cap coverage from this
    ## enum, and `tsymex_0016_k7a_survivors` pins one site per member.
    ## Caps with no walk-level degrade site yet (the parse-time and
    ## solver-side ones) join when their site is converted.
    ckNone                ## not a cap cut (the default)
    ckFrontier            ## `maxFrontierSize`: `walkBlock`'s prune (a halt)
    ckHeapDepth           ## `maxHeapDepth`: `heapDerefDecline` (a halt)
    ckCallDepth           ## `maxCallDepth`/`maxRecursionDepth`: the `isCall` bail
    ckLoopUnwind          ## `maxLoopUnwind`: the `isWhile` k-unroll
    ckLoopUnwindFollow    ## `maxLoopUnwind`: the concrete-follow loop
    ckVariantForks        ## `maxVariantConstructorForks`
    ckVariantFieldAllocs  ## `maxVariantConstructorFieldAllocs`
    ckTermWalkRead        ## `termWalkMaxDepth`: a too-wide array read
    ckTermWalkWrite       ## `termWalkMaxDepth`: a too-wide array write
    ckWalkWork            ## `walkRLimit`: the walk's total solver work (a halt)

  DegradeSink* = enum
    ## RFC-0005 S1. Which existing error sink `degrade()` records into. The
    ## sinks predate the funnel and are drained separately at verdict
    ## assembly (dedup is per sink), so the funnel must preserve each site's
    ## sink rather than collapse them into `walkDegradeErrors`.
    dsWalk          ## `w.walkDegradeErrors` (the default)
    dsHeapDepth     ## `heapDepthErrors` threadvar + `w.heapDepthErrors`
    dsNewFieldZero  ## `newFieldZeroErrors` threadvar + `w.newFieldZeroErrors`
    dsClosure       ## `currentClosureCallErrors` threadvar + `w.sinks.closureCallErrors`
    dsUnknownExn    ## `unknownExnWarnings` threadvar + `w.unknownExnWarnings`,
                    ## recorded at `sevWarning` (RFC-0005 S6b: `routeRaise`'s
                    ## `eeUnknownExnType`, a behaviour substitution whose
                    ## consumer-facing severity predates the RFC; `taintsRun`
                    ## counts it anyway -- §3.1's carve-out)

  RawWitness* = object
    paramOrder: seq[string]
    intVals:    Table[string, int64]
    uintVals:   Table[string, uint64]
    boolVals:   Table[string, bool]
    float32Vals: Table[string, float32]  ## Phase 15 F7: bit-exact float32 witness
    float64Vals: Table[string, float64]  ## Phase 15 F7: bit-exact float64 witness
    strVals:    Table[string, string]
    seqLens:    Table[string, int]   ## Phase 5: per-param seq length
    tabKeys:    Table[string, seq[string]]  ## Phase 5: per-Table key list
    setMembers: Table[string, seq[int64]]   ## Phase 5: per-HashSet members
    heapSnapshot: seq[HeapSnapshotEntry]
      ## Phase 15 R12 (ADR-0010, witness-format-v3.md). One entry per ref/ptr
      ## param: the abstract address, modelled pointee value, and alias group.
      ## Empty for a SUT with no ref/ptr params (backward compat). Built in
      ## `extractWitness` from the live Z3 model; threaded out through
      ## `RawResult.witness` and mirrored onto `SymexResult.heapSnapshot`.
    pinsComplete*: bool
      ## RFC-0016 K10b. True when `pins` covers every leaf of every
      ## parameter (`modelPins`): none was skipped as unfitting or unevaluable.
      ## A lossy witness is followed past the label only then.
    pins: seq[Z3Bool]
      ## RFC-0016 K10b. The model's choices as equalities over the initial
      ## environment's leaf terms (`svLeafTerms`, `leaf == model(leaf)`), one
      ## per pinnable leaf of every parameter, built in `trySolve` while the
      ## model is live. The whole-run gate's second walk runs under them as
      ## its `concreteEq`, so what it follows is the model, not the rendered
      ## witness. A leaf that cannot be pinned is left free: the gate then
      ## over-approximates (a side the solver can reach with any value of it
      ## is undefined), never under. In-process only, never persisted.

  RawDiagnostic* = object
    ## ADR-0012 D2. One non-winning sxRaised finding from `w.found`,
    ## collected by the reduction in `runSymex`. Parallel to the public
    ## `DefectFinding[T]`; typed by the `symexFind` macro.
    raisedTypeId*:  string
    isDefect*:      bool
    raisedMsg*:     Option[string]
    raisedWitness*: RawWitness
    witnessUnsafe*: bool
      ## RFC-0016 W3-z R5 (U7). This raise's own `Soundness.witnessUnsafe`:
      ## which diagnostic witness is safe to run in-process is per raise, never
      ## the winner's. There is no `witnessUndefined`: a raise past undefined
      ## behaviour is on a spurious path, so it is a candidate and never a
      ## diagnostic (R5b, `tsymex_0016_w3z_r5b_diag`).

  RawUndefined* = object
    ## RFC-0016 K10a-target. One undefined behaviour the walk reached and
    ## solved, before typing (`UndefinedFinding[T]`).
    kind*:    UbKind = ubUnsignedDivZero   ## a default: the range omits 0
    site*:    string
    witness*: RawWitness

  SatCandidate* = object
    ## RFC-0005 S10 (§2.3 rule 3, §4.2 "Plumbing"). A SOLVED finding on an
    ## `scSpurious`-tainted path -- the enlarged program reaches the target,
    ## reality is unknown -- in a form that CANNOT be mistaken for, or
    ## spelled as, a `sxSat`/`sxRaised`. It is deliberately NOT a
    ## `RawResult`: it has no `witness`/`raisedWitness` branch, so no
    ## `case raw.status` arm, cache writer (`saveSymexRaisedImpl` takes
    ## `seq[RawResult]`) or `SymexResult` construction can consume it. The
    ## model's input is the PRIVATE `input` field: outside this module it is
    ## readable only by `symex.nim`'s replay codegen (`candidateInput`, under
    ## `privateAccess`), and the only way to turn a candidate into a verdict
    ## is `symex.nim`'s `settleCandidate` with a `roConfirmed` replay outcome
    ## -- both private to `symex.nim`, reached from macro-generated code by
    ## `bindSym` inside `emitRunSymexReplayed`, the one place `runSymex` is
    ## called from an entry macro. The metadata a consumer may audit is
    ## public.
    status*:       SymexStatusKind
      ## The CLAIM: `sxSat` (a label hit) or `sxRaised` (a SUT-boundary
      ## raise). Never `sxUnsat`/`sxUnknown`.
    pathTaint*:    Taint
      ## The taint of the path that produced it (always `scSpurious in`),
      ## recorded at the hit; the input to replay's eligibility gate.
    errors*:       seq[SymexErrorInfo]
      ## Its own witness-extraction errors (RFC-0005 S1c), never the run's.
      ## A `feExtractionFailed` here makes the rendered witness lossy
      ## (a substituted `0.0`): replay confirms on a hit, never refutes.
    raisedTypeId*: string            ## `sxRaised` claims only
    isDefect*:     bool              ## `sxRaised` claims only
    raisedMsg*:    Option[string]    ## `sxRaised` claims only
    witnessUndefined*: set[UbOrdinal]
      ## RFC-0016 W1-d3. The claim's `Soundness.witnessUndefined`, carried to
      ## `settleCandidate` (replay cannot lift it).
    witnessUndefinedViaOnly*: set[UbOrdinal]
      ## RFC-0016 W3-z R7. The kinds of `witnessUndefined` that only a call
      ## through a module-level proc-valued variable put there
      ## (`Path.undefinedViaOnly`): a replay that names the routine each such
      ## variable held on its run replaces them by what those routines reach
      ## (`symex.nim`'s `procValueLift`). Empty claims nothing.
    witnessUnsafe*: bool
      ## RFC-0016 WA-B (S4). The claim's own `Soundness.witnessUnsafe` (a
      ## crash claim: its witness ends the process wherever it runs), carried
      ## to `settleCandidate`, which ORs the replay's `endsChild` into it.
    nilDerefOnPath*: bool
      ## RFC-0005 S8k. The claim's path went through the walker's nil
      ## dereference edge (`Path.nilDeref`): its real run would SIGSEGV
      ## where the model raises `NilAccessDefect`, so replay declines it
      ## (`roInconclusive`) without executing `fn`.
    input:         RawWitness
      ## PRIVATE: the solver's model of the input (the `witness` of an
      ## `sxSat` claim, the `raisedWitness` of an `sxRaised` one).

  CandidateReplay* = proc (order: seq[int]; cands: seq[SatCandidate]): int
                         {.closure.}
    ## RFC-0016 W4 perf. The settle's replays, handed to `runSymex` by the
    ## entry macros' replayed body (`emitRunSymexReplayed`): replays the
    ## candidates in the settle's order, `cands[k]` being the run's
    ## `RawResult.candidates[order[k]]`, up to the first confirmation, records
    ## their outcomes for the settle that follows the run, and answers the
    ## confirmed one's position in `order` (`-1`: none). The run calls it while its
    ## context is live, so it walks the tail of the candidate a replay
    ## confirmed (W3-z R2) and of no other. RFC-0016 INT-32 (item 8): the
    ## replays run at once (`replayInOrder`), and the answer is still the
    ## first in order.

  RawResult* = object
    abstractions*: AbstractionLog
    obligations*:  ObligationLog
      ## Issue #161 slice 2. Mirrors `SymexResult.obligations`; filled from
      ## the `obligationLog` threadvar on every verdict branch.
    callStats*:    CallStats
    errors*:       seq[SymexErrorInfo]
      ## Phase 14 cycle C4. Z3-layer errors caught at runSymex's top
      ## level. Always empty on a clean run; populated when a typed
      ## `Z3Error` is thrown by the solver. Translated into per-
      ## target `SymexFinding.errors` by the macro-emitted runtime
      ## in `symex.nim`. `ValueError` and `AssertionDefect` from
      ## walker logic are NOT caught — those are real walker bugs.
    undefined*:    seq[RawUndefined]
      ## RFC-0016 K10a-target. Every undefined behaviour the walk reached and
      ## solved (`SymexResult.undefined`).
    diagnostics*:  seq[RawDiagnostic]
      ## ADR-0012 D2. Non-winning sxRaised findings from the walk, collected
      ## by the reduction. Typed into `DefectFinding[T]` by the `symexFind`
      ## macro. Empty for sxUnsat/sxUnknown; also empty when the winner is
      ## the only sxRaised in w.found.
    procValueSites*: seq[string]
      ## RFC-0016 W3-z R7. Every module-level proc-valued variable an opaque
      ## call the walk noted calls through (`WalkCtx.procValueSites`): the
      ## variables a replay settle must name the routines of before it may
      ## replace a candidate's `undefinedViaOnly` kinds.
    undefinedViaOnly*: set[UbOrdinal]
      ## RFC-0016 W3-z R7. The kinds of `soundness.witnessUndefined` that only
      ## a call through a module-level proc-valued variable put there
      ## (`Path.undefinedViaOnly`); carried to `SatCandidate`.
    nilDerefOnPath*: bool
      ## RFC-0005 S8k. The path that produced this finding took the walker's
      ## nil dereference edge (`Path.nilDeref`), recorded at target-hit time
      ## beside `pathTaint`. Read only when the finding becomes a replay
      ## candidate (`SatCandidate.nilDerefOnPath`).
    witnessExtraction*: seq[SymexErrorInfo]
      ## RFC-0016 INT-32 (R1-33). On a clean `sxSat` / `sxRaised` winner: the
      ## `feExtractionFailed` records of ITS OWN witness extraction (a value
      ## the render substituted), which `winnerLossy` reads. `errors` holds
      ## the run's, a sibling hit's among them, which said nothing about this
      ## witness. Empty on every other result.
    soundness*:    Soundness
      ## RFC-0005 S11 (§8.1) -- the one carrier (was S1's bare `pathTaint`
      ## field). `soundness.pathTaint` is the taint of the path that produced
      ## this finding, recorded at TARGET-HIT time (`isTargetLabel`'s sxSat,
      ## `routeRaise`'s sxRaised) because the winning path is not otherwise
      ## available at verdict time; RFC-0005 S1c routes on it
      ## (`admitSolvedHit`): a winner's is free of `scSpurious`, a
      ## candidate's carries it. `soundness.runTaint` is derived once, at the
      ## public boundary (`runSymex`), from the final `errors`.
      ## `soundness.replay` is written only by the replay settle
      ## (`symex.nim`'s `settleCandidate`).
    bounds*:       ResourceBudget
      ## RFC-0005 S11 (§8.2). The bound echo: `settings.budget`, stamped by
      ## `runSymex` on every status, including a boundary abort.
    annotationViolations*: seq[AnnotationViolation]
      ## RFC-0005 S8 (§13.3, i3). `prog.annotationViolations`, copied onto
      ## every verdict branch by `runSymex`. Verdict-neutral (see
      ## `AnnotationViolation`).
    candidates*:   seq[SatCandidate]
      ## RFC-0005 S1c (§2.3 "Candidate lifecycle"). Every SOLVED finding
      ## whose path carries `scSpurious` (`sxSat` at a label hit, `sxRaised`
      ## at a SUT-boundary raise), in discovery order, each with its own
      ## `pathTaint` and its own witness-extraction `errors`. Never a winner
      ## by itself: `decideVerdict` returns `sxUnknown` when one exists and no
      ## clean finding does (rule 4 -- the enlarged program reaches the
      ## target). RFC-0005 S10: this is the pool rule 3's replay reads after
      ## `runSymex` returns (`symex.nim`'s `emitRunSymexReplayed`), typed
      ## `SatCandidate` so it cannot be read as a witness anywhere else.
      ## Empty on `sxUnsat` by construction.
    case status*: SymexStatusKind
    of sxSat:
      witness*: RawWitness
    of sxUnsat, sxUnknown:
      discard
    of sxRaised:
      ## Phase 15 E2a (STRUCTURAL). The raised exception's type id. The
      ## remaining fields are wired now but inert until later cycles:
      ## `isDefect` is populated in E6 (false until then) and `raisedMsg`
      ## in E2b (none until then). `raisedWitness` carries the input that
      ## reaches the raise (default/empty in E2a — no Z3 reasoning yet).
      raisedTypeId*:  string
      isDefect*:      bool
      raisedMsg*:     Option[string]
      raisedWitness*: RawWitness

func capSetting*(c: CapKind): string =
  ## RFC-0016 K7a. The `Settings` knob a cap cut is raised with, shown in the
  ## recorded message by `degrade`. Total (no `else`): a new `CapKind` member
  ## is a compile error until it names its setting.
  case c
  of ckNone:               ""
  of ckFrontier:           "maxFrontierSize"
  of ckHeapDepth:          "maxHeapDepth"
  of ckCallDepth:          "maxCallDepth/maxRecursionDepth"
  of ckLoopUnwind,
     ckLoopUnwindFollow:   "maxLoopUnwind"
  of ckVariantForks:       "maxVariantConstructorForks"
  of ckVariantFieldAllocs: "maxVariantConstructorFieldAllocs"
  of ckTermWalkRead,
     ckTermWalkWrite:      "termWalkMaxDepth"
  of ckWalkWork:           "walkRLimit"

type UninitScan* = object
  depth*: int   ## RFC-0005 S8ct. The levels of `uninitAt` open.
  ## One `uninitReadCond` query's memo: whether a term mentions a base, and
  ## the condition already built per (array, index) pair (a loop's merges
  ## share their store chains, which a plain recursion would revisit once
  ## per path through the `ite`s).
  ctx*: Z3Context
  mentions*: Table[int, bool]
  at*: Table[(int, int), Z3Bool]
  held*: seq[Z3AnyAst]   ## RFC-0005 S8bv: the terms built here, kept live
                        ## so no memo key's id is reused within the scan

type GuardLiteral* = enum glOpen, glTrue, glFalse

type
  RefPos* = object
    ## RFC-0005 S8h. One `ref`/`ptr` position of the input.
    name*:    string
    addrAst*: Z3AnyAst
    pointee*: IRType
    isRef*:   bool   ## RFC-0016 INT-88: a `ref` (a managed object), not a `ptr`

type PtrLeafAim* = object
  ## RFC-0005 S8bn (item 4). What a `sel` code names, for the snapshot: a
  ## part of a variable (`name`, the field / element `path` below it, and
  ## whether the last step is the pointer's seq index), or an element of a
  ## seq held in a heap field family (`fam`).
  name*: string
  path*: seq[int]
  steps*: seq[string]   ## RFC-0005 S8bw (item 3): `path` as the witness
                       ## names it (`ptrAimInto`)
  elemSteps*: seq[string]  ## RFC-0005 S8bz (items 1, 2): the part of the
                          ## aggregate element or value below the pointer's
                          ## index or key
  seqIdx*: bool
  tabKey*: bool
  fam*: string
  typeId*: string

type
  SnapshotBuild* = object
    ## RFC-0005 S8h. The state of one `buildHeapSnapshot` walk.
    cellOf*:  Table[string, string]   ## model address -> cell name
    entryOf*: Table[string, int]      ## cell name -> its index in `entries`
    queue*:   seq[RefPos]             ## cells to render, in discovery order
    entries*: seq[HeapSnapshotEntry]
    floor*:   Table[string, IRType]   ## RFC-0016 INT-81: cell name -> the
                                     ## deepest static pointee of a position
                                     ## holding it (`cellDynamicType`)
    seenPos*: HashSet[string]         ## RFC-0016 INT-81: positions recorded
    renderedLvls*: Table[string, seq[int64]]  ## RFC-0016 INT-81: the tags a
                                             ## cell was rendered for
    refPos*: HashSet[string]          ## RFC-0016 INT-88: the positions that
                                     ## are a `ref` (not a `ptr`)
    aliases*: seq[RefPos]             ## RFC-0016 INT-90: the positions that
                                     ## hold another position's cell

type SeqCapKinds* = object
  ## The `Z3_decl_kind` ordinals `seqLenCaps` matches on. RFC-0005 S8o:
  ## operators are matched by KIND, never by printed name -- Z3 renamed
  ## `int2bv` to `int_to_bv` (and `bv2int` to `ubv_to_int`) after 4.13, so
  ## S8k's name match never fired on the Windows leg's Z3 4.13.4, and its
  ## byte tests stayed in the slow lowered form (B7R-6 / B7r2-1a went
  ## `sxUnknown` under `seqQueryRLimit`).
  uninterp*, select*, int2bv*, toCode*, strAt*, inRe*: int
  strLen*, strIndex*: int
    ## RFC-0005 S8v: `str.len` and `str.indexof`, for `seqRangeFacts`.
  strExtract*, strToInt*, strContains*, strPrefix*, strSuffix*: int
    ## RFC-0005 S8ae: `str.substr`, `str.to_int`, `str.contains`,
    ## `str.prefixof` and `str.suffixof`, for `seqRangeFacts`.
  strConcat*, strFromInt*, strReplaceAll*: int
    ## RFC-0005 S8ai: `str.++`, `str.from_int` and `str.replace_all`, for
    ## `seqRangeFacts`. `str.replace_all` is read off a parsed term: its
    ## C constructor is absent below Z3 4.16 (`z3WithSeqReplaceAll`), the
    ## SMT-LIB operator is not.
  strFromCode*, iteK*: int
    ## RFC-0016 INT-61: `str.from_code` and `ite`, for `seqLenBoundFacts`.
  reToRe*, reRange*, reConcat*, reUnion*, reInter*, rePlus*, reOpt*, reLoop*,
    rePower*, reAllChar*: int
    ## RFC-0005 S8ai: the regex constructors `regexLenBounds` reads a
    ## membership's length bounds off (any other is `0..`, no bound).
    ## Every S8ai kind that shares its ordinal with another probed operator
    ## (Z3 reports some operators under one catch-all internal ordinal, as
    ## `seq.last_indexof`) is set to -2, so it matches nothing: its facts
    ## are dropped rather than applied to a different operator.

type FpIntervalKinds* = object
  ## RFC-0016 INT-59: the `Z3_decl_kind` ordinals `fpIntervalRefutes`
  ## reads, taken from the linked Z3 (positional, as `SeqCapKinds`).
  ok*: bool
    ## Every ordinal is distinct. A collision (a kind the linked Z3 shares
    ## between two operators) turns the interval argument off.
  toFpS*, toFpU*, fdiv*, fmul*, fadd*, fsub*, fneg*, rti*: int
  leq*, lt*, geq*, gt*, sext*, zext*, notK*, andK*, orK*: int

type LitRel* = enum
  ## RFC-0005 S8ai: the relation `seqRangeFacts`' `litHolds` folds.
  lrContains, lrPrefix, lrSuffix

type StallDeadline* = object
  ## RFC-0016 INT-57. The run's stall backstop deadline (`stallBackstopMs`),
  ## in `getMonoTime` ticks; `on` only inside a run with no run clock.
  on*: bool
  ticks*: int64

type SatModel* = object
  ## RFC-0016 int6 D1d. A model `m` (a term of the walk's context) that a
  ## search found for the query `held`. `held` keeps those roots alive, so
  ## no id in `ids` is recycled while it names one (RFC-0016 CRH-07).
  ## `checked`: every root of `held` was evaluated true in `m`.
  m*: Z3Model
  held*: seq[Z3Bool]
  ids*: HashSet[int]
  checked*: bool

type PruneFact* = object
  ## RFC-0005 S8ax. One feasibility check against a path's own facts that
  ## dropped an arm or a path (`loopArmInfeasible`, `pathInfeasible`): the
  ## path's facts as they stood (`pc`, `dsp` = its `defectSurvivorPc`) and
  ## the arm's own conjuncts (`extra`). Their conjunction (with
  ## `globalRoots`) was UNSAT.
  pc*, dsp*, extra*: seq[Z3Bool]

type
  LoopExits* = object
    ## RFC-0005 review R5. A loop frame's exit channels (`exits.nim`).
    breakPaths*:    ExitChannel[Path]
    continuePaths*: ExitChannel[Path]

  CallExits* = object
    ## RFC-0005 review R5. A call's exit channel: the paths that hit
    ## `return` inside it (`CallFrame.exits`), or inside the SUT itself
    ## (`WalkCtx.topExits`).
    returnedPaths*: ExitChannel[Path]

  LoopFrame* = object
    ## Phase 6: walker-level loop frame. `break`/`continue` consult
    ## the top entry to dispatch correctly.
    exits*:         LoopExits
    label*:         string
      ## RFC-0005 S8m. "" for a loop (`isWhile`); else the `blkLabel` of a
      ## labelled `isBlock`, the target of `break <label>` only.
    hsDepth*:       int
      ## RFC-0005 S8m. `w.frame.handlerStack.len` when the frame was pushed:
      ## a jump to it leaves every HandlerFrame at or above this depth, so
      ## each of their `finally`s runs first (`exitJump`).

  CallFrame* = object
    ## A walker-level call frame. The runtime pushes one of these per
    ## active inline-call expansion; isReturn consults the top entry
    ## to wire the returned value into the caller's `retSym`.
    callee*:        string
    retSym*:        SymVal           ## the fresh symbol returned values bind to
    retName*:       string           ## "" for void
    retTy*:         IRType
      ## RFC-0005 S8l. The callee's return type; nil for a void proc. A
      ## bare `return` that never assigned `result` binds `retSym` to this
      ## type's zero value (`completeReturn`). RFC-0005 S8m: a closure
      ## descent carries its lambda's `retTy` too (a void lambda's is the
      ## `bool` placeholder its unread `funcApp` is sorted by).
    exits*:         CallExits      ## paths that hit `return` inside this call
    ptrRiskFormals*: seq[IRParam]
      ## RFC-0005 S8bn (item 3). The `var` formals whose actual a `ptr` of
      ## unknown origin may address (`IRStmt.cVarPtrSafe` code 0, or a
      ## caller's formal passed on that is itself one). A deref of such a
      ## pointer while this call runs declines when one may hold its
      ## pointee (`ptrTargets`): the walk copies the formal in and out.
    ptrSafeFormals*: seq[string]
      ## RFC-0005 S8bn (item 3). The other `var` formals: their actual is
      ## no pointer's target. A call in the body passing one on whole
      ## (code 2) inherits that.
    sp*:            uint
      ## RFC-0005 S8ca. The native stack pointer when the frame was pushed:
      ## the next call's depth check reads one level's stack cost from it
      ## (`nativeStackShort`).

  HandlerFrame* = object
    ## Phase 15 E1. One active `try`'s except-arms + finally, pushed onto the
    ## current call frame's `handlerStack` while the try-body is walked.
    ## Structural in E1 (the walker stubs `isTry` before any frame is pushed);
    ## E3+ populates and consults these on raise-flow propagation.
    handlers*:     seq[ExceptHandler]
    finallyBlock*: IRStmt   ## nil if no finally
    loopLen*:      int      ## RFC-0005 S8m: `w.loopStack.len` at the try's
                           ## entry. `routeRaise` walks a matched `except`
                           ## arm with the loop stack cut back to it: the
                           ## arm is lexically outside every loop the try
                           ## body entered, so a `break` there must not
                           ## reach one of them.

  ExnRecord* = object
    ## Phase 15 E1. An in-flight exception value (type + optional message).
    ## Set by the raise-flow walker (E2b+); unset/`none` until then.
    typeId*: string
    msg*:    Option[string]

  WalkerStatics* = object ## Phase 15 Z4: per-walker state, immutable after parse;
                         ## E1 fills exnTable/userExnHierarchy (empty until E4a),
                         ## C2a (closureSyms), R1 (refSorts...).
    exnTable*:         Table[string, seq[string]]
                        ## Phase 15 E1: static exception-type table (each type
                        ## name -> its full ancestor chain). Empty in E1;
                        ## populated at E4 from `exn_hierarchy.exnTypeTable`.
    userExnHierarchy*: Table[string, string]
                        ## Phase 15 E1: user-exn `child -> parent` map.
                        ## Populated E4a (`getImpl` walk); empty until then.
    sutRetTy*: IRType
    globals*: Table[string, IRGlobal]
                        ## RFC-0005 S8as: the program's module-level variables
                        ## by IR name (`SymexProgram.globals`): a read before
                        ## any write takes the entry value (`entryValueOf`),
                        ## and an opaque call rebinds those it may write.
                        ## RFC-0005 S8p: the SUT's own return type (nil for a
                        ## void SUT), from `SymexProgram.retTy`. The SUT frame
                        ## has no `CallFrame`, so `unwrittenResultZero` reads
                        ## its `result`'s zero value from here.
  EscapedRaise* = object
    ## Phase 15 E3. A raise that escaped its OWN call frame's handler stack
    ## without being caught — the per-frame channel the `isCall` descent arm
    ## drains after the callee returns, re-routing each escaped raise into the
    ## CALLER's handler stack (inter-procedural propagation). Carries the
    ## raise-site `Path` so heap/pc state at the raise point is preserved across
    ## the frame boundary (R1b merge — structurally threaded; inert until
    ## Cluster R).
    path*:   Path
    typeId*: string
    msg*:    Option[string]
    crash*:  bool          ## RFC-0005 S8cu: a nil dereference (`crashRaise`),
                          ## re-routed past every handler and `finally`

  ClosureRaise* = object
    ## RFC-0005 S7. A raise that escaped a closure body, awaiting routing from
    ## the calling path (`drainClosureRaises`). RFC-0005 S8bi: the exit facts
    ## of closure calls that completed EARLIER in the same expression (which
    ## hold on the raise path) are on that path already, put there by their
    ## `rskClosureExit` stage; this call's own facts, logged after its
    ## raises, are not (they assert the body did NOT raise). S7 carried the
    ## earlier facts here, as `priorExitPc`.
    raised*:      EscapedRaise
    writes*:      seq[(string, SymVal)]
                 ## RFC-0005 S8as. The by-reference names the call writes
                 ## back (`closureEnvWrites`), as THIS raising exit left
                 ## them: the raise leaves from the call with them.
    varOuts*:     seq[tuple[name: string, val: SymVal]]
                 ## RFC-0005 S8bh: the `var` formals' values where the body
                 ## raised, written to the caller's actuals on the raise path
                 ## (the callee wrote through their addresses before it
                 ## raised).

  AddrCellEntry* = tuple[local, cell: string; ty: IRType;
                        path: seq[string]; ixs: seq[SymVal]; bound: bool;
                        view: bool; slot: string]
    ## RFC-0005 S8ax. An address-taken variable of a frame
    ## (`CallFrameCtx.addrCells`): `local`, the env name of its pointer
    ## (`cell`) and the pointee type `ty`. RFC-0005 S8bs: a `bound` entry is
    ## a `var` formal bound to a location INSIDE a caller variable's cell
    ## (`bindVarLocs`): the cell holds the whole `ty` value, and the formal
    ## is the part at `path` (a field name, or `[` for an index, the next of
    ## `ixs`). Its pointer is under `varLocCellName`, never the formal's own
    ## `addr` cell, and it never leaves the call (`carryAddrCells`).
  ## RFC-0005 S8bu: a `view` entry is a by-value seq formal sharing the
  ## memory of a caller variable whose address is taken (`bindVarLocs`):
  ## it follows the cell while the cell's elements are written in place, and
  ## its path is tainted once the cell's seq is assigned whole or resized
  ## (`syncAddrCells`).
  ## RFC-0005 S8bx (item 3): a `slot` entry is a `var` formal that IS the slot
  ## of the callee's Table formal `slot` at the key `ixs[0]` (an `mpairs` view
  ## passed with its Table, `bindViewAliases`). A Table has no heap cell (`addr
  ## t` declines), so it has no `cell`: the location is the Table's value in
  ## `Env`, and it never leaves the call.

  HeldPath* = tuple[depth: int, path: Path]
    ## A `caught` or `pendingReturn` entry: a path held for the `isTry` at
    ## handler depth `depth` (`depthOf`).
  HeldRaise* = tuple[depth: int, path: Path, typeId: string,
                    msg: Option[string]]
    ## A `pendingRaise` entry.
  HeldJump* = tuple[depth: int, path: Path, target: int, isCont: bool]
    ## A `pendingJump` entry.

  HeldExits* = object
    ## RFC-0005 review R5. The channels a frame holds for the `isTry` at an
    ## entry's depth, which claims them all at once (`claimAt`), in this
    ## order, after walking its body.
    caught*:       ExitChannel[HeldPath]
                                      ## Phase 15 E3: handler-body continuation
                                      ## paths from raises CAUGHT in this frame,
                                      ## tagged by the catching try's handler-stack
                                      ## depth. The owning `isTry` (at that depth)
                                      ## claims its entries after walking its body,
                                      ## merging them with the body's normal
                                      ## fall-through. This is what makes a caught
                                      ## raise EXIT the try rather than resume the
                                      ## try body after the raise site.
    pendingRaise*: ExitChannel[HeldRaise]
                                      ## Phase 15 E5: raises that found NO matching
                                      ## `except` arm but are guarded by an enclosing
                                      ## `finally` at `depth` (the deepest HandlerFrame
                                      ## with a non-nil `finallyBlock` at or below the
                                      ## raise's search position). The owning `isTry`
                                      ## (at that depth) claims its entries after
                                      ## walking its body, runs the finally on each
                                      ## raised continuation, then COMPOSES the result
                                      ## (finally-normal re-raises the original;
                                      ## finally-raise replaces it). This intercept is
                                      ## what makes a `finally` run on the RAISED exit
                                      ## path before the raise propagates onward.
    pendingReturn*: ExitChannel[HeldPath]
                                      ## RFC-0005 S8l: `return` exits guarded by a
                                      ## `finally` at `depth` (the deepest HandlerFrame
                                      ## with a non-nil `finallyBlock`), `result`
                                      ## already bound on `path.env`. The owning
                                      ## `isTry` claims its entries after walking its
                                      ## body, runs the finally on each, and sends the
                                      ## fall-through on outward (`exitReturn`): the
                                      ## return-exit twin of `pendingRaise`.
    pendingJump*: ExitChannel[HeldJump]
                                      ## RFC-0005 S8m: `break` / `continue` exits
                                      ## guarded by a `finally` at `depth` (the deepest
                                      ## HandlerFrame with a `finallyBlock` the jump
                                      ## leaves), bound for `w.loopStack[target]`. The
                                      ## owning `isTry` claims its entries after
                                      ## walking its body, runs the finally on each,
                                      ## and sends the fall-through on (`exitJump`):
                                      ## the jump twin of `pendingReturn`.

  FrameExits* = object
    ## RFC-0005 review R5. A call frame's exit channels
    ## (`CallFrameCtx.exits`).
    held*:         HeldExits
    escaped*:      ExitChannel[EscapedRaise]   ## Phase 15 E3: raises that escaped THIS
                                      ## frame's handlers; drained by the caller's
                                      ## isCall arm for inter-proc propagation.

  CallFrameCtx* = object  ## Phase 15 Z4: state pushed/popped per call descent;
                         ## E1 fills handlerStack/inFlightExn, C2b closureInlineCount.
    frameId*: int                      ## RFC-0005 S9: this descent's identity
                                      ## (0 = the SUT's own frame; each
                                      ## `pushFrame` mints the next id from
                                      ## `WalkCtx.frameIdCounter`). A closure
                                      ## records the id it was built under
                                      ## (`svClosure.closureFrame`).
    closureInlineCount*: int           ## Phase 15 C2b (ADR-0009 D6): the depth of
                                      ## NESTED closure-application descents at
                                      ## this frame. `lowerClosureCall` increments
                                      ## it before descending the lambda body and
                                      ## restores it after; a descent that would
                                      ## push past `settings.maxClosureInlineCount`
                                      ## is refused (`ceInlineBudgetExceeded`). C2a
                                      ## deferred this field (no descent until C2b).
    handlerStack*: seq[HandlerFrame]   ## Phase 15 E1: per-frame active tries.
    capCells*: seq[tuple[local, cell: string]]
                                      ## RFC-0005 S8ax: the by-reference
                                      ## captures a closure built (or applied)
                                      ## in this frame holds, each with its env
                                      ## cell (`capCellName`), kept equal to the
                                      ## local statement by statement
                                      ## (`syncCapCells`).
    addrCells*: seq[AddrCellEntry]
                                      ## RFC-0005 S8ax: the variables of this
                                      ## frame whose address was taken
                                      ## (`isNew.nAddrOf`), each with the env
                                      ## name of its pointer (`cell`) and its
                                      ## type; the variable and the heap at
                                      ## the pointer are kept equal statement
                                      ## by statement (`walk`). A path that
                                      ## has no `cell` binding never took it.
    outerNames*: seq[string]           ## RFC-0005 S8ax: the enclosing
                                      ## routines' variables this frame
                                      ## reaches by name (a nested routine's
                                      ## captures; a closure body's
                                      ## captures and globals).
    inFlightExn*:  Option[ExnRecord]   ## Phase 15 E1: the exn being propagated.
    exits*:        FrameExits          ## RFC-0005 review R5: this frame's raise
                                      ## and `finally` exit channels.
    raisedFinallyLoops*: seq[int]      ## RFC-0005 S8l/S8m: one entry per `finally` of
                                      ## this frame running on a RAISED exit (S8l's
                                      ## `raisedFinally` count), holding
                                      ## `w.loopStack.len` at its entry. A `return`
                                      ## there is backend-divergent
                                      ## (`eeFinallyReturnOnRaise`), and so is a
                                      ## `break` / `continue` that leaves it -- one
                                      ## whose target frame lies below the innermost
                                      ## entry (`eeFinallyJumpOnRaise`).


  WalkMode* = enum
    ## RFC-fuzzer-nextgen G1a: the concolic-bridge mode discriminant, threaded
    ## through the walker's per-construct dispatch (`walk`'s `case stmt.kind`,
    ## and `walkHeapArm`'s isDeref/isNew/isDerefWrite arm) so G1b/G2 can add
    ## concrete-guidance logic per arm without re-plumbing. `wmExplore` is the
    ## existing whole-proc-exploration walker (default; every current caller
    ## gets this — `WalkCtx`'s zero-value is `wmExplore`, ordinal 0). At G1a,
    ## `wmFollowConcrete` is INERT: no caller constructs a `WalkCtx` with it
    ## yet, and every arm's `case w.mode` seam is a no-op `discard` on both
    ## branches — behavior is byte-identical to pre-G1a regardless of `mode`.
    ## G1b fills `wmFollowConcrete` with draw-symbolication + concrete-trace
    ## constraint collection; G2 adds branch-flipping.
    wmExplore, wmFollowConcrete

  ConcolicBranchRecord* = object
    ## RFC-fuzzer-nextgen G2. One entry per `if`-decision `walkIfFollowConcrete`
    ## resolves along a concolic replay, in ENCOUNTER order — this is the
    ## "walker's own trace... identifies the branch" surface the RFC's
    ## mechanism-clarifications call for (frontier picks the corpus entry;
    ## THIS is what identifies the concrete branch to flip within it).
    prefixPc*: seq[Z3Bool]
      ## The path's `pc` as of ENTERING this if-statement — i.e. BEFORE any
      ## of ITS OWN branch predicates are lowered/appended. This is exactly
      ## the RFC step-4 "prefix constraints up to that branch": solving
      ## `prefixPc ++ [not observedTruth]` keeps everything upstream of this
      ## decision fixed while forcing a different outcome AT it.
    observedTruth*: Z3Bool
      ## The predicate that was concretely TRUE at this decision: the taken
      ## arm's own condition (`armTaken >= 0`), or the conjunction of every
      ## branch's negated condition when no `if`/`elif` arm fired (else body
      ## or plain fallthrough, `armTaken == -1`). Negating this one Z3Bool is
      ## the RFC's "flip the target branch predicate" — Z3 is free to land on
      ## whichever untaken sibling arm is feasible, not just the sequentially
      ## next one.
    armTaken*: int
      ## Index into `stmt.branches` that fired, or `-1` for else/fallthrough.
      ## Used post-solve to detect whether a materialized seed's replay
      ## actually changed the outcome AT THIS decision (the intended-vs-
      ## unrelated coverage split).

  ConcolicDefinedFact* = object
    ## RFC-0016 K10a-concolic (section 9.1 item 1). One operation a concolic
    ## replay executed whose undefined side the definedness axis names
    ## (`drainArithTraps`' `ub` deposits): `cond` is the undefined side,
    ## `at` the number of `if` decisions recorded when it was evaluated, so
    ## a flip of decision `k` carries every fact with `at <= k` (the
    ## operations on the prefix and in the target's own condition).
    cond*: Z3Bool
    kind*: UbKind = ubUnsignedDivZero
    site*: string
    at*: int

  IfSiteStat* = object
    ## RFC-0005 S8ax. How often one `if` arm (or else path) outside a
    ## recursion was checked, and how often the check dropped it.
    checks*, prunes*: int

  WalkCtx* = object
    z3*:        Z3Context
    target*:    SymexTarget
    params*:    seq[IRParam]
    mode*:      WalkMode   ## RFC-fuzzer-nextgen G1a. Zero-value `wmExplore` —
                           ## every existing construction site (`runSymexImpl`)
                           ## is unchanged and gets `wmExplore` for free.
    undefinedFound*: seq[RawUndefined]
                ## RFC-0016 K10a-target. The undefined behaviours `haltUndefined`
                ## reached and solved (`SymexResult.undefined`), at most
                ## `maxUndefinedFindings` per run under a target that is not
                ## `tUndefined`.
    found*:     seq[RawResult]   ## Phase 15 Z4: was Option[RawResult]. Accumulated
                                ## findings; shouldStop halts on the first sxSat
                                ## (sxRaised added to the stop set in E2a).
                                ## RFC-0005 S1c: CLEAN findings only
                                ## (`scSpurious notin pathTaint`) -- a SAT on a
                                ## spurious-tainted path goes to `candidates`.
    candidates*: seq[RawResult]
      ## RFC-0005 S1c (§2.3 "Candidate lifecycle"). Solved SAT findings
      ## (`sxSat` at `isTargetLabel`, `sxRaised` at `routeRaise`) whose path
      ## carries `scSpurious`: the enlarged program reaches the target, reality
      ## is unknown. A SEPARATE pool, not a filter over `found`, for one
      ## reason: `shouldStop` halts the whole walk on the first stopping entry
      ## in `found`, so a candidate there would end exploration before a clean
      ## witness on a sibling path was ever solved -- and the relaxation would
      ## LOSE a verdict today's engine earns. `shouldStop` never reads this
      ## pool. Consumed by `decideVerdict` (rule 4: any solved SAT blocks
      ## `sxUnsat`) and handed out on `RawResult.candidates` for S10's replay.
    sinks*:     LowerSinks       ## RFC-0016 D3c-2: what the `sync*` family appends to (`walk_state`)
    statics*:   WalkerStatics    ## Phase 15 Z4 — populated E1/C2a/R1
    frame*:     CallFrameCtx     ## Phase 15 Z4 — populated E1/C2a. The CURRENT
                                ## call frame's exception context (handler stack
                                ## + in-flight exn). Per-frame: a try opened in a
                                ## callee is invisible to the caller after return.
    frameStack*: seq[CallFrameCtx]  ## Phase 15 E1: saved caller frames. Every
                                ## isCall/generic/closure descent `pushFrame`s
                                ## (saves `frame`, installs a fresh empty one)
                                ## before walking the callee body and `popFrame`s
                                ## on return. See pushFrame/popFrame below.
    capSyncDepth*: int           ## RFC-0005 S8ax: the statement nesting depth
                                ## `walk` snapshots capture cells at
    frameIdCounter*: int         ## RFC-0005 S9: the last `CallFrameCtx.frameId`
                                ## `pushFrame` minted (ids are never reused
                                ## within a walk).
    runTaint*:  Taint
      ## RFC-0005 S1 (was `sawUnknown: bool`; `sawUnknown ≡ runTaint != {}`).
      ## The RUN coordinate — DERIVED, never written at a degrade site: the
      ## ONLY writer is `runSymexImpl`'s verdict assembly, which sets it to
      ## `runTaintOf(drained errors)` (`types.nim`). `{}` for the whole walk
      ## until then. Pinned by the writer grep-pin. RFC-0005 S1c: purely
      ## derived -- the transitional kindless ⊤ mark is gone, because no site
      ## skips solving a tainted path any more (the only unsolved outcome, a
      ## solver unknown, records `beSolverUndef`).
    settings*:  SymexSettings
    procs*:     Table[string, ProcSig]
    callStack*: seq[CallFrame]
    topExits*: CallExits
      ## RFC-0005 S8j. The paths that left the SUT through its OWN `return`
      ## (`isReturn` with an empty `callStack`), each with `result` bound to
      ## the returned value. `walk` never returns them (a `return` ends its
      ## statement list), so a driver that reads the SUT's normal exits
      ## joins them to the walk's fall-through survivors
      ## (`runConcolicCollectImpl`'s soundness pin).
    callStats*: Table[string, CallStat]
    loopStack*: seq[LoopFrame]   ## Phase 6: nested-loop tracking
    budgetOutDepths*: seq[seq[tuple[loop: int, iters: int]]]
      ## RFC-0005 S8y. The loop depths (`Path.loopIters`) of each tainted
      ## target hit whose solve ran out of budget (`solveTargetHit`).
    hitExtraction*: seq[SymexErrorInfo]
      ## RFC-0016 INT-32 (R1-33). The `feExtractionFailed` records the last
      ## CLEAN target hit's own witness extraction made (`solveTargetHit`),
      ## read by `admitSolvedHit` into that hit's
      ## `RawResult.witnessExtraction`. The shared sink holds every hit's.
    callCache*: Table[string, seq[CallCacheEntry]]
                       ## RFC-0005 S8ax: a bucket per `argShapeKey`; each
                       ## entry carries its exact arguments and the facts its
                       ## walk dropped (`CallCacheEntry`).
    activeCalls*: HashSet[string]
    depthWalks*: seq[int]
                       ## RFC-0005 S8ax: callee walks entered at each call
                       ## depth (`depthMayExtend`).
    depthHardHits*: int
                       ## RFC-0005 S8ax: declines at the hard call-depth
                       ## budget so far; an extension that sees this move
                       ## is abandoned at its root (`depthBail`).
    levelStack*: int    ## RFC-0005 S8ca: the most native stack one call
                       ## level has cost so far (`nativeStackShort`).
    extHardMark*: int   ## RFC-0005 S8ax: `depthHardHits` when the current
                       ## extension's root began, -1 outside one; once it
                       ## moves, no call under the root extends again.
    ifSites*: Table[pointer, IfSiteStat]
                       ## RFC-0005 S8ax: per-`if`-arm feasibility-check
                       ## record, keyed by the arm's IR node
                       ## (`ifArmInfeasible`).
    synthZ3*:   int
    initialEnv*: Env   ## snapshot before walking, used so witness
                      ## extraction reads the INITIAL param SymVals
                      ## (not values after `isAssign` mutations).
    # CR-9 Stage 5 Group-3 error/hint sinks:
    heapDepthErrors*: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (R9). LIVE accumulator for
                      ## `heDepthExhausted` (sevError) during a walk.
                      ## `heapDepthExhausted` has `w: var WalkCtx` so it
                      ## writes directly to `w.heapDepthErrors`; verdict-
                      ## assembly reads this field. Threadvar `heapDepthErrors`
                      ## remains fallback (no out-of-walk caller exists today).
    newFieldZeroErrors*: seq[SymexErrorInfo]
                      ## Cluster H Step C. LIVE accumulator for
                      ## `heNewFieldZeroUnsupported` (sevError) during a walk.
                      ## The `isNew` walker arm has `w: var WalkCtx` so it
                      ## writes directly to `w.newFieldZeroErrors`; verdict-
                      ## assembly reads this field. Threadvar
                      ## `newFieldZeroErrors` remains fallback.
    walkDegradeErrors*: seq[SymexErrorInfo]
                      ## v64 (chapulin catalog #5(b)/#6, Invariant 7). LIVE
                      ## accumulator for in-walk classified degrades that
                      ## occur OUTSIDE the lowering wrappers (whose threadvar
                      ## sink is reset at every wrapper entry): the
                      ## `maxLoopUnwind` k-unroll exhaustion and
                      ## `maxFrontierSize` prune sites (`beBudgetExhausted`;
                      ## RFC-0005 S6a split the prune off as
                      ## `beBudgetExhaustedPrune`)
                      ## and the isReturn composite-return drain guard
                      ## (`feUnsupportedOp`) — all previously either set
                      ## `w.sawUnknown` BARE (empty-errors sxUnknown) or
                      ## raised. Every site has `w: var WalkCtx`, so no
                      ## threadvar twin is needed. Drained (dedup'd by
                      ## message) into every verdict branch, exactly the R9
                      ## `heapDepthErrors` idiom.
    ptrFamilyHints*: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (R8). LIVE accumulator for `hePtrFamily`
                      ## (sevHint) during a walk. isDeref/isDerefWrite arms
                      ## write directly to `w.ptrFamilyHints` (they have
                      ## `w: var WalkCtx`); verdict-assembly reads this field.
                      ## Threadvar `ptrFamilyHints` remains fallback.
    unknownExnWarnings*: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (E4). LIVE accumulator for
                      ## `eeUnknownExnType` (sevWarning) during a walk.
                      ## `routeRaise` has `w: var WalkCtx` so it writes
                      ## directly to `w.unknownExnWarnings`; verdict-assembly
                      ## reads this field. Threadvar `unknownExnWarnings`
                      ## remains fallback for any non-walk callers.
    stmtStrayTaint*: Taint
    stmtStrayUb*: set[UbKind]       ## RFC-0016 W1-d3: `stmtStrayTaint`'s undefined
                      ## RFC-0005 review R1-04. Pending lowering taint
                      ## (`symval`'s lowering queue) that a walker lowering
                      ## entry point found already queued
                      ## (`claimStrayPendingTaint`): a deposit no earlier
                      ## lowering of this statement drained, so the path it
                      ## belongs to is not known. `walk` taints every path
                      ## the statement yields with it, and with any taint
                      ## still queued when the statement returns.
    closureVarOuts*: seq[tuple[name: string, val: SymVal]]
                      ## RFC-0005 S8bh. The `var` formals' exit values of the
                      ## closure calls lowered in the current expression,
                      ## each for the caller variable its actual names
                      ## (`applyClosureGround`); `drainPendingLowerEffects`
                      ## writes them onto the consuming path, in call order.
    exitClock*: ExitClock
                      ## RFC-0005 review R4, R5: the serial clock every exit
                      ## channel of the walk is bound to (`exits.nim`).
    closureRaises*: seq[ClosureRaise]
                      ## RFC-0005 S7. Raises that escaped a closure body's own
                      ## handlers during `applyClosureGround`'s descent (the
                      ## closure frame's `escaped` channel, captured before
                      ## `popFrame`). The call is lowered inside an expression,
                      ## so -- exactly like the scalar raise predicates above --
                      ## it cannot route them itself: `drainClosureRaises` (the
                      ## first stage of `drainScalarRaiseForks`) forks each one
                      ## off the calling path and routes it through the
                      ## CALLER's handlers, as the `isCall` arm does for a
                      ## named callee. Before S7 `popFrame` discarded them (a
                      ## raised target through a closure was a false `sxUnsat`).
                      ## Reset alongside the scalar raise sinks.
    callerHeaps*: Table[string, Z3AnyAst]
                      ## CR-9 Stage 6 Group-3 (currentCallerHeaps migration).
                      ## LIVE copy of the caller path's heaps, written by
                      ## `seedCallerHeapInWalkCtx` when a walk is active.
                      ## `applyClosureGround` reads from this field (not the
                      ## threadvar) when `currentWalkCtxPtr != nil`.
    callerHeapDepth*: int
                      ## CR-9 Stage 6 Group-3 (currentCallerHeapDepth
                      ## migration). Companion to `callerHeaps`.
    callerAllocCounters*: Table[string, int]
                      ## CR-9 Stage 6 Group-3 (currentCallerAllocCounters
                      ## migration). Companion to `callerHeaps`.
    callerLiveRefs*: Table[string, seq[Z3AnyAst]]
                      ## CR-9 Stage 6 Group-3 (currentCallerLiveRefs migration).
                      ## Companion to `callerHeaps` (CR-5 freshness seeding).
    callerElemCells*: seq[ElemCell]
                      ## RFC-0005 S8bu. The seeded path's element cells
                      ## (`seedCallerHeapInWalkCtx`): a closure call binds a
                      ## formal whose actual is an element of a seq with
                      ## element cells to its cell (`bindVarLocs`, from
                      ## `applyClosureGround`). Replaces S8bs's
                      ## `callerCellRoots`, whose roots declined such a call.
    closureExitHeaps*: Table[string, Z3AnyAst]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitHeaps
                      ## migration). LIVE exit-heap from the most recent
                      ## `applyClosureGround` call. Written by
                      ## `applyClosureGround`; drained by `drainClosureExitHeap`
                      ## which reads this field (not the threadvar) when a walk
                      ## is active. Threadvar `currentClosureExitHeaps` remains
                      ## fallback for the no-walk path.
    closureExitAllocCounters*: Table[string, int]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitAllocCounters
                      ## migration). Companion to `closureExitHeaps`.
    closureExitLiveRefs*: Table[string, seq[Z3AnyAst]]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitLiveRefs
                      ## migration). Companion to `closureExitHeaps`.
    closureDidMutateHeap*: bool
                      ## CR-9 Stage 6 Group-4 (currentClosureDidMutateHeap
                      ## migration). True iff `applyClosureGround` merged at
                      ## least one exit path this call; `drainClosureExitHeap`
                      ## skips the merge when false (fast path for heap-write-
                      ## free closures). Written by `applyClosureGround`,
                      ## read by `drainClosureExitHeap`, reset by
                      ## `seedCallerHeapInWalkCtx` (per-call reset, NI-1).
    procValueSites*: seq[string]
                      ## RFC-0016 W3-z R7. Every proc-valued variable
                      ## (`IRStmt.opaqueUndefinedVia`) an opaque call this walk
                      ## noted calls through: the run-wide set a replay must
                      ## name the routines of (`RawResult.procValueSites`).
    tailVia*: set[UbKind]
                      ## RFC-0016 W3-z R7. On the tail walk (`tailGate`): the
                      ## kinds an opaque call reached under the pins added
                      ## only through its proc-valued variables
                      ## (`IRStmt.opaqueUndefinedVia`); the walk went on past
                      ## it, and `verifyTailDefined` reports them apart.
    tailUb*: set[UbKind]
                      ## RFC-0016 0.10.0 review H2. On the tail walk
                      ## (`tailGate`): the kinds a degrade token newly put on
                      ## a path the pins do not rule out (`noteUbAtFork`), the
                      ## `{.noinit.}` read's `ubIndeterminateRead`. The token
                      ## is the only carrier of such a kind: its record is a
                      ## `dcFreshSymbol` one with no kind of its own, so
                      ## `verifyTailDefinedKinds` reads the kinds here.
    tailGate*: bool
                      ## RFC-0016 K10b. This is the whole-run gate's second
                      ## walk (`verifyTailDefined`): `wmFollowConcrete` under
                      ## a sat's model pins, past the label. `opaqueRaiseForks`
                      ## ends a path at an opaque call whose body may be
                      ## undefined (`IRStmt.opaqueUndefined`); the concolic
                      ## collect driver, also `wmFollowConcrete`, never sets it.
                      ## RFC-0016 W3-z R2/R6: the walk over-approximates the
                      ## run. A branch the pins and the `pc` leave open (a
                      ## global havoc, an opaque call's result: a fresh symbol
                      ## the pins do not fix) forks both arms
                      ## (`walkIfFollowConcrete`, `walkWhileFollowConcrete`),
                      ## as the explore walk does, and a `dcFreshSymbol`
                      ## record does not by itself untrust the tail: a fresh
                      ## symbol is a superset of what the real run computes,
                      ## and every undefined side it opens is still decided at
                      ## the op. The winner and a replay candidate walk alike.
    concreteEq*: seq[Z3Bool]
                      ## RFC-fuzzer-nextgen G1b. Only meaningful when
                      ## `mode == wmFollowConcrete`: one `drawVar == concreteLit`
                      ## equality per draw-linked symbolic variable, built ONCE
                      ## at concolic-entry setup (`runConcolicCollectImpl`) and
                      ## never asserted onto any `Path.pc` — kept OUT of the
                      ## live path so the symbolic draws stay free (unpinned)
                      ## for a later G2 flip-solve. `walkIfFollowConcrete`
                      ## consults it (via a SCRATCH solver, `newSolver` on the
                      ## side) purely to determine which arm the concrete
                      ## replay actually took.
    concolicAmbiguousBranches*: int
                      ## RFC-fuzzer-nextgen G1b. LIVE counter: incremented each
                      ## time `wmFollowConcrete`'s isIf/isWhile handler cannot
                      ## determine a branch's concrete outcome from
                      ## `concreteEq` alone (the condition depends on something
                      ## outside the symbolicated-draws fragment) — the
                      ## walker-boundary concretization case for CONTROL FLOW
                      ## specifically. `runConcolicCollectImpl` drains this into
                      ## `ConcolicYieldCounters.ambiguousBranches`.
    concolicAmbiguousByConstruct*: Table[WalkerConstructKind, int]
                      ## R28: the SAME degrade, keyed by which construct
                      ## (`wckIf`/`wckWhile`) produced it — see
                      ## `markAmbiguous` (the one proc that increments both
                      ## this and `concolicAmbiguousBranches` together, so
                      ## they can never drift apart) and
                      ## `ConcolicYieldCounters.ambiguousByConstruct`'s doc.
    definedFacts*: seq[ConcolicDefinedFact]
                      ## RFC-0016 K10a-concolic. Written by `drainArithTraps`
                      ## in `wmFollowConcrete` only; copied out to
                      ## `ConcolicCollectResult.definedFacts`.
    branchTrace*: seq[ConcolicBranchRecord]
                      ## RFC-fuzzer-nextgen G2. Only meaningful when
                      ## `mode == wmFollowConcrete`: appended once per `if`
                      ## decision by `walkIfFollowConcrete`, in encounter
                      ## order. `runConcolicCollectImpl` copies this out into
                      ## `ConcolicCollectResult.branchTrace` for
                      ## `runConcolicFlipImpl` to index by `targetBranchIndex`.
                      ## `wmExplore` never touches this field — byte-identical
                      ## walker behavior, no SW bump.
    followCutAt*: int  ## RFC-0016 K7c. `branchTrace.len` when the follow
                      ## `while` first hit `maxLoopUnwind` with the replay
                      ## still iterating (valid when `followCut`): every record
                      ## from there on is on the fabricated continuation.
    followCut*: bool   ## RFC-0016 K7c. Whether that cut happened.

  CallCacheEntry* = object
    ## Function summary: the (callee, argShape) pair maps to the Z3
    ## variable representing the return value plus the constraint
    ## delta added to the returning path. On a cache hit, the entry's
    ## retSym binds to the caller's retName and the pcDelta extends
    ## the current path's pc — no re-walking required.
    retSym*:  SymVal
    exits*:   seq[seq[Z3Bool]]
      ## The constraint delta of each exit, `retInit` first. RFC-0005 S8ax:
      ## one per exit path (explicit returns and fall-through alike), each
      ## replayed as its own path. Before S8ax only a callee with exactly
      ## one explicit-return path and no fall-through was cached, so an
      ## expression-bodied routine (`if k < 2: k else: ...`) never was.
    args*:    seq[SymVal]
      ## RFC-0005 S8ax. The actuals the summary was walked with. The bucket
      ## key (`argShapeKey`) is a hash of their Z3 ASTs, and Z3's AST hash is
      ## 32 bits and not injective: the BV64 literals 8472 and 45048 share
      ## one. A hit replayed the other literal's summary -- `id(45048)`
      ## returned 8472, a false verdict either way with `errors` empty. A hit
      ## now needs the same actuals, handle for handle (`cacheArgsSame`).
    outer*: seq[tuple[name: string, val: SymVal]]
      ## RFC-0005 S8be. The caller state outside the actuals the summary was
      ## walked with: every global and capture cell (`capCellName`) the
      ## call threads in (`threadOuterBindings`), and the captures it
      ## reaches. A hit needs the same values (`cacheOuterSame`), and only
      ## a summary none of whose exits wrote one is kept. S8an left any call
      ## that threaded such state uncached, which is every call in a frame
      ## holding a capture cell.
    pruneFacts*: seq[seq[Z3Bool]]
      ## RFC-0005 S8ax. Per drop the walk decided against its context
      ## (`ctxPruneLog`), the facts the callee's walk added beyond the
      ## caller's (path facts, defect-survivor facts, the arm). Each was
      ## UNSAT with the caller's facts; the summary is replayed only where
      ## each still is (`pruneFactsHold`).

type
  Rfc0005S1CarrierProbe* = object
    ## Observations `rfc0005S1CarrierProbe` reports (see its doc).
    hasTaintField*, hasNoUncertainField*: bool
    forkPathPropagated*: Taint
    forkTaintedJoined*, forkTaintedParentUntouched*: Taint
    walkSinkKinds*: seq[SymexErrorKind]
    walkSinkSeverities*: seq[SymexErrorSeverity]
    tokenPath*: Taint
    heapDepthSinkKinds*, newFieldZeroSinkKinds*: seq[SymexErrorKind]
    closureSinkKinds*, closureThreadvarKinds*: seq[SymexErrorKind]
    runTaintBeforeDrain*: Taint
    taintInPlaceJoined*: Taint
    returnMergeJoined*, returnMergeCleanStaysClean*: Taint
    lowerPendingAfter*: Taint
    loweringSinkKinds*: seq[SymexErrorKind]
    lowerDrainedPath*, lowerPendingAfterDrain*: Taint
    # RFC-0016 W1-d3: `Path.undefined` through every carrier that joins taint.
    undefForkPropagated*, undefForkTaintedJoined*: set[UbKind]
    undefForkTaintedParentUntouched*, undefInPlaceJoined*: set[UbKind]
    undefReturnMergeJoined*, undefReturnMergeCleanStaysClean*: set[UbKind]
    undefLowerDrained*, undefLowerPendingAfterDrain*: set[UbKind]
    undefTokenFromKind*: set[UbKind]

  Rfc0005S1LeakPinProbe* = object
    ## Observations `rfc0005S1LeakPinProbe` reports (see its doc).
    cleanStampedKinds*: seq[SymexErrorKind]
    leakStampedKinds*: seq[SymexErrorKind]
    leakStampedSeverities*: seq[SymexErrorSeverity]
    pendingAfterStamp*: Taint

type
  PendingLowerEffects* = object
    ## RFC-0005 S7. Everything a `lower()` in progress has deposited for its
    ## enclosing walk arm to drain, plus the caller-heap seed it lowers under.
    ## `applyClosureGround` descends a closure body with the LIVE walker from
    ## INSIDE that `lower()`, and the body's own statement arms reset, seed
    ## and drain these same sinks -- so before S7 a descent silently consumed
    ## the calling expression's pending effects: an argument's raise
    ## predicate was wiped (a false `sxUnsat`), an earlier closure's exit
    ## facts and heap were dropped, a pending decline's path taint landed on
    ## the body's path instead of the caller's, and the caller-heap seed
    ## became the body's. `takePendingLowerEffects` sets them aside (and
    ## clears the sinks) before the descent; `restorePendingLowerEffects` puts
    ## them back after it, before the call deposits its own.
    queue*: PendingDegrade                     ## RFC-0016 INT-34 (W1-d3: with its `ub`)
    parseInt*: seq[ParseIntRaise]              ## RFC-0005 S10
    divByZero*, overflow*, strIndexOob*, seqOob*: seq[Z3Bool]
    convBound*: seq[ConvBound]
    rangeDefect*: seq[Z3Bool]
    arithTrap*: seq[ArithTrap]                    ## RFC-0005 S8i
    uninitRead*: seq[Z3Bool]                   ## RFC-0005 S8bv
    regexRaise*: seq[string]                   ## RFC-0005 S8ay
    raiseOrder*: seq[RaiseSinkKind]            ## RFC-0005 S8bb
    closureRaises*: seq[ClosureRaise]
    closureVarOuts*: seq[tuple[name: string, val: SymVal]]   ## RFC-0005 S8bh
    exitPc*: seq[Z3Bool]
    didMutate*: bool
    exitHeaps*: Table[string, Z3AnyAst]
    exitAlloc*: Table[string, int]
    exitLiveRefs*: Table[string, seq[Z3AnyAst]]
    callerHeaps*: Table[string, Z3AnyAst]
    callerHeapDepth*: int
    callerAlloc*: Table[string, int]
    callerLiveRefs*: Table[string, seq[Z3AnyAst]]
    envWrites*: seq[(string, SymVal)]          ## RFC-0005 S8as
    readNames*: seq[string]                    ## RFC-0005 S8as

type TargetSolveCost* = enum
  ## RFC-0005 S8ag. What a target-hit solve's spend says about it.
  tscCheap      ## neither below
  tscBudgetOut  ## unknown, with the whole budget spent (S8y)
  tscSlowSat    ## SAT, with at least half the budget spent: `checkCapped`'s
                ## capped step 1 ran out and the uncapped step 3 found it

type
  VerdictDecision* = object
    ## RFC-0005 S1c. The outcome of `decideVerdict`: the status the run
    ## reports and, for `sxSat`/`sxRaised`, the index of the winning entry in
    ## `found` (`-1` otherwise).
    status*:    SymexStatusKind
    winnerIdx*: int

type AddrCarry* = tuple[moved: seq[Z3AnyAst]; lost: seq[string];
                       unowned: seq[Z3AnyAst]]
  ## RFC-0016 S8ch: `unowned` are cells that became a module-level variable's
  ## (a `var` formal bound to it): its storage never dangles.

type
  InternalVerdictKind* = enum
    ## Phase 15 E2b. PRIVATE intermediate verdict produced by the raise-flow
    ## walker. It is deliberately NOT the public `SymexStatusKind`/`RawResult`:
    ## a raise that is caught by an enclosing handler (E3+) must never surface as
    ## a public `sxRaised`. Only `runSymex` converts an `ivRaised` that escapes
    ## the SUT boundary into a public `RawResult{sxRaised}` via `toPublic`
    ## (Invariant 9 — single boundary conversion).
    ivSat, ivUnsat, ivUnknown, ivRaised

  InternalVerdict* = object
    case kind*: InternalVerdictKind
    of ivSat:
      satWitness*: RawWitness
    of ivUnsat, ivUnknown:
      discard
    of ivRaised:
      raisedTypeId*: string
      raisedMsg*:    Option[string]
      raisedWitness*: RawWitness
      raisedIsDefect*: bool   ## Phase 15 E6. True iff the raised type is a Nim
                             ## `Defect` subtype (populated at the boundary from
                             ## `exnTable.isDefect`).

type DepthCut* = enum
  ## RFC-0005 S8ca. Why `depthBail` declines a call.
  dcutFrontier   ## the frontier was growing: the budget was not extended
  dcutHard       ## the hard budget was reached (here or under an abandoned
                 ## extension)
  dcutStack      ## the native stack left is under the walk's reserve

type DiscOutcome* = object
  ## RFC-0005 S8cp (item 2). One way an assignment to a discriminator goes.
  cond*: Z3Bool                            ## when it goes this way
  arms*: OrderedTable[int, seq[SymVal]]    ## the arm fields after it
  havoc*: bool     ## the arm holds a fresh value (`feUncheckedDiscBytes`)
  decline*: bool   ## a field of the arm has no fresh or zero value here
  keepImage*: bool ## PRC-07 slice B (c): the union image is carried over; the
                  ## new arm's fields are read from it (no havoc)

type FollowOutcome* = enum
  ## RFC-0016 W3-z int6. What a follow-mode branch's scratch asks say.
  foTrue    ## the pins (and the `pc` the walk asked with) decide `cond` true
  foFalse   ## ... decide it false
  foOpen    ## they do not decide it
  foOffRun  ## tail walk only: both sides are UNSAT, so the pins contradict
            ## the path itself and it is not the followed run

template forEachExitGroup*(w, g, body: untyped) =
  ## RFC-0005 review R5. Run `body` with `g` naming each exit group a walk
  ## keeps, in turn: the SUT's own returns (`topExits`), each call's
  ## (`CallFrame.exits`), each loop frame's (`LoopFrame.exits`), and the
  ## current call frame's raise and `finally` channels (`CallFrameCtx.exits`).
  ## Saved caller frames (`frameStack`) are not reached: a statement parks
  ## only on the frame it runs in, and one that pushes a frame pops it before
  ## it returns.
  block:
    template g(): untyped = w.topExits
    body
  for f in w.callStack.mitems:
    template g(): untyped = f.exits
    body
  for f in w.loopStack.mitems:
    template g(): untyped = f.exits
    body
  block:
    template g(): untyped = w.frame.exits
    body

const
  exitGroupsWalked* = ["WalkCtx.topExits", "WalkCtx.callStack",
                      "WalkCtx.loopStack", "WalkCtx.frame", "CallFrame.exits",
                      "LoopFrame.exits", "CallFrameCtx.exits"]
    ## RFC-0016 INT-35 (R6-03). What `forEachExitGroup` reaches: each field
    ## of a walk or frame type that holds an exit group, or a frame or a seq
    ## of frames holding one.
  exitGroupsUnwalked* = ["WalkCtx.frameStack"]
    ## Saved caller frames: a statement parks only on the frame it runs in.

template isExitGroupType*(T: typedesc): bool =
  T is CallExits or T is LoopExits or T is FrameExits

template isExitFrameType*(T: typedesc): bool =
  T is CallFrame or T is LoopFrame or T is CallFrameCtx

proc collectExitGroupFields*[T: object](x: T; owner: static string;
                                       acc: var seq[string]) =
  ## RFC-0016 INT-35 (R6-03). Every field of `x` that holds an exit group
  ## (directly, as a frame, or as a seq of frames), as `owner.field`. One
  ## that `exitGroupsWalked` and `exitGroupsUnwalked` do not name is a
  ## compile error: a group `forEachExitGroup` does not visit is stamped by
  ## no statement and claimed by no `try`.
  for name, f in fieldPairs(x):
    when isExitGroupType(typeof(f)) or isExitFrameType(typeof(f)):
      const path = owner & "." & name
      when path notin exitGroupsWalked and path notin exitGroupsUnwalked:
        {.error: "RFC-0016 INT-35: `" & path & "` holds an exit group " &
                 "that forEachExitGroup does not visit".}
      acc.add path
      when isExitFrameType(typeof(f)):
        collectExitGroupFields(f, $typeof(f), acc)
    elif typeof(f) is seq:
      when isExitGroupType(typeof(f[0])) or isExitFrameType(typeof(f[0])):
        const path = owner & "." & name
        when path notin exitGroupsWalked and path notin exitGroupsUnwalked:
          {.error: "RFC-0016 INT-35: `" & path & "` holds exit groups " &
                   "that forEachExitGroup does not visit".}
        acc.add path
        when isExitFrameType(typeof(f[0])):
          var e: typeof(f[0])
          collectExitGroupFields(e, $typeof(f[0]), acc)
