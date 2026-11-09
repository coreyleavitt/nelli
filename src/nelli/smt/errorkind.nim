## RFC-0016 §8.1 -- the symex error vocabulary, in a leaf module that
## imports nothing: `SymexErrorSeverity`, `SymexErrorKind` and the
## `UbKind` range of its `ub*` members.
##
## Why a leaf. `admission.nim` (the cell identity and `Admit`/`Row`/
## `AxisTable`) names `SymexErrorKind` in every decline, and the engines
## that own a payload type (`pcre_engine.admitPcreLib`) build on
## `admission`. `buildprofile.nim`, which `types.nim` imports, reads the
## PCRE host through `pcre_engine`. With the enum inside `types.nim` that
## was the cycle `types -> buildprofile -> pcre_engine -> admission ->
## types`. The layering is now: this leaf, then `admission`, then
## `pcre_engine`, then `buildprofile`, then `types` (which imports and
## re-exports this module, so every name is still reachable where it was).

type
  SymexErrorSeverity* = enum
    ## Phase 15 Z3. Severity contract (cross-cluster invariant 7):
    ## an `sxUnknown` result must carry >= 1 `sevError`; a result whose
    ## errors are all `sevHint`/`sevWarning` must resolve to sat/unsat.
    sevHint     ## classified hint — informational; does NOT force sxUnknown
    sevWarning  ## non-fatal issue; walker continues; verdict may be valid
    sevError    ## halting error — causes sxUnknown result

  SymexErrorKind* = enum
    ## Phase 15 Z3. Closed set of classified symex error kinds, replacing
    ## the free-form `kind: string`. Prefixes: ek=Z3 engine, fe=front-end,
    ## se=string/seq, ee=exception, ge=generics, ce=closure, he=heap/ref.
    ## Phase-14 Z3Error kinds come first so Phase-15 kinds keep higher ordinals.
    ##
    ## STANDING RULE (RFC-0005 §3.2), which no mechanism can check: reusing an
    ## EXISTING kind at a NEW emission site asserts that the new site shares
    ## that kind's substitution class (`classOf`, below: what the site
    ## SUBSTITUTES -- a fresh unconstrained symbol, a forced value / stale
    ## env, a fabricated continuation, a pure omission, or no answer at all).
    ## `classOf`'s exhaustive `case` forces a row for a NEW kind but cannot
    ## see a reused one. If your site's class differs, split: tail-append ONE
    ## sibling for the minority funnel and keep this member for the majority
    ## (never retire-and-append-two -- each retirement is a permanent
    ## tombstone in every consumer `case`).
    ekZ3Error, ekZ3MemoryError, ekZ3InternalError, ekZ3SolverError,
    feUnsupportedOp, feExtractionFailed,
    feConvDomainExcluded, ## retired R16-2 — do not reuse ordinal.
                          ## (Was: sevHint emitted when float→int conversion domain
                          ## was bounded to the target integer range. Replaced by a
                          ## real RangeDefect raise fork in R16-2; the hint emission
                          ## was removed. Ordinal kept for CR-16 cache-key stability.)
    seUnsupportedStringOp, seUnsupportedRegex, seZ3StringIncomplete,
    seZ3VersionMissing,   ## Phase 15 S5: op requires a newer Z3 (e.g.
                          ## `Z3_mk_seq_replace_all`, absent < 4.15.5).
    seBytesSymbolicLength, ## RETIRED RFC-0005 S8c -- retained for ordinal
                           ## stability, NEVER EMITTED. Was the `bytes(s)`
                           ## model's symbolic-length decline; that model was
                           ## reachable only through a USER proc named `bytes`
                           ## (Nim's stdlib has none), and S8c walks user
                           ## routines instead of name-matching them.
    seBytesLengthTooLarge, ## RETIRED RFC-0005 S8c -- as `seBytesSymbolicLength`
                           ## (the same deleted `bytes(s)` model's length cap).
    seByteIndexUnsupported, ## reserved/unused: no distinct runtime degrade site
                            ## for symbolic byte-index constructs — string index
                            ## `s[i]` is handled upstream through a different path
                            ## (the walker resolves the BV8 element directly).
                            ## Retained for enum ordinal stability (shifting would
                            ## invalidate any external consumer relying on ordinal
                            ## values).
    seByteIterUnsupported,
    seUnsupportedTableValType, seUnsupportedSetCharInterop,
    seNestedSeqUnsupported,
    seParseIntPreE,       ## Phase 15 S10a: parseInt non-digit input returned an
                          ## unconstrained model until S10b's raises-path landed.
                          ## NO LONGER EMITTED (S10b closed the window — a non-digit
                          ## parseInt now RAISES `ValueError`). Variant retained for
                          ## enum/cache stability; the emission is gone.
    eeUninterpRefExtraction,
    eeRaiseUnimplemented,  ## Phase 15 E1: walker hit an `isRaise` while
                           ## raise-flow semantics are not yet modeled
                           ## (structural cycle). sevError → sxUnknown.
    eeTryUnimplemented,    ## Phase 15 E1: walker hit an `isTry` while
                           ## try/except semantics are not yet modeled.
    eeRaiseOutsideHandler, ## Phase 15 E2b: a bare `raise` (re-raise) reached
                           ## with an empty handler stack and no in-flight
                           ## exception — nothing to re-raise. sevError →
                           ## sxUnknown (Invariant 3).
    eeNotInHandler,        ## Phase 15 E8: `getCurrentException()` /
                           ## `getCurrentExceptionMsg()` called outside any
                           ## `except` handler body (no in-flight exception).
                           ## sevError → sxUnknown (Invariant 3 — never a panic).
    eeUnknownExnType,      ## Phase 15 E4: a raised exception type is not in the
                           ## static `ExnTypeTable` nor `userExnHierarchy`. The
                           ## walker matches it ONLY against a bare `except:`
                           ## (conservative — no silent false-negative,
                           ## Invariant 3). sevWarning (verdict may still be
                           ## valid; the type may simply not be modeled yet).
    geInstantiationCapped, geConceptViolation,
    geUnresolvedGeneric,   ## reserved/unused: unresolved-generic constructs
                           ## produce a compile-time error() or fall to
                           ## geInstantiationCapped + sawUnknown → sxUnknown;
                           ## this variant is NEVER emitted. Retained for enum
                           ## ordinal stability (shifting would invalidate any
                           ## external consumer relying on ordinal values).
    geDistinctBijectivitySkipped,
    geDistinctBarrier,    ## Phase 15 G4 (net-new, sevError): an operation
                          ## attempted an IMPLICIT coercion between a `distinct`
                          ## type and its base (or two distinct types) without an
                          ## explicit conversion. The type wall forbids it
                          ## (Invariant 3 — classified, never a silent UNSAT).
    ceNotImplemented,
    ceUnsupportedCapture,  ## reserved/unused: a `ref T`-capturing closure was
                           ## previously classified here (before R13 landed the
                           ## heap machinery). R13 lifts the restriction; captures
                           ## of ref/ptr locals now succeed. This variant is NEVER
                           ## emitted. Retained for enum ordinal stability.
    ceUnsupportedHof,
    ceClosureUnknownCallee, ## Phase 15 C2b (ADR-0009 D6, Invariant 3): a
                            ## closure CALL whose callee variable does not
                            ## resolve to an `svClosure` in the current env
                            ## (e.g. a proc value the walker never bound).
                            ## sevError → sxUnknown (classified, never a
                            ## silent UNSAT or a crash).
    ceInlineBudgetExceeded, ## Phase 15 C2b: closure-application descent
                            ## exceeded `settings.maxClosureInlineCount`
                            ## (the `CallFrameCtx.closureInlineCount` budget).
                            ## sevError → sxUnknown (Invariant 3).
    heDepthExhausted, heUnsafeCast,
    hePtrArith,            ## RETIRED RFC-0005 S8c -- retained for ordinal
                           ## stability, NEVER EMITTED. Its one producer keyed
                           ## on `inc`/`dec` over a `ptr` operand, a call that
                           ## exists only as a USER overload (`system.inc`
                           ## takes an Ordinal); S8c walks that user routine.
                           ## Real pointer arithmetic goes through `cast`,
                           ## which records `heUnsafeCast`.
    hePtrFamily,
    heFreshnessCapExceeded, heUnsupportedVarRef,
    # `heRefVariantUnsupported` stood here until RFC-0005 S8m: S8l modelled
    # every ref-variant shape it declined, and S8m retired it; its six
    # unreachable carriers raise `weInternalWalkerFault` now.
    heUnsupportedOwnership,
    heUnresolvedRef,       ## Phase 15 R1a (ADR-0010): the walker reached an
                           ## `itRef`/`itPtr`/`isDeref`/`isNew` while the
                           ## logical-heap semantics are not yet modeled
                           ## (structural cycle). sevError → sxUnknown
                           ## (Invariant 3). R1+ replace the stub with real
                           ## heap semantics. RFC-0005 S4: `liftHeapValue`'s
                           ## unsupported-pointee read no longer emits this
                           ## kind (split to `heUnsupportedPointeeRead`).
    geVtableDispatch,      ## Phase 16 INV (reserved/unused): subtype-dispatch /
                           ## vtable method call — when a `nnkMethodDef` callee
                           ## reaches `ensureProcRegistered`, the current walker
                           ## fires a compile-time `error()` rather than yielding
                           ## a classified sxUnknown (Phase 15 deferred; a future
                           ## phase wires the emission). NEVER EMITTED. Appended
                           ## at enum tail to preserve ordinal stability of all
                           ## preceding members (shifting would invalidate any
                           ## external consumer relying on ordinal values).
                           ## sevError → sxUnknown (Invariant 3).
    ceClosureBodyUncertain ## RFC-chapulin-hardening SND-1b (walker v39): a
                           ## closure-body return sub-path had `cp.uncertain ==
                           ## true` (SND-1 taint from an unmodeled statement,
                           ## or a nested maxCallDepth bail) — `applyClosureGround`
                           ## SKIPS folding that sub-path into
                           ## `currentClosureCallAxioms` (would otherwise
                           ## assert a possibly-wrong value as a PERMANENT
                           ## ground fact for the rest of the run) and instead
                           ## pushes this kind (through SND-1b the whole-run
                           ## `closureForcedUnknown` read it; RFC-0005 S9
                           ## deleted that veto -- the path taint below is
                           ## what keeps the verdict honest).
                           ## Appended at enum tail (ordinal stability).
                           ## RFC-0005 S7: also joins `{scSpurious}` onto the
                           ## calling path (`closureDegrade`); the result is a
                           ## per-occurrence fresh constant (`dcFreshSymbol`).
    weInternalWalkerFault ## RFC-chapulin-hardening CR-1c (walker v43,
                          ## ADR-0020): the walker's last-resort safety net —
                          ## the final `except CatchableError` catch-all on the
                          ## `runSymex` try (`runtime.nim`) — classified a
                          ## genuinely UNANTICIPATED native exception (one that
                          ## matched NONE of the specific arms: NOT one of the
                          ## 18 named construct-gap carriers, NOT
                          ## `SymexClassifiedDegradeError`, NOT a `Z3Error`)
                          ## that escaped the walker from any dispatch depth.
                          ## DISTINCT from every `se*`/`fe*` construct-gap kind
                          ## by design: it means "the walker itself hit a bug
                          ## here", not "this SUT construct isn't modeled yet"
                          ## — CI/telemetry can track its occurrence as a live
                          ## walker-bug backlog (§0's totality-is-an-audit
                          ## philosophy) rather than treat it as an ordinary
                          ## degrade. sevError → sxUnknown (Invariant 3 — never
                          ## a crash, never a silent wrong sat/unsat). Appended
                          ## at enum tail (ordinal stability).
    beBudgetExhausted     ## Chapulin 0.1.0 re-test triage (catalog #5(b),
                          ## walker v64): a WALK BUDGET ran out with paths
                          ## still live — `maxLoopUnwind` k-unroll exhaustion
                          ## (the loop guard was still SAT-able past the
                          ## bound). RFC-0005 S6a narrowed it to exactly that
                          ## (`dcFabricated`): the `maxFrontierSize` prune is
                          ## now `beBudgetExhaustedPrune` and the
                          ## `maxCallDepth` / variant-constructor bails are
                          ## `beBudgetExhaustedUnmodelled`. The
                          ## affected paths are tainted/pruned and the run
                          ## degrades to `sxUnknown`; before v64 these sites
                          ## set `w.sawUnknown` bare, producing the
                          ## Invariant-7-violating "sxUnknown with EMPTY
                          ## errors" chapulin's re-test flagged. sevError →
                          ## sxUnknown. Appended at enum tail (ordinal
                          ## stability).
    feUnsupportedExprKind ## RFC-chapulin-hardening CR-2a (walker v44):
                          ## `parseExpr`'s expression-position catch-all
                          ## (`dsl_parser.nim`) reached a NimNode `kind` not
                          ## in its `case` — previously a macro-expansion
                          ## `error()` that aborted compilation outright
                          ## (strictly worse than `sxUnknown`; the SUT could
                          ## not be analysed at all). Now registers this
                          ## classified `sevError` and emits `mkUnsupported`
                          ## into the preamble, returning a type-correct dummy
                          ## (`classifyType(n).ty`). Sound because `of
                          ## isUnsupported` taints `Path.uncertain` (SND-1) —
                          ## the dummy can never produce a false witness; also
                          ## Class-A: the parse record joins the walk's reach
                          ## record on the marker (RFC-0005 S9; was the
                          ## `capForcedUnknown` backstop). Covers the whole expression-
                          ## position macro-error class (M2/M5/P1/P2a shapes).
                          ## Appended at enum tail (ordinal stability).
    feUnsupportedParamType ## RFC-chapulin-hardening CR-2b (walker v45):
                          ## `classifyType`'s resolved-type-name text-match
                          ## catch-all (`dsl_typebridge.nim`) reached a
                          ## PARAMETER type not in its supported scalar set
                          ## — previously a macro-expansion `error()` that
                          ## aborted compilation outright, before any proc
                          ## body was even walkable. A different mechanism
                          ## from `feUnsupportedExprKind` (CR-2a):
                          ## `classifyType` takes no `ctx`/`preamble`, so
                          ## there is no statement to taint and no sound
                          ## dummy `IRType`. Now classifies to an
                          ## `itUninterp("__unsupported:" & s)` placeholder;
                          ## `allocateSym` raises the generic
                          ## `SymexClassifiedDegradeError` carrier (CR-1c)
                          ## with this kind at parameter-allocation time —
                          ## before the body is walked — forcing a
                          ## WHOLE-RUN `sxUnknown` (Invariant 3 — never a
                          ## compile failure, never a walk-time crash).
                          ## Appended at enum tail (ordinal stability).
    feUnsupportedWitnessType ## RFC-chapulin-hardening CR-2c (walker v46):
                          ## `emitTyAndReader` (`symex.nim`) — the POST-
                          ## SOLVE witness-reader codegen macro, a THIRD
                          ## macro-`error()` surface distinct from CR-2a
                          ## (SUT-body parse) and CR-2b (param-type
                          ## classify) — reached a `seq`/`Table`/`HashSet`
                          ## element/key/value shape outside its fixed
                          ## renderable fragment (`isRenderableSeqElemTy`/
                          ## `isRenderableTableTy`/`isRenderableSetElemTy`
                          ## above) — previously a macro-expansion `error()`
                          ## that aborted compilation outright. `parseProc*`'s
                          ## TOP-LEVEL SUT parameter-classification loop
                          ## (`dsl_parser.nim`) now runs each parameter's
                          ## `classifyType` result through
                          ## `demoteUnrenderableWitnessTy`, applying the SAME
                          ## renderability predicate, and demotes an
                          ## unrenderable shape to an
                          ## `itUninterp("__unsupported_witness:" & s)`
                          ## placeholder instead of a real `itSeq`/`itTable`/
                          ## `itSet` (deliberately NOT inside `classifyType`
                          ## itself — it is also used for purely-internal,
                          ## non-witness types); `allocateSym` raises the generic
                          ## `SymexClassifiedDegradeError` carrier (CR-1c)
                          ## with this DISTINCT kind (not
                          ## `feUnsupportedParamType` — a different macro,
                          ## different call site, per §0's three-classes
                          ## framing) at parameter-allocation time — before
                          ## the body is walked and before the witness
                          ## reader is ever reached — forcing a WHOLE-RUN
                          ## `sxUnknown` (Invariant 3 — never a compile
                          ## failure, never a walk-time crash). Appended at
                          ## enum tail (ordinal stability).
    heNewFieldZeroUnsupported ## Cluster H Step C (ADR-0022): the universal
                          ## `isNew` zero-write (`runtime_heap.nim`) found a
                          ## freshly-allocated object FIELD whose type has no
                          ## clean zero encoding this cycle
                          ## (`zeroIRExprForType` returned `nil` — a
                          ## `seq`/`Table`/`HashSet`/`array`/variant/distinct
                          ## field). SND-1 taints the whole run to `sxUnknown`
                          ## (Invariant 3) rather than leaving that field's
                          ## heap cell unconstrained (which would risk a false
                          ## `sxSat`). Appended at enum tail (ordinal
                          ## stability).
    seUnsupportedTableKeyType ## N40 (round-6 fix round 6, allocateSym
                          ## totality). `allocateSym(itTable)`'s Table KEY
                          ## type is not modeled (only `Table[string, V]` is
                          ## backed — the Z3 array representation is always
                          ## `Z3Array[Z3String, ...]`). Previously an untagged
                          ## `raise newException(ValueError, ...)` — a crash on
                          ## ORDINARY user syntax (`Table[int, string]` is a
                          ## perfectly valid Nim type, not a walker-internal
                          ## invariant state), which `unallocatableFieldIssue`
                          ## (below) had a false-negative gap for prior to this
                          ## slice. DISTINCT from `seUnsupportedTableValType`
                          ## (the pre-existing sibling for a bad VALUE type)
                          ## so a human reading `errors[0].kind` can tell which
                          ## half of the `(K, V)` pair was unsupported.
                          ## sevError → sxUnknown (Invariant 3 — never a
                          ## crash, never a silent UNSAT). Appended at enum
                          ## tail (ordinal stability).
    seUnsupportedCompoundSortLeaf ## Round-6 N41: `rawAnyAstOf` (`runtime.nim`)
                          ## derives a SINGLE scalar leaf ast/sort for a
                          ## closure funcSym domain/range leaf (`sortOfTuple`)
                          ## or a heap array's value sort (`heapValueSort`,
                          ## `runtime_heap.nim`) — `svTable`/`svSet` are
                          ## COMPOUND values (a data `Z3Array` plus a separate
                          ## present `Z3Array`, never a single scalar ast), so
                          ## there is no sound representative leaf here,
                          ## REGARDLESS of whether the underlying Table/Set
                          ## shape itself is otherwise supported (DISTINCT
                          ## from `seUnsupportedTableKeyType`/
                          ## `seUnsupportedTableValType`/
                          ## `seUnsupportedSetCharInterop`, which classify an
                          ## unsupported KEY/VALUE/ELEMENT type specifically —
                          ## a perfectly valid `Table[string, int]` closure
                          ## param hits THIS gap instead). Previously an
                          ## untagged `raise newException(ValueError, ...)` —
                          ## a crash that escaped uncaught to the top-level
                          ## `runSymexImpl` catch-all (`weInternalWalkerFault`,
                          ## a WHOLE-RUN degrade with no per-path precision),
                          ## masking the itTable/itSet family behind the
                          ## walker's generic "the walker itself hit a bug"
                          ## carrier instead of a construct-gap kind.
                          ## sevError → sxUnknown (Invariant 3 — never a
                          ## crash, never a silent wrong sat/unsat). Appended
                          ## at enum tail (ordinal stability).
    beBudgetExhaustedAssumedBound ## N20 (RFC-chapulin-hardening bucket-2,
                          ## walker v121). RFC-0005 S8k superseded the
                          ## history below: the k-unroll now walks an arm
                          ## only if it is feasible on the path, so an
                          ## assume that really bounds the loop records
                          ## nothing, and this kind fires only where the
                          ## assumed bound does not end the loop within
                          ## `maxLoopUnwind` (or the check ran out of
                          ## `loopPruneRLimit`). As written at v121:
                          ## A SIBLING of `beBudgetExhausted`,
                          ## not a replacement: the plain while-loop k-unroll
                          ## (`isWhile`, no closed-form recognizer match) never
                          ## consults path-condition feasibility per iteration
                          ## — it structurally forks BOTH the continue and
                          ## exit branches at every one of `maxLoopUnwind`
                          ## iterations regardless of whether the continue
                          ## branch is provably infeasible, so `active.len > 0`
                          ## after the unwind loop fires even for a loop whose
                          ## trip count a `symexAssume` call has ALREADY
                          ## bounded well under `maxLoopUnwind` — reproduced
                          ## concretely (`symexAssume(n < 3)` with
                          ## `maxLoopUnwind` at its default 5 still reports
                          ## exhaustion). This is a STRUCTURAL k-unroll
                          ## limitation, not a real "ran out of budget"
                          ## signal — the honest fix (a per-iteration
                          ## satisfiability check on the continue branch, à la
                          ## `trySolve`) would multiply Z3 calls by
                          ## `unwind × active-path-count` for EVERY plain
                          ## while-loop in EVERY run, a genuine architecture
                          ## change this round's scope excludes (this
                          ## engine's `trySolve`/`s.check()` calls are
                          ## deliberately deferred to path-TERMINAL points
                          ## only — no other walk arm calls the solver
                          ## mid-loop). `collectAssumedLoopBound`
                          ## (`dsl_parser.nim`, parse-time, mirrors
                          ## `collectIntOffsetParams`'s established
                          ## precedent) marks `IRStmt.isWhile.wHasAssumedBound`
                          ## when the guard references a variable ALSO
                          ## constrained by a preceding `symexAssume` in the
                          ## same proc body — a purely LEXICAL, zero-solver-
                          ## cost signal, deliberately conservative (a
                          ## variable-name match, not a provable-bound
                          ## derivation) — so this kind is emitted INSTEAD OF
                          ## `beBudgetExhausted` (never both) exactly when
                          ## that signal fires, letting the ordinary
                          ## "genuinely unbounded loop" case keep its
                          ## unchanged classification while a caller/auditor
                          ## can distinguish "assumed-bounded but the
                          ## structural k-unroll couldn't use it" from
                          ## "no assumed bound exists at all." sevError →
                          ## sxUnknown (Invariant 3 — never a crash, never a
                          ## silent wrong sat/unsat; the STATUS/soundness
                          ## behavior is UNCHANGED from `beBudgetExhausted` —
                          ## only the classification is more honest).
                          ## Appended at enum tail (ordinal stability).
    feOpaqueCallUnmodelled ## Issue #163 (walker v131): `walk`'s `#137`
                          ## opaque-call arm (`runtime.nim`) reached a call
                          ## the front end classified as a black box — a
                          ## member of `OpaqueEffectfulProcs` (`echo`,
                          ## `readLine`, `writeFile`, …) or a user proc
                          ## carrying `{.symexOpaque.}` — whose result or
                          ## effects the walker cannot model, so every
                          ## continuation is tainted. `fe` and not `we`
                          ## deliberately: the black-box decision is the
                          ## FRONT END's (the parser chose `mkOpaqueCall`),
                          ## and this is an ordinary construct gap, not
                          ## "the walker itself hit a bug here". Before
                          ## #163 this arm set `w.sawUnknown` BARE, so an
                          ## `echo` ahead of the interesting branch reported
                          ## `weInternalWalkerFault` — the Invariant-7
                          ## backstop — instead of naming the call that cost
                          ## the answer. The message carries the callee name
                          ## for exactly that reason. sevError → sxUnknown
                          ## (Invariant 3; the soundness behavior is
                          ## UNCHANGED — only the classification is honest).
                          ## Appended at enum tail (ordinal stability).
    feEnumOrdinalUnresolved ## Issue #163 review R19: `dsl_parser.parseExpr`'s
                          ## `nnkSym` arm resolves an enum CONSTANT's ordinal
                          ## by finding its declaring `nnkEnumTy` body via
                          ## `n.getTypeInst` -> `getImpl` (R15's fix — the
                          ## only route that keeps explicit field values,
                          ## per R15's own `getType`-discards-values probe).
                          ## This kind fires when `getTypeInst` does NOT
                          ## resolve to a usable enum impl. The RETIRED
                          ## fallback here used to re-resolve via the direct
                          ## `n.getType` path instead — but that path is
                          ## PROVEN (same R15 probe) to always reconstruct
                          ## the enum with every explicit value discarded,
                          ## so it could only ever be right for a dense
                          ## zero-based enum by coincidence, and silently
                          ## wrong (a confidently-embedded, provably
                          ## incorrect constant) for any enum with an
                          ## explicit non-auto ordinal — the exact defect
                          ## class R15 exists to close, reopened one level
                          ## up. Whether some generic- or alias-mediated
                          ## shape can still defeat `getTypeInst` for a
                          ## legitimately-typed enum field symbol is not
                          ## enumerated; per Invariant 3, the answer to "not
                          ## proven unreachable" is to decline and name the
                          ## cause, not guess. `fe` (front-end): the failure
                          ## is in ordinary constant resolution, not a
                          ## walker-internal fault. sevError → sxUnknown.
                          ## Appended at enum tail (ordinal stability).
    feTransparentArgNotInert ## RETIRED RFC-0005 S8 (§13.3, i3 -- Corey
                          ## 2026-09-26) -- retained for ordinal stability,
                          ## NEVER EMITTED. Not a decline: nothing is
                          ## approximated because of it (the opaque fallback's
                          ## own `feOpaqueCallUnmodelled` taints every path
                          ## through the call); it reports that the user's
                          ## pragma claim is false. That report now rides the
                          ## verdict-neutral `AnnotationViolation` channel
                          ## (`avArgNotInert`). History follows.
                          ## Issue #163 review R7: a `{.symexTransparent.}`
                          ## callee in STATEMENT position was deleted
                          ## UNCONDITIONALLY (`dsl_parser.nim`'s statement-arm
                          ## `hasSymexTransparentPragma` branch) -- never
                          ## consulting `isInertArg`/`isInertOpaqueCall`, the
                          ## very predicate its OPAQUE sibling a few lines
                          ## below applies to the same argument shapes. A
                          ## `var` formal (`nnkHiddenAddr`) or a `ref`/`ptr`/
                          ## object-that-may-carry-a-ref argument lets the
                          ## real callee write through or observe state the
                          ## deleted call's absence cannot account for --
                          ## `withMutateT`/`mutate(m); if m != x: ...` is the
                          ## concrete false-`sxUnsat` witness. The parser now
                          ## emits THIS kind (parse-time, `ctx.parseErrors`)
                          ## naming the callee and which promise it broke,
                          ## alongside the generic `feOpaqueCallUnmodelled`
                          ## the resulting opaque-call fallback also produces
                          ## at walk time -- so the message a caller sees is
                          ## specific ("tagged `{.symexTransparent.}` but
                          ## takes a writable argument, treated as opaque")
                          ## rather than only the generic unmodelled-call
                          ## text, which would otherwise tell an already-
                          ## compliant caller to do the very thing they
                          ## already did. `fe` (front-end): the parser's own
                          ## pragma-honouring decision, not a walker fault.
                          ## sevError -> sxUnknown (Invariant 3 -- fails
                          ## SAFE, never a silent wrong verdict). Appended at
                          ## the enum tail WHEN IT LANDED (ordinal stability);
                          ## `feTransparentResultUsed` (R10) was appended after
                          ## it, so this is no longer the last member -- append
                          ## new kinds after the CURRENT tail, not here.
    feTransparentResultUsed ## RETIRED RFC-0005 S8 (§13.3, i3 -- Corey
                          ## 2026-09-26) -- retained for ordinal stability,
                          ## NEVER EMITTED; now the `AnnotationViolation`
                          ## channel's `avResultUsed` (see
                          ## `feTransparentArgNotInert`, above). History
                          ## follows.
                          ## Issue #163 review R10: the OTHER way a
                          ## `{.symexTransparent.}` callee can over-claim its
                          ## promise -- R7 (`feTransparentArgNotInert`, above)
                          ## covers the statement-position/non-inert-argument
                          ## route; this covers the EXPRESSION-position route,
                          ## where the call's RESULT is used. Both routes fall
                          ## back to `{.symexOpaque.}` handling
                          ## (`dsl_parser.nim`'s expression-position call arm)
                          ## and both also reach the generic
                          ## `feOpaqueCallUnmodelled` at walk time -- but that
                          ## generic message tells the caller to "mark it
                          ## `{.symexTransparent.}`", which is actively wrong
                          ## advice for a callee that already carries the
                          ## pragma. The parser now emits THIS kind
                          ## (parse-time, `ctx.parseErrors`) naming the callee
                          ## and the real broken promise -- the pragma is
                          ## honoured only in STATEMENT position, not that the
                          ## pragma is missing. `fe` (front-end): the parser's
                          ## own pragma-honouring decision, not a walker
                          ## fault. sevError -> sxUnknown (Invariant 3 --
                          ## fails SAFE, never a silent wrong verdict).
                          ## Appended at the enum tail WHEN IT LANDED (ordinal
                          ## stability); `feGlobalReadUnmodelled` was appended
                          ## after it, so this is no longer the last member --
                          ## append new kinds after the CURRENT tail, not here.
    feGlobalReadUnmodelled ## Issues #161/#163 handoff: `lower`'s `iekVar` arm
                          ## (`runtime.nim`) reached a name absent from the
                          ## current `env` -- the walker does not model
                          ## module-level globals AT ALL, and the parser
                          ## deliberately passes a free/global name through as
                          ## a bare `iekVar` (every local/param the parser
                          ## emits is bound before its first read, so an
                          ## unbound name here is never a parser bug). Before
                          ## this kind, the resulting `KeyError` escaped to
                          ## the top-level catch-all and reported
                          ## `weInternalWalkerFault` -- an internal-bug
                          ## attribution for an ordinary, everywhere-
                          ## applicable modeling gap. The message carries the
                          ## unbound name so the user knows which global to
                          ## remove from the reachable computation (or thread
                          ## through as an explicit parameter). sevError ->
                          ## sxUnknown (Invariant 3); the soundness argument
                          ## this unblocks: #163 slice 4's opaque-call
                          ## inertness proof relies on this decline being
                          ## real and classified -- see `isInertOpaqueCall`'s
                          ## doc, dsl_parser.nim. `seVariantFieldOnDeclinedCtor`
                          ## was appended after it, so this is no longer the
                          ## last member -- append new kinds after the
                          ## CURRENT tail, not here.
    seVariantFieldOnDeclinedCtor ## #163 regression fix (post-round-9 gate).
                          ## `isVariantField`'s walker arm (`runtime.nim`)
                          ## reached a receiver SymVal that is NEITHER
                          ## `svVariant` NOR `svMultiVariant` -- reachable
                          ## ONLY when the receiver's own CONSTRUCTION already
                          ## declined (`itVariant`/`itMultiVariant` object-
                          ## constructor edge cases in `dsl_parser.nim` return
                          ## a bound placeholder, per `unsupportedFieldPlaceholder`'s
                          ## own documented residual: no literal IR constructor
                          ## exists for a variant-shaped value, so the
                          ## placeholder is a plain `mkIntLit(0)`, deliberately
                          ## NOT variant-shaped) -- a later field read on that
                          ## already-tainted value is a REAL, reachable
                          ## consequence of an ALREADY-recorded classified
                          ## decline, not a fresh walker bug. Before this
                          ## kind, the receiver-kind mismatch was a bare
                          ## `doAssert false` (an uncatchable `AssertionDefect`
                          ## crash), reported at the `runSymex` boundary as
                          ## `weInternalWalkerFault` -- an internal-bug
                          ## attribution for an ordinary, everywhere-
                          ## applicable consequence of an existing, honestly-
                          ## classified construction gap. sevError ->
                          ## sxUnknown (Invariant 3). Appended at enum tail
                          ## (ordinal stability). The RFC-0005 S1b kinds were
                          ## appended after it, so this is no longer the last
                          ## member -- append new kinds after the CURRENT tail.
    # ---- RFC-0005 S1b (§2.2 "the premise 'every taint site has a kind in
    # hand' is false"): the kinds for the degrade sites that recorded NO
    # `SymexErrorInfo` before S1b. Each of these sites used to reach the
    # drain only through a transitional kindless ⊤ mark, so a run whose ONLY
    # degrade was one of them hit the Invariant-7 backstop and was stamped
    # `weInternalWalkerFault` -- a walker-bug attribution for an ordinary,
    # classifiable degrade. Every one is routed through `degrade()`
    # (`runtime.nim`), which records. All six are `dcNoAnswer` in `classOf`
    # (the conservative ⊤ default); S4-S6 reclassify. Appended at the enum
    # tail, in this order (ordinal stability).
    feUnsupportedStmtKind ## RFC-0005 S1b: a STATEMENT-position shape outside
                          ## the supported fragment that the parser replaces
                          ## by an `isUnsupported` node WITHOUT a parse-time
                          ## error of its own (§2.5's "Class-B" sites in
                          ## `dsl_parser.nim`: the `statement kind ... not in
                          ## supported fragment` catch-all, unmodelled
                          ## `nnkAsgn`/augmented-assign shapes, a statement
                          ## call outside the fragment, the A3/ADR-0014
                          ## iterator-inlining declines, an uninitialised
                          ## `var` of an unmodelled type). The statement is
                          ## DROPPED -- its effects never reach `env` -- so the
                          ## surviving path is tainted. The kind rides the
                          ## `isUnsupported` node (`IRStmt.unKind`) and is
                          ## recorded by the walker's `isUnsupported` arm when
                          ## a path reaches it. The expression-position
                          ## sibling is `feUnsupportedExprKind` (Class-A,
                          ## paired with a parse error). sevError -> sxUnknown.
    weRecursionCycleCut   ## RFC-0005 S1b: the `isCall` arm met a call whose
                          ## `argShapeKey` is already on `w.activeCalls` --
                          ## the callee is being walked further up the stack
                          ## with an identical argument shape (mutual/direct
                          ## recursion, or an `argShapeKey` hash collision).
                          ## The cycle is CUT: the call returns a fresh
                          ## unconstrained `_cyc` symbol, the callee's body
                          ## (its var-param/heap effects and raises) is not
                          ## walked for this occurrence, and the path is
                          ## tainted. Before S1b it recorded nothing and did
                          ## not mark the run (only a later tainted target
                          ## hit did). sevError -> sxUnknown.
    eeHandlerReraiseUnmodelled ## RFC-0005 S1b: a bare `raise` (re-raise)
                          ## reached with a NON-empty handler stack but no
                          ## in-flight exception -- e.g. a bare `raise` in a
                          ## `try` BODY, where real Nim raises
                          ## `ReraiseDefect`. Not modelled; the path is
                          ## dropped. Distinct from `eeRaiseOutsideHandler`
                          ## (empty handler stack). sevError -> sxUnknown.
    ceClosureBodyDiverged ## RFC-0005 S1b: a closure application
                          ## (`applyClosureGround`) whose body produced NO
                          ## value-bearing exit at all -- no `return`, no
                          ## fall-through (every body path raised, halted or
                          ## was dropped) -- so the call's result symbol is
                          ## unconstrained by any body path. A void closure
                          ## that falls through is NOT this (it has
                          ## fall-through paths). Recorded in the WALK sink,
                          ## not the closure sink (through S8 the closure veto,
                          ## `closureForcedUnknown`, read that sink; RFC-0005
                          ## S9 deleted it). sevError -> sxUnknown.
                          ## RFC-0005 S7: the body's raises now reach the
                          ## caller and the continuation past the call is
                          ## made infeasible (exit coverage `false`), so the
                          ## site is a halt: `dcOmitted`.
    weBreakOutsideLoop    ## RFC-0005 S1b: an `isBreak`/`isContinue` reached
                          ## with an EMPTY loop stack. Surface route: the
                          ## parser flattens `block:` into its body, so a
                          ## `break` out of a top-level `block` arrives here
                          ## with no loop frame; the breaking path is dropped
                          ## instead of resuming after the block. (`continue`
                          ## outside a loop is rejected by Nim itself, so it
                          ## is reachable only from hand-built IR.) sevError
                          ## -> sxUnknown.
    beSolverUndef         ## RFC-0005 S1b (§3.1's solver-undef row): `trySolve`
                          ## returned `zsUnknown` -- Z3 gave up on a path that
                          ## reached a finding (the `isTargetLabel` hit or
                          ## `routeRaise`'s raised finding): the deterministic
                          ## `queryRLimit` truncation, or an incomplete theory.
                          ## Distinct from the `ekZ3*` kinds, which are minted
                          ## only from RAISED Z3 exceptions, never from an
                          ## unknown RESULT; before S1b this recorded nothing,
                          ## so a run whose only degrade was a routine solver
                          ## resource-out was stamped `weInternalWalkerFault`.
                          ## The natural carrier for the rlimit provenance
                          ## RFC-0005 §8.2 owes RFC-0011/0008. sevError ->
                          ## sxUnknown.
    heUnsupportedPointeeRead ## RFC-0005 S4 (§3.2 split of `heUnresolvedRef`,
                          ## the minority funnel): a heap READ whose pointee
                          ## kind `liftHeapValue` does not lift (a `string`/
                          ## `seq`/`Table`/`HashSet`/`distinct`/... field or
                          ## bare pointee reached through a `ref`/`ptr`). The
                          ## select happens on the NON-NIL continuation (the
                          ## NilAccessDefect fork already ran), and the read
                          ## value is replaced by a FRESH, per-occurrence,
                          ## UNCONSTRAINED symbol of the pointee type -- a
                          ## superset of whatever the real cell holds, so
                          ## `classOf` is `dcFreshSymbol`. Split off because
                          ## every OTHER `heUnresolvedRef` site substitutes
                          ## differently (the non-ref-SymVal deref arms skip
                          ## the nil fork, the write arms drop the write, the
                          ## boundary arm aborts the run): reusing that kind
                          ## here would have promoted them all. sevError; as
                          ## `dcFreshSymbol` it blocks `sxSat` on its own path
                          ## (a candidate until replay confirms it) but never
                          ## `sxUnsat` on the run.
    seRuneDecodeSymbolic  ## RFC-0005 S5 (§3.2 split of `seZ3StringIncomplete`,
                          ## the minority funnel): a UTF-8 rune decode over a
                          ## SYMBOLIC string -- `runeLen(s)` / `for r in
                          ## s.runes` (ADR-0017). Variable-length grouping over
                          ## an unknown byte stream has no quantifier-free
                          ## encoding, so the PARSER declines: `runeLen(s)` is
                          ## replaced by the literal `0` and the `runes` loop
                          ## statement is dropped (its body's effects never
                          ## happen). Both substitute -- `classOf` is
                          ## `dcSubstituted`. Split off because every OTHER
                          ## `seZ3StringIncomplete` site is a lowering-time
                          ## `degradeStrArm` decline whose result is a fresh
                          ## per-read symbol (`dcFreshSymbol`): reusing that
                          ## kind here would have promoted a forced `0`.
                          ## sevError -> sxUnknown.
    beBudgetExhaustedPrune ## RFC-0005 S6a (§3.2 split of `beBudgetExhausted`,
                          ## the `dcOmitted` minority funnel): the
                          ## `maxFrontierSize` post-step frontier prune
                          ## (`walkBlock`, `runtime.nim`) EVICTED live paths.
                          ## The evicted paths are dropped outright and the
                          ## kept paths are untouched -- a pure
                          ## under-approximation, so `classOf` is `dcOmitted`
                          ## (`{scIncomplete}` on the run: an UNSAT claim over
                          ## the pruned run is void; `{}` on the path, which is
                          ## inert because the site is a HALT -- no survivor
                          ## receives the token). Split off because the
                          ## k-unroll survivor that keeps `beBudgetExhausted`
                          ## is `dcFabricated` and the call-depth/variant bails
                          ## (`beBudgetExhaustedUnmodelled`) substitute:
                          ## classifying the merged kind by THIS site would
                          ## have stripped the path taint from both. sevError
                          ## -> sxUnknown.
    beBudgetExhaustedUnmodelled ## RFC-0005 S6a (§3.2 split of
                          ## `beBudgetExhausted`, the `dcSubstituted` minority
                          ## funnel): a walk budget ran out and the walker
                          ## CONTINUED PAST an operation it did not model. The
                          ## `maxCallDepth` bail (`isCall`) binds the result to
                          ## a fresh havoc `retSym` but drops the callee's
                          ## var-param writes, heap writes and raises, and never
                          ## lowers the actuals; the `maxVariantConstructorForks`
                          ## / `maxVariantConstructorFieldAllocs` declines
                          ## (`isVariantConstructSym`) leave the destination
                          ## UNBOUND and never lower the discriminant or
                          ## plain-field operands. Both leave a stale env (and
                          ## drop raise forks), neither ⊇ nor ⊆ the real
                          ## behaviour set: `classOf` is `dcSubstituted`, ⊤ on
                          ## both coordinates. sevError -> sxUnknown.
    feUnsupportedOpHavoc  ## RFC-0005 S6b (§3.2 split of `feUnsupportedOp`,
                          ## the `dcFreshSymbol` minority funnel): an
                          ## unmodelled operation whose result is replaced by a
                          ## FRESH, per-evaluation, unconstrained symbol of the
                          ## result sort, with every operand already lowered
                          ## and nothing else dropped -- a superset of the real
                          ## behaviours. The sites: `iteSV`'s svUninterpRef /
                          ## genuine-svSeq / svString-svTable-svSet merges, the
                          ## same-width reinterpret of an Int-sorted operand,
                          ## ordering on two bools (system's magic `<`), the
                          ## closure-environment leaf equality conjunct, and
                          ## the three composite call-result bindings whose
                          ## per-call `retSym` (a `synthZ3`-numbered name) is
                          ## left free (explicit `return`, implicit `result`
                          ## fallthrough, untouched result with no
                          ## zero-default). RFC-0005 S8bi: `newSeqUninit`'s
                          ## element array (`lower`'s `iekSeqNew` arm).
                          ## `classOf` is `dcFreshSymbol`:
                          ## `{scSpurious}` on both coordinates -- a hit through
                          ## it is a candidate, and it does not void `sxUnsat`.
                          ## A new site may reuse this kind ONLY if its operands
                          ## are lowered first, its symbol is fresh per
                          ## evaluation and it drops no fork, write or raise.
    feUnsupportedOpAborted ## RFC-0005 S6b (§3.2 split of `feUnsupportedOp`,
                          ## the `dcNoAnswer` minority funnel): the §3.3
                          ## boundary abort -- a `SymexUnsupportedOpError`
                          ## (an unmodelled `math.<name>` / float op raised by
                          ## `runtime_floats.nim`) unwound the whole walk to
                          ## `runSymex`, which reports `sxUnknown` with no
                          ## path at all. No enlarged or shrunk program exists
                          ## for an aborted walk: `classOf` is `dcNoAnswer`.
                          ## sevError -> sxUnknown.
    seParseIntLaxSyntax   ## RFC-0005 S10. `parseInt(s)` on a string with a
                          ## `_`: Nim's `rawParseInt` skips it as a digit
                          ## separator, Z3's `str.to_int` is -1 on it, and
                          ## the value needs the version-gated
                          ## `str.replace_all`, so both the modelled
                          ## `ValueError` raise and (RFC-0005 S8b) the
                          ## continuation on a fresh value are SUPERSETS of
                          ## the real ones (`drainParseIntRaises`,
                          ## `ParseIntRaise.lax`). S10 also put a `+` prefix
                          ## here; S8b models the sign exactly. `classOf` is
                          ## `dcFreshSymbol` (`{scSpurious}` on both
                          ## coordinates): what it produces is a
                          ## replay-gated candidate, and it never voids
                          ## `sxUnsat`. sevError.
    feReplayTimedOut      ## RFC-0005 S8be (§4.2 `roTimedOut`). NOT a
                          ## degrade: the verdict-time replay of a
                          ## candidate's witness did not end within
                          ## `SymexSettings.replayTimeoutMs` and was
                          ## abandoned. Neither a confirmation nor a
                          ## refutation: the real `fn` may be looping on
                          ## that witness, or only slow. Recorded by
                          ## `settleCandidate` like `feReplayRefuted`, so it
                          ## never enters `runTaint`; always `sevHint`.
                          ## RFC-0005 0.9.1: also on a CONFIRMED claim whose
                          ## child ran past the bound after reaching the
                          ## target (`Soundness.witnessUnsafe`, WA-2), and on
                          ## a lossy winner left `rsUnconfirmed` (WA-9).
                          ## `classOf` is `dcFreshSymbol`, for the same reason.
    feReplayCrashed       ## RFC-0005 S8ct (§4.2 `roCrashed`). NOT a degrade:
                          ## the verdict-time replay of a candidate's witness
                          ## ended its child process (an exit, a signal, a
                          ## system exception) before it reached the target.
                          ## The message says how, and on what input. Recorded
                          ## by `settleCandidate` like `feReplayRefuted`, so it
                          ## never enters `runTaint`; always `sevHint`.
                          ## RFC-0005 0.9.1: also on a CONFIRMED claim whose
                          ## child ended AFTER reaching the target
                          ## (`Soundness.witnessUnsafe`, WA-2), and on a lossy
                          ## winner left `rsUnconfirmed` (WA-9).
    feReplayDeclined      ## RFC-0005 S8ct (§4.2 `roDeclined`). NOT a degrade:
                          ## no child could run this replay (it could not be
                          ## started, or, on a platform where the program is
                          ## re-executed, the state the SUT may reach cannot be
                          ## handed to one), so it did not run. As
                          ## `feReplayRefuted`, always `sevHint`.
    feReplayRefuted       ## RFC-0005 S10 (§4.2 `roRefuted`). NOT a degrade:
                          ## the verdict-time replay of a candidate's witness
                          ## ran the real SUT to completion without reaching
                          ## the target -- a CONFIRMED model gap on that
                          ## witness, surfaced as its own classified
                          ## diagnostic on the `sxUnknown` result. Recorded
                          ## by `symex.nim`'s `settleCandidate` AFTER
                          ## `runSymex` returns, so it never enters
                          ## `runTaint`; always `sevHint`. `classOf` is
                          ## `dcFreshSymbol`: only an entirely fresh-symbol
                          ## path is replayed at all (`replayEligible`), so
                          ## the gap it names is that class's.
    ceCaptureByRefUnmodelled ## RFC-0005 S9. A closure application whose
                          ## by-reference captures the walker cannot follow.
                          ## Nim captures a `var` by reference; the walker
                          ## reads such a capture from the CURRENT env, which
                          ## it can do only when the closure is applied in the
                          ## frame that built it (`refreshByRefCaptures`).
                          ## Recorded when a closure with a mutable capture is
                          ## applied in another frame (the body reads the
                          ## construction-time snapshot, possibly stale), or
                          ## when the body writes a mutable capture (the write
                          ## is not carried back to the caller). `classOf` is
                          ## `dcSubstituted`: a stale value is forced, or a
                          ## write is dropped. sevError, via `closureDegrade`.
    feConvFloatToIntUndefined ## RFC-0005 S8g. A float -> int conversion
                          ## whose operand may lie outside the target type's
                          ## range (NaN, +-Inf, or a finite value whose
                          ## truncation does not fit). Nim 2.2.10 never
                          ## raises there -- its generated C casts first and
                          ## range-checks the CAST value -- and the cast is
                          ## C-level undefined (x86-64 gives `low(int)` for
                          ## `int`, 0 for `int32(1e30)`, the low byte for
                          ## `int8(300.0)`; other targets differ). The
                          ## out-of-range continuation takes a FRESH value of
                          ## the target type on its own path
                          ## (`drainConvFloatToIntFresh`); the in-range one
                          ## is exact and clean. `classOf` is `dcFreshSymbol`:
                          ## every value any platform produces is a model of
                          ## the fresh symbol, nothing is forked away, and a
                          ## candidate on that path is replay-gated. Recorded
                          ## once per drain whose out-of-range half does not
                          ## simplify to `false`. sevError.
    eeFinallyReturnOnRaise ## RFC-0005 S8l. A `return` inside a `finally`
                          ## that is running on a RAISED exit (the try body
                          ## or an `except` arm raised, nothing caught it).
                          ## The pinned toolchain's two backends disagree
                          ## there: `try: raise newException(ValueError,
                          ## "a") finally: return 7` returns 7 under cpp and
                          ## re-raises the ValueError under c (probed,
                          ## Nim 2.2.10). The walker cannot know which
                          ## backend replays the witness, so the path is
                          ## dropped. `classOf` is `dcOmitted` (a HALT, token
                          ## discarded). sevError -> sxUnknown.
    eeFinallyJumpOnRaise  ## RFC-0005 S8m. A `break` / `continue` that leaves
                          ## a `finally` running on a RAISED exit -- the
                          ## jump twin of `eeFinallyReturnOnRaise`. The
                          ## pinned toolchain's backends disagree there:
                          ## `for i in 0..1: (try: raise newException(
                          ## ValueError, "r") finally: break)` re-raises the
                          ## ValueError under c and swallows it under cpp; a
                          ## `continue` there overflows the call depth under
                          ## c (probed, Nim 2.2.10). The path is dropped.
                          ## `classOf` is `dcOmitted` (a HALT, token
                          ## discarded). sevError -> sxUnknown.
    feGlobalHavoc         ## RFC-0005 S8as. A module-level variable whose
                          ## value the walk does not know takes a fresh
                          ## value of its type: a read before any write in
                          ## the walk (the value the property meets, which
                          ## other code may have set -- `IRGlobal`), or a
                          ## global an inert opaque call's effect summary
                          ## says it may write (`IRStmt.opaqueHavoc`). Every
                          ## real value is a model, nothing is forked away
                          ## and no effect is dropped: `classOf` is
                          ## `dcFreshSymbol` (`{scSpurious}`), so a hit
                          ## through it is a replay-gated candidate and it
                          ## never voids `sxUnsat`. sevError.
    feOpaqueEffectHavoc   ## RFC-0005 S8ax. An inert opaque call's other
                          ## effects: the heap cells its summary reaches
                          ## take fresh contents (`IRStmt.opaqueHeapTys`,
                          ## `opaqueHeapAll`), a raise of each type its
                          ## `raises` list names is forked
                          ## (`opaqueRaises`), and the path that returns
                          ## past a call that may raise assumes it did not.
                          ## Each path is a superset of what the real call
                          ## does there, nothing is dropped: `classOf` is
                          ## `dcFreshSymbol`, a hit is replayed, and an
                          ## `sxUnsat` stands. sevError.
    feUncheckedDiscBytes  ## RFC-0005 S8cp (item 2). A discriminator written under
                          ## `{.cast(uncheckedAssign).}` to a different value on
                          ## an object that may or may not have a hook (`dwmHavoc`):
                          ## the new arm reads the old bytes or zero, so it holds a
                          ## fresh value of its type. Every real value is a model
                          ## and nothing is dropped: `classOf` is `dcFreshSymbol`,
                          ## a hit is replayed, an `sxUnsat` stands. sevError.
    feLocalPragma         ## RFC-0016 W1-b (W-02). A local `var` / `let` carries a
                          ## pragma the walker does not model (`{.cursor.}`, which
                          ## shares the memory the walk copies, `align`,
                          ## `volatile` ...). The declaration is lowered as if it
                          ## had none and the path that reaches it declines
                          ## (`dcSubstituted`). sevError.
    feEvalOrderUnmodelled ## RFC-0005 S8ax. An operand Nim checks where it
                          ## stands but reads after a later operand's call
                          ## (`a[i] + f()`, `-x + f()`, `x div 2 + f()`),
                          ## where that call changed what the operand reads:
                          ## the walk checks and reads it in one place, so
                          ## the path that reaches the change declines.
                          ## Default class (no answer). sevError.
    feTableIterOrder      ## RFC-0005 S8bc (item 6). A `for` over a `Table`'s
                          ## `pairs` / `keys` / `values` with two or more
                          ## entries on the path. Nim visits the keys in the
                          ## table's hash order; the walker visits them in a
                          ## FREE order (`isTabKeys`: any enumeration of the
                          ## present keys), which over-approximates: every
                          ## real order is one of the models and nothing is
                          ## forked away, so an `sxUnsat` holds for the real
                          ## order too. A candidate whose label depends on the
                          ## order may not be realised by Nim's order, so
                          ## `classOf` is `dcFreshSymbol`: the candidate is
                          ## replayed (S10), and a refuted one is `sxUnknown`
                          ## -- the order-dependent program declines. sevError.
    seRecursiveValueDepth ## RFC-0005 S8bc (item 3). A value object that
                          ## recurs through a seq (`type T = object; kids:
                          ## seq[T]`) is unrolled to a bounded depth
                          ## (`maxRecursiveValueDepth` levels of `T` below
                          ## the outermost); the seq at the bound is a
                          ## scoped-decline placeholder, so a read of it,
                          ## and a store of a value whose depth does not
                          ## match the slot's, declines. `classOf` is
                          ## `dcNoAnswer`, as `seNestedSeqUnsupported`.
    feGlobalRouteUnproved ## RFC-0005 S8cs. A read of a module-level `var`
                          ## that a store the walk does not see may reach (a
                          ## lifetime hook the compiler inserts, code the
                          ## macro-time analysis cannot read):
                          ## `IRGlobal.hiddenRoute`. The value the walk holds
                          ## may be stale, in either direction, whether it
                          ## came from an entry value or from the walk's own
                          ## write. `classOf` is `dcSubstituted`. sevError.
    feCheckOption         ## RFC-0005 S8cu. A routine compiled without a check
                          ## the walker models (`fieldChecks`, `rangeChecks`,
                          ## `boundChecks`, `objChecks`), or with a float check
                          ## it does not (`check_options.nim`). The routine's
                          ## raises and values are not the model's, so a path
                          ## reaching it declines. Unchecked semantics are not
                          ## modelled. sevError.
    feOverflowCheckOption ## RFC-0005 S8cu. `overflowChecks` off on a routine
                          ## while the settings model it on. With `acOverflow`
                          ## out of `arithChecks` the walker models the wrap
                          ## and the trap (S8w, S8aa), and the marker is passed
                          ## through. sevError.
    heNilDerefMayBeCaught ## RFC-0005 S8cu. A nil dereference under a `try`
                          ## (an `except` or a `finally`) in a build with
                          ## `--exceptions:setjmp`, where `std/segfaults` makes
                          ## it a catchable `NilAccessDefect` and runs the
                          ## `finally`. Whether the program imports it is not
                          ## read, so the path declines. Every other build
                          ## crashes there (SIGSEGV) and no handler runs.
                          ## sevError.
    feFloatWidth          ## RFC-0016 W1-e (W-04). A conversion between
                          ## `float32` and `float64`, explicit (`float32(x)`,
                          ## `float64(y)`) or one the compiler inserts (a
                          ## `float32` passed or assigned where a `float64`
                          ## is expected). The two widths are different Z3
                          ## sorts; the conversion was the transparent
                          ## pass-through, so a value of one width flowed on
                          ## as the other. RFC-0016 K2b models the
                          ## conversion exactly (`fp.to_fp`, RNE), so
                          ## nothing produces this kind now.
                          ## `classOf` is `dcNoAnswer`, as
                          ## `feUnsupportedExprKind`. sevError. See
                          ## `docs/symex/README.md`, "Float widths".
    # RFC-0016 W1-d1a (section 9.1 item 4): the undefined-behaviour kinds,
    # declared together and contiguous so `UbKind` is one range. Each names a
    # place where the program's behaviour is undefined, not a Defect and not
    # a value: the path ends there (`haltUndefined`) and the run records the
    # omission. All `dcOmitted`, sevError. Producers: `ubIntMinModMinusOne`
    # (W1-d1a), `ubUnsignedDivZero` (W1-d1b), `ubSignedDivZero`, `ubSignedOverflow`
    # (W1-d2) and `ubIndeterminateRead` (W1-d3, the `{.noinit.}` read).
    # `ubFloatToIntRange` has none until K10a.
    ubUnsignedDivZero     ## `x div 0` / `x mod 0` on an unsigned type.
    ubIntMinModMinusOne   ## `low(T) mod -1` (and `low(T) div -1` with
                          ## overflow checks off) at 32 and 64 bits: the C
                          ## division is undefined and traps on x86 (SIGFPE).
    ubSignedOverflow      ## signed add / sub / mul / neg overflow with the
                          ## overflow checks off and no `-d:nelliFwrapv` at
                          ## 32 and 64 bits (K5a; 8 and 16 bit wrap).
    ubFloatToIntRange     ## a float to int conversion out of range.
    ubIndeterminateRead   ## a read of an uninitialised value.
    ubSignedDivZero       ## `x div 0` / `x mod 0` on a signed type with the
                          ## overflow checks off (Nim emits no zero check
                          ## then, and the C division is undefined). RFC-0016
                          ## WA-B; appended so every earlier ordinal holds.
    feHostUnadmitted      ## RFC-0016 K5a (section 8.3). The host half of the
                          ## build profile is not a verified one: the loaded
                          ## libz3 is not 4.13.4 or 5.1, or no build row
                          ## covers this build under it. The run decides
                          ## nothing and is `sxUnknown`; it is not a raise.
                          ## The message names the field and the value.
                          ## Appended after the `ub*` range, so `UbKind` and
                          ## every earlier ordinal hold. `classOf` is
                          ## `dcNoAnswer`. sevError.
    feUnadmitted          ## RFC-0016 ADM-1 (§8.1). A cell with no row in its
                          ## admission table: the code reached something the
                          ## axis was never asked to classify, which is a
                          ## decline, never a silent model. `classOf` is
                          ## `dcOmitted` since K7b: every site that reaches
                          ## one drops the path (`halted`; the walker's
                          ## missing-callee arm, for a magic), so no path
                          ## carries it and no clean `sxSat` rides past the
                          ## cell, while the run coordinate `{scIncomplete}`
                          ## keeps `sxUnsat` untrusted. sevError. Produced
                          ## by the magic axis for a `var`-parameter magic
                          ## with no row.
    feDefectExcluded      ## RFC-0016 K7b (W-16). A `Defect` raise that
                          ## reached the SUT boundary on a feasible path was
                          ## suppressed because its `DefectKind` is in
                          ## `settings.defectExclusions`: the path ends with
                          ## no finding, a pure omission. `classOf` is
                          ## `dcOmitted` (run `{scIncomplete}`), so a search
                          ## that the excluded raise could have answered is
                          ## never a trusted `sxUnsat`. sevError. Appended
                          ## after `feUnadmitted`, so every earlier ordinal
                          ## holds.

  UbKind* = range[ubUnsignedDivZero .. ubSignedDivZero]
    ## RFC-0016 W1-d1a (section 9.1 item 4). The undefined-behaviour kinds:
    ## the contiguous `ub*` members of `SymexErrorKind`.
static:
  # RFC-0016 W1-d3: `Soundness.witnessUndefined` and codec version 4 store
  # `ord(k) - ord(low(UbKind))`, so these ords ARE the persisted format:
  # reordering, inserting or removing a member fails the build (the fix is a
  # new `soundnessMetaVersion` and this pin).
  doAssert ord(ubUnsignedDivZero) + 1 == ord(ubIntMinModMinusOne) and
           ord(ubIntMinModMinusOne) + 1 == ord(ubSignedOverflow) and
           ord(ubSignedOverflow) + 1 == ord(ubFloatToIntRange) and
           ord(ubFloatToIntRange) + 1 == ord(ubIndeterminateRead) and
           ord(ubIndeterminateRead) + 1 == ord(ubSignedDivZero) and
           ord(high(UbKind)) - ord(low(UbKind)) < 30
