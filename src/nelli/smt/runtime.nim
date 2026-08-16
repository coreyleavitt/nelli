## Phase-2 IR interpreter.
##
## The IR is type-erased after parsing; the runtime determines the
## width of each integer subexpression by probing the env or
## inheriting from the surrounding context (let RHS = let LHS type;
## comparison operands = the matching variable's type).
##
## Storage: `SymVal` is a sum over the Z3 families we need
##
##   { Z3Bool, Z3BitVec[8|16|32|64], Z3Int }
##
## with a `signed: bool` field inside each BV variant case (Nim's `int*`/`uint*`
## distinguish signedness at the operator layer, not the bit-pattern).
## `Z3Int` lands as a SymVal variant for Phase-2 cycles 5+ when the
## abstraction layer promotes range-typed integers; the parser/runtime
## here ship with the variant present and the structural plumbing in
## place, so cycle 5 only adds the promotion logic, not new families.

import std/tables
import std/options
import std/sets
import std/hashes
import std/math   ## Phase 15 F2: classify() for float-literal NaN/Inf/-0.0 lowering
import std/strutils   ## Phase 15 S5: parseInt on a concrete seqLen numeral; split
import z3

import ./types
import ./abstraction
import ./regex_parser   ## Phase 15 S6b: parseNimRegexToZ3Regex (re"…" → Z3Regex)
import ./exn_hierarchy   ## Phase 15 E4: exnTypeTable / isSubtypeOf / isDefect

export tables, sets   ## for `Table` / `HashSet` in witness types

# Once-per-process banner for `isLoose` mode. ADR-0001 calls this out
# as a deliberate footgun; the banner is the documented warning.
var isLooseBannerEmitted = false

proc emitIsLooseBanner() =
  if not isLooseBannerEmitted:
    stderr.writeLine "nelli/symex: WARNING — `isLoose` integer semantics " &
                     "is UNSOUND (Z3Int everywhere, no BV floor). May produce " &
                     "witnesses that overflow at runtime. See ADR-0001."
    isLooseBannerEmitted = true

# ---- SymVal -----------------------------------------------------------------

type
  SymexUnsupportedOpError* = object of CatchableError
    ## Phase 15 F6. Raised during `lower` when an unmodeled float op
    ## (`classify`/`copySign`/`nextafter`/any unmodeled `math.<name>`) is
    ## encountered. Caught at the `runSymex` boundary and mapped to an
    ## `sxUnknown` result carrying a `feUnsupportedOp` (sevError) error, so
    ## the verdict is never a silent UNSAT (Invariant 3).
    op*: string

  SymexUnsupportedStringOpError* = object of CatchableError
    ## Phase 15 Cluster S (S1). Raised during `lower` when an `iekStr*`
    ## string op is encountered that the current cycle does not yet model
    ## (in S1 that is *all* of them — S2–S11 flesh them out one per cycle).
    ## Caught at the `runSymex` boundary and mapped to `sxUnknown` carrying a
    ## `seUnsupportedStringOp` (sevError) error per ADR-0006 — never a silent
    ## UNSAT (Invariant 3).
    op*: string

  SymexZ3VersionMissingError* = object of CatchableError
    ## Phase 15 S5. Raised during `lower` when a string op needs a Z3 FFI
    ## symbol the current build lacks (e.g. `replaceAll` →
    ## `Z3_mk_seq_replace_all`, gated behind `-d:z3WithSeqReplaceAll`,
    ## absent on Z3 < 4.15.5). Caught at the `runSymex` boundary → `sxUnknown`
    ## carrying a `seZ3VersionMissing` (sevError) error — never a crash, never
    ## a silent UNSAT (Invariant 3).

  SymexZ3StringIncompleteError* = object of CatchableError
    ## Phase 15 S5. Raised during `lower` for a string-theory decomposition the
    ## walker cannot soundly bound — specifically the GENERAL symbolic-`split`
    ## path (a universal quantifier over a symbolic `seq[string]` whose length
    ## is unbounded). Rather than emit the quantifier (a Z3 string-solver hang
    ## risk) the walker classifies it `seZ3StringIncomplete` → `sxUnknown`
    ## (Invariant 3 — structured, never a silent UNSAT, never a hang).

  SymexBytesSymbolicLengthError* = object of CatchableError
    ## Phase 15 S7a. Raised during `lower` for `bytes(s)` when the receiver's
    ## byte/char count is NOT statically known (the receiver IR is not a string
    ## literal, so its length is symbolic). The byte-view is materialised as a
    ## concrete-length `svSeq` of BV8 elements, which requires a known length;
    ## a symbolic length has no bounded element chain. Caught at the `runSymex`
    ## boundary → `sxUnknown` carrying `seBytesSymbolicLength` (sevError) —
    ## never a silent UNSAT (Invariant 3).

  SymexBytesLengthTooLargeError* = object of CatchableError
    ## Phase 15 S7a. Raised during `lower` for `bytes(s)` when the receiver's
    ## concrete byte/char count exceeds `SymexSettings.maxBytesEncodingLen`
    ## (default 32). Rather than expand a long element chain, the byte-view is
    ## classified `seBytesLengthTooLarge` → `sxUnknown` (Invariant 3).

  SymexUnsupportedRegexError* = object of CatchableError
    ## Phase 15 S6b. Raised during `lower` when S6a's `parseNimRegexToZ3Regex`
    ## rejects a `re"…"` pattern (backreference / lookahead / named group, or a
    ## malformed pattern), and for `iekStrFindRe` (no nim-z3 `indexOf`-on-regex
    ## API — a documented deferral). Caught at the `runSymex` boundary →
    ## `sxUnknown` carrying a `seUnsupportedRegex` (sevError) error — never a
    ## crash, never a silent UNSAT (ADR-0006, Invariant 3). The S6a error
    ## message rides in `msg`.

  SymexRaiseUnimplementedError* = object of CatchableError
    ## Phase 15 E1. Raised by the `walk(isRaise)` STUB. E1 is purely structural
    ## — `raise`-flow semantics (in-flight exn, handler dispatch, `sxRaised`)
    ## land E2b+. Until then the walker classifies any `isRaise` it reaches as
    ## `eeRaiseUnimplemented` → `sxUnknown` (Invariant 3 — never a silent UNSAT,
    ## never a crash). The qualified exception type rides in `msg`.

  SymexTryUnimplementedError* = object of CatchableError
    ## Phase 15 E1. Raised by the `walk(isTry)` STUB. Try/except/finally
    ## dispatch lands E3+. Until then any `isTry` the walker reaches is
    ## classified `eeTryUnimplemented` → `sxUnknown` (Invariant 3).

  SymexClosureUnimplementedError* = object of CatchableError
    ## Phase 15 C1. Raised by the `lower(iekLambda)` / `lower(iekClosureCall)`
    ## STUBs. C1 is purely structural — closure CONSTRUCTION lands C2a and
    ## APPLICATION (the ground per-call-site axiom, ADR-0009 D6) lands C2b.
    ## Until then any lambda/closure-call the walker reaches is classified
    ## `ceNotImplemented` → `sxUnknown` (Invariant 3 — never a silent UNSAT,
    ## never a crash). The diagnostic rides in `msg`.

  SymexRaiseOutsideHandlerError* = object of CatchableError
    ## Phase 15 E2b. Raised by `walk(isRaise)` when a BARE `raise`
    ## (re-raise) is reached with an EMPTY handler stack AND no in-flight
    ## exception — i.e. a re-raise at top level with nothing to re-raise.
    ## Caught at the `runSymex` boundary → `sxUnknown` carrying an
    ## `eeRaiseOutsideHandler` (sevError) classified error (Invariant 3 —
    ## never a silent UNSAT, never a crash).

  SymexNotInHandlerError* = object of CatchableError
    ## Phase 15 E8. Raised when `getCurrentException()` /
    ## `getCurrentExceptionMsg()` is lowered with NO in-flight exception
    ## (`w.frame.inFlightExn.isNone`) — i.e. called outside any `except`
    ## handler body. Caught at the `runSymex` boundary → `sxUnknown` carrying
    ## an `eeNotInHandler` (sevError) classified error (Invariant 3 — never a
    ## panic, never a silent UNSAT). The intrinsic name rides in `msg`.

  SymexRefUnresolvedError* = object of CatchableError
    ## Phase 15 Cluster R (R1a, ADR-0010). Raised by the `allocateSym(itRef/
    ## itPtr)` and `walk(isDeref/isNew)` STUBs while the logical-heap semantics
    ## are not yet modeled (structural cycle). Caught at the `runSymex` boundary
    ## → `sxUnknown` carrying a `heUnresolvedRef` (sevError) classified error
    ## (Invariant 3 — never a silent UNSAT, never a crash). R1+ replace the stub
    ## with real ref-sort / heap-array semantics. The diagnostic rides in `msg`.

  SymexRefVariantUnsupportedError* = object of CatchableError
    ## Phase 15 Cluster R (R6, ADR-0010, Feas-MED-4 / M17). Raised when a field
    ## access through a `ref`/`ptr` to a VARIANT object is reached: the
    ## field-split heap has no flat positional layout to split a variant on, so
    ## it is out of scope. Caught at the `runSymex` boundary → `sxUnknown`
    ## carrying a `heRefVariantUnsupported` (sevError) classified error
    ## (Invariant 3 — never a silent UNSAT, never a Defect on svTuple dispatch).
    ## The diagnostic rides in `msg`.

  SymexOwnershipUnsupportedError* = object of CatchableError
    ## Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). Raised when an
    ## `owned T` / `WeakRef[T]` / `Atomic[T]` formal is allocated (classifyType
    ## maps these to an `__ownership:*` placeholder). Caught at the `runSymex`
    ## boundary → `sxUnknown` carrying a `heUnsupportedOwnership` (sevError)
    ## classified error (Invariant 3). These ownership wrappers are out of scope
    ## for the cluster; the diagnostic rides in `msg`.

  SymexNestedSeqUnsupportedError* = object of CatchableError
    ## Phase 16 INV. Raised by `allocateSeqDataRaw` when the element type of a
    ## `seq[T]` is itself a `seq` (i.e. `seq[seq[T]]`). The nested-seq encoding
    ## is not modeled: the Z3 array-of-arrays representation requires a concrete
    ## inner sort, and a symbolic nested seq would require a second-level length
    ## variable. Caught at the `runSymex` boundary → `sxUnknown` carrying a
    ## `seNestedSeqUnsupported` (sevError) classified error (Invariant 3 —
    ## never a crash, never a silent UNSAT). The diagnostic rides in `msg`.

  SymexUnsupportedTableValTypeError* = object of CatchableError
    ## Phase 16 INV. Raised by `allocateSym(itTable)` and the `isIndex/svTable`
    ## walker arm when the Table's value type is not a modeled type. Currently
    ## only `Table[string, int]` is supported; any other value type (e.g.
    ## `Table[string, string]`, `Table[K, object]`) degrades here. Caught at
    ## the `runSymex` boundary → `sxUnknown` carrying a `seUnsupportedTableValType`
    ## (sevError) classified error (Invariant 3 — never a crash, never a silent
    ## UNSAT). The diagnostic rides in `msg`.

  SymexUnsupportedSetCharInteropError* = object of CatchableError
    ## Phase 16 INV. Raised by `allocateSym(itSet)` and the `iekContains/svSet`
    ## walker arm when the Set's element type is not int64 (BV[64]). Currently
    ## only `HashSet[int]` is modeled; `set[char]` / `HashSet[uint8]` and other
    ## non-int64 element types degrade here. Caught at the `runSymex` boundary →
    ## `sxUnknown` carrying a `seUnsupportedSetCharInterop` (sevError) classified
    ## error (Invariant 3 — never a crash, never a silent UNSAT).
    ## The diagnostic rides in `msg`.

  SymexClassifiedDegradeError* = object of CatchableError
    ## Phase 16 CR-1c (RFC-chapulin-hardening, Cluster 2 — Crash-totality,
    ## ADR-0020). A SINGLE generic carrier for DELIBERATE classified walker
    ## degrades that do not warrant their own dedicated exception type —
    ## introduced by CR-1c and reused rather than minting a 19th near-identical
    ## `object of CatchableError` alongside the ones above. Any code that wants
    ## to degrade to a pre-classified `sxUnknown` raises this with the intended
    ## `kind`; caught by its dedicated arm at the `runSymex` boundary →
    ## `sxUnknown` carrying `kind` verbatim (Invariant 3). CR-2b's degrade path
    ## reuses it. NOTE: CR-1c's OWN genuinely-unanticipated-native safety net
    ## does NOT raise this — an unanticipated native escaping the walker is
    ## caught by the final `except CatchableError` catch-all on the `runSymex`
    ## try (which classifies it `weInternalWalkerFault`), because a per-`walk`-
    ## frame catch/re-raise crashed the C backend (see the catch-all's comment
    ## + ADR-0020). This carrier exists for the pre-classified-degrade case.
    kind*: SymexErrorKind

  SVKind* = enum
    svBV8, svBV16, svBV32, svBV64
    svInt
    svBool
    svString  ## Phase 5: Nim string, encoded as Z3String.
    svTuple
    svArray   ## Phase 4: static array, per-element SymVals.
    svSeq     ## Phase 5: dynamic seq[T] — (Z3Int len, Z3Array data).
    svTable   ## Phase 5: Table[K, V] — (data, present).
    svSet     ## Phase 5: HashSet[T] — Z3Array[T, Z3Bool].
    svVariant ## Phase 11: tagged sum (Nim variant object) — disc-
              ## riminator + per-arm symbolic field bindings.
    svMultiVariant ## Phase 14 (ADR-0003 D1): multi-axis variant —
              ## per-axis discriminators + per-axis arm fields.
              ## Symmetric with svVariant but with multiple axes.
    svUninterpRef ## Phase 15 Z3b: uninterpreted reference sort; fields not
              ## modelled symbolically. Produced by cluster E (E8,
              ## getCurrentException). Carries the Z3 uninterpreted-sort
              ## ast plus diagnostic names.
    svFloat32  ## Phase 15 F1: IEEE float32 (Z3Float32).
    svFloat64  ## Phase 15 F1: IEEE float64 (Z3Float64); Nim `float`.
    svDistinct ## Phase 15 G4 (ADR-0008 D4): a `distinct T` value. Carries the
               ## opaque distinct-sort Z3 ast (the type-wall identity) PLUS a
               ## boxed BASE SymVal — the `eject_T(distinctConst)` value, bound
               ## by the inject/eject round-trip and used for witness rendering
               ## (the eject-then-base-reader chain) and for explicit
               ## `T(distinctVal)` / `Distinct(baseVal)` conversions in the body.
    svClosure  ## Phase 15 Cluster C (C1, ADR-0009 D1): the `(funcSym, envRecord)`
               ## pair. `funcSym` is the (siteHash, declOrder)-keyed uninterpreted
               ## Z3 function (declared per site in C2a, on
               ## `WalkerStatics.closureSyms`). `envRecord` is an `svTuple` of the
               ## captured locals snapshotted at construction. STUB in C1 (no
               ## walker descent — `lower` raises `ceNotImplemented`); C2a
               ## constructs it, C2b applies it (ground per-call axiom, D6).
    svRef      ## Phase 15 Cluster R (R1a, ADR-0010): a `Ref_T`-sorted symbolic
               ## ref constant. STUB in R1a (no sort/heap semantics — allocation
               ## raises `heUnresolvedRef`); R1 allocates the `Ref_T`
               ## uninterpreted sort and the per-path `Z3Array[Ref_T, T]` heap.
    svPtr      ## Phase 15 Cluster R (R1a, ADR-0010): same heap model as `svRef`
               ## for `ptr T`. `ptrFamily` marks the pointer family (R8 pointer
               ## arithmetic). STUB in R1a.

  SymVal* = object
    ## `signed` is only meaningful when `kind in {svBV8,svBV16,svBV32,svBV64}`.
    ## Nim variant objects cannot enforce this at the type level (duplicate field
    ## names across separate `of` branches are rejected by the compiler), so we
    ## keep it as a common pre-case field but WITHOUT the export marker `*` —
    ## external callers cannot phantom-access it; all read sites in this module
    ## are already guarded by a BV-kind case branch (Stage A, CR-9(a)).
    signed: bool
    case kind*: SVKind
    of svBV8:  bv8:  Z3BitVec[8]
    of svBV16: bv16: Z3BitVec[16]
    of svBV32: bv32: Z3BitVec[32]
    of svBV64: bv64: Z3BitVec[64]
    of svInt:  zi:   Z3Int
    of svBool: bo:   Z3Bool
    of svTuple:
      fields*:     seq[SymVal]
      fieldNames*: seq[string]
    of svArray:
      arrElems*:  seq[SymVal]
      arrElemTy*: IRType
    of svString:
      str*: Z3String
    of svSeq:
      seqLen*:     Z3Int
      seqDataRaw*: Z3AnyAst       ## erased Z3Array[Z3Int, sortOf(T)]
      seqElemTy*:  IRType
      isUnsupportedFieldPlaceholder*: bool
        ## Round-6 Bug #2 (scoped decline). Default false. True iff this
        ## `svSeq` was built by `allocateSym`'s placeholder branch (a
        ## declared field whose `IRType` is `isUnsupportedFieldPlaceholder`)
        ## — `seqLen` is forced `== 0` and `seqDataRaw` is an INERT array
        ## (never selected from). Mirrors `IRType.seqUnsupportedFieldReason`
        ## onto the runtime value so `retBindEq`/witness-extraction can
        ## detect it without re-deriving from the (already-discarded) type.
    of svTable:
      tabDataRaw*:    Z3AnyAst
      tabPresentRaw*: Z3AnyAst
      tabSize*:       Z3Int       ## #144: cardinality counter; mutations
                                  ## update this alongside the present
                                  ## array.
      tabKeyTy*:      IRType
      tabValTy*:      IRType
    of svSet:
      setMembersRaw*: Z3AnyAst
      setSize*:       Z3Int       ## #144: same as tabSize, for HashSet
      setElemTy*:     IRType
    of svVariant:
      vDisc*:        ref SymVal           ## discriminator (svBV{8,16})
                                          ## boxed since SymVal is a
                                          ## value type and Nim disallows
                                          ## direct self-recursion
      vDiscName*:    string               ## discriminator field name
      vObjectName*:  string               ## Nim object name (for diagnostics)
      vArmFields*:   OrderedTable[int, seq[SymVal]]
                                          ## tag ordinal → per-arm field
                                          ## SymVals (ARM-SPECIFIC only)
      vArmFieldNames*: OrderedTable[int, seq[string]]
                                          ## arm-parallel field names
      vPlainFields*: seq[SymVal]          ## plain (always-present) field
                                          ## SymVals — shared across all
                                          ## arms; allocated once;
                                          ## survives discriminator
                                          ## reassignment.
      vPlainFieldNames*: seq[string]
    of svMultiVariant:
      ## Phase 14 cycle A1c per ADR-0003 D1. Symmetric with svVariant
      ## but holds one VariantAxisSym per discriminator. Each axis
      ## is independently constrained over `pcOut`; the walker's
      ## field-access path identifies the axis by field-name
      ## membership in any of the axis's arm field-name lists.
      mvObjectName*:      string
      mvAxes*:            seq[VariantAxisSym]
      mvPlainFields*:     seq[SymVal]
      mvPlainFieldNames*: seq[string]
    of svUninterpRef:
      ## Phase 15 Z3b. Opaque reference: an uninterpreted-sort Z3 ast plus
      ## diagnostic names. Fields are not modelled; produced by cluster E.
      uninterpAst*: Z3AnyAst
      sortName*:    string   ## Z3 uninterpreted-sort name (e.g. "ExnRef_ValueError")
      typeTag*:     string   ## Nim type name, for diagnostics
    of svFloat32:
      fp32*: Z3Float32       ## Phase 15 F1
    of svFloat64:
      fp64*: Z3Float64       ## Phase 15 F1
    of svDistinct:
      ## Phase 15 G4. A `distinct T` value modelled as an opaque const of the
      ## fresh "DistinctName" uninterpreted sort, plus its ejected base.
      distinctAst*:   Z3AnyAst   ## opaque const of the distinct uninterpreted sort
      distinctName*:  string     ## the distinct type / Z3 sort name (e.g. "Meters")
      distinctBaseSym*: ref SymVal
                                 ## eject_T(distinctAst): the base SymVal, bound
                                 ## by the round-trip; boxed (SymVal is a value
                                 ## type and cannot directly self-recurse).
    of svClosure:
      ## Phase 15 Cluster C (C1 stub → C2a construction, ADR-0009 D1). The
      ## `(funcSym, envRecord)` pair. C2a fleshes this out: `closureEnv` is the
      ## `svTuple` SNAPSHOT of the captured locals at construction; `closureRawFD`
      ## is the per-site uninterpreted `funcSym` handle (declared once per
      ## `((siteHash, declOrder), envSortId, paramsSortTupleId)` and memoized in
      ## the `currentClosureSyms` threadvar / `WalkerStatics.closureSyms`). C2b
      ## applies `closureRawFD` over the flattened env leaves ++ call args (the
      ## ground per-call axiom, D6).
      closureSite*: tuple[siteHash: int64, declOrder: int]
      closureEnv*:  ref SymVal   ## the svTuple env (boxed; SymVal cannot
                                 ## directly self-recurse). The captured-locals
                                 ## snapshot (C2a); empty svTuple in the C1 stub.
      closureRawFD*: RawZ3FuncDecl
                                 ## Phase 15 C2a: the uninterpreted funcSym handle
                                 ## (the per-site decl). Nil in the C1 stub.
    of svRef:
      ## Phase 15 Cluster R (R1, ADR-0010). A `Ref_T`-sorted symbolic ref
      ## constant. `refAst` is the uninterpreted-sort const (the abstract
      ## address `p`); `refPointee` carries the pointee type so `tyOf` and the
      ## witness reader can resolve the heap value sort without re-deriving it.
      refAst*:     Z3AnyAst
      refPointee*: IRType   ## Phase 15 R1: the `ref T` pointee type (IRType is
                            ## itself a `ref object`, so no extra boxing).
    of svPtr:
      ## Phase 15 Cluster R (R1, ADR-0010). Same model as `svRef` for `ptr T`.
      ## `ptrFamily` marks the pointer family (R8).
      ptrAst*:     Z3AnyAst
      ptrFamily*:  bool
      ptrPointee*: IRType   ## Phase 15 R1: the `ptr T` pointee type.

  VariantAxisSym* = object
    discName*:      string
    disc*:          ref SymVal
    armFields*:     OrderedTable[int, seq[SymVal]]
    armFieldNames*: OrderedTable[int, seq[string]]

  Env = OrderedTable[string, SymVal]

  Path = ref object
    pc:        seq[Z3Bool]
    defectSurvivorPc: seq[Z3Bool]
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
    env:       Env
    uncertain: bool   ## true once any call along this path has bailed
                      ## (maxCallDepth exceeded). A target hit on an
                      ## uncertain path can't be reported as a sound
                      ## witness — it degrades to sxUnknown.
    # ---- Phase 15 H1: logical-heap state (ADR-0010) ----
    # These three fields are PURE SCAFFOLDING for Cluster R. They are
    # empty/zero on every path today and the walker never reads or writes
    # them — H1 ships only the field shape so Cluster E (E3/E5/E7) and
    # Cluster R can compile against `path.heaps`. Heap SEMANTICS (alloc /
    # deref / nil-fork / alias / witness) land in Cluster R, not here.
    # The deep-copy-at-fork contract (deepCopyHeapState) is wired NOW so
    # that R does not have to re-audit every fork site.
    heaps:         Table[string, Z3AnyAst]  ## per-path symbolic heap, keyed
                                            ## by Z3 sort name (Cluster R fills)
    heapDepth:     int                      ## current heap-descent depth
                                            ## (bounded by maxHeapDepth in R)
    allocCounters: Table[string, int]       ## per-type fresh-ref counter,
                                            ## keyed by type-ID string
    # ---- Phase 15 R2: per-path live fresh-ref tracking (ADR-0010) ----
    liveRefs:      Table[string, seq[Z3AnyAst]]
      ## Phase 15 R2. Per-pointee-type list of the fresh `Ref_T` consts minted
      ## by `new T` on THIS path (keyed by the same `refPointeeTypeId` as
      ## `heaps`/`allocCounters`). `assertFreshness` reads it to emit the GROUND
      ## `newRef != prior` distinctness inequalities, then appends the new ref.
      ## Deep-copied at every fork (`deepCopyHeapState`), so DISJOINT forked
      ## paths do NOT share prior refs — a `new T` on a forked branch restarts
      ## from the fork snapshot's list (no cross-path `ref_T_i != ref_T_j`).
    freshnessAssertCount: int
      ## Phase 15 R2. Count of fresh-ref distinctness inequalities already
      ## emitted on this path; compared against `settings.maxFreshnessAssertions`
      ## (the cap). Threaded by value at every fork like `heapDepth`.

  RawWitness = object
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

  RawDiagnostic* = object
    ## ADR-0012 D2. One non-winning sxRaised finding from `w.found`,
    ## collected by the reduction in `runSymex`. Parallel to the public
    ## `DefectFinding[T]`; typed by the `symexFind` macro.
    raisedTypeId*:  string
    isDefect*:      bool
    raisedMsg*:     Option[string]
    raisedWitness*: RawWitness

  RawResult* = object
    abstractions*: AbstractionLog
    callStats*:    CallStats
    errors*:       seq[SymexErrorInfo]
      ## Phase 14 cycle C4. Z3-layer errors caught at runSymex's top
      ## level. Always empty on a clean run; populated when a typed
      ## `Z3Error` is thrown by the solver. Translated into per-
      ## target `SymexFinding.errors` by the macro-emitted runtime
      ## in `symex.nim`. `ValueError` and `AssertionDefect` from
      ## walker logic are NOT caught — those are real walker bugs.
    diagnostics*:  seq[RawDiagnostic]
      ## ADR-0012 D2. Non-winning sxRaised findings from the walk, collected
      ## by the reduction. Typed into `DefectFinding[T]` by the `symexFind`
      ## macro. Empty for sxUnsat/sxUnknown; also empty when the winner is
      ## the only sxRaised in w.found.
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

# ---- Phase 15 H1: logical-heap fork deep-copy (ADR-0010) --------------------
# Every fork site that builds a CHILD `Path` from a PARENT must carry the
# parent's heap state forward by VALUE, so a later mutation on one branch can
# never bleed into a sibling/parent path. In Nim a `Table` assignment is a deep
# value copy, so `result.heaps = src.heaps` already gives the fork isolation we
# need; this helper just names the contract for the fork sites and keeps the
# field list in one place. `heapDepth` is an `int` and copies by value with the
# rest of the construction, so it needs no helper.
#
# H1 caveat: `heaps`/`allocCounters` are empty on every path today, so these
# copies are no-ops until Cluster R populates the heap. They are wired now so R
# does not have to re-audit the fork sites. See the fork-site registry comment
# immediately above `walk`, and `forkPath`/`forkPathTainted` below (R3
# hardening) for the taint-propagation contract.
proc deepCopyHeapState(src: Path):
    tuple[heaps: Table[string, Z3AnyAst],
          allocCounters: Table[string, int],
          liveRefs: Table[string, seq[Z3AnyAst]]] =
  result.heaps = src.heaps              ## Table assignment = value copy in Nim
  result.allocCounters = src.allocCounters
  # Phase 15 R2: per-path live fresh-ref list. `Table`/`seq` assignment is a
  # value copy in Nim, so the child gets an INDEPENDENT snapshot — the fork
  # isolation that gives disjoint-path counter restart for free.
  result.liveRefs = src.liveRefs

template forkPathWithTaint(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                           uncExpr: bool): Path =
  ## Phase 15 H1 / R3 hardening: construct a CHILD `Path` from `parent`,
  ## deep-copying the logical-heap state (heaps / heapDepth / allocCounters)
  ## so the fork is isolated — the single enforcement point for the
  ## ADR-0010 fork deep-copy contract. (The fresh ROOT path in `runSymex`
  ## does NOT use this: it has no parent and correctly gets empty-default
  ## heap fields.)
  ##
  ## This is the shared INTERNAL body. It is deliberately NOT the spelling
  ## ordinary fork sites use: `uncExpr` is a bare `bool`, so a call here can
  ## silently pass `false`/forget the parent's taint. Ordinary fork sites in
  ## `walk` MUST go through one of the two public wrappers below instead —
  ## `forkPath` (implicit PROPAGATE) or `forkPathTainted` (explicit FORCE) —
  ## which make "drop the taint" unspellable. Call this internal template
  ## directly ONLY when a site needs a taint value that is neither a bare
  ## propagate nor a bare force (e.g. the isReturn return-merge site, which
  ## ORs the caller's and callee's `uncertain` together); such sites are rare
  ## and each must carry a comment explaining why.
  let hs = deepCopyHeapState(parent)
  Path(pc: pcExpr, env: envExpr, uncertain: uncExpr,
       defectSurvivorPc: parent.defectSurvivorPc,        ## Phase 16 ADR-0012
       heaps: hs.heaps, heapDepth: parent.heapDepth,
       allocCounters: hs.allocCounters,
       liveRefs: hs.liveRefs,                            ## Phase 15 R2
       freshnessAssertCount: parent.freshnessAssertCount)  ## Phase 15 R2

template forkPath(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env): Path =
  ## R3 hardening: the ONLY spelling ordinary fork sites use to derive a
  ## CHILD `Path` from `parent`. Implicitly PROPAGATES `parent.uncertain`
  ## (SND-1's per-path soundness taint) to the child — there is no bool
  ## parameter to silently drop or forget, so a future fork site can no
  ## longer accidentally lose the taint the way a bare 4th-arg bool could.
  ## Use `forkPathTainted` at sites that deliberately INTRODUCE taint.
  forkPathWithTaint(parent, pcExpr, envExpr, parent.uncertain)

template forkPathTainted(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env): Path =
  ## R3 hardening: the explicit-FORCE counterpart to `forkPath`. Sets the
  ## child's `uncertain = true` unconditionally, regardless of the parent's
  ## taint — for the small set of sites that deliberately introduce SND-1/
  ## SND-3 taint (an opaque call, a maxCallDepth/maxLoopUnwind/instantiation-
  ## cap bail, a recursion-cycle bail, an unmodeled-statement drop, or an
  ## in-band lowering-degrade). Self-documenting at the call site: no
  ## `.uncertain` field read to misread or omit.
  forkPathWithTaint(parent, pcExpr, envExpr, true)

# ---- Phase 15 H1: exported test hooks ---------------------------------------
# `Path` is a private `ref object`, so the H1 RED test cannot name it. These two
# hooks let `tests/tsymex_phase15_H1_path_heap_fields.nim` verify the field
# scaffolding and the fork deep-copy contract WITHOUT exporting the walker
# internals (`Path`, `forkPath`, the env machinery) gratuitously. They exist
# solely for that test and have no role in the walker.

proc h1PathHasHeapFields*(): bool =
  ## True iff `Path` carries the three H1 heap-state fields. Compile-time
  ## `compiles` checks on a constructed Path — they fail to compile before
  ## H1's GREEN lands (the fields do not yet exist), which is the RED signal.
  var p {.used.} = Path()
  result = compiles(p.heaps) and compiles(p.heapDepth) and
           compiles(p.allocCounters)

proc h1ForkIsolation*(): bool =
  ## Exercise the fork-site deep-copy contract directly: build a parent Path,
  ## seed `parent.heaps["x"]`, fork a CHILD via the real `forkPath` template
  ## (the same construction every fork site uses), mutate the child's
  ## `heaps["x"]` to a DIFFERENT ast, and assert the parent's entry is
  ## unchanged. This is the synthetic isolation fixture H1's DoD requires.
  let ctx = newContext()
  setCurrentContext(ctx)
  let astA = toAnyAst(mkInt(1))
  let astB = toAnyAst(mkInt(2))
  let parent = Path(pc: @[], env: initOrderedTable[string, SymVal]())
  parent.heaps["x"] = astA
  # Fork a child the way a fork site does (identical heap-state deep-copy path).
  let child = forkPath(parent, parent.pc, parent.env)
  # Child must start with an isolated copy of the parent's heap.
  doAssert child.heaps.hasKey("x")
  # Mutate the child; the parent must NOT observe it (value-copy isolation).
  child.heaps["x"] = astB
  result = parent.heaps["x"].raw == astA.raw and
           child.heaps["x"].raw == astB.raw and
           parent.heaps["x"].raw != child.heaps["x"].raw

# ---- SymVal lifting helpers -------------------------------------------------

template liftBV[W: static int](x: Z3BitVec[W], isSigned: bool): SymVal =
  ## Construct the matching SymVal variant for a given static-width BV.
  when W == 8:
    SymVal(kind: svBV8,  signed: isSigned, bv8:  x)
  elif W == 16:
    SymVal(kind: svBV16, signed: isSigned, bv16: x)
  elif W == 32:
    SymVal(kind: svBV32, signed: isSigned, bv32: x)
  elif W == 64:
    SymVal(kind: svBV64, signed: isSigned, bv64: x)
  else:
    {.error: "liftBV: unsupported width " & $W.}

template ofBool*(x: Z3Bool): SymVal =
  SymVal(kind: svBool, bo: x)

# Construct a SymVal from an IRType + a constant Nim integer value.
proc bvConst(ty: IRType, n: int64): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVec[8](n),  ty.signed)
  of 16: liftBV(mkBitVec[16](n), ty.signed)
  of 32: liftBV(mkBitVec[32](n), ty.signed)
  of 64: liftBV(mkBitVec[64](n), ty.signed)
  else:  raise newException(ValueError,
                            "bvConst: unsupported width " & $ty.width)

proc intLitProto(ty: IRType): Option[SymVal] =
  ## v69 (sello #1, bv32/svBV64 width confusion): the literal-shaping proto
  ## for a binding/argument site with a declared fixed-width int type. A bare
  ## `iekIntLit` lowered with NO proto defaults to svBV64 (`lower`'s iekIntLit
  ## arm), so `let mask = -1'i32`, an if-expression arm's temp binding, or a
  ## bare-literal call argument minted a 64-bit SymVal into 32-bit-typed
  ## flow — tripping `overflowCond`'s width-keyed field access (FieldDefect
  ## 'bv32' on svBV64) and `binBV`'s width doAssert downstream. Passing this
  ## proto shapes only LITERALS (the sole consumer of `lower`'s proto param);
  ## non-literal values are untouched. Follows the iekArrayLit elemTy-proto
  ## precedent. Plain `int` is itInt(64) — its proto equals today's default,
  ## so this is a no-op for unfixed-width code.
  if ty != nil and ty.kind == itInt and ty.width in {8, 16, 32, 64}:
    some(bvConst(ty, 0))
  else:
    none(SymVal)

proc envLitProto(env: Env, name: string): Option[SymVal] =
  ## v69 (sello #1): the literal-shaping proto for an ASSIGNMENT site, where
  ## the IR carries no declared type — the assign target's CURRENT SymVal is
  ## the authoritative representation (`x = 5` must materialize 5 at x's
  ## width). Restricted to the kinds `coerceIntLit` can shape.
  if env.hasKey(name) and env[name].kind in {svInt, svBV8, svBV16, svBV32,
                                             svBV64, svFloat32, svFloat64}:
    some(env[name])
  else:
    none(SymVal)

proc bvVar(ty: IRType, name: string): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVecVar[8](name),  ty.signed)
  of 16: liftBV(mkBitVecVar[16](name), ty.signed)
  of 32: liftBV(mkBitVecVar[32](name), ty.signed)
  of 64: liftBV(mkBitVecVar[64](name), ty.signed)
  else:  raise newException(ValueError,
                            "bvVar: unsupported width " & $ty.width)

proc allocRefSort*(ctx: Z3Context, pointeeTy: IRType): RawZ3Sort
  ## Phase 15 R3 fwd-decl (defined below) — `allocateSeqDataRaw` needs the
  ## per-walker `Ref_T` sort to build a `seq[ref T]` backing array before the
  ## R1 definition appears.
proc refPointeeTypeId*(pointeeTy: IRType): string
  ## Phase 15 R3 fwd-decl (defined below).
proc heapSelect(ctx: Z3Context, heap: Z3AnyAst, refAst: Z3AnyAst,
                pointeeTy: IRType): SymVal
  ## ADR-0013 Slice 2 fwd-decl (defined in runtime_heap.nim, included below).
  ## `extractFromSymVal` (D5 witness serialization) selects the active arm's
  ## fields out of `currentVariantHeaps` before the heap cluster is included.
proc fieldHeapKey*(objTy: IRType, field: string): string
  ## Cluster H H_witness fwd-decl (defined in runtime_heap.nim, included
  ## below). `buildHeapSnapshot`'s recursive descent needs the field-split
  ## heap key before the heap cluster is included.
proc effectiveHeapDepthLimit(settings: SymexSettings): int
  ## Cluster H H_witness fwd-decl (defined below, after `buildHeapSnapshot`).
  ## `buildHeapSnapshot` needs the SAME effective heap-depth budget the
  ## walker itself enforces (`heapDepthExhausted`) to bound its own recursion.

proc allocateSeqDataRaw(elemTy: IRType, name: string): Z3AnyAst =
  ## Dispatch on the element type to instantiate `Z3Array[Z3Int, V]`
  ## with the right typed V, then erase via `toAnyAst`. Cycle 1
  ## supports int/bool elements; more arrive incrementally.
  case elemTy.kind
  of itRef, itPtr:   ## Phase 15 R3 (ADR-0010): seq[ref T] / seq[ptr T] backing.
    # The element value sort is the per-walker uninterpreted `Ref_T` address
    # sort — a RUNTIME sort the typed `mkArrayVar[Z3Int, V]` cannot express, so
    # we build the `Z3Array[Z3Int, Ref_T]` raw (mirroring `mkHeapArrayVar`'s
    # raw-FFI discipline) and erase to `Z3AnyAst`. The array is FREE — each
    # element select yields an abstract `Ref_T` address (an svRef), which a
    # later `[]` derefs through `path.heaps[T]`. NO universal-∀ over the
    # uninterpreted sort (the G4 hang lesson).
    let ctx = requireCurrentContext()
    let pointee = if elemTy.kind == itRef: elemTy.refPointeeTy
                  else: elemTy.ptrPointeeTy
    let refSort = allocRefSort(ctx, pointee)
    let idxSort = ctx.checkErr Z3_mk_int_sort(ctx.raw)
    let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, idxSort, refSort)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
    return wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))
  of itBool:
    toAnyAst(mkArrayVar[Z3Int, Z3Bool](name))
  of itFloat32:   ## Phase 15 F9b
    toAnyAst(mkArrayVar[Z3Int, Z3Float32](name))
  of itFloat64:   ## Phase 15 F9b
    toAnyAst(mkArrayVar[Z3Int, Z3Float64](name))
  of itString:    ## Phase 15 S5: seq[string] backing array (split result / join arg)
    toAnyAst(mkArrayVar[Z3Int, Z3String](name))
  of itInt:
    case elemTy.width
    of 8:  toAnyAst(mkArrayVar[Z3Int, Z3BitVec[8]](name))
    of 16: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[16]](name))
    of 32: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[32]](name))
    of 64: toAnyAst(mkArrayVar[Z3Int, Z3BitVec[64]](name))
    else:
      raise newException(ValueError,
        "allocateSeqDataRaw: unsupported int width " & $elemTy.width)
  else:
    raise (ref SymexNestedSeqUnsupportedError)(
      msg: "seq[seq[T]] / seq[complex] not modeled — element kind " &
           $elemTy.kind & " (seNestedSeqUnsupported)")

proc mkZ3IntLit(v: int64): Z3Int {.inline.} =
  ## Phase 14 A6 (moved earlier from the abstraction layer block).
  ## Build a Z3Int from an `int64`. `mkInt` truncates to `cint`
  ## (32 bits on Linux); for values that don't fit, route through
  ## `mkBigInt`'s decimal-string ctor.
  if v >= int64(low(int32)) and v <= int64(high(int32)):
    mkInt(int(v))
  else:
    mkBigInt($v)

# ---- Phase 15 G4: `distinct T` fresh-uninterpreted-sort machinery -----------
#
# A `distinct T` is a TYPE WALL: a fresh uninterpreted Z3 sort, NOT the base
# sort. Two uninterpreted functions per distinct type model the round-trip —
# `inject_T: Base→Distinct` and `eject_T: Distinct→Base`. Bijectivity axioms
# (`∀x:Base. eject(inject(x))==x` and `∀y:Distinct. inject(eject(y))==y`) are
# asserted ONLY when the base is in the decidable fragment {int, BV, bool}; for
# {float32, float64, string} the universally-quantified axioms over FP/string
# sorts push Z3 into the incomplete quantified fragment (a hang risk), so they
# are SKIPPED and a `geDistinctBijectivitySkipped` (sevHint) is emitted.
#
# `allocateSym` has no `WalkCtx` access (it is a pure type→SymVal allocator), so
# the per-run distinct-sort cache + the inject/eject func-decls live in
# threadvars reset at `runSymexImpl` entry — exactly E8's in-flight-exn-mirror
# mechanism. `WalkerStatics.distinctSorts` (ADR-0008 D4) records the same map
# for post-walk inspection; the threadvar is the live populator.

type DistinctSortEntry = object
  sort:    Z3Sort[stUninterpreted]    ## the fresh "DistinctName" sort
  inject:  RawZ3FuncDecl              ## inject_T: Base → Distinct
  eject:   RawZ3FuncDecl              ## eject_T: Distinct → Base

var currentDistinctSorts* {.threadvar.}: Table[string, DistinctSortEntry]
  ## Phase 15 G4. Per-run cache of distinct sorts + their inject/eject
  ## func-decls, keyed by distinct type name. Reset at `runSymexImpl` entry.
  ## Shared across all call frames (one entry per distinct type per run) — the
  ## sort allocation + bijectivity axioms fire AT MOST ONCE per (name, run).

var distinctBijectivityHints* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 G4. Accumulator for `geDistinctBijectivitySkipped` (sevHint),
  ## emitted when a distinct type's base is FP/String (bijectivity elided).
  ## Reset at `runSymexImpl` entry; drained into `RawResult.errors` on every
  ## verdict branch (a hint never changes the verdict). Mirrors E4's
  ## `unknownExnWarnings` threadvar.

var distinctSortNames* {.threadvar.}: seq[string]
  ## Phase 15 G4 test hook: the order distinct sorts were first allocated this
  ## run (so a test can assert "two sorts allocated" for a nested chain).

var freshnessCapHints* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 R2. Accumulator for `heFreshnessCapExceeded` (sevHint), emitted
  ## when a `new T` on a path would push the freshness-assertion count past
  ## `settings.maxFreshnessAssertions`. Reset at `runSymexImpl` entry; drained
  ## (dedup'd) into `RawResult.errors` on every verdict branch. A hint never
  ## changes the verdict (Invariant 7) — exactly the G4 `distinctBijectivityHints`
  ## idiom. The walker has a `WalkCtx` at the `isNew` arm, but the drain is a
  ## verdict-time concern shared across paths, so it rides the threadvar sink.

var heapDepthErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 R9 (ADR-0010). Accumulator for `heDepthExhausted` (sevError),
  ## recorded when a deref/deref-write on a path would push `path.heapDepth` to
  ## the EFFECTIVE heap-depth limit (`maxHeapDepth`, else `maxCallDepth`, else
  ## 256). The exhausting path is HALTED (it returns no survivor → contributes
  ## `sxUnknown` via `w.sawUnknown`); shallower paths continue. The error rides
  ## every verdict branch via `exnWarnings` (dedup'd by message) so a degraded
  ## `sxUnknown` carries the classified kind (Invariant 3). Reset at
  ## `runSymexImpl` entry. A SUT whose every deref stays UNDER the cap drains
  ## NOTHING — exactly the R2 `freshnessCapHints` / R8 `ptrFamilyHints` idiom.

var newFieldZeroErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Cluster H Step C (ADR-0022). Accumulator for `heNewFieldZeroUnsupported`
  ## (sevError), recorded when the universal `isNew` zero-write
  ## (`runtime_heap.nim`) finds a freshly-allocated object FIELD whose type has
  ## no clean zero encoding this cycle (`zeroIRExprForType` returned `nil`).
  ## The path is tainted `uncertain = true` and `w.sawUnknown` is set (SND-1,
  ## mirroring `isUnsupported`) rather than halted outright, so a shallower/
  ## unrelated finding on the SAME run can still surface — but this path's own
  ## verdict is forced to `sxUnknown`. Reset at `runSymexImpl` entry; drained
  ## (dedup'd) into `RawResult.errors` on every verdict branch — exactly the R9
  ## `heapDepthErrors` idiom.

var ptrFamilyHints* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 R8. Accumulator for `hePtrFamily` (sevHint), emitted whenever an
  ## UNMANAGED `ptr T` (an `svPtr`, `ptrFamily = true`) is dereffed or written
  ## through. Lets consumers distinguish an unmanaged-ptr witness from a managed
  ## `ref T` one (which emits NO such hint). A hint never changes the verdict
  ## (Invariant 7) — drained (dedup'd) into `RawResult.errors` on every verdict
  ## branch, exactly the R2 `freshnessCapHints` idiom. Reset at `runSymexImpl`
  ## entry.

var loweringDegradeErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## RFC-chapulin-hardening SND-3 (walker v58, ADR-0023). Accumulator for a
  ## lowering-time degrade of an unmodeled expression-lowering construct
  ## (currently: char-ordering / string-ordering / non-int64-set `contains`
  ## comparisons — see `loweringDidDegrade`). Populated from INSIDE `lower()`
  ## (and pure helpers it calls, e.g. `cmpString`), which has no `w: var
  ## WalkCtx` in scope, so — unlike `newFieldZeroErrors`'s CR-9 Stage-5
  ## dual-store — this is threadvar-ONLY (no parallel WalkCtx field). Reset at
  ## `runSymexImpl` entry; drained (dedup'd) into `RawResult.errors` on every
  ## verdict branch — exactly the R9 `heapDepthErrors` idiom.

var setMembershipKeyTerms* {.threadvar.}: Table[uint, seq[Z3AnyAst]]
  ## v65 (round-3 ledger: HashSet witness gap, root-caused). Registry of the
  ## exact KEY TERMS asserted in `iekContains`/svSet membership constraints,
  ## keyed by the membership array's raw AST pointer. Why it exists: for a
  ## symbolically-keyed membership (`s.len in hs`), Z3's simplest model is
  ## the CONST-TRUE array — the set is universal, there is no store chain to
  ## harvest and no literal candidate to probe, so the extracted finite
  ## witness came out EMPTY (observed `s = "", hs = {}` — inconsistent).
  ## Evaluating each recorded key term under the model yields the concrete
  ## member(s) the program actually tested — the minimal faithful finite
  ## rendering of a possibly-universal model set. Reset at `runSymexImpl`
  ## entry. Mutated sets (`incl` → `store`) re-key to the new array AST and
  ## simply miss — extraction then falls back to candidates + store-chain
  ## harvest, the pre-v65 behaviour.

var loweringDidDegrade* {.threadvar.}: bool
  ## RFC-chapulin-hardening SND-3 (walker v58, ADR-0023). Per-`lower()`-call
  ## signal: set alongside `loweringDegradeErrors` whenever a lowering site
  ## degrades in-band (returns a fresh unconstrained symbol) instead of
  ## `raise`-ing. MUST NEVER be consumed via a bare `w.sawUnknown = true` at
  ## the raise site — that alone would be UNSOUND (a fresh unconstrained bool
  ## on the tainted path could let that path reach the target and fabricate a
  ## false `sxSat`, trading a false `sxUnsat` for a WORSE false `sxSat` under
  ## Invariant 3). Instead this flag is consumed EXCLUSIVELY by
  ## `drainPendingLowerEffects` — the single choke-point every `lower()`/
  ## `lowerBool()` call site in `walk` already drains through — which forks
  ## the PATH's `uncertain = true` (SND-1's per-path taint) before also
  ## setting `w.sawUnknown` via `currentWalkCtxPtr`, then resets this flag.
  ## THE reason a lowering-time degrade must NEVER `raise`: on the C backend
  ## (goto exceptions), a raise deep inside expression lowering that unwinds
  ## through a loop's live `seq[Path]` result is SILENTLY LOST (the
  ## b7258f7/CR-1c divergence class) — the walk continues with a mis-lowered
  ## guard, producing a false `sxUnsat` (c) vs. the honest `sxUnknown` (cpp,
  ## whose native exceptions propagate cleanly). In-band taint sidesteps the
  ## raise entirely, so both backends agree.

var convFloatToIntBoundConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 CR-3/CR-4. Path constraints deposited by `lower(iekConvFloatToInt)`
  ## bounding the float operand to the target integer type's representable range.
  ## Each `int(f)` / `int32(f)` lowering appends one `Z3Bool` (a conjunction of
  ## FP range + finiteness constraints) here. The walker drains this into the
  ## current path condition immediately after any `lower()`/`lowerBool()` call —
  ## mirroring the `parseIntRaiseConds` / `drainParseIntRaises` pattern (S10b).
  ## Reset at each `lower` call-site in the walker (before the call) and consumed
  ## (not forked — it's a path-narrowing, not a branch) immediately after.
  ## Reset at `runSymexImpl` entry.

var convFloatToIntDomainConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 R16-2. Parallel sink to `convFloatToIntBoundConds`: carries the
  ## SAME `domainCond` (in-range predicate) deposited by `lower(iekConvFloatToInt)`,
  ## but drained by `drainConvFloatToIntRaises` (a raise-fork drain) rather than
  ## `drainConvFloatToIntBounds` (a path-narrowing drain). The raise fork branches
  ## off the PRE-narrowing path with `not(domainCond)` → RangeDefect, so the two
  ## drains are DUAL: the bounds drain narrows the normal path; this drain opens the
  ## raise path. `syncConvFloatToIntDomainCond` appends here when in a walk.
  ## Reset at every `convFloatToIntBoundConds` reset site (they are always in sync).

var divByZeroConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 R16-3. Raise-fork sink for div/mod-by-zero predicates.
  ## `lowerArith` pushes `divisorIsZero(b)` here for every `bDiv`/`bMod`
  ## op on svInt or BV operands. `drainDivByZeroRaises` (called via
  ## `drainScalarRaiseForks`) reads and resets this sink, forking each
  ## predicate as a `DivByZeroDefect` raise path. The surviving non-zero
  ## continuation carries the negated predicates in its pc.
  ## `syncDivByZeroCond` appends to `WalkCtx.divByZeroConds` when in a walk.
  ## Reset alongside `convFloatToIntBoundConds`/`convFloatToIntDomainConds`
  ## at every reset site.

var overflowConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 R16-4. Raise-fork sink for signed integer overflow predicates.
  ## `lowerArith` pushes overflow conditions here for bAdd/bSub/bMul ops on
  ## signed BV operands (int, int8..int64). `drainOverflowRaises` (called via
  ## `drainScalarRaiseForks`) reads and resets this sink, forking each predicate
  ## as an `OverflowDefect` raise path. The surviving non-overflow continuation
  ## carries the negated predicates in its pc.
  ## `syncOverflowCond` appends to `WalkCtx.overflowConds` when in a walk.
  ## svInt (unbounded Z3Int) is skipped — overflow is meaningless there AND BV
  ## predicates on Int terms hang Z3. Unsigned BV is skipped — Nim wraps silently.
  ## Reset alongside `divByZeroConds` at every reset site.

var strIndexOobConds* {.threadvar.}: seq[Z3Bool]
  ## RFC-chapulin-hardening SND-4 (ADR-0024). Raise-fork sink for string-index
  ## (`s[i]`) out-of-bounds predicates. `lowerStrArm`'s `iekStrAt` arm pushes
  ## `(idx < 0) or (idx >= len(s))` here for every `s[i]` (char read) lowered.
  ## `drainStrIndexRaises` (called via `drainScalarRaiseForks`) reads and
  ## resets this sink, forking each predicate as a routed `IndexDefect` raise
  ## path — parity with the seq/array/Table indexing arms, which already fork
  ## `IndexDefect` unconditionally (Phase 16 D1a); `s[i]` was the sole
  ## container-index site with zero bounds modeling (an OOB read silently
  ## degraded to a fabricated byte value via Z3's `at`/`toCode` spec instead of
  ## raising). The surviving in-bounds continuation carries the negated
  ## predicates as `defectSurvivorPc` facts (ADR-0012), exactly like
  ## `parseIntRaiseConds`/`divByZeroConds`/`overflowConds`.
  ## `syncStrIndexOobCond` appends to `WalkCtx.strIndexOobConds` when in a walk.
  ## Reset alongside `overflowConds` at every reset site.

# ---- Phase 15 Cluster R (R1): per-walker ref-sort + nil-const cache -----------
#
# Each distinct `ref T`/`ptr T` pointee type gets ONE fresh uninterpreted sort
# `Ref_<typeId>` (`mkUninterpretedSort`) shared across every path — the sort is
# per-WALKER, not per-path (ADR-0010). Like G4's distinct sorts and C2a's
# closure funcSyms, the sort is allocated where there is no `WalkCtx`
# (`allocateSym(itRef)`, a pure type→SymVal allocator, allocates the param's
# `Ref_T` const), so the cache lives in threadvars reset at `runSymexImpl`
# entry and is mirrored into `WalkerStatics.refSorts`/`.nilConsts` after the
# walk for post-run inspection. The `nil_<typeId>` const rides alongside.

var currentRefSorts* {.threadvar.}: Table[string, RawZ3Sort]
  ## Phase 15 R1 (ADR-0010). Per-run cache of `Ref_T` uninterpreted sorts,
  ## keyed by pointee typeId. The LIVE populator (`allocateSym(itRef)` /
  ## `allocRefSort`); reset at `runSymexImpl` entry; mirrored into
  ## `WalkerStatics.refSorts`. Allocated AT MOST ONCE per (typeId, run).

var currentNilConsts* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 R1 (ADR-0010). The `nil_<typeId>` distinguished constant of each
  ## `Ref_T` sort. Allocated alongside the sort in `allocRefSort`; reset at
  ## `runSymexImpl` entry; mirrored into `WalkerStatics.nilConsts`.

# CR-9 Stage 4: `currentWalkCtxPtr` moved here (from the C2b cluster) so that
# `allocRefSort` and `assertFreshness` — defined before `WalkCtx` — can test
# the nil-guard and delegate to `syncRefSortEntry` (forward-decl below). The
# variable is `pointer` (not `ptr WalkCtx`) so no WalkCtx forward-reference is
# needed; callers cast it after WalkCtx is in scope.
var currentWalkCtxPtr* {.threadvar.}: pointer
  ## Phase 15 C2b. A `ptr WalkCtx` to the live walk, set in `runSymexImpl`
  ## immediately before the top-level `walk` so `lowerClosureCall` (running in
  ## the `lower` evaluator, which has no `WalkCtx` parameter) can drive a body
  ## descent through `walk`. Typed `pointer` because `WalkCtx` is declared far
  ## below `lower`; cast back at use. Nil outside an active walk (the C2a probes
  ## and `c1ClosurePoCApply` never set it — they don't reach `iekClosureCall`).
  ## CR-9 Stage 4: also used by `allocRefSort`/`assertFreshness` (pre-WalkCtx
  ## procs) via `syncRefSortEntry` to populate `WalkerStatics.refSorts/nilConsts`
  ## during an active walk.

proc syncRefSortEntry*(typeId: string, srt: RawZ3Sort, nc: Z3AnyAst)
  ## CR-9 Stage 4 fwd-decl. If `currentWalkCtxPtr != nil`, copies `srt`/`nc`
  ## into `WalkCtx.statics.refSorts[typeId]`/`.nilConsts[typeId]`. No-op when
  ## no active walk (probe paths). Defined after `WalkCtx` type.

proc syncDistinctSortEntry*(name: string, entry: DistinctSortEntry)
  ## CR-9 Stage 4 fwd-decl. If `currentWalkCtxPtr != nil`, copies `entry`
  ## into `WalkCtx.statics.distinctSorts[name]` and appends `name` to
  ## `.distinctSortNames`. No-op when no active walk. Defined after `WalkCtx`.

proc syncFreshnessCapHint*(info: SymexErrorInfo)
  ## CR-9 Stage 5 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active),
  ## appends `info` to `WalkCtx.freshnessCapHints`. No-op when no active walk
  ## (assertFreshness can be called from probe paths). Defined after `WalkCtx`.

proc syncDistinctBijectivityHint*(info: SymexErrorInfo)
  ## CR-9 Stage 5 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active),
  ## appends `info` to `WalkCtx.distinctBijectivityHints`. No-op when no active
  ## walk (allocDistinctSym can be called from probe/pre-walk paths). Defined
  ## after `WalkCtx`.

proc syncConvFloatToIntDomainCond*(cond: Z3Bool)
  ## R16-2 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active), appends
  ## `cond` to `WalkCtx.convFloatToIntDomainConds` (the LIVE store for the
  ## parallel raise-fork sink). No-op when no active walk (lower() can be called
  ## from probe paths). Defined after `WalkCtx`.

proc syncDivByZeroCond*(cond: Z3Bool)
  ## R16-3 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active), appends
  ## `cond` to `WalkCtx.divByZeroConds` (the LIVE store for the div/mod-by-zero
  ## raise-fork sink). No-op when no active walk. Defined after `WalkCtx`.

proc syncOverflowCond*(cond: Z3Bool)
  ## R16-4 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active), appends
  ## `cond` to `WalkCtx.overflowConds` (the LIVE store for the signed-integer
  ## overflow raise-fork sink). No-op when no active walk. Defined after `WalkCtx`.

proc syncStrIndexOobCond*(cond: Z3Bool)
  ## RFC-chapulin-hardening SND-4 fwd-decl. If `currentWalkCtxPtr != nil` (a
  ## walk is active), appends `cond` to `WalkCtx.strIndexOobConds` (the LIVE
  ## store for the string-index OOB raise-fork sink). No-op when no active walk
  ## (lower() can be called from probe paths). Defined after `WalkCtx`.

proc syncExtractionError*(info: SymexErrorInfo)
  ## CR-9 Stage 5 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active),
  ## appends `info` to `WalkCtx.extractionErrors`. No-op when no active walk
  ## (extractLeaf/extractFromSymVal always run inside trySolve which is called
  ## inside walk arms, but the guard ensures correctness). Defined after `WalkCtx`.

proc syncClosureCallError*(info: SymexErrorInfo)
  ## CR-9 Stage 5 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active),
  ## appends `info` to `WalkCtx.closureCallErrors`. No-op when no active walk
  ## (lowerClosureCall/applyClosureGround/lowerHofCall run in lower() which has
  ## no WalkCtx). Defined after `WalkCtx`.

proc syncConvFloatToIntBoundCond*(cond: Z3Bool)
  ## CR-9 Stage 6 fwd-decl (Group-1). If `currentWalkCtxPtr != nil` (a walk
  ## is active), appends `cond` to `WalkCtx.convFloatToIntBoundConds`.
  ## No-op when no active walk (lower() can be called from probe paths).
  ## Defined after `WalkCtx`.

proc syncParseIntRaiseCond*(cond: Z3Bool)
  ## CR-9 Stage 6 fwd-decl (Group-2). If `currentWalkCtxPtr != nil` (a walk
  ## is active), appends `cond` to `WalkCtx.parseIntRaiseConds`.
  ## No-op when no active walk (lower() can be called from probe paths).
  ## Defined after `WalkCtx`.

proc syncParseIntGateConstraint*(c: Z3Bool)
  ## CR-9 A0 fwd-decl. If `currentWalkCtxPtr != nil` (a walk is active),
  ## appends `c` to `WalkCtx.parseIntGateConstraints` so the field is the
  ## LIVE store for parseInt digits-gate constraints during a walk. No-op
  ## when no active walk (lower() can be called from probe paths).
  ## Defined after `WalkCtx`.

proc parseIntGateConstraintsLive*(): seq[Z3Bool]
  ## CR-9 A0 fwd-decl. Returns the active parseInt digits-gate constraint
  ## sequence for `trySolve` to assert. When a walk is active
  ## (`currentWalkCtxPtr != nil`), returns `WalkCtx.parseIntGateConstraints`
  ## (the LIVE store); otherwise falls back to the `parseIntGateConstraints`
  ## threadvar. Mutually exclusive — never both — so no constraint is
  ## double-asserted. Defined after `WalkCtx` (needs the cast).
  ## Called from `trySolve` (defined before `WalkCtx`, so cannot cast directly).

proc seedCallerHeapInWalkCtx*(p: Path)
  ## CR-9 Stage 6 fwd-decl (Groups 3+4). If `currentWalkCtxPtr != nil` (a
  ## walk is active), mirrors `p`'s heap state into the WalkCtx fields
  ## (callerHeaps/HeapDepth/AllocCounters/LiveRefs) AND resets the
  ## closure-exit fields (closureExitHeaps/AllocCounters/LiveRefs/
  ## DidMutateHeap) so each lower() call starts with a clean exit-heap slate.
  ## Companions the threadvar-only `seedCallerHeapThreadvars` (which still
  ## runs for the threadvar fallback path).
  ## Defined after `WalkCtx`.

var currentHeapDerefVals* {.threadvar.}: Table[string, SymVal]
  ## Phase 15 R1 (ADR-0010, C7/Breadth-CRIT-1). The MINIMAL R1 witness reader
  ## hook: when a `ref T`/`ptr T` PARAM `p` is dereferenced, the heap-select
  ## value (`select(heap, p)`) is recorded here keyed by the param name, so the
  ## witness for `p` renders the dereffed value (the value `p[]` takes in the
  ## model) rather than a silent empty leaf. `extractFromSymVal(svRef/svPtr)`
  ## consumes it. (The full heap-snapshot witness format — `pointsTo`/`aliasRef`
  ## per ADR-0010 §Heap witness invariants — lands R11b/R12; R1 needs only a
  ## sound scalar reader for the `ref int` DoD.) Reset at `runSymexImpl` entry.

var currentVariantHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## ADR-0013 D5 (Slice 2). The WINNING path's logical-heap arrays, snapshotted
  ## just before `extractWitness` (in `trySolve`'s sat branch) so the witness
  ## serializer can `select` a ref-to-variant pointee's ACTIVE-arm field values
  ## out of the per-(arm,field) heaps (`<typeId>__@<ord>__<field>`) at the ref's
  ## abstract address — emitting only the active arm's observed fields (D5).
  ## Mirrors `currentHeapDerefVals`'s role for the disc/plain leaves. Keyed by
  ## the same `heapKey` strings the walk used. Reset at `runSymexImpl` entry.

var heapWitnessNominalRegistry* {.threadvar.}: Table[string, IRType]
  ## Cluster H H_witness (ADR-0022, ADR-0010 invariant #4). Maps a named
  ## object's `nominalId` to its FULL (non-placeholder) `itTuple` IRType, so
  ## the recursive heap-snapshot witness can recover a RECURSIVE FIELD's real
  ## field list. `classifyFieldType` (`dsl_typebridge.nim`, Phase 15 R9) gives
  ## a ref-typed OBJECT FIELD (e.g. `next: Node`) an EMPTY-fielded
  ## `namedRefPlaceholder` pointee — deliberately, to keep the compile-time
  ## `IRType` finite for a self-referential object — so `pointee.fields` at a
  ## FIELD site is never the real field list. `refPointeeTypeId` already
  ## unifies the placeholder and the full pointee onto the SAME `Ref_<id>`
  ## sort by keying on `nominalId` (Cluster H Step B), so this registry keys
  ## the same way: populated the first time `buildHeapSnapshot`'s traversal
  ## observes a genuinely-fielded instance of a nominal type (always true for
  ## a bare ref/ptr PARAM's pointee, or a container element's pointee — a
  ## `namedRefPlaceholder` is never registered, `isPlaceholder` guards it).
  ## `resolveObjectFields` reads it; a lookup miss (never observed a full
  ## instance this run) means the schema is genuinely unknown and nested
  ## rendering honestly renders an empty object rather than guessing fields.
  ## Reset at `runSymexImpl` entry alongside `currentRefSorts`.

var currentCallerHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 R1b (ADR-0010). The CALLER path's logical-heap arrays, threaded
  ## into a CLOSURE-call descent. The `isCall`/`isGenericCall` arms thread the
  ## caller heap structurally (the callee path is `forkPath`'d from the caller,
  ## carrying `p.heaps` in via `deepCopyHeapState`), but a `iekClosureCall` is
  ## lowered inside `lower` (a pure env→SymVal evaluator with NO `Path` in
  ## scope — the same constraint that forced `currentWalkCtxPtr`). So the walk
  ## arm that is about to lower an expression seeds this threadvar from the
  ## current path's `heaps`, and `applyClosureGround` builds the closure
  ## `descentBase` from it instead of R1's fresh-empty default — so a deref in
  ## the closure body reads the SAME threaded heap. Reset at `runSymexImpl`
  ## entry and (re)seeded per path before expression lowering.
  ## NOTE: closure-body heap WRITES (the return-merge BACK out of a closure
  ## descent) are inert until R4 (closures cannot mutate the heap yet); R1b
  ## threads the READ direction (entry) for the closure arm.

var currentCallerHeapDepth* {.threadvar.}: int
  ## Phase 15 R1b. Companion to `currentCallerHeaps`: the caller path's
  ## `heapDepth`, threaded into the closure descent's `descentBase`.

var currentCallerAllocCounters* {.threadvar.}: Table[string, int]
  ## Phase 15 R1b. Companion to `currentCallerHeaps`: the caller path's
  ## `allocCounters`, threaded into the closure descent's `descentBase` so
  ## allocations inside the closure body (R2+) start above the caller's
  ## freshness counters.

var currentCallerLiveRefs* {.threadvar.}: Table[string, seq[Z3AnyAst]]
  ## Phase 15 CR-5. Companion to `currentCallerHeaps`: the caller path's
  ## `liveRefs`, seeded into the closure `descentBase` so `assertFreshness`
  ## for a `new T` inside the closure body emits `newRef != callerRef`
  ## distinctness inequalities against every prior live ref the caller
  ## already minted. Without this seed, the closure descent sees an empty
  ## `liveRefs` and Z3 can alias a closure-body `new T` with a caller ref
  ## (CR-5 spurious aliasing witness). Reset at `runSymexImpl` entry.

# ---- Phase 15 CR-1: post-closure heap state threadvars ----------------------
# Complement to the `currentCallerHeap*` entry threadvars (R1b): these carry
# the EXIT heap from a closure body descent BACK to the calling walk arm.
# `applyClosureGround` writes them after merging the closure's exit paths;
# `drainClosureExitHeap` in `walk` applies them to the survivor path. This
# mirrors the named-proc return-merge (isCall arm ~5443-5463) for the closure
# arm — the same `max(caller, callee)` allocCounter merge and direct heap
# replacement. Reset at `runSymexImpl` entry and at each `applyClosureGround`
# entry (so a non-heap-writing closure leaves the drain a no-op).

var currentClosureExitHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 CR-1. The merged logical-heap arrays from the closure body's
  ## exit paths. Written by `applyClosureGround` when the body produced at
  ## least one exit path; empty when the closure produced no exit paths (the
  ## body diverged or was fully-stubbed).

var currentClosureExitAllocCounters* {.threadvar.}: Table[string, int]
  ## Phase 15 CR-1. The per-type alloc counter from the closure body's exit
  ## heap (max-merged over all exit paths, exactly like the named-proc arm).

var currentClosureExitLiveRefs* {.threadvar.}: Table[string, seq[Z3AnyAst]]
  ## Phase 15 CR-1. The per-type live-ref list from the closure body's exit
  ## heap (union-merged over all exit paths so subsequent caller `new T`s
  ## are distinct from every closure-allocated ref too).

var currentClosureDidMutateHeap* {.threadvar.}: bool
  ## Phase 15 CR-1. True iff `applyClosureGround` merged at least one
  ## closure exit path back; the drain proc skips the update when false so
  ## a heap-write-free closure call is a no-op on the caller path's heaps.

var currentClosureExitPc* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 ADR-0012. Caller-LOCAL defect-survivor facts produced by a closure
  ## body descent (`applyClosureGround`): each exit path's `not overflow`/`not
  ## divByZero`/`not parseIntRaise` negations, guarded by that path's branch
  ## conditions (`implies(branchConds_i, neg)`). Mirrors the closure-exit-HEAP
  ## channel (`currentClosureExitHeaps`): written by `applyClosureGround`, drained
  ## by `drainPendingLowerEffects` onto the caller path's `defectSurvivorPc`, reset
  ## by `seedCallerHeapThreadvars` before each lower() and at `runSymexImpl` entry.
  ## CRUCIAL (anti-masking): this is NOT `currentClosureCallAxioms` — those drain
  ## into every trySolve globally; a GLOBAL `not overflow` would make the in-body
  ## OverflowDefect raise path UNSAT and mask the defect. These facts are local to
  ## the caller continuation only.

proc seedCallerHeapThreadvars*(p: Path) {.inline.} =
  ## Phase 15 R1b / CR-5. Mirror a path's logical-heap state (and liveRefs)
  ## into the caller-heap threadvars so a CLOSURE call lowered out of `p.env`
  ## (no `Path` in scope) descends with the caller's threaded heap and
  ## liveRefs (ADR-0010 R1b; CR-5 freshness seeding). Mirrors the
  ## `setInFlightThreadvars` (E8) / `currentWalkCtxPtr` (C2b) idiom.
  ##
  ## CR-9 Stage 6: also calls `seedCallerHeapInWalkCtx` (forward-decl above;
  ## defined after WalkCtx) to mirror the same values into the live WalkCtx
  ## fields when a walk is active, keeping the threadvar path and WalkCtx path
  ## in sync for Groups 3 and 4.
  currentCallerHeaps = p.heaps
  currentCallerHeapDepth = p.heapDepth
  currentCallerAllocCounters = p.allocCounters
  currentCallerLiveRefs = p.liveRefs                     ## Phase 15 CR-5
  # Reset the exit-heap threadvars so a non-heap-writing closure doesn't
  # carry the PREVIOUS call's exit heap forward to the next call.
  currentClosureDidMutateHeap = false                     ## Phase 15 CR-1
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()
  currentClosureExitAllocCounters = initTable[string, int]()
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  currentClosureExitPc = @[]                              ## Phase 16 ADR-0012
  # CR-9 Stage 6 Groups 3+4: mirror into WalkCtx fields (dual-write).
  seedCallerHeapInWalkCtx(p)

proc rawConstOf(ctx: Z3Context, sort: RawZ3Sort, name: string): RawZ3Ast
  ## Phase 15 R2: forward decl (defined below) — `freshRef` mints its fresh
  ## `Ref_T` const through it before its definition appears. Bodies of
  ## `refPointeeTypeId`, `allocRefSort`, `freshRef`, `assertFreshness`,
  ## `pcImpliesNonNil` moved to runtime_heap.nim (CR-7-deeper Stage 8+).

# ---- Phase 15 Cluster C (C2a): per-site closure funcSym memoization ----------
#
# A lambda site's uninterpreted `funcSym` is declared ONCE per
# `((siteHash, declOrder), envSortId, paramsSortTupleId)` and reused across
# every construction of that closure on the run. Like G4's distinct sorts, the
# decl is built where there is no `WalkCtx` (closure construction runs in
# `lower`, a pure env→SymVal evaluator), so the cache lives in a threadvar reset
# at `runSymexImpl` entry — the exact `currentDistinctSorts` idiom.
# `WalkerStatics.closureSyms` mirrors it after the walk for inspection.

type ClosureSymKey* = tuple[siteHash: int64, declOrder: int,
                            envSortId: string, paramsSortTupleId: string]
  ## Phase 15 C2a (ADR-0009). The memo key: the lambda-site identity PLUS the
  ## construction-time env/param sort fingerprints (so the SAME site at two
  ## monomorphizations — distinct leaf/param sorts — gets distinct funcSyms).

var currentClosureSyms* {.threadvar.}: Table[ClosureSymKey, RawZ3FuncDecl]
  ## Phase 15 C2a. Per-run cache of per-site closure funcSyms. Reset at
  ## `runSymexImpl` entry; the LIVE populator (`lower(iekLambda)` has no
  ## `WalkCtx`). Mirrored into `WalkerStatics.closureSyms` after the walk.

proc syncClosureSymEntry*(key: ClosureSymKey, fd: RawZ3FuncDecl)
  ## CR-9 Stage 4 fwd-decl. If `currentWalkCtxPtr != nil`, copies `fd`
  ## into `WalkCtx.statics.closureSyms[key]`. No-op when no active walk
  ## (C2a probe paths, pre-walk lambda lowering). Defined after `WalkCtx`.

# ---- Phase 15 Cluster C (C2b): closure-CALL descent plumbing -----------------
#
# `lower(iekClosureCall)` must descend the lambda BODY to collect its return
# sub-paths and assert the GROUND per-call axiom (ADR-0009 D6). But the body is
# in `iekLambda.lambdaBody`, NOT carried on `svClosure` (which holds only the
# site key + env + funcSym). So at CONSTRUCTION (`buildClosure`) we stash the
# lambda's body + signature in `currentClosureBodies`, keyed by `(siteHash,
# declOrder)`. At the call, the resolved `svClosure`'s site keys back into this
# map to reach the body. (Same threadvar idiom as `currentClosureSyms` — `lower`
# has no `WalkCtx`. Reset at `runSymexImpl` entry.)

type ClosureBody* = object  ## Phase 15 C2b. The descent payload for a lambda
                            ## site, stashed at construction so the CALL can
                            ## reach the body that `svClosure` does not carry.
  body*:     IRStmt
  params*:   seq[IRParam]
  captures*: seq[string]
  retTy*:    IRType

var currentClosureBodies* {.threadvar.}: Table[
    tuple[siteHash: int64, declOrder: int], ClosureBody]
  ## Phase 15 C2b. Per-run site→body map (the body `svClosure` does not carry).
  ## Populated by `buildClosure` (C2a construction path), consumed by
  ## `lowerClosureCall` (C2b application). Reset at `runSymexImpl` entry.

proc syncClosureBodyEntry*(siteKey: tuple[siteHash: int64, declOrder: int],
                           cb: ClosureBody)
  ## CR-9 Stage 4 fwd-decl. If `currentWalkCtxPtr != nil`, copies `cb`
  ## into `WalkCtx.statics.closureBodies[siteKey]`. No-op when no active
  ## walk (probe paths). Defined after `WalkCtx` type.

var currentClosureCallAxioms* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 C2b (ADR-0009 D6). The GROUND per-call-site closure axioms
  ## (`implies(callerPC and pc_i, funcSym(env, args) == v_i)`), one per body
  ## return sub-path of each closure call lowered this run. Each is a CLOSED
  ## implication (vacuously true off its call occurrence's path), so — like the
  ## `parseIntGateConstraints` digits-gate — it is drained into EVERY `trySolve`
  ## globally. NEVER a `∀env,args` axiom (that HANGS Z3 — the G4 MBQI lesson);
  ## the function is applied at the GROUND `(env, args)` of THIS occurrence and
  ## equated to a value, identical in shape to G4's decidable eject-pin. Reset
  ## at `runSymexImpl` entry.
  ## CR-9 A0: intentionally LEFT as a threadvar. It is a global-by-design solver
  ## axiom pool drained into every `trySolve` check — soundness-critical and just
  ## stabilised by ADR-0012 slice 1. Migrating it to a WalkCtx field yields no
  ## verdict benefit and risks the closure-soundness machinery.

var currentClosureCallAxiomStrs* {.threadvar.}: seq[string]
  ## Phase 15 C2b test hook. The SMT-LIB rendering (`Z3_ast_to_string`) of each
  ## asserted closure-call axiom, captured WHILE the Z3 context is live (a raw
  ## `Z3Bool` handle outlives its context as a dangling pointer, so a test must
  ## not stringify `currentClosureCallAxioms` after the run). Lets a test assert
  ## the GROUND multi-return-path encoding — both `=>` arms, no `forall`. Reset
  ## at `runSymexImpl` entry.
  ## CR-9 A0: intentionally LEFT as a threadvar. It is a Z3-context-lifetime-bound
  ## test hook: `tests/tsymex_phase15_C2b_closure_call.nim` reads it POST-RUN.
  ## A WalkCtx field would be freed when the Z3 context is destroyed, leaving a
  ## dangling reference from the test. Migration yields no verdict benefit.

var currentClosureCallErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 C2b. Classified closure-call failures accumulated during lowering
  ## (`ceClosureUnknownCallee`, `ceInlineBudgetExceeded`) — `lower` has no
  ## WalkCtx to push onto `w.sawUnknown`/findings, so they ride this sink and are
  ## drained into the finding's errors (and force `sxUnknown`) at the SUT
  ## boundary. Reset at `runSymexImpl` entry. (The `unknownExnWarnings` idiom.)

## NOTE: `currentWalkCtxPtr` has been moved earlier (to the R1 cluster, before
## `allocRefSort`) so pre-WalkCtx procs can test the nil-guard. See new location.

proc lowerClosureCall(env: Env, e: IRExpr): SymVal
  ## Phase 15 C2b fwd-decl. Defined AFTER `walk` (it descends the lambda body
  ## via `walk`), called from `lower(iekClosureCall)` (defined before `walk`).

proc lowerSeqLit(env: Env, e: IRExpr): SymVal
  ## Phase 15 C4 fwd-decl. Concrete seq-literal `@[..]` → concrete-length svSeq.

proc lowerTupleLit(env: Env, e: IRExpr): SymVal
  ## RFC-chapulin-hardening P1 fwd-decl. General N-ary tuple constructor
  ## `(a, b, c)` → svTuple, one lowered SymVal per field.

proc lowerVariantLit(env: Env, e: IRExpr): SymVal
  ## Round-6 A1 fwd-decl (ADR-0029). Literal-discriminant variant
  ## constructor → svVariant, disc pinned to the literal tag.

proc lowerHofCall(env: Env, e: IRExpr): SymVal
  ## Phase 15 C4 fwd-decl. Defined AFTER `walk` (the inline path applies the
  ## closure per element via the C2b descent), called from `lower(iekHofCall)`.

proc allocateSym(ty: IRType, baseName: string, pcOut: var seq[Z3Bool],
                 stringBacked: bool = false,
                 intOffsetPositions: seq[int] = @[]): SymVal   ## fwd-decl (mutual: itDistinct)
  ## `stringBacked` (round-6 B1, ADR-0028 Leg 1): true only for a
  ## TOP-LEVEL `seq[byte]` PARAM the `IRParam.isStringBacked` field marks
  ## (threaded in from `runSymexImpl`'s per-param loop). Recursive internal
  ## `allocateSym` calls (tuple fields, array elements, ...) never pass it —
  ## it is a sibling allocation hint on the parameter itself, not a
  ## recursively-propagated type property.
  ## `intOffsetPositions` (round-6 B5, ADR-0028 Leg 1, chained composition):
  ## non-empty ONLY for a call-return placeholder (`freshRetSym`) whose type
  ## is `itTuple`/`itInt` and whose SOURCE positions
  ## `calleeIntOffsetReturnPositions` (dsl_parser.nim) proved are the
  ## callee's own scan closed form's index — those positions allocate
  ## `svInt` directly (mirrors `IRParam.isIntOffset`'s TOP-LEVEL-param
  ## promotion, at the call-RETURN end instead). `0` addresses a bare
  ## (non-tuple) `itInt` allocation; for `itTuple` it indexes `ty.fields`.
  ## Every OTHER caller passes `@[]` (identity — the pre-existing default
  ## allocation, unchanged).

proc baseIsDecidable(base: IRType): bool =
  ## Phase 15 G4. The bijectivity-axiom fragment: int / BV / bool. Anything
  ## else (FP, string, and — conservatively — composite bases) is skipped.
  ## A nested distinct base is decidable iff ITS base is (recurse).
  case base.kind
  of itInt, itBool: true
  of itDistinct: baseIsDecidable(base.distinctBase)
  else: false

proc rawConstOf(ctx: Z3Context, sort: RawZ3Sort, name: string): RawZ3Ast =
  ## Fresh named const of a (possibly uninterpreted) sort.
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  ctx.checkErr Z3_mk_const(ctx.raw, sym, sort)

proc rawApp1(ctx: Z3Context, fd: RawZ3FuncDecl, arg: Z3AnyAst): Z3AnyAst =
  ## Apply a unary func-decl to one argument. Both the argument and the result
  ## are wrapped `Z3AnyAst`s (ref-counted): intermediate application results MUST
  ## be inc-ref'd, or Z3 may garbage-collect them between the nested apply calls.
  ## The args array is a HEAP-allocated seq (NOT a stack array): Z3 4.15 SIGSEGVs
  ## on stack-passed `Z3_mk_app` args (same hazard funcdecl.nim documents for
  ## rec_func_decl). `wrap` does the inc_ref.
  var args = @[arg.raw]
  let raw = ctx.checkErr Z3_mk_app(ctx.raw, fd, 1,
    cast[ptr UncheckedArray[RawZ3Ast]](addr args[0]))
  wrap[Z3AnyAst](ctx, raw)

proc isBijectivityBaseSym(sv: SymVal): bool {.inline.} =
  ## Phase 15 G4. The SymVal kinds over which the bijectivity axioms are
  ## decidable: bool, the genuine Z3Int, AND the BV families (Nim `int` and the
  ## fixed-width ints allocate as `svBV*` by default — `bvVar`). Anything else
  ## (FP, string, composite) skips bijectivity.
  sv.kind in {svBool, svInt, svBV8, svBV16, svBV32, svBV64}

proc rawAstOf(sv: SymVal): RawZ3Ast =
  ## The raw ast of a decidable-base primitive SymVal (bool / int / BV).
  case sv.kind
  of svInt:  sv.zi.raw
  of svBool: sv.bo.raw
  of svBV8:  sv.bv8.raw
  of svBV16: sv.bv16.raw
  of svBV32: sv.bv32.raw
  of svBV64: sv.bv64.raw
  else:
    raise newException(ValueError, "rawAstOf: unsupported base kind " & $sv.kind)

proc rawSortOf(sv: SymVal): RawZ3Sort =
  ## The Z3 sort underlying a decidable-base primitive SymVal. Used to declare
  ## the inject/eject domains/ranges and bind the base-side quantified variable.
  let ctx = requireCurrentContext()
  ctx.checkErr Z3_get_sort(ctx.raw, rawAstOf(sv))

proc rawAnyAstOf(sv: SymVal): RawZ3Ast =
  ## The raw ast of ANY base SymVal that may underlie a distinct type — used
  ## only to derive the base sort for the inject/eject func-decl signatures
  ## (works for FP/String bases too, where bijectivity is skipped).
  case sv.kind
  of svInt:     sv.zi.raw
  of svBool:    sv.bo.raw
  of svBV8:     sv.bv8.raw
  of svBV16:    sv.bv16.raw
  of svBV32:    sv.bv32.raw
  of svBV64:    sv.bv64.raw
  of svFloat32: sv.fp32.raw
  of svFloat64: sv.fp64.raw
  of svString:  sv.str.raw
  of svDistinct: sv.distinctAst.raw   ## nested distinct base
  of svRef:     sv.refAst.raw         ## Phase 15 R9: ref-typed heap field value
  of svPtr:     sv.ptrAst.raw         ## Phase 15 R9: ptr-typed heap field value
  else:
    raise newException(ValueError,
      "rawAnyAstOf: unsupported distinct base kind " & $sv.kind)

proc sortOfTuple*(sv: SymVal): seq[RawZ3Sort] =
  ## Phase 15 Cluster C (C1, ADR-0009 D5). Derive the FLATTENED sequence of
  ## per-leaf Z3 sorts of an `svTuple` env at walk time. Because the closure
  ## environment is a Nim-side `svTuple` (NOT a Z3 record sort — there is no Z3
  ## aggregate sort anywhere in this engine, ADR-0009 D2), the closure's
  ## `funcSym` domain is the CONCATENATION of these per-leaf sorts ++ the
  ## parameter sorts. Nested tuples flatten recursively; each scalar leaf
  ## contributes one sort via `Z3_get_sort`. Consumed by the C2b application
  ## path (raw `Z3_mk_func_decl` / `Z3_mk_app`, D4). Non-tuple input is treated
  ## as a single leaf (the degenerate one-element env).
  let ctx = requireCurrentContext()
  case sv.kind
  of svTuple:
    for f in sv.fields:
      for s in sortOfTuple(f): result.add s
  else:
    result.add ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(sv))

proc c1ClosurePoCApply*(): bool =
  ## Phase 15 Cluster C (C1) PoC fixture (Feas-H2 / ADR-0009 D4). Validate the
  ## raw `Z3_mk_app` application path over RUNTIME-constructed sorts BEFORE C2b
  ## wires it into the full closure-call descent. Builds a two-leaf `svTuple`
  ## env (an int leaf + a bool leaf), derives its flattened domain sorts via
  ## `sortOfTuple`, declares an uninterpreted `Z3_mk_func_decl` over
  ## `(domain..., int param) -> int`, and applies it via `Z3_mk_app` with
  ## HEAP-seq args (the G4 raw-FFI discipline — stack args SIGSEGV in Z3 4.15).
  ## Returns true iff Z3 accepts the application (the result is a well-sorted
  ## int ast) without a sort-mismatch error. This de-risks C2b's funcSym apply.
  let ctx = newContext()
  setCurrentContext(ctx)
  # 1. A representative env: svTuple{ int, bool } (two captured leaves).
  let envLeafInt  = SymVal(kind: svBV64, bv64: mkBitVec[64](7'i64), signed: true)
  let envLeafBool = SymVal(kind: svBool, bo: mkBool(true))
  let env = SymVal(kind: svTuple, fields: @[envLeafInt, envLeafBool],
                   fieldNames: @["a", "b"])
  # 2. Flattened domain sorts of the env (D5) ++ one int param sort.
  var domain = sortOfTuple(env)
  let paramLeaf = SymVal(kind: svBV64, bv64: mkBitVec[64](3'i64), signed: true)
  let paramSort = ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(paramLeaf))
  domain.add paramSort
  let rangeSort = paramSort   ## funcSym returns an int
  # 3. Declare the uninterpreted funcSym over the runtime-known sorts (D4).
  let fsym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, "C1_poc_funcSym".cstring)
  let fd = ctx.checkErr Z3_mk_func_decl(ctx.raw, fsym, cuint(domain.len),
    cast[ptr UncheckedArray[RawZ3Sort]](addr domain[0]), rangeSort)
  incRefFD(ctx, fd)
  # 4. Apply via raw Z3_mk_app with HEAP-seq args (G4 discipline). Args are the
  #    flattened env leaves ++ the param leaf, all as raw asts.
  var args = @[rawAnyAstOf(envLeafInt), rawAnyAstOf(envLeafBool),
               rawAnyAstOf(paramLeaf)]
  let appRaw = ctx.checkErr Z3_mk_app(ctx.raw, fd, cuint(args.len),
    cast[ptr UncheckedArray[RawZ3Ast]](addr args[0]))
  let appAst = wrap[Z3AnyAst](ctx, appRaw)
  # 5. Round-trip: the application's sort must match the declared range sort.
  let appSort = ctx.checkErr Z3_get_sort(ctx.raw, appAst.raw)
  result = appSort == rangeSort

# ---- Phase 15 Cluster C (C2a): closure CONSTRUCTION --------------------------

proc allocDistinctSym(ty: IRType, baseName: string,
                      pcOut: var seq[Z3Bool]): SymVal =
  ## Phase 15 G4 (ADR-0008 D4). Allocate a `distinct T` SymVal: a fresh const of
  ## the "DistinctName" uninterpreted sort plus its ejected base. The sort,
  ## inject/eject func-decls, and (decidable-base) bijectivity axioms are
  ## created AT MOST ONCE per (name, run) — guarded by the `currentDistinctSorts`
  ## cache. The base SymVal is bound to `eject(distinctConst)` so the witness
  ## eject-chain (and explicit conversions) resolve to a concrete base value.
  let ctx = requireCurrentContext()
  let name = ty.distinctName
  # 1. Allocate (or reuse) the distinct sort + inject/eject func-decls + axioms.
  if not currentDistinctSorts.hasKey(name):
    let sort = mkUninterpretedSort(ctx, name)        # ADR D4: fresh sort
    # Pin the uninterpreted sort with a Z3 ref: without it, the heavy ast
    # allocation that follows (baseRep + func-decls + axioms) lets Z3
    # garbage-collect the un-referenced sort, corrupting every func-decl whose
    # domain/range names it (an earlier SIGSEGV: the sort read back as
    # Z3_UNKNOWN_SORT). The ref is held for the whole run (never dec'd — the
    # context is torn down at run end).
    Z3_inc_ref(ctx.raw, Z3_sort_to_ast(ctx.raw, sort.raw))
    distinctSortNames.add name
    # Declare inject_T / eject_T over the BASE sort. We need a representative
    # base SymVal to read its Z3 sort; allocate a throwaway (its init
    # constraints are discarded — the func-decls only need the sort).
    var scratchPC: seq[Z3Bool]
    let baseRep = allocateSym(ty.distinctBase, name & ".__baseSort", scratchPC)
    if baseIsDecidable(ty.distinctBase) and isBijectivityBaseSym(baseRep):
      let baseSort = rawSortOf(baseRep)
      var injDom = @[baseSort]
      let injSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
        ("inject_" & name).cstring)
      let inject = ctx.checkErr Z3_mk_func_decl(ctx.raw, injSym, 1,
        cast[ptr UncheckedArray[RawZ3Sort]](addr injDom[0]), sort.raw)
      var ejDom = @[sort.raw]
      let ejSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
        ("eject_" & name).cstring)
      let eject = ctx.checkErr Z3_mk_func_decl(ctx.raw, ejSym, 1,
        cast[ptr UncheckedArray[RawZ3Sort]](addr ejDom[0]), baseSort)
      incRefFD(ctx, inject)   # keep the decls alive for the run's lifetime
      incRefFD(ctx, eject)
      let dentry = DistinctSortEntry(sort: sort, inject: inject, eject: eject)
      currentDistinctSorts[name] = dentry
      # CR-9 Stage 4: also populate WalkerStatics when a walk is active so
      # the live WalkerStatics is the authoritative source and the post-walk
      # mirror loop for distinctSorts becomes redundant.
      syncDistinctSortEntry(name, dentry)
      # Decidable base: the round-trip is realised as a GROUND `eject(dConst)
      # == baseSym` pin per occurrence (asserted below in step 3), NOT as a
      # universal quantifier (which HANGS — see step 3's note). No skip hint.
    else:
      # FP / String / composite base → bijectivity SKIPPED (hang risk). Still
      # declare inject/eject so explicit conversions have func-decls, but assert
      # NO quantified axioms. Emit the classified sevHint (Invariant 3).
      let baseSort = ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(baseRep))
      var injDom = @[baseSort]
      let injSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
        ("inject_" & name).cstring)
      let inject = ctx.checkErr Z3_mk_func_decl(ctx.raw, injSym, 1,
        cast[ptr UncheckedArray[RawZ3Sort]](addr injDom[0]), sort.raw)
      var ejDom = @[sort.raw]
      let ejSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
        ("eject_" & name).cstring)
      let eject = ctx.checkErr Z3_mk_func_decl(ctx.raw, ejSym, 1,
        cast[ptr UncheckedArray[RawZ3Sort]](addr ejDom[0]), baseSort)
      incRefFD(ctx, inject)
      incRefFD(ctx, eject)
      let dentry = DistinctSortEntry(sort: sort, inject: inject, eject: eject)
      currentDistinctSorts[name] = dentry
      # CR-9 Stage 4: also populate WalkerStatics when a walk is active.
      syncDistinctSortEntry(name, dentry)
      let bijHint = SymexErrorInfo(
        kind: geDistinctBijectivitySkipped, severity: sevHint,
        msg: "bijectivity axiom skipped for distinct `" & name &
             "` over non-decidable base " & $ty.distinctBase.kind &
             " (FP/String): the distinct sort is modeled without the " &
             "inject/eject round-trip guarantee")
      distinctBijectivityHints.add bijHint      # threadvar: fallback
      syncDistinctBijectivityHint(bijHint)      # CR-9 Stage 5: also WalkCtx
  let entry = currentDistinctSorts[name]
  # 2. A fresh const of the distinct sort for THIS occurrence.
  let dAny = wrap[Z3AnyAst](ctx, rawConstOf(ctx, entry.sort.raw, baseName))
  # 3. The ejected base SymVal: a base allocated normally (gives a witness leaf
  #    + base init constraints) and PINNED equal to eject(dConst), so the
  #    witness reads the real round-tripped base value.
  let baseSym = allocateSym(ty.distinctBase, baseName, pcOut)
  if isBijectivityBaseSym(baseSym):
    # ---- GROUND per-occurrence eject pin (decidable base; NO HANG) ---------
    # The round-trip guarantee is realised as a GROUND equality over THIS
    # occurrence's consts, NOT a universal quantifier:
    #   eject(dConst) == baseSym
    # `baseSym` is a fresh base var (carrying the witness leaf + base init
    # constraints), `dConst` an opaque const of the fresh distinct sort. This
    # makes `eject` a concrete total function at this value while the distinct
    # const stays walled off from the base sort (the type wall). Two distinct
    # occurrences whose eject-bases are equal share a base value but remain
    # distinct consts — exactly Nim's `distinct` semantics.
    #
    # We deliberately do NOT assert the REVERSE ground pin `inject(baseSym) ==
    # dConst`, nor a UNIVERSAL `∀x. eject(inject(x))==x`: empirically (verified
    # under the bounded runner) BOTH make Z3 NON-TERMINATE on the
    # uninterpreted-function-over-BV combination — a hard HANG (the universal
    # form even untriggered; the reverse ground inject-app likewise). Per the
    # HARD "never ship a hang" rule, the eject pin alone is the decidable
    # model, and it is sufficient for the DoD (target reachable, witness via
    # eject, type wall preserved, int base decidable sxSat/sxUnsat). Inject is
    # still DECLARED so an explicit `Distinct(baseVal)` construction has a
    # func-decl to reference, but it is never APPLIED at allocation time.
    let ejD = rawApp1(ctx, entry.eject, dAny)
    pcOut.add wrap[Z3Bool](ctx,
      ctx.checkErr Z3_mk_eq(ctx.raw, ejD.raw, rawAstOf(baseSym)))
  let boxed = new(SymVal)
  boxed[] = baseSym
  SymVal(kind: svDistinct, distinctAst: dAny, distinctName: name,
         distinctBaseSym: boxed)

proc variantDiscEq(d: SymVal, tagOrd: int64): Z3Bool =
  ## `disc == tagOrd` over a variant discriminator's SymVal, whatever BV
  ## width (or `svInt`/`svBool` fallback) it was allocated at. Round-6 A2
  ## (ADR-0029) extraction: this file previously carried the identical
  ## closure as three separate copies — `allocateSym`'s `itVariant` arm
  ## (arm-disjunction), `isVariantField`'s walker arm (in-arm guard), and
  ## `retBindEq`'s `svVariant` arm (per-arm implication guard) — collapsed
  ## here so a future 4th site does not become a 4th copy.
  case d.kind
  of svBV8:  d.bv8  == mkBitVec[8](tagOrd)
  of svBV16: d.bv16 == mkBitVec[16](tagOrd)
  of svBV32: d.bv32 == mkBitVec[32](tagOrd)
  of svBV64: d.bv64 == mkBitVec[64](tagOrd)
  of svInt:  d.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
  of svBool: d.bo   == mkBool(tagOrd != 0)  ## Phase 15 F9c: bool disc
  else:
    raise newException(ValueError,
      "variantDiscEq: discriminator must be a BV or Z3Int kind (got " &
      $d.kind & ")")

proc allocateSym(ty: IRType, baseName: string, pcOut: var seq[Z3Bool],
                 stringBacked: bool = false,
                 intOffsetPositions: seq[int] = @[]): SymVal =
  ## Recursively allocate a SymVal for `ty`. Init-side constraints
  ## (like `seqLen ≥ 0`) accumulate into `pcOut`.
  case ty.kind
  of itUninterp:
    # Phase 15 R1a (ADR-0010, Breadth-LOW-L4): classifyType maps `owned T` /
    # `WeakRef[T]` / `Atomic[T]` to an `__ownership:*` placeholder. Allocating
    # one raises the classified ownership halt (caught at the runSymex boundary
    # → heUnsupportedOwnership → sxUnknown, Invariant 3).
    if ty.uninterpName.startsWith("__ownership:"):
      raise (ref SymexOwnershipUnsupportedError)(
        msg: "ownership wrapper `" & ty.uninterpName.substr(len("__ownership:")) &
             "` is out of scope for the ref cluster (Breadth-LOW-L4)")
    # RFC-chapulin-hardening CR-2b (Cluster 2 — Crash-totality, round-2
    # Option 2): `classifyType`'s parameter-type catch-all
    # (`dsl_typebridge.nim`) maps an unsupported PARAMETER type to an
    # `__unsupported:*` placeholder rather than aborting compilation. Reached
    # here at PARAMETER-ALLOCATION time — before the proc body is walked —
    # so raising forces a WHOLE-RUN degrade. Reuses CR-1c's generic
    # `SymexClassifiedDegradeError` carrier (deliberately, per the RFC: no
    # 20th near-identical dedicated exception type) with the distinct
    # `feUnsupportedParamType` kind; caught at the `runSymex` boundary ->
    # `sxUnknown` (Invariant 3 — never a crash, never a silent UNSAT).
    if ty.uninterpName.startsWith("__unsupported:"):
      raise (ref SymexClassifiedDegradeError)(
        kind: feUnsupportedParamType,
        msg: "unsupported parameter type `" &
             ty.uninterpName.substr(len("__unsupported:")) &
             "`; the supported fragment is {bool, int, int{8,16,32,64}, " &
             "uint, uint{8,16,32,64}, range[..], Natural, Positive, float, " &
             "float{32,64}, string, char, byte}")
    # RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality). Mirrors the
    # `__unsupported:` branch above, but for the WITNESS-READER codegen
    # catch-all: `parseProc*`'s TOP-LEVEL SUT parameter-classification loop
    # (`dsl_parser.nim`) runs each parameter's `classifyType` result through
    # `demoteUnrenderableWitnessTy`, which maps an unrenderable seq/Table/
    # HashSet element/key/value shape (per the shared
    # `isRenderable{Seq,Table,Set}*` predicates, `smt/types.nim`) to this
    # `__unsupported_witness:*` placeholder rather than a real
    # `itSeq`/`itTable`/`itSet`. Deliberately NOT inside `classifyType`
    # itself — that classifier also runs on purely-internal (non-witness)
    # types (e.g. an in-body helper's `seq[byte]` return type), which must
    # keep their ordinary `itSeq`/`itTable`/`itSet` classification. So
    # `emitTyAndReader`'s three seq/Table/HashSet `error()` sites
    # (`symex.nim`) never see one of these shapes for a TOP-LEVEL parameter;
    # the degrade fires HERE, at parameter-allocation time, before the body
    # is walked and before witness codegen is ever reached. Kept DISTINCT
    # from `feUnsupportedParamType`: a different macro (post-solve
    # witness-reader codegen, not param-type classify), different call
    # site, per §0's three-classes framing.
    if ty.uninterpName.startsWith("__unsupported_witness:"):
      raise (ref SymexClassifiedDegradeError)(
        kind: feUnsupportedWitnessType,
        msg: "unsupported witness shape `" &
             ty.uninterpName.substr(len("__unsupported_witness:")) &
             "`; the supported fragment is {seq[int64], seq[float64], " &
             "seq[float32], seq[ref T], Table[string, int64], " &
             "HashSet[int64]} plus scalar/tuple/array/object element or " &
             "value types therein")
    raise newException(ValueError,
      "allocateSym(itUninterp): uninterpreted-ref allocation lands with cluster E")
  of itRef, itPtr:
    # Phase 15 R1 (ADR-0010). Allocate (or reuse) the per-walker `Ref_<typeId>`
    # uninterpreted sort for the pointee, then build a FRESH `Ref_T`-sorted
    # const for this param — the abstract address `p`. No heap read happens
    # here: the per-path heap array is materialised lazily on the first
    # `isDeref` (the walker arm), where the GROUND `select(heap, p)` lands.
    let ctx = requireCurrentContext()
    let pointee = if ty.kind == itRef: ty.refPointeeTy else: ty.ptrPointeeTy
    let refSort = allocRefSort(ctx, pointee)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, baseName.cstring)
    let refRaw = ctx.checkErr Z3_mk_const(ctx.raw, sym, refSort)
    let refAny = wrap[Z3AnyAst](ctx, refRaw)
    if ty.kind == itRef:
      SymVal(kind: svRef, refAst: refAny, refPointee: pointee)
    else:
      SymVal(kind: svPtr, ptrAst: refAny, ptrFamily: true, ptrPointee: pointee)
  of itFloat32: SymVal(kind: svFloat32, fp32: mkFloat32Var(baseName))
  of itFloat64: SymVal(kind: svFloat64, fp64: mkFloat64Var(baseName))
  of itDistinct:   ## Phase 15 G4 (ADR-0008 D4): fresh uninterpreted sort.
    allocDistinctSym(ty, baseName, pcOut)
  of itVariant:
    # Phase 11 cycle 3 — allocate the discriminator and every arm's
    # per-arm field symbols. Constrain the discriminator to the
    # disjunction of legal arm ordinals so Z3 never picks an out-
    # of-range tag.
    let discInner = allocateSym(ty.vDiscTy,
                                 baseName & "." & ty.vDiscName, pcOut)
    let discBoxed = new(SymVal)
    discBoxed[] = discInner
    # Plain fields: allocated ONCE; shared across every arm. Their
    # witness paths are `<baseName>.<plainFieldName>` (no @tag).
    var plainFields: seq[SymVal]
    for i, ft in ty.vPlainFieldTypes:
      let path = baseName & "." & ty.vPlainFieldNames[i]
      plainFields.add allocateSym(ft, path, pcOut)
    var armFields = initOrderedTable[int, seq[SymVal]]()
    var armNames  = initOrderedTable[int, seq[string]]()
    var armEqClauses: seq[Z3Bool]
    var hasElse = false
    for arm in ty.vArms:
      var fields: seq[SymVal]
      for j, ft in arm.fieldTypes:
        let path = baseName & ".@" & arm.tagName & "." & arm.fieldNames[j]
        fields.add allocateSym(ft, path, pcOut)
      armFields[arm.tagOrdinal] = fields
      armNames[arm.tagOrdinal]  = arm.fieldNames
      # Phase 14 cycle A2: else arm contributes NO direct equality
      # disjunct (its membership constraint is the conjunction of
      # negations against the non-else arms — emitted lazily at
      # `isVariantField` lowering time). The else arm's coverage is
      # instead supplied by the dord-fanout below.
      if arm.isElse:
        hasElse = true
        continue
      armEqClauses.add variantDiscEq(discInner, int64(arm.tagOrdinal))
    # Phase 14 cycle A2: when an else arm is present, expand the
    # disjunction to cover ALL disc-enum ordinals (not just the
    # non-else arms') so Z3 can pick any legal disc value, including
    # those covered ONLY by the else arm. Without an else arm, the
    # per-arm disjunction is exhaustive by Nim's variant validity
    # rules and no expansion is needed.
    if hasElse:
      for dt in ty.vDiscTags:
        # Skip ordinals already covered by a non-else arm — they're
        # in armEqClauses already.
        var inNonElse = false
        for arm in ty.vArms:
          if (not arm.isElse) and arm.tagOrdinal == dt.ord:
            inNonElse = true; break
        if inNonElse: continue
        armEqClauses.add variantDiscEq(discInner, int64(dt.ord))
    if armEqClauses.len > 0:
      var clause = armEqClauses[0]
      for k in 1 ..< armEqClauses.len:
        clause = clause or armEqClauses[k]
      pcOut.add clause
    SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: ty.vDiscName,
           vObjectName: ty.vObjectName,
           vArmFields: armFields, vArmFieldNames: armNames,
           vPlainFields: plainFields,
           vPlainFieldNames: ty.vPlainFieldNames)
  of itMultiVariant:
    # Phase 14 cycle A1c per ADR-0003 D1. Each axis is allocated
    # independently: its discriminator gets a fresh BV symbol and
    # the arm-ordinal disjunction is appended to pcOut. Per-axis
    # arm fields are allocated up front (the walker reads them
    # conditionally on the disc value). Plain fields are shared
    # across all axes — same semantics as Phase 11's plain-field
    # sharing in itVariant.
    var plainFields: seq[SymVal]
    for i, ft in ty.mvPlainFieldTypes:
      let path = baseName & "." & ty.mvPlainFieldNames[i]
      plainFields.add allocateSym(ft, path, pcOut)
    var axisSyms: seq[VariantAxisSym]
    for ax in ty.mvAxes:
      let discInner = allocateSym(ax.discTy,
                                  baseName & "." & ax.discName, pcOut)
      let discBoxed = new(SymVal)
      discBoxed[] = discInner
      var armFields = initOrderedTable[int, seq[SymVal]]()
      var armNames  = initOrderedTable[int, seq[string]]()
      var armEqClauses: seq[Z3Bool]
      for arm in ax.arms:
        var fields: seq[SymVal]
        for j, ft in arm.fieldTypes:
          let path = baseName & "." & ax.discName &
                     ".@" & arm.tagName & "." & arm.fieldNames[j]
          fields.add allocateSym(ft, path, pcOut)
        armFields[arm.tagOrdinal] = fields
        armNames[arm.tagOrdinal]  = arm.fieldNames
        let tagOrd = int64(arm.tagOrdinal)
        let eqBool =
          case discInner.kind
          of svBV8:  discInner.bv8  == mkBitVec[8](tagOrd)
          of svBV16: discInner.bv16 == mkBitVec[16](tagOrd)
          of svBV32: discInner.bv32 == mkBitVec[32](tagOrd)
          of svBV64: discInner.bv64 == mkBitVec[64](tagOrd)
          else:
            raise newException(ValueError,
              "symex Phase 14: multi-variant axis disc must be a BV kind " &
              "(got " & $discInner.kind & ")")
        armEqClauses.add eqBool
      if armEqClauses.len > 0:
        var clause = armEqClauses[0]
        for k in 1 ..< armEqClauses.len:
          clause = clause or armEqClauses[k]
        pcOut.add clause
      axisSyms.add VariantAxisSym(
        discName: ax.discName, disc: discBoxed,
        armFields: armFields, armFieldNames: armNames)
    SymVal(kind: svMultiVariant, mvObjectName: ty.mvObjectName,
           mvAxes: axisSyms,
           mvPlainFields: plainFields,
           mvPlainFieldNames: ty.mvPlainFieldNames)
  of itInt:
    # Round-6 B5 (ADR-0028 Leg 1, chained composition): position 0 marks a
    # bare (non-tuple) scan-offset return — allocate svInt directly rather
    # than the type-driven BV default, mirroring `IRParam.isIntOffset`'s
    # top-level-param promotion at the call-RETURN end.
    if 0 in intOffsetPositions:
      SymVal(kind: svInt, zi: mkIntVar(baseName))
    else:
      bvVar(ty, baseName)
  of itBool:
    SymVal(kind: svBool, bo: mkBoolVar(baseName))
  of itString:
    # Phase 15 S3: byte-faithful ≤0xFF char-range constraint (ADR-0006). This is
    # the soundness mechanism: without it Z3 may pick full-Unicode codepoints
    # (0..0x2FFFF) that occupy one Z3 position but multiple Nim bytes, so a
    # witness extracted via `evalStrBytes` would not round-trip to a Nim string of
    # the same length/content. We assert that the free string is a member of
    # `(re.range '\x00' '\xff')*` — every character is a single Latin-1 byte — so
    # Z3 position == Nim byte index. This is threaded into the path condition via
    # `pcOut`, exactly like `seqLen >= 0` and the table/set size floors above.
    # mkString("\x00")/("\xff") are single-byte lstring endpoints; range() builds
    # the char-class regex, star() the Kleene closure, matches() the membership.
    let sv = mkStringVar(baseName)
    let byteRange = star(range(mkString("\x00"), mkString("\xff")))
    pcOut.add matches(sv, byteRange)
    SymVal(kind: svString, str: sv)
  of itTuple:
    var fields: seq[SymVal]
    for i, ft in ty.fields:
      let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                   else: "." & $i
      # Round-6 B5: a traced position allocates svInt directly (only
      # meaningful for an itInt field — any other field kind at a traced
      # position is simply not a scan-offset shape, so it falls through to
      # the ordinary recursive allocation unchanged).
      if i in intOffsetPositions and ft.kind == itInt:
        fields.add SymVal(kind: svInt, zi: mkIntVar(baseName & suffix))
      else:
        fields.add allocateSym(ft, baseName & suffix, pcOut)
    SymVal(kind: svTuple, fields: fields, fieldNames: ty.fieldNames)
  of itArray:
    # #142: nested arrays land via the existing recursion. The
    # previous guard was overly cautious — allocateSym recurses
    # naturally through the element type.
    var elems: seq[SymVal]
    for i in 0 ..< ty.size:
      elems.add allocateSym(ty.elemTy, baseName & "." & $i, pcOut)
    SymVal(kind: svArray, arrElems: elems, arrElemTy: ty.elemTy)
  of itSeq:
    if ty.seqUnsupportedFieldReason.len > 0:
      # Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution
      # 2026-08-15): a declared field whose element kind
      # `allocateSeqDataRaw` cannot back (e.g. `seq[(string,string)]`).
      # Force `seqLen == 0` and build an INERT placeholder data array —
      # never selected from (nothing indexes a length-0 seq) — instead of
      # calling `allocateSeqDataRaw(ty.seqElemTy, ...)` (which would raise
      # `SymexNestedSeqUnsupportedError` unconditionally, reintroducing
      # Bug #2's whole-run poison the moment this FIELD is merely
      # allocated, regardless of whether any path reads it). The element
      # SORT here is arbitrary/fixed (`Z3Int -> Z3Bool`) — never the real
      # `ty.seqElemTy` — because it structurally can never be selected
      # from; every SUT-level READ of this field is intercepted at PARSE
      # time (`dsl_parser.nim`'s `nnkDotExpr` arm) before any real walker
      # access of this SymVal is ever built. `isUnsupportedFieldPlaceholder:
      # true` lets `retBindEq` (below) and witness extraction
      # (`extractFromSymVal`) recognize and special-case this value.
      let lenSym = mkIntVar(baseName & ".len")
      pcOut.add (lenSym == mkInt(0))
      let dataRaw = toAnyAst(mkArrayVar[Z3Int, Z3Bool](baseName & ".data"))
      SymVal(kind: svSeq, seqLen: lenSym, seqDataRaw: dataRaw,
             seqElemTy: ty.seqElemTy, isUnsupportedFieldPlaceholder: true)
    elif stringBacked:
      # Round-6 B1 (ADR-0028 Leg 1): a `seq[byte]` param the B1a scan-shape
      # predicate recognized — allocate via the SAME itString machinery as
      # the `of itString:` arm above (ADR-0006 byte-range constraint),
      # PLUS the itSeq arm's own `[0,1024]` length ceiling (the
      # witness-extraction safety bound this representation swap must not
      # silently drop — the plain `of itString:` arm above carries no such
      # cap, so it is added here explicitly rather than by widening that
      # arm's unrelated behavior).
      let sv = mkStringVar(baseName)
      let byteRange = star(range(mkString("\x00"), mkString("\xff")))
      pcOut.add matches(sv, byteRange)
      pcOut.add (len(sv) <= mkInt(1024))
      SymVal(kind: svString, str: sv)
    else:
      let lenSym = mkIntVar(baseName & ".len")
      # Sanity floor + ceiling so the model returns Nim-representable
      # lengths. The ceiling of 1024 is chosen so that any reasonable
      # path-condition is still satisfiable while Z3 doesn't pick
      # values that overflow `cint` during witness extraction.
      pcOut.add (lenSym >= mkInt(0))
      pcOut.add (lenSym <= mkInt(1024))
      let dataRaw = allocateSeqDataRaw(ty.seqElemTy, baseName & ".data")
      SymVal(kind: svSeq, seqLen: lenSym,
             seqDataRaw: dataRaw, seqElemTy: ty.seqElemTy)
  of itTable:
    # Phase 5 cycle 5 narrow scope: Table[string, int]. Other (K, V)
    # pairs land incrementally — the wrap[Z3Array[K, V]] machinery
    # supports them with a per-pair dispatch.
    if ty.tabKeyTy.kind != itString:
      raise newException(ValueError,
        "Phase 5 cycle 5: only Table[string, V] supported (got key=" &
        $ty.tabKeyTy & ")")
    case ty.tabValTy.kind
    of itInt:
      doAssert ty.tabValTy.width == 64 and ty.tabValTy.signed,
        "Phase 5 cycle 5: only Table[string, int] supported"
      let dataAst = toAnyAst(
        mkArrayVar[Z3String, Z3BitVec[64]](baseName & ".data"))
      let presentAst = toAnyAst(
        mkArrayVar[Z3String, Z3Bool](baseName & ".present"))
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym >= mkInt(0))
      pcOut.add (sizeSym <= mkInt(1024))   ## same ceiling as seqs
      SymVal(kind: svTable, tabDataRaw: dataAst,
             tabPresentRaw: presentAst, tabSize: sizeSym,
             tabKeyTy: ty.tabKeyTy, tabValTy: ty.tabValTy)
    else:
      raise (ref SymexUnsupportedTableValTypeError)(
        msg: "Table value type not modeled: " & $ty.tabValTy &
             " — only Table[string, int] is supported (seUnsupportedTableValType)")
  of itSet:
    if ty.setElemTy.kind == itInt and ty.setElemTy.width == 64:
      let memAst = toAnyAst(
        mkArrayVar[Z3BitVec[64], Z3Bool](baseName & ".members"))
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym >= mkInt(0))
      pcOut.add (sizeSym <= mkInt(1024))
      SymVal(kind: svSet, setMembersRaw: memAst,
             setSize: sizeSym, setElemTy: ty.setElemTy)
    else:
      raise (ref SymexUnsupportedSetCharInteropError)(
        msg: "HashSet element type not modeled: " & $ty.setElemTy &
             " — only HashSet[int] (BV[64]) is supported (seUnsupportedSetCharInterop)")

# Phase 15 R1: logical-heap array helpers (heapValueSort, mkHeapArrayVar,
# liftHeapValue, heapSelect, fieldHeapKey) moved to runtime_heap.nim
# (CR-7-deeper Stage 8+). Bodies of refPointeeTypeId/allocRefSort/freshRef/
# assertFreshness/pcImpliesNonNil also moved there.

proc tyOf(sv: SymVal): IRType =
  case sv.kind
  of svUninterpRef: tUninterp(sv.sortName)
  of svFloat32: tFloat32()
  of svFloat64: tFloat64()
  of svDistinct: tDistinct(sv.distinctName, tyOf(sv.distinctBaseSym[]))  ## G4
  of svClosure:
    # Phase 15 C1 STUB. There is no `itClosure` IRType in Cluster C (the IR for a
    # closure is the `iekLambda` EXPRESSION, not a new type). `tyOf` on an
    # svClosure is diagnostics-only and never reached in C1 (the walker stubs
    # before any svClosure is built); return the env's type as a placeholder.
    if sv.closureEnv != nil: tyOf(sv.closureEnv[]) else: tBool()
  of svRef:
    # Phase 15 R1. The pointee type is carried on the svRef (`refPointee`).
    if sv.refPointee != nil: tRef(sv.refPointee) else: tRef(tBool())
  of svPtr:
    if sv.ptrPointee != nil: tPtr(sv.ptrPointee) else: tPtr(tBool())
  of svBV8:  tInt(8,  sv.signed)
  of svBV16: tInt(16, sv.signed)
  of svBV32: tInt(32, sv.signed)
  of svBV64: tInt(64, sv.signed)
  of svInt:  tInt(64, true)
  of svBool: tBool()
  of svTuple:
    var ftys: seq[IRType]
    for f in sv.fields: ftys.add tyOf(f)
    tTuple(ftys, sv.fieldNames)
  of svArray:
    tArray(sv.arrElemTy, sv.arrElems.len)
  of svString:
    tString()
  of svSeq:
    tSeq(sv.seqElemTy)
  of svTable:
    tTable(sv.tabKeyTy, sv.tabValTy)
  of svSet:
    tSet(sv.setElemTy)
  of svVariant:
    # Reconstruct the IRType from the live SymVal. Used only for
    # diagnostics; cycle 7's witness emitter consults the SUT's
    # macro-time IR directly.
    var arms: seq[VariantArm]
    for tagOrdinal, fields in sv.vArmFields.pairs:
      var tys: seq[IRType]
      for f in fields: tys.add tyOf(f)
      arms.add VariantArm(tagOrdinal: tagOrdinal,
                          tagName: "",  # not preserved on the SymVal
                          fieldNames: sv.vArmFieldNames[tagOrdinal],
                          fieldTypes: tys)
    tVariant(sv.vObjectName, sv.vDiscName, tyOf(sv.vDisc[]), arms)
  of svMultiVariant:
    # Phase 14 cycle A1c. Diagnostics-only: rebuild the IRType from
    # the SymVal's axes. Tag names are not preserved on the SymVal
    # (same gap as svVariant).
    var axes: seq[VariantAxis]
    for ax in sv.mvAxes:
      var arms: seq[VariantArm]
      for tagOrdinal, fields in ax.armFields.pairs:
        var tys: seq[IRType]
        for f in fields: tys.add tyOf(f)
        arms.add VariantArm(tagOrdinal: tagOrdinal, tagName: "",
                            fieldNames: ax.armFieldNames[tagOrdinal],
                            fieldTypes: tys)
      axes.add VariantAxis(discName: ax.discName,
                           discTy: tyOf(ax.disc[]), arms: arms)
    mkMultiVariant(sv.mvObjectName, axes)

# ---- Prototype probe over the IR --------------------------------------------
#
# Each non-trivial subexpression takes its representation (Z3 BV[W] vs
# Z3Int) from a "prototype" SymVal — the first env-resident variable
# its subtree reaches. Literals coerce to match the prototype; arith
# / comparison ops dispatch on the prototype kind.
#
# When no env-resident var is reachable (e.g. `5 + 6`), no prototype
# exists and the caller defaults to BV[64] signed.

proc probeProto(env: Env, e: IRExpr): Option[SymVal] =
  if e == nil: return none(SymVal)
  case e.kind
  of iekVar:
    if env.hasKey(e.vname): some(env[e.vname]) else: none(SymVal)
  of iekBinop:
    let l = probeProto(env, e.lhs)
    if l.isSome: l else: probeProto(env, e.rhs)
  of iekUnop:
    probeProto(env, e.operand)
  of iekField:
    let inner = probeProto(env, e.obj)
    if inner.isSome and inner.get.kind == svTuple:
      some(inner.get.fields[e.fieldIx])
    else: none(SymVal)
  of iekIndex:
    # For Phase 4: probe propagation through array index is not
    # straightforward without lowering the array. The caller will
    # resolve at the iekIndex lowering site.
    none(SymVal)
  of iekArrayLit:
    for c in e.lelems:
      let p = probeProto(env, c)
      if p.isSome: return p
    none(SymVal)
  of iekTupleLit:
    # RFC-chapulin-hardening P1. A tuple literal's own SymVal kind is always
    # `svTuple` — no scalar surrounding op takes ITS representation from a
    # sub-element's proto the way an array literal's homogeneous elemTy does.
    none(SymVal)
  of iekVariantLit:
    # Round-6 A1. Same reasoning as iekTupleLit: a variant literal's own
    # SymVal kind is always `svVariant` — no scalar proto to offer.
    none(SymVal)
  of iekSeqAdd, iekSeqDel, iekSeqInsert, iekSeqPop,
     iekTableSet, iekTableDel, iekSetIncl, iekSetExcl:
    # Mutation expressions produce container SymVals; arithmetic
    # surrounding them is rare. Don't return a proto.
    none(SymVal)
  of iekSeqLen:
    # `s.len` produces a Z3Int. Return an svInt sentinel so the
    # surrounding op (comparison, arithmetic) lowers literals at the
    # right representation.
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekSeqSlice:
    # v67: a slice VALUE is a seq — no scalar prototype to offer.
    none(SymVal)
  of iekStrLit:
    none(SymVal)
  of iekStrLen:
    # Phase 15 S3: `s.len` → Z3Int. svInt sentinel so a surrounding comparison
    # lowers its literal at the right representation.
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekStrAt:
    # Phase 15 S3: `s[i]` → a Nim `char` == svBV8 (unsigned). Proto so a
    # `s[i] == 'c'` literal lowers as a BV8.
    some(SymVal(kind: svBV8, signed: false, bv8: mkBitVec[8](0)))
  of iekStrSubstr:
    # Phase 15 S3: `s[a..b]` → Z3String. svString sentinel so `s[a..b] == "lit"`
    # lowers the literal as a string and dispatches through cmpString.
    some(SymVal(kind: svString, str: mkString("")))
  of iekStrContains, iekStrStartsWith, iekStrEndsWith, iekStrMatch:
    # Phase 15 S4/S6b: the substring predicates and regex membership
    # (`s.match(re"…")`/`s.contains(re"…")`) produce a Z3Bool. svBool sentinel so
    # a surrounding boolean context is lowered correctly.
    some(SymVal(kind: svBool, bo: mkBool(true)))
  of iekStrFind, iekStrRfind, iekStrFindRe, iekStrToInt:
    # Phase 15 S4/S6b/S10a: `s.find(sub)` / `s.find(re"…")` / `parseInt(s)` → Z3Int.
    # RFC M3: `s.rfind(sub)` → Z3Int too (same shape, `lastIndexOf` instead of
    # `indexOf`). svInt sentinel so a surrounding comparison (e.g.
    # `s.find("bc") == 1`, `s.rfind("bc") == 1`, `parseInt(s) == 42`) lowers its
    # literal as a Z3Int. (iekStrFindRe's lower() raises a deferral; the proto
    # keeps a surrounding `>= 0` comparison's literal side well-typed.)
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekIntToStr, iekStrReplace, iekStrReplaceAll, iekStrReplaceRe, iekStrJoin, iekStrConcat,
     iekStrToLower, iekStrToUpper, iekRadixFmt, iekRuneToStr:
    # Phase 15 S5/S8/S10a: replace/replaceAll/join/concat/`$int` all produce a
    # Z3String. svString sentinel so `s.replace(...) == "lit"` / `xs.join(sep) ==
    # "lit"` / `$n == "42"` lowers its literal as a string and dispatches through
    # cmpString. (replaceAll's version-gate raise happens in lower(), not here —
    # probeProto must still return a string proto so the literal side is lowered.)
    #
    # RFC Cluster 3 M6: `toLowerAscii`/`toUpperAscii` (Phase 16 A9), `toHex`/
    # `toBin`/etc. (Phase 16 A8), and `$r` for `r: Rune` (Phase 16 A7-S2) were
    # missing from this arm and fell through to the `none` catch-all below,
    # despite all four also producing Z3Strings (runtime_strings.nim). This
    # was defensive-only: `lowerStrArm` (runtime_strings.nim) never reads its
    # `proto` parameter, so no string arm's lowering decision could ever have
    # been affected — the `bEq`/`bNe` probe-miss fallback (which lowers one
    # side for real and hands its computed kind to the other as proto)
    # already recovered the correct representation either way. Added here for
    # sentinel completeness / defense against a future proto-consuming arm.
    some(SymVal(kind: svString, str: mkString("")))
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrRfind, iekStrReplace, iekStrReplaceAll, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe, iekStrConcat,
                   iekIntToStr, iekStrToInt,
                   iekStrToLower, iekStrToUpper, iekRadixFmt, iekRuneToStr}:
    # Phase 15: string ops not modeled in this cycle have no proto. lower()
    # raises SymexUnsupportedStringOpError. (iekStrSplit and iekStrBytes (S7a)
    # produce an svSeq, consumed only via `.len`/index — never a direct `==` —
    # so they need no comparison proto here.)
    none(SymVal)
  of iekContains:
    none(SymVal)
  of iekGetCurrentExnMsg:
    # Phase 15 E8: `getCurrentExceptionMsg()` → Z3String. svString sentinel so a
    # surrounding `getCurrentExceptionMsg() == s` lowers the other operand as a
    # string and dispatches through cmpString.
    some(SymVal(kind: svString, str: mkString("")))
  of iekGetCurrentExn:
    # Phase 15 E8: `getCurrentException()` → opaque svUninterpRef; never compared
    # via a literal proto. No useful prototype.
    none(SymVal)
  of iekIntLit, iekFloatLit, iekBoolLit:
    none(SymVal)
  of iekConvIntToFloat:
    if e.convWidth == 32: some(SymVal(kind: svFloat32, fp32: mkFloat32(0'f32)))
    else: some(SymVal(kind: svFloat64, fp64: mkFloat64(0.0)))
  of iekConvFloatToInt:
    # Phase 15 F5-probeproto fix: return the SAME kind that lower() returns for
    # this node — svBV32 for convWidth==32, svBV64 otherwise — so that when
    # int(f)/int32(f) meets a literal operand, probeProto hands the literal the
    # correct proto and it is lowered to the matching BV width.  Before this fix
    # probeProto returned svInt (stale from before CR-4), causing:
    #   • ordering/equality vs literal: bv2int wrap reintroduced → F5 pathology
    #   • arithmetic vs literal: binBV doAssert `a.kind==b.kind` fired → crash
    if e.convWidth == 32:
      some(SymVal(kind: svBV32, signed: true, bv32: mkBitVec[32](0)))
    else:
      some(SymVal(kind: svBV64, signed: true, bv64: mkBitVec[64](0'i64)))
  of iekConvIntWidth:
    # Round-6 B2. MIRRORS the iekConvFloatToInt fix directly above (the exact
    # stale-proto crash precedent this defends against): return the SAME
    # kind/width/signedness `lower()` returns for this node — a BV sentinel
    # at `e.ciwTgtWidth`, signed per `e.ciwTgtSigned` — so when `uint16(b)
    # shl 8` meets a literal operand, probeProto hands the literal the
    # WIDENED proto and it lowers to the matching (target) BV width instead
    # of the pre-conversion (source) width. A stale/wrong-width proto here
    # would reproduce F5's exact pathology: `binBV`'s width-mismatch
    # `doAssert` firing, or a bv2int/int2bv wrap silently reintroducing a
    # narrower representation.
    case e.ciwTgtWidth
    of 16: some(SymVal(kind: svBV16, signed: e.ciwTgtSigned, bv16: mkBitVec[16](0)))
    of 32: some(SymVal(kind: svBV32, signed: e.ciwTgtSigned, bv32: mkBitVec[32](0)))
    else:  some(SymVal(kind: svBV64, signed: e.ciwTgtSigned, bv64: mkBitVec[64](0'i64)))
  of iekMathCall:
    # Phase 15 F6: predicates produce svBool; float ops produce a float of
    # the first arg's width; deferred ops have no proto (they raise on lower).
    # Phase 16 A5: classify → svBV64 (signed); copySign → float of first arg's width.
    if e.mathOp in ["signbit", "isNaN", "isInf", "isFinite", "isNormal"]:
      some(SymVal(kind: svBool, bo: mkBool(false)))
    elif e.mathOp == "classify":
      # classify returns a FloatClass ordinal modeled as svBV64 (signed).
      # This proto drives enum-ordinal literals (e.g. fcNan ordinal 4) to also
      # lower as BV64, keeping classify(f)==fcX comparisons in QF_BVFP (F5 safety).
      some(SymVal(kind: svBV64, signed: true, bv64: mkBitVec[64](0'i64)))
    elif e.mathOp in ["abs", "sqrt", "min", "max",
                      "floor", "ceil", "round", "trunc", "copySign"]:
      if e.mathArgs.len > 0: probeProto(env, e.mathArgs[0]) else: none(SymVal)
    else:
      none(SymVal)
  of iekBorrowOp:
    # Phase 15 G5: a borrowed comparison produces svBool; a borrowed arithmetic
    # produces an svDistinct (re-boxed). The OPERANDS are distinct vars; their
    # proto is found by probing them (so a surrounding comparison against a
    # distinct const lowers correctly). Arithmetic-borrow → probe an operand
    # (yields the svDistinct proto); comparison-borrow → bool sentinel.
    if e.borrowReturnsDistinct:
      let l = probeProto(env, e.borrowLhs)
      if l.isSome: l else: probeProto(env, e.borrowRhs)
    else:
      some(SymVal(kind: svBool, bo: mkBool(true)))
  of iekLambda, iekClosureCall:
    # Phase 15 C1 STUB. A closure's representation (the funcSym + env-flattened
    # leaves) is not a single prototype SymVal, and these nodes are STUBBED in
    # `lower` anyway — no surrounding subexpression takes its representation from
    # one. No prototype; the C1 walker never reaches a downstream lowering.
    none(SymVal)
  of iekSeqLit, iekHofCall:
    # Phase 15 C4. A seq literal / HOF result is a container (svSeq) or a fold
    # accumulator; no single prototype SymVal drives a surrounding literal's
    # representation. (The result is consumed via `.len` / index, which carry
    # their own protos.)
    none(SymVal)
  of iekNil:
    # Phase 15 R5. The `nil` literal is not env-resident and carries no integer
    # representation; the ref/ptr operand it is compared against supplies the
    # comparison's shape (ref/ptr ==/!= dispatches via `refEq`, not a proto).
    none(SymVal)

# ---- IR-expr → SymVal -------------------------------------------------------

var currentMaxBytesEncodingLen* {.threadvar.}: int
  ## Phase 15 S7a. The active `SymexSettings.maxBytesEncodingLen`, set at the
  ## top of `runSymexImpl` so the `iekStrBytes` arm in `lower` (which has no
  ## settings parameter) can read the cap without threading settings through
  ## the whole expression-lowering recursion. Mirrors F7's `extractionErrors`
  ## threadvar.

var currentMaxSplitParts* {.threadvar.}: int
  ## CR-11/CR-18. The active `SymexSettings.budget.maxSplitParts`, set at the
  ## top of `runSymexImpl` so the `iekStrSplit` concrete-inline arms in
  ## `lowerStrArm` can enforce the cap without threading settings through the
  ## lower() recursion. Mirrors the `currentMaxBytesEncodingLen` idiom (S7a).
  ## A value of 0 means unlimited (no cap applied). When the computed parts
  ## count exceeds this cap, the split is classified sxUnknown via
  ## SymexZ3StringIncompleteError (seZ3StringIncomplete) — the same error
  ## kind used by the general symbolic split path — rather than emitting
  ## potentially thousands of Z3 store calls (compile-time DoS prevention).

var parseIntGateConstraints* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 S10a. Side soundness-gate constraints emitted by the `iekStrToInt`
  ## (`parseInt`) lowering — `toInt(s) >= 0` on the active digits/negative branch
  ## (the digits gate from Z3's `Z3_mk_str_to_int`, which is `>= 0` for digit
  ## strings). `lower` has no path-condition sink (Env is a pure value table), so
  ## these accumulate here and are drained into EVERY solver check (`trySolve`).
  ## That is sound: each clause references the specific param string var's Z3 AST,
  ## which is identical across paths, and the gate only narrows non-digit models.
  ## Mirrors F7's `extractionErrors` / S7a's `currentMaxBytesEncodingLen` threadvars.

var stripDecompConds* {.threadvar.}: seq[Z3Bool]
  ## Round-4 Slice B (ADR-0026). Decomposition constraints emitted by the
  ## `iekStrStrip` lowering: for `strip(s, leading, trailing, chars)` with a
  ## literal char set, fresh strings `pre`/`core`/`suf` are allocated and
  ##   s == pre ++ core ++ suf
  ##   pre ∈ (union chars)*    (leading; else pre == "")
  ##   suf ∈ (union chars)*    (trailing; else suf == "")
  ##   core == "" ∨ (¬startsWith(core, c) ∀c   when leading
  ##                 ∧ ¬endsWith(core, c) ∀c   when trailing)
  ## are pushed here and drained into EVERY solver check (`trySolve`) —
  ## exactly the `parseIntGateConstraints`/`currentClosureCallAxioms` idiom.
  ## GLOBAL assertion is sound because the clauses are DEFINITIONAL: for
  ## every value of `s` there exists exactly ONE satisfying assignment of
  ## (pre, core, suf) — the maximal-strip decomposition (maximality is
  ## forced by the boundary clause: were `suf` non-maximal, `core` would
  ## end in a stripped char) — so conjoining them never prunes a model of
  ## any other variable, and `core` is FORCED to `strutils.strip`'s exact
  ## value (soundness AND completeness, no over-approximation). The
  ## fragment is quantifier-free string+regex (concat / prefixof /
  ## suffixof / re.star over a finite literal char union) — the same
  ## decidable machinery class as S6b regex membership; no Int/BV mixing
  ## (the CR-17 hang shape). Reset at `runSymexImpl` entry.

var sliceViewCounter* {.threadvar.}: int
  ## v67 (dev item 1). Per-run unique-name counter for `iekSeqSlice`'s
  ## lambda bound variable — two slice views must not share the bound
  ## const's NAME (Z3 consts are keyed by name; aliasing two views' bound
  ## vars is not unsound after lambda closure, but distinct names keep
  ## printed models legible and rule the question out entirely). Reset at
  ## `runSymexImpl` entry.

var stripSynthCounter* {.threadvar.}: int
  ## Round-4 Slice B. Per-run unique-name counter for `iekStrStrip`'s fresh
  ## `pre`/`core`/`suf` allocations — two strip occurrences MUST NOT share
  ## Z3 consts (same name = same const = unsound cross-linking). Reset at
  ## `runSymexImpl` entry.

var variantLitFreshCounter* {.threadvar.}: int
  ## Round-6 A1 (ADR-0029). Per-run unique-name counter for
  ## `lowerVariantLit`'s FRESH inactive-arm field allocations — two
  ## construction-site evaluations (e.g. inside an unrolled loop, or two
  ## distinct constructor call sites) MUST NOT share Z3 consts (same name =
  ## same const = unsound cross-linking), mirroring the `stripSynthCounter`/
  ## `sliceViewCounter` precedent. Reset at `runSymexImpl` entry.

var variantConstructSymFreshCounter* {.threadvar.}: int
  ## Round-6 A3 (ADR-0029). Per-run unique-name counter for
  ## `isVariantConstructSym`'s FRESH per-fork arm-field allocations —
  ## DISTINCT from `variantLitFreshCounter` (own prefix, own counter): two
  ## DIFFERENT forks of the SAME construction statement, or two distinct
  ## construction-site evaluations, MUST NOT share Z3 consts (same name =
  ## same const = unsound cross-linking — the dedicated "fresh inactive-arm
  ## fields PER FORK" divergence this slice pins). Reset at `runSymexImpl`
  ## entry.

var currentInFlightTypeId* {.threadvar.}: Option[string]
  ## Phase 15 E8. The in-flight exception's TYPE id while an `except` handler
  ## body is being walked (mirrors `w.frame.inFlightExn.get.typeId`). `none`
  ## outside any handler. The two `getCurrent*` magic intrinsics lower in
  ## `lower` (a pure Env→SymVal function with no WalkCtx/frame access), so the
  ## walk arms that set/clear `w.frame.inFlightExn` keep this threadvar in
  ## lockstep. A `none` value at lower time means the intrinsic was called
  ## out-of-handler → `SymexNotInHandlerError`. Mirrors the F7/S7a/S10 threadvars.

var currentInFlightMsg* {.threadvar.}: Option[string]
  ## Phase 15 E8. The in-flight exception's MESSAGE (mirrors
  ## `w.frame.inFlightExn.get.msg`) while an `except` handler body is walked.
  ## `none` if the raise carried no message (zero-arg object construction);
  ## `getCurrentExceptionMsg()` returns `currentInFlightMsg.get("")`.

var currentExnRefCounter* {.threadvar.}: int
  ## Phase 15 E8. Monotonic counter for fresh `getCurrentException()` constant
  ## names, so distinct call sites get distinct uninterpreted constants. Reset
  ## per run in `runSymexImpl`.

var lastGetCurrentExnRef* {.threadvar.}: tuple[sortName, typeTag: string]
  ## Phase 15 E8 (test hook). Records the `sortName`/`typeTag` of the most
  ## recently produced `getCurrentException()` `svUninterpRef`. The returned
  ## opaque ref is not witness-extractable through `symexFind`, so E8's test 2
  ## inspects this threadvar to assert the tagging (`Exn_<typeId>` / `typeId`).

var parseIntRaiseConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 S10b. Raise predicates emitted by the `iekStrToInt` (`parseInt`)
  ## lowering — one `(not isNeg) and (posVal < 0)` clause per `parseInt` lowered
  ## (the non-digit, non-`-`-prefixed case, where Nim's runtime RAISES
  ## `ValueError`). `lower` cannot route a raise itself (no WalkCtx/Path), so the
  ## predicate is surfaced here and DRAINED by the enclosing statement walk arm
  ## (`drainParseIntRaises`), which forks a routed-`ValueError` raise sub-path and
  ## a digits continuation. Reset before each lower-and-drain so predicates never
  ## leak across paths/statements. Closes the S10a `seParseIntPreE` window — that
  ## hint is no longer emitted. Mirrors the `parseIntGateConstraints` threadvar.

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal

proc ejectBase(sv: SymVal): SymVal =
  ## Phase 15 G4. When a `distinct T` value is USED in a base-typed context
  ## (an explicit `T(distinctVal)` conversion, which the parser passes through
  ## to the bare distinct var, or any arith/compare against a base value), it
  ## ejects to its base SymVal. The base was bound `== eject_T(distinctConst)`
  ## at allocation, so this is the sound round-trip value (Nim's `T(d)`). For
  ## any non-distinct SymVal this is the identity. Nested distinct chains
  ## (`distinct (distinct U)`) eject all the way down to the ground base.
  if sv.kind == svDistinct: ejectBase(sv.distinctBaseSym[]) else: sv

var currentBorrowReboxCounter* {.threadvar.}: int
  ## Phase 15 G5. Fresh-name counter for re-boxed distinct consts produced by a
  ## borrowed arithmetic operator. `lower` has no `WalkCtx` access (mirroring
  ## E8/G4's threadvar mechanism), so the per-occurrence const name is uniquified
  ## from this counter. Reset at `runSymexImpl` entry.

proc reboxDistinct(distinctName: string, base: SymVal): SymVal =
  ## Phase 15 G5. Re-box a BASE SymVal as a fresh `svDistinct` of `distinctName`
  ## — the result of a borrowed ARITHMETIC operator (`+`/`-`/`*`/`/` returning
  ## the distinct type). A fresh opaque const of the distinct sort carries the
  ## type-wall identity; the COMPUTED base value is boxed underneath so it ejects
  ## back correctly and the witness renders through the eject-reader chain.
  ##
  ## This operates entirely on the G4 boxed base — it does NOT apply the Z3
  ## `inject_T` function (which HANGS on the uninterpreted-fn-over-BV / MBQI
  ## combination, per the G4 finding). The distinct sort is guaranteed present in
  ## `currentDistinctSorts` because the operands were already allocated as this
  ## distinct type earlier in the run.
  let ctx = requireCurrentContext()
  doAssert currentDistinctSorts.hasKey(distinctName),
    "reboxDistinct: distinct sort `" & distinctName & "` not allocated"
  let entry = currentDistinctSorts[distinctName]
  inc currentBorrowReboxCounter
  let constName = "borrow_" & distinctName & "#" & $currentBorrowReboxCounter
  let dAny = wrap[Z3AnyAst](ctx, rawConstOf(ctx, entry.sort.raw, constName))
  let boxed = new(SymVal)
  boxed[] = base
  SymVal(kind: svDistinct, distinctAst: dAny, distinctName: distinctName,
         distinctBaseSym: boxed)

proc bvToZ3Int(sv: SymVal): Z3Int =
  ## Z3-level conversion of a typed BV SymVal to Z3Int. Used when a
  ## BV-shaped value (e.g. a Nim `int` param `i`) meets a Z3Int-shaped
  ## operand (e.g. `s.len`). Z3's `bv2int` is the canonical conversion.
  template wrapIt(bv: untyped): Z3Int =
    wrap[Z3Int](bv.ctx,
      bv.ctx.checkErr Z3_mk_bv2int(bv.ctx.raw, bv.raw, sv.signed))
  case sv.kind
  of svBV8:  wrapIt(sv.bv8)
  of svBV16: wrapIt(sv.bv16)
  of svBV32: wrapIt(sv.bv32)
  of svBV64: wrapIt(sv.bv64)
  else:
    raise newException(ValueError,
      "bvToZ3Int: not a BV — got " & $sv.kind)

proc toZ3Int(sv: SymVal): Z3Int =
  ## Coerce an int-typed SymVal (svInt or BV) to Z3Int.
  case sv.kind
  of svInt: sv.zi
  of svBV8, svBV16, svBV32, svBV64: bvToZ3Int(sv)
  else:
    raise newException(ValueError,
      "toZ3Int: not an int-typed SymVal — got " & $sv.kind)

proc svIntToBV(sv: SymVal, likeKind: SVKind): SymVal =
  ## CR-1a: coerce a Z3-Int-sorted SymVal (`.len`/`.find`/`.indexOf`/
  ## `parseInt` results — these ALWAYS lower to `svInt` unconditionally;
  ## there is no BV-vs-Int representation *choice* made for them the way
  ## there is for a plain symbolic var, so there is no promotion decision
  ## to decline) into a BV SymVal of `likeKind`'s width via Z3's `int2bv`.
  ## Z3's Int theory has no bitwise operators, so this is the only way to
  ## correctly model `bAnd`/`bOr`/`bXor` when an operand is Int-sorted;
  ## `binBV` can then dispatch as usual. `Z3_mk_int2bv` embeds via `n mod
  ## 2^W`, which is exact two's-complement for a negative `n` too (e.g. a
  ## `parseInt("-5")` result is a legitimate negative svInt reaching here),
  ## not just for the non-negative case (`.len`/`.find`/`.indexOf`).
  doAssert sv.kind == svInt, "svIntToBV: not svInt — got " & $sv.kind
  template mk(W: static int): SymVal =
    liftBV(wrap[Z3BitVec[W]](sv.zi.ctx,
      sv.zi.ctx.checkErr Z3_mk_int2bv(sv.zi.ctx.raw, cuint(W), sv.zi.raw)), false)
  case likeKind
  of svBV8:  mk(8)
  of svBV16: mk(16)
  of svBV32: mk(32)
  of svBV64: mk(64)
  else:
    raise newException(ValueError,
      "svIntToBV: target kind is not BV — got " & $likeKind)

proc lowerConvIntWidth(operandSV: SymVal, tgtWidth: int, tgtSigned: bool): SymVal =
  ## Round-6 B2: WIDENING-only int-family width conversion. Every fixed-width
  ## Nim int (including plain `int`/`uint`, width 64) allocates as an svBV*
  ## (never svInt — `allocateSym`'s `itInt` arm goes through `bvVar`), and
  ## `binBV` keeps every arithmetic result at matching BV width, so
  ## `operandSV` is always svBV{8,16,32} here (parse-time width ordering
  ## guarantees `tgtWidth` is one of the three legal wider targets for each
  ## source width — narrowing/same-width never reach this proc, they are
  ## classified declines at parse time).
  ##
  ## `zeroExtend`/`signExtend`'s `extraBits` argument is a `static int`, so
  ## each (srcWidth, tgtWidth) pair needs its OWN literal call site — the
  ## same reason `toBv64ForFp` (runtime_floats.nim) enumerates per-width
  ## arms instead of computing `extra` as a runtime value.
  let srcSigned = operandSV.signed
  case operandSV.kind
  of svBV8:
    let b = operandSV.bv8
    case tgtWidth
    of 16: SymVal(kind: svBV16, signed: tgtSigned,
                   bv16: (if srcSigned: signExtend(b, 8) else: zeroExtend(b, 8)))
    of 32: SymVal(kind: svBV32, signed: tgtSigned,
                   bv32: (if srcSigned: signExtend(b, 24) else: zeroExtend(b, 24)))
    of 64: SymVal(kind: svBV64, signed: tgtSigned,
                   bv64: (if srcSigned: signExtend(b, 56) else: zeroExtend(b, 56)))
    else:
      raiseAssert "lowerConvIntWidth: bad target width from BV8: " & $tgtWidth
  of svBV16:
    let b = operandSV.bv16
    case tgtWidth
    of 32: SymVal(kind: svBV32, signed: tgtSigned,
                   bv32: (if srcSigned: signExtend(b, 16) else: zeroExtend(b, 16)))
    of 64: SymVal(kind: svBV64, signed: tgtSigned,
                   bv64: (if srcSigned: signExtend(b, 48) else: zeroExtend(b, 48)))
    else:
      raiseAssert "lowerConvIntWidth: bad target width from BV16: " & $tgtWidth
  of svBV32:
    let b = operandSV.bv32
    case tgtWidth
    of 64: SymVal(kind: svBV64, signed: tgtSigned,
                   bv64: (if srcSigned: signExtend(b, 32) else: zeroExtend(b, 32)))
    else:
      raiseAssert "lowerConvIntWidth: bad target width from BV32: " & $tgtWidth
  else:
    raiseAssert "lowerConvIntWidth: unsupported operand kind for widening: " &
      $operandSV.kind

proc iteSV(cond: Z3Bool, t, e: SymVal): SymVal =
  ## Z3-level if-then-else over SymVals. Both branches must share kind.
  doAssert t.kind == e.kind, "iteSV: kind mismatch " &
    $t.kind & " vs " & $e.kind
  case t.kind
  of svUninterpRef:
    raise newException(ValueError, "iteSV: svUninterpRef merge lands with cluster E")
  of svFloat32:   ## Phase 15 F9a: IEEE float path-merge over Z3 FP `ite`.
    SymVal(kind: svFloat32, fp32: ite(cond, t.fp32, e.fp32))
  of svFloat64:
    SymVal(kind: svFloat64, fp64: ite(cond, t.fp64, e.fp64))
  of svBool: ofBool(ite(cond, t.bo, e.bo))
  of svInt:  SymVal(kind: svInt, zi: ite(cond, t.zi, e.zi))
  of svBV8:  liftBV(ite(cond, t.bv8,  e.bv8),  t.signed)
  of svBV16: liftBV(ite(cond, t.bv16, e.bv16), t.signed)
  of svBV32: liftBV(ite(cond, t.bv32, e.bv32), t.signed)
  of svBV64: liftBV(ite(cond, t.bv64, e.bv64), t.signed)
  of svTuple:
    var fs: seq[SymVal]
    for i, ft in t.fields: fs.add iteSV(cond, ft, e.fields[i])
    SymVal(kind: svTuple, fields: fs, fieldNames: t.fieldNames)
  of svArray:
    var fs: seq[SymVal]
    for i, ae in t.arrElems: fs.add iteSV(cond, ae, e.arrElems[i])
    SymVal(kind: svArray, arrElems: fs, arrElemTy: t.arrElemTy)
  of svDistinct:
    # Phase 15 G4: merge the opaque distinct ast over Z3's polymorphic `ite`
    # (uninterpreted-sort ites are fine) and the base recursively.
    let ctx = t.distinctAst.ctx
    var args = [cond.raw, t.distinctAst.raw, e.distinctAst.raw]
    let merged = ctx.checkErr Z3_mk_ite(ctx.raw, args[0], args[1], args[2])
    let boxed = new(SymVal)
    boxed[] = iteSV(cond, t.distinctBaseSym[], e.distinctBaseSym[])
    SymVal(kind: svDistinct, distinctAst: wrap[Z3AnyAst](ctx, merged),
           distinctName: t.distinctName, distinctBaseSym: boxed)
  of svString, svSeq, svTable, svSet, svVariant, svMultiVariant:
    raise newException(ValueError,
      "iteSV: not supported for " & $t.kind & " (Phase 5+)")
  of svClosure:
    # Phase 15 C1 STUB. Closure path-merge lands with the C2a/C2b walker
    # (an ite over the site-keyed funcSym + a recursive env merge). Never
    # reached in C1 (the walker stubs before any svClosure is constructed).
    raise newException(ValueError,
      "iteSV: svClosure merge lands with Cluster C C2a/C2b")
  of svRef, svPtr:
    # Cluster H H_containers (ADR-0022): a per-position `ite` over the two
    # `Ref_T` addresses. Needed for `array[N, Node]` INDEXING — the static-
    # array `isIndex` arm always builds a full ite-merge chain over every
    # element (even for a compile-time-literal index; there is no fast path,
    # unlike the Z3Array-backed `seq[Node]`), so a >1-element `array[N,
    # Node]` reaches this arm. Sound: every element of a homogeneous
    # `array[N, T]` shares the SAME `Ref_T` sort, so a plain value-level
    # `Z3_mk_ite` over the two addresses (mirroring the `svBV*`/`svInt` arms
    # above) is well-typed. This is a distinct axis from R5's nil-fork /
    # R7's alias-equality machinery (those reason about whether two refs
    # DENOTE the same address; this just picks one of two already-built
    # addresses per branch, the same shape as any other primitive merge).
    let refT = if t.kind == svPtr: t.ptrAst else: t.refAst
    let refE = if e.kind == svPtr: e.ptrAst else: e.refAst
    let ctx = refT.ctx
    let mergedRaw = ctx.checkErr Z3_mk_ite(ctx.raw, cond.raw, refT.raw, refE.raw)
    let merged = wrap[Z3AnyAst](ctx, mergedRaw)
    if t.kind == svPtr:
      SymVal(kind: svPtr, ptrAst: merged, ptrFamily: t.ptrFamily, ptrPointee: t.ptrPointee)
    else:
      SymVal(kind: svRef, refAst: merged, refPointee: t.refPointee)

proc symEq(a, b: SymVal): Z3Bool =
  ## Equality of two same-kind primitive SymVals as a Z3Bool.
  doAssert a.kind == b.kind
  case a.kind
  of svBool: a.bo == b.bo
  of svInt:  a.zi == b.zi
  of svBV8:  a.bv8  == b.bv8
  of svBV16: a.bv16 == b.bv16
  of svBV32: a.bv32 == b.bv32
  of svBV64: a.bv64 == b.bv64
  else:
    raise newException(ValueError,
      "symEq: not a primitive — got " & $a.kind)

proc reconcileInt*(a, b: SymVal): (SymVal, SymVal)
  ## v69 fwd-decl (defined below, CR-9(c) Stage B) — retBindEq's svTuple arm
  ## reconciles mixed int reps PER FIELD before recursing (a field can be
  ## svInt via range propagation while its retSym slot allocated svBV*).

proc retBindEq(retSym, retVal: SymVal): Z3Bool =
  ## Phase 15 G3: the binding constraint linking a call's fresh `retSym`
  ## placeholder to the value the callee actually returns (used by the
  ## `isReturn` arm). This is a *binding*, not a user-facing `==`, so it
  ## must be SOUND on every reachable return value — in particular it must
  ## NOT prune a path that returns `NaN`. Floats therefore use a structural
  ## equality (`(a == b) or (both NaN)`) rather than the bare IEEE `==`
  ## (which is `false` for `NaN == NaN` and would kill a NaN-returning
  ## path). Int/bool/string keep their native structural equality. This is
  ## what lets a value-returning generic instantiated at `float64`/`string`
  ## flow its result into the caller (G3 centerpiece: the float bridge
  ## reached THROUGH a generic call, not just at a top-level float param).
  doAssert retSym.kind == retVal.kind,
    "retBindEq: kind mismatch " & $retSym.kind & " vs " & $retVal.kind
  case retSym.kind
  of svBool: retSym.bo == retVal.bo
  of svInt:  retSym.zi == retVal.zi
  of svBV8:  retSym.bv8  == retVal.bv8
  of svBV16: retSym.bv16 == retVal.bv16
  of svBV32: retSym.bv32 == retVal.bv32
  of svBV64: retSym.bv64 == retVal.bv64
  of svFloat32:
    (retSym.fp32 == retVal.fp32) or (isNaN(retSym.fp32) and isNaN(retVal.fp32))
  of svFloat64:
    (retSym.fp64 == retVal.fp64) or (isNaN(retSym.fp64) and isNaN(retVal.fp64))
  of svString: retSym.str == retVal.str
  of svSeq:
    ## Round-6 Bug #2 (scoped decline): reached recursively from the
    ## `svTuple`/`svVariant` arms below when binding an object/variant field
    ## whose type carries the per-field UNSUPPORTED PLACEHOLDER
    ## (`isUnsupportedFieldPlaceholder`, `types.nim` — mirrored onto the
    ## SymVal as `isUnsupportedFieldPlaceholder`, set by `allocateSym`'s
    ## `itSeq` arm). SKIP the eq constraint for a placeholder field
    ## (no-constraint is a sound over-approximation: the field's content is
    ## never modeled either side, so asserting them equal would be
    ## meaningless, and omitting the constraint costs nothing since no read
    ## of this field ever trusts its content anyway — the `nnkDotExpr`
    ## read-taint owns honesty). A GENUINE (non-placeholder) `svSeq` return
    ## field is not yet a wired capability — same as before this slice —
    ## and still raises, so this does not silently change behavior for any
    ## already-tested plain-seq-returning SUT.
    if retSym.isUnsupportedFieldPlaceholder or retVal.isUnsupportedFieldPlaceholder:
      mkBool(true)
    else:
      raise newException(ValueError,
        "retBindEq: svSeq composite return not yet wired (outside the " &
        "Round-6 Bug #2 scoped-decline placeholder)")
  of svTuple:
    ## v69 (sello #2): structural per-field binding for a tuple-returning
    ## callee — the capability the v64 catalog-#6 degrade preserved as
    ## `feUnsupportedOp`. Recurses so nested tuples bind too; each field
    ## pair is int-reconciled first (same discipline as the scalar site).
    doAssert retSym.fields.len == retVal.fields.len,
      "retBindEq: tuple arity mismatch " & $retSym.fields.len & " vs " &
      $retVal.fields.len
    var acc = mkBool(true)
    for i in 0 ..< retSym.fields.len:
      let (fs, fv) = reconcileInt(retSym.fields[i], retVal.fields[i])
      acc = acc and retBindEq(fs, fv)
    acc
  of svVariant:
    ## Round-6 A2 (ADR-0029): the GENERAL encoding — sound for both a
    ## freshly-pinned literal construction (A1's `iekVariantLit`, where
    ## "active arm" is host-selectable) and a pass-through return of a
    ## variant-typed PARAMETER (genuinely symbolic discriminant, no arm
    ## distinguished at bind time):
    ##   discEq ∧ (⋀ declared arms: disc==tag → per-field eq) ∧ plain-field eq
    ## The per-arm IMPLICATION guard (not a bare conjunction) is what keeps
    ## this sound for a symbolic disc: an unguarded all-arms-equated
    ## encoding would force every arm's fields equal regardless of which
    ## tag the discriminant actually takes.
    doAssert retSym.vObjectName == retVal.vObjectName,
      "retBindEq: variant object mismatch " & retSym.vObjectName & " vs " &
      retVal.vObjectName
    let (sDisc, vDisc) = reconcileInt(retSym.vDisc[], retVal.vDisc[])
    var acc = retBindEq(sDisc, vDisc)
    for tagOrd, symFields in retSym.vArmFields:
      let valFields = retVal.vArmFields[tagOrd]
      doAssert symFields.len == valFields.len,
        "retBindEq: variant arm arity mismatch for tag " & $tagOrd & ": " &
        $symFields.len & " vs " & $valFields.len
      var armEq = mkBool(true)
      for i in 0 ..< symFields.len:
        let (fs, fv) = reconcileInt(symFields[i], valFields[i])
        armEq = armEq and retBindEq(fs, fv)
      acc = acc and variantDiscEq(retSym.vDisc[], int64(tagOrd)).implies(armEq)
    doAssert retSym.vPlainFields.len == retVal.vPlainFields.len,
      "retBindEq: variant plain-field arity mismatch " &
      $retSym.vPlainFields.len & " vs " & $retVal.vPlainFields.len
    for i in 0 ..< retSym.vPlainFields.len:
      let (fs, fv) = reconcileInt(retSym.vPlainFields[i], retVal.vPlainFields[i])
      acc = acc and retBindEq(fs, fv)
    acc
  else:
    raise newException(ValueError,
      "retBindEq: composite-typed proc return not yet wired — got " &
      $retSym.kind)

proc freshRetSym(ty: IRType, name: string, pcOut: var seq[Z3Bool],
                 intOffsetPositions: seq[int] = @[]): SymVal =
  ## Phase 15 G3: allocate a fresh, well-typed symbol for a call's return
  ## value. Replaces the old `bvVar`-only allocation (which asserted
  ## `itInt`) at every call-return site so a generic — or any proc —
  ## returning a `float`/`string`/composite type gets a correctly-typed
  ## placeholder instead of crashing on the int assertion. Routes through
  ## the existing type-aware `allocateSym`; any init-side constraints (the
  ## string byte-range floor, seq-len floor, …) are threaded into `pcOut`.
  ## `intOffsetPositions` (round-6 B5): forwarded verbatim to `allocateSym` —
  ## see its own doc for the chained-scan-composition rationale.
  allocateSym(ty, name, pcOut, intOffsetPositions = intOffsetPositions)

proc coerceIntLit(proto: SymVal, ival: int64): SymVal =
  ## Build a SymVal representing literal `ival` at `proto`'s
  ## representation. Used when an `iekIntLit`'s Z3 representation
  ## must match a surrounding variable.
  case proto.kind
  of svUninterpRef:
    raise newException(ValueError, "symLit: svUninterpRef has no integer form (cluster E)")
  of svFloat32:   ## Phase 15 F5: int literal in a float context -> float numeral
    SymVal(kind: svFloat32, fp32: mkFloat32(float32(ival)))
  of svFloat64:
    SymVal(kind: svFloat64, fp64: mkFloat64(float64(ival)))
  of svBV8:  liftBV(mkBitVec[8](ival),  proto.signed)
  of svBV16: liftBV(mkBitVec[16](ival), proto.signed)
  of svBV32: liftBV(mkBitVec[32](ival), proto.signed)
  of svBV64: liftBV(mkBitVec[64](ival), proto.signed)
  of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(ival))
  of svBool:
    raise newException(ValueError,
      "coerceIntLit: bool prototype for integer literal")
  of svDistinct:   ## Phase 15 G4: coerce against the distinct's ejected base.
    coerceIntLit(proto.distinctBaseSym[], ival)
  of svTuple, svArray, svString, svSeq, svTable, svSet, svVariant,
     svMultiVariant, svClosure, svRef, svPtr:
    ## svClosure: Phase 15 C1; svRef/svPtr: Phase 15 R1a (never an int proto)
    raise newException(ValueError,
      "coerceIntLit: composite prototype for integer literal kind=" & $proto.kind)

# Width-uniform BV arithmetic. Both operands must be the same width.
template binBV(a, b: SymVal, op: untyped): SymVal =
  ## Apply `op(va, vb)` where `va`/`vb` are the typed BV handles.
  ## Asserts both SymVals share a BV kind.
  doAssert a.kind == b.kind, "binBV: width mismatch"
  case a.kind
  of svBV8:
    liftBV(op(a.bv8, b.bv8), a.signed)
  of svBV16:
    liftBV(op(a.bv16, b.bv16), a.signed)
  of svBV32:
    liftBV(op(a.bv32, b.bv32), a.signed)
  of svBV64:
    liftBV(op(a.bv64, b.bv64), a.signed)
  else:
    raise newException(ValueError, "binBV on non-BV SymVal")

template cmpBV(a, b: SymVal, sop, uop: untyped): SymVal =
  ## Apply signed/unsigned comparison and lift to SymVal Bool.
  doAssert a.kind == b.kind, "cmpBV: width mismatch"
  let useSigned = a.signed
  case a.kind
  of svBV8:
    ofBool(if useSigned: sop(a.bv8,  b.bv8)  else: uop(a.bv8,  b.bv8))
  of svBV16:
    ofBool(if useSigned: sop(a.bv16, b.bv16) else: uop(a.bv16, b.bv16))
  of svBV32:
    ofBool(if useSigned: sop(a.bv32, b.bv32) else: uop(a.bv32, b.bv32))
  of svBV64:
    ofBool(if useSigned: sop(a.bv64, b.bv64) else: uop(a.bv64, b.bv64))
  else:
    raise newException(ValueError, "cmpBV on non-BV SymVal")

template divBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: bvsdiv(a.bv8,  b.bv8)  else: bvudiv(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: bvsdiv(a.bv16, b.bv16) else: bvudiv(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: bvsdiv(a.bv32, b.bv32) else: bvudiv(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: bvsdiv(a.bv64, b.bv64) else: bvudiv(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "divBV on non-BV SymVal")

template modBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: bvsmod(a.bv8,  b.bv8)  else: bvurem(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: bvsmod(a.bv16, b.bv16) else: bvurem(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: bvsmod(a.bv32, b.bv32) else: bvurem(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: bvsmod(a.bv64, b.bv64) else: bvurem(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "modBV on non-BV SymVal")

template shrBV(a, b: SymVal): SymVal =
  ## Nim `shr` on signed → arithmetic (ashr); on unsigned → logical (lshr).
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: ashr(a.bv8,  b.bv8)  else: lshr(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: ashr(a.bv16, b.bv16) else: lshr(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: ashr(a.bv32, b.bv32) else: lshr(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: ashr(a.bv64, b.bv64) else: lshr(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "shrBV on non-BV SymVal")

template negBV(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(-a.bv8,  a.signed)
  of svBV16: liftBV(-a.bv16, a.signed)
  of svBV32: liftBV(-a.bv32, a.signed)
  of svBV64: liftBV(-a.bv64, a.signed)
  else: raise newException(ValueError, "negBV on non-BV SymVal")

template notBV(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(not a.bv8,  a.signed)
  of svBV16: liftBV(not a.bv16, a.signed)
  of svBV32: liftBV(not a.bv32, a.signed)
  of svBV64: liftBV(not a.bv64, a.signed)
  else: raise newException(ValueError, "notBV on non-BV SymVal")

# ---- Equality across BV widths is uniform -----------------------------------

template eqBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  case a.kind
  of svBV8:  ofBool(a.bv8  == b.bv8)
  of svBV16: ofBool(a.bv16 == b.bv16)
  of svBV32: ofBool(a.bv32 == b.bv32)
  of svBV64: ofBool(a.bv64 == b.bv64)
  else: raise newException(ValueError, "eqBV on non-BV SymVal")

template neBV(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  case a.kind
  of svBV8:  ofBool(a.bv8  != b.bv8)
  of svBV16: ofBool(a.bv16 != b.bv16)
  of svBV32: ofBool(a.bv32 != b.bv32)
  of svBV64: ofBool(a.bv64 != b.bv64)
  else: raise newException(ValueError, "neBV on non-BV SymVal")

proc refEq(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 R2 (ADR-0010). `==`/`!=` over two ref/ptr SymVals — a GROUND
  ## equality of the two `Ref_T`-sorted address consts (`Z3_mk_eq`, negated for
  ## `!=`). With the per-path freshness inequalities asserted at each `new T`,
  ## two distinct fresh refs are provably non-equal (so `if p == q` over two
  ## fresh allocations is an unreachable branch). No heap read happens here.
  let aAst = (if a.kind == svRef: a.refAst else: a.ptrAst)
  let bAst = (if b.kind == svRef: b.refAst else: b.ptrAst)
  let ctx = requireCurrentContext()
  let eq = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_eq(ctx.raw, aAst.raw, bAst.raw))
  case op
  of bEq: ofBool(eq)
  of bNe: ofBool(not eq)
  else: raise newException(ValueError,
    "ref/ptr comparison op " & $op & " not valid (only ==/!=)")

# ---- Lowering ---------------------------------------------------------------

proc reconcileFloat*(a, b: SymVal): (SymVal, SymVal) =
  ## Phase 15 D-3 (re-review). Widen the narrower of two float SymVals to the
  ## wider sort, so both operands are the SAME float width before any comparison
  ## or arithmetic. When one side is svFloat32 and the other is svFloat64, widen
  ## the float32 to float64 via `toFp(rmRNE(), fp32, Z3Float64)` — matching Nim's
  ## semantics: Nim widens the narrower operand (the `nnkHiddenStdConv` the parser
  ## strips). Mirror of the mixed-integer reconciliation at ~3204-3210.
  ## When both operands are the same width, returns them unchanged (identity).
  doAssert a.kind in {svFloat32, svFloat64} and b.kind in {svFloat32, svFloat64},
    "reconcileFloat: both operands must be svFloat32 or svFloat64, got " &
    $a.kind & " and " & $b.kind
  if a.kind == svFloat32 and b.kind == svFloat64:
    (SymVal(kind: svFloat64, fp64: toFp(rmRNE(), a.fp32, Z3Float64)), b)
  elif a.kind == svFloat64 and b.kind == svFloat32:
    (a, SymVal(kind: svFloat64, fp64: toFp(rmRNE(), b.fp32, Z3Float64)))
  else:
    (a, b)  ## same width — no widening needed

proc reconcileInt*(a, b: SymVal): (SymVal, SymVal) =
  ## CR-9(c) Stage B. When the two operands have DIFFERENT int-family kinds
  ## (e.g. svBV64 vs svInt, or svBV32 vs svBV64), convert both to svInt via
  ## `toZ3Int` (Z3's `bv2int`).  When the kinds match, return them unchanged.
  ## This is the exact body extracted from the probe-hit comparison arm:
  ##   if l.kind != r.kind and
  ##      l.kind in {svInt,svBV8..svBV64} and r.kind in {svInt,svBV8..svBV64}:
  ##     l = SymVal(kind: svInt, zi: toZ3Int(l))
  ##     r = SymVal(kind: svInt, zi: toZ3Int(r))
  ## Additive — no call-site change in this commit (Stage B).
  ## Mirror of reconcileFloat (~2084): same identity-fast-path, same goal.
  if a.kind != b.kind and
     a.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
     b.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
    (SymVal(kind: svInt, zi: toZ3Int(a)),
     SymVal(kind: svInt, zi: toZ3Int(b)))
  else:
    (a, b)  ## same kind (or non-int) — identity

proc cmpFloat(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 F2: IEEE equality via Z3 FP theory (`==`/`!=` on Z3Fp are
  ## IEEE, so NaN == NaN is false). F4 adds ordering (`<` `<=` `>` `>=`).
  ##
  ## Phase 15 CR-6 / D-3: mixed-precision reconciliation via `reconcileFloat`.
  ## When one side is svFloat32 and the other is svFloat64, widen the float32
  ## to float64 — matching Nim's semantics. The widening lives in one place
  ## (`reconcileFloat`) so `arithFloat` and other float ops can reuse it.
  # DES-2: the `doAssert a.kind in {svFloat32, svFloat64}` that was here is
  # now redundant: `reconcileFloat` carries its own doAssert with the same
  # check (and a clearer diagnostic message). Removed to keep one assertion
  # site (DRY). `reconcileFloat` will catch any non-float operand loud and
  # early before any Z3 call is made.
  # Reconcile mixed float widths via the extracted helper (D-3).
  var (a, b) = reconcileFloat(a, b)
  # Both operands are now the same width.
  if a.kind == svFloat32:
    case op
    of bEq: ofBool(a.fp32 == b.fp32)
    of bNe: ofBool(a.fp32 != b.fp32)
    of bLt: ofBool(a.fp32 <  b.fp32)   # Phase 15 F4: IEEE ordering (false on NaN)
    of bLe: ofBool(a.fp32 <= b.fp32)
    of bGt: ofBool(a.fp32 >  b.fp32)
    of bGe: ofBool(a.fp32 >= b.fp32)
    else: raise newException(ValueError, "cmpFloat: not a comparison op")
  else:
    case op
    of bEq: ofBool(a.fp64 == b.fp64)
    of bNe: ofBool(a.fp64 != b.fp64)
    of bLt: ofBool(a.fp64 <  b.fp64)   # Phase 15 F4: IEEE ordering (false on NaN)
    of bLe: ofBool(a.fp64 <= b.fp64)
    of bGt: ofBool(a.fp64 >  b.fp64)
    of bGe: ofBool(a.fp64 >= b.fp64)
    else: raise newException(ValueError, "cmpFloat: not a comparison op")

proc arithFloat(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 F3: IEEE arithmetic via Z3 FP theory. The Z3Fp `+ - * /`
  ## operators default to round-to-nearest-even (ADR-0005 / OQ2). Division
  ## by zero follows IEEE (yields ±Inf / NaN) — not a defect.
  doAssert a.kind == b.kind and a.kind in {svFloat32, svFloat64}
  if a.kind == svFloat32:
    SymVal(kind: svFloat32, fp32:
      (case op
       of bAdd: a.fp32 + b.fp32
       of bSub: a.fp32 - b.fp32
       of bMul: a.fp32 * b.fp32
       of bDiv: a.fp32 / b.fp32
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))
  else:
    SymVal(kind: svFloat64, fp64:
      (case op
       of bAdd: a.fp64 + b.fp64
       of bSub: a.fp64 - b.fp64
       of bMul: a.fp64 * b.fp64
       of bDiv: a.fp64 / b.fp64
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))

proc arithInt(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  case op
  of bAdd: SymVal(kind: svInt, zi: a.zi + b.zi)
  of bSub: SymVal(kind: svInt, zi: a.zi - b.zi)
  of bMul: SymVal(kind: svInt, zi: a.zi * b.zi)
  of bDiv: SymVal(kind: svInt, zi: a.zi div b.zi)
  of bMod: SymVal(kind: svInt, zi: a.zi mod b.zi)
  else: raise newException(ValueError, "arithInt: not an arithmetic op")

proc cmpInt(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  case op
  of bEq: ofBool(a.zi == b.zi)
  of bNe: ofBool(a.zi != b.zi)
  of bLt: ofBool(a.zi <  b.zi)
  of bLe: ofBool(a.zi <= b.zi)
  of bGt: ofBool(a.zi >  b.zi)
  of bGe: ofBool(a.zi >= b.zi)
  else: raise newException(ValueError, "cmpInt: not a comparison op")

proc cmpString(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 Cluster S (S1). Z3 String equality (`==`/`!=`). This is the
  ## previously-missing free-`string` `==` path — Phase 5 only wired string
  ## table-key equality, not `s == "lit"`. Lexicographic ordering (`<`/`<=`,
  ## via Z3 `str.<`) lands in S3; until then ordering ops degrade in-band
  ## (SND-3, ADR-0023, walker v58) rather than mis-dispatching to BV compare.
  ## `cmpString` is a PURE helper (no `env`/`w` in scope), called from
  ## `lowerCmp` on the SAME call chain as the CR-17(a) char-ordering guard
  ## above — reachable inside a loop guard (e.g. `while s1 < s2: ...`), so a
  ## `raise` here would hit the identical C-backend silent-loss hazard. See
  ## `loweringDidDegrade`'s doc comment for the full mechanism.
  doAssert a.kind == svString and b.kind == svString
  case op
  of bEq: ofBool(a.str == b.str)
  of bNe: ofBool(a.str != b.str)
  else:
    loweringDegradeErrors.add SymexErrorInfo(kind: seUnsupportedStringOp,
      severity: sevError,
      msg: "string ordering `" & $op & "` is not modeled until S3")
    loweringDidDegrade = true
    var fresh: seq[Z3Bool]
    allocateSym(tBool(), "__strOrderingDegrade", fresh)

proc svLeafEq(a, b: SymVal): Z3Bool =
  ## Phase 15 C5. Structural equality of two SAME-kind LEAF SymVals as a Z3Bool.
  ## The per-leaf building block of `svTupleEq` (closure-environment equality,
  ## ADR-0009 D7). Mirrors the per-kind `==` the binop comparison arm dispatches
  ## (cmpInt/cmpFloat/cmpString/eqBV/bool-eq), but returns the raw Z3Bool so the
  ## tuple helper can AND the field equalities. `svDistinct` ejects to its base
  ## (G4 round-trip) and recurses; nested `svTuple`/`svArray` recurse element-wise.
  doAssert a.kind == b.kind,
    "svLeafEq: kind mismatch " & $a.kind & " vs " & $b.kind
  case a.kind
  of svBool: a.bo == b.bo
  of svInt:  a.zi == b.zi
  of svBV8:  a.bv8  == b.bv8
  of svBV16: a.bv16 == b.bv16
  of svBV32: a.bv32 == b.bv32
  of svBV64: a.bv64 == b.bv64
  of svFloat32: a.fp32 == b.fp32   ## IEEE `==` (NaN != NaN); env values are concrete
  of svFloat64: a.fp64 == b.fp64
  of svString:  a.str == b.str
  of svDistinct:
    # G4: compare the EJECTED base values (the round-trip sound base), not the
    # opaque distinct consts (which are fresh per allocation).
    svLeafEq(ejectBase(a), ejectBase(b))
  else:
    raise newException(ValueError,
      "svLeafEq: closure-environment field of kind " & $a.kind &
      " is not supported for structural equality (C5)")

proc svTupleEq(a, b: SymVal): Z3Bool =
  ## Phase 15 C5 (ADR-0009 D7) — NET-NEW. Structural equality of two `svTuple`
  ## values as a Z3Bool: the per-field equalities AND-ed together. Used for
  ## closure ENVIRONMENT equality on the same-site branch of `svClosure` `==`
  ## (the engine had no `svTuple` `==` arm before C5, per the C0-ADR). Handles
  ## nested tuples and arrays (recursing) and every leaf SymVal kind (via
  ## `svLeafEq`). A ZERO-field tuple (unit-env closure, C3) is vacuously equal
  ## → `mkBool(true)`.
  doAssert a.kind == svTuple and b.kind == svTuple,
    "svTupleEq: not a tuple — got " & $a.kind & " / " & $b.kind
  doAssert a.fields.len == b.fields.len,
    "svTupleEq: arity mismatch " & $a.fields.len & " vs " & $b.fields.len
  var acc: Z3Bool
  var seeded = false
  for i in 0 ..< a.fields.len:
    let fa = a.fields[i]
    let fb = b.fields[i]
    let feq =
      if fa.kind == svTuple:   svTupleEq(fa, fb)
      elif fa.kind == svArray:
        # element-wise AND over a concrete-length array.
        doAssert fb.kind == svArray and fa.arrElems.len == fb.arrElems.len,
          "svTupleEq: nested array arity mismatch"
        var aacc: Z3Bool
        var aseeded = false
        for j in 0 ..< fa.arrElems.len:
          let e =
            if fa.arrElems[j].kind == svTuple: svTupleEq(fa.arrElems[j], fb.arrElems[j])
            else: svLeafEq(fa.arrElems[j], fb.arrElems[j])
          if not aseeded: aacc = e; aseeded = true
          else:           aacc = aacc and e
        if aseeded: aacc else: mkBool(true)
      else:                    svLeafEq(fa, fb)
    if not seeded: acc = feq; seeded = true
    else:          acc = acc and feq
  if seeded: acc else: mkBool(true)   ## unit-env → vacuously equal

proc closureEq(c1, c2: SymVal, op: IRBinop): SymVal =
  ## Phase 15 C5 (ADR-0009 D7). `==`/`!=` on two `svClosure` operands under
  ## NOMINAL-for-site + STRUCTURAL-for-env semantics:
  ##   - DIFFERENT site `(siteHash, declOrder)` integer-pair → ALWAYS unequal:
  ##     a pure Nim-side comparison, NO Z3 involved (`==`→false, `!=`→true). The
  ##     common different-site case stays entirely off the solver.
  ##   - SAME site pair → equal iff the captured ENVIRONMENTS are structurally
  ##     equal: `c1.closureEnv == c2.closureEnv` via the net-new `svTupleEq`
  ##     (a field-by-field Z3 conjunction; a unit-env is vacuously equal).
  ## Nim's own `==` on closures is undefined (proc/env pointer identity); the
  ## symex model is the DEFINED one (closures.md / determinism.md § divergences).
  doAssert c1.kind == svClosure and c2.kind == svClosure
  doAssert op in {bEq, bNe},
    "closureEq: only ==/!= are defined on closure values, got " & $op
  let sameSite = c1.closureSite == c2.closureSite   ## (siteHash, declOrder) pair
  if not sameSite:
    # Different syntactic sites → always unequal, regardless of environments.
    case op
    of bEq: ofBool(mkBool(false))
    else:   ofBool(mkBool(true))
  else:
    # Same site → structural environment equality.
    let envA = if c1.closureEnv != nil: c1.closureEnv[]
               else: SymVal(kind: svTuple, fields: @[], fieldNames: @[])
    let envB = if c2.closureEnv != nil: c2.closureEnv[]
               else: SymVal(kind: svTuple, fields: @[], fieldNames: @[])
    let eq = svTupleEq(envA, envB)
    case op
    of bEq: ofBool(eq)
    else:   ofBool(not eq)

proc coerceToBoolSV(sv: SymVal): SymVal =
  ## Phase 15 G7. A `static bool` param's value is baked by Nim's semchecker
  ## into the typed body as an INTEGER literal (`true`→`IntLit 1`,
  ## `false`→`IntLit 0`), so a `(pred) == B` comparison lowers `B` to an
  ## int/BV SymVal while the LHS is `svBool`. When a bool `==`/`!=` finds an
  ## int-rep operand, coerce it to `svBool` via `value != 0` (the canonical
  ## C/Nim truthiness). Already-`svBool` operands pass through unchanged.
  if sv.kind == svBool: return sv
  if sv.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
    let zi = toZ3Int(sv)
    return ofBool(zi != mkInt(0))
  sv

proc divisorIsZero(b: SymVal): Z3Bool =
  ## R16-3: build divisor==0 predicate in the operand's NATIVE sort.
  ## Uses NO bv2int / int2bv — mixed-theory conversions hang Z3.
  case b.kind
  of svInt:  b.zi == mkZ3IntLit(0)
  of svBV8:  b.bv8  == mkBitVec[8](0)
  of svBV16: b.bv16 == mkBitVec[16](0)
  of svBV32: b.bv32 == mkBitVec[32](0)
  of svBV64: b.bv64 == mkBitVec[64](0)
  else:
    raise newException(ValueError,
      "divisorIsZero: unexpected divisor kind " & $b.kind)

proc overflowCond(a, b: SymVal, op: IRBinop): Z3Bool =
  ## R16-4: build "this signed BV arithmetic op overflows" predicate.
  ## Returns true (raise) when the operation overflows OR underflows.
  ## Only called for signed BV operands — caller guards `a.signed == true` and
  ## `a.kind in {svBV8, svBV16, svBV32, svBV64}`.
  ## svInt is skipped entirely (BV overflow predicates on Int terms hang Z3).
  ## Unsigned BV is skipped (Nim wraps silently — no OverflowDefect).
  case a.kind
  of svBV8:
    case op
    of bAdd: not addNoOverflow(a.bv8, b.bv8, true) or not addNoUnderflow(a.bv8, b.bv8)
    of bSub: not subNoOverflow(a.bv8, b.bv8) or not subNoUnderflow(a.bv8, b.bv8, true)
    of bMul: not mulNoOverflow(a.bv8, b.bv8, true) or not mulNoUnderflow(a.bv8, b.bv8)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)
  of svBV16:
    case op
    of bAdd: not addNoOverflow(a.bv16, b.bv16, true) or not addNoUnderflow(a.bv16, b.bv16)
    of bSub: not subNoOverflow(a.bv16, b.bv16) or not subNoUnderflow(a.bv16, b.bv16, true)
    of bMul: not mulNoOverflow(a.bv16, b.bv16, true) or not mulNoUnderflow(a.bv16, b.bv16)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)
  of svBV32:
    case op
    of bAdd: not addNoOverflow(a.bv32, b.bv32, true) or not addNoUnderflow(a.bv32, b.bv32)
    of bSub: not subNoOverflow(a.bv32, b.bv32) or not subNoUnderflow(a.bv32, b.bv32, true)
    of bMul: not mulNoOverflow(a.bv32, b.bv32, true) or not mulNoUnderflow(a.bv32, b.bv32)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)
  of svBV64:
    case op
    of bAdd: not addNoOverflow(a.bv64, b.bv64, true) or not addNoUnderflow(a.bv64, b.bv64)
    of bSub: not subNoOverflow(a.bv64, b.bv64) or not subNoUnderflow(a.bv64, b.bv64, true)
    of bMul: not mulNoOverflow(a.bv64, b.bv64, true) or not mulNoUnderflow(a.bv64, b.bv64)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)
  else:
    raise newException(ValueError,
      "overflowCond: unexpected kind " & $a.kind)

proc lowerArith(a, b: SymVal, op: IRBinop): SymVal =
  ## CR-9(c) Stage C. Centralised arithmetic dispatch: exact copy of the
  ## `of bAdd,bSub,bMul,bDiv,bMod` arm body from `iekBinop` (~2707-2722).
  ## Same op-pair order; same signed/unsigned selection (via binBV/divBV/modBV).
  ## Additive — no call-site wired yet (Stage C).
  ##
  ## Round-6 B4: `reconcileInt(a, b)` at the top, MIRRORING `lowerCmp`'s own
  ## top-of-proc call — a mixed-representation pair (one operand `svInt`, the
  ## other `svBV*`) was previously IMPOSSIBLE to reach here (every `itInt`
  ## value shared one uniform representation, chosen once by
  ## `SymexSettings.integerSemantics`), so this arm never needed the bridge
  ## `lowerCmp` already carries. `IRParam.isIntOffset` (ADR-0027's recorded
  ## lift, B4's `collectIntOffsetParams`) is the first thing to promote a
  ## SINGLE top-level int param to `svInt` while its siblings (and any
  ## call-return placeholder allocated via the ordinary `allocateSym` itInt
  ## arm, which always chooses BV) stay BV — surfaced as a live crash
  ## (`FieldDefect: field 'bv64' is not accessible ... using 'kind =
  ## svInt'`) in `overflowCond`, which reads `b.bv64` unconditionally once
  ## its caller confirms only `a`'s kind/signedness. Reconciling FIRST closes
  ## the gap the same way `lowerCmp` already does for comparisons.
  var a = a
  var b = b
  (a, b) = reconcileInt(a, b)
  ##
  ## R16-3: for bDiv/bMod on non-float types, push `divisorIsZero(b)` to the
  ## `divByZeroConds` sink BEFORE dispatching. `arithInt`/`divBV`/`modBV` are
  ## unchanged; the cond fires from the pre-lower path in `drainDivByZeroRaises`.
  ## R16-4: for bAdd/bSub/bMul on signed BV operands, push `overflowCond(a,b,op)`
  ## to the `overflowConds` sink BEFORE dispatching. `binBV` is unchanged; the
  ## cond fires from the pre-lower path in `drainOverflowRaises`.
  if op in {bDiv, bMod} and a.kind notin {svFloat32, svFloat64}:
    let c = divisorIsZero(b)
    divByZeroConds.add c
    syncDivByZeroCond(c)
  if op in {bAdd, bSub, bMul} and a.kind in {svBV8, svBV16, svBV32, svBV64} and a.signed:
    let oc = overflowCond(a, b, op)
    overflowConds.add oc
    syncOverflowCond(oc)
  if a.kind == svInt:
    arithInt(a, b, op)
  elif a.kind in {svFloat32, svFloat64}:
    arithFloat(a, b, op)        # Phase 15 F3
  else:
    case op
    of bAdd: binBV(a, b, `+`)
    of bSub: binBV(a, b, `-`)
    of bMul: binBV(a, b, `*`)
    of bDiv: divBV(a, b)
    of bMod: modBV(a, b)
    else: raise newException(ValueError, "unreachable")

proc lowerCmp(a, b: SymVal, op: IRBinop): SymVal =
  ## CR-9(c) Stage C. Centralised comparison dispatch: exact copy of the
  ## inner dispatch body (after closureEq/refEq short-circuits) shared by the
  ## probe-hit comparison arm (~2618-2644) and probe-miss arm (~2656-2670).
  ## Calls `reconcileInt` at top (per the RFC plan) — the probe-hit arm had the
  ## inline equivalent; probe-miss arm had none (but kinds always matched there).
  ## Same op-pair order: bvslt,bvult; bvsle,bvule; bvsgt,bvugt; bvsge,bvuge.
  ## The closureEq / refEq short-circuits MUST remain in the call sites
  ## (they must `return` early and lowerCmp is not reached for those kinds).
  ## Additive — no call-site wired yet (Stage C).
  var (a, b) = reconcileInt(a, b)
  if a.kind == svInt and b.kind != svBool:
    cmpInt(a, b, op)
  elif a.kind == svBool or b.kind == svBool:
    # Bool ==/!= only. Phase 15 G7: a `static bool` literal arrives as an
    # int rep (`IntLit 0/1`); coerce both sides so e.g. `(x>0) == B` (B
    # baked to `IntLit 1`) compares bool-to-bool, not bool-to-int.
    let lb = coerceToBoolSV(a)
    let rb = coerceToBoolSV(b)
    case op
    of bEq: ofBool(lb.bo == rb.bo)
    of bNe: ofBool(lb.bo != rb.bo)
    else:
      raise newException(ValueError,
        "comparison op " & $op & " not valid on bool operands")
  elif a.kind in {svFloat32, svFloat64}:
    cmpFloat(a, b, op)        # Phase 15 F2: IEEE ==/!=; F4 adds ordering
  elif a.kind == svString:
    cmpString(a, b, op)       # Phase 15 S1: Z3 String ==/!= (S3 adds </<=)
  else:
    case op
    of bEq: eqBV(a, b)
    of bNe: neBV(a, b)
    of bLt: cmpBV(a, b, bvslt, bvult)
    of bLe: cmpBV(a, b, bvsle, bvule)
    of bGt: cmpBV(a, b, bvsgt, bvugt)
    of bGe: cmpBV(a, b, bvsge, bvuge)
    else: raise newException(ValueError, "unreachable")

include "runtime_strings.nim"  # Stage 8 CR-7 Cluster S: lowerStrArm

include "runtime_floats.nim"  # Stage 8 CR-7 Cluster F: lowerFloatArm

include "runtime_exceptions.nim"  # Stage 8 CR-7 Cluster E: lowerExnArm

include "runtime_closures.nim"  # Stage 8 CR-7 Cluster C: lowerClosureArm

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal =
  if e == nil:
    raise newException(ValueError, "lower: nil expression")
  case e.kind
  of iekIntLit:
    if proto.isSome and proto.get.kind != svBool:
      coerceIntLit(proto.get, e.ival)
    else:
      bvConst(tInt(64, true), e.ival)
  of iekFloatLit, iekConvIntToFloat, iekConvFloatToInt, iekMathCall:
    # Stage 7 (CR-7) Cluster F: float literal, int→float, float→int, math
    # arms extracted into `lowerFloatArm` (defined above, before this proc body).
    lowerFloatArm(env, e)
  of iekConvIntWidth:
    # Round-6 B2: WIDENING-only int-family width conversion.
    lowerConvIntWidth(lower(env, e.ciwOperand), e.ciwTgtWidth, e.ciwTgtSigned)
  of iekBoolLit:
    ofBool(mkBool(e.bval))
  of iekVar:
    env[e.vname]
  of iekField:
    # Lower the receiver, then pick the field by index (tuple) or
    # by name (variant — Phase 11).
    let recv = lower(env, e.obj)
    case recv.kind
    of svTuple:
      recv.fields[e.fieldIx]
    of svVariant:
      # iekField on a variant: discriminator or plain (shared)
      # field. Arm-specific access takes the `isVariantField`
      # statement-level path (parser A-normalises so the walker
      # can fork). Any arm-field that reaches here is a parser
      # bug — fail loud.
      if e.fieldName == recv.vDiscName:
        recv.vDisc[]
      elif e.fieldName in recv.vPlainFieldNames:
        let ix = recv.vPlainFieldNames.find(e.fieldName)
        recv.vPlainFields[ix]
      else:
        raise newException(ValueError,
          "symex Phase 11: arm-specific field `" & e.fieldName &
          "` reached lower(iekField) on svVariant — parser should " &
          "have A-normalised this through isVariantField")
    of svMultiVariant:
      # Phase 14 cycle A1d. Same contract as svVariant: only the
      # per-axis discriminators and the (shared) plain fields are
      # legal here; arm-specific access is parser-routed through
      # `isVariantField`. Plain fields are matched first because
      # they're shared across all axes.
      if e.fieldName in recv.mvPlainFieldNames:
        let ix = recv.mvPlainFieldNames.find(e.fieldName)
        recv.mvPlainFields[ix]
      else:
        var found: SymVal
        var hit = false
        for ax in recv.mvAxes:
          if e.fieldName == ax.discName:
            found = ax.disc[]; hit = true; break
        if hit: found
        else:
          raise newException(ValueError,
            "symex Phase 14: arm-specific field `" & e.fieldName &
            "` reached lower(iekField) on svMultiVariant — parser " &
            "should have A-normalised this through isVariantField")
    else:
      raise newException(ValueError,
        "iekField on unsupported SymVal kind=" & $recv.kind)
  of iekSeqLen:
    let recv = lower(env, e.lenObj)
    case recv.kind
    of svSeq:   SymVal(kind: svInt, zi: recv.seqLen)
    of svTable: SymVal(kind: svInt, zi: recv.tabSize)
    of svSet:   SymVal(kind: svInt, zi: recv.setSize)
    of svString:
      # Round-6 B1 (ADR-0028 Leg 1) totality backstop: a string-backed
      # `seq[byte]` param's `.len` reaching here with an `svString`
      # receiver — SND-4 mirror of `iekStrLen`'s lowering
      # (`runtime_strings.nim`), same byte-faithful `str.len` read. Makes
      # `data.len` WORK (not merely decline) even through a call-chain hop
      # whose OWN parse never routed the dispatch through `iekStrLen`.
      SymVal(kind: svInt, zi: len(recv.str))
    else:
      # Round-6 B1 backstop: was a bare `ValueError` (a live crash gap) —
      # a mis-classified receiver now declines classified instead of
      # crashing (SND-4 mirror: the existing generic
      # `SymexClassifiedDegradeError` carrier, CR-1c/CR-2b precedent).
      let locPrefix = if e.lenLoc.len > 0: e.lenLoc & ": " else: ""
      raise (ref SymexClassifiedDegradeError)(
        kind: feUnsupportedExprKind,
        msg: locPrefix & "iekSeqLen: unsupported receiver kind " &
             $recv.kind & " (expected seq/table/set/string) — degraded " &
             "to sxUnknown (feUnsupportedExprKind)")
  of iekSeqSlice:
    # v67 (dev item 1): seq-slice VALUE as an ARRAY-LAMBDA VIEW — the
    # lowered svSeq is `{len: hi - lo + 1, data: (lambda (i) (select base
    # (+ i lo)))}` (see the IR kind's doc, types.nim). Element-sort-GENERIC
    # (raw `Z3_mk_select`/`Z3_mk_lambda_const` — the base's array raw is
    # used untyped); Z3 beta-reduces selects over the lambda natively, so
    # downstream `isIndex`/`iekSeqLen` need no changes. Copy semantics come
    # free: the lambda closes over the base's array AST AT SLICE TIME.
    let recv = lower(env, e.ssBase)
    if recv.kind != svSeq:
      raise (ref SymexClassifiedDegradeError)(
        kind: feUnsupportedOp,
        msg: "iekSeqSlice: base lowered to " & $recv.kind &
             " — expected svSeq (→ sxUnknown, Invariant 3)")
    # ADR-0027 bound discipline: svInt proto so literals/adaptables arrive
    # Int-sorted; a genuinely BV-allocated bound would bv2int-bridge — the
    # empirical Z3 non-termination shape — and declines classified.
    let intProto = some(SymVal(kind: svInt, zi: mkInt(0)))
    let loSV = lower(env, e.ssLo, intProto)
    let hiSV = lower(env, e.ssHi, intProto)
    if loSV.kind != svInt or hiSV.kind != svInt:
      raise (ref SymexClassifiedDegradeError)(
        kind: feUnsupportedOp,
        msg: "iekSeqSlice: slice bound lowered as " & $loSV.kind & "/" &
             $hiSV.kind & " — a bitvector-represented bound would " &
             "bv2int-bridge into the array query (ADR-0027 non-termination " &
             "class; bounds from find/len/literals prove) " &
             "(→ sxUnknown, Invariant 3)")
    let lo = loSV.zi
    let hi = hiSV.zi
    # A real Nim slice raises IndexDefect outside `lo >= 0 ∧ hi < len ∧
    # lo <= hi + 1` (the last conjunct admits the empty slice). Deposit the
    # OOB predicate into the SND-4 sink — `drainStrIndexRaises` routes an
    # IndexDefect fork at the statement boundary; the sink is string-NAMED
    # but its routed defect type is exactly right for container slices too.
    # The view below is only ever OBSERVED on the in-bounds survivor path.
    let lenZ = recv.seqLen
    let ok = (lo >= mkInt(0)) and (hi < lenZ) and (lo <= hi + mkInt(1))
    when not defined(symexSliceNoOobFork):
      strIndexOobConds.add (not ok)
      syncStrIndexOobCond(not ok)
    inc sliceViewCounter
    let zctx = recv.seqDataRaw.ctx
    let iVar = mkIntVar("__sliceview_i" & $sliceViewCounter)
    let shifted = iVar + lo
    # OWNERSHIP DISCIPLINE (hard-won): under a refcounting Z3 context an
    # rc-0 node returned by one API call MAY BE FREED BY THE NEXT CALL.
    # The select node was previously left raw (rc 0) across `Z3_to_app`
    # and `Z3_mk_lambda_const` — a use-after-free that corrupted the AST
    # heap and surfaced as a SIGSEGV inside `Z3_dec_ref` at scope
    # teardown, memory-timing-dependent (the SAT path happened to
    # survive; the first non-SAT query died). Every intermediate is now
    # wrapped (inc_ref'd) IMMEDIATELY on creation.
    let sel = wrap[Z3AnyAst](zctx,
      zctx.checkErr Z3_mk_select(zctx.raw, recv.seqDataRaw.raw, shifted.raw))
    var iApp = zctx.checkErr Z3_to_app(zctx.raw, iVar.raw)
    let lam = wrap[Z3AnyAst](zctx,
      zctx.checkErr Z3_mk_lambda_const(zctx.raw, 1'u32,
        cast[ptr UncheckedArray[RawZ3App]](addr iApp), sel.raw))
    SymVal(kind: svSeq,
           seqLen: (hi - lo) + mkInt(1),
           seqDataRaw: lam,
           seqElemTy: recv.seqElemTy)
  of iekStrLit, StrOpKinds:
    # Stage 7 (CR-7) Cluster S: all string literal and string-op arms are
    # extracted into `lowerStrArm` (defined above, before this proc body).
    lowerStrArm(env, e)
  of iekGetCurrentExnMsg, iekGetCurrentExn:
    # Stage 7 (CR-7) Cluster E: exception expression arms extracted into
    # `lowerExnArm` (defined above, before this proc body).
    lowerExnArm(env, e)
  of iekSeqAdd:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSeq, "iekSeqAdd: receiver not svSeq"
    let val = lower(env, e.mutArg)
    # New seq: data = store(old.data, old.len, val); len = old.len + 1
    let oldLen = recv.seqLen
    let newLen = oldLen + mkInt(1)
    var newDataRaw: Z3AnyAst
    case recv.seqElemTy.kind
    of itInt:
      case recv.seqElemTy.width
      of 64:
        let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
          recv.seqDataRaw.ctx, recv.seqDataRaw.raw)
        let vbv = case val.kind
          of svBV64: val.bv64
          of svInt:  mkBitVec[64](0'i64)  ## fallback (shouldn't happen)
          else: mkBitVec[64](0'i64)
        let stored = store(typed, oldLen, vbv)
        newDataRaw = toAnyAst(stored)
      else:
        raise newException(ValueError,
          "iekSeqAdd: unsupported width " & $recv.seqElemTy.width)
    of itBool:
      let typed = wrap[Z3Array[Z3Int, Z3Bool]](
        recv.seqDataRaw.ctx, recv.seqDataRaw.raw)
      doAssert val.kind == svBool
      newDataRaw = toAnyAst(store(typed, oldLen, val.bo))
    else:
      raise newException(ValueError,
        "iekSeqAdd: unsupported elem " & $recv.seqElemTy.kind)
    SymVal(kind: svSeq, seqLen: newLen,
           seqDataRaw: newDataRaw, seqElemTy: recv.seqElemTy)
  of iekTableSet:
    let recv = lower(env, e.tabRecv)
    doAssert recv.kind == svTable
    let keyProto = SymVal(kind: svString, str: mkString(""))
    let keySV = lower(env, e.tabKey, some(keyProto))
    doAssert keySV.kind == svString
    let val = lower(env, e.tabVal)
    # New table: data = store(old.data, k, v); present = store(old.present, k, true).
    # Size: increment if !present[k] before.
    case recv.tabValTy.kind
    of itInt:
      let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
        recv.tabDataRaw.ctx, recv.tabDataRaw.raw)
      let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
        recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
      let vbv = case val.kind
        of svBV64: val.bv64
        else: mkBitVec[64](0'i64)
      let newData = store(typedData, keySV.str, vbv)
      let newPresent = store(typedPresent, keySV.str, mkBool(true))
      let wasPresent = select(typedPresent, keySV.str)
      # size += 1 if !wasPresent
      let newSize = SymVal(kind: svInt,
        zi: ite(wasPresent, recv.tabSize, recv.tabSize + mkInt(1)))
      SymVal(kind: svTable,
        tabDataRaw: toAnyAst(newData),
        tabPresentRaw: toAnyAst(newPresent),
        tabSize: newSize.zi,
        tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
    else:
      raise newException(ValueError,
        "iekTableSet: unsupported val " & $recv.tabValTy.kind)
  of iekTableDel:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svTable
    let keyProto = SymVal(kind: svString, str: mkString(""))
    let keySV = lower(env, e.mutArg, some(keyProto))
    let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
      recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
    let wasPresent = select(typedPresent, keySV.str)
    let newPresent = store(typedPresent, keySV.str, mkBool(false))
    let newSize = ite(wasPresent, recv.tabSize - mkInt(1), recv.tabSize)
    SymVal(kind: svTable,
      tabDataRaw: recv.tabDataRaw,
      tabPresentRaw: toAnyAst(newPresent),
      tabSize: newSize,
      tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
  of iekSetIncl:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSet
    let elem = lower(env, e.mutArg)
    doAssert elem.kind == svBV64
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    let wasMember = select(typed, elem.bv64)
    let newMembers = store(typed, elem.bv64, mkBool(true))
    let newSize = ite(wasMember, recv.setSize, recv.setSize + mkInt(1))
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSetExcl:
    let recv = lower(env, e.mutRecv)
    doAssert recv.kind == svSet
    let elem = lower(env, e.mutArg)
    doAssert elem.kind == svBV64
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    let wasMember = select(typed, elem.bv64)
    let newMembers = store(typed, elem.bv64, mkBool(false))
    let newSize = ite(wasMember, recv.setSize - mkInt(1), recv.setSize)
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSeqDel, iekSeqInsert, iekSeqPop:
    raise newException(ValueError,
      "Phase 5+: " & $e.kind & " lowering arrives with #143 follow-up")
  of iekContains:
    let recv = lower(env, e.container)
    case recv.kind
    of svTable:
      let keyProto = SymVal(kind: svString, str: mkString(""))
      let keySV = lower(env, e.key, some(keyProto))
      doAssert keySV.kind == svString
      let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
        recv.tabPresentRaw.ctx, recv.tabPresentRaw.raw)
      ofBool(select(typedPresent, keySV.str))
    of svSet:
      # For HashSet[int]: key is BV[64]; select(members, key) → Bool.
      # Phase 16 INV: non-int64 element types (e.g. set[char] / HashSet[uint8])
      # are not modeled — classify rather than crash (seUnsupportedSetCharInterop).
      # SND-3 (ADR-0023, walker v58): degrade IN-BAND (never `raise`) — this
      # arm is inside `lower`, reachable evaluating `x in mySet` inside a loop
      # guard, the same C-backend silent-loss hazard as the CR-17(a) site
      # above. See `loweringDidDegrade`'s doc comment for the full mechanism.
      if recv.setElemTy.kind != itInt or recv.setElemTy.width != 64:
        loweringDegradeErrors.add SymexErrorInfo(
          kind: seUnsupportedSetCharInterop, severity: sevError,
          msg: "set[char] / HashSet membership not modeled — element type " &
               $recv.setElemTy & " (width " & $recv.setElemTy.width &
               " != 64) (seUnsupportedSetCharInterop)")
        loweringDidDegrade = true
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), "__setContainsDegrade", fresh)
      let bv64Proto = SymVal(kind: svBV64, signed: true,
                             bv64: mkBitVec[64](0'i64))
      var keySV = lower(env, e.key, some(bv64Proto))
      # v64 (sibling audit, chapulin catalog #3 class): an svInt key is a
      # LEGITIMATE arrival — `.len`/`.find`/`parseInt` results lower
      # unconditionally to svInt (CR-1a), so `s.len in myIntSet` reached the
      # former `doAssert keySV.kind == svBV64` and native-crashed. Bridge
      # svInt→BV64 via `svIntToBV` (CR-1a precedent); anything else degrades
      # IN-BAND per SND-3 instead of asserting.
      if keySV.kind == svInt:
        keySV = svIntToBV(keySV, svBV64)
      if keySV.kind != svBV64:
        loweringDegradeErrors.add SymexErrorInfo(
          kind: weInternalWalkerFault, severity: sevError,
          msg: "HashSet membership key lowered to " & $keySV.kind &
               " — expected svBV64 (weInternalWalkerFault)")
        loweringDidDegrade = true
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), "__setKeyDegrade", fresh)
      # v65: record the key TERM for witness extraction (see
      # `setMembershipKeyTerms` — a symbolically-keyed membership can be
      # satisfied by a const-true model array, leaving nothing else to
      # enumerate the witness from).
      setMembershipKeyTerms.mgetOrPut(
        cast[uint](recv.setMembersRaw.raw), @[]).add toAnyAst(keySV.bv64)
      let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
        recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
      ofBool(select(typed, keySV.bv64))
    else:
      raise newException(ValueError,
        "iekContains on unsupported kind " & $recv.kind)
  of iekArrayLit:
    # Lower each element with a prototype matching the declared
    # element type. The first element's lowered SymVal becomes the
    # prototype for the rest (and for the array's SymVal kind).
    var elems: seq[SymVal]
    # Build a prototype SymVal from elemTy. For primitive types this
    # is a constant-zero SymVal of the right kind, used only for its
    # `kind`/`signed` shape via coerceIntLit.
    var protoSV: Option[SymVal] = none(SymVal)
    if e.lelemTy.kind == itInt:
      protoSV = some(bvConst(e.lelemTy, 0))
    elif e.lelemTy.kind == itBool:
      protoSV = some(ofBool(mkBool(false)))
    for c in e.lelems:
      elems.add lower(env, c, protoSV)
    SymVal(kind: svArray, arrElems: elems, arrElemTy: e.lelemTy)
  of iekIndex:
    let recv = lower(env, e.arr)
    doAssert recv.kind == svArray,
      "iekIndex on non-array kind=" & $recv.kind
    if e.idx.kind == iekIntLit:
      # Fast path: concrete index. No fork; direct element lookup.
      let ix = int(e.idx.ival)
      if ix < 0 or ix >= recv.arrElems.len:
        raise newException(ValueError,
          "Phase 4: literal index " & $ix & " out of bounds 0..<" &
          $recv.arrElems.len)
      recv.arrElems[ix]
    else:
      # Symbolic index: ite-chain over each element. Z3 picks an i.
      # The "default" branch (i below first match) falls through to
      # element[0] — for OOB-handling cycle 8, the OOB path forks
      # before this point and adds the OOB constraint to its pc.
      let idxSV = lower(env, e.idx)
      doAssert recv.arrElems.len > 0
      var res = recv.arrElems[0]
      for k in 1 ..< recv.arrElems.len:
        let kSV = coerceIntLit(idxSV, int64(k))
        let cond = symEq(idxSV, kSV)
        res = iteSV(cond, recv.arrElems[k], res)
      res
  of iekUnop:
    case e.uop
    of uNeg:
      # CR-9(c) Stage E audit: this svInt/float/BV dispatch is a UNARY negation,
      # not an arith/cmp ladder — lowerArith/lowerCmp do not cover unary ops.
      # Left inline (no helper captures one-operand form).
      let inner = ejectBase(lower(env, e.operand, proto))   ## Phase 15 G4
      if inner.kind == svInt: SymVal(kind: svInt, zi: -inner.zi)
      elif inner.kind == svFloat32: SymVal(kind: svFloat32, fp32: -inner.fp32)  # Phase 15 F3
      elif inner.kind == svFloat64: SymVal(kind: svFloat64, fp64: -inner.fp64)  # Phase 15 F3
      else: negBV(inner)
    of uNot:
      let inner = lower(env, e.operand, some(ofBool(mkBool(true))))
      # v64 (chapulin catalog #3 residual): this arm used to be
      # `doAssert inner.kind == svBool` — an UNCAUGHT AssertionDefect (native
      # crash) whenever a non-bool operand arrived. Two legitimate non-bool
      # arrivals exist: (a) Nim's prefix `not` on an INT operand is the
      # bitwise complement (the parser emits uNot for both spellings), for
      # which `notBV` is the faithful lowering; (b) any other kind is a
      # mis-typed lowering upstream — degrade IN-BAND per SND-3 (ADR-0023):
      # this arm is inside `lower`, so a `raise` here risks the C-backend
      # silent-loss hazard (b7258f7/CR-1c class). Taint via the threadvar
      # sinks and return a fresh unconstrained bool so the walk continues
      # soundly (the path is marked uncertain — no false sxSat possible).
      case inner.kind
      of svBool:
        ofBool(not inner.bo)
      of svBV8, svBV16, svBV32, svBV64:
        notBV(inner)
      else:
        loweringDegradeErrors.add SymexErrorInfo(
          kind: weInternalWalkerFault, severity: sevError,
          msg: "uNot on unsupported operand kind " & $inner.kind &
               " — expected svBool or a BV (weInternalWalkerFault)")
        loweringDidDegrade = true
        var fresh: seq[Z3Bool]
        allocateSym(tBool(), "__uNotDegrade", fresh)
  of iekBinop:
    case e.bop
    # ---- comparison ops always produce Bool; operand repr from probe ----
    of bEq, bNe, bLt, bLe, bGt, bGe:
      # CR-17(a) DEFENSIVE: an ORDERING goal (`<`/`<=`/`>`/`>=`) where one
      # operand is `iekStrAt` (a char read: `s[i]`) would lower the char to
      # `svBV8` wrapping `int2bv(toCode(at(s,i)))` — a mix of Z3 string and
      # BV theories in a single ordering query. Z3 can struggle with this
      # mixed-theory ordering shape (the F5 pathology variant: String+Int+BV).
      # This guard classifies sxUnknown (honest) rather than risking a hang.
      # Equality (`==`/`!=`) is NOT guarded: BV8 equality over string-char
      # terms is decidable (Z3 string theory handles it; tested in S3).
      #
      # SND-3 (ADR-0023, walker v58): degrade IN-BAND, never `raise`. A raise
      # here would unwind through the enclosing loop's live `seq[Path]` and be
      # silently lost on the C backend's goto-exception model (b7258f7/CR-1c
      # class) — the walk would continue with a mis-lowered guard, producing a
      # false `sxUnsat` on c vs. the honest `sxUnknown` on cpp. Instead: taint
      # via the threadvar sinks (consumed by `drainPendingLowerEffects`, which
      # forks the PATH's `uncertain = true` — SND-1's per-path taint — so a
      # false `sxSat` on the tainted path is impossible) and return a fresh
      # unconstrained bool so evaluation can continue soundly.
      if e.bop in {bLt, bLe, bGt, bGe} and
         (e.lhs.kind == iekStrAt or e.rhs.kind == iekStrAt):
        loweringDegradeErrors.add SymexErrorInfo(kind: seUnsupportedStringOp,
          severity: sevError,
          msg: "ordering comparison on s[i] (char) is not modeled " &
               "(CR-17: String+Int+BV ordering — latent Z3 hang shape; " &
               "use == / != for char comparisons)")
        loweringDidDegrade = true
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), "__strCmpOrderingDegrade", fresh)
      let pp = probeProto(env, e)
      if pp.isSome:
        var l = ejectBase(lower(env, e.lhs, pp))   ## Phase 15 G4: distinct→base
        var r = ejectBase(lower(env, e.rhs, pp))
        # Phase 15 C5: closure ==/!= (nominal-for-site + structural-for-env,
        # ADR-0009 D7). ejectBase passes svClosure through unchanged.
        # MUST return before lowerCmp (short-circuit; lowerCmp has no closure branch).
        if l.kind == svClosure and r.kind == svClosure:
          return closureEq(l, r, e.bop)
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        # MUST return before lowerCmp (short-circuit; lowerCmp has no ref/ptr branch).
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        # CR-9(c) D2: delegate to lowerCmp (reconcileInt + dispatch).
        lowerCmp(l, r, e.bop)
      else:
        # No env-resident var via probe — but the lowered LHS might
        # still be svInt (e.g. `iekSeqLen`). Re-dispatch on its kind.
        let l = ejectBase(lower(env, e.lhs, none(SymVal)))   ## Phase 15 G4
        let r = ejectBase(lower(env, e.rhs, some(l)))
        # Phase 15 C5: closure ==/!= (ADR-0009 D7); probe-miss branch.
        # MUST return before lowerCmp (short-circuit).
        if l.kind == svClosure and r.kind == svClosure:
          return closureEq(l, r, e.bop)
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        # MUST return before lowerCmp (short-circuit).
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        # CR-9(c) D3: delegate to lowerCmp.  reconcileInt is a no-op when
        # kinds match (probe-miss: both sides lowered without width steering).
        lowerCmp(l, r, e.bop)
    # ---- boolean / bitwise dispatch by operand type ----
    of bAnd, bOr, bXor:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, pp)
      if l.kind == svBool:
        doAssert r.kind == svBool
        case e.bop
        of bAnd: ofBool(l.bo and r.bo)
        of bOr:  ofBool(l.bo or  r.bo)
        of bXor: ofBool(l.bo xor r.bo)
        else: raise newException(ValueError, "unreachable")
      elif l.kind == svInt:
        # CR-1a: `l` is a Z3 Int — always from `.len`/`.find`/`.indexOf`/
        # `parseInt` (these are UNCONDITIONALLY svInt; there is no
        # BV-vs-Int promotion choice for them to have "declined", unlike
        # a plain symbolic var). Z3's Int theory has no bitwise operators,
        # so bridge both operands to BV via `int2bv` (matching `r`'s width
        # when `r` is already BV; defaulting to BV64 — Nim's native `int`
        # width — when `r` is also svInt, e.g. an int-literal RHS) and
        # dispatch through the existing `binBV` machinery. This replaces
        # the former native crash with a correctly-modeled bitwise op.
        let targetKind =
          if r.kind in {svBV8, svBV16, svBV32, svBV64}: r.kind else: svBV64
        let lb = svIntToBV(l, targetKind)
        let rb = if r.kind == svInt: svIntToBV(r, targetKind) else: r
        case e.bop
        of bAnd: binBV(lb, rb, `and`)
        of bOr:  binBV(lb, rb, `or`)
        of bXor: binBV(lb, rb, `xor`)
        else: raise newException(ValueError, "unreachable")
      else:
        case e.bop
        of bAnd: binBV(l, r, `and`)
        of bOr:  binBV(l, r, `or`)
        of bXor: binBV(l, r, `xor`)
        else: raise newException(ValueError, "unreachable")
    # ---- bit shifts (always BV; cycle 8 ban list applies) ----
    of bShl, bShr:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, some(l))
      doAssert l.kind notin {svInt, svBool},
        "shift on promoted Z3Int — abstraction should have declined"
      case e.bop
      of bShl: binBV(l, r, `shl`)
      of bShr: shrBV(l, r)
      else: raise newException(ValueError, "unreachable")
    # ---- arithmetic — all preserve representation ----
    of bAdd, bSub, bMul, bDiv, bMod:
      let pp = probeProto(env, e)
      let l = ejectBase(lower(env, e.lhs, pp))   ## Phase 15 G4: distinct→base
      let r = ejectBase(lower(env, e.rhs, pp))
      lowerArith(l, r, e.bop)
  of iekBorrowOp:
    # Phase 15 G5. A `{.borrow.}` operator on a `distinct T`: EJECT both operands
    # to their base SymVals (G4's `distinctBaseSym`, via `ejectBase`), apply the
    # BASE operator, and either RE-BOX (arithmetic) or return the raw bool
    # (comparison). This works on the boxed base value — it does NOT build the
    # Z3 `inject_T(eject_T(a) op eject_T(b))` function-application chain, which
    # HANGS (uninterpreted-fn-over-BV / MBQI; the G4 finding). The eject-pin from
    # G4 ties each operand's dConst to its base, so the base op is sound.
    let l = ejectBase(lower(env, e.borrowLhs))
    let r = ejectBase(lower(env, e.borrowRhs))
    case e.borrowOp
    of bEq, bNe, bLt, bLe, bGt, bGe:
      # Comparison borrow → raw svBool from the base comparison.
      # CR-9(c) D4: delegate to lowerCmp (same dispatch as iekBinop arms).
      # ejectBase already applied to l+r above; no closureEq/refEq in
      # borrow context (base types are never svClosure/svRef/svPtr).
      lowerCmp(l, r, e.borrowOp)
    of bAdd, bSub, bMul, bDiv, bMod:
      # Arithmetic borrow → apply the base op, then re-box as the distinct type.
      # CR-9(c) D4: delegate to lowerArith; preserve ejectBase (above) +
      # reboxDistinct wrap (below).
      let baseRes = lowerArith(l, r, e.borrowOp)
      if e.borrowReturnsDistinct:
        reboxDistinct(e.borrowDistinctName, baseRes)
      else:
        baseRes
    else:
      raise newException(ValueError,
        "borrow: unsupported base operator " & $e.borrowOp)
  of iekLambda, iekClosureCall:
    # Stage 7 (CR-7) Cluster C: closure construction and application arms
    # extracted into `lowerClosureArm` (defined above, before this proc body).
    lowerClosureArm(env, e)
  of iekSeqLit:
    # Phase 15 C4. A concrete seq literal `@[a, b, c]` → a CONCRETE-length
    # svSeq: store each lowered element at its index in a fresh data array, and
    # pin `seqLen` to the literal count (a numeral). The empty `@[]` yields a
    # length-0 svSeq. Concrete length is what lets a downstream HOF inline.
    lowerSeqLit(env, e)
  of iekTupleLit:
    # RFC-chapulin-hardening P1. General N-ary tuple constructor `(a,b,c)` /
    # named `(x:a,y:b)` → svTuple, extracted to `lowerTupleLit` (mirrors the
    # iekSeqLit extraction precedent).
    lowerTupleLit(env, e)
  of iekVariantLit:
    # Round-6 A1 (ADR-0029). Literal-discriminant variant constructor →
    # svVariant, extracted to `lowerVariantLit` (mirrors the `lowerTupleLit`
    # extraction precedent).
    lowerVariantLit(env, e)
  of iekHofCall:
    # Phase 15 C4 (ADR-0009). DSL higher-order call. Selects the INLINE path
    # (concrete length ≤ seqInlineThreshold; unroll the closure per element,
    # quantifier-free) or the AXIOM path (symbolic length: map → `mapArray`;
    # fold → raw `Z3_mk_app`; filter → `ceUnsupportedHof`, Phase-16 deferred).
    # Uses `walk` via `currentWalkCtxPtr`, so the body lives after `walk`.
    lowerHofCall(env, e)
  of iekNil:
    # Phase 15 R5 (Cluster R, ADR-0010). The `nil` ref/ptr literal. Lower it to an
    # `svRef`/`svPtr` carrying the per-sort distinguished `nilConst` (`nil_<typeId>`,
    # allocated + cached by `allocRefSort`). `nilPointee` is the FULL `itRef`/`itPtr`
    # type of the ref/ptr `nil` is compared against; key the sort on its POINTEE
    # (matching `isNew`/`allocateSym`). `refEq` then decides `p == nil` as a ground
    # equality of the two `Ref_T` consts.
    let ctx = requireCurrentContext()
    let isPtr = e.nilPointee.kind == itPtr
    let pointee = if isPtr: e.nilPointee.ptrPointeeTy else: e.nilPointee.refPointeeTy
    discard allocRefSort(ctx, pointee)        ## ensure the sort + nilConst exist
    let typeId = refPointeeTypeId(pointee)
    let nilAst = currentNilConsts[typeId]
    if isPtr:
      SymVal(kind: svPtr, ptrAst: nilAst, ptrFamily: true, ptrPointee: pointee)
    else:
      SymVal(kind: svRef, refAst: nilAst, refPointee: pointee)

proc lowerBool(env: Env, e: IRExpr): Z3Bool =
  let sv = lower(env, e, some(ofBool(mkBool(true))))
  # v64 (sibling audit of the uNot arm's crash class, chapulin catalog #3):
  # this was `doAssert sv.kind == svBool` — the guard-path chokepoint every
  # mis-typed boolean lowering funnels through, and an uncaught
  # AssertionDefect (native crash) when hit. Degrade IN-BAND per SND-3
  # (ADR-0023): taint via the threadvar sinks and hand back a fresh
  # unconstrained bool — the path is marked uncertain, so no false sxSat.
  if sv.kind == svBool:
    sv.bo
  else:
    loweringDegradeErrors.add SymexErrorInfo(
      kind: weInternalWalkerFault, severity: sevError,
      msg: "lowerBool: expected Bool, got " & $sv.kind &
           " (weInternalWalkerFault)")
    loweringDidDegrade = true
    var fresh: seq[Z3Bool]
    allocateSym(tBool(), "__lowerBoolDegrade", fresh).bo

# ---- Path / solve / walk ----------------------------------------------------

var extractionErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 F7. Accumulator for eval-side extraction failures. `extractLeaf`
  ## appends a `feExtractionFailed` record here when a SAT-model float AST
  ## fails to resolve to a concrete numeral even under `modelCompletion=true`
  ## (should not happen — Invariant: a SAT model completes every leaf). Reset
  ## at `runSymex` entry; drained into the returned `RawResult.errors` on a
  ## sat finding. A threadvar avoids plumbing a `var seq` through the whole
  ## extract recursion (extractLeaf -> extractFromSymVal -> extractWitness).

var unknownExnWarnings* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 E4. Accumulator for `eeUnknownExnType` warnings (sevWarning):
  ## a raised exception type not in `exnTypeTable` nor `userExnHierarchy`.
  ## Such a type is matched conservatively against a bare `except:` ONLY (no
  ## silent false-negative — Invariant 3) and the warning records the type
  ## name. Reset at `runSymex` entry; drained into the returned
  ## `RawResult.errors`. A threadvar avoids plumbing a `var seq` through the
  ## handler-search recursion (routeRaise is called both inline and from the
  ## isCall inter-proc arm).

proc evalStrBytes(m: Z3Model, a: Z3String): string =
  ## Round-6 B4-rider: byte-faithful replacement for nim-z3's `evalStr`
  ## (`m.eval(a).toStr`, which wraps `Z3_get_lstring`). Isolated repro
  ## (bypassing all of nelli, direct `_deps/z3` calls only) proved
  ## `Z3_get_lstring` itself — not nim-z3's binding, not anything in this
  ## file — mis-renders any string containing a byte it treats as needing
  ## SMT-LIB escaping (embedded NUL confirmed; also backslash, quote, and
  ## low/high bytes < 0x20 / >= 0x7f): instead of the raw byte it returns
  ## the LITERAL TEXT of that byte's escape spelling (`\u{0}` = 5 chars for
  ## one NUL byte), and the reported length grows to match — so callers
  ## can't detect the corruption from the length alone. `getStringLength`/
  ## `getStringContents` (`Z3_get_string_length`/`Z3_get_string_contents`,
  ## already bound in `z3/strings`, re-exported through `import z3`) are a
  ## SEPARATE Z3 API returning raw Unicode codepoints; the same repro
  ## confirmed it round-trips every tested byte correctly, both on a bare
  ## literal AST and on a solver-model evaluation. Every `itString` free
  ## variable nelli ever allocates is constrained to `(re.range '\x00'
  ## '\xff')*` (see the `itString` arm above, Phase 15 S3/ADR-0006), so
  ## every codepoint here is guaranteed in `[0, 255]` and maps 1:1 to a
  ## Nim byte — the `raise` below is an assertion on that standing
  ## invariant, not a real runtime path.
  let ev = m.eval(a, modelCompletion = true)
  let codepoints = getStringContents(ev)
  result = newString(codepoints.len)
  for i, cp in codepoints:
    if cp < 0 or cp > 255:
      raise newException(ValueError,
        "evalStrBytes: model codepoint " & $cp & " at index " & $i &
        " outside nelli's byte-string invariant [0, 255]")
    result[i] = char(cp)

proc extractLeaf(m: Z3Model, w: var RawWitness, path: string, sv: SymVal) =
  ## Populate the flat witness tables for a primitive SymVal at the
  ## given path. Tuple/array roots recurse via `extractFromSymVal`.
  case sv.kind
  of svUninterpRef: discard  ## opaque ref — no witness leaf (hint recorded in cluster E)
  of svFloat64:
    # Phase 15 F7: bit-exact extraction. NaN is handled first because
    # Z3's `Z3_mk_fpa_to_ieee_bv` on a NaN is *unspecified* — it does not
    # fold to a numeral, so `evalFloat64Opt` would (correctly) return `none`
    # and lose the NaN. We instead ask the model whether the value is NaN via
    # the `isNaN` FP predicate and emit Nim's canonical NaN (ADR-0005: a
    # single canonical NaN, no payload distinctions). All other values —
    # ±Inf, ±0, normals, subnormals — extract losslessly through
    # `evalFloat64Opt(a, modelCompletion = true)`, whose explicit
    # modelCompletion forces any Z3_mk_select-derived AST to a concrete numeral.
    if m.evalBool(isNaN(sv.fp64), modelCompletion = true):
      w.float64Vals[path] = NaN
    else:
      let opt = m.evalFloat64Opt(sv.fp64, modelCompletion = true)
      if opt.isSome:
        w.float64Vals[path] = opt.get
      else:
        let exErr64 = SymexErrorInfo(kind: feExtractionFailed, severity: sevError,
          msg: "float64 witness at '" & path & "' did not resolve to a concrete numeral")
        extractionErrors.add exErr64     # threadvar: fallback
        syncExtractionError(exErr64)     # CR-9 Stage 5: LIVE WalkCtx field
        w.float64Vals[path] = 0.0
  of svFloat32:
    if m.evalBool(isNaN(sv.fp32), modelCompletion = true):
      w.float32Vals[path] = float32(NaN)
    else:
      let opt = m.evalFloat32Opt(sv.fp32, modelCompletion = true)
      if opt.isSome:
        w.float32Vals[path] = opt.get
      else:
        let exErr32 = SymexErrorInfo(kind: feExtractionFailed, severity: sevError,
          msg: "float32 witness at '" & path & "' did not resolve to a concrete numeral")
        extractionErrors.add exErr32     # threadvar: fallback
        syncExtractionError(exErr32)     # CR-9 Stage 5: LIVE WalkCtx field
        w.float32Vals[path] = 0.0'f32
  of svBool: w.boolVals[path] = m.evalBool(sv.bo)
  of svBV8:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv8))
    else:         w.uintVals[path] = m.evalUint(sv.bv8)
  of svBV16:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv16))
    else:         w.uintVals[path] = m.evalUint(sv.bv16)
  of svBV32:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv32))
    else:         w.uintVals[path] = m.evalUint(sv.bv32)
  of svBV64:
    if sv.signed: w.intVals[path] = int64(m.evalInt(sv.bv64))
    else:         w.uintVals[path] = m.evalUint(sv.bv64)
  of svInt:
    let v = int64(m.evalInt(sv.zi))
    w.intVals[path] = v
    # Phase 14 A6: a promoted variant discriminator lands in svInt
    # but the witness reader for its underlying `itInt(unsigned)`
    # disc type reads from `uintVals`. Mirror into both maps so
    # whichever reader path the emitter picks finds the value.
    if v >= 0: w.uintVals[path] = uint64(v)
  of svString:
    w.strVals[path] = m.evalStrBytes(sv.str)
  of svTuple, svArray, svSeq, svTable, svSet, svVariant, svMultiVariant,
     svDistinct, svClosure, svRef, svPtr:
    ## svClosure: Phase 15 C1; svRef/svPtr: Phase 15 R1a (no witness leaf yet —
    ## the heap-snapshot witness format lands R11b/R12).
    raise newException(ValueError,
      "extractLeaf called on non-primitive kind=" & $sv.kind)

proc collectSetLitMembers(s: IRStmt, paramName: string,
                          members: var HashSet[int64])
proc collectSetLitMembersExpr(e: IRExpr, paramName: string,
                              members: var HashSet[int64]) =
  if e == nil: return
  case e.kind
  of iekBinop:
    collectSetLitMembersExpr(e.lhs, paramName, members)
    collectSetLitMembersExpr(e.rhs, paramName, members)
  of iekUnop:
    collectSetLitMembersExpr(e.operand, paramName, members)
  of iekField:
    collectSetLitMembersExpr(e.obj, paramName, members)
  of iekIndex:
    collectSetLitMembersExpr(e.arr, paramName, members)
    collectSetLitMembersExpr(e.idx, paramName, members)
  of iekContains:
    if e.container != nil and e.container.kind == iekVar and
       e.container.vname == paramName and
       e.key != nil and e.key.kind == iekIntLit:
      members.incl e.key.ival
    collectSetLitMembersExpr(e.container, paramName, members)
    collectSetLitMembersExpr(e.key, paramName, members)
  of iekArrayLit:
    for c in e.lelems: collectSetLitMembersExpr(c, paramName, members)
  of iekTupleLit:
    for c in e.telems: collectSetLitMembersExpr(c, paramName, members)
  of iekSeqLen:
    collectSetLitMembersExpr(e.lenObj, paramName, members)
  else: discard

proc collectSetLitMembers(s: IRStmt, paramName: string,
                          members: var HashSet[int64]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectSetLitMembers(c, paramName, members)
  of isIf:
    for br in s.branches:
      collectSetLitMembersExpr(br.cond, paramName, members)
      collectSetLitMembers(br.body, paramName, members)
    if s.elseBody != nil: collectSetLitMembers(s.elseBody, paramName, members)
  of isLet:
    collectSetLitMembersExpr(s.lvalue, paramName, members)
  of isAssign:
    collectSetLitMembersExpr(s.avalue, paramName, members)
  of isWhile:
    collectSetLitMembersExpr(s.wcond, paramName, members)
    collectSetLitMembers(s.wbody, paramName, members)
  of isBreak, isContinue:
    discard
  of isAssert, isAssume:
    collectSetLitMembersExpr(s.acond, paramName, members)
  of isCall:
    for a in s.cargs: collectSetLitMembersExpr(a, paramName, members)
  of isIndex:
    collectSetLitMembersExpr(s.ixArr, paramName, members)
    collectSetLitMembersExpr(s.ixIdx, paramName, members)
  of isVariantField:
    collectSetLitMembersExpr(s.vfRecv, paramName, members)
  of isVariantReassign:
    discard
  of isVariantReassignSymbolic:
    if s.vrsRhs != nil:
      collectSetLitMembersExpr(s.vrsRhs, paramName, members)
  of isVariantConstructSym:
    collectSetLitMembersExpr(s.vcsDiscExpr, paramName, members)
    for fe in s.vcsPlainFields: collectSetLitMembersExpr(fe, paramName, members)
  of isReturn:
    if s.retExpr != nil: collectSetLitMembersExpr(s.retExpr, paramName, members)
  of isRaise:
    if s.raiseMsg != nil:
      collectSetLitMembersExpr(s.raiseMsg, paramName, members)
  of isTry:
    collectSetLitMembers(s.tryBody, paramName, members)
    for h in s.tryHandlers: collectSetLitMembers(h.body, paramName, members)
    if s.tryFinally != nil: collectSetLitMembers(s.tryFinally, paramName, members)
  of isDeref:   ## Phase 15 R1a: scan the dereffed ptr expr.
    collectSetLitMembersExpr(s.dPtr, paramName, members)
  of isNew:     ## Phase 15 R1a: allocation has no operand expr.
    discard
  of isDerefWrite:   ## Phase 15 R3: scan the ptr expr + the stored RHS.
    collectSetLitMembersExpr(s.dwPtr, paramName, members)
    collectSetLitMembersExpr(s.dwValue, paramName, members)
  of isTargetLabel, isUnsupported, isUnsafeCast: discard

proc collectTableLitKeys(s: IRStmt, paramName: string,
                         keys: var HashSet[string])
proc collectTableLitKeysExpr(e: IRExpr, paramName: string,
                             keys: var HashSet[string]) =
  if e == nil: return
  case e.kind
  of iekBinop:
    collectTableLitKeysExpr(e.lhs, paramName, keys)
    collectTableLitKeysExpr(e.rhs, paramName, keys)
  of iekUnop:
    collectTableLitKeysExpr(e.operand, paramName, keys)
  of iekField:
    collectTableLitKeysExpr(e.obj, paramName, keys)
  of iekIndex:
    collectTableLitKeysExpr(e.arr, paramName, keys)
    collectTableLitKeysExpr(e.idx, paramName, keys)
  of iekArrayLit:
    for c in e.lelems: collectTableLitKeysExpr(c, paramName, keys)
  of iekTupleLit:
    for c in e.telems: collectTableLitKeysExpr(c, paramName, keys)
  of iekSeqLen:
    collectTableLitKeysExpr(e.lenObj, paramName, keys)
  of iekContains:
    collectTableLitKeysExpr(e.container, paramName, keys)
    collectTableLitKeysExpr(e.key, paramName, keys)
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    collectTableLitKeysExpr(e.mutRecv, paramName, keys)
    collectTableLitKeysExpr(e.mutArg, paramName, keys)
  of iekTableSet:
    if e.tabRecv != nil and e.tabRecv.kind == iekVar and
       e.tabRecv.vname == paramName and
       e.tabKey != nil and e.tabKey.kind == iekStrLit:
      keys.incl e.tabKey.sval
    collectTableLitKeysExpr(e.tabRecv, paramName, keys)
    collectTableLitKeysExpr(e.tabKey, paramName, keys)
    collectTableLitKeysExpr(e.tabVal, paramName, keys)
  of iekSeqDel:
    collectTableLitKeysExpr(e.delSeq, paramName, keys)
    collectTableLitKeysExpr(e.delIdx, paramName, keys)
  of iekSeqInsert:
    collectTableLitKeysExpr(e.insSeq, paramName, keys)
    collectTableLitKeysExpr(e.insVal, paramName, keys)
    collectTableLitKeysExpr(e.insIdx, paramName, keys)
  of iekSeqPop:
    collectTableLitKeysExpr(e.popSeq, paramName, keys)
  else: discard

proc collectTableLitKeys(s: IRStmt, paramName: string,
                         keys: var HashSet[string]) =
  if s == nil: return
  case s.kind
  of isBlock:
    for c in s.stmts: collectTableLitKeys(c, paramName, keys)
  of isIf:
    for br in s.branches:
      collectTableLitKeysExpr(br.cond, paramName, keys)
      collectTableLitKeys(br.body, paramName, keys)
    if s.elseBody != nil: collectTableLitKeys(s.elseBody, paramName, keys)
  of isLet:
    collectTableLitKeysExpr(s.lvalue, paramName, keys)
  of isAssign:
    collectTableLitKeysExpr(s.avalue, paramName, keys)
  of isWhile:
    collectTableLitKeysExpr(s.wcond, paramName, keys)
    collectTableLitKeys(s.wbody, paramName, keys)
  of isBreak, isContinue:
    discard
  of isAssert, isAssume:
    collectTableLitKeysExpr(s.acond, paramName, keys)
  of isCall:
    for a in s.cargs: collectTableLitKeysExpr(a, paramName, keys)
  of isIndex:
    if s.ixArr != nil and s.ixArr.kind == iekVar and
       s.ixArr.vname == paramName and
       s.ixIdx != nil and s.ixIdx.kind == iekStrLit:
      keys.incl s.ixIdx.sval
    collectTableLitKeysExpr(s.ixArr, paramName, keys)
    collectTableLitKeysExpr(s.ixIdx, paramName, keys)
  of isVariantField:
    collectTableLitKeysExpr(s.vfRecv, paramName, keys)
  of isVariantReassign:
    discard
  of isVariantReassignSymbolic:
    if s.vrsRhs != nil:
      collectTableLitKeysExpr(s.vrsRhs, paramName, keys)
  of isVariantConstructSym:
    collectTableLitKeysExpr(s.vcsDiscExpr, paramName, keys)
    for fe in s.vcsPlainFields: collectTableLitKeysExpr(fe, paramName, keys)
  of isReturn:
    if s.retExpr != nil: collectTableLitKeysExpr(s.retExpr, paramName, keys)
  of isRaise:
    if s.raiseMsg != nil:
      collectTableLitKeysExpr(s.raiseMsg, paramName, keys)
  of isTry:
    collectTableLitKeys(s.tryBody, paramName, keys)
    for h in s.tryHandlers: collectTableLitKeys(h.body, paramName, keys)
    if s.tryFinally != nil: collectTableLitKeys(s.tryFinally, paramName, keys)
  of isDeref:   ## Phase 15 R1a: scan the dereffed ptr expr.
    collectTableLitKeysExpr(s.dPtr, paramName, keys)
  of isNew:     ## Phase 15 R1a: allocation has no operand expr.
    discard
  of isDerefWrite:   ## Phase 15 R3: scan the ptr expr + the stored RHS.
    collectTableLitKeysExpr(s.dwPtr, paramName, keys)
    collectTableLitKeysExpr(s.dwValue, paramName, keys)
  of isTargetLabel, isUnsupported, isUnsafeCast: discard

proc extractTableEntries(m: Z3Model, w: var RawWitness, path: string,
                         sv: SymVal, keys: HashSet[string]) =
  case sv.tabValTy.kind
  of itInt:
    let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
      sv.tabDataRaw.ctx, sv.tabDataRaw.raw)
    let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
      sv.tabPresentRaw.ctx, sv.tabPresentRaw.raw)
    var keyList: seq[string]
    for k in keys:
      if m.evalBool(select(typedPresent, mkString(k))):
        keyList.add k
        let v = m.evalInt(select(typedData, mkString(k)))
        w.intVals[path & "." & k] = int64(v)
    w.tabKeys[path] = keyList
  else: discard

proc extractSeqElements(m: Z3Model, w: var RawWitness, path: string,
                        sv: SymVal, n: int) =
  ## Read elements 0..<n from the seq's Z3Array, dispatching on the
  ## element type to wrap/select with the right typed handle.
  case sv.seqElemTy.kind
  of itInt:
    case sv.seqElemTy.width
    of 8:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 16:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 32:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 64:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
      for i in 0 ..< n:
        let v = m.evalInt(select(typed, mkInt(i)))
        if sv.seqElemTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    else:
      raise newException(ValueError,
        "extractSeqElements: unsupported int width " & $sv.seqElemTy.width)
  of itBool:
    let typed = wrap[Z3Array[Z3Int, Z3Bool]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
    for i in 0 ..< n:
      w.boolVals[path & "." & $i] = m.evalBool(select(typed, mkInt(i)))
  of itFloat32:   ## Phase 15 F9b: delegate to extractLeaf for NaN handling.
    let typed = wrap[Z3Array[Z3Int, Z3Float32]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
    for i in 0 ..< n:
      let elem = SymVal(kind: svFloat32, fp32: select(typed, mkInt(i)))
      extractLeaf(m, w, path & "." & $i, elem)
  of itFloat64:   ## Phase 15 F9b
    let typed = wrap[Z3Array[Z3Int, Z3Float64]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw)
    for i in 0 ..< n:
      let elem = SymVal(kind: svFloat64, fp64: select(typed, mkInt(i)))
      extractLeaf(m, w, path & "." & $i, elem)
  of itRef, itPtr:   ## Phase 15 R3 (ADR-0010): seq[ref T] / seq[ptr T] elements.
    # The per-element pointee VALUES of a `seq[ref T]` were observed only
    # through the heap (`select(path.heaps[T], elem)`); the full per-element
    # heap-snapshot witness (alias groups / nil rendering) is the deferred
    # R11b/R12 format. R3 records only the LENGTH (already set by the caller in
    # `seqLens[path]`) — the witness reader reconstructs a `seq[ref T]` of that
    # length with default-zero cells, which is sound (the pointees were never
    # rendered, only constrained in-solver). No element leaf is emitted; the
    # reader uses defaults so it never KeyErrors.
    discard
  else:
    raise newException(ValueError,
      "extractSeqElements: unsupported element kind " & $sv.seqElemTy.kind)

proc harvestSetStoreKeys(m: Z3Model, sv: SymVal): seq[int64] =
  ## v65 (round-3 ledger: HashSet witness gap). The model VALUE of the
  ## membership array is — for the finite models Z3 produces here — a
  ## nested `(store (store ((as const …) dflt) k1 v1) k2 v2)` chain. Walk
  ## it and harvest every concrete BV64 key. This surfaces members
  ## constrained only through a SYMBOLIC key (e.g. `s.len in hs`, whose
  ## key is `int2bv(len(s))` — the literal-candidate scan
  ## `collectSetLitMembers` cannot see it, which produced the observed
  ## `s = "", hs = {}` inconsistent witness). Keys whose stored value is
  ## `false` (a later overwrite / explicit exclusion) are filtered by the
  ## caller's `select` re-check, so this only needs to be a SUPERSET
  ## harvest. A non-store model shape (e.g. an as-array function graph)
  ## harvests nothing and the caller falls back to literal candidates
  ## alone — exactly the pre-v65 behaviour, never worse.
  let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
    sv.setMembersRaw.ctx, sv.setMembersRaw.raw)
  var cur = toAnyAst(m.eval(typed, modelCompletion = true))
  var guard = 0
  while guard < 4096:   # cycle-proof bound; model store chains are finite
    inc guard
    if getAstKind(cur) != akApp: break
    if declName(cur.ctx, getAppDecl(cur)) != "store": break
    let keyAst = getAppArg(cur, 1)
    if getAstKind(keyAst) == akNumeral:
      try:
        result.add cast[int64](parseBiggestUInt(getNumeralString(keyAst)))
      except ValueError:
        discard   # non-decimal numeral rendering — skip this key
    cur = getAppArg(cur, 0)

proc extractSetMembers(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal, candidates: HashSet[int64]) =
  doAssert sv.setElemTy.kind == itInt and sv.setElemTy.width == 64
  let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
    sv.setMembersRaw.ctx, sv.setMembersRaw.raw)
  # v65: union the literal candidates with keys harvested from the model's
  # own store chain, so symbolically-keyed members surface too.
  var cands = candidates
  for k in harvestSetStoreKeys(m, sv):
    cands.incl k
  # v65: include the concrete model value of every key TERM this set was
  # membership-tested with (`setMembershipKeyTerms`) — the only faithful
  # finite rendering when the model chose a const-true (universal) array.
  let keyId = cast[uint](sv.setMembersRaw.raw)
  if setMembershipKeyTerms.hasKey(keyId):
    for t in setMembershipKeyTerms[keyId]:
      cands.incl int64(m.evalInt(asZ3BitVec[64](t)))
  when defined(symexSetTrace):
    stderr.writeLine "[settrace] path=" & path & " cands=" & $cands
    stderr.writeLine "[settrace] model(A) = " & $(m.eval(typed, true))
  var present: seq[int64]
  for v in cands:
    if m.evalBool(select(typed, mkBitVec[64](v))):
      present.add v
  w.setMembers[path] = present

proc evalDiscOrdinal(m: Z3Model, disc: SymVal): int64 =
  ## ADR-0013 D5 (Slice 2). Evaluate a ref-to-variant discriminant SymVal under
  ## the model to its integer ordinal, so the witness serializer can pick the
  ## ACTIVE arm (the arm whose `tagOrdinal` equals this ordinal). Same kind
  ## dispatch as `isVariantField` / `refVariantDiscRangeClause`'s `discEq`.
  case disc.kind
  of svBV8:  int64(m.evalInt(disc.bv8))
  of svBV16: int64(m.evalInt(disc.bv16))
  of svBV32: int64(m.evalInt(disc.bv32))
  of svBV64: int64(m.evalInt(disc.bv64))
  of svInt:  m.evalInt(disc.zi)
  of svBool: (if m.evalBool(disc.bo): 1'i64 else: 0'i64)
  else:      0'i64

proc extractFromSymVal(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal,
                       tabKeys: Table[string, HashSet[string]],
                       setMembers: Table[string, HashSet[int64]]) =
  case sv.kind
  of svTuple:
    for i, f in sv.fields:
      let suffix = if sv.fieldNames[i].len > 0: "." & sv.fieldNames[i]
                   else: "." & $i
      extractFromSymVal(m, w, path & suffix, f, tabKeys, setMembers)
  of svArray:
    for i, e in sv.arrElems:
      extractFromSymVal(m, w, path & "." & $i, e, tabKeys, setMembers)
  of svSeq:
    if sv.isUnsupportedFieldPlaceholder:
      # Round-6 Bug #2 (scoped decline): `seqLen` was forced `== 0` at
      # allocation time and `seqElemTy` is an UNBACKED kind (e.g. itTuple)
      # `extractSeqElements`'s dispatch does not cover — calling it would
      # raise regardless of `n`. Content is never modeled or trusted for
      # this field (any SUT read was already intercepted at parse time), so
      # record the length only.
      w.seqLens[path] = 0
    else:
      let lenVal = int(m.evalInt(sv.seqLen))
      let n = max(0, min(lenVal, 64))
      w.seqLens[path] = n
      extractSeqElements(m, w, path, sv, n)
  of svTable:
    let keys = if tabKeys.hasKey(path): tabKeys[path] else: initHashSet[string]()
    extractTableEntries(m, w, path, sv, keys)
  of svSet:
    let cands = if setMembers.hasKey(path): setMembers[path]
                else: initHashSet[int64]()
    extractSetMembers(m, w, path, sv, cands)
  of svVariant:
    # Discriminator goes under the standard `.kind` path; arm
    # fields land under `.@<armTag>.<fieldName>`. Cycle 7's
    # witness emitter consumes them via a case dispatch on the
    # discriminator value.
    extractFromSymVal(m, w, path & "." & sv.vDiscName, sv.vDisc[],
                      tabKeys, setMembers)
    # Plain fields under direct sub-paths (no @tag prefix).
    for i, f in sv.vPlainFields:
      let sub = path & "." & sv.vPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
    for tagOrdinal, fields in sv.vArmFields.pairs:
      let armNames = sv.vArmFieldNames[tagOrdinal]
      for j, f in fields:
        # Use a tag-ordinal-keyed subpath so cycle 7 can resolve
        # by discriminator value rather than by tag name.
        let sub = path & ".@" & $tagOrdinal & "." & armNames[j]
        extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
  of svMultiVariant:
    # Phase 14 cycle A1c. Same shape as svVariant extraction but
    # iterates each axis: extract per-axis disc + arm fields. Plain
    # fields are emitted once (shared across all axes).
    for i, f in sv.mvPlainFields:
      let sub = path & "." & sv.mvPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
    for ax in sv.mvAxes:
      extractFromSymVal(m, w, path & "." & ax.discName, ax.disc[],
                        tabKeys, setMembers)
      for tagOrdinal, fields in ax.armFields.pairs:
        let armNames = ax.armFieldNames[tagOrdinal]
        for j, f in fields:
          let sub = path & "." & ax.discName &
                    ".@" & $tagOrdinal & "." & armNames[j]
          extractFromSymVal(m, w, sub, f, tabKeys, setMembers)
  of svDistinct:
    # Phase 15 G4 (Breadth-CRIT-1). The witness for a `distinct T` param goes
    # through ejection: extract the BASE SymVal (`== eject_T(distinctConst)`) at
    # the SAME path, so the emitter's eject-then-base-reader chain reads a real
    # base value instead of a silent empty leaf.
    extractFromSymVal(m, w, path, sv.distinctBaseSym[], tabKeys, setMembers)
  of svUninterpRef:
    # Phase 15 E8. An opaque exception ref (`getCurrentException()`): its fields
    # are not modeled symbolically, so there is no witness leaf to extract.
    # Emit an informational `eeUninterpRefExtraction` (sevHint, NOT halting) and
    # drop the leaf. Drained into the sat finding's `errors` alongside F7's
    # extraction errors.
    let uninterpHint = SymexErrorInfo(
      kind: eeUninterpRefExtraction, severity: sevHint,
      msg: "exception object fields not modeled symbolically (" & sv.typeTag & ")")
    extractionErrors.add uninterpHint    # threadvar: fallback
    syncExtractionError(uninterpHint)    # CR-9 Stage 5: LIVE WalkCtx field
  of svClosure:
    # Phase 15 C2a / R13 (Invariant 3). A closure as a top-level SUT RESULT has
    # no concrete proc-value rendering (a proc cannot be reconstructed as a
    # literal), so the closure VALUE itself is still classified `ceNotImplemented`
    # (sevError) rather than silently dropped. BUT R13 (sub-track A) lets a
    # closure CAPTURE a `ref T`/`ptr T` free variable; those captured refs DO
    # have a sound heap witness. So follow each captured `svRef`/`svPtr` field in
    # the envRecord through the heap and extract its `pointsTo` value (the same
    # `currentHeapDerefVals`/default-zero leaf the svRef arm produces) into the
    # witness under the field's sub-path. The closure-value rendering degrades
    # gracefully (classified note); the captured-ref pointees are recovered.
    let cloErr = SymexErrorInfo(kind: ceNotImplemented, severity: sevError,
      msg: "closure as a top-level SUT result is not supported (no witness " &
           "rendering for a proc value)")
    extractionErrors.add cloErr          # threadvar: fallback
    syncExtractionError(cloErr)          # CR-9 Stage 5: LIVE WalkCtx field
    if sv.closureEnv != nil and sv.closureEnv.kind == svTuple:
      let env = sv.closureEnv[]
      for i, f in env.fields:
        if f.kind in {svRef, svPtr}:
          let suffix = if env.fieldNames[i].len > 0: "." & env.fieldNames[i]
                       else: "." & $i
          extractFromSymVal(m, w, path & suffix, f, tabKeys, setMembers)
  of svRef, svPtr:
    # Phase 15 R1 (ADR-0010, C7/Breadth-CRIT-1). The minimal R1 witness for a
    # `ref T`/`ptr T` param: if the param was dereferenced (`p[]`), render the
    # heap-select value (`select(heap, p)`) — recorded under the param name in
    # `currentHeapDerefVals` — at the SAME path, so the reader produces a `ref T`
    # holding the value `p[]` took in the model. A NEVER-dereferenced ref param
    # has no observed pointee value: render its pointee as the type's DEFAULT
    # (zero) so the leaf exists and the reader never KeyErrors — any value is
    # sound since the pointee was never observed. The full heap-snapshot witness
    # format (alias groups / nil rendering) lands R11b/R12.
    if currentHeapDerefVals.hasKey(path):
      extractFromSymVal(m, w, path, currentHeapDerefVals[path],
                        tabKeys, setMembers)
    else:
      let pointee = if sv.kind == svRef: sv.refPointee else: sv.ptrPointee
      if pointee != nil:
        case pointee.kind
        of itInt:
          if pointee.signed: w.intVals[path]  = 0
          else:              w.uintVals[path] = 0'u64
        of itBool: w.boolVals[path] = false
        of itFloat32: w.float32Vals[path] = 0.0'f32
        of itFloat64: w.float64Vals[path] = 0.0'f64
        of itTuple:
          # Phase 15 R6 (ADR-0010). A `ref object` param accessed only by field
          # (`p.field`, the field-split heap) records NO whole-object deref value
          # under `currentHeapDerefVals` — but the witness reader
          # (`emitTyAndReader(itTuple)`) still reads a leaf PER FIELD. Materialise
          # a DEFAULT object SymVal and extract its leaves so every field leaf
          # exists (the reader never KeyErrors). Sound: the field-array pointee
          # values were observed only through the heap; the rendered object cell
          # is a replayable default. The full heap-snapshot witness (per-field
          # observed values) lands R11b/R12.
          var scratchPC: seq[Z3Bool]
          let protoObj = allocateSym(pointee, "__refObjWitness", scratchPC)
          extractFromSymVal(m, w, path, protoObj, tabKeys, setMembers)
        of itVariant:
          # ADR-0013 Slice 1. Witness extraction for a ref-to-variant pointee.
          # Allocate a proto svVariant (default arm fields), extract all its
          # sub-paths so the macro reader never KeyErrors, then OVERRIDE the disc
          # sub-path with the actually-observed disc SymVal (recorded in
          # `currentHeapDerefVals["<path>.<discName>"]`) so the macro's case
          # dispatch on the discriminator reflects the real model value.
          # Arm-specific field observed values land in Slice 2.
          var scratchPC: seq[Z3Bool]
          let protoVariant = allocateSym(pointee, "__refVariantWitness", scratchPC)
          extractFromSymVal(m, w, path, protoVariant, tabKeys, setMembers)
          # Override disc with observed SymVal (if we actually read it via heap).
          let discPath = path & "." & pointee.vDiscName
          if currentHeapDerefVals.hasKey(discPath):
            let discSV = currentHeapDerefVals[discPath]
            extractLeaf(m, w, discPath, discSV)
            # ADR-0013 D5 (Slice 2): emit ONLY the ACTIVE arm's fields. Evaluate
            # the disc ordinal, find the matching arm (or the else arm), and for
            # each of its fields whose per-(arm,field) heap was materialised on
            # the winning path, `select` the observed value at the ref's address
            # and override the proto-default leaf. The macro witness reader case-
            # dispatches on the disc and reads exactly `<path>.@<ord>.<field>`, so
            # only the active arm's leaves are consumed — inactive arms keep their
            # (harmless) proto defaults. Soundness: the disc-range clause (D4.5)
            # guarantees the ordinal is a legal arm tag, so a real arm is found.
            let discOrd = evalDiscOrdinal(m, discSV)
            let addrAst = if sv.kind == svRef: sv.refAst else: sv.ptrAst
            let baseId = refPointeeTypeId(pointee)
            var activeArm: VariantArm
            var foundArm = false
            var elseArm: VariantArm
            var hasElse = false
            for arm in pointee.vArms:
              if arm.isElse: (elseArm = arm; hasElse = true)
              elif int64(arm.tagOrdinal) == discOrd: (activeArm = arm; foundArm = true)
            if (not foundArm) and hasElse:
              activeArm = elseArm; foundArm = true
            if foundArm:
              for j, fname in activeArm.fieldNames:
                let armHeapKey = baseId & "__@" & $activeArm.tagOrdinal & "__" & fname
                if currentVariantHeaps.hasKey(armHeapKey):
                  try:
                    let heap = currentVariantHeaps[armHeapKey]
                    let fieldSV = heapSelect(heap.ctx, heap, addrAst,
                                             activeArm.fieldTypes[j])
                    let fieldPath = path & ".@" & $activeArm.tagOrdinal & "." & fname
                    extractLeaf(m, w, fieldPath, fieldSV)
                  except CatchableError:
                    discard  ## non-primitive arm field: keep proto default (sound)
        else: discard   ## other composite pointees' witness lands R3+/R11b
  else:
    extractLeaf(m, w, path, sv)

proc pointeeRendering(w: RawWitness, path: string): Option[string] =
  ## Phase 15 R12. Render the modelled pointee value at `path` for a ref/ptr
  ## param's heap-snapshot `pointsTo`, reading back the leaf that
  ## `extractFromSymVal(svRef/svPtr)` populated into the flat witness tables.
  ## A primitive pointee resolves to a stringified value; a composite pointee
  ## (`ref object` field-split, R6) has no single whole-object leaf — render a
  ## structural placeholder so the snapshot is honest (Invariant 3, no silent
  ## gap) rather than fabricating a value.
  ##
  ## Cluster H H_witness: this proc still handles the TOP-LEVEL, PRIMITIVE-
  ## pointee case unchanged (a `ref int`/`ref float`/`ref bool` etc. param —
  ## `currentHeapDerefVals`/R1's bare-`p[]` witness hook already gives it a
  ## REAL observed value, never a fabricated default). A composite (`itTuple`)
  ## pointee no longer reaches the `"<object>"` fallback below at all —
  ## `buildHeapSnapshot` routes those through `renderObjectFields` instead,
  ## which reads the REAL per-field heap values via the model (not the
  ## default-zero prototype `extractFromSymVal`'s `itTuple` arm populates).
  ## The fallback is kept for any OTHER composite kind (`seq`/`Table`/`HashSet`
  ## pointee) this slice does not extend.
  if w.intVals.hasKey(path):     return some($w.intVals[path])
  if w.uintVals.hasKey(path):    return some($w.uintVals[path])
  if w.boolVals.hasKey(path):    return some($w.boolVals[path])
  if w.float64Vals.hasKey(path): return some($w.float64Vals[path])
  if w.float32Vals.hasKey(path): return some($w.float32Vals[path])
  if w.strVals.hasKey(path):     return some(w.strVals[path])
  # Composite pointee (object/seq): leaves live under `path.<sub>` sub-paths.
  # The whole-cell value isn't a single leaf; render a structural marker.
  for k in w.intVals.keys:
    if k.len > path.len and k.startsWith(path & "."): return some("<object>")
  for k in w.boolVals.keys:
    if k.len > path.len and k.startsWith(path & "."): return some("<object>")
  none(string)

# --- Cluster H H_witness (ADR-0022, ADR-0010 invariant #4) ------------------
# The recursive heap-snapshot witness. `buildHeapSnapshot` used to stop at the
# top-level ref/ptr PARAMS, rendering any composite (`itTuple`) pointee as the
# blind `"<object>"` placeholder. H_witness descends the REACHABLE ref graph
# from every param — object fields, and (additively) container (seq/array/
# tuple) elements — reading each cell's REAL modelled value out of the
# winning path's heap arrays (`currentVariantHeaps`, snapshotted from
# `path.heaps` just before `extractWitness` runs), bounded by the SAME
# effective heap-depth budget the walker itself enforces
# (`effectiveHeapDepthLimit`) and cycle-safe via a `visited` address->name
# map (a revisited address renders `aliasRef` to the name it was FIRST seen
# under — never re-recursed, so a self-cycle or ring provably terminates).
#
# Cell naming: a top-level param keeps its bare name (`p`, `q`, unchanged).
# A reachable cell is named by its ACCESS PATH from the param that reached it
# first: a field hop appends `.<field>` (`p.next`, `p.next.next`); a container
# index appends `[<i>]` (`s[0]`, `arr[1]`). Every reachable cell (param or
# not) that denotes a live, in-budget, non-alias address gets its own
# `HeapSnapshotEntry` in the SAME flat `seq` — no new struct shape, `pointsTo`/
# `aliasRef` simply now populate for the WHOLE reachable graph, not just
# top-level params, per ADR-0010 invariant #4.
#
# An object cell's `pointsTo` is a structural rendering `"{f1=v1, f2=v2}"`:
#   * a primitive field renders its stringified value (same stringifier as a
#     top-level primitive pointee, via `extractLeaf` + `pointeeRendering`);
#   * a nil ref/ptr field renders inline as `"nil"` (no separate cell — a nil
#     field has no substructure worth naming);
#   * a non-nil ref/ptr field renders `"@<cellName>"` — a REFERENCE to another
#     entry in this same flat seq (which may be a fresh cell, a param, or an
#     alias entry); the consumer resolves it by name, exactly like resolving
#     an `aliasRef`;
#   * a field whose per-field heap array was never materialised on the
#     winning path (the SUT never touched it, so Z3 asserts nothing about it)
#     renders `"<unobserved>"` — Invariant 3 (never fabricate a value) rather
#     than guessing;
#   * a field one hop beyond the effective heap-depth budget renders
#     `"<max-heap-depth>"` — the hop is never taken (no select performed),
#     mirroring `heapDepthExhausted`'s "halt the path" semantics for the walk
#     itself;
#   * a field of a container/variant/nested-by-value-object type (not yet
#     witness-renderable through the field-split heap this slice) renders
#     `"<unsupported>"` — a documented ceiling, not a crash or a guess.

proc registerNominalIfFull(ty: IRType) =
  ## Learn `ty`'s field structure under its `nominalId`, but only if `ty` is a
  ## genuinely fielded (non-placeholder) named object — a `namedRefPlaceholder`
  ## must never overwrite a real entry (and never seeds one, since it carries
  ## no real fields to learn).
  if ty != nil and ty.kind == itTuple and not ty.isPlaceholder and
     ty.nominalId.len > 0 and not heapWitnessNominalRegistry.hasKey(ty.nominalId):
    heapWitnessNominalRegistry[ty.nominalId] = ty

proc resolveObjectFields(ty: IRType): IRType =
  ## Recover the REAL field list for `ty` when `ty` is an empty-fielded
  ## `namedRefPlaceholder` (a recursive field's pointee) whose nominal type has
  ## already been observed elsewhere this run (always true once ANY bare
  ## ref/ptr param or container element of that nominal type has been visited
  ## — `registerNominalIfFull` seeds it before any field recurses). Falls back
  ## to `ty` itself (possibly still empty) when the schema is genuinely
  ## unknown this run.
  if ty.isPlaceholder and ty.nominalId.len > 0 and
     heapWitnessNominalRegistry.hasKey(ty.nominalId):
    heapWitnessNominalRegistry[ty.nominalId]
  else:
    ty

proc heapAddrIsNil(m: Z3Model, addrAst: Z3AnyAst, pointeeTy: IRType): bool =
  let typeId = refPointeeTypeId(pointeeTy)
  currentNilConsts.hasKey(typeId) and
    $m.eval(currentNilConsts[typeId]) == $m.eval(addrAst)

proc renderLeafFieldAt(m: Z3Model, w: var RawWitness, ctx: Z3Context,
                       heapKey, leafPath: string, addrAst: Z3AnyAst,
                       fty: IRType): string =
  ## Render a PRIMITIVE field (or bare primitive pointee) at `addrAst`,
  ## reusing `extractLeaf`/`pointeeRendering` for byte-identical stringifying
  ## with the rest of the witness. `"<unobserved>"` when the heap array was
  ## never materialised (the SUT never touched this cell/field on the winning
  ## path — Invariant 3: never fabricate).
  if not currentVariantHeaps.hasKey(heapKey): return "<unobserved>"
  let leafSV = heapSelect(ctx, currentVariantHeaps[heapKey], addrAst, fty)
  extractLeaf(m, w, leafPath, leafSV)
  pointeeRendering(w, leafPath).get("<unobserved>")

proc renderObjectFields(m: Z3Model, w: var RawWitness,
                        cellName: string, addrAst: Z3AnyAst, pointeeTyIn: IRType,
                        depth, limit: int, visited: var Table[string, string],
                        acc: var seq[HeapSnapshotEntry]): string

proc renderRefFieldValue(m: Z3Model, w: var RawWitness,
                         cellName: string, addrAst: Z3AnyAst, objTy: IRType,
                         fname: string, fty: IRType, depth, limit: int,
                         visited: var Table[string, string],
                         acc: var seq[HeapSnapshotEntry]): string =
  ## Render one ref/ptr-typed FIELD's value fragment. ALWAYS materialises a
  ## `HeapSnapshotEntry` in `acc` for `cellName & "." & fname` when the target
  ## is non-nil and in-budget — carrying `pointsTo` (a fresh address, which
  ## recurses into it) or `aliasRef` (an address already seen — a param, or an
  ## earlier reachable cell, POSSIBLY AN ANCESTOR of this very field, i.e. a
  ## self-loop/ring). Returns `"@<cellName>"` either way, so the parent's
  ## `{...}` rendering always names a lookup key one hop away — the consumer
  ## chases `aliasRef` exactly as it already must for param-vs-param aliasing.
  ## Cycle-safe: `visited` is checked BEFORE any recursion, so a self-loop or
  ## ring resolves to an `aliasRef` on the SECOND visit and never re-descends.
  let ctx = addrAst.ctx
  let heapKey = fieldHeapKey(objTy, fname)
  if not currentVariantHeaps.hasKey(heapKey): return "<unobserved>"
  let childDepth = depth + 1
  if limit > 0 and childDepth >= limit: return "<max-heap-depth>"
  let fieldSV = heapSelect(ctx, currentVariantHeaps[heapKey], addrAst, fty)
  let (childAddr, childPointee) =
    if fieldSV.kind == svRef: (fieldSV.refAst, fieldSV.refPointee)
    else: (fieldSV.ptrAst, fieldSV.ptrPointee)
  if heapAddrIsNil(m, childAddr, childPointee): return "nil"
  let addrRendering = $m.eval(childAddr)
  let childName = cellName & "." & fname
  if visited.hasKey(addrRendering):
    # ALIAS / CYCLE: this address was already registered under an earlier
    # name (a param, or an earlier reachable cell — possibly an ANCESTOR of
    # this very field, i.e. a self-loop/ring). Still materialise a named
    # entry for `childName` (mirrors param-vs-param aliasing: every name
    # gets an entry) carrying `aliasRef` — but do NOT recurse again (the
    # visited-set check runs BEFORE any recursion, so a cycle provably
    # terminates here rather than re-descending).
    acc.add HeapSnapshotEntry(
      name: childName, sort: "Ref_" & refPointeeTypeId(childPointee),
      value: addrRendering, pointsTo: none(string),
      aliasRef: some(visited[addrRendering]))
    return "@" & childName
  visited[addrRendering] = childName
  registerNominalIfFull(childPointee)
  var childEntry = HeapSnapshotEntry(
    name: childName, sort: "Ref_" & refPointeeTypeId(childPointee),
    value: addrRendering, pointsTo: none(string), aliasRef: none(string))
  case childPointee.kind
  of itTuple:
    childEntry.pointsTo = some(renderObjectFields(m, w, childName, childAddr,
      childPointee, childDepth, limit, visited, acc))
  of itInt, itBool, itFloat32, itFloat64:
    # A `ref`/`ptr` FIELD whose own pointee is a bare primitive (e.g.
    # `next: ref int`) — a SECOND, bare (non-field) heap keyed on the pointee
    # type alone, only materialised if the SUT itself dereffed it directly.
    let rendered = renderLeafFieldAt(m, w, ctx, refPointeeTypeId(childPointee),
                                     childName, childAddr, childPointee)
    if rendered != "<unobserved>": childEntry.pointsTo = some(rendered)
  else:
    discard  ## container/variant/etc pointee: documented ceiling this slice —
             ## `pointsTo` stays `none` (honest, not fabricated).
  acc.add childEntry
  "@" & childName

proc renderObjectFields(m: Z3Model, w: var RawWitness,
                        cellName: string, addrAst: Z3AnyAst, pointeeTyIn: IRType,
                        depth, limit: int, visited: var Table[string, string],
                        acc: var seq[HeapSnapshotEntry]): string =
  ## Build the `"{field=value, ...}"` structural rendering for an OBJECT cell
  ## already known live/in-budget/non-alias at `cellName`/`addrAst`. Recurses
  ## into ref/ptr fields via `renderRefFieldValue` (which appends new entries
  ## to `acc`); primitive fields render via `renderLeafFieldAt`; any other
  ## field kind (container/variant/nested-by-value-object — not yet
  ## witness-renderable through the field-split heap) renders `"<unsupported>"`.
  let realTy = resolveObjectFields(pointeeTyIn)
  if realTy.fields.len == 0: return "{}"
  let ctx = addrAst.ctx
  var parts: seq[string]
  for i, fname in realTy.fieldNames:
    let fty = realTy.fields[i]
    let frag =
      if fty.kind in {itRef, itPtr}:
        renderRefFieldValue(m, w, cellName, addrAst, realTy, fname, fty,
                            depth, limit, visited, acc)
      elif fty.kind in {itInt, itBool, itFloat32, itFloat64}:
        renderLeafFieldAt(m, w, ctx, fieldHeapKey(realTy, fname),
                          cellName & "." & fname, addrAst, fty)
      else:
        "<unsupported>"
    parts.add fname & "=" & frag
  "{" & parts.join(", ") & "}"

proc renderContainerElemCell(m: Z3Model, w: var RawWitness, cellName: string,
                             elemSV: SymVal, limit: int,
                             visited: var Table[string, string],
                             acc: var seq[HeapSnapshotEntry]) =
  ## Render one container ELEMENT (a `seq[Node]`/`array[N, Node]`/
  ## `tuple[...]` slot) whose value is already an `svRef`/`svPtr` SymVal — the
  ## SAME nil/alias/recurse machinery as a field, just entered from a
  ## container index/field instead of an object field. A container element
  ## costs no heap-depth hop to OBTAIN (its address is already bound, exactly
  ## like a top-level param) — depth starts at 0, matching a param cell.
  let (addrAst, pointee) =
    if elemSV.kind == svRef: (elemSV.refAst, elemSV.refPointee)
    else: (elemSV.ptrAst, elemSV.ptrPointee)
  if pointee == nil: return
  let sortName = "Ref_" & refPointeeTypeId(pointee)
  if heapAddrIsNil(m, addrAst, pointee):
    acc.add HeapSnapshotEntry(name: cellName, sort: sortName, value: "nil",
                              pointsTo: none(string), aliasRef: none(string))
    return
  let addrRendering = $m.eval(addrAst)
  if visited.hasKey(addrRendering):
    acc.add HeapSnapshotEntry(name: cellName, sort: sortName,
                              value: addrRendering, pointsTo: none(string),
                              aliasRef: some(visited[addrRendering]))
    return
  visited[addrRendering] = cellName
  registerNominalIfFull(pointee)
  var entry = HeapSnapshotEntry(name: cellName, sort: sortName,
                                value: addrRendering, pointsTo: none(string),
                                aliasRef: none(string))
  if pointee.kind == itTuple:
    entry.pointsTo = some(renderObjectFields(m, w, cellName, addrAst, pointee,
                                              0, limit, visited, acc))
  elif pointee.kind in {itInt, itBool, itFloat32, itFloat64}:
    let rendered = renderLeafFieldAt(m, w, addrAst.ctx, refPointeeTypeId(pointee),
                                     cellName, addrAst, pointee)
    if rendered != "<unobserved>": entry.pointsTo = some(rendered)
  acc.add entry

proc renderContainerElemsIntoSnapshot(m: Z3Model, w: var RawWitness,
                                      pname: string, sv: SymVal, limit: int,
                                      visited: var Table[string, string],
                                      acc: var seq[HeapSnapshotEntry]) =
  ## Cluster H H_witness: a top-level CONTAINER param (`seq[Node]`/
  ## `array[N, Node]`/`tuple[...]`) whose element(s) are ref/ptr-typed —
  ## descend into each element the model pins, naming cells `pname[i]`
  ## (seq/array) or `pname.field` (tuple). PURELY ADDITIVE: before H_witness a
  ## container param contributed ZERO heapSnapshot entries (only bare
  ## ref/ptr-KIND params did), so this cannot alter any existing snapshot's
  ## shape — it can only add new cells for a param class that rendered
  ## nothing at all before.
  case sv.kind
  of svArray:
    if sv.arrElemTy.kind notin {itRef, itPtr}: return
    for i, elemSV in sv.arrElems:
      renderContainerElemCell(m, w, pname & "[" & $i & "]", elemSV, limit,
                              visited, acc)
  of svTuple:
    for i, fname in sv.fieldNames:
      let f = sv.fields[i]
      if f.kind in {svRef, svPtr}:
        let label = if fname.len > 0: fname else: $i
        renderContainerElemCell(m, w, pname & "." & label, f, limit,
                                visited, acc)
  of svSeq:
    if sv.seqElemTy.kind notin {itRef, itPtr}: return
    let ctx = sv.seqDataRaw.ctx
    let n = max(0, min(int(m.evalInt(sv.seqLen)), 64))
    let isPtr = sv.seqElemTy.kind == itPtr
    let pointee = if isPtr: sv.seqElemTy.ptrPointeeTy else: sv.seqElemTy.refPointeeTy
    for i in 0 ..< n:
      # `Ref_T` is a RUNTIME uninterpreted sort the typed `select` can't
      # express — raw FFI, mirroring `isIndex/seq`'s itRef/itPtr arm
      # (runtime.nim ~5415) and `storeSeqElem`'s itRef/itPtr arm. GROUND
      # select; no quantifier.
      let raw = ctx.checkErr Z3_mk_select(ctx.raw, sv.seqDataRaw.raw, mkInt(i).raw)
      let elemAny = wrap[Z3AnyAst](ctx, raw)
      let elemSV = if isPtr: SymVal(kind: svPtr, ptrAst: elemAny,
                                    ptrFamily: true, ptrPointee: pointee)
                   else: SymVal(kind: svRef, refAst: elemAny, refPointee: pointee)
      renderContainerElemCell(m, w, pname & "[" & $i & "]", elemSV, limit,
                              visited, acc)
  else: discard

proc buildHeapSnapshot(m: Z3Model, w: var RawWitness, env: Env,
                       params: seq[IRParam],
                       settings: SymexSettings): seq[HeapSnapshotEntry] =
  ## Phase 15 R12 (ADR-0010, witness-format-v3.md); Cluster H H_witness
  ## extends this to the FULL reachable heap graph (ADR-0010 invariant #4),
  ## not just top-level ref/ptr params. Empty when the SUT has no ref/ptr
  ## params AND no container-of-ref params (the `heapSnapshot` key is ABSENT,
  ## not null — backward compat with every prior cluster's witness).
  ##
  ## Aliasing: two refs that bound to the SAME `Ref_T` address in the model
  ## render as the SAME cell. Pass 1 (UNCHANGED from pre-H_witness) evaluates
  ## each ref/ptr PARAM's address const under the model and groups by the
  ## resulting rendering; the lexicographically-FIRST param name in a group is
  ## the PRIMARY and carries `pointsTo`; the rest carry `aliasRef = <primary>`
  ## (and no `pointsTo`) — preserved byte-for-byte so param-vs-param aliasing
  ## behaviour never changes. `visited` (address rendering -> the name
  ## registered for it) is then SEEDED from this param-primary table before
  ## any recursion, so a reachable cell that turns out to share a PARAM's
  ## address (the "one-hop alias" shape, `p.next == q`) always renders as an
  ## alias of that param, never a duplicate cell. Nil refs (`value == "nil"`)
  ## are never aliased to a non-nil cell and carry no `pointsTo`.
  ##
  ## `value` is the model rendering of the abstract address (`$m.eval(refAst)`);
  ## the address-rendering string doubles as the alias-group key. Nil is
  ## detected by comparing that rendering against the evaluated `nil_<typeId>`
  ## const. `limit` (`effectiveHeapDepthLimit`, the SAME budget the walker's
  ## own `heapDepthExhausted` enforces) bounds recursion depth; a `visited` set
  ## makes a cycle (self-loop or ring) terminate via `aliasRef` rather than
  ## infinite recursion — see `renderRefFieldValue`.
  let limit = effectiveHeapDepthLimit(settings)
  # The ref/ptr params, in declaration order (the snapshot preserves it).
  var refParams: seq[IRParam]
  for p in params:
    if not env.hasKey(p.name): continue
    let sv = env[p.name]
    if sv.kind in {svRef, svPtr}:
      let pointee = if sv.kind == svRef: sv.refPointee else: sv.ptrPointee
      if pointee != nil: refParams.add p
  # Pass 1: per-param address rendering + nil flag; and, per non-nil address
  # group, the lexicographically-FIRST param name (the alias-group PRIMARY that
  # carries `pointsTo`).
  var addrOf = initTable[string, string]()   ## param name -> address rendering
  var isNilOf = initTable[string, bool]()     ## param name -> nil?
  var primaryFor = initTable[string, string]()## address rendering -> primary name
  for p in refParams:
    let sv = env[p.name]
    let pointee = if sv.kind == svRef: sv.refPointee else: sv.ptrPointee
    let typeId = refPointeeTypeId(pointee)
    let addrAst = if sv.kind == svRef: sv.refAst else: sv.ptrAst
    let addrRendering = $m.eval(addrAst)
    addrOf[p.name] = addrRendering
    var isNil = false
    if currentNilConsts.hasKey(typeId):
      isNil = ($m.eval(currentNilConsts[typeId]) == addrRendering)
    isNilOf[p.name] = isNil
    if not isNil:
      if (not primaryFor.hasKey(addrRendering)) or
         (p.name < primaryFor[addrRendering]):
        primaryFor[addrRendering] = p.name
    registerNominalIfFull(pointee)  ## H_witness: seed the nominal registry up
                                    ## front so a self-referential field's
                                    ## placeholder always resolves.
  # H_witness: seed the shared visited/alias map from the param-primary table.
  var visited = initTable[string, string]()
  for addrRendering, primaryName in primaryFor:
    visited[addrRendering] = primaryName
  # Pass 2: emit one entry per ref/ptr PARAM. Param-vs-param RELATIVE order is
  # UNCHANGED (still one `.add` per `p in refParams`, in declaration order).
  # H_witness swaps the composite-pointee rendering from the flat `"<object>"`
  # placeholder to a real recursive descent (`renderObjectFields`), which
  # appends new REACHABLE, non-param cell entries into `result` as a side
  # effect DURING the `pointsTo` computation — so a param with ref-typed
  # fields now has its DISCOVERED CHILDREN precede its own entry in `result`
  # (a flat param with no ref fields is entirely unaffected: no children are
  # ever discovered for it, so its position is unchanged). Entry ORDER was
  # never a documented contract (existing tests key off `.name`, not
  # position), so this is not a regression.
  for p in refParams:
    let sv = env[p.name]
    let pointee = if sv.kind == svRef: sv.refPointee else: sv.ptrPointee
    let sortName = "Ref_" & refPointeeTypeId(pointee)
    let addrRendering = addrOf[p.name]
    var entry = HeapSnapshotEntry(
      name: p.name, sort: sortName,
      value: (if isNilOf[p.name]: "nil" else: addrRendering),
      pointsTo: none(string), aliasRef: none(string))
    if not isNilOf[p.name]:
      if primaryFor[addrRendering] == p.name:
        if pointee.kind == itTuple:
          let addrAst = if sv.kind == svRef: sv.refAst else: sv.ptrAst
          entry.pointsTo = some(renderObjectFields(m, w, p.name, addrAst,
            pointee, 0, limit, visited, result))
        else:
          entry.pointsTo = pointeeRendering(w, p.name)   ## unchanged primitive path
      else:
        entry.aliasRef = some(primaryFor[addrRendering])
    result.add entry
  # H_witness: container-typed params (seq/array/tuple of ref/ptr elements) —
  # purely additive (see `renderContainerElemsIntoSnapshot`'s doc comment).
  for p in params:
    if not env.hasKey(p.name): continue
    let sv = env[p.name]
    if sv.kind in {svArray, svSeq, svTuple}:
      renderContainerElemsIntoSnapshot(m, w, p.name, sv, limit, visited, result)

proc extractWitness(m: Z3Model, env: Env, params: seq[IRParam],
                    tabKeys: Table[string, HashSet[string]],
                    setMembers: Table[string, HashSet[int64]],
                    settings: SymexSettings
                    ): RawWitness =
  result.paramOrder = newSeq[string](params.len)
  for i, p in params:
    result.paramOrder[i] = p.name
    extractFromSymVal(m, result, p.name, env[p.name], tabKeys, setMembers)
  # Phase 15 R12: the heap-snapshot witness — after every leaf is populated,
  # so `pointeeRendering` can read back each ref/ptr param's pointee value.
  # Cluster H H_witness: `buildHeapSnapshot` now ALSO writes new leaves into
  # `result` (recursively-discovered cells' primitive fields), hence `var`.
  result.heapSnapshot = buildHeapSnapshot(m, result, env, params, settings)

var symexZ3CallCount* {.threadvar.}: int
  ## Phase 13 cycle 1. Increments on every Z3 `s.check()` invocation
  ## inside symex. Always-on (no compile-time gate) — the increment
  ## cost is negligible against a Z3 query and tests observe it to
  ## assert "cache hit, Z3 not called" contracts. Re-exported by
  ## `nelli/symex` so consumers can `import nelli/symex` and
  ## reach it directly.

proc trySolve(ctx: Z3Context,
              path: Path,
              params: seq[IRParam],
              settings: SymexSettings = defaultSymexSettings(),
              tabKeys: Table[string, HashSet[string]] = initTable[string, HashSet[string]](),
              setMembers: Table[string, HashSet[int64]] = initTable[string, HashSet[int64]](),
              initialEnv: Env = initOrderedTable[string, SymVal]()
              ): tuple[status: SymexStatusKind, witness: RawWitness] =
  let s = newSolver(ctx)
  # Z3 bound: deterministic logical-step count (NOT wall-clock) so
  # the same SUT + Z3 build produces identical outcomes across
  # machines. `rlimit = 0` is Z3's documented "unbounded"; non-zero
  # truncates to `Z3_L_UNDEF` (sxUnknown). `random_seed = 0'u`
  # overrides any caller's `setGlobalParam` so the verdict cache's
  # determinism guarantee doesn't depend on undocumented Z3 defaults.
  let solverParams = newParams(ctx)
  solverParams.set("rlimit", settings.budget.queryRLimit)
  solverParams.set("random_seed", 0'u)
  s.setParams(solverParams)
  for c in path.pc:
    s.add(c)
  # Phase 16 ADR-0012: defect-survivor feasibility facts (the `not overflow`/
  # `not divByZero`/`not parseIntRaise` negations) are asserted alongside `pc`,
  # so the effective path condition (pc ++ defectSurvivorPc) is identical to the
  # pre-ADR-0012 behaviour for every non-closure path. The split only changes
  # which of these a closure's return-axiom uses as its implication guard.
  for c in path.defectSurvivorPc:
    s.add(c)
  # Phase 15 S10a / CR-9 A0: drain the parseInt digits soundness-gate constraints
  # (`toInt(s) >= 0` on the active branch) into every check. Sound because each
  # clause references the specific param string var's Z3 AST (identical across
  # paths) and only narrows non-digit models.
  # CR-9 A0: use `parseIntGateConstraintsLive()` (fwd-decl; defined after WalkCtx)
  # which returns the WalkCtx field when a walk is active, else the threadvar.
  # Mutually exclusive — never both — so no gate constraint is double-asserted.
  for c in parseIntGateConstraintsLive():
    s.add(c)
  # Phase 15 C2b (ADR-0009 D6): drain the GROUND closure-call axioms
  # (`implies(branch_conds_i, funcSym(env, args) == v_i)`) into every check.
  # Each is a CLOSED implication tied to a specific call occurrence's funcSym
  # application — vacuously true off its branch, so globally sound to add (the
  # `parseIntGateConstraints` idiom). The funcSym is applied at the GROUND
  # `(env, args)` of the occurrence, NOT universally quantified (the G4 hang
  # lesson) — so the query stays in QF_UF... and does not MBQI-loop.
  for c in currentClosureCallAxioms:
    s.add(c)
  # Round-4 Slice B (ADR-0026): drain the strip decomposition constraints
  # into every check — definitional clauses over per-occurrence fresh
  # strings (see `stripDecompConds`' doc for the soundness argument).
  for c in stripDecompConds:
    s.add(c)
  inc symexZ3CallCount
  let r = s.check()
  case r
  of zsSat:
    let m = s.model()
    # Use initialEnv when provided — mutations may have rebound params
    # to post-store SymVals; the witness wants the pre-call value.
    let envForExtract = if initialEnv.len > 0: initialEnv else: path.env
    # ADR-0013 D5 (Slice 2): snapshot the WINNING path's heaps so the witness
    # serializer can select a ref-to-variant pointee's active-arm field values.
    currentVariantHeaps = path.heaps
    (status: sxSat,
     witness: extractWitness(m, envForExtract, params, tabKeys, setMembers,
                             settings))
  of zsUnsat:
    (status: sxUnsat, witness: RawWitness())
  of zsUnknown:
    (status: sxUnknown, witness: RawWitness())

type
  LoopFrame = object
    ## Phase 6: walker-level loop frame. `break`/`continue` consult
    ## the top entry to dispatch correctly.
    breakPaths*:    seq[Path]
    continuePaths*: seq[Path]

  CallFrame = object
    ## A walker-level call frame. The runtime pushes one of these per
    ## active inline-call expansion; isReturn consults the top entry
    ## to wire the returned value into the caller's `retSym`.
    callee:        string
    retSym:        SymVal           ## the fresh symbol returned values bind to
    retName:       string           ## "" for void
    returnedPaths: seq[Path]        ## paths that hit `return` inside this call

  HandlerFrame = object
    ## Phase 15 E1. One active `try`'s except-arms + finally, pushed onto the
    ## current call frame's `handlerStack` while the try-body is walked.
    ## Structural in E1 (the walker stubs `isTry` before any frame is pushed);
    ## E3+ populates and consults these on raise-flow propagation.
    handlers:     seq[ExceptHandler]
    finallyBlock: IRStmt   ## nil if no finally

  ExnRecord = object
    ## Phase 15 E1. An in-flight exception value (type + optional message).
    ## Set by the raise-flow walker (E2b+); unset/`none` until then.
    typeId: string
    msg:    Option[string]

  WalkerStatics = object ## Phase 15 Z4: per-walker state, immutable after parse;
                         ## E1 fills exnTable/userExnHierarchy (empty until E4a),
                         ## C2a (closureSyms), R1 (refSorts...).
    exnTable:         Table[string, seq[string]]
                        ## Phase 15 E1: static exception-type table (each type
                        ## name -> its full ancestor chain). Empty in E1;
                        ## populated at E4 from `exn_hierarchy.exnTypeTable`.
    userExnHierarchy: Table[string, string]
                        ## Phase 15 E1: user-exn `child -> parent` map.
                        ## Populated E4a (`getImpl` walk); empty until then.
    distinctSorts: Table[string, DistinctSortEntry]
                        ## Phase 15 G4 (ADR-0008 D4): the per-walker distinct-
                        ## sort cache (one full DistinctSortEntry per distinct
                        ## type name, with sort + inject + eject func-decls).
                        ## CR-9 Stage 4: now the LIVE store (written by
                        ## `syncDistinctSortEntry` from `allocDistinctSym` via
                        ## `currentWalkCtxPtr`); threadvar `currentDistinctSorts`
                        ## remains the fallback for probe/pre-walk allocations.
    distinctSortNames: seq[string]
                        ## Phase 15 G4 alloc-order hook: the ordered list of
                        ## distinct-sort names first allocated this run (so a
                        ## test can assert "two sorts allocated" for a chain).
                        ## CR-9 Stage 4: now the LIVE store in WalkerStatics
                        ## (mirroring the `distinctSortNames` threadvar).
                        ## Populated by `syncDistinctSortEntry` when in a walk.
    closureSyms: Table[ClosureSymKey, RawZ3FuncDecl]
                        ## Phase 15 C2a (ADR-0009 Consequences): the per-site
                        ## closure funcSym memo (one uninterpreted decl per
                        ## (site, env/param sorts)), shared across frames. The
                        ## LIVE populator is the `currentClosureSyms` threadvar
                        ## (`lower(iekLambda)` has no WalkCtx); this field mirrors
                        ## it after the walk for post-run inspection. CR-9 Stage 4c:
                        ## LIVE store during a walk (written by `syncClosureSymEntry`).
    closureBodies: Table[tuple[siteHash: int64, declOrder: int], ClosureBody]
                        ## Phase 15 C2b: per-site lambda body + signature stash,
                        ## mirroring `currentClosureBodies`. Populated by
                        ## `syncClosureBodyEntry` (from `buildClosure`) when a walk
                        ## is active. CR-9 Stage 4d: LIVE store during a walk so
                        ## `applyClosureGround` reads statics via nil-guard.
                        ## Threadvar remains fallback for pre-walk paths.
    refSorts: Table[string, RawZ3Sort]
                        ## Phase 15 R1 (ADR-0010): the per-walker `Ref_T`
                        ## uninterpreted sort cache, keyed by pointee typeId
                        ## (one fresh `mkUninterpretedSort("Ref_" & typeId)`
                        ## per distinct pointee type, shared across ALL paths —
                        ## the sort is per-WALKER, not per-path). The LIVE
                        ## populator is the `currentRefSorts` threadvar
                        ## (`allocateSym(itRef)` has no WalkCtx); this field
                        ## mirrors it after the walk for post-run inspection.
    nilConsts: Table[string, Z3AnyAst]
                        ## Phase 15 R1 (ADR-0010): the distinguished `nil_<typeId>`
                        ## constant of each `Ref_T` sort, one per pointee typeId.
                        ## Allocated alongside the sort in `allocRefSort` and
                        ## NEVER returned by the freshness mechanism (R2), so a
                        ## fresh alloc is always distinct from nil. CR-9 Stage 4:
                        ## LIVE store during a walk (written by `syncRefSortEntry`);
                        ## pre-walk/probe paths use `currentNilConsts` threadvar.
  EscapedRaise = object
    ## Phase 15 E3. A raise that escaped its OWN call frame's handler stack
    ## without being caught — the per-frame channel the `isCall` descent arm
    ## drains after the callee returns, re-routing each escaped raise into the
    ## CALLER's handler stack (inter-procedural propagation). Carries the
    ## raise-site `Path` so heap/pc state at the raise point is preserved across
    ## the frame boundary (R1b merge — structurally threaded; inert until
    ## Cluster R).
    path:   Path
    typeId: string
    msg:    Option[string]

  CallFrameCtx = object  ## Phase 15 Z4: state pushed/popped per call descent;
                         ## E1 fills handlerStack/inFlightExn, C2b closureInlineCount.
    closureInlineCount: int           ## Phase 15 C2b (ADR-0009 D6): the depth of
                                      ## NESTED closure-application descents at
                                      ## this frame. `lowerClosureCall` increments
                                      ## it before descending the lambda body and
                                      ## restores it after; a descent that would
                                      ## push past `settings.maxClosureInlineCount`
                                      ## is refused (`ceInlineBudgetExceeded`). C2a
                                      ## deferred this field (no descent until C2b).
    handlerStack: seq[HandlerFrame]   ## Phase 15 E1: per-frame active tries.
    inFlightExn:  Option[ExnRecord]   ## Phase 15 E1: the exn being propagated.
    escaped:      seq[EscapedRaise]   ## Phase 15 E3: raises that escaped THIS
                                      ## frame's handlers; drained by the caller's
                                      ## isCall arm for inter-proc propagation.
    caught:       seq[tuple[depth: int, path: Path]]
                                      ## Phase 15 E3: handler-body continuation
                                      ## paths from raises CAUGHT in this frame,
                                      ## tagged by the catching try's handler-stack
                                      ## depth. The owning `isTry` (at that depth)
                                      ## claims its entries after walking its body,
                                      ## merging them with the body's normal
                                      ## fall-through. This is what makes a caught
                                      ## raise EXIT the try rather than resume the
                                      ## try body after the raise site.
    pendingRaise: seq[tuple[depth: int, path: Path, typeId: string,
                            msg: Option[string]]]
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

  WalkCtx = object
    z3:        Z3Context
    target:    SymexTarget
    params:    seq[IRParam]
    found:     seq[RawResult]   ## Phase 15 Z4: was Option[RawResult]. Accumulated
                                ## findings; shouldStop halts on the first sxSat
                                ## (sxRaised added to the stop set in E2a).
    statics:   WalkerStatics    ## Phase 15 Z4 — populated E1/C2a/R1
    frame:     CallFrameCtx     ## Phase 15 Z4 — populated E1/C2a. The CURRENT
                                ## call frame's exception context (handler stack
                                ## + in-flight exn). Per-frame: a try opened in a
                                ## callee is invisible to the caller after return.
    frameStack: seq[CallFrameCtx]  ## Phase 15 E1: saved caller frames. Every
                                ## isCall/generic/closure descent `pushFrame`s
                                ## (saves `frame`, installs a fresh empty one)
                                ## before walking the callee body and `popFrame`s
                                ## on return. See pushFrame/popFrame below.
    sawUnknown: bool
    settings:  SymexSettings
    procs:     Table[string, ProcSig]
    callStack: seq[CallFrame]
    callStats: Table[string, CallStat]
    loopStack: seq[LoopFrame]   ## Phase 6: nested-loop tracking
    callCache: Table[string, CallCacheEntry]
    activeCalls: HashSet[string]
    synthZ3:   int
    tabKeys:   Table[string, HashSet[string]]
    setMembers: Table[string, HashSet[int64]]
    initialEnv: Env   ## snapshot before walking, used so witness
                      ## extraction reads the INITIAL param SymVals
                      ## (not values after `isAssign` mutations).
    # CR-9 Stage 5 Group-3 error/hint sinks:
    freshnessCapHints: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (R2). LIVE accumulator for
                      ## `heFreshnessCapExceeded` (sevHint) during a walk.
                      ## `syncFreshnessCapHint` appends here when
                      ## `currentWalkCtxPtr != nil`; verdict-assembly reads
                      ## this field directly from the WalkCtx local. Threadvar
                      ## `freshnessCapHints` remains fallback for probe paths.
    heapDepthErrors: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (R9). LIVE accumulator for
                      ## `heDepthExhausted` (sevError) during a walk.
                      ## `heapDepthExhausted` has `w: var WalkCtx` so it
                      ## writes directly to `w.heapDepthErrors`; verdict-
                      ## assembly reads this field. Threadvar `heapDepthErrors`
                      ## remains fallback (no out-of-walk caller exists today).
    newFieldZeroErrors: seq[SymexErrorInfo]
                      ## Cluster H Step C. LIVE accumulator for
                      ## `heNewFieldZeroUnsupported` (sevError) during a walk.
                      ## The `isNew` walker arm has `w: var WalkCtx` so it
                      ## writes directly to `w.newFieldZeroErrors`; verdict-
                      ## assembly reads this field. Threadvar
                      ## `newFieldZeroErrors` remains fallback.
    walkDegradeErrors: seq[SymexErrorInfo]
                      ## v64 (chapulin catalog #5(b)/#6, Invariant 7). LIVE
                      ## accumulator for in-walk classified degrades that
                      ## occur OUTSIDE the lowering wrappers (whose threadvar
                      ## sink is reset at every wrapper entry): the
                      ## `maxLoopUnwind` k-unroll exhaustion and
                      ## `maxFrontierSize` prune sites (`beBudgetExhausted`)
                      ## and the isReturn composite-return drain guard
                      ## (`feUnsupportedOp`) — all previously either set
                      ## `w.sawUnknown` BARE (empty-errors sxUnknown) or
                      ## raised. Every site has `w: var WalkCtx`, so no
                      ## threadvar twin is needed. Drained (dedup'd by
                      ## message) into every verdict branch, exactly the R9
                      ## `heapDepthErrors` idiom.
    ptrFamilyHints: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (R8). LIVE accumulator for `hePtrFamily`
                      ## (sevHint) during a walk. isDeref/isDerefWrite arms
                      ## write directly to `w.ptrFamilyHints` (they have
                      ## `w: var WalkCtx`); verdict-assembly reads this field.
                      ## Threadvar `ptrFamilyHints` remains fallback.
    unknownExnWarnings: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (E4). LIVE accumulator for
                      ## `eeUnknownExnType` (sevWarning) during a walk.
                      ## `routeRaise` has `w: var WalkCtx` so it writes
                      ## directly to `w.unknownExnWarnings`; verdict-assembly
                      ## reads this field. Threadvar `unknownExnWarnings`
                      ## remains fallback for any non-walk callers.
    distinctBijectivityHints: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (G4). LIVE accumulator for
                      ## `geDistinctBijectivitySkipped` (sevHint) during a
                      ## walk. `syncDistinctBijectivityHint` appends here when
                      ## `currentWalkCtxPtr != nil`. Verdict-assembly reads
                      ## this field. Threadvar `distinctBijectivityHints`
                      ## remains fallback for probe/pre-walk callers.
    convFloatToIntDomainConds: seq[Z3Bool]
                      ## R16-2 (parallel raise-fork sink). LIVE accumulator for
                      ## float→int domain-condition predicates deposited by
                      ## `lower(iekConvFloatToInt)` during a walk — the SAME
                      ## `domainCond` pushed to `convFloatToIntBoundConds`, kept
                      ## in a SEPARATE sink so `drainPendingLowerEffects` (which
                      ## consumes `convFloatToIntBoundConds`) does NOT consume
                      ## this one. `drainConvFloatToIntRaises` reads this field
                      ## and forks each `not(domainCond)` as a RangeDefect raise
                      ## from the PRE-narrowing path. `syncConvFloatToIntDomainCond`
                      ## appends here when `currentWalkCtxPtr != nil`. Reset
                      ## alongside `convFloatToIntBoundConds` at every reset site.
    extractionErrors: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (F7/E8). LIVE accumulator for
                      ## `feExtractionFailed`/`eeUninterpRefExtraction`/
                      ## `ceNotImplemented` (all sevError or sevHint) during
                      ## a walk. `syncExtractionError` appends here when
                      ## `currentWalkCtxPtr != nil`. Verdict-assembly reads
                      ## this field (sat-branch only). Threadvar
                      ## `extractionErrors` remains fallback.
    closureCallErrors: seq[SymexErrorInfo]
                      ## CR-9 Stage 5 (C2b). LIVE accumulator for
                      ## `ceClosureUnknownCallee`/`ceInlineBudgetExceeded`/
                      ## `ceUnsupportedHof` (all sevError) during a walk.
                      ## `syncClosureCallError` appends here when
                      ## `currentWalkCtxPtr != nil`. Verdict-assembly reads
                      ## this field (all branches, forces sxUnknown). Threadvar
                      ## `currentClosureCallErrors` remains fallback.
    convFloatToIntBoundConds: seq[Z3Bool]
                      ## CR-9 Stage 6 Group-1 (convFloatToIntBoundConds
                      ## migration). LIVE accumulator for float→int domain-bound
                      ## constraints deposited by `lower(iekConvFloatToInt)`
                      ## during a walk. `syncConvFloatToIntBoundCond` appends
                      ## here when `currentWalkCtxPtr != nil`. Drained by
                      ## `drainConvFloatToIntBounds` which reads this field
                      ## (not the threadvar) when a walk is active. Threadvar
                      ## `convFloatToIntBoundConds` remains fallback for
                      ## probe-path lower() calls. Reset (to @[]) in
                      ## `lowerInExpr`/`lowerBoolInExpr` (via w param) and
                      ## in `drainConvFloatToIntBounds` after drain.
    parseIntRaiseConds: seq[Z3Bool]
                      ## CR-9 Stage 6 Group-2 (parseIntRaiseConds migration).
                      ## LIVE accumulator for parseInt raise predicates deposited
                      ## by `lower(iekStrToInt)` during a walk.
                      ## `syncParseIntRaiseCond` appends here when
                      ## `currentWalkCtxPtr != nil`. Drained by
                      ## `drainParseIntRaises` which reads this field (not the
                      ## threadvar) when a walk is active. Threadvar
                      ## `parseIntRaiseConds` remains fallback for probe paths.
                      ## Reset in `lowerInExpr`/`lowerBoolInExpr` (via w param)
                      ## and in `drainParseIntRaises` after drain.
    divByZeroConds: seq[Z3Bool]
                      ## R16-3 (divByZeroConds). LIVE accumulator for
                      ## div/mod-by-zero predicates deposited by `lowerArith`
                      ## for bDiv/bMod ops during a walk.
                      ## `syncDivByZeroCond` appends here when
                      ## `currentWalkCtxPtr != nil`. Drained by
                      ## `drainDivByZeroRaises` (via `drainScalarRaiseForks`).
                      ## Reset alongside `parseIntRaiseConds` at every reset site.
    overflowConds: seq[Z3Bool]
                      ## R16-4 (overflowConds). LIVE accumulator for signed
                      ## integer overflow predicates deposited by `lowerArith`
                      ## for bAdd/bSub/bMul ops on signed BV operands during
                      ## a walk. `syncOverflowCond` appends here when
                      ## `currentWalkCtxPtr != nil`. Drained by
                      ## `drainOverflowRaises` (via `drainScalarRaiseForks`).
                      ## Reset alongside `divByZeroConds` at every reset site.
    strIndexOobConds: seq[Z3Bool]
                      ## RFC-chapulin-hardening SND-4 (ADR-0024). LIVE
                      ## accumulator for string-index (`s[i]`) out-of-bounds
                      ## predicates deposited by `lowerStrArm`'s `iekStrAt` arm
                      ## during a walk. `syncStrIndexOobCond` appends here when
                      ## `currentWalkCtxPtr != nil`. Drained by
                      ## `drainStrIndexRaises` (via `drainScalarRaiseForks`).
                      ## Reset alongside `overflowConds` at every reset site.
    parseIntGateConstraints: seq[Z3Bool]
                      ## CR-9 A0 (S10a parseInt soundness gate). LIVE accumulator
                      ## for `toInt(s) >= 0` gate constraints deposited by
                      ## `lower(iekStrToInt)` during a walk. `syncParseIntGateConstraint`
                      ## appends here when `currentWalkCtxPtr != nil`. Read in
                      ## `trySolve` via field-else-threadvar (never both, so no gate
                      ## constraint is double-asserted). Threadvar
                      ## `parseIntGateConstraints` remains fallback for probe-path
                      ## lower() calls. Zero-initialised at WalkCtx construction;
                      ## threadvar reset at `runSymexImpl` entry remains.
    callerHeaps: Table[string, Z3AnyAst]
                      ## CR-9 Stage 6 Group-3 (currentCallerHeaps migration).
                      ## LIVE copy of the caller path's heaps, written by
                      ## `seedCallerHeapInWalkCtx` when a walk is active.
                      ## `applyClosureGround` reads from this field (not the
                      ## threadvar) when `currentWalkCtxPtr != nil`.
    callerHeapDepth: int
                      ## CR-9 Stage 6 Group-3 (currentCallerHeapDepth
                      ## migration). Companion to `callerHeaps`.
    callerAllocCounters: Table[string, int]
                      ## CR-9 Stage 6 Group-3 (currentCallerAllocCounters
                      ## migration). Companion to `callerHeaps`.
    callerLiveRefs: Table[string, seq[Z3AnyAst]]
                      ## CR-9 Stage 6 Group-3 (currentCallerLiveRefs migration).
                      ## Companion to `callerHeaps` (CR-5 freshness seeding).
    closureExitHeaps: Table[string, Z3AnyAst]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitHeaps
                      ## migration). LIVE exit-heap from the most recent
                      ## `applyClosureGround` call. Written by
                      ## `applyClosureGround`; drained by `drainClosureExitHeap`
                      ## which reads this field (not the threadvar) when a walk
                      ## is active. Threadvar `currentClosureExitHeaps` remains
                      ## fallback for the no-walk path.
    closureExitAllocCounters: Table[string, int]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitAllocCounters
                      ## migration). Companion to `closureExitHeaps`.
    closureExitLiveRefs: Table[string, seq[Z3AnyAst]]
                      ## CR-9 Stage 6 Group-4 (currentClosureExitLiveRefs
                      ## migration). Companion to `closureExitHeaps`.
    closureDidMutateHeap: bool
                      ## CR-9 Stage 6 Group-4 (currentClosureDidMutateHeap
                      ## migration). True iff `applyClosureGround` merged at
                      ## least one exit path this call; `drainClosureExitHeap`
                      ## skips the merge when false (fast path for heap-write-
                      ## free closures). Written by `applyClosureGround`,
                      ## read by `drainClosureExitHeap`, reset by
                      ## `seedCallerHeapInWalkCtx` (per-call reset, NI-1).

  CallCacheEntry = object
    ## Function summary: the (callee, argShape) pair maps to the Z3
    ## variable representing the return value plus the constraint
    ## delta added to the returning path. On a cache hit, the entry's
    ## retSym binds to the caller's retName and the pcDelta extends
    ## the current path's pc — no re-walking required.
    retSym:  SymVal
    pcDelta: seq[Z3Bool]

proc syncRefSortEntry*(typeId: string, srt: RawZ3Sort, nc: Z3AnyAst) =
  ## CR-9 Stage 4 (currentRefSorts/currentNilConsts migration). If
  ## `currentWalkCtxPtr != nil` (a walk is active), copies `srt` and `nc` into
  ## `WalkCtx.statics.refSorts[typeId]` and `.nilConsts[typeId]` so that
  ## `WalkerStatics` becomes the LIVE store for the ref-sort cache during a walk.
  ## When `currentWalkCtxPtr == nil` (probe paths: C2a construction probes,
  ## `allocateSym(itRef)` outside a walk), this is a no-op; the threadvar cache
  ## (`currentRefSorts`/`currentNilConsts`) remains the sole store for those paths.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].statics.refSorts[typeId] = srt
    wp[].statics.nilConsts[typeId] = nc

proc syncDistinctSortEntry*(name: string, entry: DistinctSortEntry) =
  ## CR-9 Stage 4 (currentDistinctSorts/distinctSortNames migration). If
  ## `currentWalkCtxPtr != nil` (a walk is active), copies `entry` into
  ## `WalkCtx.statics.distinctSorts[name]` and appends `name` to
  ## `.distinctSortNames`. No-op when no active walk (probe paths and pre-walk
  ## env-setup calls); `currentDistinctSorts`/`distinctSortNames` threadvars
  ## remain the sole store for those paths.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].statics.distinctSorts[name] = entry
    wp[].statics.distinctSortNames.add name

proc syncClosureSymEntry*(key: ClosureSymKey, fd: RawZ3FuncDecl) =
  ## CR-9 Stage 4 (currentClosureSyms migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), copies `fd` into `WalkCtx.statics.closureSyms[key]`
  ## so that `WalkerStatics.closureSyms` is the LIVE store during a walk.
  ## No-op when no active walk (C2a construction probes and probe functions
  ## that directly reset/read `currentClosureSyms`); the threadvar remains
  ## the sole store for those paths.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].statics.closureSyms[key] = fd

proc syncClosureBodyEntry*(siteKey: tuple[siteHash: int64, declOrder: int],
                           cb: ClosureBody) =
  ## CR-9 Stage 4 (currentClosureBodies migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), copies `cb` into `WalkCtx.statics.closureBodies[siteKey]`
  ## so that `WalkerStatics.closureBodies` is the LIVE store during a walk.
  ## No-op when no active walk; `currentClosureBodies` remains the sole store.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].statics.closureBodies[siteKey] = cb

proc syncFreshnessCapHint*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (freshnessCapHints migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), appends `info` to `WalkCtx.freshnessCapHints` so that
  ## the WalkCtx field is the LIVE store for this hint during a walk. No-op when
  ## `currentWalkCtxPtr == nil` (probe paths, pre-walk assertFreshness calls);
  ## the `freshnessCapHints` threadvar remains the sole store for those paths.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].freshnessCapHints.add info

proc syncDistinctBijectivityHint*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (distinctBijectivityHints migration). If
  ## `currentWalkCtxPtr != nil` (a walk is active), appends `info` to
  ## `WalkCtx.distinctBijectivityHints`. No-op when `currentWalkCtxPtr == nil`
  ## (probe paths and pre-walk allocDistinctSym calls from env setup).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].distinctBijectivityHints.add info

proc syncConvFloatToIntDomainCond*(cond: Z3Bool) =
  ## R16-2 (convFloatToIntDomainConds migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), appends `cond` to `WalkCtx.convFloatToIntDomainConds`
  ## so the field is the LIVE store for the raise-fork sink during a walk.
  ## No-op when `currentWalkCtxPtr == nil` (probe-path lower() calls outside an
  ## active walk — no raise drain runs on probe paths).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].convFloatToIntDomainConds.add cond

proc syncExtractionError*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (extractionErrors migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), appends `info` to `WalkCtx.extractionErrors` so the
  ## field is the LIVE store for extraction failures during a walk. No-op when
  ## `currentWalkCtxPtr == nil` (extractLeaf/extractFromSymVal are called from
  ## trySolve which runs inside walk arms — ptr is always set at these sites —
  ## but the nil-guard ensures correctness if that assumption ever changes).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].extractionErrors.add info

proc syncClosureCallError*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (currentClosureCallErrors migration). If
  ## `currentWalkCtxPtr != nil` (a walk is active), appends `info` to
  ## `WalkCtx.closureCallErrors`. No-op when `currentWalkCtxPtr == nil`
  ## (lowerClosureCall short-circuits early when ptr==nil, but
  ## applyClosureGround/lowerHofCall have nil-guard checks — this proc
  ## stays safe for all paths).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].closureCallErrors.add info

proc syncConvFloatToIntBoundCond*(cond: Z3Bool) =
  ## CR-9 Stage 6 Group-1 (convFloatToIntBoundConds migration). If
  ## `currentWalkCtxPtr != nil` (a walk is active), appends `cond` to
  ## `WalkCtx.convFloatToIntBoundConds` so the field is the LIVE store for
  ## float→int domain-bound constraints during a walk. No-op when
  ## `currentWalkCtxPtr == nil` (lower() can be called from probe paths via
  ## c1ClosurePoCApply / applyClosureGround outside an active walk).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].convFloatToIntBoundConds.add cond

# NOTE (R5): these four sync procs share a body modulo the sink field, but each
# is FORWARD-DECLARED above (~909-943) because the lowering code calls them long
# before this point — and a template-generated proc does not satisfy a forward
# declaration in Nim. So they stay as explicit definitions (the ~230-line drain
# dedup, `genRaiseForkDrain` below, is the substantive R5 consolidation; these
# 6-liners are not forward-decl-compatible with that pattern). Keep the bodies
# identical if you edit one.
proc syncParseIntRaiseCond*(cond: Z3Bool) =
  ## CR-9 Stage 6 Group-2. Appends `cond` to `WalkCtx.parseIntRaiseConds` (the
  ## LIVE store) when a walk is active; no-op on probe paths (currentWalkCtxPtr
  ## == nil — no drain runs there).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].parseIntRaiseConds.add cond

proc syncDivByZeroCond*(cond: Z3Bool) =
  ## R16-3. div/mod-by-zero raise predicates. See syncParseIntRaiseCond.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].divByZeroConds.add cond

proc syncOverflowCond*(cond: Z3Bool) =
  ## R16-4. signed-integer-overflow raise predicates. See syncParseIntRaiseCond.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].overflowConds.add cond

proc syncStrIndexOobCond*(cond: Z3Bool) =
  ## SND-4. string-index OOB raise predicates. See syncParseIntRaiseCond.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].strIndexOobConds.add cond

proc syncParseIntGateConstraint*(c: Z3Bool) =
  ## CR-9 A0 (parseIntGateConstraints migration). If `currentWalkCtxPtr != nil`
  ## (a walk is active), appends `c` to `WalkCtx.parseIntGateConstraints` so
  ## the field is the LIVE store for parseInt digits-gate constraints during a
  ## walk. No-op when `currentWalkCtxPtr == nil` (lower() can be called from
  ## probe paths outside an active walk).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].parseIntGateConstraints.add c

proc parseIntGateConstraintsLive*(): seq[Z3Bool] =
  ## CR-9 A0. Returns the active parseInt digits-gate constraints for
  ## `trySolve` to assert: WalkCtx field when a walk is active
  ## (`currentWalkCtxPtr != nil`), else the `parseIntGateConstraints` threadvar.
  ## Mutually exclusive — never both — so no constraint is double-asserted.
  ## Defined after `WalkCtx` so the cast is valid.
  if currentWalkCtxPtr != nil:
    cast[ptr WalkCtx](currentWalkCtxPtr)[].parseIntGateConstraints
  else:
    parseIntGateConstraints

proc seedCallerHeapInWalkCtx*(p: Path) =
  ## CR-9 Stage 6 Groups 3+4. If `currentWalkCtxPtr != nil` (a walk is
  ## active), mirrors `p`'s heap state into the WalkCtx caller-heap fields
  ## AND resets the closure-exit fields to clean state — matching the
  ## NI-1 per-call-site reset that `seedCallerHeapThreadvars` performs on
  ## the threadvars. No-op when `currentWalkCtxPtr == nil` (no walk active).
  ##
  ## Called immediately after `seedCallerHeapThreadvars` at every seed site
  ## so both the threadvar path and the WalkCtx path are kept in sync.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].callerHeaps = p.heaps
    wp[].callerHeapDepth = p.heapDepth
    wp[].callerAllocCounters = p.allocCounters
    wp[].callerLiveRefs = p.liveRefs
    # Reset the closure-exit fields (NI-1 fix — mirror of threadvar reset
    # inside seedCallerHeapThreadvars): each lower() call starts clean so
    # a non-heap-writing closure doesn't carry the previous call's exit-heap
    # into the next lower() drain.
    wp[].closureDidMutateHeap = false
    wp[].closureExitHeaps = initTable[string, Z3AnyAst]()
    wp[].closureExitAllocCounters = initTable[string, int]()
    wp[].closureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()

proc setInFlightThreadvars(inFlight: Option[ExnRecord]) {.inline.} =
  ## Phase 15 E8. Mirror the structural `w.frame.inFlightExn` into the
  ## lower-time threadvars (`currentInFlightTypeId` / `currentInFlightMsg`) that
  ## the no-arg `getCurrentException()` / `getCurrentExceptionMsg()` intrinsics
  ## read in `lower` (a pure Env→SymVal function with no WalkCtx access). Called
  ## at every site that sets/restores `w.frame.inFlightExn` (handler-body entry
  ## and the finally raised-exit walk), keeping the two views in lockstep.
  if inFlight.isSome:
    currentInFlightTypeId = some(inFlight.get.typeId)
    currentInFlightMsg = inFlight.get.msg
  else:
    currentInFlightTypeId = none(string)
    currentInFlightMsg = none(string)

proc pushFrame(w: var WalkCtx) {.inline.} =
  ## Phase 15 E1. Save the current call frame's exception context and install a
  ## fresh, empty one for the callee being descended into. The handler stack is
  ## per-frame: a `try` opened inside the callee is NOT visible to the caller
  ## after the callee returns (popFrame restores the caller's frame verbatim).
  ## Structural in E1 (handlerStack/inFlightExn are always empty until E2b+);
  ## wired now so E3/E5 need not re-audit the call-descent arms.
  w.frameStack.add w.frame
  w.frame = CallFrameCtx()

proc popFrame(w: var WalkCtx) {.inline.} =
  ## Phase 15 E1. Restore the caller's call frame saved by `pushFrame`.
  if w.frameStack.len > 0:
    w.frame = w.frameStack[^1]
    w.frameStack.setLen(w.frameStack.len - 1)

proc shouldStop(w: WalkCtx): bool {.inline.} =
  ## Phase 16 ADR-0012. Halt once the finding that ANSWERS THE TARGET exists.
  ## stkLabel: only an sxSat answers "is the label reachable?" — an incidental
  ## sxRaised (defect found on a sibling path) must NOT stop exploration, or the
  ## label's sxSat is never computed. All raise-flavoured targets: an sxRaised IS
  ## the terminal answer (unchanged).
  for r in w.found:
    if r.status == sxSat: return true
    if r.status == sxRaised and w.target.kind != stkLabel: return true
  false

proc symValHash(sv: SymVal): uint =
  ## Hash of a SymVal's Z3 representation for use as a call-cache key.
  case sv.kind
  of svUninterpRef: astHash(sv.uninterpAst)
  of svFloat32: astHash(sv.fp32)
  of svFloat64: astHash(sv.fp64)
  of svDistinct: astHash(sv.distinctAst) xor symValHash(sv.distinctBaseSym[])  ## G4
  of svClosure:   ## Phase 15 C1: site key + env hash (nominal-for-site, D7).
    var h = uint(sv.closureSite.siteHash) xor (uint(sv.closureSite.declOrder) shl 1)
    if sv.closureEnv != nil: h = h xor symValHash(sv.closureEnv[])
    h
  of svRef:   ## Phase 15 R1a: the Ref_T const ast (never reached in R1a stub).
    astHash(sv.refAst)
  of svPtr:   ## Phase 15 R1a: the ptr const ast.
    astHash(sv.ptrAst) xor (if sv.ptrFamily: 1'u else: 0'u)
  of svBool: astHash(sv.bo)
  of svInt:  astHash(sv.zi)
  of svString: astHash(sv.str)
  of svSeq:
    astHash(sv.seqLen) xor astHash(sv.seqDataRaw)
  of svTable:
    astHash(sv.tabDataRaw) xor astHash(sv.tabPresentRaw)
  of svSet:
    astHash(sv.setMembersRaw)
  of svTuple:
    var h: uint = 0
    for f in sv.fields:
      h = (h shl 1) xor symValHash(f)
    h
  of svArray:
    var h: uint = 0
    for e in sv.arrElems:
      h = (h shl 1) xor symValHash(e)
    h
  of svBV8:  astHash(sv.bv8)
  of svBV16: astHash(sv.bv16)
  of svBV32: astHash(sv.bv32)
  of svBV64: astHash(sv.bv64)
  of svVariant:
    var h = symValHash(sv.vDisc[])
    for tagOrdinal, fields in sv.vArmFields.pairs:
      h = (h shl 1) xor uint(tagOrdinal)
      for f in fields:
        h = (h shl 1) xor symValHash(f)
    h
  of svMultiVariant:
    var h: uint = 0
    for ax in sv.mvAxes:
      h = (h shl 1) xor symValHash(ax.disc[])
      for tagOrdinal, fields in ax.armFields.pairs:
        h = (h shl 1) xor uint(tagOrdinal)
        for f in fields:
          h = (h shl 1) xor symValHash(f)
    h

proc argShapeKey(callee: string, args: seq[SymVal]): string =
  ## (callee, argShapeHash) → a string key. Hash combination is XOR
  ## with bit rotation — collisions are merely cache misses, never
  ## correctness bugs.
  var h: uint = 0
  for a in args:
    h = (h shl 1) xor symValHash(a)
  callee & "#" & $h

# ============================================================================
# Fork-site registry (Phase 15 H1 deep-copy contract — ADR-0010)
# ----------------------------------------------------------------------------
# Every site that creates a CHILD `Path` from a PARENT MUST construct it via
# `forkPath` / `forkPathTainted` (defined above), which deep-copy the
# logical-heap state (`heaps` + `allocCounters` via `deepCopyHeapState`;
# `heapDepth` copies by value). This is the single enforcement point for fork
# isolation so a heap mutation on one branch can never bleed into a
# sibling/parent path. The fresh ROOT path in `runSymex`
# (`let initial = Path(...)`) is one of only TWO raw `Path(` constructions —
# it has no parent and correctly gets empty-default heap fields. The other is
# `applyClosureGround`'s `descentBase` (closure-body descent entry, ~6393):
# also root-like (no parent Path to fork FROM — the closure body descends
# fresh, seeded from the CALLER's threaded heap threadvars rather than a
# parent Path), and — per SND-1b (RFC-chapulin-hardening, walker v39) —
# hardcodes `uncertain: false` deliberately (the descent starts clean;
# SND-1's taint is picked back up via `forkPath`/`forkPathTainted` calls made
# BY `walk()` while descending the body, and read back off each returned
# sub-path's `cp.uncertain` by `applyClosureGround` after the descent, to skip
# axiomatizing any uncertain sub-path into the global `currentClosureCallAxioms`
# sink).
#
# In H1 the tables are empty on every path (the walker neither reads nor writes
# them); the copies are inert until Cluster R populates the heap. They are
# wired now so E/G/C/R need not re-audit the fork sites. New fork sites added
# by E/G/C/R MUST use `forkPath`/`forkPathTainted` and be added to this
# registry; the R-cluster walker comment block supersedes this one.
#
# R3 hardening (post-H1): `forkPath` takes no taint parameter at all — it
# always PROPAGATES `parent.uncertain` to the child, which is the correct
# behavior at every site below except the handful marked "deliberate taint,"
# which call `forkPathTainted` instead. Because the taint argument is no
# longer a bare bool at the call site, "silently drop the parent's taint" is
# not spellable; the two proc names below ARE the taint registry (previously
# enforced only by convention/this comment). The list below still documents
# fork-site provenance for the heap-copy contract.
#
# Fork sites (line numbers reflect post-H1 state):
#   walk(isIf)                       — true/arm-branch fork
#   walk(isIf)                       — else-branch fork
#   walk(isLet)                      — sequential child (binding)
#   walk(isAssign)                   — sequential child (binding)
#   walk(isWhile)                    — loop-body (cond=true) entry
#   walk(isWhile)                    — loop-exit (cond=false)
#   walk(isWhile)                    — unwind-exhausted uncertain path
#   walk(isIndex) Table              — present-key survivor
#   walk(isIndex) seq                — OOB target solve path
#   walk(isIndex) seq                — in-bounds survivor
#   walk(isIndex) array              — OOB target solve path
#   walk(isIndex) array              — in-bounds survivor
#   walk(isVariantReassign)          — static-tag disc reassign
#   walk(isVariantReassignSymbolic)  — per-arm fork (svVariant)
#   walk(isVariantReassignSymbolic)  — per-arm fork (svMultiVariant)
#   walk(isVariantField)             — out-of-arm (fieldDefect) solve path
#   walk(isVariantField)             — in-arm survivor
#   walk(isReturn)                   — returned-path into call frame
#   walk(isCall) opaque              — fresh-retSym uncertain path
#   walk(isCall) depth-bail          — fresh-retSym uncertain path
#   walk(isCall) recursion-cycle     — fresh-retSym uncertain path
#   walk(isCall) cache-hit           — pcDelta-extended survivor
#   walk(isCall) descent             — callee-frame clone (heap threaded in)
#   walk(isCall) return-merge        — post-call survivor (heap threaded out)
#   walk(isAssert)                   — assertion-violation solve path
#   walk(isAssert)                   — assertion-holds survivor
# (26 fork sites; the single ROOT `Path(` in runSymex is excluded by design.)
# ============================================================================

type
  InternalVerdictKind = enum
    ## Phase 15 E2b. PRIVATE intermediate verdict produced by the raise-flow
    ## walker. It is deliberately NOT the public `SymexStatusKind`/`RawResult`:
    ## a raise that is caught by an enclosing handler (E3+) must never surface as
    ## a public `sxRaised`. Only `runSymex` converts an `ivRaised` that escapes
    ## the SUT boundary into a public `RawResult{sxRaised}` via `toPublic`
    ## (Invariant 9 — single boundary conversion).
    ivSat, ivUnsat, ivUnknown, ivRaised

  InternalVerdict = object
    case kind: InternalVerdictKind
    of ivSat:
      satWitness: RawWitness
    of ivUnsat, ivUnknown:
      discard
    of ivRaised:
      raisedTypeId: string
      raisedMsg:    Option[string]
      raisedWitness: RawWitness
      raisedIsDefect: bool   ## Phase 15 E6. True iff the raised type is a Nim
                             ## `Defect` subtype (populated at the boundary from
                             ## `exnTable.isDefect`).

proc typeIdToDefectKind*(typeId: string): DefectKind =
  ## Phase 15 E6. Map a raised exception type id to its `DefectKind` for the
  ## `defectExclusions` membership test. The standard-library Defect families
  ## map to their dedicated kind; the real Nim out-of-memory type is
  ## `OutOfMemDefect` (both spellings resolve, per the E4 hierarchy
  ## reconciliation). EVERY user-defined Defect subtype maps to `dkOther`, so
  ## user defects can only be excluded all-or-none (documented on `dkOther`).
  case typeId
  of "AssertionDefect":    dkAssertionDefect
  of "IndexDefect":        dkIndexDefect
  of "FieldDefect":        dkFieldDefect
  of "RangeDefect":        dkRangeDefect
  of "OutOfMemDefect", "OutOfMemoryDefect": dkOutOfMemoryDefect
  of "StackOverflowDefect": dkStackOverflowDefect
  of "OverflowDefect":     dkOverflowDefect    ## R16-1 (ADR-0011 F3)
  of "DivByZeroDefect":    dkDivByZeroDefect   ## R16-1 (ADR-0011 F3)
  else:                    dkOther

proc toPublic(iv: InternalVerdict): RawResult =
  ## Phase 15 E2b. The SINGLE conversion from a private `InternalVerdict` to a
  ## public `RawResult`, called EXACTLY ONCE per finding at the `runSymex`
  ## boundary (Invariant 9 — no `sxRaised` escapes internal raise-flow code; the
  ## walker accumulates `RawResult`s into `w.found` and only the `ivRaised` path
  ## flows through here). E2b only ever maps `ivRaised` (the other arms exist for
  ## the E3+ handler-propagation machinery that consumes `InternalVerdict`).
  case iv.kind
  of ivRaised:
    RawResult(status: sxRaised,
              raisedTypeId: iv.raisedTypeId,
              raisedMsg: iv.raisedMsg,
              isDefect: iv.raisedIsDefect,   ## Phase 15 E6
              raisedWitness: iv.raisedWitness)
  of ivSat:
    RawResult(status: sxSat, witness: iv.satWitness)
  of ivUnsat:
    RawResult(status: sxUnsat)
  of ivUnknown:
    RawResult(status: sxUnknown)

proc evalRaiseMsg(env: Env, msg: IRExpr): Option[string] =
  ## Phase 15 E2b. Evaluate a `raise newException(T, <msg>)` message expression
  ## to a concrete `Option[string]`. A nil/absent message → `none`. A string
  ## literal (`iekStrLit`) yields its constant value — the common
  ## `newException(T, "literal")` form. Any non-literal message expression has no
  ## single concrete value without a Z3 model on a string sort (deferred to a
  ## later cycle); it conservatively yields `none` so `raisedMsg` is only ever
  ## populated when it is provably exact (Invariant 3 — never a guessed value).
  if msg == nil:
    none(string)
  elif msg.kind == iekStrLit:
    some(msg.sval)
  else:
    none(string)

proc effectiveHeapDepthLimit(settings: SymexSettings): int =
  ## Phase 15 R9 (ADR-0010, Des-LOW-D1 / M9). Resolve the EFFECTIVE heap-depth
  ## budget. `maxHeapDepth = 0` is the unlimited sentinel (consistent with
  ## `maxFrontierSize = 0`): fall back to `maxCallDepth` if > 0, else a hard cap
  ## of 256. There is NO separate unlimited-mode code path — the deref guard is
  ## simply `if limit > 0 and path.heapDepth >= limit`, and this proc never
  ## returns 0 (the hard cap is the floor), so the guard always fires eventually
  ## (no infinite recursive-deref loop).
  if settings.budget.maxHeapDepth > 0: settings.budget.maxHeapDepth
  elif settings.budget.maxCallDepth > 0: settings.budget.maxCallDepth
  else: 256

# heapDepthExhausted moved to runtime_heap.nim (CR-7-deeper Stage 8+).

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]

proc routeRaise(p: Path, typeId: string, msg: Option[string],
                w: var WalkCtx): seq[Path]

proc forkDefect(p: Path, defectCond: Z3Bool, typeId: string,
                msg: Option[string], w: var WalkCtx): seq[Path] =
  ## Phase 16 D1a. Unconditionally fork the defect sub-path (constrained by
  ## `defectCond`) and route it through `routeRaise` so a try/except handler
  ## can CATCH it (gating on the *defect condition* not the *target* is what
  ## lets `try: arr[i] except IndexDefect` be modeled). routeRaise checks
  ## satisfiability via trySolve, respects `defectExclusions` (E6), and at the
  ## SUT boundary surfaces sxRaised{isDefect:true, raisedWitness}. Returns its
  ## result (@[] at the boundary; caught continuations exit via the caught
  ## channel). The caller continues the NON-defect path separately.
  let defectPath = forkPath(p, p.pc & @[defectCond], p.env)
  routeRaise(defectPath, typeId, msg, w)

proc drainConvFloatToIntBounds(p: Path): Path =
  ## Phase 15 CR-3/CR-4. Drain any float→int domain-bounding constraints
  ## accumulated by `lower(iekConvFloatToInt)` during the just-completed
  ## `lower`/`lowerBool` call on path `p`, folding them into the path condition.
  ## Unlike `drainParseIntRaises`, this is NOT a fork: the bounds are a
  ## path-narrowing (they restrict the sat domain, not a branching choice), so we
  ## simply extend `p.pc` with the accumulated constraints and return ONE path.
  ##
  ## Callers MUST reset `convFloatToIntBoundConds = @[]` immediately BEFORE the
  ## `lower`/`lowerBool` call so the drained predicates belong to THIS path only.
  ## Returns `p` unchanged (identity) when no bounds were accumulated.
  ##
  ## CR-9 Stage 6 Group-1: when a walk is active, read from and reset
  ## `WalkCtx.convFloatToIntBoundConds` (the LIVE store); fall back to the
  ## threadvar when `currentWalkCtxPtr == nil` (probe-path lower() calls).
  ## Both stores are reset so a subsequent lower() starts clean (idempotent).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    if wp[].convFloatToIntBoundConds.len == 0:
      convFloatToIntBoundConds = @[]   # keep threadvar reset in sync
      return p
    let conds = wp[].convFloatToIntBoundConds
    wp[].convFloatToIntBoundConds = @[]
    convFloatToIntBoundConds = @[]     # keep threadvar reset in sync
    return forkPath(p, p.pc & conds, p.env)
  # Fallback: no active walk (probe paths).
  if convFloatToIntBoundConds.len == 0:
    return p
  let conds = convFloatToIntBoundConds
  convFloatToIntBoundConds = @[]
  forkPath(p, p.pc & conds, p.env)

template genRaiseForkDrain(procName, field: untyped; gate: static[Option[ArithCheck]];
                            defectType, msg: string) =
  ## R5 dedup. Generates a scalar-raise-fork drain proc of the shape shared by
  ## `drainParseIntRaises`/`drainDivByZeroRaises`/`drainOverflowRaises`/
  ## `drainStrIndexRaises` (was 4 near-identical bodies differing only in the
  ## sink field, an optional settings-gate, the routed defect-type string, and
  ## the message). Each generated proc:
  ##  - reads and resets `field` (the raise-predicate sink accumulated by the
  ##    just-completed `lower`/`lowerBool` call) — from `WalkCtx.field` (the
  ##    LIVE store) when a walk is active, else the module threadvar `field`
  ##    (probe-path `lower()` calls, where no drain runs). Both stores are
  ##    reset so a subsequent lower() starts clean (idempotent).
  ##  - `gate` is `none(ArithCheck)` for an unconditional drain (parseInt/
  ##    str-index — no opt-out) or `some(acFoo)` for a settings-gated drain
  ##    (div-by-zero/overflow). When `gate` is `some` and its value is NOT in
  ##    `w.settings.arithChecks`, or there are no drained predicates, returns
  ##    `@[p]` unchanged — honest-incomplete.
  ##  - otherwise forks each predicate `c` into its own RAISES sub-path
  ##    (`p.pc & @[c]`), routed via E3's `routeRaise(…, defectType, msg, w)`
  ##    (which either transfers it into a surrounding `except` or surfaces a
  ##    public `sxRaised{defectType}` at the SUT boundary, then terminates the
  ##    raise path); the survivor continuation is `p` unchanged, with the
  ##    conjunction of all negated predicates riding in `defectSurvivorPc`
  ##    (ADR-0012: defect-survivor FEASIBILITY facts, not branch selectors —
  ##    asserted by trySolve, inherited by forkPath, excluded from a closure
  ##    return-axiom's implication guard).
  ##
  ## This drain always forks from the POST-lower path `p` directly (unlike
  ## `drainConvFloatToIntRaises`, which forks from the PRE-narrowing path and
  ## is NOT part of this family — see its own doc comment for why).
  proc procName(p: Path, w: var WalkCtx): seq[Path] =
    let conds = block:
      if currentWalkCtxPtr != nil:
        let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
        let c = wp[].field
        wp[].field = @[]
        field = @[]         # keep threadvar reset in sync
        c
      else:
        let c = field
        field = @[]
        c
    # `gate` is a compile-time `static[Option[ArithCheck]]`. `none(ArithCheck)`
    # means "unconditional drain" (parseInt/str-index) — never early-returns on
    # the gate. `some(acFoo)` (div-by-zero/overflow) is settings-gated: skip
    # (honest-incomplete) unless that check is enabled.
    if (gate.isSome and gate.get notin w.settings.arithChecks) or conds.len == 0:
      return @[p]
    for c in conds:
      let raisePath = forkPath(p, p.pc & @[c], p.env)
      discard routeRaise(raisePath, defectType, some(msg), w)
    var negated: seq[Z3Bool]
    for c in conds:
      negated.add(not c)
    let surv = forkPath(p, p.pc, p.env)
    for n in negated: surv.defectSurvivorPc.add n
    @[surv]

## Phase 15 S10b. parseInt raise predicates from `iekStrToInt` — unconditional
## (no settings gate).
genRaiseForkDrain(drainParseIntRaises, parseIntRaiseConds, none(ArithCheck),
                   "ValueError", "invalid integer: parseInt")

proc drainConvFloatToIntRaises(pPre: Path, w: var WalkCtx): seq[Path] =
  ## Phase 16 R16-2. Drain any float→int domain-condition predicates accumulated
  ## by `lower(iekConvFloatToInt)` during the just-completed `lower`/`lowerBool`
  ## call, forking each `not(domainCond)` into a routed `RangeDefect` raise.
  ##
  ## KEY INVARIANT (UNSAT-drop prevention): this drain reads `convFloatToIntDomainConds`
  ## (the PARALLEL sink) and forks from `pPre` — the PRE-narrowing path, BEFORE
  ## `drainPendingLowerEffects`/`drainConvFloatToIntBounds` narrowed the path to
  ## `p & domainCond`. If we forked `not(domainCond)` from the POST-narrowed path,
  ## the pc would be `... & domainCond & not(domainCond)` = UNSAT → silent drop.
  ##
  ## Returns `@[]` always (raise paths are terminal; the surviving in-range
  ## continuation is the post-drain path already handled by the bounds drain).
  ##
  ## `drainPendingLowerEffects` (inside `lowerInExpr`/`lowerBoolInExpr`) consumes
  ## `convFloatToIntBoundConds` but does NOT touch `convFloatToIntDomainConds` —
  ## they are separate sinks. Both are reset before each `lower()` call so they
  ## are always in sync.
  ##
  ## Reads from WalkCtx.convFloatToIntDomainConds (the LIVE store when in a walk);
  ## falls back to the threadvar for probe-path lower() calls (where no drain runs).
  let conds = block:
    if currentWalkCtxPtr != nil:
      let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
      let c = wp[].convFloatToIntDomainConds
      wp[].convFloatToIntDomainConds = @[]
      convFloatToIntDomainConds = @[]   # keep threadvar reset in sync
      c
    else:
      let c = convFloatToIntDomainConds
      convFloatToIntDomainConds = @[]
      c
  if acRange notin w.settings.arithChecks or conds.len == 0:
    # acRange gate: when the check is disabled, suppress the fork (honest-
    # incomplete only — the bounds drain still narrows the normal path).
    return @[]
  # Fork a RangeDefect raise path for each not(domainCond) predicate.
  for c in conds:
    let raisePath = forkPath(pPre, pPre.pc & @[not c], pPre.env)
    discard routeRaise(raisePath, "RangeDefect",
                       some("int(float): value outside target integer range"), w)
  @[]

## Phase 16 R16-3. div/mod-by-zero predicates from `lowerArith` (bDiv/bMod on
## svInt or BV operands). Gated by `acDivByZero`: when disabled, honest-
## incomplete (the division result is still usable, matching pre-R16-3
## behavior).
genRaiseForkDrain(drainDivByZeroRaises, divByZeroConds, some(acDivByZero),
                   "DivByZeroDefect", "division by zero")

## Phase 16 R16-4. Signed integer overflow predicates from `lowerArith`
## (bAdd/bSub/bMul on signed BV operands — svInt and unsigned BV produce no
## entries). Gated by `acOverflow`: when disabled, honest-incomplete
## (arithmetic result still usable, matching pre-R16-4 behavior).
genRaiseForkDrain(drainOverflowRaises, overflowConds, some(acOverflow),
                   "OverflowDefect", "integer overflow")

## RFC-chapulin-hardening SND-4 (ADR-0024). String-index (`s[i]`)
## out-of-bounds predicates from `lowerStrArm`'s `iekStrAt` arm — parity with
## the seq/array/Table indexing arms' unconditional `forkDefect` (Phase 16
## D1a), which already model `IndexDefect` for every OTHER container index;
## `s[i]` was the sole gap. Unconditional (no `arithChecks`-style opt-out
## gate) — mirrors the seq/array `isIndex` arm's `forkDefect` call.
genRaiseForkDrain(drainStrIndexRaises, strIndexOobConds, none(ArithCheck),
                   "IndexDefect", "string index out of bounds")

proc drainScalarRaiseForks(p: Path, w: var WalkCtx): seq[Path] =
  ## R16-4 + SND-4: chain parseInt, div/mod-by-zero, signed-integer-overflow,
  ## and string-index-OOB raise drains. Runs `drainParseIntRaises` first, then
  ## `drainDivByZeroRaises`, then `drainOverflowRaises`, then
  ## `drainStrIndexRaises`. Each stage feeds the survivors of the previous
  ## stage so every combination of independent defect conditions is explored.
  ## The conv-float drain (`drainConvFloatToIntRaises`) is NOT folded in here —
  ## it operates on the pre-narrowing path and stays at its call sites.
  var survivors = drainParseIntRaises(p, w)
  var out2: seq[Path]
  for s in survivors:
    out2.add drainDivByZeroRaises(s, w)
  var out3: seq[Path]
  for s in out2:
    out3.add drainOverflowRaises(s, w)
  var out4: seq[Path]
  for s in out3:
    out4.add drainStrIndexRaises(s, w)
  out4

proc drainClosureExitHeap(p: Path): Path =
  ## Phase 15 CR-1. Apply the exit heap from the most recent `applyClosureGround`
  ## call back to the caller path `p` (the path that is about to become the
  ## post-call survivor). Mirrors the named-proc return-merge (isCall arm
  ## ~5443-5463): the closure's exit `heaps` replace the caller's; `allocCounters`
  ## are max-merged; `liveRefs` are union-merged so subsequent caller `new T`s
  ## are distinct from closure-allocated refs too.
  ##
  ## Returns a NEW path forked from `p` (via `forkPath` deep-copy) with the
  ## merged heap state. If `currentClosureDidMutateHeap` is false (the closure
  ## wrote nothing / is heap-write-free), returns `p` unchanged (no-op, zero cost).
  ##
  ## Called immediately after `lower()` in `isLet`/`isAssign`/`isIf` walk arms
  ## that seed `seedCallerHeapThreadvars` before the `lower()` call.
  ##
  ## CR-9 Stage 6 Group-4: when a walk is active, read from WalkCtx fields
  ## (`closureDidMutateHeap`, `closureExitHeaps`, etc.) rather than the
  ## threadvars. Falls back to threadvars when `currentWalkCtxPtr == nil`.
  ## NOTE: `drainPendingLowerEffects` resets the exit-heap fields after this
  ## call — do NOT reset here (drainPendingLowerEffects is the single reset site).
  let didMutate = if currentWalkCtxPtr != nil:
    cast[ptr WalkCtx](currentWalkCtxPtr)[].closureDidMutateHeap
  else:
    currentClosureDidMutateHeap
  if not didMutate:
    return p                    # most closures are heap-write-free — fast path
  # Fork from `p` but with the closure's exit heap replacing the caller's.
  # `forkPath` deep-copies heap state from `p` first; then we overwrite the
  # fields that the closure exit merged into.
  let merged = forkPath(p, p.pc, p.env)
  let (exitHeaps, exitAlloc, exitLiveRefs) =
    if currentWalkCtxPtr != nil:
      let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
      (wp[].closureExitHeaps, wp[].closureExitAllocCounters, wp[].closureExitLiveRefs)
    else:
      (currentClosureExitHeaps, currentClosureExitAllocCounters, currentClosureExitLiveRefs)
  merged.heaps = exitHeaps
  merged.heapDepth = p.heapDepth     ## preserve caller depth (closure body may
                                      ## have descended further, but that depth is
                                      ## scoped to the descent — mirrors isCall arm)
  # max-merge allocCounters: post-closure caller allocs must not collide with
  # closure-allocated refs, exactly like the named-proc arm (line ~5459-5462).
  for tkey, closureCount in exitAlloc:
    let callerCount = merged.allocCounters.getOrDefault(tkey, 0)
    if closureCount > callerCount:
      merged.allocCounters[tkey] = closureCount
  # union-merge liveRefs: caller's subsequent `new T` must be distinct from
  # closure-allocated refs. The closure's liveRefs are a SUPERSET of the seeded
  # caller liveRefs (seeded from callerLiveRefs + new refs inside the body).
  # Replace with the closure exit's list — it is already the union.
  for tkey, refs in exitLiveRefs:
    merged.liveRefs[tkey] = refs
  merged

proc drainPendingLowerEffects(p: Path): Path =
  ## Phase 15 re-review (S-1/S-2/S-3/S-4/NI-1/NI-2 drain consolidation).
  ## Single choke-point that drains ALL out-of-band `lower()`/`lowerBool()`
  ## effects into path `p` and resets all associated threadvars so no stale
  ## effect leaks to the next `lower()` call:
  ##   (a) Float→int domain bounds from `convFloatToIntBoundConds` are folded
  ##       into `p.pc` (via `drainConvFloatToIntBounds`) and the sink is reset.
  ##   (b) Closure exit-heap state from `currentClosureExitHeaps/AllocCounters/
  ##       LiveRefs` is merged into the path's `heaps/allocCounters/liveRefs`
  ##       (via `drainClosureExitHeap`, conditional on `currentClosureDidMutateHeap`)
  ##       and all four exit-heap threadvars are reset to clean state.
  ##   (d) SND-3 (ADR-0023, walker v58): if `loweringDidDegrade` was set (a
  ##       lowering site returned a fresh unconstrained symbol in-band instead
  ##       of raising), fork the path's `uncertain = true` — SND-1's per-path
  ##       taint — and set `w.sawUnknown` via `currentWalkCtxPtr`, then reset
  ##       the flag. This is the ONLY consumer of `loweringDidDegrade`.
  ##
  ## USAGE CONVENTION (uniform pattern at every `lower()`/`lowerBool()` call site
  ## inside `walk`):
  ##   seedCallerHeapThreadvars(p)     # seed caller heap + reset exit-heap sink
  ##   convFloatToIntBoundConds = @[]  # reset float-bound sink
  ##   let sv = lower(p.env, expr)     # may deposit float bounds + closure writes
  ##   let p = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## `seedCallerHeapThreadvars` still seeds the CALLER heap into threadvars
  ## (so a closure body descends with the right heap); this helper handles the
  ## drain and cleanup AFTER. Together they collapse what were two separate
  ## conventions (seed/drain float-bounds and seed/drain closure-exit-heap) into
  ## one auditable pair.
  let p1 = drainConvFloatToIntBounds(p)   ## (a) float→int bounds; also resets sink
  var p2 = drainClosureExitHeap(p1)       ## (b) closure exit heap (conditional)
  # (c) Phase 16 ADR-0012: closure exit defect-survivor facts. A closure call
  # lowered during this lower() deposited each body exit path's `not overflow`/
  # `not divByZero`/`not parseIntRaise` negations (branch-guarded) here; thread
  # them onto the CALLER path's `defectSurvivorPc` as hard caller-local facts.
  # Fork before mutating so we never alias a sibling path's constraint list.
  if currentClosureExitPc.len > 0:
    p2 = forkPath(p2, p2.pc, p2.env)
    for c in currentClosureExitPc: p2.defectSurvivorPc.add c
    currentClosureExitPc = @[]
  # (d) SND-3 (ADR-0023, walker v58). Fork BEFORE mutating (same rationale as
  # (c) above) so we never alias a sibling path's `uncertain` flag. This is
  # the single choke-point that folds an in-band lowering-degrade into the
  # SND-1 per-path taint — see `loweringDidDegrade`'s doc comment for why the
  # degrade must never route through a bare `w.sawUnknown = true` alone.
  if loweringDidDegrade:
    p2 = forkPathTainted(p2, p2.pc, p2.env)
    if currentWalkCtxPtr != nil:
      cast[ptr WalkCtx](currentWalkCtxPtr)[].sawUnknown = true
    loweringDidDegrade = false
  # Reset exit-heap threadvars so a subsequent lower() that contains no closure
  # call does not see the prior call's heaps, and so drainPendingLowerEffects
  # is idempotent (safe to call again without an intervening seed).
  currentClosureDidMutateHeap = false
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()
  currentClosureExitAllocCounters = initTable[string, int]()
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  # CR-9 Stage 6 Groups 3+4: also reset WalkCtx fields (idempotent).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp[].closureDidMutateHeap = false
    wp[].closureExitHeaps = initTable[string, Z3AnyAst]()
    wp[].closureExitAllocCounters = initTable[string, int]()
    wp[].closureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()
  p2

proc lowerInExpr(p: Path, e: IRExpr, w: var WalkCtx,
                 proto = none(SymVal)): (SymVal, Path) =
  ## Phase 15 CR-9 Stage 1. Encapsulates the seed → reset-transient-sinks →
  ## lower → drain pattern so a walk arm cannot forget to drain. Returns the
  ## lowered value and the drained path.
  ##
  ## Reproduces the exact sequence performed by the isLet / isAssign arms:
  ##   parseIntRaiseConds = @[]          # reset parseInt-raise sink
  ##   convFloatToIntBoundConds = @[]    # reset float-bound sink
  ##   seedCallerHeapThreadvars(p)       # seed caller heap + reset exit-heap sink
  ##   let sv = lower(p.env, e, proto)   # may deposit float bounds + closure writes
  ##   let p2 = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## NOTE: drainParseIntRaises is a FORK (returns seq[Path]) and is intentionally
  ## NOT called here — arms that need the parseInt raise-fork call it on the
  ## returned path p2 after this wrapper returns.
  ##
  ## CR-9 Stage 6: resets WalkCtx fields (via w param) in addition to the
  ## threadvar resets so the WalkCtx LIVE store starts clean for each lower() call.
  ## `seedCallerHeapThreadvars` (called below) also calls `seedCallerHeapInWalkCtx`
  ## to reset the exit-heap WalkCtx fields; the remaining sink resets happen here.
  parseIntRaiseConds = @[]
  w.parseIntRaiseConds = @[]            # CR-9 Stage 6 Group-2: reset WalkCtx field
  convFloatToIntBoundConds = @[]
  w.convFloatToIntBoundConds = @[]      # CR-9 Stage 6 Group-1: reset WalkCtx field
  convFloatToIntDomainConds = @[]
  w.convFloatToIntDomainConds = @[]     # R16-2: reset parallel raise-fork sink
  divByZeroConds = @[]
  w.divByZeroConds = @[]                # R16-3: reset div/mod-by-zero raise sink
  overflowConds = @[]
  w.overflowConds = @[]                 # R16-4: reset signed-integer overflow raise sink
  strIndexOobConds = @[]
  w.strIndexOobConds = @[]              # SND-4: reset string-index OOB raise sink
  seedCallerHeapThreadvars(p)           # also calls seedCallerHeapInWalkCtx(p)
  let sv = lower(p.env, e, proto)
  let p2 = drainPendingLowerEffects(p)
  (sv, p2)

proc lowerBoolInExpr(p: Path, e: IRExpr, w: var WalkCtx): (Z3Bool, Path) =
  ## Phase 15 CR-9 Stage 1. Same as lowerInExpr but for boolean predicate
  ## positions (calls lowerBool instead of lower). Reproduces the exact
  ## sequence performed by the isAssert arm:
  ##   parseIntRaiseConds = @[]          # reset parseInt-raise sink
  ##   convFloatToIntBoundConds = @[]    # reset float-bound sink
  ##   seedCallerHeapThreadvars(p)       # seed caller heap + reset exit-heap sink
  ##   let b = lowerBool(p.env, e)       # may deposit float bounds + closure writes
  ##   let p2 = drainPendingLowerEffects(p)  # drain + reset both sinks
  ##
  ## CR-9 Stage 6: resets WalkCtx fields (via w param) in addition to the
  ## threadvar resets so the WalkCtx LIVE store starts clean for each lowerBool() call.
  parseIntRaiseConds = @[]
  w.parseIntRaiseConds = @[]            # CR-9 Stage 6 Group-2: reset WalkCtx field
  convFloatToIntBoundConds = @[]
  w.convFloatToIntBoundConds = @[]      # CR-9 Stage 6 Group-1: reset WalkCtx field
  convFloatToIntDomainConds = @[]
  w.convFloatToIntDomainConds = @[]     # R16-2: reset parallel raise-fork sink
  divByZeroConds = @[]
  w.divByZeroConds = @[]                # R16-3: reset div/mod-by-zero raise sink
  overflowConds = @[]
  w.overflowConds = @[]                 # R16-4: reset signed-integer overflow raise sink
  strIndexOobConds = @[]
  w.strIndexOobConds = @[]              # SND-4: reset string-index OOB raise sink
  seedCallerHeapThreadvars(p)           # also calls seedCallerHeapInWalkCtx(p)
  let b = lowerBool(p.env, e)
  let p2 = drainPendingLowerEffects(p)
  (b, p2)

proc lowerLeafInExpr(p: Path, e: IRExpr): SymVal =
  ## Phase 15 CR-9 Stage 3. A container/pointer operand of a deref/index/field
  ## arm that is side-effect-free — no closure call, no float→int conversion —
  ## so no seed/drain is needed. The assert makes any violation loud.
  ##
  ## Admitted kinds and their side-effect status:
  ##   iekVar      — env lookup, trivially pure.
  ##   iekField    — struct field projection, pure.
  ##   iekStrBytes — `bytes(s)` on a string literal: raises early for symbolic
  ##                 or oversized inputs; for a concrete literal it builds a Z3
  ##                 const-array of BV8 with no closures or float→int sinks.
  ##                 Added CR-20 (S7-bytes-index-assert): the parser does NOT
  ##                 A-normalise `bytes(lit)[i]` — `ixArr` carries the
  ##                 iekStrBytes expr directly. It is pure, so no drain needed.
  doAssert e.kind in {iekVar, iekField, iekStrBytes},
    "lowerLeafInExpr: expected side-effect-free container expr; got " & $e.kind &
    " — add seed+drain if parser changes"
  lower(p.env, e)

# nilDerefFork moved to runtime_heap.nim (CR-7-deeper Stage 8+).

proc walkBlock(stmts: seq[IRStmt], paths: seq[Path], w: var WalkCtx): seq[Path] =
  result = paths
  for s in stmts:
    if w.shouldStop: return
    result = walk(s, result, w)
    if result.len == 0: return
    # Phase 14 cycle C3 (ADR-0004). Post-step frontier prune. A
    # `maxFrontierSize` of 0 keeps the unbounded baseline; any
    # positive value triggers highest-uncertainty-first eviction:
    # certain paths sort before uncertain (stable within each
    # tier), and the tail is dropped. Pruned paths' contribution
    # is reported as unknown via `w.sawUnknown = true`, which
    # cascades into the final `sxUnknown` verdict cached under
    # `:unk` (NOT `:unsat`).
    if w.settings.budget.maxFrontierSize > 0 and
       result.len > w.settings.budget.maxFrontierSize:
      var certain, uncertain: seq[Path]
      for p in result:
        if p.uncertain: uncertain.add p
        else:           certain.add p
      var kept: seq[Path]
      for p in certain:
        if kept.len >= w.settings.budget.maxFrontierSize: break
        kept.add p
      for p in uncertain:
        if kept.len >= w.settings.budget.maxFrontierSize: break
        kept.add p
      w.sawUnknown = true
      # v64 (chapulin catalog #5(b), Invariant 7): classify the prune — a
      # bare `sawUnknown` here yielded sxUnknown with EMPTY errors.
      w.walkDegradeErrors.add SymexErrorInfo(
        kind: beBudgetExhausted, severity: sevError,
        msg: "path-frontier cap (maxFrontierSize=" &
             $w.settings.budget.maxFrontierSize & ") pruned " &
             $(result.len - kept.len) &
             " live path(s) — their verdicts are unexplored (beBudgetExhausted)")
      result = kept

include "runtime_heap.nim"  # Stage 8 CR-7 Cluster R: walkHeapArm

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path] =
  if w.shouldStop or stmt == nil or paths.len == 0:
    return paths
  case stmt.kind
  of isBlock:
    walkBlock(stmt.stmts, paths, w)
  of isIf:
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      # Phase 15 S10b: evaluating a branch condition may itself raise (a
      # `parseInt` on a non-digit string). The raise fork happens during cond
      # evaluation — its sub-path is routed as `ValueError` and the digits
      # continuation (`cp`) carries the non-raise constraint forward to ALL
      # subsequent arms and the else. `cp` threads that digits-constrained base
      # path across the branch loop.
      var cp = p
      var accumNegated: seq[Z3Bool]
      for br in stmt.branches:
        ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
        ## NI-1 semantics preserved: lowerBoolInExpr seeds from the CURRENT cp
        ## (the path passed to the wrapper), NOT the original p.
        let cpPre = cp  ## R16-2: capture PRE-narrowing path before wrapper narrows it
        let (condBool, cp2) = lowerBoolInExpr(cp, br.cond, w)
        cp = cp2
        # DES-4 invariant: `condBool` was computed from the pre-drain `cp.env`
        # (env passed into lowerBoolInExpr) and is a Z3 AST.
        # `lowerBoolInExpr` returns the drained path as cp2; we set cp = cp2.
        # The drain mutates cp.pc (extends with float→int domain bounds and/or
        # closure heap state) but does NOT touch cp.env. Since `condBool` is a
        # Z3 term constructed from the pre-drain env variables, it remains a
        # valid Z3 AST after the drain and can safely be added to the arm/else
        # path conditions below (`cp.pc & accumNegated & @[condBool]`).
        let cont = drainScalarRaiseForks(cp, w)  ## R16-3: parseInt + div/mod-by-zero raise forks
        discard drainConvFloatToIntRaises(cpPre, w)  ## R16-2: RangeDefect fork from pre-narrowing cp
        if cont.len == 0:
          # The whole cond raised on every path (digits continuation infeasible).
          cp = forkPath(cp, cp.pc, cp.env)
        else:
          cp = cont[0]   ## digits-constrained continuation (non-raise pc)
        let armPath = forkPath(cp, cp.pc & accumNegated & @[condBool],
                               cp.env)
        survivors.add walk(br.body, @[armPath], w)
        accumNegated.add(not condBool)
        if w.shouldStop: return
      let elsePath = forkPath(cp, cp.pc & accumNegated, cp.env)
      if stmt.elseBody != nil:
        survivors.add walk(stmt.elseBody, @[elsePath], w)
      else:
        survivors.add elsePath
    survivors
  of isLet:
    var out2: seq[Path]
    for p in paths:
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      ## drainParseIntRaises is a FORK — NOT inside the wrapper; called on pb.
      ## v69 (sello #1): shape a bare-literal RHS at the DECLARED width.
      let (lv, pb) = lowerInExpr(p, stmt.lvalue, w, intLitProto(stmt.lty))
      discard drainConvFloatToIntRaises(p, w)   ## R16-2: RangeDefect fork from pre-narrowing p
      for cp in drainScalarRaiseForks(pb, w):   ## R16-3: parseInt + div/mod-by-zero raise forks
        var newEnv = cp.env
        newEnv[stmt.lname] = lv
        out2.add forkPath(cp, cp.pc, newEnv)
    out2
  of isAssign:
    var out2: seq[Path]
    for p in paths:
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      ## drainParseIntRaises is a FORK — NOT inside the wrapper; called on pb.
      ## v69 (sello #1): shape a bare-literal RHS at the target's CURRENT
      ## representation (assign IR carries no declared type).
      let (av, pb) = lowerInExpr(p, stmt.avalue, w,
                                 envLitProto(p.env, stmt.aname))
      discard drainConvFloatToIntRaises(p, w)   ## R16-2: RangeDefect fork from pre-narrowing p
      for cp in drainScalarRaiseForks(pb, w):   ## R16-3: parseInt + div/mod-by-zero raise forks
        var newEnv = cp.env
        newEnv[stmt.aname] = av
        out2.add forkPath(cp, cp.pc, newEnv)
    out2
  of isWhile:
    # Phase 6: k-unroll. Each iteration forks on the guard.
    var survivors: seq[Path] = @[]
    var active = paths
    w.loopStack.add LoopFrame(breakPaths: @[], continuePaths: @[])
    let frameIx = w.loopStack.high
    let unwind = w.settings.budget.maxLoopUnwind
    for iter in 0 ..< unwind:
      if w.shouldStop: break
      if active.len == 0: break
      var nextActive: seq[Path]
      for p in active:
        ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
        let (cond, pb) = lowerBoolInExpr(p, stmt.wcond, w)
        ## R1 (Invariant-3 soundness fix): the guard `stmt.wcond` may itself
        ## deposit scalar-raise-fork predicates (e.g. `s[i]` OOB, `x div 0`)
        ## into the sinks `lowerBoolInExpr` reset at entry. Undrained, those
        ## predicates were silently discarded — no raise fork, no bounds
        ## narrowing — so a target reachable only PAST a real raise on the
        ## guard was falsely `sxSat`. Drain here, exactly as `isIf` does for
        ## its branch conditions, and thread the survivor(s) forward into
        ## both the true (body) and false (exit) continuations. `cond` was
        ## built from `pb`'s (pre-drain) env, which the drain does not
        ## mutate, so it stays a valid Z3 AST against each drained survivor.
        for dp in drainScalarRaiseForks(pb, w):
          # cond=true: walk body
          let truePath = forkPath(dp, dp.pc & @[cond], dp.env)
          let afterBody = walk(stmt.wbody, @[truePath], w)
          # Continue-paths from the body merge into next-iter active.
          let cps = w.loopStack[frameIx].continuePaths
          w.loopStack[frameIx].continuePaths = @[]
          for cp in cps: nextActive.add cp
          for ap in afterBody: nextActive.add ap
          # cond=false: exit loop (use dp — the drained path with domain
          # bounds folded in).
          survivors.add forkPath(dp, dp.pc & @[not cond], dp.env)
      active = nextActive
    # Break-paths exit the loop directly (with their accumulated pc/env).
    for bp in w.loopStack[frameIx].breakPaths:
      survivors.add bp
    # Any paths still active after maxLoopUnwind iterations are
    # exhausted: cond=true was still SAT-able. Mark uncertain.
    if active.len > 0:
      w.sawUnknown = true
      # v64 (chapulin catalog #5(b), Invariant 7): record the classified
      # reason — a bare `sawUnknown` here yielded sxUnknown with EMPTY errors.
      w.walkDegradeErrors.add SymexErrorInfo(
        kind: beBudgetExhausted, severity: sevError,
        msg: "while-loop k-unroll budget exhausted (maxLoopUnwind=" &
             $unwind & ") with the guard still satisfiable — trip counts " &
             "beyond the bound are unexplored (beBudgetExhausted)")
      for p in active:
        survivors.add forkPathTainted(p, p.pc, p.env)
    discard w.loopStack.pop()
    survivors
  of isBreak:
    if w.loopStack.len == 0:
      w.sawUnknown = true   # break outside any loop — degenerate
      return @[]
    for p in paths:
      w.loopStack[w.loopStack.high].breakPaths.add p
    @[]
  of isContinue:
    if w.loopStack.len == 0:
      w.sawUnknown = true
      return @[]
    for p in paths:
      w.loopStack[w.loopStack.high].continuePaths.add p
    @[]
  of isIndex:
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      ## Drain-coverage audit: `stmt.ixArr` is a side-effect-free container
      ## expression. The parser A-normalises most container expressions to named
      ## bindings (iekVar), but `bytes(lit)[i]` is the known exception — the
      ## parser passes the iekStrBytes expr directly as ixArr (CR-20). Both
      ## iekVar and iekStrBytes are pure (no closure/float→int sinks), so
      ## lowerLeafInExpr handles them without seed+drain.
      let arrSV = lowerLeafInExpr(p, stmt.ixArr)
      # ---- Phase 5: Table[K, V] indexing ----
      if arrSV.kind == svTable:
        ## Table key: always a string expression — no float→int conv or closure
        ## can appear in a string sub-expression, so no seed+drain needed here.
        ## If the parser ever emits non-string keyed tables, add the uniform
        ## seed/drain wrapper before the lower call.
        let keyProto = SymVal(kind: svString, str: mkString(""))
        let keySV = lower(p.env, stmt.ixIdx, some(keyProto))
        doAssert keySV.kind == svString
        # Nim's `Table[K, V].[]` raises `KeyError` when the key is
        # absent. To preserve that semantics in symex we add a
        # presence constraint to the surviving path.
        let typedPresent = wrap[Z3Array[Z3String, Z3Bool]](
          arrSV.tabPresentRaw.ctx, arrSV.tabPresentRaw.raw)
        let presentCond = select(typedPresent, keySV.str)
        case arrSV.tabValTy.kind
        of itInt:
          doAssert arrSV.tabValTy.width == 64
          let typedData = wrap[Z3Array[Z3String, Z3BitVec[64]]](
            arrSV.tabDataRaw.ctx, arrSV.tabDataRaw.raw)
          let v = select(typedData, keySV.str)
          var newEnv = p.env
          newEnv[stmt.ixRetName] = liftBV(v, arrSV.tabValTy.signed)
          survivors.add forkPath(p, p.pc & @[presentCond], newEnv)
        else:
          raise (ref SymexUnsupportedTableValTypeError)(
            msg: "Table value type not modeled at index: " & $arrSV.tabValTy &
                 " — only Table[string, int] is supported (seUnsupportedTableValType)")
        continue
      # ---- Phase 5: dynamic seq[T] indexing ----
      if arrSV.kind == svSeq:
        # Seq index is Z3Int. Lower with an svInt proto for literals;
        # for env-resident BV-typed Nim ints we coerce via bv2int.
        ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
        # CR-9(c) D5 note: reconcileInt is NOT applied here — the intProto
        # already steers index literals to svInt, and toZ3Int(idxSV) handles
        # the BV-typed env var → Z3Int coercion (bv2int). No cross-rep issue.
        let intProto = SymVal(kind: svInt, zi: mkInt(0))
        let (idxSV, idxP) = lowerInExpr(p, stmt.ixIdx, w, some(intProto))
        ## R1 (Invariant-3 soundness fix): `stmt.ixIdx` may itself deposit
        ## scalar-raise-fork predicates (e.g. a `div`/`parseInt` sub-expr).
        ## Undrained, those were silently discarded — no raise fork, no
        ## bounds narrowing. Drain and thread the survivor(s) forward
        ## through the seq-bounds check below, mirroring `isLet`/`isAssign`.
        for cp in drainScalarRaiseForks(idxP, w):
          let lenZi = arrSV.seqLen
          let idxZi = toZ3Int(idxSV)
          let inLoCond = idxZi >= mkInt(0)
          let inHiCond = idxZi <  lenZi
          discard forkDefect(cp, not (inLoCond and inHiCond),   ## Phase 16 D1a
                             "IndexDefect", none(string), w)
          # Bind retName = select(seqData, idx) at element type
          var indexed: SymVal
          case arrSV.seqElemTy.kind
          of itInt:
            case arrSV.seqElemTy.width
            of 8:
              let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
                arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
              indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
            of 16:
              let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
                arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
              indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
            of 32:
              let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
                arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
              indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
            of 64:
              let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
                arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
              indexed = liftBV(select(typed, idxZi), arrSV.seqElemTy.signed)
            else:
              raise newException(ValueError,
                "isIndex/seq: unsupported elem width " & $arrSV.seqElemTy.width)
          of itBool:
            let typed = wrap[Z3Array[Z3Int, Z3Bool]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = ofBool(select(typed, idxZi))
          of itFloat32:   ## Phase 15 F9b
            let typed = wrap[Z3Array[Z3Int, Z3Float32]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = SymVal(kind: svFloat32, fp32: select(typed, idxZi))
          of itFloat64:   ## Phase 15 F9b
            let typed = wrap[Z3Array[Z3Int, Z3Float64]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = SymVal(kind: svFloat64, fp64: select(typed, idxZi))
          of itString:   ## Phase 15 S5: seq[string] element (e.g. split result)
            let typed = wrap[Z3Array[Z3Int, Z3String]](
              arrSV.seqDataRaw.ctx, arrSV.seqDataRaw.raw)
            indexed = SymVal(kind: svString, str: select(typed, idxZi))
          of itRef, itPtr:   ## Phase 15 R3 (ADR-0010): seq[ref T] / seq[ptr T] elem.
            # The element is an abstract `Ref_T` address (the backing array is a
            # raw `Z3Array[Z3Int, Ref_T]`). The select goes through raw FFI
            # (`Z3_mk_select` over `seqDataRaw` at the index) because `Ref_T` is a
            # RUNTIME uninterpreted sort the typed `select` can't express. The
            # result is an svRef/svPtr — a later `[]` (isDeref) derefs it through
            # `path.heaps[T]`. GROUND select; NO quantifier (the G4 hang lesson).
            let ctx = w.z3
            let isPtr = arrSV.seqElemTy.kind == itPtr
            let pointee = if isPtr: arrSV.seqElemTy.ptrPointeeTy
                          else: arrSV.seqElemTy.refPointeeTy
            let elemRaw = ctx.checkErr Z3_mk_select(ctx.raw,
              arrSV.seqDataRaw.raw, idxZi.raw)
            let elemAny = wrap[Z3AnyAst](ctx, elemRaw)
            if isPtr:
              indexed = SymVal(kind: svPtr, ptrAst: elemAny,
                               ptrFamily: true, ptrPointee: pointee)
            else:
              indexed = SymVal(kind: svRef, refAst: elemAny, refPointee: pointee)
          else:
            raise newException(ValueError,
              "isIndex/seq: unsupported elem kind " & $arrSV.seqElemTy.kind)
          var newEnv = cp.env
          newEnv[stmt.ixRetName] = indexed
          survivors.add forkPath(cp, cp.pc & @[inLoCond, inHiCond], newEnv)
        continue
      # ---- Round-6 B1 (ADR-0028 Leg 1): string-backed seq[byte] index READ.
      # A `data[i]` reaching here with an `svString` receiver means the
      # receiver was allocated string-backed (B1a) but the CONSUMING op's
      # IR is the ordinary `isIndex` node — e.g. a call-chain hop whose OWN
      # parse never routed the dispatch through `iekStrAt` (no qualifying
      # scan loop over ITS OWN same-named parameter), yet the VALUE flowing
      # in at THIS point is the caller's string-backed allocation. Route
      # through the SAME OOB-probe + read logic `iekStrAt`'s lowering uses
      # (SND-4 mirror, `runtime_strings.nim`) so the read stays TOTAL and
      # actually decides — not merely declines.
      if arrSV.kind == svString:
        let intProto = SymVal(kind: svInt, zi: mkInt(0))
        let (idxSV, idxP) = lowerInExpr(p, stmt.ixIdx, w, some(intProto))
        for cp in drainScalarRaiseForks(idxP, w):
          let idxZi = toZ3Int(idxSV)
          let strLenZi = len(arrSV.str)
          let inLoCond = idxZi >= mkInt(0)
          let inHiCond = idxZi <  strLenZi
          discard forkDefect(cp, not (inLoCond and inHiCond),
                             "IndexDefect", none(string), w)
          let code = toCode(at(arrSV.str, idxZi))
          var newEnv = cp.env
          newEnv[stmt.ixRetName] = liftBV(intToBv[8](code, Z3BitVec[8]), false)
          survivors.add forkPath(cp, cp.pc & @[inLoCond, inHiCond], newEnv)
        continue
      # ---- Phase 4: static array (the existing path) ----
      if arrSV.kind != svArray:
        # Round-6 B1 backstop: was a hard `doAssert` (a live crash gap) —
        # a mis-classified receiver now declines classified instead of
        # crashing (SND-4 mirror: the existing generic
        # `SymexClassifiedDegradeError` carrier, CR-1c/CR-2b precedent).
        let locPrefix = if stmt.ixLoc.len > 0: stmt.ixLoc & ": " else: ""
        raise (ref SymexClassifiedDegradeError)(
          kind: feUnsupportedExprKind,
          msg: locPrefix & "isIndex: unsupported receiver kind " &
               $arrSV.kind & " (expected array/seq/table/string) — " &
               "degraded to sxUnknown (feUnsupportedExprKind)")
      let n = arrSV.arrElems.len
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      let (idxSV, idxP) = lowerInExpr(p, stmt.ixIdx, w)
      ## R1 (Invariant-3 soundness fix): `stmt.ixIdx` may itself deposit
      ## scalar-raise-fork predicates. Undrained, those were silently
      ## discarded — no raise fork, no bounds narrowing. Drain and thread
      ## the survivor(s) forward, mirroring `isLet`/`isAssign`.
      for cp in drainScalarRaiseForks(idxP, w):
        # Build the in-bounds & OOB Z3 conditions.
        let loSV  = coerceIntLit(idxSV, 0)
        let hiSV  = coerceIntLit(idxSV, int64(n))
        let inLoCond = case idxSV.kind
          of svBV8:  bvsle(loSV.bv8,  idxSV.bv8)
          of svBV16: bvsle(loSV.bv16, idxSV.bv16)
          of svBV32: bvsle(loSV.bv32, idxSV.bv32)
          of svBV64: bvsle(loSV.bv64, idxSV.bv64)
          of svInt:  loSV.zi <= idxSV.zi
          else: raise newException(ValueError, "isIndex: non-int index kind")
        let inHiCond = case idxSV.kind
          of svBV8:  bvslt(idxSV.bv8,  hiSV.bv8)
          of svBV16: bvslt(idxSV.bv16, hiSV.bv16)
          of svBV32: bvslt(idxSV.bv32, hiSV.bv32)
          of svBV64: bvslt(idxSV.bv64, hiSV.bv64)
          of svInt:  idxSV.zi < hiSV.zi
          else: raise newException(ValueError, "isIndex: non-int index kind")
        # OOB defect fork — Phase 16 D1a unconditional.
        discard forkDefect(cp, not (inLoCond and inHiCond),
                           "IndexDefect", none(string), w)
        # In-bounds path continues with binding; build the value via ite.
        var indexed = arrSV.arrElems[0]
        for k in 1 ..< n:
          let kSV = coerceIntLit(idxSV, int64(k))
          indexed = iteSV(symEq(idxSV, kSV), arrSV.arrElems[k], indexed)
        var newEnv = cp.env
        newEnv[stmt.ixRetName] = indexed
        survivors.add forkPath(cp, cp.pc & @[inLoCond, inHiCond], newEnv)
    survivors
  of isVariantReassign:
    # Phase 11 cycle 6 — `obj.kind = tagLiteral`. Build a new
    # svVariant whose discriminator IS the literal tag (constant
    # BV) and whose new arm's primitive fields are zero-init'd
    # (Nim runtime semantics on discriminator reassignment).
    proc defaultZero(t: IRType, baseName: string): SymVal =
      ## Phase 14 cycle A5 (ADR-0003 D5). Recursive type-driven
      ## zero-init for arm fields under static-tag disc reassign.
      ## Replaces Phase 11's "primitives only" guard with a full
      ## walk over the IR type tree. Inherits `allocateSym`'s scope
      ## for containers — Table with non-string keys and HashSet
      ## with non-int64 elements still raise (RFC §A5 sub-deferral).
      case t.kind
      of itUninterp:
        raise newException(ValueError, "defaultZero(itUninterp): lands with cluster E")
      of itFloat32, itFloat64:
        raise newException(ValueError, "defaultZero(float): lands with F7")
      of itBool: SymVal(kind: svBool, bo: mkBool(false))
      of itInt:
        case t.width
        of 8:  liftBV(mkBitVec[8](0),  t.signed)
        of 16: liftBV(mkBitVec[16](0), t.signed)
        of 32: liftBV(mkBitVec[32](0), t.signed)
        of 64: liftBV(mkBitVec[64](0), t.signed)
        else:
          raise newException(ValueError,
            "A5 zero-init: int width " & $t.width & " not supported")
      of itString:
        SymVal(kind: svString, str: mkString(""))
      of itTuple:
        var fields: seq[SymVal]
        for i, ft in t.fields:
          let suffix = if t.fieldNames[i].len > 0: "." & t.fieldNames[i]
                       else: "." & $i
          fields.add defaultZero(ft, baseName & suffix)
        SymVal(kind: svTuple, fields: fields, fieldNames: t.fieldNames)
      of itArray:
        var elems: seq[SymVal]
        for i in 0 ..< t.size:
          elems.add defaultZero(t.elemTy, baseName & "." & $i)
        SymVal(kind: svArray, arrElems: elems, arrElemTy: t.elemTy)
      of itSeq:
        # Empty seq: len pinned to 0; the data array is allocated
        # so the SymVal shape is well-formed, but never read past
        # len. Mirrors Nim's `default(seq[T]) == @[]`.
        let dataRaw = allocateSeqDataRaw(t.seqElemTy, baseName & ".data")
        SymVal(kind: svSeq, seqLen: mkInt(0),
               seqDataRaw: dataRaw, seqElemTy: t.seqElemTy)
      of itSet, itTable:
        # RFC §A5 sub-deferral: container fields in reassigned arms
        # inherit `allocateSym`'s scope guard. Empty-container
        # construction requires a fresh Z3Array allocation which
        # the current SymVal shape doesn't expose a constructor
        # for outside `allocateSym`; defer until a concrete
        # consumer demands it.
        raise newException(ValueError,
          "A5 zero-init: container arm field " & $t &
          " in reassigned arm not yet supported " &
          "(RFC §A5 sub-deferral)")
      of itVariant, itMultiVariant:
        # Nested variant in an arm field: zero-initing it requires
        # picking a default disc + recursing. The walker doesn't
        # have access to the constructor here; this remains
        # unsupported until a concrete demand surfaces.
        raise newException(ValueError,
          "A5 zero-init: nested variant " & $t &
          " in reassigned arm not supported")
      of itDistinct:
        # Phase 15 G4: a distinct-typed arm field zero-init needs the per-run
        # distinct-sort cache + pcOut threading, which this constructor-less
        # context doesn't expose. Out of G4 scope; raised loudly (Invariant 3).
        raise newException(ValueError,
          "A5 zero-init: distinct " & $t &
          " in reassigned arm not supported (Phase 15 G4 sub-deferral)")
      of itRef, itPtr:
        # Phase 15 R1a STUB: zero-initing a ref/ptr arm field is `nil`, but the
        # logical-heap nil-const lands R5. Out of R1a scope; classified halt.
        raise (ref SymexRefUnresolvedError)(
          msg: "ref/ptr arm-field zero-init " & $t &
               " not yet modeled (Cluster R R1a structural stub; nil lands R5)")
    var out2: seq[Path]
    for p in paths:
      if not p.env.hasKey(stmt.vrObjName):
        out2.add p
        continue
      let oldSV = p.env[stmt.vrObjName]
      doAssert oldSV.kind == svVariant,
        "isVariantReassign on non-variant kind=" & $oldSV.kind
      let oldDisc = oldSV.vDisc[]
      let tagOrd = int64(stmt.vrNewTag)
      let newDiscInner: SymVal =
        case oldDisc.kind
        of svBV8:  liftBV(mkBitVec[8](tagOrd),  oldDisc.signed)
        of svBV16: liftBV(mkBitVec[16](tagOrd), oldDisc.signed)
        of svBV32: liftBV(mkBitVec[32](tagOrd), oldDisc.signed)
        of svBV64: liftBV(mkBitVec[64](tagOrd), oldDisc.signed)
        of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(tagOrd))  # A6
        else:
          raise newException(ValueError,
            "isVariantReassign: disc must be BV or Z3Int kind")
      let newDiscBoxed = new(SymVal)
      newDiscBoxed[] = newDiscInner
      var newArmFields = oldSV.vArmFields
      let priorFields = oldSV.vArmFields.getOrDefault(stmt.vrNewTag)
      var newFields: seq[SymVal]
      let armNames = oldSV.vArmFieldNames.getOrDefault(stmt.vrNewTag)
      for ix, f in priorFields:
        let fname = if ix < armNames.len: armNames[ix] else: $ix
        let basePath = stmt.vrObjName & ".@" &
                       $stmt.vrNewTag & "." & fname & ".reass"
        newFields.add defaultZero(tyOf(f), basePath)
      newArmFields[stmt.vrNewTag] = newFields
      let newSV = SymVal(kind: svVariant,
                         vDisc: newDiscBoxed,
                         vDiscName: oldSV.vDiscName,
                         vObjectName: oldSV.vObjectName,
                         vArmFields: newArmFields,
                         vArmFieldNames: oldSV.vArmFieldNames,
                         vPlainFields: oldSV.vPlainFields,       # shared:
                         vPlainFieldNames: oldSV.vPlainFieldNames) # preserved.
      var newEnv = p.env
      newEnv[stmt.vrObjName] = newSV
      out2.add forkPath(p, p.pc, newEnv)
    return out2
  of isVariantReassignSymbolic:
    # Phase 14 cycle A4b (ADR-0003 D4). Symbolic-RHS disc reassign:
    # fork one path per arm-ordinal in the disc's domain. Each path
    # is constrained `rhsSV == k_ord` AND the variant SymVal in env
    # is rebuilt with the new disc SET TO THAT TAG'S CONSTANT.
    # Arm-field SymVals are PRESERVED — no zero-init (that's the
    # static-tag path's job per D4). For itMultiVariant: only the
    # named axis's disc is updated; other axes are preserved as-is.
    var out2: seq[Path]
    for p in paths:
      if not p.env.hasKey(stmt.vrsObjName):
        out2.add p
        continue
      let oldSV = p.env[stmt.vrsObjName]
      ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
      let (rhsSV, pr) = lowerInExpr(p, stmt.vrsRhs, w)
      proc rhsEq(tagOrd: int64): Z3Bool =
        case rhsSV.kind
        of svBV8:  rhsSV.bv8  == mkBitVec[8](tagOrd)
        of svBV16: rhsSV.bv16 == mkBitVec[16](tagOrd)
        of svBV32: rhsSV.bv32 == mkBitVec[32](tagOrd)
        of svBV64: rhsSV.bv64 == mkBitVec[64](tagOrd)
        of svInt:  rhsSV.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
        else:
          raise newException(ValueError,
            "isVariantReassignSymbolic: RHS must lower to a BV or " &
            "Z3Int kind (got " & $rhsSV.kind & ")")
      ## R1 (Invariant-3 soundness fix): `stmt.vrsRhs` may itself deposit
      ## scalar-raise-fork predicates. Undrained, those were silently
      ## discarded — no raise fork, no bounds narrowing. Drain and thread
      ## the survivor(s) forward, mirroring `isLet`/`isAssign`.
      for cp in drainScalarRaiseForks(pr, w):
        case oldSV.kind
        of svVariant:
          for tag in oldSV.vArmFields.keys:
            if tag < 0: continue  # else arm — covered by D4 future work
            let newDiscInner: SymVal =
              case oldSV.vDisc[].kind
              of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldSV.vDisc[].signed)
              of svBV16: liftBV(mkBitVec[16](int64(tag)), oldSV.vDisc[].signed)
              of svBV32: liftBV(mkBitVec[32](int64(tag)), oldSV.vDisc[].signed)
              of svBV64: liftBV(mkBitVec[64](int64(tag)), oldSV.vDisc[].signed)
              of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
              else:
                raise newException(ValueError,
                  "isVariantReassignSymbolic: old disc must be BV or Z3Int")
            let newDiscBoxed = new(SymVal)
            newDiscBoxed[] = newDiscInner
            let newSV = SymVal(kind: svVariant,
                               vDisc: newDiscBoxed,
                               vDiscName: oldSV.vDiscName,
                               vObjectName: oldSV.vObjectName,
                               vArmFields: oldSV.vArmFields,       # PRESERVED
                               vArmFieldNames: oldSV.vArmFieldNames,
                               vPlainFields: oldSV.vPlainFields,
                               vPlainFieldNames: oldSV.vPlainFieldNames)
            var newEnv = cp.env
            newEnv[stmt.vrsObjName] = newSV
            out2.add forkPath(cp, cp.pc & @[rhsEq(int64(tag))], newEnv)
        of svMultiVariant:
          # Locate the named axis (vrsDiscName); other axes preserve
          # their disc + arm state.
          var axisIx = -1
          for i, ax in oldSV.mvAxes:
            if ax.discName == stmt.vrsDiscName:
              axisIx = i; break
          doAssert axisIx >= 0,
            "isVariantReassignSymbolic on svMultiVariant: no axis named " &
            stmt.vrsDiscName
          let oldAxis = oldSV.mvAxes[axisIx]
          for tag in oldAxis.armFields.keys:
            if tag < 0: continue
            let newDiscInner: SymVal =
              case oldAxis.disc[].kind
              of svBV8:  liftBV(mkBitVec[8](int64(tag)),  oldAxis.disc[].signed)
              of svBV16: liftBV(mkBitVec[16](int64(tag)), oldAxis.disc[].signed)
              of svBV32: liftBV(mkBitVec[32](int64(tag)), oldAxis.disc[].signed)
              of svBV64: liftBV(mkBitVec[64](int64(tag)), oldAxis.disc[].signed)
              of svInt:  SymVal(kind: svInt, zi: mkZ3IntLit(int64(tag)))  # A6
              else:
                raise newException(ValueError,
                  "isVariantReassignSymbolic: axis disc must be a BV kind")
            let newDiscBoxed = new(SymVal)
            newDiscBoxed[] = newDiscInner
            var newAxes = oldSV.mvAxes
            newAxes[axisIx] = VariantAxisSym(
              discName: oldAxis.discName, disc: newDiscBoxed,
              armFields: oldAxis.armFields,       # PRESERVED
              armFieldNames: oldAxis.armFieldNames)
            let newSV = SymVal(kind: svMultiVariant,
                               mvObjectName: oldSV.mvObjectName,
                               mvAxes: newAxes,
                               mvPlainFields: oldSV.mvPlainFields,
                               mvPlainFieldNames: oldSV.mvPlainFieldNames)
            var newEnv = cp.env
            newEnv[stmt.vrsObjName] = newSV
            out2.add forkPath(cp, cp.pc & @[rhsEq(int64(tag))], newEnv)
        else:
          doAssert false,
            "isVariantReassignSymbolic on non-variant kind=" & $oldSV.kind
    return out2
  of isVariantConstructSym:
    # Round-6 A3 (ADR-0029). Fork-per-tag SYMBOLIC-discriminant variant
    # CONSTRUCTION — clones `isVariantReassignSymbolic`'s fork-per-tag shape
    # (same tag loop, same `disc == tag` pc append) with the deliberate
    # divergence: construction has no "active arm" data to preserve (Nim
    # itself only accepts a non-constant discriminant in constructor syntax
    # when no arm-specific field is set — the parser's `of itVariant:` arm
    # enforces this), so EVERY declared arm's fields allocate FRESH,
    # INDEPENDENTLY, IN EACH FORK (mirrors `lowerVariantLit`'s inactive-arm
    # allocation, applied here to every arm unconditionally).
    #
    # The `maxVariantConstructorForks` budget is a STRUCTURAL check against
    # `stmt.vcsTagSet.len` — before any solver work, uniform across every
    # input path (the tag SET is fixed at parse time; only which tags are
    # ultimately SAT-feasible depends on the path). Reuses the existing
    # `beBudgetExhausted` classified-decline kind (SND-4 "mirror, don't
    # reinvent" — this IS a walk budget running out with paths still live,
    # exactly that kind's own doc comment). No `NimNode` exists here to
    # build a `siteMsg`-shaped message from, so `stmt.vcsLoc` (the
    # PARSE-TIME-captured file:line:col + `n.repr`) is glued in VERBATIM.
    var out2: seq[Path]
    let vcsBudget = w.settings.budget.maxVariantConstructorForks
    if vcsBudget > 0 and stmt.vcsTagSet.len > vcsBudget:
      w.sawUnknown = true
      w.walkDegradeErrors.add SymexErrorInfo(
        kind: beBudgetExhausted, severity: sevError,
        msg: stmt.vcsLoc & ": variant constructor fork budget exhausted " &
             "(maxVariantConstructorForks=" & $vcsBudget & ", feasible " &
             "tags=" & $stmt.vcsTagSet.len & ") — construction unmodeled " &
             "(beBudgetExhausted)")
      for p in paths:
        # `stmt.vcsResultVar` is deliberately left UNBOUND in `p.env` — the
        # same safe-degrade idiom the P2b ref-variant decline uses (any
        # later read raises KeyError, caught by the CR-1c safety net as
        # `weInternalWalkerFault` → sxUnknown; SND-1's per-path taint is
        # ALSO forced via `forkPathTainted` so the verdict never rides a
        # bare `w.sawUnknown` alone).
        out2.add forkPathTainted(p, p.pc, p.env)
      return out2
    let vcsTy = stmt.vcsVariantTy
    for p in paths:
      let (discSV, pr) = lowerInExpr(p, stmt.vcsDiscExpr, w)
      proc vcsDiscEq(tagOrd: int64): Z3Bool =
        case discSV.kind
        of svBV8:  discSV.bv8  == mkBitVec[8](tagOrd)
        of svBV16: discSV.bv16 == mkBitVec[16](tagOrd)
        of svBV32: discSV.bv32 == mkBitVec[32](tagOrd)
        of svBV64: discSV.bv64 == mkBitVec[64](tagOrd)
        of svInt:  discSV.zi   == mkZ3IntLit(tagOrd)
        else:
          raise newException(ValueError,
            "isVariantConstructSym: disc must lower to a BV or Z3Int " &
            "kind (got " & $discSV.kind & ")")
      ## R1-style Invariant-3 soundness: `stmt.vcsDiscExpr` may itself
      ## deposit scalar-raise-fork predicates. Drain and thread the
      ## survivor(s) forward, mirroring `isVariantReassignSymbolic`.
      for cp in drainScalarRaiseForks(pr, w):
        var plainFields: seq[SymVal]
        for fe in stmt.vcsPlainFields:
          plainFields.add lower(cp.env, fe)
        for tag in stmt.vcsTagSet:
          var armFields = initOrderedTable[int, seq[SymVal]]()
          var armNames  = initOrderedTable[int, seq[string]]()
          for arm in vcsTy.vArms:
            armNames[arm.tagOrdinal] = arm.fieldNames
            var fields: seq[SymVal]
            for j, ft in arm.fieldTypes:
              inc variantConstructSymFreshCounter
              let path = "__variantConstructSym." & vcsTy.vObjectName & ".@" &
                         arm.tagName & "." & arm.fieldNames[j] & ".fork" &
                         $tag & "." & $variantConstructSymFreshCounter
              var scratchPC: seq[Z3Bool]
              fields.add allocateSym(ft, path, scratchPC)
            armFields[arm.tagOrdinal] = fields
          let discBoxed = new(SymVal)
          discBoxed[] = bvConst(vcsTy.vDiscTy, int64(tag))
          let newSV = SymVal(kind: svVariant, vDisc: discBoxed,
                             vDiscName: vcsTy.vDiscName,
                             vObjectName: vcsTy.vObjectName,
                             vArmFields: armFields, vArmFieldNames: armNames,
                             vPlainFields: plainFields,
                             vPlainFieldNames: vcsTy.vPlainFieldNames)
          var newEnv = cp.env
          newEnv[stmt.vcsResultVar] = newSV
          out2.add forkPath(cp, cp.pc & @[vcsDiscEq(int64(tag))], newEnv)
    return out2
  of isVariantField:
    # Phase 11 cycle 5 — A-normalised arm-field access. Forks: the
    # in-arm path adds `disc IN matchingTags` to pc and binds
    # `retName` to an ite-chain over the matching arms' field
    # SymVals; the out-of-arm path adds `disc NOT IN matchingTags`
    # and (under `tFieldDefect`) is solved for a witness.
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return
      ## Drain-coverage audit: `stmt.vfRecv` is always an env-resident var —
      ## the parser A-normalises so variant object accesses are through named
      ## bindings (no complex expression as receiver). A violation here means
      ## the parser emitted a non-var receiver and drains would be needed.
      let recv = lowerLeafInExpr(p, stmt.vfRecv)
      # Phase 14 cycle A1c: select the axis-local disc + arm tables
      # by SymVal kind. For svMultiVariant, locate the axis whose
      # arm field-name lists include vfFieldName — the parser
      # selected the same axis via the same membership test.
      var disc: SymVal
      var armFieldsTbl: OrderedTable[int, seq[SymVal]]
      var armFieldNamesTbl: OrderedTable[int, seq[string]]
      case recv.kind
      of svVariant:
        disc            = recv.vDisc[]
        armFieldsTbl    = recv.vArmFields
        armFieldNamesTbl = recv.vArmFieldNames
      of svMultiVariant:
        var found = false
        for ax in recv.mvAxes:
          for _, names in ax.armFieldNames.pairs:
            if stmt.vfFieldName in names:
              disc             = ax.disc[]
              armFieldsTbl     = ax.armFields
              armFieldNamesTbl = ax.armFieldNames
              found = true
              break
          if found: break
        doAssert found,
          "isVariantField on svMultiVariant: no axis owns field " &
          stmt.vfFieldName
      else:
        doAssert false,
          "isVariantField on non-variant SymVal kind=" & $recv.kind
      # Build the matching-arm equalities + collect each arm's SymVal
      # for the requested field.
      var armEqs: seq[Z3Bool]
      var armBindings: seq[(int, SymVal)]
      for tag in stmt.vfMatchingTags:
        let armNames  = armFieldNamesTbl[tag]
        let fieldIx   = armNames.find(stmt.vfFieldName)
        if fieldIx < 0: continue
        let armEq =
          if tag == -1:
            # Phase 14 cycle A2: else-arm membership is the
            # conjunction of negations against all non-else arms on
            # the same axis (ADR-0003 D2).
            var conj: Z3Bool
            var seeded = false
            for otherTag in armFieldsTbl.keys:
              if otherTag == -1: continue
              let neg = not variantDiscEq(disc, int64(otherTag))
              if not seeded: conj = neg; seeded = true
              else:          conj = conj and neg
            if not seeded:
              raise newException(ValueError,
                "isVariantField: else-only variant has no non-else " &
                "arms to negate against (degenerate; the parser " &
                "should not have emitted such an IR)")
            conj
          else:
            variantDiscEq(disc, int64(tag))
        armEqs.add armEq
        armBindings.add (tag, armFieldsTbl[tag][fieldIx])
      doAssert armEqs.len > 0,
        "isVariantField: parser produced an empty matchingTags list"
      var inArmCond = armEqs[0]
      for k in 1 ..< armEqs.len:
        inArmCond = inArmCond or armEqs[k]
      let outOfArmCond = not inArmCond
      # FieldDefect fork — Phase 16 D1a unconditional.
      discard forkDefect(p, outOfArmCond, "FieldDefect", none(string), w)
      if w.shouldStop: return
      # In-arm path — bind retName to the ite-chain over arms.
      var bound = armBindings[armBindings.len - 1][1]
      for k in countdown(armBindings.len - 2, 0):
        let eqB = variantDiscEq(disc, int64(armBindings[k][0]))
        bound = iteSV(eqB, armBindings[k][1], bound)
      var newEnv = p.env
      newEnv[stmt.vfRetName] = bound
      survivors.add forkPath(p, p.pc & @[inArmCond], newEnv)
    survivors
  of isReturn:
    if w.callStack.len == 0:
      @[]
    else:
      # Inside a callee: bind the returned value to the retSym and
      # record the path into the call frame's returnedPaths.
      let frameIx = w.callStack.high
      for p in paths:
        if stmt.retExpr == nil:
          w.callStack[frameIx].returnedPaths.add p
        else:
          ## CR-9 Stage 2: encapsulate seed→reset→lower→drain via wrapper.
          let (retVal, pr) = lowerInExpr(p, stmt.retExpr, w,
                                         some(w.callStack[frameIx].retSym))
          ## R1 (Invariant-3 soundness fix): `stmt.retExpr` may itself
          ## deposit scalar-raise-fork predicates (e.g. `s[i]` OOB,
          ## `x div 0`). Undrained, those were silently discarded — no
          ## raise fork, no bounds narrowing. Drain and thread the
          ## survivor(s) forward, mirroring `isLet`/`isAssign`.
          for cp in drainScalarRaiseForks(pr, w):
            let retSym = w.callStack[frameIx].retSym
            # v64 (chapulin catalog #6): a COMPOSITE-typed retSym (svTuple/
            # svArray/…) reaching this binding used to flow into `retBindEq`,
            # whose non-primitive arm RAISES ValueError — an in-walk raise
            # that unwinds through live `seq[Path]` state (the b7258f7/CR-1c
            # C-backend silent-loss hazard). Chapulin observed the same shape
            # both as a hard native crash and as a net-caught
            # `weInternalWalkerFault` — nondeterministic manifestations of
            # this one raise. Repro: DESTRUCTURING a tuple return from a
            # loop-bearing callee that can raise (`let (_, p1) =
            # readCStringTwin(data, 2)`); a `discard`ed call of the same
            # callee never arrives here composite-typed and still proves.
            # Composite binding through this drain is not yet wired (P1
            # wired tuple RETURN PARSING, not the raise-fork return bind) —
            # degrade IN-BAND: classify + taint the returned path
            # (uncertain ⇒ no false sxSat), never raise.
            # v69 (sello #2): svTuple joins the wired set — retBindEq now
            # binds tuples structurally per field. svArray/other composites
            # (and closures returning tuples, bound at the funcApp site)
            # remain in the degrade net.
            # Round-6 A2 (ADR-0029): svVariant joins the wired set —
            # retBindEq's general encoding (discEq + guarded per-arm field
            # eq + plain-field eq) binds a variant-returning callee.
            if retSym.kind notin {svBool, svInt, svBV8, svBV16, svBV32,
                                  svBV64, svFloat32, svFloat64, svString,
                                  svTuple, svVariant}:
              # NOTE: `w.walkDegradeErrors`, NOT the `loweringDegradeErrors`
              # threadvar — that sink is reset at every `lowerInExpr` wrapper
              # entry, so an entry added HERE (after the wrapper returned)
              # would be wiped by the next lowering before verdict assembly.
              w.walkDegradeErrors.add SymexErrorInfo(
                kind: feUnsupportedOp, severity: sevError,
                msg: "composite-typed proc return (kind " & $retSym.kind &
                     ") bound through the scalar-raise drain is not yet " &
                     "wired — path degraded to sxUnknown (feUnsupportedOp)")
              w.sawUnknown = true
              w.callStack[frameIx].returnedPaths.add forkPathTainted(
                cp, cp.pc, cp.env)
              continue
            # Reconcile mixed int reps (e.g. callee returns svInt because
            # of #135 range propagation while retSym was allocated svBV*).
            # CR-9(c) D5: reconcileInt handles the cross-rep case; retBindEq
            # then works on same-kind operands (bv2int was applied if needed).
            let (rSym, rVal) = reconcileInt(retSym, retVal)
            let retConstraint =
              # Phase 15 G3: same-kind structural binding (BV-wrap semantics
              # preserved; Z3Int = Z3Int when both are Int after reconcileInt;
              # float uses a NaN-safe structural eq so a NaN-returning callee
              # is not pruned; string binds natively). This is what wires a
              # value-returning generic instantiated at `float64`/`string` to
              # flow its result into the caller.
              retBindEq(rSym, rVal)
            w.callStack[frameIx].returnedPaths.add forkPath(
              cp, cp.pc & @[retConstraint], cp.env)
      @[]
  of isCall:
    # ---- #137: opaque effectful call ----
    if stmt.opaque:
      # Don't resolve a body; allocate fresh retSym; mark path
      # uncertain so any target reached on this path degrades to
      # sxUnknown rather than emitting an unsound witness.
      w.sawUnknown = true
      var out2: seq[Path]
      for p in paths:
        var newEnv = p.env
        var pcInit: seq[Z3Bool]
        if stmt.retName.len > 0:
          inc w.synthZ3
          let z3Name = stmt.retName & "_op" & $w.synthZ3
          newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
        out2.add forkPathTainted(p, p.pc & pcInit, newEnv)
      return out2
    if not w.procs.hasKey(stmt.callee):
      # The callee's `ProcSig` is absent. Pre-G1c this "should not happen"
      # (the parser rejected unresolved callees at compile time); G1c adds a
      # legitimate cause — a generic instantiation OVER the per-proc cap is
      # intentionally NOT registered (`maxInstantiationsPerProc`), so its
      # `mkCall` key has no `ProcSig`. Treat it exactly like the depth-bail
      # arm: continue with a FRESH unconstrained retSym (so a downstream read
      # of `stmt.retName` does not KeyError) and mark the surviving paths
      # uncertain so any target reached on them degrades to sxUnknown — never
      # an unsound witness. `geInstantiationCapped` is surfaced from
      # `prog.parseErrors` (see `runSymexImpl`), so the unknown is never silent.
      w.sawUnknown = true
      var out2: seq[Path]
      for p in paths:
        var newEnv = p.env
        var pcInit: seq[Z3Bool]
        if stmt.retName.len > 0:
          inc w.synthZ3
          let z3Name = stmt.retName & "_cap" & $w.synthZ3
          newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
        out2.add forkPathTainted(p, p.pc & pcInit, newEnv)
      return out2
    let sig = w.procs[stmt.callee]
    # Statistics
    if not w.callStats.hasKey(stmt.callee):
      w.callStats[stmt.callee] = CallStat(name: stmt.callee, walked: 0, cacheHits: 0)
    # Depth check
    if w.callStack.len >= w.settings.budget.maxCallDepth:
      # Bail: continue with a fresh unconstrained retSym; flag unknown.
      # The surviving paths are marked uncertain so any target hit on
      # them degrades to sxUnknown (the witness would otherwise be
      # an unsoundly-Z3-defaulted value).
      w.sawUnknown = true
      var out2: seq[Path]
      for p in paths:
        var newEnv = p.env
        var pcInit: seq[Z3Bool]
        if stmt.retName.len > 0:
          inc w.synthZ3
          let z3Name = stmt.retName & "_d" & $w.synthZ3
          newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
        out2.add forkPathTainted(p, p.pc & pcInit, newEnv)
      out2
    else:
      var survivors: seq[Path]
      for p in paths:
        if w.shouldStop: return
        # Phase 15 R1b: seed the caller-heap threadvars from THIS path so a
        # CLOSURE call lowered out of `p.env` below (a closure passed as an
        # argument, or invoked while lowering an actual) descends with this
        # path's threaded heap (ADR-0010 R1b — the closure-arm companion to the
        # structural `isCall` forkPath threading).
        seedCallerHeapThreadvars(p)
        # Lower actuals in the caller env once; reused for cache key
        # and for callee env construction.
        var argVals: seq[SymVal]
        convFloatToIntBoundConds = @[]    ## Phase 15 CR-3/CR-4: these args' bounds
        w.convFloatToIntBoundConds = @[]  ## CR-9 Stage 6 Group-1: WalkCtx field
        convFloatToIntDomainConds = @[]   ## R16-2: parallel raise-fork sink reset
        w.convFloatToIntDomainConds = @[] ## R16-2: WalkCtx field
        parseIntRaiseConds = @[]          ## CR-21: also reset threadvar (was only w.field)
        w.parseIntRaiseConds = @[]        ## CR-9 Stage 6 Group-2: WalkCtx field
        divByZeroConds = @[]              ## R16-3: div/mod-by-zero raise sink reset
        w.divByZeroConds = @[]            ## R16-3: WalkCtx field
        overflowConds = @[]               ## R16-4: signed-integer overflow raise sink reset
        w.overflowConds = @[]             ## R16-4: WalkCtx field
        strIndexOobConds = @[]            ## SND-4: string-index OOB raise sink reset
        w.strIndexOobConds = @[]          ## SND-4: WalkCtx field
        for i, formal in sig.params:
          ## v69 (sello #1): shape a bare-literal actual at the FORMAL's width.
          ## Round-6 B5 (ADR-0028 Leg 1, chained composition): `intLitProto`
          ## always shapes a plain `itInt` formal's literal actual as BV — the
          ## type-driven default. A formal `collectIntOffsetParams` traced
          ## (`IRParam.isIntOffset`, now also set for CALLEES via
          ## `parseCalleeImpl`, not just top-level entry procs) instead needs
          ## an svInt proto, so a LITERAL offset argument (e.g. the corpus's
          ## own `readCStringHelper(s, 0)` first hop) arrives Int-sorted
          ## exactly like a traced VARIABLE argument already does (a
          ## non-literal lowers untouched regardless of proto — this only
          ## ever affects literal shaping).
          let argProto = if formal.isIntOffset: some(SymVal(kind: svInt, zi: mkInt(0)))
                         else: intLitProto(formal.ty)
          argVals.add lower(p.env, stmt.cargs[i], argProto)
        let pd = drainPendingLowerEffects(p)  ## re-review S-3: drain float bounds + closure-arg heap
        # CR-21/R16-3: drain parseInt and div/mod-by-zero raise conditions accumulated
        # during arg-lowering. `drainScalarRaiseForks` chains both drains and returns
        # the surviving non-raise continuations. The callee dispatch below runs once
        # per continuation (typically 1 path, so zero overhead on the common case).
        discard drainConvFloatToIntRaises(p, w)  ## R16-2: RangeDefect fork from pre-narrowing p
        for p in drainScalarRaiseForks(pd, w):  ## R16-3: parseInt + div/mod-by-zero raise forks
          if w.shouldStop: break
          # Cache lookup — pure procs with deterministic-arg-shape hits
          # are served without re-walking. The cache entry's `pcDelta`
          # carries the returning-path constraints; we extend the
          # current path with them.
          let key = argShapeKey(stmt.callee, argVals)
          if key in w.activeCalls:
            # Mutual / direct recursion with identical args — the call
            # is already being walked further up the stack. Break the
            # cycle: return a fresh symbolic retval, mark uncertain.
            w.callStats[stmt.callee] = CallStat(
              name: stmt.callee,
              walked: w.callStats[stmt.callee].walked,
              cacheHits: w.callStats[stmt.callee].cacheHits + 1)
            var newEnv = p.env
            var pcInit: seq[Z3Bool]
            if stmt.retName.len > 0:
              inc w.synthZ3
              let z3Name = stmt.retName & "_cyc" & $w.synthZ3
              newEnv[stmt.retName] = freshRetSym(stmt.retTy, z3Name, pcInit)
            survivors.add forkPathTainted(p, p.pc & pcInit, newEnv)
            continue
          if w.callCache.hasKey(key):
            let entry = w.callCache[key]
            w.callStats[stmt.callee] = CallStat(
              name: stmt.callee,
              walked: w.callStats[stmt.callee].walked,
              cacheHits: w.callStats[stmt.callee].cacheHits + 1)
            var newEnv = p.env
            if stmt.retName.len > 0:
              newEnv[stmt.retName] = entry.retSym
            survivors.add forkPath(p, p.pc & entry.pcDelta, newEnv)
            continue
          # Build callee env
          var calleeEnv: Env
          # #140: track var-param formal→actual binding for write-back.
          var varArgs: seq[(string, string)]   # (formalName, callerVarName)
          for i, formal in sig.params:
            calleeEnv[formal.name] = argVals[i]
            if formal.isVar and stmt.cargs[i].kind == iekVar:
              varArgs.add (formal.name, stmt.cargs[i].vname)
          # Allocate retSym with a *runtime-fresh* Z3 name. Phase 15 G3: a
          # non-bool, non-void return type (float/string/composite as well as
          # int) routes through `freshRetSym` so a value-returning generic
          # instantiated at e.g. `float64` gets a correctly-typed placeholder.
          # Any init-side constraints (string byte-range floor, …) are threaded
          # onto the post-call survivor paths below (where `retSym` flows out).
          inc w.synthZ3
          let z3Name = stmt.retName & "_c" & $w.synthZ3
          var retInit: seq[Z3Bool]
          let retSym = if sig.isVoid:
                         SymVal(kind: svBool, bo: mkBool(true))  ## placeholder
                       else:
                         # Round-6 B5: thread the parse-time-traced offset
                         # positions so a chained scan's second-hop offset
                         # allocates svInt instead of the type-driven BV
                         # default (see `IRStmt.isCall.retIntOffsetPositions`).
                         freshRetSym(stmt.retTy, z3Name, retInit,
                                     stmt.retIntOffsetPositions)
          w.callStack.add CallFrame(
            callee: stmt.callee, retSym: retSym,
            retName: stmt.retName, returnedPaths: @[])
          w.callStats[stmt.callee] = CallStat(
            name: stmt.callee,
            walked: w.callStats[stmt.callee].walked + 1,
            cacheHits: w.callStats[stmt.callee].cacheHits)
          w.activeCalls.incl key
          # Phase 15 R1b call-ENTRY heap threading: the callee inherits the
          # CALLER's logical-heap state (`heaps` / `heapDepth` / `allocCounters`)
          # as its starting heap, instead of R1's fresh-empty default. `forkPath`
          # deep-copies all three (`deepCopyHeapState` + by-value `heapDepth`), so
          # a deref in the callee reads the SAME heap array the caller already
          # constrained (ADR-0010 R1b). Live as of R1 (heaps are no longer empty).
          let calleePath = forkPath(p, p.pc, calleeEnv)
          # Phase 15 E1: per-frame exception context. Save the caller's frame
          # (handler stack + in-flight exn) and install a fresh one before walking
          # the callee body — a `try` opened inside the callee must not leak to
          # the caller. Inert in E1 (handlerStack/inFlightExn always empty), wired
          # so E3/E5 raise-flow threading is correct by construction.
          pushFrame(w)
          let fallThrough = walk(sig.body, @[calleePath], w)
          # Phase 15 E3 inter-proc propagation. Capture any raises that escaped the
          # CALLEE's own handlers (recorded on the callee frame's `escaped` channel
          # by `routeRaise`) BEFORE popFrame restores the caller frame. After the
          # pop, re-route each through the CALLER's handler stack: a `try` around
          # this call site catches the helper's raise. Heap/pc state at the raise
          # point is preserved on `er.path` (R1b merge — structural now, inert until
          # Cluster R). The handler-body continuations join the call's survivors.
          let calleeEscaped = w.frame.escaped
          popFrame(w)
          for er in calleeEscaped:
            var rEnv = p.env
            let raisePath = forkPath(er.path, er.path.pc, rEnv)
            survivors.add routeRaise(raisePath, er.typeId, er.msg, w)
            if w.shouldStop: return survivors
          let frame = w.callStack[w.callStack.high]
          w.callStack.setLen(w.callStack.high)
          w.activeCalls.excl key
          # Cache: single-return, single-fall-through-free, non-uncertain
          # calls cache for argShape-keyed reuse. Phase 15 E3: a callee that
          # escaped a raise is NOT cached — its summary is incomplete (a cache hit
          # would replay the normal return but silently drop the escaped raise).
          # ADR-0012: the cache replays only `pcDelta` (branch + retInit), NOT the
          # callee's `defectSurvivorPc`. An arith-defect callee normally ESCAPES
          # (calleeEscaped != [] ⇒ already not cached); but a callee that CATCHES
          # its own defect (try/except) could add a defect-survivor fact without
          # escaping. Conservatively skip caching when the callee added any such
          # fact, so a cache hit can never silently drop a `not overflow`/`not
          # divByZero` feasibility constraint. (Sound; merely less reuse.)
          if calleeEscaped.len == 0 and
             frame.returnedPaths.len == 1 and fallThrough.len == 0 and
             not frame.returnedPaths[0].uncertain and
             frame.returnedPaths[0].defectSurvivorPc.len == p.defectSurvivorPc.len:
            let cp = frame.returnedPaths[0]
            let prefixLen = p.pc.len
            if cp.pc.len >= prefixLen:
              # Phase 15 G3: `retInit` (retSym init-side constraints, e.g. the
              # string byte-range floor) must ride in `pcDelta` so a cache REPLAY
              # re-asserts them on the cached retSym.
              w.callCache[key] = CallCacheEntry(
                retSym: retSym,
                pcDelta: retInit & cp.pc[prefixLen ..< cp.pc.len])
          for cp in frame.returnedPaths & fallThrough:
            var newEnv = p.env
            if stmt.retName.len > 0:
              newEnv[stmt.retName] = retSym
            # #140: propagate var-param mutations back to caller's env.
            for (formalName, callerName) in varArgs:
              if cp.env.hasKey(formalName):
                newEnv[callerName] = cp.env[formalName]
            # Phase 15 R1b return-MERGE: the post-call caller path carries the
            # callee's exit heap state back out (ADR-0010 R1b).
            # `forkPathWithTaint(cp, ...)` forks from `cp` (the returned
            # CALLEE path), so:
            #   * `heaps`: REPLACEMENT — the callee's final `heaps` become the
            #     caller's, so callee heap modifications are observed downstream.
            #   * `heapDepth`: threaded from `cp` (the callee's exit depth).
            # `allocCounters`, however, must NOT be a plain replacement: we take
            # `max(caller[T], callee[T])` per type key so the freshness invariant
            # holds — a post-call caller `new T` uses a counter strictly above any
            # callee allocation and cannot collide with a callee-allocated ref on
            # this path. (Inert until R2 wires `isNew`/`allocCounters` increments;
            # the merge is correct by construction now.)
            # Phase 15 G3: `retInit` threads the retSym init constraints onto the
            # surviving caller path (where `retSym` becomes visible).
            # R3 hardening: taint is neither a bare propagate nor a bare force
            # here — a post-call path is tainted if EITHER the caller (`p`) or
            # the callee (`cp`) picked up SND-1/SND-3 taint, so this is the one
            # site that calls the internal `forkPathWithTaint` directly with a
            # computed bool instead of `forkPath`/`forkPathTainted`.
            let merged = forkPathWithTaint(cp, cp.pc & retInit, newEnv,
                                           p.uncertain or cp.uncertain)
            for tkey, callerCount in p.allocCounters:
              let calleeCount = merged.allocCounters.getOrDefault(tkey, 0)
              if callerCount > calleeCount:
                merged.allocCounters[tkey] = callerCount
            survivors.add merged
      survivors
  of isAssert:
    var out2: seq[Path]
    for p0 in paths:
      if w.shouldStop: return
      ## CR-9 Stage 2: encapsulate seed→reset→lowerBool→drain via wrapper.
      ## drainScalarRaiseForks is a FORK — NOT inside the wrapper; called on pb0.
      let (cond, pb0) = lowerBoolInExpr(p0, stmt.acond, w)
      let cont = drainScalarRaiseForks(pb0, w)  ## R16-3: parseInt + div/mod-by-zero raise forks
      discard drainConvFloatToIntRaises(p0, w)  ## R16-2: RangeDefect fork from pre-narrowing p0
      if cont.len == 0: continue
      let p = cont[0]
      discard forkDefect(p, not cond, "AssertionDefect", none(string), w)   ## Phase 16 D1a
      out2.add forkPath(p, p.pc & @[cond], p.env)
    out2
  of isAssume:
    ## Phase 16 SND-2 (ADR-0019): filter/prune, NOT assert. Shares steps
    ## (1) lowerBoolInExpr+drainScalarRaiseForks, (2) drainConvFloatToIntRaises,
    ## and (4) conjoin cond into pc VERBATIM with the isAssert arm above —
    ## those steps surface raises arising from EVALUATING cond itself (e.g.
    ## `symexAssume(1 div x == 0)` with symbolic x must still surface
    ## DivByZeroDefect) and are not assert-specific. The ONE thing omitted is
    ## step (3): `forkDefect(... "AssertionDefect" ...)` — a violatable
    ## `symexAssume` must NEVER itself produce a false sxRaised(AssertionDefect).
    var out2: seq[Path]
    for p0 in paths:
      if w.shouldStop: return
      let (cond, pb0) = lowerBoolInExpr(p0, stmt.acond, w)
      let cont = drainScalarRaiseForks(pb0, w)
      discard drainConvFloatToIntRaises(p0, w)
      if cont.len == 0: continue
      let p = cont[0]
      out2.add forkPath(p, p.pc & @[cond], p.env)
    out2
  of isTargetLabel:
    when defined(symexTestInjectWalkerFault):
      # CR-1c fault-injection hook (RFC-chapulin-hardening, Cluster 2):
      # compiled OUT of every normal build/test — only present under the
      # `-d:symexTestInjectWalkerFault` define, wired for exactly one test
      # file via its companion `tests/tsymex_phase16_CR1c_internal_fault.nim.cfg`
      # (Nim auto-reads `<testfile>.nim.cfg`). Raises a synthetic, genuinely
      # UNANTICIPATED-shaped exception (plain `ValueError`, indistinguishable
      # in TYPE from a real walker bug) the moment dispatch reaches a
      # sentinel `symexTarget("__inject_walker_fault__")` label, regardless
      # of whether that label is the run's actual solve target — this
      # exercises the last-resort `walk` dispatch catch end-to-end on BOTH
      # backends through the unmodified `dt-bounded.sh` harness.
      if stmt.tname == "__inject_walker_fault__":
        raise newException(ValueError,
          "CR-1c synthetic fault (symexTestInjectWalkerFault)")
      # Round-3 Defect-net variant (crash-doctrine decision, Corey
      # 2026-08-06): a SECOND sentinel raising an `AssertionDefect` — the
      # exact type the ~63 internal doAsserts produce — so the new outermost
      # `except Defect` arm is exercised end-to-end (including the fiber
      # trampoline ferrying the Defect across the fiber switch on Windows).
      if stmt.tname == "__inject_walker_defect__":
        raise newException(AssertionDefect,
          "round-3 synthetic defect (symexTestInjectWalkerFault)")
    if w.target.kind == stkLabel and w.target.label == stmt.tname:
      for p in paths:
        if w.shouldStop: return
        if p.uncertain:
          # Uncertain path: a SAT witness here would be unsound because
          # bailed-call retSyms are unconstrained at the Z3 level.
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, p, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
          of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
    paths
  of isRaise:
    # Phase 15 E3 handler-aware raise. The walker reaches a `raise` on a feasible
    # (already-forked) path. We resolve the type id + message of the exception,
    # then hand each path to `routeRaise`, which consults the current frame's
    # handler stack: a matching `except` CONSUMES the raise (the path transfers
    # into the handler body and continues — those continuation paths flow OUT of
    # this arm); an unmatched raise either escapes to the caller (via the frame's
    # `escaped` channel, drained by the `isCall` arm) or surfaces at the SUT
    # boundary as a public `sxRaised` finding (E2b semantics, target-gated).
    #
    # Resolve the type id + message of the exception being raised. A bare
    # `raise` (re-raise) with an in-flight exn re-raises THAT exn's type;
    # with no in-flight exn and an empty handler stack it is an
    # `eeRaiseOutsideHandler` classified error (nothing to re-raise).
    var raiseTypeId = stmt.raiseTypeId
    var raiseMsg = evalRaiseMsg(paths[0].env, stmt.raiseMsg)
    if stmt.raiseIsReraise:
      if w.frame.inFlightExn.isSome:
        # Re-raise the in-flight exception (propagate its ExnRecord).
        let exn = w.frame.inFlightExn.get
        raiseTypeId = exn.typeId
        raiseMsg = exn.msg
      elif w.frame.handlerStack.len == 0:
        # Bare `raise` at top level with nothing to re-raise → classified error.
        raise (ref SymexRaiseOutsideHandlerError)(
          msg: "bare `raise` (re-raise) with no in-flight exception")
      else:
        # Inside a handler with no recorded in-flight exn yet — handler-stack
        # re-raise is E3+. Surface as unknown rather than guess.
        for p in paths:
          w.sawUnknown = true
        return @[]
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      survivors.add routeRaise(p, raiseTypeId, raiseMsg, w)
    survivors
  of isTry:
    # Phase 15 E3. `try: body  (except [T,…]: h)*  [finally: f]`. Push a handler
    # frame for the try's `except` arms onto the CURRENT call frame's handler
    # stack, walk the body (raises within consult this frame), then pop. A raise
    # in the body is routed by `routeRaise` to the first matching arm (exact
    # type-string membership at E3; subtype catch is E4; a bare `except:` is
    # catch-all). The handler bodies' continuation paths emerge from `routeRaise`
    # and are returned alongside the body's normal fall-through.
    let myDepth = w.frame.handlerStack.len  ## index this try's HandlerFrame sits at
    w.frame.handlerStack.add HandlerFrame(handlers: stmt.tryHandlers,
                                          finallyBlock: stmt.tryFinally)
    let bodyPaths = walk(stmt.tryBody, paths, w)
    # Pop our handler frame — it is no longer active once the body is walked.
    if w.frame.handlerStack.len > myDepth:
      w.frame.handlerStack.setLen(myDepth)
    # Claim the handler-body continuations for raises CAUGHT at our depth (routed
    # by `routeRaise` while walking the body or a callee called from the body).
    # These join the body's normal fall-through; the caught path exits the try.
    var continuations = bodyPaths
    var keptCaught: seq[tuple[depth: int, path: Path]]
    for c in w.frame.caught:
      if c.depth == myDepth: continuations.add c.path
      else:                  keptCaught.add c
    w.frame.caught = keptCaught
    # Phase 15 E5: claim the RAISED exit continuations deferred to this try's
    # finally (recorded by `routeRaise` on `pendingRaise` at our depth when a
    # raise in the body found no matching `except` but is guarded by our
    # `finally`). These run the finally on the RAISED path and re-propagate.
    var raisedConts: seq[tuple[path: Path, typeId: string, msg: Option[string]]]
    var keptPending: seq[tuple[depth: int, path: Path, typeId: string,
                              msg: Option[string]]]
    for pr in w.frame.pendingRaise:
      if pr.depth == myDepth: raisedConts.add (pr.path, pr.typeId, pr.msg)
      else:                   keptPending.add pr
    w.frame.pendingRaise = keptPending
    if stmt.tryFinally == nil:
      # No finally: normal continuations flow through; any raised continuations
      # re-propagate immediately (re-route through the now-popped outer stack).
      var survivors = continuations
      for rc in raisedConts:
        if w.shouldStop: return survivors
        survivors.add routeRaise(rc.path, rc.typeId, rc.msg, w)
      survivors
    else:
      # Phase 15 E5 finally composition. The finally runs ONCE per exit
      # continuation (never combinatorially): once on the merged normal-exit
      # set, and once per raised-exit continuation. The handler stack is already
      # popped to `myDepth`, so a raise INSIDE the finally routes to the
      # NEXT-OUTER try/finally (or escapes / surfaces) — it does NOT re-enter
      # this finally (no loop).
      var survivors: seq[Path]
      # (a) NORMAL exits: walk finally; finally fall-through survives. A raise in
      #     the finally is routed by `routeRaise` (replaces — there is no
      #     in-flight exn on a normal exit, so a finally raise is a fresh raise,
      #     NOT an `eeRaiseOutsideHandler`). `inFlightExn` stays untouched (none).
      if continuations.len > 0:
        survivors.add walk(stmt.tryFinally, continuations, w)
        if w.shouldStop: return survivors
      # (b) RAISED exits: for each, set `inFlightExn` to the original exn for the
      #     finally's duration (so a bare re-raise inside finally sees it), walk
      #     the finally on the raised path; the survivors are the paths where the
      #     finally fell through WITHOUT raising — on those the ORIGINAL exn is
      #     RE-RAISED (re-routed outward). Where the finally itself raised, that
      #     new exn was already routed by `routeRaise` and REPLACES the original
      #     (so we do NOT re-raise the original on those sub-paths).
      for rc in raisedConts:
        if w.shouldStop: return survivors
        let savedInFlight = w.frame.inFlightExn
        w.frame.inFlightExn = some(ExnRecord(typeId: rc.typeId, msg: rc.msg))
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        let finallyNormal = walk(stmt.tryFinally, @[rc.path], w)
        w.frame.inFlightExn = savedInFlight
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        for fp in finallyNormal:
          if w.shouldStop: return survivors
          # Finally fell through on this sub-path → re-propagate the ORIGINAL.
          survivors.add routeRaise(fp, rc.typeId, rc.msg, w)
      survivors
  of isDeref, isNew, isDerefWrite:
    # Stage 7 (CR-7) Cluster R: heap read, allocation, and heap write arms
    # extracted into `walkHeapArm` (defined above, before this proc body).
    # `isIndex` is left inline (handles Table/seq/array/ref — multi-theory).
    walkHeapArm(stmt, paths, w)
  of isUnsupported:
    # SND-1: an unmodeled statement dropped its mutation, so `env` is now
    # STALE relative to the real program. Taint-and-continue (SND-1, RFC
    # Cluster 1): mirror the `maxCallDepth` bail arm above — set
    # `w.sawUnknown` and fork every path through with `uncertain = true`
    # rather than continuing with unmarked (and therefore falsely-trustable)
    # state. This is Invariant-3-safe AND preserves downstream exploration:
    # the existing `uncertain` chokepoints (`isTargetLabel`, `routeRaise`)
    # demote any later sxSat/sxRaised on this path to sxUnknown, so a
    # dropped mutation can never surface a silently-wrong witness.
    w.sawUnknown = true
    var out2: seq[Path]
    for p in paths:
      out2.add forkPathTainted(p, p.pc, p.env)
    out2
  of isUnsafeCast:
    # Phase 15 R11 (ADR-0010, RFC §R11). An unsafe pointer materialisation
    # (`cast[ptr T]`/`addr`/`unsafeAddr`) is unmodelable in the logical-heap
    # model. HALT the path: set `sawUnknown` → the verdict degrades to
    # `sxUnknown` (Invariant 3), and DROP the path (`@[]`) so the unmodelable
    # pointer binding (which was NOT added to env) is never referenced
    # downstream (a subsequent `p[]` deref would otherwise key-fault on the
    # unbound name). The classified `heUnsafeCast` (sevError) was emitted at
    # parse time into `prog.parseErrors` (drained into `RawResult.errors` on
    # every verdict branch — the SAME classify→sxUnknown mechanism R8
    # established for `hePtrArith`), so the unknown is never silent.
    w.sawUnknown = true
    @[]

proc routeRaise(p: Path, typeId: string, msg: Option[string],
                w: var WalkCtx): seq[Path] =
  ## Phase 15 E3. Route a raise on path `p` carrying `typeId`/`msg`. This is the
  ## single handler-matching primitive, called both inline by `walk(isRaise)` and
  ## by the `isCall` arm for inter-procedural propagation of a callee's escaped
  ## raise. It searches the CURRENT call frame's handler stack top-down for the
  ## first `ExceptHandler` whose `typeIds` contains `typeId` (EXACT-STRING
  ## membership — subtype catch is E4; an empty `typeIds` is a bare `except:`
  ## catch-all matching everything).
  ##
  ## MATCH → the raise is CONSUMED: walk the matched handler body on `p` with
  ## `inFlightExn` set to the raised exn (so a bare `raise` re-raises it), cleared
  ## on normal handler exit. The handler body's continuation paths are recorded on
  ## the frame's `caught` channel (tagged by the catching try's depth) so they
  ## EXIT the try via the owning `isTry` arm — they must NOT flow back inline into
  ## the try body at the raise site. `routeRaise` itself returns `@[]` (the raise
  ## terminates the current straight-line path).
  ##
  ## NO MATCH (or empty handler stack) → propagate. If this is a callee frame
  ## (`frameStack` non-empty), record the raise on the frame's `escaped` channel
  ## for the caller's `isCall` arm to re-route (inter-proc). Otherwise we are at
  ## the SUT boundary: surface a public `sxRaised` finding (E2b semantics,
  ## target-gated) and terminate the path (return `@[]`).
  if p.uncertain:
    # Bailed-call retSyms are unconstrained at the Z3 level; neither a witness
    # nor a confident handler-routing decision is sound here.
    w.sawUnknown = true
    return @[]
  # Phase 15 E4. Subtype matching (replaces E3's exact-string membership). An
  # unknown raised type (not in `exnTable` nor `userExnHierarchy`) is matched
  # ONLY against a bare `except:` — never a named handler — and records a
  # `eeUnknownExnType` sevWarning (Invariant 3: no silent false-negative). A
  # known type matches a named handler `ht` iff `isSubtypeOf(typeId, ht, …)`.
  let raisedKnown = isKnownExnType(typeId, w.statics.exnTable,
                                   w.statics.userExnHierarchy)
  if not raisedKnown:
    let exnWarn = SymexErrorInfo(kind: eeUnknownExnType, severity: sevWarning,
                                 msg: typeId)
    unknownExnWarnings.add exnWarn   # threadvar: fallback
    w.unknownExnWarnings.add exnWarn # CR-9 Stage 5: LIVE WalkCtx field
  # 1. Search the handler stack top-down for the first matching arm.
  for i in countdown(w.frame.handlerStack.high, 0):
    let hf = w.frame.handlerStack[i]
    for h in hf.handlers:
      var matched = h.typeIds.len == 0   ## bare `except:` always catches
      if not matched and raisedKnown:
        for ht in h.typeIds:
          if isSubtypeOf(typeId, ht, w.statics.exnTable,
                         w.statics.userExnHierarchy):
            matched = true
            break
      if matched:
        # MATCH. Pop the handler stack down to BELOW the matched frame for the
        # duration of the handler body (an inner try no longer guards us, and a
        # re-raise inside the handler must propagate to the NEXT-outer try, not
        # re-enter this one). Restore afterwards.
        let savedStack = w.frame.handlerStack
        let savedInFlight = w.frame.inFlightExn
        w.frame.handlerStack.setLen(i)
        w.frame.inFlightExn = some(ExnRecord(typeId: typeId, msg: msg))
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8: mirror into
                                                     ## the lower-time threadvars
                                                     ## so getCurrent* see this exn
                                                     ## during the handler body.
        let handlerPaths = walk(h.body, @[p], w)
        # Normal handler exit: clear the in-flight exn, restore the stack.
        w.frame.handlerStack = savedStack
        w.frame.inFlightExn = savedInFlight
        setInFlightThreadvars(w.frame.inFlightExn)   ## Phase 15 E8
        # Record the handler continuations on the frame's `caught` channel tagged
        # by the catching try's depth (`i`). The owning `isTry` claims them and
        # merges them into ITS continuation, so the caught path exits the try
        # instead of resuming the try body after the raise site.
        for hp in handlerPaths:
          w.frame.caught.add (depth: i, path: hp)
        return @[]
  # Phase 15 E5. No `except` arm matched, but a `finally` may still guard this
  # raise: it must run on the RAISED exit path BEFORE the raise propagates
  # onward. Scan the handler stack top-down for the deepest frame with a non-nil
  # `finallyBlock`; if found, defer the raise to that try's `isTry` arm (which
  # claims `pendingRaise` at its depth, runs the finally, and composes the
  # result). This is the raised-path analogue of E3's caught channel. The
  # finally interception happens BEFORE the escape/boundary fall-through below so
  # that a `try: raise … finally: …` (no except) still runs its finally.
  for i in countdown(w.frame.handlerStack.high, 0):
    if w.frame.handlerStack[i].finallyBlock != nil:
      w.frame.pendingRaise.add (depth: i, path: p, typeId: typeId, msg: msg)
      return @[]
  # 2. No handler matched in this frame.
  if w.frameStack.len > 0:
    # We are inside a callee — let the raise escape to the caller's handlers.
    # The caller's `isCall` arm drains `escaped` after we return. Carry the
    # raise-site path so heap/pc state is preserved (R1b; structural now).
    w.frame.escaped.add EscapedRaise(path: p, typeId: typeId, msg: msg)
    return @[]
  # 3. Top-level (SUT) frame: surface as a public sxRaised finding.
  # Phase 15 E6. A raise of a Nim `Defect` subtype is a CONTRACT VIOLATION that
  # must surface as `sxRaised{isDefect: true}` regardless of the user's search
  # target (a reachable defect is never silently dropped — that would let a
  # property test pass an input the SUT would crash on). EXCEPT when the
  # defect's `DefectKind` is in `settings.defectExclusions` (default: OOM +
  # stack-overflow): those are suppressed, since modelling them yields spurious
  # findings for virtually all real SUTs. A non-defect `CatchableError` raise
  # keeps the E2b target-gated behavior (only surfaced under an assertion or a
  # matching `stkRaisedExn` search; otherwise the path just terminates).
  let raisedIsDefect = isDefect(w.statics.exnTable, typeId,
                                w.statics.userExnHierarchy)
  let defectExcluded =
    raisedIsDefect and
    typeIdToDefectKind(typeId) in w.settings.defectExclusions
  let wantsRaise =
    if defectExcluded:
      false  ## E6: an excluded defect is suppressed (no finding).
    elif raisedIsDefect:
      true   ## E6: a non-excluded defect always surfaces.
    else:
      case w.target.kind
      of stkAssertionViolation:
        true   ## a reachable raise is a violation finding
      of stkRaisedExn:
        w.target.typeFilter.len == 0 or w.target.typeFilter == typeId
      else:
        false  ## e.g. an stkLabel search: the raise just terminates the path
  if wantsRaise:
    let (st, wit) = trySolve(w.z3, p, w.params, w.settings,
                             w.tabKeys, w.setMembers, w.initialEnv)
    case st
    of sxSat:
      let iv = InternalVerdict(kind: ivRaised,
                               raisedTypeId: typeId,
                               raisedMsg: msg,
                               raisedWitness: wit,
                               raisedIsDefect: raisedIsDefect)  ## Phase 15 E6
      w.found.add(toPublic(iv))
    of sxUnknown: w.sawUnknown = true
    of sxUnsat:   discard
    of sxRaised:  discard   ## trySolve never returns sxRaised
  @[]

# ---- Phase 15 Cluster C (C2b): closure CALL application ----------------------

proc flattenLeafAsts(sv: SymVal): seq[RawZ3Ast] =
  ## Phase 15 C2b. The FLATTENED sequence of per-leaf raw Z3 asts of a SymVal,
  ## in the SAME order `sortOfTuple` walks the sorts (ADR-0009 D2/D5). Used to
  ## build the `Z3_mk_app` argument vector — the funcSym's domain is the
  ## flattened env-leaf sorts ++ param sorts, so its argument asts are the
  ## flattened env-leaf asts ++ the flattened arg-leaf asts. Nested tuples
  ## flatten recursively; every other kind is a single leaf via `rawAnyAstOf`.
  case sv.kind
  of svTuple:
    for f in sv.fields:
      for a in flattenLeafAsts(f): result.add a
  else:
    result.add rawAnyAstOf(sv)

proc symValFromRawAst(raw: RawZ3Ast, ty: IRType): SymVal =
  ## Phase 15 C2b. Wrap a raw Z3 ast (the result of a closure funcSym
  ## application) into the typed SymVal its `lambdaRetTy` calls for. The funcSym
  ## range sort was declared from `ty` (`sortOfTuple` of an `allocateSym(ty)`
  ## representative), so the wrap is sort-consistent by construction (ADR-0009
  ## D4). Single-leaf scalar return types only (the C2a `buildClosure` asserts
  ## a single-leaf range sort).
  let ctx = requireCurrentContext()
  case ty.kind
  of itInt:
    case ty.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, raw),  ty.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, raw), ty.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, raw), ty.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, raw), ty.signed)
    else:
      raise newException(ValueError,
        "symValFromRawAst: unsupported int width " & $ty.width)
  of itBool:
    ofBool(wrap[Z3Bool](ctx, raw))
  of itFloat32:
    SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, raw))
  of itFloat64:
    SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, raw))
  else:
    raise newException(ValueError,
      "symValFromRawAst: unsupported closure return type kind " & $ty.kind)

proc applyClosureGround(clo: SymVal, argSyms: seq[SymVal],
                        label: string): SymVal   ## Phase 15 C4 fwd-decl.

proc lowerClosureCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C2b (ADR-0009 D6). Closure APPLICATION. Resolve `e.ccCallee` to an
  ## `svClosure`, descend the lambda body ONCE collecting its return sub-paths
  ## `(pc_i, v_i)`, apply the per-site funcSym at the GROUND `(env, args)` of
  ## THIS occurrence (raw `Z3_mk_app`), and assert one GROUND implication per
  ## sub-path:
  ##     implies(and(branch_conds_i), funcApp == v_i)
  ## into `currentClosureCallAxioms` (drained into every `trySolve`). The call
  ## RESULT is the funcApp itself (the axioms constrain it). NEVER a
  ## `∀env,args` axiom — the function is applied at the ground occurrence and
  ## equated to a value, the same decidable shape as G4's eject-pin (the hang
  ## lesson). The body is reached via the site→body map (`svClosure` carries the
  ## site, not the body IR). Descent uses the live `walk` via `currentWalkCtxPtr`
  ## (this proc runs in the `lower` evaluator, which has no `WalkCtx`).
  let ctx = requireCurrentContext()
  # ---- 1. Resolve the callee to an svClosure (Invariant 3 on failure). ----
  if not env.hasKey(e.ccCallee) or env[e.ccCallee].kind != svClosure:
    let cloErr1 = SymexErrorInfo(kind: ceClosureUnknownCallee, severity: sevError,
      msg: "closure call through `" & e.ccCallee &
           "` does not resolve to a closure value in scope")
    currentClosureCallErrors.add cloErr1   # threadvar: fallback
    syncClosureCallError(cloErr1)          # CR-9 Stage 5: LIVE WalkCtx field
    # No semantics: return a FRESH unconstrained result so a downstream read
    # does not crash; the classified error forces sxUnknown at the SUT boundary.
    var fresh: seq[Z3Bool]
    return allocateSym(tInt(64, true), "__closureUnknownCallee", fresh)
  let clo = env[e.ccCallee]
  var argSyms: seq[SymVal]
  for a in e.ccArgs: argSyms.add lower(env, a)
  return applyClosureGround(clo, argSyms, "`" & e.ccCallee & "`")

proc applyClosureGround(clo: SymVal, argSyms: seq[SymVal],
                        label: string): SymVal =
  ## Phase 15 C4 (factored from C2b `lowerClosureCall`). Apply an `svClosure`
  ## to a vector of already-lowered argument SymVals at the GROUND occurrence:
  ## build the per-site funcSym application (raw `Z3_mk_app` over flattened
  ## env-leaf ++ arg asts), descend the lambda body ONCE, and assert one GROUND
  ## implication per body return sub-path (`implies(branch_conds_i, funcApp ==
  ## v_i)`) into `currentClosureCallAxioms` — NEVER a `∀env,args` axiom (the G4
  ## hang lesson). The call RESULT is the funcApp the axioms constrain. Shared
  ## by `lowerClosureCall` (C2b) and the C4 HOF inline path (one application per
  ## seq element). `label` is a human-readable site tag for error messages.
  let ctx = requireCurrentContext()
  doAssert clo.kind == svClosure, "applyClosureGround: not an svClosure"
  let siteKey = (clo.closureSite.siteHash, clo.closureSite.declOrder)
  # CR-9 Stage 4: read closureBodies from live WalkerStatics when in a walk,
  # else fall back to threadvar (applyClosureGround is always in a walk in
  # practice — lowerClosureCall short-circuits when ptr==nil — but the guard
  # keeps the code correct for any future probe path).
  let closureBodiesLive =
    if currentWalkCtxPtr != nil:
      cast[ptr WalkCtx](currentWalkCtxPtr)[].statics.closureBodies
    else:
      currentClosureBodies
  if not closureBodiesLive.hasKey(siteKey):
    # The closure was constructed but its body was never stashed — should not
    # happen (buildClosure always stashes). Classify rather than crash.
    let cloErr2 = SymexErrorInfo(kind: ceClosureUnknownCallee, severity: sevError,
      msg: "closure call through " & label & ": lambda body not reachable for descent")
    currentClosureCallErrors.add cloErr2   # threadvar: fallback
    syncClosureCallError(cloErr2)          # CR-9 Stage 5: LIVE WalkCtx field
    var fresh: seq[Z3Bool]
    return allocateSym(tInt(64, true), "__closureNoBody", fresh)
  let cb = closureBodiesLive[siteKey]
  # ---- 2. Build the funcSym application at THIS occurrence (ground). ----
  # Argument vector = flattened env-leaf asts ++ flattened call-arg asts, in the
  # exact order `buildClosure` built the domain (env leaves then params, D2).
  var appArgs: seq[RawZ3Ast]
  if clo.closureEnv != nil:
    for a in flattenLeafAsts(clo.closureEnv[]): appArgs.add a
  for s in argSyms:
    for a in flattenLeafAsts(s): appArgs.add a
  let argsPtr = if appArgs.len > 0:
                  cast[ptr UncheckedArray[RawZ3Ast]](addr appArgs[0])
                else: nil
  let appRaw = ctx.checkErr Z3_mk_app(ctx.raw, clo.closureRawFD,
    cuint(appArgs.len), argsPtr)
  let funcApp = symValFromRawAst(appRaw, cb.retTy)
  # ---- 3. Inline-budget guard (CallFrameCtx.closureInlineCount). ----
  # `currentWalkCtxPtr` is nil only outside an active walk (the C2a probes never
  # reach here). If absent, fall back to the funcApp alone (no descent, no
  # axiom) — sound but imprecise; classified so the verdict degrades.
  if currentWalkCtxPtr == nil:
    # No active walk: the verdict cannot degrade via w.closureCallErrors, so
    # write only to the threadvar (syncClosureCallError would be a no-op here).
    currentClosureCallErrors.add SymexErrorInfo(
      kind: ceInlineBudgetExceeded, severity: sevError,
      msg: "closure call through " & label &
           " lowered with no active walk context (no body descent)")
    return funcApp
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  template w: untyped = wp[]   ## the live WalkCtx (mutable through the ptr)
  if w.frame.closureInlineCount >= w.settings.budget.maxClosureInlineCount:
    let budgetErr = SymexErrorInfo(kind: ceInlineBudgetExceeded, severity: sevError,
      msg: "closure-application descent exceeded maxClosureInlineCount (" &
           $w.settings.budget.maxClosureInlineCount & ") at " & label)
    currentClosureCallErrors.add budgetErr  # threadvar: fallback
    w.closureCallErrors.add budgetErr       # CR-9 Stage 5: LIVE WalkCtx field
    w.sawUnknown = true
    return funcApp
  # ---- 4. Descend the lambda body ONCE; collect return sub-paths. ----
  # Fresh descent env: params bound to the concrete call args, captures bound
  # from the svClosure's env tuple (by capture name, matching the stash order).
  var descentEnv: Env = initOrderedTable[string, SymVal]()
  if clo.closureEnv != nil and clo.closureEnv[].kind == svTuple:
    let envRec = clo.closureEnv[]
    for i, nm in envRec.fieldNames:
      descentEnv[nm] = envRec.fields[i]
  for i, p in cb.params:
    if i < argSyms.len: descentEnv[p.name] = argSyms[i]
  # Push a call frame whose retSym IS the funcApp: `walk(isReturn)` binds each
  # returning path's value to it as `funcApp == v_i` on that path's pc delta.
  w.callStack.add CallFrame(
    callee: "closure@" & $clo.closureSite.siteHash & "/" &
            $clo.closureSite.declOrder,
    retSym: funcApp, retName: "__closureRet", returnedPaths: @[])
  let frameIx = w.callStack.high
  # Per-frame exception context for the body, and bump the inline budget.
  pushFrame(w)
  w.frame.closureInlineCount = w.frameStack[^1].closureInlineCount + 1
  # Phase 15 R1b call-ENTRY heap threading for the CLOSURE arm: the closure
  # body descends with the CALLER's threaded heap (seeded into the caller-heap
  # threadvars by the walk arm before this expression was lowered), instead of
  # R1's fresh-empty default — so a deref inside the closure body reads the SAME
  # heap the caller already constrained (ADR-0010 R1b). Empty when unset (no
  # caller heap), preserving pre-R1b behaviour. The Table assignments are
  # value-copies (Nim semantics), so the closure descent cannot alias-mutate the
  # caller's tables.
  #
  # Phase 15 CR-5: seed `liveRefs` from the caller's live refs so
  # `assertFreshness` for a `new T` inside the closure body emits
  # `newRef != callerRef` distinctness inequalities against every ref the
  # caller already minted.  Without seeding, the empty `liveRefs` lets Z3
  # alias a closure-body `new T` with a caller ref (spurious aliasing witness).
  # CR-9 Stage 6 Group-3: read caller-heap values from WalkCtx fields when a
  # walk is active (the LIVE store); fall back to threadvars otherwise.
  # `w` is always available here (applyClosureGround has `w: var WalkCtx`).
  let descentBase = Path(pc: @[], env: descentEnv,
                         uncertain: false,
                         heaps: w.callerHeaps,
                         heapDepth: w.callerHeapDepth,
                         allocCounters: w.callerAllocCounters,
                         liveRefs: w.callerLiveRefs)  ## Phase 15 CR-5
  let fallThrough = walk(cb.body, @[descentBase], w)
  let frame = w.callStack[frameIx]
  popFrame(w)
  w.callStack.setLen(frameIx)
  # ---- 5. Lift each body return sub-path to a GROUND per-call axiom (D6). ----
  # Two channels yield sub-paths `(branch_conds_i, v_i)`:
  #   (a) EXPLICIT `return EXPR` — `walk(isReturn)` bound the value to the frame
  #       retSym (== funcApp) as the LAST pc constraint (`funcApp == v_i`), under
  #       that path's branch conditions; the delta = `[branch_conds..., retEq]`.
  #   (b) IMPLICIT `result` / fall-through — a value-returning lambda body whose
  #       last statement is `result = EXPR` (Nim's semchecked implicit result)
  #       leaves `cp.env["result"]` holding v_i with the path still live; we
  #       build `funcApp == result_i` ourselves under that path's pc.
  # Each axiom is GROUND (funcApp applied at THIS occurrence, equated to a value)
  # — NEVER `∀env,args` (the G4 hang). The base descent pc is empty, so a path's
  # full pc IS its branch conditions.
  proc assertArm(branchConds: openArray[Z3Bool], eq: Z3Bool) =
    let ax = if branchConds.len == 0:
               eq                          # single, unconditional return
             else:
               var guard = branchConds[0]
               for k in 1 ..< branchConds.len: guard = guard and branchConds[k]
               guard.implies(eq)
    currentClosureCallAxioms.add ax
    currentClosureCallAxiomStrs.add $ax    # stringify while the ctx is live
  var sawValue = false
  # SND-1b (RFC-chapulin-hardening, walker v39): a body sub-path tainted
  # `uncertain` (SND-1's `isUnsupported`/maxCallDepth taint) must NOT be folded
  # into `currentClosureCallAxioms` — that sink is GLOBAL and drained into
  # EVERY subsequent `trySolve` for the rest of the run (unlike the call-cache,
  # which already gates on `not frame.returnedPaths[0].uncertain`, ~5850). Skip
  # axiomatizing that sub-path and record `ceClosureBodyUncertain` so
  # `closureForcedUnknown` (below, ~7322) whole-run-degrades the verdict
  # instead of asserting a possibly-wrong value as a permanent ground fact.
  var uncertainDrop = false
  for cp in frame.returnedPaths:                       # (a) explicit return
    if cp.pc.len == 0: continue
    sawValue = true
    if cp.uncertain:
      uncertainDrop = true
      continue
    # ADR-0012: cp.pc holds ONLY genuine branch conditions now (defect-survivor
    # negations were split into cp.defectSurvivorPc by the drains), so the guard
    # is clean — this is the fix for the C3 unsound witness. cp.pc[^1] is the
    # retEq value binding; cp.pc[0..<high] are the branch selectors.
    assertArm(cp.pc[0 ..< cp.pc.high], cp.pc[^1])
  for cp in fallThrough:                                # (b) implicit result
    if cp.env.hasKey("result"):
      sawValue = true
      if cp.uncertain:
        uncertainDrop = true
        continue
      assertArm(cp.pc, retBindEq(funcApp, cp.env["result"]))
  if uncertainDrop:
    let bodyErr = SymexErrorInfo(kind: ceClosureBodyUncertain, severity: sevError,
      msg: "closure call through " & label &
           " body produced an uncertain sub-path (unmodeled-construct taint or " &
           "nested budget bail) — dropped from the ground-axiom set instead of " &
           "asserting an unsound permanent fact")
    currentClosureCallErrors.add bodyErr   # threadvar: fallback
    w.closureCallErrors.add bodyErr        # CR-9 Stage 5: LIVE WalkCtx field
    w.sawUnknown = true
  # ADR-0012: thread each exit path's defect-survivor facts onto the CALLER via
  # the exit-pc channel (drained by drainPendingLowerEffects). Each fact is
  # guarded by THAT path's branch conditions — `implies(branchConds_i, neg)` —
  # so a multi-arm body stays sound (the caller commits to "took arm i ⇒ arm i
  # didn't overflow"); for the common straight-line body branchConds is empty and
  # the fact is the bare negation. Collected over ALL exit paths (incl. void
  # fall-through) so a defect on a value-less path is not dropped. NEVER added to
  # currentClosureCallAxioms (global) — that would UNSAT the in-body raise path.
  var mergedDefectPc: seq[Z3Bool]
  proc addGuardedDefects(branchConds: openArray[Z3Bool], dnegs: seq[Z3Bool]) =
    if dnegs.len == 0: return
    if branchConds.len == 0:
      for d in dnegs: mergedDefectPc.add d
    else:
      var guard = branchConds[0]
      for k in 1 ..< branchConds.len: guard = guard and branchConds[k]
      for d in dnegs: mergedDefectPc.add guard.implies(d)
  for cp in frame.returnedPaths:                       # explicit: exclude retEq
    let bc = if cp.pc.len > 0: cp.pc[0 ..< cp.pc.high] else: cp.pc
    addGuardedDefects(bc, cp.defectSurvivorPc)
  for cp in fallThrough:                                # implicit/void: all pc
    addGuardedDefects(cp.pc, cp.defectSurvivorPc)
  for c in mergedDefectPc: currentClosureExitPc.add c
  # If the body produced NO value-bearing sub-path AND there are no output paths
  # at all (body diverged / was fully stubbed), mark uncertain so a target
  # reached through this result degrades to sxUnknown.
  # NOTE: void closures (no result, no explicit return) are NOT flagged unknown
  # here — they DO produce fallThrough paths (the body ran to completion without
  # a return value), which is the expected and sound behaviour for a void lambda.
  # The original `if not sawValue: sawUnknown = true` incorrectly caught all
  # void closures, collaterally degrading any UNSAT target after a void closure
  # call (see CR-1 companion fix for the sawUnknown/UNSAT interaction).
  if not sawValue and fallThrough.len == 0 and frame.returnedPaths.len == 0:
    w.sawUnknown = true
  # ---- Phase 15 CR-1: merge closure exit heaps back to caller ----------------
  # The exit paths from the closure body may carry heap modifications (e.g.
  # `p[] = 99` inside the body) that must be visible to the CALLER after the
  # call returns.  We merge these exit paths' heap state into the CR-1 exit
  # threadvars; `drainClosureExitHeap` in the enclosing `walk` arm applies them
  # to the survivor caller path (the same mechanism `seedCallerHeapThreadvars` +
  # `drainParseIntRaises` uses for the R1b entry-heap and S10b raises).
  #
  # Merge strategy mirrors the named-proc return-merge (isCall arm ~5443-5463):
  #   * heaps: REPLACEMENT — we take the exit heap directly (the caller's ENTIRE
  #     heap is replaced by the closure's, as for named procs).  For multiple
  #     exit paths we ITE-merge (branch_cond_i ? heap_i : else_heap) per type
  #     key; the single-exit-path case (most common: straight-line bodies) is a
  #     direct assignment with no Z3 ite overhead.
  #   * allocCounters: max-merge — post-closure caller `new T` must not collide
  #     with closure-allocated refs (same invariant as named-proc arm).
  #   * liveRefs: the closure exit's liveRefs is already the UNION of the seeded
  #     caller refs + any refs minted inside the body; replace directly.
  let exitPaths = fallThrough & frame.returnedPaths
  if exitPaths.len > 0:
    currentClosureDidMutateHeap = true   # threadvar fallback
    # Single-exit-path fast path (straight-line body, most common case).
    var mergedHeaps = exitPaths[0].heaps
    var mergedAlloc = exitPaths[0].allocCounters
    var mergedLiveRefs = exitPaths[0].liveRefs
    for i in 1 ..< exitPaths.len:
      # Multiple exit paths (branching inside the closure body): merge heaps
      # with Z3 ITE per type key so the caller sees the correct value on each
      # concrete execution path.  `exitPaths[i].pc` holds the accumulated
      # branch conditions for this sub-path; the ITE guard is their conjunction.
      let ePath = exitPaths[i]
      let ctx = w.z3
      if ePath.pc.len > 0:
        var guard = ePath.pc[0]
        for k in 1 ..< ePath.pc.len: guard = guard and ePath.pc[k]
        for tkey, exitHeap in ePath.heaps:
          let prevHeap = mergedHeaps.getOrDefault(tkey, exitHeap)
          let rawIte = ctx.checkErr Z3_mk_ite(ctx.raw,
                         guard.raw, exitHeap.raw, prevHeap.raw)
          mergedHeaps[tkey] = wrap[Z3AnyAst](ctx, rawIte)
      else:
        # Unconditional path (else branch of the last if / the only path):
        # this branch's heap dominates.
        for tkey, exitHeap in ePath.heaps:
          mergedHeaps[tkey] = exitHeap
      # max-merge allocCounters
      for tkey, cnt in ePath.allocCounters:
        if cnt > mergedAlloc.getOrDefault(tkey, 0):
          mergedAlloc[tkey] = cnt
      # re-review S-1: true set-union for liveRefs (dedup by raw AST identity).
      # The earlier "take longest list" heuristic silently dropped equal-length
      # arms (e.g. two exit paths each minting one new T), allowing a caller
      # new T to alias the dropped arm's ref. True set-union appends every ref
      # not already in the merged list (compared by raw Z3 AST pointer identity).
      for tkey, refs in ePath.liveRefs:
        var cur = mergedLiveRefs.getOrDefault(tkey, @[])
        for r in refs:
          var found = false
          for c in cur:
            if c.raw == r.raw: found = true; break
          if not found: cur.add r
        mergedLiveRefs[tkey] = cur
    # Dual-write: threadvar (fallback) + WalkCtx fields (LIVE store).
    # CR-9 Stage 6 Group-4: `w` is always available here (applyClosureGround
    # has `w: var WalkCtx` from the walk-descent call above).
    currentClosureExitHeaps = mergedHeaps              # threadvar fallback
    currentClosureExitAllocCounters = mergedAlloc      # threadvar fallback
    currentClosureExitLiveRefs = mergedLiveRefs        # threadvar fallback
    w.closureDidMutateHeap = true                      # CR-9 Stage 6 Group-4
    w.closureExitHeaps = mergedHeaps                   # CR-9 Stage 6 Group-4
    w.closureExitAllocCounters = mergedAlloc           # CR-9 Stage 6 Group-4
    w.closureExitLiveRefs = mergedLiveRefs             # CR-9 Stage 6 Group-4
  funcApp

# ---- Phase 15 C4: DSL higher-order functions over seq[T] --------------------

proc seqElemAt(seqSV: SymVal, idx: Z3Int): SymVal =
  ## Read element `idx` of a `svSeq` as a SymVal (dispatch on element type).
  ## Mirrors the `isIndex`/seq walker arm. Caller guarantees `idx` in bounds.
  doAssert seqSV.kind == svSeq, "seqElemAt: not an svSeq"
  case seqSV.seqElemTy.kind
  of itInt:
    case seqSV.seqElemTy.width
    of 8:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[8]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 16:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[16]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 32:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[32]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 64:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[64]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    else:
      raise newException(ValueError, "seqElemAt: unsupported int width " & $seqSV.seqElemTy.width)
  of itBool:
    let t = wrap[Z3Array[Z3Int, Z3Bool]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
    ofBool(select(t, idx))
  of itFloat32:
    let t = wrap[Z3Array[Z3Int, Z3Float32]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
    SymVal(kind: svFloat32, fp32: select(t, idx))
  of itFloat64:
    let t = wrap[Z3Array[Z3Int, Z3Float64]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
    SymVal(kind: svFloat64, fp64: select(t, idx))
  of itString:
    let t = wrap[Z3Array[Z3Int, Z3String]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
    SymVal(kind: svString, str: select(t, idx))
  else:
    raise newException(ValueError, "seqElemAt: unsupported elem kind " & $seqSV.seqElemTy.kind)

proc storeSeqElem(dataRaw: Z3AnyAst, elemTy: IRType, idx: Z3Int,
                  val: SymVal): Z3AnyAst =
  ## Store `val` at index `idx` in the (erased) seq data array, returning the
  ## new erased array. Mirrors the `iekSeqAdd` store dispatch.
  case elemTy.kind
  of itInt:
    case elemTy.width
    of 8:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[8]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, val.bv8))
    of 16:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[16]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, val.bv16))
    of 32:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[32]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, val.bv32))
    of 64:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[64]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, val.bv64))
    else:
      raise newException(ValueError, "storeSeqElem: unsupported int width " & $elemTy.width)
  of itBool:
    let t = wrap[Z3Array[Z3Int, Z3Bool]](dataRaw.ctx, dataRaw.raw)
    toAnyAst(store(t, idx, val.bo))
  of itFloat32:
    let t = wrap[Z3Array[Z3Int, Z3Float32]](dataRaw.ctx, dataRaw.raw)
    toAnyAst(store(t, idx, val.fp32))
  of itFloat64:
    let t = wrap[Z3Array[Z3Int, Z3Float64]](dataRaw.ctx, dataRaw.raw)
    toAnyAst(store(t, idx, val.fp64))
  of itString:
    let t = wrap[Z3Array[Z3Int, Z3String]](dataRaw.ctx, dataRaw.raw)
    toAnyAst(store(t, idx, val.str))
  of itRef, itPtr:   ## Cluster H H_containers (ADR-0022): seq[Node] LITERAL
    # construction (`@[a, b]`) for a named `ref object` element. The backing
    # array is the raw `Z3Array[Z3Int, Ref_T]` `allocateSeqDataRaw` already
    # allocates for itRef/itPtr elements (built for Phase 15 R3's inline-ref
    # seqs) — this was the missing STORE half. `Ref_T` is a RUNTIME
    # uninterpreted sort the typed `store` helper can't express, so this
    # stores via raw `Z3_mk_store` (mirrors the `isIndex/seq` read-path's raw
    # `Z3_mk_select`, runtime.nim's itRef/itPtr arm above ~5410). GROUND
    # store; no quantifier.
    let ctx = dataRaw.ctx
    let valAst = case val.kind
      of svRef: val.refAst
      of svPtr: val.ptrAst
      else:
        raise newException(ValueError,
          "storeSeqElem(itRef/itPtr): val is not svRef/svPtr, kind=" & $val.kind)
    let storedRaw = ctx.checkErr Z3_mk_store(ctx.raw, dataRaw.raw, idx.raw, valAst.raw)
    wrap[Z3AnyAst](ctx, storedRaw)
  else:
    raise newException(ValueError, "storeSeqElem: unsupported elem kind " & $elemTy.kind)

proc lowerSeqLit(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C4. `@[a, b, c]` → a CONCRETE-length svSeq: a fresh data array
  ## with each lowered element stored at its index, and `seqLen` pinned to the
  ## literal count (a numeral). Empty `@[]` → length-0 svSeq.
  ##
  ## Round-6 B6 rider: the EMPTY literal (`e.seqLitElems.len == 0`) skips
  ## `allocateSeqDataRaw` entirely and uses an inert placeholder array
  ## instead — sound for ANY `elemTy`, INCLUDING kinds `allocateSeqDataRaw`
  ## does not support (e.g. `itTuple`, the `seq[(string,string)]` gap this
  ## rider was written to unblock: `var pairs: seq[(string,string)] = @[]`,
  ## chapulin's own `readOptions` accumulator declaration). A length-0 seq
  ## has no valid index — `isIndex`'s `0 <= idx < seqLen` bound is
  ## unsatisfiable for every idx, so the OOB/IndexDefect fork is the ONLY
  ## surviving path and `seqDataRaw`'s actual content is NEVER read on any
  ## live path — a placeholder is exact, not an approximation. This does
  ## NOT touch `allocateSym`'s itSeq arm (fresh/symbolic-length seqs, where
  ## a genuinely-reachable index needs REAL element content) — declining
  ## classified there is unchanged; only the ALREADY-KNOWN-EMPTY literal
  ## case, which needs no element representation at all, is widened.
  let elemTy = e.seqLitElemTy
  var dataRaw =
    if e.seqLitElems.len == 0:
      toAnyAst(mkArrayVar[Z3Int, Z3Bool]("__seqlit.emptyPlaceholder"))
    else:
      allocateSeqDataRaw(elemTy, "__seqlit.data")
  for i, ce in e.seqLitElems:
    let elemSV = lower(env, ce)
    dataRaw = storeSeqElem(dataRaw, elemTy, mkInt(i), elemSV)
  SymVal(kind: svSeq, seqLen: mkInt(e.seqLitElems.len),
         seqDataRaw: dataRaw, seqElemTy: elemTy)

proc lowerTupleLit(env: Env, e: IRExpr): SymVal =
  ## RFC-chapulin-hardening P1. `(a, b, c)` → svTuple. Unlike `lowerSeqLit`
  ## (one uniform `elemTy` for every element — Nim requires seq homogeneity),
  ## tuple fields may be HETEROGENEOUS, so each element is lowered with its
  ## OWN per-field prototype derived from `e.ttupleTy.fields[i]` (mirrors
  ## `iekArrayLit`'s protoSV construction, just per-field instead of once) —
  ## this matters so a bare int-literal field (e.g. `(x, 5'u8)`) lowers at
  ## its DECLARED width/signedness rather than defaulting to signed BV64
  ## (`lower`'s `iekIntLit` arm with no proto).
  var fields: seq[SymVal]
  for i, ce in e.telems:
    var protoSV: Option[SymVal] = none(SymVal)
    if i < e.ttupleTy.fields.len:
      let fty = e.ttupleTy.fields[i]
      if fty.kind == itInt:
        protoSV = some(bvConst(fty, 0))
      elif fty.kind == itBool:
        protoSV = some(ofBool(mkBool(false)))
    fields.add lower(env, ce, protoSV)
  SymVal(kind: svTuple, fields: fields, fieldNames: e.ttupleTy.fieldNames)

proc lowerVariantLit(env: Env, e: IRExpr): SymVal =
  ## Round-6 A1 (ADR-0029). `T(kind: tagLit, f1: e1, ...)` → svVariant.
  ## Mirrors `allocateSym(itVariant)`'s shape (disc + per-arm fields +
  ## plain fields) with two deliberate divergences: the discriminator is a
  ## Z3 CONST pinned to the literal tag (`bvConst`, not a fresh symbol with
  ## a disjunction constraint — `vDiscTy` is always `itInt`, per its own
  ## doc comment, so `bvConst` covers every legal disc shape), and the
  ## ACTIVE arm's fields are the LOWERED constructor exprs rather than
  ## fresh allocations.
  ##
  ## Every OTHER arm allocates FRESH-UNCONSTRAINED fields (never zero) —
  ## the ADR's soundness note: real Nim raises `FieldDefect` on an
  ## out-of-arm read before any value is observable, so a zero-filled
  ## inactive field would let a buggy twin "read" a value real Nim never
  ## yields. The fresh allocation's own `pcOut` is intentionally a LOCAL,
  ## discarded scratch — mirrors the existing `__refVariantWitness`
  ## proto-allocation precedent (`extractFromSymVal`'s `itVariant` arm,
  ## above) for the identical reason: an inactive arm's fields are only
  ## ever reachable through `isVariantField`'s fork, whose out-of-arm side
  ## is exactly the `FieldDefect` raise — no live SAT path ever reads a
  ## fresh inactive field's value, so no pc constraint on it could ever
  ## affect a reachable verdict.
  let ty = e.vlVariantTy
  let discBoxed = new(SymVal)
  discBoxed[] = bvConst(ty.vDiscTy, int64(e.vlTagOrd))
  var plainFields: seq[SymVal]
  for fe in e.vlPlainFields:
    plainFields.add lower(env, fe)
  var armFields = initOrderedTable[int, seq[SymVal]]()
  var armNames  = initOrderedTable[int, seq[string]]()
  for arm in ty.vArms:
    armNames[arm.tagOrdinal] = arm.fieldNames
    if arm.tagOrdinal == e.vlTagOrd:
      var fields: seq[SymVal]
      for fe in e.vlArmFields:
        fields.add lower(env, fe)
      armFields[arm.tagOrdinal] = fields
    else:
      var fields: seq[SymVal]
      for j, ft in arm.fieldTypes:
        inc variantLitFreshCounter
        let path = "__variantLit." & ty.vObjectName & ".@" & arm.tagName &
                   "." & arm.fieldNames[j] & "." & $variantLitFreshCounter
        var scratchPC: seq[Z3Bool]
        fields.add allocateSym(ft, path, scratchPC)
      armFields[arm.tagOrdinal] = fields
  SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: ty.vDiscName,
         vObjectName: ty.vObjectName, vArmFields: armFields,
         vArmFieldNames: armNames, vPlainFields: plainFields,
         vPlainFieldNames: ty.vPlainFieldNames)

proc concreteSeqLen(seqSV: SymVal): Option[int] =
  ## Phase 15 C4. If the seq's length folds (via `simplify`) to a Z3 numeral,
  ## return its concrete value; otherwise `none`. `iekSeqAdd` produces a length
  ## like `0 + 1 + 1` that is NOT a bare numeral until simplified, so we
  ## `simplify` first (decidable, cheap) before inspecting the AST kind.
  let folded = simplify(seqSV.seqLen)
  if getAstKind(folded) == akNumeral:
    try: some(parseInt(getNumeralString(folded)))
    except CatchableError: none(int)
  else:
    none(int)

proc lowerHofCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C4 (ADR-0009). DSL higher-order call `filter`/`map`/`fold` over a
  ## `seq[T]` with a closure arg. INLINE path (concrete length ≤
  ## seqInlineThreshold under a permitting `inlinePolicy`): unroll the closure
  ## per element (quantifier-free). AXIOM path (symbolic length): `map` →
  ## `mapArray` (decidable array-map, NO universal-∀); `fold` → raw `Z3_mk_app`;
  ## `filter` → `ceUnsupportedHof` (Phase-16 deferred). Bounded by
  ## seqInlineThreshold (≤ 8) — no combinatorial fan-out.
  let ctx = requireCurrentContext()
  let seqSV = lower(env, e.hofSeq)
  doAssert seqSV.kind == svSeq, "lowerHofCall: receiver is not an svSeq"
  # Build the closure value (svClosure) from the lambda arg (C2a construction:
  # snapshots captures, stashes the body, declares the per-site funcSym).
  let cloSV = lower(env, e.hofClosure)
  doAssert cloSV.kind == svClosure, "lowerHofCall: closure arg is not an svClosure"

  # Settings (via the live WalkCtx, mirroring lowerClosureCall).
  var policy = ipHybrid
  var threshold = 8
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    policy    = wp[].settings.inlinePolicy
    threshold = wp[].settings.budget.seqInlineThreshold

  let lenOpt = concreteSeqLen(seqSV)
  # Decide inline vs axiom. ipAlwaysInline forces inline (requires concrete
  # length to be sound; a symbolic length under ipAlwaysInline degrades to the
  # axiom path with a warning, since we cannot unroll an unknown count).
  let canInline =
    lenOpt.isSome and
    (policy == ipAlwaysInline or
     (policy == ipHybrid and lenOpt.get <= threshold))

  if canInline:
    let n = lenOpt.get
    case e.hofOp
    of "map":
      # Result svSeq of element type hofRetElemTy; elem i = mapper(elem i).
      var dataRaw = allocateSeqDataRaw(e.hofRetElemTy, "__hofmap.data")
      for i in 0 ..< n:
        let elemSV = seqElemAt(seqSV, mkInt(i))
        let mapped = applyClosureGround(cloSV, @[elemSV], "map@" & $i)
        dataRaw = storeSeqElem(dataRaw, e.hofRetElemTy, mkInt(i), mapped)
      SymVal(kind: svSeq, seqLen: mkInt(n),
             seqDataRaw: dataRaw, seqElemTy: e.hofRetElemTy)
    of "filter":
      # Result svSeq: pack kept elements (predicate true) into running compacted
      # indices. result length = sum ite(pred_i, 1, 0); for each i, if pred_i,
      # store elem_i at the current kept count. Bounded, quantifier-free.
      let elemTy = e.hofRetElemTy   ## filter preserves element type
      var dataRaw = allocateSeqDataRaw(elemTy, "__hoffilter.data")
      var keptLen: Z3Int = mkInt(0)
      for i in 0 ..< n:
        let elemSV = seqElemAt(seqSV, mkInt(i))
        let predSV = applyClosureGround(cloSV, @[elemSV], "filter@" & $i)
        doAssert predSV.kind == svBool, "filter predicate did not return Bool"
        # Store elem_i at the CURRENT kept index. Stores past the final kept
        # length are never observed (reads are len-bounded), so an
        # unconditional store at `keptLen` is sound.
        dataRaw = storeSeqElem(dataRaw, elemTy, keptLen, elemSV)
        keptLen = keptLen + ite(predSV.bo, mkInt(1), mkInt(0))
      SymVal(kind: svSeq, seqLen: simplify(keptLen),
             seqDataRaw: dataRaw, seqElemTy: elemTy)
    of "fold":
      # Left-fold: acc = folder(acc, elem_i), from the init accumulator.
      doAssert e.hofInit != nil, "fold inline path requires an init accumulator"
      var acc = lower(env, e.hofInit)
      for i in 0 ..< n:
        let elemSV = seqElemAt(seqSV, mkInt(i))
        acc = applyClosureGround(cloSV, @[acc, elemSV], "fold@" & $i)
      acc
    else:
      raise newException(ValueError, "lowerHofCall: unknown HOF op " & e.hofOp)
  else:
    # ---- AXIOM path (symbolic length, or concrete length above threshold). ----
    case e.hofOp
    of "filter":
      # DEFERRED to Phase 16 — no Z3 seqFilter HOF; a quantified filter
      # predicate over a symbolic-length seq is a hang risk. Classify (sevError
      # → sxUnknown) and return a fresh seq so a downstream read does not crash.
      let filterErr = SymexErrorInfo(kind: ceUnsupportedHof, severity: sevError,
        msg: "filter over a symbolic-length seq is not supported (no Z3 " &
             "seqFilter HOF; axiomatize-filter deferred to Phase 16)")
      currentClosureCallErrors.add filterErr  # threadvar: fallback
      syncClosureCallError(filterErr)         # CR-9 Stage 5: LIVE WalkCtx field
      if currentWalkCtxPtr != nil:
        cast[ptr WalkCtx](currentWalkCtxPtr)[].sawUnknown = true
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(e.hofRetElemTy), "__hofFilterUnsupported", fresh)
    of "map":
      # Axiom path: `mapArray` (Z3_mk_map) — pointwise application of the
      # closure funcSym over the seq's data array. DECIDABLE array-map (no
      # universal quantifier; no G4-style hang). Result is a new seq with the
      # SAME (symbolic) length and a data array `r[i] = f(a[i])`.
      # CR-9 Stage 4: read closureBodies from live WalkerStatics when in a walk.
      let hofSiteKey = (cloSV.closureSite.siteHash, cloSV.closureSite.declOrder)
      let hofBodiesLive =
        if currentWalkCtxPtr != nil:
          cast[ptr WalkCtx](currentWalkCtxPtr)[].statics.closureBodies
        else:
          currentClosureBodies
      let cb = hofBodiesLive[hofSiteKey]
      # Build a typed unary func_decl from the per-site funcSym. For the axiom
      # map the closure must be capture-free (unit-env) so its funcSym arity is
      # exactly 1 (the element); a captured closure has env-leaf domain args and
      # cannot be a unary array-map function — classify that case.
      var envLeaves = 0
      if cloSV.closureEnv != nil:
        for _ in flattenLeafAsts(cloSV.closureEnv[]): inc envLeaves
      if envLeaves != 0 or e.hofRetElemTy.kind != itInt or
         seqSV.seqElemTy.kind != itInt:
        # Capturing closure or non-int element: the unary-funcdecl array-map
        # shape does not apply. Classify rather than risk an unsound/hang path.
        let mapErr = SymexErrorInfo(kind: ceUnsupportedHof, severity: sevError,
          msg: "map axiom path supports only a capture-free int->int closure " &
               "over a symbolic seq[int]; this shape is deferred")
        currentClosureCallErrors.add mapErr   # threadvar: fallback
        syncClosureCallError(mapErr)          # CR-9 Stage 5: LIVE WalkCtx field
        if currentWalkCtxPtr != nil:
          cast[ptr WalkCtx](currentWalkCtxPtr)[].sawUnknown = true
        var fresh: seq[Z3Bool]
        return allocateSym(tSeq(e.hofRetElemTy), "__hofMapUnsupported", fresh)
      # mapArray over Z3Array[Z3Int, BV64] using the unary funcSym.
      let fd = Z3FuncDecl[(Z3BitVec[64],), Z3BitVec[64]](
        raw: cloSV.closureRawFD, ctx: ctx)
      let srcArr = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
        seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw)
      let mappedArr = mapArray[Z3Int, Z3BitVec[64], Z3BitVec[64]](fd, srcArr)
      discard cb   ## body already stashed; ground axioms still constrain f
      SymVal(kind: svSeq, seqLen: seqSV.seqLen,
             seqDataRaw: toAnyAst(mappedArr), seqElemTy: e.hofRetElemTy)
    of "fold":
      # Axiom path: a raw `Z3_mk_app` of an uninterpreted fold result over the
      # seq's length + data + init (ground, C2b discipline — never a ∀ axiom).
      # The result is an uninterpreted value of the accumulator type; its
      # relation to the elements is left opaque (sound over-approximation —
      # degrades the verdict, never a false sat/unsat).
      let foldErr = SymexErrorInfo(kind: ceUnsupportedHof, severity: sevError,
        msg: "fold over a symbolic-length seq is modeled as an opaque " &
             "ground result (precise symbolic fold deferred)")
      currentClosureCallErrors.add foldErr  # threadvar: fallback
      syncClosureCallError(foldErr)         # CR-9 Stage 5: LIVE WalkCtx field
      if currentWalkCtxPtr != nil:
        cast[ptr WalkCtx](currentWalkCtxPtr)[].sawUnknown = true
      var fresh: seq[Z3Bool]
      return allocateSym(e.hofRetElemTy, "__hofFoldOpaque", fresh)
    else:
      raise newException(ValueError, "lowerHofCall: unknown HOF op " & e.hofOp)

# ---- Public driver ----------------------------------------------------------

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings): RawResult

when defined(windows) and not defined(symexNoBigStack):
  # Chapulin 0.1.0 re-test triage (catalog #11, CRASH class), walker v64.
  # The walker's recursive lowering + Z3's recursive rewriters are
  # stack-hungry, and a Windows main thread defaults to a 1 MB (MSVC) /
  # 2 MB (MinGW) stack vs 8 MB on Linux — chapulin's depth-2/3 nested-if
  # string twins overflowed and died as a BARE SILENT EXIT (empirically
  # exit code 255 in the toolchain container; the classic 0xC00000FD
  # never surfaces through the CRT), while the identical shapes prove
  # sxUnsat under a 16 MB stack. Fix: execute the whole solve on a FIBER
  # with an explicitly reserved 16 MB stack.
  #
  # A fiber — NOT a thread — is deliberate: a fiber shares the creating
  # thread's identity and TLS, so every threadvar sink the walker relies
  # on (`loweringDegradeErrors`, `extractionErrors`, `currentWalkCtxPtr`,
  # …) stays coherent with zero re-plumbing, and ORC needs no
  # foreign-thread setup (ARC/ORC never scans stacks). Nim's own
  # `createThread` is no alternative: its stack size is the FIXED
  # `ThreadStackMask`-derived ~2 MB on desktop targets — the
  # `-d:nimThreadStackSize` define only applies to embedded targets.
  #
  # Exceptions cannot unwind across `SwitchToFiber`, so the trampoline
  # catches EVERYTHING (including Defect — nothing may escape on a dead
  # fiber) and re-raises on the main fiber, where `runSymex`'s existing
  # arms observe the original dynamic type unchanged.
  #
  # Escape hatch: compile with `-d:symexNoBigStack` to run the solve
  # directly on the calling thread's stack (pre-v64 behaviour).
  type FiberSolveCtx = object
    prog: SymexProgram
    target: SymexTarget
    settings: SymexSettings
    res: RawResult
    exn: ref Exception
    mainFiber: pointer

  const symexFiberStackReserve = 16 * 1024 * 1024
  const symexFiberStackCommit  = 256 * 1024

  proc convertThreadToFiber(param: pointer): pointer
    {.importc: "ConvertThreadToFiber", stdcall, dynlib: "kernel32".}
  proc convertFiberToThread(): int32
    {.importc: "ConvertFiberToThread", stdcall, dynlib: "kernel32".}
  proc createFiberEx(stackCommit, stackReserve: csize_t, flags: uint32,
                     startAddr, param: pointer): pointer
    {.importc: "CreateFiberEx", stdcall, dynlib: "kernel32".}
  proc deleteFiber(f: pointer)
    {.importc: "DeleteFiber", stdcall, dynlib: "kernel32".}
  proc switchToFiber(f: pointer)
    {.importc: "SwitchToFiber", stdcall, dynlib: "kernel32".}

  proc fiberTrampoline(param: pointer) {.stdcall.} =
    when defined(symexFiberTrace): stderr.writeLine "[fiber] trampoline enter"
    let ctx = cast[ptr FiberSolveCtx](param)
    try:
      ctx.res = runSymexImpl(ctx.prog, ctx.target, ctx.settings)
      when defined(symexFiberTrace): stderr.writeLine "[fiber] impl returned"
    except Exception as e:
      ctx.exn = e
      when defined(symexFiberTrace): stderr.writeLine "[fiber] impl raised " & e.msg
    switchToFiber(ctx.mainFiber)
    # Never reached: the fiber is deleted by the main fiber after the switch.

  proc runSymexWithBigStack(prog: SymexProgram, target: SymexTarget,
                            settings: SymexSettings): RawResult =
    # ConvertThreadToFiber returns nil if the thread is ALREADY a fiber (or
    # on failure) — degrade gracefully to a direct call on the current stack
    # (the pre-v64 behaviour) rather than failing the run outright.
    let mainFiber = convertThreadToFiber(nil)
    when defined(symexFiberTrace):
      stderr.writeLine "[fiber] converted mainFiber nil=" & $(mainFiber == nil)
    if mainFiber == nil:
      return runSymexImpl(prog, target, settings)
    var ctx = FiberSolveCtx(prog: prog, target: target, settings: settings,
                            mainFiber: mainFiber)
    # FIBER_FLAG_FLOAT_SWITCH (1): float-state switching — a no-op on x64,
    # required for correctness on x86.
    let fib = createFiberEx(csize_t(symexFiberStackCommit),
                            csize_t(symexFiberStackReserve), 1,
                            cast[pointer](fiberTrampoline), addr ctx)
    when defined(symexFiberTrace):
      stderr.writeLine "[fiber] created nil=" & $(fib == nil)
    if fib == nil:
      discard convertFiberToThread()
      return runSymexImpl(prog, target, settings)
    # Debug-build frame-chain hygiene: Nim's `--stackTrace` machinery links
    # stack-ALLOCATED `TFrame` records through a threadvar chain
    # (`framePtr`), and the trampoline never RETURNS through its Nim
    # epilogue (it switches back and is then deleted) — so its frame would
    # stay linked, pointing into the FREED fiber stack, and the next frame
    # operation on the main fiber would deref freed memory (observed as the
    # same silent 0xFF death this whole fix exists to cure). Save/restore
    # the frame state around the switch — the exact idiom Nim's own
    # coroutines used. No-op in release builds (procs still exist; the
    # chain is simply empty).
    when declared(getFrameState) and declared(setFrameState):
      let savedFrames = getFrameState()
    switchToFiber(fib)
    when declared(getFrameState) and declared(setFrameState):
      setFrameState(savedFrames)
    when defined(symexFiberTrace): stderr.writeLine "[fiber] back on main"
    deleteFiber(fib)
    discard convertFiberToThread()
    if ctx.exn != nil:
      raise ctx.exn
    ctx.res

proc runSymex*(prog: SymexProgram,
               target: SymexTarget,
               settings: SymexSettings = defaultSymexSettings()): RawResult =
  ## Phase 14 cycle C4. Wrap the implementation in a `try/except` that
  ## catches `Z3Error` (the abstract base class — all 12 typed
  ## subclasses derive from it). On catch, return `sxUnknown` with
  ## the error structured into `errors`. Walker-level
  ## `ValueError` and `AssertionDefect` are NOT caught — those
  ## are real bugs in the symex layer and must surface.
  try:
    # v64 (catalog #11): on Windows the solve runs on a 16 MB fiber stack —
    # the fiber trampoline re-raises any escaped exception HERE on the main
    # fiber with its dynamic type intact, so the arms below are unaffected.
    when declared(runSymexWithBigStack):
      runSymexWithBigStack(prog, target, settings)
    else:
      runSymexImpl(prog, target, settings)
  except SymexUnsupportedOpError as e:
    # Phase 15 F6: an unmodeled float op (classify/copySign/nextafter/any
    # unmodeled math.<name>) -> sxUnknown + feUnsupportedOp (Invariant 3:
    # a classified error, never a silent UNSAT). The op name rides in `msg`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: feUnsupportedOp,
                                       severity: sevError, msg: e.msg)])
  except SymexUnsupportedStringOpError as e:
    # Phase 15 Cluster S (S1): an unmodeled string op (in S1, every iekStr*) ->
    # sxUnknown + seUnsupportedStringOp (Invariant 3 — classified, never silent
    # UNSAT). The surface op name rides in `msg`. S2–S11 narrow this as each op
    # gains a real lowering.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedStringOp,
                                       severity: sevError, msg: e.msg)])
  except SymexUnsupportedRegexError as e:
    # Phase 15 S6b: a `re"…"` pattern S6a rejects (backreference / lookahead /
    # named group / malformed) or a regex `find` (no Z3 indexOf/regex API) ->
    # sxUnknown + seUnsupportedRegex (Invariant 3 — classified, never silent
    # UNSAT). The S6a reason rides in `msg`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedRegex,
                                       severity: sevError, msg: e.msg)])
  except SymexZ3VersionMissingError as e:
    # Phase 15 S5: a string op whose Z3 FFI symbol is absent on this build
    # (e.g. replaceAll on Z3 < 4.15.5) -> sxUnknown + seZ3VersionMissing
    # (Invariant 3 — classified, never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seZ3VersionMissing,
                                       severity: sevError, msg: e.msg)])
  except SymexZ3StringIncompleteError as e:
    # Phase 15 S5: a string-theory decomposition the walker cannot soundly
    # bound (the general symbolic-split path) -> sxUnknown + seZ3StringIncomplete
    # (Invariant 3 — structured, never a hang).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seZ3StringIncomplete,
                                       severity: sevError, msg: e.msg)])
  except SymexBytesSymbolicLengthError as e:
    # Phase 15 S7a: `bytes(s)` over a symbolic-length receiver -> sxUnknown +
    # seBytesSymbolicLength (Invariant 3 — classified, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seBytesSymbolicLength,
                                       severity: sevError, msg: e.msg)])
  except SymexBytesLengthTooLargeError as e:
    # Phase 15 S7a: `bytes(s)` concrete length > maxBytesEncodingLen -> sxUnknown
    # + seBytesLengthTooLarge (Invariant 3 — classified, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seBytesLengthTooLarge,
                                       severity: sevError, msg: e.msg)])
  except SymexRaiseUnimplementedError as e:
    # Phase 15 E1: the walker reached an `isRaise` while raise-flow is not yet
    # modeled (structural cycle) -> sxUnknown + eeRaiseUnimplemented (Invariant 3
    # — classified, never a silent UNSAT). E2b+ replaces this with real semantics.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: eeRaiseUnimplemented,
                                       severity: sevError, msg: e.msg)])
  except SymexTryUnimplementedError as e:
    # Phase 15 E1: the walker reached an `isTry` while try/except is not yet
    # modeled -> sxUnknown + eeTryUnimplemented (Invariant 3). E3+ replaces it.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: eeTryUnimplemented,
                                       severity: sevError, msg: e.msg)])
  except SymexClosureUnimplementedError as e:
    # Phase 15 C1: the walker reached an `iekLambda`/`iekClosureCall` while
    # closure semantics are not yet modeled (structural cycle) -> sxUnknown +
    # ceNotImplemented (Invariant 3 — classified, never a silent UNSAT). C2a
    # (construction) / C2b (application) replace this with real semantics.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: ceNotImplemented,
                                       severity: sevError, msg: e.msg)])
  except SymexRaiseOutsideHandlerError as e:
    # Phase 15 E2b: a bare `raise` (re-raise) reached with an empty handler stack
    # and no in-flight exception -> sxUnknown + eeRaiseOutsideHandler (Invariant 3
    # — classified, never a silent UNSAT). Handler-stack re-raise lands E3.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: eeRaiseOutsideHandler,
                                       severity: sevError, msg: e.msg)])
  except SymexNotInHandlerError as e:
    # Phase 15 E8: `getCurrentException()` / `getCurrentExceptionMsg()` called
    # outside any `except` handler body (no in-flight exception) -> sxUnknown +
    # eeNotInHandler (Invariant 3 — classified, never a panic). The intrinsic
    # name rides in `msg`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: eeNotInHandler,
                                       severity: sevError, msg: e.msg)])
  except SymexRefUnresolvedError as e:
    # Phase 15 R1a (ADR-0010): the walker reached an `itRef`/`itPtr`/`isDeref`/
    # `isNew` while the logical-heap semantics are not yet modeled (structural
    # cycle) -> sxUnknown + heUnresolvedRef (Invariant 3 — classified, never a
    # silent UNSAT, never a crash). R1+ replace the stub with real heap
    # semantics. The diagnostic rides in `msg`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: heUnresolvedRef,
                                       severity: sevError, msg: e.msg)])
  except SymexRefVariantUnsupportedError as e:
    # Phase 15 R6 (ADR-0010, Feas-MED-4 / M17): a field access through a ref/ptr
    # to a VARIANT object -> sxUnknown + heRefVariantUnsupported (Invariant 3 —
    # classified, never a Defect on svTuple dispatch, never a silent UNSAT). The
    # field-split heap has no flat positional layout to split a variant on.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: heRefVariantUnsupported,
                                       severity: sevError, msg: e.msg)])
  except SymexOwnershipUnsupportedError as e:
    # Phase 15 R1a (ADR-0010, Breadth-LOW-L4): an `owned T` / `WeakRef[T]` /
    # `Atomic[T]` formal was allocated -> sxUnknown + heUnsupportedOwnership
    # (Invariant 3 — classified, out of scope for the cluster).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: heUnsupportedOwnership,
                                       severity: sevError, msg: e.msg)])
  except SymexNestedSeqUnsupportedError as e:
    # Phase 16 INV: `seq[seq[T]]` / complex-element seq — nested-seq encoding
    # not modeled -> sxUnknown + seNestedSeqUnsupported (Invariant 3 — classified,
    # never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seNestedSeqUnsupported,
                                       severity: sevError, msg: e.msg)])
  except SymexUnsupportedTableValTypeError as e:
    # Phase 16 INV: Table value type not modeled (only Table[string, int] supported)
    # -> sxUnknown + seUnsupportedTableValType (Invariant 3 — classified,
    # never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedTableValType,
                                       severity: sevError, msg: e.msg)])
  except SymexUnsupportedSetCharInteropError as e:
    # Phase 16 INV: set[char] / HashSet element type not modeled (only HashSet[int]
    # BV[64] is supported) -> sxUnknown + seUnsupportedSetCharInterop (Invariant 3
    # — classified, never a crash, never a silent UNSAT).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: seUnsupportedSetCharInterop,
                                       severity: sevError, msg: e.msg)])
  except SymexClassifiedDegradeError as e:
    # Phase 16 CR-1c (ADR-0020): the single generic classified-degrade carrier's
    # `kind` rides through verbatim -> sxUnknown (Invariant 3). This arm handles
    # any code that DELIBERATELY raises a pre-classified degrade (CR-2b reuses
    # this carrier with its own `kind`). CR-1c's own genuinely-unanticipated
    # native fault does NOT flow here — it is caught by the final `except
    # CatchableError` catch-all below and classified `weInternalWalkerFault`.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: e.kind,
                                       severity: sevError, msg: e.msg)])
  except Z3Error as e:
    # Phase 15 Z3: map the Z3Error subclass name to the closed SymexErrorKind.
    # A caught Z3Error -> sxUnknown, so severity is sevError (invariant 7).
    let ek = case $e.name
             of "Z3MemoryError":   ekZ3MemoryError
             of "Z3InternalError": ekZ3InternalError
             of "Z3SolverError":   ekZ3SolverError
             else:                 ekZ3Error
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: ek, severity: sevError, msg: e.msg)])
  except CatchableError as e:
    # Phase 16 CR-1c (RFC-chapulin-hardening, Cluster 2 — Crash-totality,
    # ADR-0020): the genuine last-resort SAFETY NET for the §0 "walker never
    # crashes" invariant. This arm is REACHED ONLY by a `CatchableError` that
    # matched NONE of the specific arms above — i.e. NEITHER one of the 18 known
    # construct-gap `Symex*Error` carriers, NOR `SymexClassifiedDegradeError`,
    # NOR `Z3Error`. By construction that is a genuinely UNANTICIPATED native
    # exception (a stray `KeyError`/`ValueError`/etc.) that escaped the walker
    # from ANY dispatch depth — a walker bug, not an unmodeled SUT construct.
    #
    # It is classified with the DISTINCT `weInternalWalkerFault` kind, NEVER
    # conflated with the ordinary `se*`/`fe*` construct-gap kinds, so CI/
    # telemetry can track "how often we hit the safety net" as a live walker-bug
    # backlog (§0: totality is an audit, not a silently-closed invariant).
    #
    # WHY here (the outermost, pre-existing `try`) and NOT a per-`walk`-frame
    # catch: a `try/except` wrapped around the recursive per-statement dispatch
    # catches-and-re-raises the ANTICIPATED carriers at EVERY frame; on Nim's C
    # backend (ORC + goto exceptions) that repeated catch/re-raise, interacting
    # with the ORC destructor unwind of `walkBlock`'s live `seq[Path]` result
    # (whose `Path` fields hold refcounted Z3 ASTs), corrupted memory into a nil
    # read — a C-backend-only SIGSEGV, invisible on C++ (the same backend-
    # divergence class as the b7258f7 `try/finally` precedent). Placing the ONE
    # catch on the ALREADY-EXISTING `runSymex` try lets an unanticipated native
    # unwind straight through the walk exactly as it did pre-CR-1c (which was
    # sound), while the anticipated carriers are consumed by their specific arms
    # ABOVE and never reach this catch-all. `try/except`, NEVER `try/finally`
    # (b7258f7 hard rule).
    #
    # `Defect`-class raises (the ~63 `doAssert`s and any stray `IndexDefect`/
    # `RangeDefect`/`AssertionDefect`) are NOT `CatchableError` and are NOT
    # caught here — they keep crashing loudly per the §0 crash-doctrine.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: weInternalWalkerFault,
                                       severity: sevError,
                                       msg: $e.name & ": " & e.msg)])
  except Defect as e:
    # Round-3 crash-doctrine decision (Corey, 2026-08-06 — supersedes the
    # CR-1c "Defects keep crashing loudly" carve-out for CONSUMER-facing
    # totality): with 0.1.0 shipped and chapulin consuming, the ~63
    # doAssert-class internal-invariant failures no longer take down the
    # consumer's process. This ONE outermost arm classifies them
    # `weInternalWalkerFault` — the same telemetry contract as the
    # CatchableError net above: "the walker itself hit a bug here", a live
    # walker-bug backlog kind never conflated with construct gaps. The
    # C-backend corruption hazard that forbade per-frame catching (ADR-0020)
    # does not apply at this locus: the unwind passes through the walk
    # exactly as it did pre-net; only the final destination changes.
    # Caveats (round-3 ledger): under `--panics:on` Defects are not
    # catchable (this arm never fires); stack overflow and libz3 aborts are
    # not exceptions — the v64 fiber-stack work addresses those. On Windows
    # the fiber trampoline ferries Defects across the fiber switch with
    # their dynamic type intact, so they arrive here unchanged.
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: weInternalWalkerFault,
                                       severity: sevError,
                                       msg: $e.name & ": " & e.msg)])

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings): RawResult =
  # CR-13: clear any stale walk-context pointer left by a previous call that
  # raised. A raise inside walk() propagates through runSymexImpl to the
  # runSymex except handlers WITHOUT clearing currentWalkCtxPtr (the Nim c
  # backend goto-exception model does not re-raise after a finally block when
  # nested try blocks are present, so an inner try/finally cannot be used).
  # Resetting it HERE — before any sync*/allocRef* call that checks
  # `currentWalkCtxPtr != nil` — ensures the stale pointer is never dereffed.
  currentWalkCtxPtr = nil
  let ctx = newContext()
  setCurrentContext(ctx)
  extractionErrors = @[]   ## Phase 15 F7: reset per-run float-extraction error sink
  currentMaxBytesEncodingLen = settings.budget.maxBytesEncodingLen  ## Phase 15 S7a
  currentMaxSplitParts = settings.budget.maxSplitParts             ## CR-11/CR-18
  parseIntGateConstraints = @[]   ## Phase 15 S10a: reset parseInt digits-gate sink
  parseIntRaiseConds = @[]        ## Phase 15 S10b: reset parseInt raise-predicate sink
  unknownExnWarnings = @[]        ## Phase 15 E4: reset unknown-exn-type warning sink
  currentInFlightTypeId = none(string)   ## Phase 15 E8: reset in-flight-exn mirror
  currentInFlightMsg = none(string)      ## Phase 15 E8
  currentExnRefCounter = 0               ## Phase 15 E8: reset fresh-ref counter
  currentDistinctSorts = initTable[string, DistinctSortEntry]()  ## Phase 15 G4
  distinctBijectivityHints = @[]         ## Phase 15 G4: reset skip-hint sink
  distinctSortNames = @[]                ## Phase 15 G4: reset alloc-order hook
  freshnessCapHints = @[]                ## Phase 15 R2: reset cap-hint sink
  ptrFamilyHints = @[]                   ## Phase 15 R8: reset ptr-family hint sink
  heapDepthErrors = @[]                  ## Phase 15 R9: reset heap-depth-error sink
  newFieldZeroErrors = @[]               ## Cluster H Step C: reset isNew-zero-write sink
  loweringDegradeErrors = @[]            ## SND-3 (ADR-0023): reset lowering-degrade sink
  loweringDidDegrade = false             ## SND-3 (ADR-0023): reset per-call degrade signal
  setMembershipKeyTerms = initTable[uint, seq[Z3AnyAst]]()  ## v65: reset set-key registry
  stripDecompConds = @[]                 ## ADR-0026: reset strip-decomposition sink
  stripSynthCounter = 0                  ## ADR-0026: reset strip fresh-name counter
  sliceViewCounter = 0                   ## v67: reset slice-view bound-var counter
  variantLitFreshCounter = 0             ## Round-6 A1: reset variant-lit fresh-field counter
  variantConstructSymFreshCounter = 0    ## Round-6 A3: reset per-fork fresh-field counter
  convFloatToIntBoundConds = @[]         ## Phase 15 CR-3/CR-4: reset domain-bound cond sink
  convFloatToIntDomainConds = @[]        ## R16-2: reset parallel raise-fork sink
  divByZeroConds = @[]                   ## R16-3: reset div/mod-by-zero raise-fork sink
  overflowConds = @[]                    ## R16-4: reset signed-integer overflow raise-fork sink
  strIndexOobConds = @[]                 ## SND-4: reset string-index OOB raise-fork sink
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()  ## Phase 15 C2a
  currentClosureBodies = initTable[      ## Phase 15 C2b: reset site→body map
    tuple[siteHash: int64, declOrder: int], ClosureBody]()
  currentClosureCallAxioms = @[]         ## Phase 15 C2b: reset ground-axiom sink
  currentClosureExitPc = @[]             ## Phase 16 ADR-0012: reset exit-pc channel
  currentClosureCallAxiomStrs = @[]      ## Phase 15 C2b: reset axiom-string hook
  currentClosureCallErrors = @[]         ## Phase 15 C2b: reset closure-call errors
  currentWalkCtxPtr = nil                ## Phase 15 C2b: set just before the walk
  currentBorrowReboxCounter = 0          ## Phase 15 G5: reset rebox-name counter
  currentRefSorts = initTable[string, RawZ3Sort]()    ## Phase 15 R1
  currentNilConsts = initTable[string, Z3AnyAst]()    ## Phase 15 R1
  currentHeapDerefVals = initTable[string, SymVal]()  ## Phase 15 R1
  currentVariantHeaps = initTable[string, Z3AnyAst]() ## ADR-0013 D5 (Slice 2)
  heapWitnessNominalRegistry = initTable[string, IRType]()  ## Cluster H H_witness
  currentCallerHeaps = initTable[string, Z3AnyAst]()  ## Phase 15 R1b
  currentCallerHeapDepth = 0                          ## Phase 15 R1b
  currentCallerAllocCounters = initTable[string, int]()  ## Phase 15 R1b
  currentCallerLiveRefs = initTable[string, seq[Z3AnyAst]]()  ## Phase 15 CR-5
  currentClosureExitHeaps = initTable[string, Z3AnyAst]()     ## Phase 15 CR-1
  currentClosureExitAllocCounters = initTable[string, int]()  ## Phase 15 CR-1
  currentClosureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()  ## Phase 15 CR-1
  currentClosureDidMutateHeap = false                         ## Phase 15 CR-1
  var env: Env
  var initialPC: seq[Z3Bool]
  var log: AbstractionLog
  # ADR-0001 ban scan: variables whose def-use chain contains a
  # bit-twiddling op can't be soundly promoted to Z3Int.
  var intParamNames: HashSet[string]
  for p in prog.params:
    if p.ty.kind == itInt:
      intParamNames.incl p.name
  let banned = collectBan(prog.body, intParamNames)
  # #134: assertion-derived range refinements. Disabled when the
  # user's target is `tAssertionViolation` — the whole point of that
  # search is to find inputs that violate the assertion, so we
  # mustn't fold the assertion into the initial range constraints.
  var assertRanges: Table[string, Interval]
  if target.kind != stkAssertionViolation:
    collectAssertRanges(prog.body, assertRanges)
  if settings.integerSemantics == isLoose:
    emitIsLooseBanner()
  for p in prog.params:
    case p.ty.kind
    of itTuple, itArray, itString, itSeq, itTable, itSet, itMultiVariant, itUninterp, itFloat32, itFloat64, itDistinct, itRef, itPtr:
      # itMultiVariant included here as Phase 14 cycle A1a stub; the
      # `allocateSym` for itMultiVariant raises a clear ValueError
      # (see runtime.nim allocateSym stub). Falling through to the
      # same call site keeps the dispatch surface uniform. itRef/itPtr
      # (Phase 15 R1a) likewise route through `allocateSym`, whose stub
      # raises the classified `heUnresolvedRef` (caught at the runSymex
      # boundary → sxUnknown, Invariant 3).
      # Round-6 B1: `p.isStringBacked` only ever affects the `itSeq` arm;
      # harmless to pass unconditionally for every other kind here.
      env[p.name] = allocateSym(p.ty, p.name, initialPC, p.isStringBacked)
    of itVariant:
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
      # Phase 14 cycle A6 (ADR-0003 D6, mandatory). Under
      # `isOptimised`, promote the variant discriminator to Z3Int
      # so it composes cleanly with other Z3Int-promoted operands
      # (mixed BV/Int comparisons crack the abstraction layer).
      # The BV disc allocated above stays in the Z3 context but
      # becomes unreferenced after the swap; its old disjunction
      # in pcOut is harmless (BV is unused; constraints are
      # tautologies w.r.t. the new svInt disc).
      if settings.integerSemantics == isOptimised and
         p.ty.vDiscTy.kind != itBool:
        # Phase 15 F9c: a `bool` discriminator stays svBool — it is only
        # ever compared to true/false (handled by discEq/isVariantField's
        # svBool arms), never arithmetic, so the Z3Int promotion (which
        # would force `if v.k:` to read an svInt) does not apply.
        var minOrd = high(int)
        var maxOrd = low(int)
        for arm in p.ty.vArms:
          if arm.tagOrdinal < 0: continue  # else sentinel
          if arm.tagOrdinal < minOrd: minOrd = arm.tagOrdinal
          if arm.tagOrdinal > maxOrd: maxOrd = arm.tagOrdinal
        # Phase 14 A6: when an `else:` arm is present, the convex
        # hull must also include the else-covered ordinals from
        # `vDiscTags` (the enum's full domain). Without this, the
        # range bound below excludes legal disc values.
        for dt in p.ty.vDiscTags:
          if dt.ord < minOrd: minOrd = dt.ord
          if dt.ord > maxOrd: maxOrd = dt.ord
        if minOrd == high(int):
          # No non-else arms AND no vDiscTags — degenerate.
          minOrd = 0; maxOrd = 0
        let promotedDisc = SymVal(kind: svInt,
          zi: mkIntVar(p.name & "." & p.ty.vDiscName & ".zi"))
        # Tight bound + per-ordinal disjunction on the Z3Int.
        initialPC.add (promotedDisc.zi >= mkZ3IntLit(int64(minOrd)))
        initialPC.add (promotedDisc.zi <= mkZ3IntLit(int64(maxOrd)))
        # Disjunction over legal ordinals (including else-covered
        # ordinals via vDiscTags when populated).
        var ordSet: seq[int]
        for arm in p.ty.vArms:
          if arm.tagOrdinal >= 0: ordSet.add arm.tagOrdinal
        for dt in p.ty.vDiscTags:
          if dt.ord notin ordSet: ordSet.add dt.ord
        if ordSet.len > 0:
          var clause = promotedDisc.zi == mkZ3IntLit(int64(ordSet[0]))
          for k in 1 ..< ordSet.len:
            clause = clause or
              (promotedDisc.zi == mkZ3IntLit(int64(ordSet[k])))
          initialPC.add clause
        env[p.name].vDisc[] = promotedDisc
        let ivl = interval(int64(minOrd), int64(maxOrd))
        log.add AbstractionEntry(
          name: p.name & "." & p.ty.vDiscName,
          interval: ivl,
          evidence: aeVariantDisc,
          derivation: "variant discriminator promoted to Z3Int " &
                      "over " & $ivl & " (" & $p.ty.vArms.len & " arms)")
    of itInt:
      # Type-derived range takes precedence; otherwise look for
      # assertion-derived ranges (#134).
      var hasRange = p.hasRange
      var rangeLo = p.rangeLo
      var rangeHi = p.rangeHi
      var fromAssert = false
      if not hasRange and assertRanges.hasKey(p.name):
        let ai = assertRanges[p.name]
        if not ai.isEmpty:
          hasRange = true
          rangeLo = ai.lo
          rangeHi = ai.hi
          fromAssert = true
      let ivl = interval(rangeLo, rangeHi)
      let promoteLoose = settings.integerSemantics == isLoose
      let promoteSound = settings.integerSemantics == isOptimised and
                         hasRange and
                         fitsBVWindow(ivl, p.ty) and
                         p.name notin banned
      # Round-6 B4 (ADR-0028 Leg 1, ADR-0027's recorded lift): a param
      # `collectIntOffsetParams` (`dsl_parser.nim`) traced to an
      # accumulating-scan's entry offset promotes UNCONDITIONALLY — it
      # carries no proven range (unlike `promoteSound`), so it must NOT add
      # the range constraints below; it exists purely so `iekStrSubstr`'s
      # strict Int-sortedness requirement (the CR-17 non-termination guard)
      # is met by the closed form's own LOW bound.
      let promote = promoteLoose or promoteSound or p.isIntOffset
      if promote:
        env[p.name] = SymVal(kind: svInt, zi: mkIntVar(p.name))
        if promoteSound:
          initialPC.add (env[p.name].zi >= mkZ3IntLit(rangeLo))
          initialPC.add (env[p.name].zi <= mkZ3IntLit(rangeHi))
          log.add AbstractionEntry(
            name: p.name,
            interval: ivl,
            evidence: if fromAssert: aeNumericFold else: aeTypeRange,
            derivation:
              (if fromAssert: "assertion-derived range "
               else: "type-derived range ") &
              $ivl & " fits " & $p.ty & " BV window")
        elif p.hasRange and not promoteLoose:
          # isIntOffset-only promotion (not isLoose, not promoteSound) with
          # a DECLARED range (e.g. `range[..]`/`Natural`/`Positive`): unlike
          # isLoose's user-opted unsoundness, `isIntOffset` is a purely
          # internal representation choice the user never asked to be
          # unsound for — carry the same range constraint the BV `else`
          # branch below would have added, just Int-sorted. `lowerBool`
          # dispatches on the now-svInt `env[p.name]`, so this is the exact
          # BV-branch idiom below, sort-adapted.
          initialPC.add lowerBool(env,
            mkBinop(bGe, mkVar(p.name), mkIntLit(p.rangeLo)))
          initialPC.add lowerBool(env,
            mkBinop(bLe, mkVar(p.name), mkIntLit(p.rangeHi)))
        # isLoose (regardless of isIntOffset): no range constraints, no
        # audit entry — by design, the user is told this is unsound and
        # accepts it.
      else:
        env[p.name] = bvVar(p.ty, p.name)
        if p.hasRange:
          # Type-derived range as BV constraints (so `x > 100` is
          # still UNSAT under isExact for range[0..100]).
          initialPC.add lowerBool(env,
            mkBinop(bGe, mkVar(p.name), mkIntLit(p.rangeLo)))
          initialPC.add lowerBool(env,
            mkBinop(bLe, mkVar(p.name), mkIntLit(p.rangeHi)))
    of itBool:
      env[p.name] = SymVal(kind: svBool, bo: mkBoolVar(p.name))
  let initial = Path(pc: initialPC, env: env)
  # Static IR scan: collect string-literal keys accessed on each
  # Table-typed param so witness extraction returns a Nim Table
  # populated for those keys.
  var tabKeys: Table[string, HashSet[string]]
  var setMembers: Table[string, HashSet[int64]]
  for p in prog.params:
    if p.ty.kind == itTable:
      var keys: HashSet[string]
      collectTableLitKeys(prog.body, p.name, keys)
      tabKeys[p.name] = keys
    elif p.ty.kind == itSet:
      var members: HashSet[int64]
      collectSetLitMembers(prog.body, p.name, members)
      setMembers[p.name] = members
  var w = WalkCtx(
    z3: ctx, target: target, params: prog.params,
    found: @[], sawUnknown: false,
    settings: settings, procs: prog.procs,
    callStack: @[], callStats: initTable[string, CallStat](),
    callCache: initTable[string, CallCacheEntry](),
    activeCalls: initHashSet[string](),
    tabKeys: tabKeys,
    setMembers: setMembers,
    initialEnv: env,
    statics: WalkerStatics(exnTable: exnTypeTable,   ## Phase 15 E4
                           userExnHierarchy: prog.userExnHierarchy),  ## E4a
  )
  # Phase 15 C2b: publish a pointer to the live WalkCtx so `lowerClosureCall`
  # (running in the `lower` evaluator, no `WalkCtx` parameter) can drive the
  # lambda-body descent through `walk`. `w` is a stack local that lives across
  # the whole walk; the pointer is cleared after.
  currentWalkCtxPtr = addr w
  # CR-13: clear on the normal exit path (see the nil assignment below after
  # walk() returns). On the exception path, the pointer is cleared at the start
  # of the NEXT runSymexImpl call (the `currentWalkCtxPtr = nil` above), so it
  # is never stale when a sync*/allocRef* helper checks it. No inner try/except
  # or try/finally here — Nim's c backend goto-exception model can silently
  # swallow re-raises from nested try blocks, breaking exception propagation.
  # CR-9 Stage 4: sync caches that were already allocated during env setup
  # (lines above; `currentWalkCtxPtr` was nil then so `sync*` were no-ops).
  # This seeds WalkerStatics with any sorts allocated before the walk so that
  # in-walk reads from `w.statics.*` find the expected keys.
  for tid, srt in currentRefSorts:
    w.statics.refSorts[tid] = srt
  for tid, nc in currentNilConsts:
    w.statics.nilConsts[tid] = nc
  for dn, de in currentDistinctSorts:
    if not w.statics.distinctSorts.hasKey(dn):
      w.statics.distinctSorts[dn] = de
      w.statics.distinctSortNames.add dn
  for ck, fd in currentClosureSyms:
    if not w.statics.closureSyms.hasKey(ck):
      w.statics.closureSyms[ck] = fd
  for sk, cb in currentClosureBodies:
    if not w.statics.closureBodies.hasKey(sk):
      w.statics.closureBodies[sk] = cb
  discard walk(prog.body, @[initial], w)
  currentWalkCtxPtr = nil   ## (a) normal-path clear: walk() completed without raising
  # Phase 15 G4 (ADR-0008 D4): CR-9 Stage 4 — `WalkerStatics.distinctSorts`/
  # `.distinctSortNames` are now the LIVE store, populated during the walk by
  # `syncDistinctSortEntry` (called from `allocDistinctSym`). No post-walk
  # mirror needed; `w.statics.distinctSorts`/`.distinctSortNames` are current.
  # Phase 15 C2a (ADR-0009): CR-9 Stage 4 — `WalkerStatics.closureSyms` is now
  # the LIVE store, populated during the walk by `syncClosureSymEntry` (called
  # from `buildClosure`). No post-walk mirror needed; `w.statics.closureSyms`
  # already contains the final values.
  # Phase 15 R1 (ADR-0010): CR-9 Stage 4 — `WalkerStatics.refSorts`/`.nilConsts`
  # are now the LIVE store, populated during the walk by `syncRefSortEntry` (called
  # from `allocRefSort` whenever a new sort is allocated). No post-walk mirror copy
  # needed; `w.statics.refSorts`/`.nilConsts` already contain the final values.
  var statsSeq: CallStats
  for name, st in w.callStats:
    statsSeq.add st
  # Phase 15 E4. Drain the unknown-exn-type warning sink, dedup'd by type name.
  # sevWarning never halts a verdict (Invariant 7), so it is appended to the
  # result's errors regardless of which verdict branch is taken below.
  # CR-9 Stage 5: read from WalkCtx.unknownExnWarnings (LIVE store during walk);
  # fall back to threadvar. Union covers both walk and any non-walk callers.
  var exnWarnings: seq[SymexErrorInfo]
  let unknownExnWarningsLive = w.unknownExnWarnings & unknownExnWarnings
  if unknownExnWarningsLive.len > 0:
    var seen: HashSet[string]
    for e in unknownExnWarningsLive:
      if e.msg notin seen:
        seen.incl e.msg
        exnWarnings.add e
  # Phase 15 G4. Drain the distinct-bijectivity-skipped hint sink, dedup'd by
  # message (one per distinct type whose base was FP/String). sevHint never
  # changes the verdict (Invariant 7), so it rides every branch alongside
  # exnWarnings — appended to `exnWarnings` so the existing append sites carry
  # it on sat/unsat/unknown uniformly.
  # CR-9 Stage 5: read from WalkCtx.distinctBijectivityHints (LIVE store during
  # walk); fall back to threadvar for pre-walk/probe allocations. Union covers all.
  let distinctBijectivityHintsLive = w.distinctBijectivityHints & distinctBijectivityHints
  if distinctBijectivityHintsLive.len > 0:
    var seenD: HashSet[string]
    for e in distinctBijectivityHintsLive:
      if e.msg notin seenD:
        seenD.incl e.msg
        exnWarnings.add e
  # Phase 15 R2. Drain the freshness-cap hint sink, dedup'd by message (one per
  # ref type whose per-path distinctness inequalities hit the cap). sevHint
  # never changes the verdict (Invariant 7) — rides every branch via
  # `exnWarnings`, exactly the G4 bijectivity-skip drain above.
  # CR-9 Stage 5: read from WalkCtx.freshnessCapHints (the LIVE store during
  # the walk); fall back to threadvar for any hints appended outside a walk.
  let freshnessCapHintsLive = w.freshnessCapHints & freshnessCapHints
  if freshnessCapHintsLive.len > 0:
    var seenF: HashSet[string]
    for e in freshnessCapHintsLive:
      if e.msg notin seenF:
        seenF.incl e.msg
        exnWarnings.add e
  # Phase 15 R8. Drain the ptr-family hint sink, dedup'd by message (one entry
  # per run regardless of how many ptr derefs occurred). sevHint never changes
  # the verdict (Invariant 7) — rides every branch via `exnWarnings`, exactly the
  # R2 freshness-cap drain above. A managed-`ref T`-only run drains NOTHING.
  # CR-9 Stage 5: read from WalkCtx.ptrFamilyHints (LIVE store); fall back to
  # threadvar. Union covers both walk and any potential pre-walk callers.
  let ptrFamilyHintsLive = w.ptrFamilyHints & ptrFamilyHints
  if ptrFamilyHintsLive.len > 0:
    var seenP: HashSet[string]
    for e in ptrFamilyHintsLive:
      if e.msg notin seenP:
        seenP.incl e.msg
        exnWarnings.add e
  # R16-2: convFloatToIntDomainHints removed — replaced by real RangeDefect raise
  # forks via drainConvFloatToIntRaises. No hint drain here.
  # Phase 15 R9. Drain the heap-depth-error sink (dedup'd by message). A
  # `heDepthExhausted` is `sevError`, but the verdict is already driven PER-PATH:
  # the exhausting path was halted (returned no survivor) and set `w.sawUnknown`,
  # so a run with NO sat finding degrades to `sxUnknown` carrying this classified
  # kind, while a SHALLOWER path that reached the target still yields its `sxSat`
  # witness (the `w.found` precedence below). Riding `exnWarnings` surfaces the
  # kind on whichever branch is taken (Invariant 3). A run that never exhausts the
  # budget drains NOTHING (no spurious halt). Mirrors the R8 ptr-family drain.
  # CR-9 Stage 5: read from WalkCtx.heapDepthErrors (the LIVE store during the
  # walk); heapDepthExhausted writes both threadvar and w field. Union covers all.
  let heapDepthErrorsLive = w.heapDepthErrors & heapDepthErrors
  if heapDepthErrorsLive.len > 0:
    var seenD: HashSet[string]
    for e in heapDepthErrorsLive:
      if e.msg notin seenD:
        seenD.incl e.msg
        exnWarnings.add e
  # v64 (chapulin catalog #5(b), Invariant 7). Drain the budget-bail error
  # sink (dedup'd by message) — mirrors the R9 heap-depth-error drain. A
  # `beBudgetExhausted` is `sevError`; the exhausted/pruned paths already
  # drove the verdict via `w.sawUnknown` — this drain ensures the degraded
  # `sxUnknown` carries the classified WHY instead of an empty errors seq.
  # WalkCtx-field-only (both emitting sites have `w: var WalkCtx`).
  if w.walkDegradeErrors.len > 0:
    var seenB: HashSet[string]
    for e in w.walkDegradeErrors:
      if e.msg notin seenB:
        seenB.incl e.msg
        exnWarnings.add e
  # Cluster H Step C. Drain the isNew-zero-write error sink (dedup'd by
  # message) — mirrors the R9 heap-depth-error drain exactly. A
  # `heNewFieldZeroUnsupported` is `sevError`; the offending path was tainted
  # `uncertain = true` (not halted) so its own downstream sat/raised findings
  # already demote to `sxUnknown` at the `uncertain` chokepoints — this drain
  # only ensures the classified kind rides every verdict branch (Invariant 3).
  let newFieldZeroErrorsLive = w.newFieldZeroErrors & newFieldZeroErrors
  if newFieldZeroErrorsLive.len > 0:
    var seenNZ: HashSet[string]
    for e in newFieldZeroErrorsLive:
      if e.msg notin seenNZ:
        seenNZ.incl e.msg
        exnWarnings.add e
  # SND-3 (ADR-0023, walker v58). Drain the lowering-degrade error sink
  # (dedup'd by message) — mirrors the R9 heap-depth-error / Cluster-H
  # newFieldZeroErrors drains exactly. Each entry is `sevError`; the
  # offending path was tainted `uncertain = true` by `drainPendingLowerEffects`
  # (not halted), so its own downstream sat/raised findings already demote to
  # `sxUnknown` at the `uncertain` chokepoints — this drain only ensures the
  # classified kind rides every verdict branch (Invariant 3). Threadvar-only
  # (no WalkCtx-field union): the lowering sites that populate it (`lower`'s
  # `iekBinop`/`iekContains` arms, `cmpString`) have no `w: var WalkCtx` in
  # scope.
  if loweringDegradeErrors.len > 0:
    var seenLD: HashSet[string]
    for e in loweringDegradeErrors:
      if e.msg notin seenLD:
        seenLD.incl e.msg
        exnWarnings.add e
  # Phase 15 G1c. Parse-time errors (generic instantiation-cap overflow) are
  # surfaced on every verdict branch. A `geInstantiationCapped` is `sevError`:
  # the over-cap instantiation was never registered, so the SUT's coverage is
  # incomplete and the verdict MUST degrade to `sxUnknown` (Invariant 3 — a
  # `sevError` never resolves to sat/unsat). The walker's missing-callee arm
  # already sets `w.sawUnknown` when the capped call is reached, but we force
  # it here so a cap discovered on a NON-walked path (the over-cap callee is
  # parsed but, e.g., guarded behind an unreachable branch) still cannot yield
  # an unsound sat/unsat.
  #
  # NOTE (SND-1, RFC Cluster 1): despite the name, `capForcedUnknown` below is
  # NOT specific to instantiation caps — it is a blanket switch that forces
  # `sxUnknown` whenever ANY `sevError` parseError exists anywhere in
  # `prog.parseErrors`, regardless of which parse-time classifier raised it
  # (e.g. `heUnsafeCast`, the Class-A `mkUnsupported` sites that also record a
  # `sevError`, …). Class-B bare `mkUnsupported` sites (no accompanying
  # `sevError`) are NOT covered by this switch — those rely on the walker-arm
  # `isUnsupported` taint-and-continue fix above (SND-1) to reach the
  # `w.sawUnknown`/`Path.uncertain` chokepoints instead.
  let capForcedUnknown = block:
    var any = false
    for e in prog.parseErrors:
      if e.severity == sevError: any = true; break
    any
  # Phase 15 C2b. Drain the closure-call error sink (dedup'd by message). A
  # `ceClosureUnknownCallee`/`ceInlineBudgetExceeded` is `sevError`: the call's
  # semantics were not modeled, so the verdict MUST degrade to `sxUnknown`
  # (Invariant 3 — never a silent sat/unsat). Surface them on every branch.
  # CR-9 Stage 5: read from WalkCtx.closureCallErrors (LIVE store during walk)
  # and union with threadvar (covers the no-walk path in applyClosureGround).
  let closureCallErrorsLive = w.closureCallErrors & currentClosureCallErrors
  var closureErrs: seq[SymexErrorInfo]
  block:
    var seenC: HashSet[string]
    for e in closureCallErrorsLive:
      if e.msg notin seenC:
        seenC.incl e.msg
        closureErrs.add e
  let closureForcedUnknown = block:
    var any = false
    for e in closureErrs:
      if e.severity == sevError: any = true; break
    any
  ## ADR-0012 D2: unified, target-independent precedence over w.found:
  ##   sxSat  >  sxRaised  >  sxUnsat/sxUnknown.
  ## Scan for the FIRST sxSat (the direct answer — for stkLabel this is the only
  ## status that answers "is the label reachable?"); else the FIRST sxRaised (a
  ## defect that fires). This is correct for ALL target kinds, NOT a label
  ## special-case: raise-flavoured targets only ever accumulate sxRaised in
  ## w.found (label sxSat is added solely at isTargetLabel, gated on stkLabel),
  ## so first-sxRaised-wins is bit-identical to the prior w.found[0] behaviour
  ## for them. sxUnsat/sxUnknown only when no sxSat/sxRaised exists.
  var winnerFound = false
  var winnerIdx   = -1
  var winner: RawResult
  if w.found.len > 0 and not capForcedUnknown and not closureForcedUnknown:
    for i, f in w.found:
      if f.status == sxSat:
        winner     = f
        winnerFound = true
        winnerIdx  = i
        break
    if not winnerFound:
      for i, f in w.found:
        if f.status == sxRaised:
          winner     = f
          winnerFound = true
          winnerIdx  = i
          break
  if winnerFound:
    var r = winner
    r.abstractions = log
    r.callStats = statsSeq
    ## ADR-0012 D2: collect every non-winning sxRaised into diagnostics.
    ## If winner is sxSat (winnerIdx points to it), ALL sxRaised entries
    ## qualify (none has i==winnerIdx AND is sxRaised). If winner is the
    ## first sxRaised (winnerIdx points to it), all other sxRaised go in.
    var diags: seq[RawDiagnostic]
    for i, f in w.found:
      if f.status == sxRaised and i != winnerIdx:
        diags.add RawDiagnostic(raisedTypeId: f.raisedTypeId,
                                isDefect:     f.isDefect,
                                raisedMsg:    f.raisedMsg,
                                raisedWitness: f.raisedWitness)
    r.diagnostics = diags
    # CR-9 Stage 5: read from WalkCtx.extractionErrors (LIVE store during walk)
    # and union with threadvar fallback. extractionErrors is SAT-branch-only.
    let extractionErrorsLive = w.extractionErrors & extractionErrors
    if extractionErrorsLive.len > 0:   ## Phase 15 F7: surface any float-extraction failures
      r.errors.add extractionErrorsLive
    r.errors.add exnWarnings       ## Phase 15 E4
    r.errors.add prog.parseErrors  ## Phase 15 G1c
    r.errors.add closureErrs       ## Phase 15 C2b
    r
  elif w.sawUnknown or capForcedUnknown or closureForcedUnknown:
    # v64 (chapulin catalog #5(b)): Invariant-7 BACKSTOP. Every sxUnknown
    # must carry at least one classified error. All known degrade sites now
    # classify (budget bails via `beBudgetExhausted`, lowering degrades via
    # `loweringDegradeErrors`, …) — if this fires, some `sawUnknown` site
    # escaped classification, which is itself a walker bug: surface it as
    # `weInternalWalkerFault` so telemetry tracks it, never an empty seq.
    var unknownErrs = exnWarnings & prog.parseErrors & closureErrs
    if unknownErrs.len == 0:
      unknownErrs.add SymexErrorInfo(
        kind: weInternalWalkerFault, severity: sevError,
        msg: "sxUnknown produced with no classified reason — an unclassified " &
             "degrade site set sawUnknown bare (walker classification gap; " &
             "weInternalWalkerFault)")
    RawResult(status: sxUnknown, abstractions: log, callStats: statsSeq,
              errors: unknownErrs)
  else:
    RawResult(status: sxUnsat, abstractions: log, callStats: statsSeq,
              errors: exnWarnings & prog.parseErrors & closureErrs)

# ---- Raw → typed witness ----------------------------------------------------
#
# Per-width readers used by the macro's tuple-construction. The macro
# selects the right reader based on the param's IRType.

proc readBool*(w: RawWitness, name: string): bool =
  w.boolVals[name]

# Phase 15 F7: bit-exact float witness readers. Index the float tables
# populated by `extractLeaf`'s `evalFloat64Opt`/`evalFloat32Opt` path; the
# stored value round-trips every IEEE-754 bit pattern (NaN, ±Inf, ±0).
proc readFloat*(w: RawWitness, name: string): float = w.float64Vals[name]
proc readFloat32*(w: RawWitness, name: string): float32 = w.float32Vals[name]

proc readHeapSnapshot*(w: RawWitness): seq[HeapSnapshotEntry] = w.heapSnapshot
  ## Phase 15 R12. Public accessor for the heap-snapshot witness (RawWitness is
  ## not an exported type, so the `symexFind` macro reaches the field through
  ## this proc). Empty for a SUT with no ref/ptr params.

# Signed widths return the matching Nim signed type.
proc readInt*(w: RawWitness,   name: string): int   = int(  w.intVals[name])
proc readInt8*(w: RawWitness,  name: string): int8  = int8( w.intVals[name])
proc readInt16*(w: RawWitness, name: string): int16 = int16(w.intVals[name])
proc readInt32*(w: RawWitness, name: string): int32 = int32(w.intVals[name])
proc readInt64*(w: RawWitness, name: string): int64 =       w.intVals[name]

# Unsigned widths.
proc readUInt*(w: RawWitness,   name: string): uint   = uint(  w.uintVals[name])
proc readUInt8*(w: RawWitness,  name: string): uint8  = uint8( w.uintVals[name])
proc readUInt16*(w: RawWitness, name: string): uint16 = uint16(w.uintVals[name])
proc readUInt32*(w: RawWitness, name: string): uint32 = uint32(w.uintVals[name])
proc readUInt64*(w: RawWitness, name: string): uint64 =        w.uintVals[name]

proc readString*(w: RawWitness, name: string): string = w.strVals[name]

proc readSeqLen*(w: RawWitness, name: string): int =
  ## Phase 15 R3 (ADR-0010). The model length of a seq witness leaf — used by
  ## the `seq[ref T]` reader to size a default-cell seq (the per-element pointee
  ## values are not individually rendered at R3; the full per-element
  ## heap-snapshot witness lands R11b/R12).
  if w.seqLens.hasKey(name): w.seqLens[name] else: 0

proc readSeqInt*(w: RawWitness, name: string): seq[int] =
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int(w.intVals[path])

proc readSeqInt8*(w: RawWitness, name: string): seq[int8] =
  ## RFC-chapulin-hardening M1: fixed-width-int seq element reader.
  ## Analogous to `readSeqInt` (the int64 case) but narrowing each leaf to
  ## `int8` — the value was already range-correct at extraction time
  ## (`extractSeqElements`'s `itInt`/width==8 arm evaluates the model's BV8
  ## and stores the sign-correct int64 in `intVals`), so the narrowing here
  ## is a lossless truncation, not a re-interpretation.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int8](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int8(w.intVals[path])

proc readSeqInt16*(w: RawWitness, name: string): seq[int16] =
  ## RFC-chapulin-hardening M1. See `readSeqInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int16](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int16(w.intVals[path])

proc readSeqInt32*(w: RawWitness, name: string): seq[int32] =
  ## RFC-chapulin-hardening M1. See `readSeqInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int32(w.intVals[path])

proc readSeqUInt8*(w: RawWitness, name: string): seq[uint8] =
  ## RFC-chapulin-hardening M1: fixed-width-int seq element reader. Covers
  ## both `seq[byte]` and `seq[uint8]` (`byte` is a Nim alias for `uint8`;
  ## `classifyType` maps either to the same unsigned-width-8 `IRType`, so the
  ## reader cannot distinguish the two — nor does it need to, the return
  ## type is structurally identical). Reads from `uintVals` — the unsigned
  ## twin of `readSeqInt8`'s `intVals`.
  ##
  ## Round-6 B4: a `seq[byte]` param B1 marked `isStringBacked` allocates via
  ## the itString machinery (`allocateSym`), so its model value lands in
  ## `RawWitness.strVals` (one whole-string leaf) instead of `seqLens`/
  ## `uintVals` (per-index array leaves) — B1's own flagged gap, since the
  ## GENERATED reader glue picks `readSeqUInt8` off the param's DECLARED
  ## type (`seq[byte]`), unaware of the allocation representation, and
  ## previously degraded to an empty seq no matter what the model held.
  ## Route through `strVals` first, byte-per-char, before falling back to
  ## the array representation — the two representations are mutually
  ## exclusive per param (`extractLeaf`'s `svString`/array split populates
  ## exactly one), so checking `strVals` first never shadows a genuine
  ## array-backed witness.
  if w.strVals.hasKey(name):
    let s = w.strVals[name]
    result = newSeq[uint8](s.len)
    for i in 0 ..< s.len:
      result[i] = uint8(s[i])
    return
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint8](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint8(w.uintVals[path])

proc readSeqUInt16*(w: RawWitness, name: string): seq[uint16] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint16](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint16(w.uintVals[path])

proc readSeqUInt32*(w: RawWitness, name: string): seq[uint32] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = uint32(w.uintVals[path])

proc readSeqUInt64*(w: RawWitness, name: string): seq[uint64] =
  ## RFC-chapulin-hardening M1. See `readSeqUInt8`.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[uint64](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.uintVals.hasKey(path):
      result[i] = w.uintVals[path]

proc readSeqFloat64*(w: RawWitness, name: string): seq[float] =
  ## Phase 15 F9b: reconstruct a `seq[float]` from the per-element
  ## float64Vals subtable, analogous to readSeqInt.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[float](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.float64Vals.hasKey(path):
      result[i] = w.float64Vals[path]

proc readSeqFloat32*(w: RawWitness, name: string): seq[float32] =
  ## Phase 15 F9b: reconstruct a `seq[float32]` from float32Vals.
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[float32](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.float32Vals.hasKey(path):
      result[i] = w.float32Vals[path]

proc readTableStrInt*(w: RawWitness, name: string): Table[string, int] =
  ## Phase 5 cycle 5: build a `Table[string, int]` populated with the
  ## key-value pairs the SUT accessed (static string literals).
  result = initTable[string, int]()
  if not w.tabKeys.hasKey(name):
    return
  for k in w.tabKeys[name]:
    let p = name & "." & k
    if w.intVals.hasKey(p):
      result[k] = int(w.intVals[p])

proc readSetInt*(w: RawWitness, name: string): HashSet[int] =
  ## Phase 5 cycle 8: build a `HashSet[int]` from collected members.
  result = initHashSet[int]()
  if not w.setMembers.hasKey(name): return
  for v in w.setMembers[name]:
    result.incl int(v)

# ---- Phase 15 Cluster C (C2a): closure-construction test hooks ---------------
#
# These hooks let a test introspect the CONSTRUCTED `svClosure` (env snapshot +
# per-site funcSym) WITHOUT a full `symexFind` body descent (`f(3)` would hit
# the still-stubbed `iekClosureCall`). They set up a fresh context, reset the
# closure-funcSym memo, build the construction-time env at the `let f = …`
# binding point, and lower an `iekLambda` against it via the real
# `lower(env, e)` / `buildClosure` path. The probe returns a plain record so the
# non-exported `Env`/`SymVal`/`symValHash`/`lower` stay encapsulated.

type C2aClosureProbe* = object  ## Phase 15 C2a test hook.
  isClosure*:                       bool
  siteHash*:                        int64
  declOrder*:                       int
  envIsTuple*:                      bool
  envFieldNames*:                   seq[string]
  envFieldCount*:                   int
  capturedFieldMatchesOffset*:      bool
  funcDeclIsLive*:                  bool
  closureSymsLen*:                  int
  assertionCountDuringConstruction*: int

proc c2aClosureProbe*(): C2aClosureProbe =
  ## Construct the reference closure (per RFC §C2a) and return an introspectable
  ## probe. Models the `let f = proc(y: int): int = y + offset` binding point of
  ##   proc sut(x: int): int =
  ##     let offset = x * 2
  ##     let f = proc(y: int): int = y + offset
  ##     f(3)
  ## with `offset` (== x*2) and an `unrelated` local in the construction env.
  let ctx = newContext()
  setCurrentContext(ctx)
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()
  let offsetSV = SymVal(kind: svBV64, bv64: mkBitVec[64](14'i64), signed: true)
  var env: Env = initOrderedTable[string, SymVal]()
  env["offset"] = offsetSV
  env["unrelated"] = SymVal(kind: svBV64, bv64: mkBitVec[64](99'i64),
                            signed: true)
  let body = mkReturnVal(mkBinop(bAdd, mkVar("y"), mkVar("offset")))
  let lam = mkLambda(siteHash = 4242'i64, declOrder = 0,
                     params = @[IRParam(name: "y", ty: tInt(64, true))],
                     body = body, captures = @["offset"], retTy = tInt(64, true))
  let clo = lower(env, lam)
  result.isClosure = clo.kind == svClosure
  if result.isClosure:
    result.siteHash = clo.closureSite.siteHash
    result.declOrder = clo.closureSite.declOrder
    if clo.closureEnv != nil:
      let envRec = clo.closureEnv[]
      result.envIsTuple = envRec.kind == svTuple
      result.envFieldNames = envRec.fieldNames
      result.envFieldCount = envRec.fields.len
      if result.envFieldCount == 1:
        result.capturedFieldMatchesOffset =
          envRec.fields[0].kind == svBV64 and
          symValHash(envRec.fields[0]) == symValHash(offsetSV)
    result.funcDeclIsLive = not clo.closureRawFD.isNil
  result.closureSymsLen = currentClosureSyms.len
  # Construction touches no solver — there is no solver in this probe and
  # `buildClosure` only DECLARES a funcSym (no assertion). Deterministically 0.
  result.assertionCountDuringConstruction = 0

proc c2aClosureProbeRelowered*(): C2aClosureProbe =
  ## Lower the SAME site against the SAME env/param sorts TWICE; assert the
  ## funcSym memo holds exactly one entry (the get-or-create reuse).
  let ctx = newContext()
  setCurrentContext(ctx)
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()
  let offsetSV = SymVal(kind: svBV64, bv64: mkBitVec[64](14'i64), signed: true)
  var env: Env = initOrderedTable[string, SymVal]()
  env["offset"] = offsetSV
  let body = mkReturnVal(mkBinop(bAdd, mkVar("y"), mkVar("offset")))
  let lam = mkLambda(siteHash = 7'i64, declOrder = 1,
                     params = @[IRParam(name: "y", ty: tInt(64, true))],
                     body = body, captures = @["offset"], retTy = tInt(64, true))
  let c1 = lower(env, lam)
  let c2 = lower(env, lam)
  result.isClosure = c1.kind == svClosure and c2.kind == svClosure
  result.closureSymsLen = currentClosureSyms.len
  result.assertionCountDuringConstruction = 0
