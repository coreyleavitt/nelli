## RFC-0016 0.10.0 review D3c-1: the symbolic value core, a leaf module.
##
## `SymVal` and its kind tag, `Env`, the `Symex*Error` family, the BV lifting
## templates, `bvVar`/`bvRangeConds`, and the lowering-time degrade sink
## (`lowerDegrade` with the threadvars it writes) used to be the first
## thousand lines of `runtime.nim`, which its `include`d files read by
## sharing a namespace. They depend on nothing later, so they are a module:
## imports are `z3`, `./types`, `./abstraction` and the standard library only.
## `runtime.nim` imports and re-exports this module, so importers of
## `nelli/smt/runtime` are unchanged.
##
## Threadvars here (`loweringDegradeErrors`, `loweringPendingTaint`,
## `loweringPendingUb`) are reset by `resetLoweringSink`, which
## `resetSymexRunState` calls: a threadvar left out of it would leak a prior
## run's state into the next (the `tsymex_0016_d3_include_census` scan checks
## every threadvar of this file is named there).

import std/tables
import std/options
import z3
import ./types
import ./abstraction

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

  SymexUnsupportedRegexError* = object of CatchableError
    ## Phase 15 S6b. Raised during `lower` for a `re"…"` pattern the walker
    ## cannot answer for. RFC-0005 S8ay: a pattern whose validity
    ## `pcre_syntax` does not decide (a named group, an unread escape, a
    ## non-literal Regex) and the captures overloads; a valid pattern with an
    ## unmodelled construct is `SymexZ3StringIncompleteError`, a rejected
    ## one the `RegexError` raise, and `find` is lowered. Caught at the
    ## `runSymex` boundary →
    ## `sxUnknown` carrying a `seUnsupportedRegex` (sevError) error — never a
    ## crash, never a silent UNSAT (ADR-0006, Invariant 3). The S6a error
    ## message rides in `msg`.

  SymexNotInHandlerError* = object of CatchableError
    ## Phase 15 E8. Raised when `getCurrentException()` /
    ## `getCurrentExceptionMsg()` is lowered with NO in-flight exception
    ## (`w.frame.inFlightExn.isNone`) — i.e. called outside any `except`
    ## handler body. Caught at the `runSymex` boundary → `sxUnknown` carrying
    ## an `eeNotInHandler` (sevError) classified error (Invariant 3 — never a
    ## panic, never a silent UNSAT). The intrinsic name rides in `msg`.

  SymexOwnershipUnsupportedError* = object of CatchableError
    ## Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). Raised when an
    ## `owned T` / `Atomic[T]` formal is allocated (classifyType
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

  StrBuf* = enum
    ## RFC-0005 S8ca. Whose memory a string value holds, as Nim's strings
    ## have it: a literal's (shared, read-only: the first write copies it,
    ## `prepareMutation`), or its own (written in place). A by-value copy
    ## of an address-taken string shares that memory, so a write through
    ## the pointer is seen through the copy only in the second case
    ## (`bindVarLocs`). A value of unknown provenance (a parameter, a heap
    ## read, a merge) is `sbUnknown`.
    sbUnknown, sbLiteral, sbOwned

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
    svBitSet   ## RFC-0005 S8bq: a builtin `set[T]`, one bit-vector with bit
               ## `i` for the value `lo + i` of `T` (`bitSetDomain`).

  SymVal* = object
    ## `signed` is only meaningful when `kind in {svBV8,svBV16,svBV32,svBV64}`.
    ## Nim variant objects cannot enforce this at the type level (duplicate field
    ## names across separate `of` branches are rejected by the compiler), so we
    ## keep it as a common pre-case field; all read sites are guarded by a
    ## BV-kind case branch (Stage A, CR-9(a)). RFC-0016 review D3c-1: the
    ## fields were private to `runtime.nim` and are exported now that the type
    ## lives in this leaf; `runtime.nim` and its `include`d files read them.
    signed*: bool
    case kind*: SVKind
    of svBV8:  bv8*:  Z3BitVec[8]
    of svBV16: bv16*: Z3BitVec[16]
    of svBV32: bv32*: Z3BitVec[32]
    of svBV64: bv64*: Z3BitVec[64]
    of svInt:
      zi*:   Z3Int
      ziWidth*: int
        ## R3 (S2, walker v91): static Nim width (8/16/32/64) of the value
        ## this Int term models, WHEN KNOWN. 0 (the Nim zero-value default,
        ## left untouched at most `svInt` construction sites) means
        ## UNKNOWN/unconstrained — e.g. a `.len`/`indexOf`/`parseInt`
        ## sentinel, or a probe-miss/ternary-mismatch value with no traced
        ## static type. `overflowCond`'s svInt sibling (`overflowCondInt`,
        ## below) skips forking when `ziWidth == 0` — the SAME "skip" every
        ## svInt got unconditionally before this slice, now scoped to "no
        ## known static width" instead of "any svInt whatsoever". Populated
        ## at the promotion sites where a WIDTH-TYPED Nim int becomes
        ## `svInt`: `allocateSym`'s `isIntOffset`/`intOffsetPositions` arms,
        ## the top-level param `isIntOffset`/`isLoose`/`isOptimised`
        ## promotion (`runSymexImpl`), the `lIsIntOffsetLocal`
        ## literal-seeded-local proto, the call-arg `formal.isIntOffset`
        ## proto, `coerceIntLit` (propagated from its `proto`), `reconcileInt`
        ## (propagated from a converted BV operand's own width, or kept as-is
        ## from an already-`svInt` operand), and `arithInt`/`iteSV`
        ## (propagated from their operands, so chained arithmetic and
        ## if-expression merges on a promoted value keep the fork alive).
      ziIvl*: Option[Interval]
        ## Issue #161 slice 2. A SOUND over-approximation of the values
        ## this Int term can take on the current path, or `none` for "could
        ## be anything" (the ⊤ of the domain). `lowerArith` uses it to
        ## DISCHARGE the overflow obligation statically: if the composed
        ## result interval provably fits `[low(T), high(T)]`, no fork is
        ## built and Z3 never sees the site.
        ##
        ## The direction of failure is what makes this safe to extend
        ## piecemeal. `none` is Option's zero value, so every `SymVal`
        ## construction that does not think about intervals — and there are
        ## many — gets ⊤ by default, which keeps the obligation LIVE.
        ## Forgetting to propagate an interval therefore costs a redundant
        ## solver fork; it can never delete a defect path. Soundness lives
        ## in `ziWidth` (slice 1's floor); this field is only ever allowed
        ## to make the engine faster.
        ##
        ## Seeded at `promoteSound` params (their declared `range[lo..hi]`)
        ## and at integer literals (the singleton `[v, v]`); propagated by
        ## `arithInt` through chained arithmetic. Everything else — merges,
        ## call returns, field reads, probe misses — is ⊤.
      ziSigned*: bool
        ## Static Nim signedness of the width above; meaningful only when
        ## `ziWidth != 0`. Mirrors the common `signed` field's role for the
        ## BV kinds. `overflowCond`'s svInt sibling only forks when
        ## `ziSigned` is true — Nim wraps UNSIGNED overflow silently (no
        ## `OverflowDefect`), the same rule the BV arm already applies via
        ## its own `signed` guard.
    of svBool: bo*:   Z3Bool
    of svTuple:
      fields*:     seq[SymVal]
      fieldNames*: seq[string]
    of svArray:
      arrElems*:  seq[SymVal]
      arrElemTy*: IRType
    of svString:
      str*: Z3String
      strBuf*: StrBuf   ## RFC-0005 S8ca: whose memory it is (Nim's)
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
      seqUnsupportedFieldReason*: string
        ## N47-followup (walker v110). "" (the default) for a BARE-VALUE
        ## placeholder (a local/param/call-return whose element kind
        ## `isBackedSeqElemTy` declines — `allocateSym`'s `itSeq` arm never
        ## had a `reason` to carry for that origin). Non-empty mirrors
        ## `IRType.seqUnsupportedFieldReason` for a DECLARED-FIELD or
        ## OPERATION-level (e.g. `iekSeqAdd`) placeholder, both of which are
        ## always built via `tUnsupportedFieldSeq`. `placeholderReadDeclineMsg`
        ## uses this — instead of fabricating a generic "nested seq element
        ## type is not supported" claim — whenever it is set, since that
        ## claim is FALSE for an operation-level origin (the element type IS
        ## backed there; only the specific operation's implementation
        ## declined). See `seqUnsupportedFieldKind`'s doc (types.nim).
      seqUnsupportedFieldKind*: SymexErrorKind
        ## N47-followup (walker v110). Mirrors `IRType.seqUnsupportedFieldKind`
        ## alongside the reason above; meaningful only when
        ## `seqUnsupportedFieldReason.len > 0`.
      seqSteps*: int
        ## RFC-0005 S8ar. The heap steps (`refSteps`) of the cell this seq
        ## was read from; an element ref read out of it is that many steps
        ## from a root. 0 for a seq that is not a heap read.
      seqDataMore*: seq[Z3AnyAst]
        ## RFC-0005 S8bc (item 3). A seq whose element is a tree value
        ## (`isTreeSeqElemTy`: a tuple, object, array, case object or
        ## distinct of one) is held LEAF-SPLIT: one `Int -> leaf` data array
        ## per leaf of the element (`heapLeafSuffixes(seqElemTy)`), leaf 0 in
        ## `seqDataRaw` and the rest here, in order. Empty for a scalar
        ## element. Every site that builds a seq from another carries these
        ## (`seqArrs` / `withSeqArrsOf` / `mkSeqSV`); a read rebuilds the
        ## element from the selects of every array (`seqElemAt`), a store
        ## writes every array (`seqStoreArrs`).
    of svTable:
      tabDataRaw*:    Z3AnyAst
      tabDataMore*:   seq[Z3AnyAst]
        ## RFC-0005 S8at. A container value's leaves after the first, one
        ## data array each (`tabValLeaves`); empty for a scalar value.
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
      vImage*:       seq[Z3BitVec[64]]    ## RFC-0016 PRC-07 slice B (c,
                                          ## `--fieldChecks:off` only): the
                                          ## union's bytes, 8 per cell,
                                          ## little-endian; empty = none
      vActive*:      ref SymVal           ## slice B (cpp, `--fieldChecks:off`
                                          ## only): the arm last written, the
                                          ## union's active member; nil = untracked
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
      closureMutCaptures*: seq[string]
                                 ## RFC-0005 S9: the captures Nim holds BY
                                 ## REFERENCE (`lambdaMutCaptures`). Their
                                 ## snapshot in `closureEnv` is refreshed from
                                 ## the current env at every read in the
                                 ## defining frame (`refreshByRefCaptures`).
      closureFrame*: int         ## RFC-0005 S9: `CallFrameCtx.frameId` of the
                                 ## frame that built the closure (-1 outside a
                                 ## walk). Only there do the capture NAMES in
                                 ## the env denote the captured variables.
    of svRef:
      ## Phase 15 Cluster R (R1, ADR-0010). A `Ref_T`-sorted symbolic ref
      ## constant. `refAst` is the uninterpreted-sort const (the abstract
      ## address `p`); `refPointee` carries the pointee type so `tyOf` and the
      ## witness reader can resolve the heap value sort without re-deriving it.
      refAst*:     Z3AnyAst
      refPointee*: IRType   ## Phase 15 R1: the `ref T` pointee type (IRType is
                            ## itself a `ref object`, so no extra boxing).
      refSteps*:   int      ## RFC-0005 S8ar. Heap steps from a root: 0 for a
                            ## parameter, a `new` or `nil`; `k + 1` for a ref
                            ## read out of a cell reached through a `k`-step
                            ## ref. `maxHeapDepth` bounds a deref's step
                            ## (`heapStepOf`), not the number of derefs.
    of svPtr:
      ## Phase 15 Cluster R (R1, ADR-0010). Same model as `svRef` for `ptr T`.
      ## `ptrFamily` marks the pointer family (R8).
      ptrAst*:     Z3AnyAst
      ptrFamily*:  bool
      ptrPointee*: IRType   ## Phase 15 R1: the `ptr T` pointee type.
      ptrSteps*:   int      ## RFC-0005 S8ar. As `refSteps`.
    of svBitSet:
      ## RFC-0005 S8bq. `bsRaw` is a bit-vector of `bitSetDomain(bsElemTy)
      ## .size` bits.
      bsRaw*:    Z3AnyAst
      bsElemTy*: IRType

  VariantAxisSym* = object
    discName*:      string
    disc*:          ref SymVal
    armFields*:     OrderedTable[int, seq[SymVal]]
    armFieldNames*: OrderedTable[int, seq[string]]

  Env* = OrderedTable[string, SymVal]


proc plainEnglishSymValKind*(k: SVKind): string =
  ## Round-6 N12 follow-up. The runtime-layer sibling of
  ## `plainEnglishTypeKind` (`types.nim`) — that helper is the single
  ## translation point for a bare `IRTypeKind` reaching a user-facing
  ## `SymexErrorInfo.msg`; it has no way to translate a bare `SVKind`
  ## (`sv.kind`/`recv.kind`/`refSV.kind`, etc — the WALK-time runtime value's
  ## own kind tag), so classified-decline messages built at walk time were
  ## still leaking internal vocabulary ("svTable", "svUninterpRef", ...)
  ## verbatim. Every classified-decline constructor (`allocDegrade` and the
  ## direct `SymexErrorInfo(...)` builders in `runtime.nim`/`runtime_heap.nim`/
  ## `runtime_strings.nim`, all `include`d into this same module) should route
  ## a SymVal-kind interpolation through here instead of `$sv.kind` directly.
  ## Internal `doAssert`/`raise newException` invariant strings that never
  ## reach `SymexResult.errors` may keep using `$k` freely — same scoping
  ## rule `plainEnglishTypeKind` documents for itself.
  case k
  of svBV8, svBV16, svBV32, svBV64: "fixed-width integer"
  of svInt: "integer"
  of svBool: "bool"
  of svString: "string"
  of svTuple: "tuple value"
  of svArray: "array value"
  of svSeq: "seq value"
  of svTable: "table value"
  of svSet: "set value"
  of svVariant: "variant value"
  of svMultiVariant: "multi-axis variant value"
  of svUninterpRef: "unmodeled reference value"
  of svFloat32: "float32"
  of svFloat64: "float64"
  of svDistinct: "distinct value"
  of svClosure: "closure value"
  of svRef: "ref value"
  of svPtr: "ptr value"
  of svBitSet: "builtin set value"

# ---- SymVal lifting helpers -------------------------------------------------

template liftBV*[W: static int](x: Z3BitVec[W], isSigned: bool): SymVal =
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

proc bvVar*(ty: IRType, name: string): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVecVar[8](name),  ty.signed)
  of 16: liftBV(mkBitVecVar[16](name), ty.signed)
  of 32: liftBV(mkBitVecVar[32](name), ty.signed)
  of 64: liftBV(mkBitVecVar[64](name), ty.signed)
  else:  raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always constructed as 8/16/32/64)]
                            "bvVar: unsupported width " & $ty.width)

proc bvRangeConds*(v: SymVal, lo, hi: int64, signed: bool): seq[Z3Bool] =
  ## Issue #162. The two bound assertions for a BV-allocated `range[lo..hi]`.
  ## Lives here, beside `bvVar`, because `allocateSym` runs long before
  ## `cmpBV`/`lowerBool` are defined and a range bound is not an expression
  ## the walker is lowering — it is a fact about the allocation.
  ##
  ## Signedness comes from the TYPE, matching `cmpBV`'s own split: comparing
  ## an unsigned BV with signed predicates reads `0xFF` as -1 and would
  ## reject a legal value for `range[0'u8..255'u8]`.
  case v.kind
  of svBV8:
    if signed: @[bvsge(v.bv8,  lo), bvsle(v.bv8,  hi)]
    else:      @[bvuge(v.bv8,  lo), bvule(v.bv8,  hi)]
  of svBV16:
    if signed: @[bvsge(v.bv16, lo), bvsle(v.bv16, hi)]
    else:      @[bvuge(v.bv16, lo), bvule(v.bv16, hi)]
  of svBV32:
    if signed: @[bvsge(v.bv32, lo), bvsle(v.bv32, hi)]
    else:      @[bvuge(v.bv32, lo), bvule(v.bv32, hi)]
  of svBV64:
    if signed: @[bvsge(v.bv64, lo), bvsle(v.bv64, hi)]
    else:      @[bvuge(v.bv64, lo), bvule(v.bv64, hi)]
  else:
    # Not reachable from `bvVar`, which returns only the four BV kinds. A
    # non-BV value simply carries no bound assertion: dropping a REFINEMENT
    # can only ever over-approximate the value set, never under-approximate
    # it, so this direction of imprecision cannot delete a path.
    @[]

# ---- the lowering-time degrade sink ---------------------------------------

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

var loweringPendingUb* {.threadvar.}: set[UbKind]
  ## RFC-0016 W1-d3. The undefined behaviours the pending lowering decline
  ## read through, the `loweringPendingTaint` of `Path.undefined`: set and
  ## saved, restored, drained and reset wherever that is. Non-empty implies
  ## `loweringPendingTaint != {}` (the producers also taint).

var loweringPendingTaint* {.threadvar.}: Taint
  ## RFC-0005 S1 (was RFC-chapulin-hardening SND-3's `loweringDidDegrade:
  ## bool`, walker v58, ADR-0023). The PENDING path taint of an in-band
  ## lowering-time degrade: joined (union) by `lowerDegrade` whenever a
  ## lowering site degrades in-band (returns a fresh unconstrained symbol)
  ## instead of `raise`-ing -- `pathTaint(classOf(kind))` of the recorded
  ## kind, so recording and classification share one kind mention. Consumed
  ## EXCLUSIVELY by `drainPendingLowerEffects` — the single choke-point every
  ## `lower()`/`lowerBool()` call site in `walk` already drains through —
  ## which forks the PATH with the pending taint joined in and resets this to
  ## `{}`. It carries no RUN contribution: that is derived at verdict time
  ## from the `loweringDegradeErrors` entry `lowerDegrade` recorded alongside
  ## (RFC-0005 §2.2), so a pending taint that is never drained still forces
  ## the run coordinate. The PATH half, however, can be lost (see
  ## `runtime_heap.nim`'s N42 note: a lost `{scSpurious}` would leave a havoc
  ## value on a clean path), so `stampLoweringPendingLeak` pins this to `{}`
  ## at walk end (RFC-0005 §2.2 last paragraph).
  ## THE reason a lowering-time degrade must NEVER `raise`: on the C backend
  ## (goto exceptions), a raise deep inside expression lowering that unwinds
  ## through a loop's live `seq[Path]` result is SILENTLY LOST (the
  ## b7258f7/CR-1c divergence class) — the walk continues with a mis-lowered
  ## guard, producing a false `sxUnsat` (c) vs. the honest `sxUnknown` (cpp,
  ## whose native exceptions propagate cleanly). In-band taint sidesteps the
  ## raise entirely, so both backends agree.

proc lowerDegrade*(kind: SymexErrorKind; msg: string;
                  ub: set[UbKind] = {}) =
  ## RFC-0005 S1: the LOWERING-sink sibling of `degrade(w, kind, msg)` (which
  ## lives after `WalkCtx`). For sites with no `w: var WalkCtx`/`Path` in
  ## scope — `lower()` and the pure helpers it calls. Performs both acts from
  ## one kind mention: records the classified `sevError` into
  ## `loweringDegradeErrors` (whose drained entry derives the run coordinate)
  ## and joins `pathTaint(classOf(kind))` into `loweringPendingTaint` (which
  ## `drainPendingLowerEffects` turns into the calling path's taint). The
  ## token is delivered through the drain rather than returned, because the
  ## caller has no path to fork.
  loweringDegradeErrors.add SymexErrorInfo(kind: kind, severity: severity(kind),
                                            msg: msg, scope: walkSite())
    # RFC-0005 S8: a lowering decline is recorded by the walk that reached
    # it -- its reach is the record itself (`dskWalkSite`).
  loweringPendingTaint = loweringPendingTaint + pathTaint(classOf(kind))
  loweringPendingUb = loweringPendingUb + ub     # RFC-0016 W1-d3

var rawKeep {.threadvar.}: seq[Z3AnyAst]
  ## RFC-0016 CRH-07. The terms `keepRaw` owns for the run.

proc keepRaw*[T](a: T): RawZ3Ast =
  ## RFC-0016 CRH-07. The raw handle of `a`, valid for the rest of the run.
  ## A proc that returns a raw handle of a term it built returns this: the
  ## `.raw` of its temporary has no owner once the proc returns, and Z3 frees
  ## the node at the next release or call that makes an AST.
  if a.raw.isNil: return a.raw
  rawKeep.add wrap[Z3AnyAst](a.ctx, a.raw)
  rawKeep[^1].raw

proc resetLoweringSink*() =
  ## RFC-0016 review D3c-1. The per-run reset of this module's threadvars,
  ## called from `resetSymexRunState` beside the rest of the run state.
  loweringDegradeErrors = @[]            ## SND-3 (ADR-0023): reset lowering-degrade sink
  loweringPendingUb = {}
  loweringPendingTaint = {}              ## SND-3 (ADR-0023) / RFC-0005 S1: reset per-call pending taint
  rawKeep = @[]                          ## RFC-0016 CRH-07

proc truncBV*(v: SymVal, tgtWidth: int, tgtSigned: bool): SymVal =
  ## RFC-0005 S8i. The low `tgtWidth` bits of a wider BV (C's truncating
  ## integer conversion). `lowerConvIntRange` reaches it only for a value
  ## its range check has confined to the target, where the low bits ARE the
  ## value. `extract`'s bounds are static, so each pair has its own arm.
  case v.kind
  of svBV64:
    case tgtWidth
    of 8:  SymVal(kind: svBV8,  signed: tgtSigned, bv8:  extract(v.bv64, 7, 0))
    of 16: SymVal(kind: svBV16, signed: tgtSigned, bv16: extract(v.bv64, 15, 0))
    else:  SymVal(kind: svBV32, signed: tgtSigned, bv32: extract(v.bv64, 31, 0))
  of svBV32:
    case tgtWidth
    of 8:  SymVal(kind: svBV8,  signed: tgtSigned, bv8:  extract(v.bv32, 7, 0))
    else:  SymVal(kind: svBV16, signed: tgtSigned, bv16: extract(v.bv32, 15, 0))
  of svBV16:
    SymVal(kind: svBV8, signed: tgtSigned, bv8: extract(v.bv16, 7, 0))
  else:
    raiseAssert "truncBV: unsupported operand kind: " & $v.kind

proc mkSeqSV*(len: Z3Int; arrs: seq[Z3AnyAst]; elemTy: IRType): SymVal =
  ## RFC-0005 S8bc. A backed seq value of `elemTy` from its length and its
  ## data arrays (`seqArrs`' order).
  ## RFC-0005 batch 4: the value's element type is the CELL type
  ## (`seqCellTy`, S8ba): a `distinct` element is held as its base, and a
  ## read at the distinct static type re-boxes.
  SymVal(kind: svSeq, seqLen: len, seqDataRaw: arrs[0],
         seqDataMore: arrs[1 .. ^1], seqElemTy: seqCellTy(elemTy))

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(loweringDegradeErrors, loweringPendingUb,
    loweringPendingTaint)

registerThreadStateRelease(releaseThreadState)
