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
## with a `signed: bool` tag for the BV cases (Nim's `int*`/`uint*`
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
    stderr.writeLine "proptest/symex: WARNING — `isLoose` integer semantics " &
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

  SymexOwnershipUnsupportedError* = object of CatchableError
    ## Phase 15 Cluster R (R1a, ADR-0010, Breadth-LOW-L4). Raised when an
    ## `owned T` / `WeakRef[T]` / `Atomic[T]` formal is allocated (classifyType
    ## maps these to an `__ownership:*` placeholder). Caught at the `runSymex`
    ## boundary → `sxUnknown` carrying a `heUnsupportedOwnership` (sevError)
    ## classified error (Invariant 3). These ownership wrappers are out of scope
    ## for the cluster; the diagnostic rides in `msg`.

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
    signed*: bool
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
# immediately above `walk`.
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

template forkPath(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                  uncExpr: bool): Path =
  ## Phase 15 H1: construct a CHILD `Path` from `parent`, deep-copying the
  ## logical-heap state (heaps / heapDepth / allocCounters) so the fork is
  ## isolated. Every fork site in `walk` builds its children through this
  ## template — it is the single enforcement point for the ADR-0010 fork
  ## deep-copy contract. (The fresh ROOT path in `runSymex` does NOT use this:
  ## it has no parent and correctly gets empty-default heap fields.)
  let hs = deepCopyHeapState(parent)
  Path(pc: pcExpr, env: envExpr, uncertain: uncExpr,
       heaps: hs.heaps, heapDepth: parent.heapDepth,
       allocCounters: hs.allocCounters,
       liveRefs: hs.liveRefs,                            ## Phase 15 R2
       freshnessAssertCount: parent.freshnessAssertCount)  ## Phase 15 R2

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
  let child = forkPath(parent, parent.pc, parent.env, parent.uncertain)
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

proc bvVar(ty: IRType, name: string): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVecVar[8](name),  ty.signed)
  of 16: liftBV(mkBitVecVar[16](name), ty.signed)
  of 32: liftBV(mkBitVecVar[32](name), ty.signed)
  of 64: liftBV(mkBitVecVar[64](name), ty.signed)
  else:  raise newException(ValueError,
                            "bvVar: unsupported width " & $ty.width)

proc allocateSeqDataRaw(elemTy: IRType, name: string): Z3AnyAst =
  ## Dispatch on the element type to instantiate `Z3Array[Z3Int, V]`
  ## with the right typed V, then erase via `toAnyAst`. Cycle 1
  ## supports int/bool elements; more arrive incrementally.
  case elemTy.kind
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
    raise newException(ValueError,
      "allocateSeqDataRaw: unsupported element kind " & $elemTy.kind)

proc mkConcreteStrSeq(parts: seq[string]): SymVal =
  ## Phase 15 S5. Build a fully-concrete `svSeq` whose element type is
  ## `string`: a `Z3Array[Z3Int, Z3String]` constant defaulting to the empty
  ## string, with `parts[i]` stored at index `i`, and `seqLen` pinned to the
  ## part count. No free variables and no quantifier — the `split` special
  ## cases (empty-sep / concrete-inline) compute the decomposition in Nim and
  ## hand the literal parts here, so the result is decidable with no string-
  ## solver hang risk. Unstored slots are never read (len-bounded access).
  var arr = mkConstArray[Z3Int, Z3String](mkString(""))
  for i, part in parts:
    arr = store(arr, mkInt(i), mkString(part))
  SymVal(kind: svSeq, seqLen: mkInt(parts.len),
         seqDataRaw: toAnyAst(arr), seqElemTy: tString())

proc joinStrSeq(parts: SymVal, sep: Z3String): Z3String =
  ## Phase 15 S5. Lower `xs.join(sep)` over a CONCRETE-length `svSeq[string]`
  ## to a Z3 concat chain with `sep` interleaved:
  ##   join(@[p0,p1,…,pn], sep) == p0 ++ sep ++ p1 ++ … ++ sep ++ pn
  ## The seq length must be a Z3 numeral (concrete) so the chain is finite;
  ## the split special cases guarantee that.
  doAssert parts.kind == svSeq and parts.seqElemTy.kind == itString,
    "joinStrSeq: not an svSeq[string]"
  let n = parseInt(getNumeralString(parts.seqLen))
  let typed = wrap[Z3Array[Z3Int, Z3String]](
    parts.seqDataRaw.ctx, parts.seqDataRaw.raw)
  if n <= 0:
    return mkString("")
  result = select(typed, mkInt(0))
  for i in 1 ..< n:
    result = concat(result, sep)
    result = concat(result, select(typed, mkInt(i)))

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

var currentHeapDerefVals* {.threadvar.}: Table[string, SymVal]
  ## Phase 15 R1 (ADR-0010, C7/Breadth-CRIT-1). The MINIMAL R1 witness reader
  ## hook: when a `ref T`/`ptr T` PARAM `p` is dereferenced, the heap-select
  ## value (`select(heap, p)`) is recorded here keyed by the param name, so the
  ## witness for `p` renders the dereffed value (the value `p[]` takes in the
  ## model) rather than a silent empty leaf. `extractFromSymVal(svRef/svPtr)`
  ## consumes it. (The full heap-snapshot witness format — `pointsTo`/`aliasRef`
  ## per ADR-0010 §Heap witness invariants — lands R11b/R12; R1 needs only a
  ## sound scalar reader for the `ref int` DoD.) Reset at `runSymexImpl` entry.

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

proc seedCallerHeapThreadvars*(p: Path) {.inline.} =
  ## Phase 15 R1b. Mirror a path's logical-heap state into the caller-heap
  ## threadvars so a CLOSURE call lowered out of `p.env` (no `Path` in scope)
  ## descends with the caller's threaded heap (ADR-0010 R1b). Mirrors the
  ## `setInFlightThreadvars` (E8) / `currentWalkCtxPtr` (C2b) idiom.
  currentCallerHeaps = p.heaps
  currentCallerHeapDepth = p.heapDepth
  currentCallerAllocCounters = p.allocCounters

proc refPointeeTypeId*(pointeeTy: IRType): string =
  ## Phase 15 R1. A stable per-pointee-type identifier used to key the `Ref_T`
  ## sort + heap array + nil const. `$pointeeTy` is already a stable structural
  ## rendering (see `types.$`); sanitise the characters Z3's symbol grammar
  ## dislikes so `"Ref_" & typeId` is a clean sort name.
  result = $pointeeTy
  for i in 0 ..< result.len:
    if result[i] notin {'a'..'z', 'A'..'Z', '0'..'9', '_'}:
      result[i] = '_'

proc allocRefSort*(ctx: Z3Context, pointeeTy: IRType): RawZ3Sort =
  ## Phase 15 R1 (ADR-0010). Return the per-walker `Ref_<typeId>` uninterpreted
  ## sort for `pointeeTy`, allocating + caching it (and its `nil_<typeId>` const)
  ## on first use. Idempotent per (typeId, run) via `currentRefSorts`.
  ##
  ## G4 footgun discipline: pin the fresh sort with a `Z3_inc_ref` over its
  ## `Z3_sort_to_ast` — otherwise the heavy heap/const allocation that follows
  ## lets Z3 garbage-collect the un-referenced sort, corrupting every array
  ## sort / const that names it (the G4 SIGSEGV: the sort read back as
  ## `Z3_UNKNOWN_SORT`). The ref is held for the whole run (never dec'd — the
  ## context is torn down at run end).
  let typeId = refPointeeTypeId(pointeeTy)
  if not currentRefSorts.hasKey(typeId):
    let sortName = "Ref_" & typeId
    let sort = mkUninterpretedSort(ctx, sortName)
    Z3_inc_ref(ctx.raw, Z3_sort_to_ast(ctx.raw, sort.raw))
    currentRefSorts[typeId] = sort.raw
    # The distinguished `nil_<typeId>` constant of this ref sort (ADR-0010 §Nil).
    let nilSym = ctx.checkErr Z3_mk_string_symbol(ctx.raw,
      ("nil_" & typeId).cstring)
    let nilRaw = ctx.checkErr Z3_mk_const(ctx.raw, nilSym, sort.raw)
    currentNilConsts[typeId] = wrap[Z3AnyAst](ctx, nilRaw)
  currentRefSorts[typeId]

proc rawConstOf(ctx: Z3Context, sort: RawZ3Sort, name: string): RawZ3Ast
  ## Phase 15 R2: forward decl (defined below) — `freshRef` mints its fresh
  ## `Ref_T` const through it before its definition appears.

proc freshRef*(ctx: Z3Context, refSort: RawZ3Sort, typeId: string,
               path: Path): Z3AnyAst =
  ## Phase 15 R2 (ADR-0010). Mint a FRESH `Ref_T`-sorted const for a `new T`
  ## allocation on `path`. Increment the per-path `allocCounters[typeId]` (R1b
  ## already threads + max-merges this across call boundaries, so the counter
  ## is monotone along a path and a post-call caller alloc can't collide with a
  ## callee one) and derive a const named `"ref_<typeId>_<n>"` (n = the NEW
  ## counter value) via the raw `Z3_mk_const` discipline (G4 — `allocateSym`
  ## has no typed phantom for a runtime-known uninterpreted sort). The caller
  ## (`walk(isNew)`) binds the result in the env and calls `assertFreshness`.
  let n = path.allocCounters.getOrDefault(typeId, 0) + 1
  path.allocCounters[typeId] = n
  let name = "ref_" & typeId & "_" & $n
  wrap[Z3AnyAst](ctx, rawConstOf(ctx, refSort, name))

proc assertFreshness*(ctx: Z3Context, path: Path, typeId: string,
                      newRef: Z3AnyAst, settings: SymexSettings) =
  ## Phase 15 R2 (ADR-0010). Constrain a freshly allocated `newRef` to be
  ## DISTINCT from `nil` and from every PRIOR live ref of this pointee type on
  ## `path` (the counter-based distinctness guarantee). All GROUND inequalities
  ## (`Z3_mk_eq` negated) — NEVER a universal-∀ over the uninterpreted ref sort
  ## (the G4 MBQI hang lesson). Prior live refs are read from
  ## `path.liveRefs[typeId]`; `newRef` is appended after.
  ##
  ## The `newRef != nil` pin is ALWAYS emitted (a single assertion — a fresh
  ## allocation is never nil). The pairwise `newRef != prior` inequalities are
  ## CAPPED: once `path.freshnessAssertCount` would exceed
  ## `settings.maxFreshnessAssertions` (0 = unlimited) the remaining
  ## inequalities are SKIPPED and a `heFreshnessCapExceeded` (sevHint) is
  ## emitted ONCE for this `new T`. This is a SOUND over-approximation — Z3 may
  ## then allow `newRef` to alias an un-asserted prior ref, which is
  ## conservative (more models), never a false UNSAT.
  template mkNeq(a, b: Z3AnyAst): Z3Bool =
    not wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_eq(ctx.raw, a.raw, b.raw))
  # 1. newRef != nil (always — not pairwise, not capped).
  if currentNilConsts.hasKey(typeId):
    path.pc.add mkNeq(newRef, currentNilConsts[typeId])
  # 2. newRef != every prior live ref of this sort on THIS path (capped).
  let priors = path.liveRefs.getOrDefault(typeId, @[])
  let cap = settings.maxFreshnessAssertions
  var capHitThisAlloc = false
  for prior in priors:
    if cap > 0 and path.freshnessAssertCount >= cap:
      capHitThisAlloc = true
      break
    path.pc.add mkNeq(newRef, prior)
    inc path.freshnessAssertCount
  if capHitThisAlloc:
    freshnessCapHints.add SymexErrorInfo(
      kind: heFreshnessCapExceeded, severity: sevHint,
      msg: "freshness-assertion cap (" & $cap & ") reached on this path for " &
           "ref type `" & typeId & "`: distinctness inequalities for further " &
           "`new T` allocations are skipped (sound over-approximation — Z3 may " &
           "allow aliasing beyond the cap, never a false UNSAT)")
  # 3. Record `newRef` as a live ref for subsequent allocations on this path.
  if path.liveRefs.hasKey(typeId):
    path.liveRefs[typeId].add newRef
  else:
    path.liveRefs[typeId] = @[newRef]

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

var currentClosureCallAxiomStrs* {.threadvar.}: seq[string]
  ## Phase 15 C2b test hook. The SMT-LIB rendering (`Z3_ast_to_string`) of each
  ## asserted closure-call axiom, captured WHILE the Z3 context is live (a raw
  ## `Z3Bool` handle outlives its context as a dangling pointer, so a test must
  ## not stringify `currentClosureCallAxioms` after the run). Lets a test assert
  ## the GROUND multi-return-path encoding — both `=>` arms, no `forall`. Reset
  ## at `runSymexImpl` entry.

var currentClosureCallErrors* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 C2b. Classified closure-call failures accumulated during lowering
  ## (`ceClosureUnknownCallee`, `ceInlineBudgetExceeded`) — `lower` has no
  ## WalkCtx to push onto `w.sawUnknown`/findings, so they ride this sink and are
  ## drained into the finding's errors (and force `sxUnknown`) at the SUT
  ## boundary. Reset at `runSymexImpl` entry. (The `unknownExnWarnings` idiom.)

var currentWalkCtxPtr* {.threadvar.}: pointer
  ## Phase 15 C2b. A `ptr WalkCtx` to the live walk, set in `runSymexImpl`
  ## immediately before the top-level `walk` so `lowerClosureCall` (running in
  ## the `lower` evaluator, which has no `WalkCtx` parameter) can drive a body
  ## descent through `walk`. Typed `pointer` because `WalkCtx` is declared far
  ## below `lower`; cast back at use. Nil outside an active walk (the C2a probes
  ## and `c1ClosurePoCApply` never set it — they don't reach `iekClosureCall`).

proc lowerClosureCall(env: Env, e: IRExpr): SymVal
  ## Phase 15 C2b fwd-decl. Defined AFTER `walk` (it descends the lambda body
  ## via `walk`), called from `lower(iekClosureCall)` (defined before `walk`).

proc lowerSeqLit(env: Env, e: IRExpr): SymVal
  ## Phase 15 C4 fwd-decl. Concrete seq-literal `@[..]` → concrete-length svSeq.

proc lowerHofCall(env: Env, e: IRExpr): SymVal
  ## Phase 15 C4 fwd-decl. Defined AFTER `walk` (the inline path applies the
  ## closure per element via the C2b descent), called from `lower(iekHofCall)`.

proc allocateSym(ty: IRType, baseName: string,
                 pcOut: var seq[Z3Bool]): SymVal   ## fwd-decl (mutual: itDistinct)

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

proc sortFingerprint(sorts: openArray[RawZ3Sort]): string =
  ## A stable per-context fingerprint of a sort list (the `Z3_get_sort_id`s,
  ## joined). Used to key the closure funcSym memo so the SAME lambda site at
  ## two monomorphizations (distinct leaf/param sorts) gets distinct funcSyms
  ## (ADR-0009 D8). Sort ids are monotone+unique within a context.
  let ctx = requireCurrentContext()
  var parts: seq[string]
  for s in sorts: parts.add $sortId(ctx, s)
  parts.join(",")

proc paramSorts(params: seq[IRParam]): seq[RawZ3Sort] =
  ## The Z3 sorts of a lambda's parameters. A throwaway representative SymVal is
  ## allocated per param to read its sort (G4 `baseRep` pattern — the init
  ## constraints are discarded; the decl only needs the sort).
  let ctx = requireCurrentContext()
  for p in params:
    var scratchPC: seq[Z3Bool]
    let rep = allocateSym(p.ty, "__closureParamSort." & p.name, scratchPC)
    for s in sortOfTuple(rep): result.add s

proc buildClosure(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C2a (ADR-0009 D1/D2/D4). Construct an `svClosure` from an
  ## `iekLambda`:
  ##   1. Snapshot the captured locals: look each `lambdaCaptures` name up in the
  ##      CURRENT env, collect the SymVals → an `svTuple` `envRecord` (the env
  ##      snapshot). NO body descent — the lambda body is NOT lowered here.
  ##   2. Get-or-create the per-site uninterpreted `funcSym`, memoized in the
  ##      `currentClosureSyms` threadvar keyed by `((siteHash, declOrder),
  ##      envSortId, paramsSortTupleId)`. Domain = flattened env leaf sorts ++
  ##      param sorts (the C1 PoC pattern, D2); range = `lambdaRetTy`'s sort.
  ##   3. Build `svClosure{closureSite, closureEnv, closureRawFD}`.
  ## (`lower` has no `WalkCtx`, so the memo lives on a threadvar — the G4
  ## `currentDistinctSorts` idiom.)
  let ctx = requireCurrentContext()
  # 1. Env snapshot: captured locals (in capture order) → svTuple.
  var capVals: seq[SymVal]
  var capNames: seq[string]
  for name in e.lambdaCaptures:
    if env.hasKey(name):
      capVals.add env[name]
      capNames.add name
    # A capture missing from the current env is dropped from the snapshot (it
    # was a body-local or a name the walker never bound symbolically); the
    # funcSym domain follows the snapshot, so this stays consistent.
  let envRecord = SymVal(kind: svTuple, fields: capVals, fieldNames: capNames)
  # Phase 15 C3: a no-capture lambda (a top-level proc-as-value, lambdaCaptures
  # == @[]) materializes a ZERO-field svTuple unitEnv — the snapshot must have
  # collected nothing. (Belt-and-braces: a capture present in lambdaCaptures but
  # absent from the env is dropped above, so the invariant is "empty captures ⇒
  # empty env", checked only on the no-capture path.)
  if e.lambdaCaptures.len == 0:
    doAssert envRecord.fields.len == 0,
      "buildClosure: no-capture lambda (unit-env, C3) must have a zero-field " &
      "env, got " & $envRecord.fields.len & " fields"
  # 2. Get-or-create the per-site funcSym.
  let envLeafSorts = sortOfTuple(envRecord)
  let pSorts = paramSorts(e.lambdaParams)
  let key: ClosureSymKey = (siteHash: e.lambdaSite.siteHash,
                            declOrder: e.lambdaSite.declOrder,
                            envSortId: sortFingerprint(envLeafSorts),
                            paramsSortTupleId: sortFingerprint(pSorts))
  var fd: RawZ3FuncDecl
  if currentClosureSyms.hasKey(key):
    fd = currentClosureSyms[key]
  else:
    # Domain = flattened env leaf sorts ++ param sorts (D2); range = retTy sort.
    var domain = envLeafSorts
    for s in pSorts: domain.add s
    var retPC: seq[Z3Bool]
    let retRep = allocateSym(e.lambdaRetTy, "__closureRet", retPC)
    let rangeSorts = sortOfTuple(retRep)
    doAssert rangeSorts.len == 1,
      "buildClosure: closure return type must be a single-leaf sort, got " &
      $rangeSorts.len & " leaves"
    let rangeSort = rangeSorts[0]
    let fname = "closure@" & $e.lambdaSite.siteHash & "/" &
                $e.lambdaSite.declOrder
    let fsym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, fname.cstring)
    # `Z3_mk_func_decl` over the runtime-known sorts (G4 raw-FFI discipline:
    # domains are a HEAP seq; the decl is inc-ref'd for the run's lifetime). A
    # zero-arity domain (no captures, no params) passes a nil ptr.
    let domPtr = if domain.len > 0:
                   cast[ptr UncheckedArray[RawZ3Sort]](addr domain[0])
                 else: nil
    fd = ctx.checkErr Z3_mk_func_decl(ctx.raw, fsym, cuint(domain.len),
      domPtr, rangeSort)
    incRefFD(ctx, fd)
    currentClosureSyms[key] = fd
  # 3. Stash the lambda body + signature so the CALL (C2b) can descend it —
  # `svClosure` carries the site key + env + funcSym, but NOT the body IR. The
  # site is the reach-back key (ADR-0009 D6: the body is descended at apply).
  currentClosureBodies[(e.lambdaSite.siteHash, e.lambdaSite.declOrder)] =
    ClosureBody(body: e.lambdaBody, params: e.lambdaParams,
                captures: capNames, retTy: e.lambdaRetTy)
  # 4. Assemble the svClosure.
  var boxedEnv = new(SymVal)
  boxedEnv[] = envRecord
  SymVal(kind: svClosure,
         closureSite: e.lambdaSite,
         closureEnv: boxedEnv,
         closureRawFD: fd)

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
      currentDistinctSorts[name] = DistinctSortEntry(
        sort: sort, inject: inject, eject: eject)
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
      currentDistinctSorts[name] = DistinctSortEntry(
        sort: sort, inject: inject, eject: eject)
      distinctBijectivityHints.add SymexErrorInfo(
        kind: geDistinctBijectivitySkipped, severity: sevHint,
        msg: "bijectivity axiom skipped for distinct `" & name &
             "` over non-decidable base " & $ty.distinctBase.kind &
             " (FP/String): the distinct sort is modeled without the " &
             "inject/eject round-trip guarantee")
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

proc allocateSym(ty: IRType, baseName: string,
                 pcOut: var seq[Z3Bool]): SymVal =
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
    proc discEq(d: SymVal, tagOrd: int64): Z3Bool =
      case d.kind
      of svBV8:  d.bv8  == mkBitVec[8](tagOrd)
      of svBV16: d.bv16 == mkBitVec[16](tagOrd)
      of svBV32: d.bv32 == mkBitVec[32](tagOrd)
      of svBV64: d.bv64 == mkBitVec[64](tagOrd)
      of svInt:  d.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
      of svBool: d.bo   == mkBool(tagOrd != 0)  ## Phase 15 F9c: bool disc (false=0, true=1)
      else:
        raise newException(ValueError,
          "symex Phase 14: variant discriminator must be a BV or " &
          "Z3Int kind (got " & $d.kind & ")")
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
      armEqClauses.add discEq(discInner, int64(arm.tagOrdinal))
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
        armEqClauses.add discEq(discInner, int64(dt.ord))
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
    bvVar(ty, baseName)
  of itBool:
    SymVal(kind: svBool, bo: mkBoolVar(baseName))
  of itString:
    # Phase 15 S3: byte-faithful ≤0xFF char-range constraint (ADR-0006). This is
    # the soundness mechanism: without it Z3 may pick full-Unicode codepoints
    # (0..0x2FFFF) that occupy one Z3 position but multiple Nim bytes, so a
    # witness extracted via `evalStr` would not round-trip to a Nim string of the
    # same length/content. We assert that the free string is a member of
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
      raise newException(ValueError,
        "Phase 5 cycle 5: unsupported Table value " & $ty.tabValTy)
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
      raise newException(ValueError,
        "Phase 5 cycle 8: unsupported HashSet element type " & $ty.setElemTy)

# ---- Phase 15 R1: logical-heap array helpers (ADR-0010) ----------------------
# These build/read the per-path `Z3Array[Ref_T, T_sym]` heap. They follow
# `allocateSym` because `heapValueSort` allocates a throwaway pointee SymVal to
# read its value sort (the G4 `baseRep` sort-probe idiom).

proc heapValueSort(ctx: Z3Context, pointeeTy: IRType): RawZ3Sort =
  ## Phase 15 R1. The Z3 value sort of the heap array `Z3Array[Ref_T, T_sym]`
  ## for pointee type `pointeeTy` — i.e. the sort of the SymVal a deref yields.
  ## A throwaway prototype is allocated (its init constraints are discarded —
  ## only the sort is read), mirroring G4's `baseRep` sort probe.
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(pointeeTy, "__heapValSort", scratchPC)
  ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(proto))

proc mkHeapArrayVar(ctx: Z3Context, refSort: RawZ3Sort,
                    pointeeTy: IRType, name: string): Z3AnyAst =
  ## Phase 15 R1 (ADR-0010). Build a FREE `Z3Array[Ref_T, T_sym]` variable —
  ## the initial heap for one pointee type on one path. The key sort `Ref_T`
  ## is a RUNTIME uninterpreted sort, so the typed `mkArrayVar[K, V]` (which
  ## needs static K/V) cannot express it; we go through raw FFI
  ## (`Z3_mk_array_sort` + `Z3_mk_const`) and erase to `Z3AnyAst`. The result
  ## is a GROUND free array — every `select` on it is decidable (QF_AUFLIA-ish);
  ## NO universal-∀ axiom is ever asserted over the uninterpreted sort (the G4
  ## hang lesson).
  let valSort = heapValueSort(ctx, pointeeTy)
  let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, valSort)
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc liftHeapValue(ctx: Z3Context, valRaw: RawZ3Ast, pointeeTy: IRType): SymVal =
  ## Phase 15 R1. Wrap the raw value-sorted ast produced by a heap `select`
  ## into the SymVal variant for `pointeeTy`, so the dereffed value flows back
  ## into the ordinary `lower`/`symEq`/binop machinery. R1 covers the primitive
  ## pointees the heap-select can yield directly (int/bool/float); composite
  ## pointees (`ref object`, `seq[ref T]`) land R3+.
  case pointeeTy.kind
  of itInt:
    case pointeeTy.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, valRaw),  pointeeTy.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, valRaw), pointeeTy.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, valRaw), pointeeTy.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, valRaw), pointeeTy.signed)
    else:
      raise newException(ValueError,
        "liftHeapValue: unsupported int width " & $pointeeTy.width)
  of itBool:   ofBool(wrap[Z3Bool](ctx, valRaw))
  of itFloat32: SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, valRaw))
  of itFloat64: SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, valRaw))
  else:
    raise (ref SymexRefUnresolvedError)(
      msg: "deref of `ref/ptr " & $pointeeTy & "` (non-primitive pointee) " &
           "not yet modeled (Cluster R R1 covers primitive pointees; " &
           "composite pointees — ref object / seq[ref T] — land R3+)")

proc heapSelect(ctx: Z3Context, heap: Z3AnyAst, refAst: Z3AnyAst,
                pointeeTy: IRType): SymVal =
  ## Phase 15 R1 (ADR-0010). The GROUND heap read `select(heap, p)` — a single
  ## `Z3_mk_select` over the free heap array at the abstract address `p`. The
  ## result is the value-sorted ast; lift it into a SymVal. This is the whole
  ## of R1's deref: a decidable array select, NO quantifier (the G4 lesson —
  ## a ∀ over the uninterpreted Ref_T sort would HANG Z3).
  let valRaw = ctx.checkErr Z3_mk_select(ctx.raw, heap.raw, refAst.raw)
  liftHeapValue(ctx, valRaw, pointeeTy)

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
  of iekStrFind, iekStrFindRe, iekStrToInt:
    # Phase 15 S4/S6b/S10a: `s.find(sub)` / `s.find(re"…")` / `parseInt(s)` → Z3Int.
    # svInt sentinel so a surrounding comparison (e.g. `s.find("bc") == 1`,
    # `parseInt(s) == 42`) lowers its literal as a Z3Int. (iekStrFindRe's lower()
    # raises a deferral; the proto keeps a surrounding `>= 0` comparison's literal
    # side well-typed.)
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekIntToStr, iekStrReplace, iekStrReplaceAll, iekStrReplaceRe, iekStrJoin, iekStrConcat:
    # Phase 15 S5/S8/S10a: replace/replaceAll/join/concat/`$int` all produce a
    # Z3String. svString sentinel so `s.replace(...) == "lit"` / `xs.join(sep) ==
    # "lit"` / `$n == "42"` lowers its literal as a string and dispatches through
    # cmpString. (replaceAll's version-gate raise happens in lower(), not here —
    # probeProto must still return a string proto so the literal side is lowered.)
    some(SymVal(kind: svString, str: mkString("")))
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrReplace, iekStrReplaceAll, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe, iekStrConcat,
                   iekIntToStr, iekStrToInt}:
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
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekMathCall:
    # Phase 15 F6: predicates produce svBool; float ops produce a float of
    # the first arg's width; deferred ops have no proto (they raise on lower).
    if e.mathOp in ["signbit", "isNaN", "isInf", "isFinite", "isNormal"]:
      some(SymVal(kind: svBool, bo: mkBool(false)))
    elif e.mathOp in ["abs", "sqrt", "min", "max",
                      "floor", "ceil", "round", "trunc"]:
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

# ---- IR-expr → SymVal -------------------------------------------------------

var currentMaxBytesEncodingLen* {.threadvar.}: int
  ## Phase 15 S7a. The active `SymexSettings.maxBytesEncodingLen`, set at the
  ## top of `runSymexImpl` so the `iekStrBytes` arm in `lower` (which has no
  ## settings parameter) can read the cap without threading settings through
  ## the whole expression-lowering recursion. Mirrors F7's `extractionErrors`
  ## threadvar.

var parseIntGateConstraints* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 S10a. Side soundness-gate constraints emitted by the `iekStrToInt`
  ## (`parseInt`) lowering — `toInt(s) >= 0` on the active digits/negative branch
  ## (the digits gate from Z3's `Z3_mk_str_to_int`, which is `>= 0` for digit
  ## strings). `lower` has no path-condition sink (Env is a pure value table), so
  ## these accumulate here and are drained into EVERY solver check (`trySolve`).
  ## That is sound: each clause references the specific param string var's Z3 AST,
  ## which is identical across paths, and the gate only narrows non-digit models.
  ## Mirrors F7's `extractionErrors` / S7a's `currentMaxBytesEncodingLen` threadvars.

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

proc lowerMathCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 F6. Lower a std/math float op or FP predicate to its
  ## Z3-FP-native ast. Symmetric over svFloat32 / svFloat64. Deferred and
  ## unmodeled ops raise `SymexUnsupportedOpError` (caught at the runSymex
  ## boundary -> sxUnknown + feUnsupportedOp; never a silent UNSAT).
  let op = e.mathOp
  if e.mathArgs.len == 0:
    raise (ref SymexUnsupportedOpError)(op: "math." & op,
      msg: "math." & op & ": zero-arg float op is unsupported")
  let a = lower(env, e.mathArgs[0])
  doAssert a.kind in {svFloat32, svFloat64},
    "lowerMathCall: first arg is not a float — got " & $a.kind

  # ----- predicates (return svBool), width-symmetric -----
  template pred(call: untyped): SymVal =
    if a.kind == svFloat32: ofBool(call(a.fp32)) else: ofBool(call(a.fp64))
  case op
  of "signbit": return pred(isNegative)
  of "isNaN":   return pred(isNaN)
  of "isInf":   return pred(isInf)
  of "isFinite":return pred(isFinite)
  of "isNormal":return pred(isNormal)
  else: discard

  # ----- unary float -> float ops -----
  template f32(v: untyped): SymVal = SymVal(kind: svFloat32, fp32: v)
  template f64(v: untyped): SymVal = SymVal(kind: svFloat64, fp64: v)
  case op
  of "abs":
    return (if a.kind == svFloat32: f32(abs(a.fp32)) else: f64(abs(a.fp64)))
  of "sqrt":
    return (if a.kind == svFloat32: f32(sqrt(rmRNE(), a.fp32))
            else: f64(sqrt(rmRNE(), a.fp64)))
  of "floor":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTN(), a.fp32))
            else: f64(roundToIntegral(rmRTN(), a.fp64)))
  of "ceil":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTP(), a.fp32))
            else: f64(roundToIntegral(rmRTP(), a.fp64)))
  of "round":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRNE(), a.fp32))
            else: f64(roundToIntegral(rmRNE(), a.fp64)))
  of "trunc":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTZ(), a.fp32))
            else: f64(roundToIntegral(rmRTZ(), a.fp64)))
  of "min", "max":
    doAssert e.mathArgs.len == 2, "math." & op & " expects two args"
    let b = lower(env, e.mathArgs[1])
    doAssert b.kind == a.kind, "math." & op & ": float-width mismatch"
    if op == "min":
      return (if a.kind == svFloat32: f32(min(a.fp32, b.fp32))
              else: f64(min(a.fp64, b.fp64)))
    else:
      return (if a.kind == svFloat32: f32(max(a.fp32, b.fp32))
              else: f64(max(a.fp64, b.fp64)))
  else:
    # Deferred (classify/copySign/nextafter) or any unmodeled math.<name>.
    raise (ref SymexUnsupportedOpError)(op: "math." & op,
      msg: "math." & op & " is not modeled by the symex engine (Phase 16 backlog)")

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

proc toBv64ForFp(sv: SymVal): Z3BitVec[64] =
  ## Phase 15 F5: obtain the 64-bit bit pattern of an integer SymVal
  ## directly for an int->float conversion, WITHOUT round-tripping
  ## through the Z3 mathematical-Int sort.
  ##
  ## The earlier form `intToBv[64](toZ3Int(sv), ...)` emitted
  ## `int2bv(bv2int(x))` for a BV operand. That sandwich mixes the
  ## Int + BV + FP theories in one query: trivial for an equality
  ## goal (Z3 guesses a model), but pathological for an ordering goal
  ## (e.g. `float(x) > 1.5`), where Z3 never terminates. Operating on
  ## the bitvector directly keeps the query in QF_BVFP, which Z3 solves
  ## by bit-blasting. Narrower ints are sign-/zero-extended per signedness.
  case sv.kind
  of svBV64: sv.bv64
  of svBV32: (if sv.signed: signExtend(sv.bv32, 32) else: zeroExtend(sv.bv32, 32))
  of svBV16: (if sv.signed: signExtend(sv.bv16, 48) else: zeroExtend(sv.bv16, 48))
  of svBV8:  (if sv.signed: signExtend(sv.bv8, 56)  else: zeroExtend(sv.bv8, 56))
  of svInt:  intToBv[64](sv.zi, Z3BitVec[64])   # genuine unbounded Int: last resort
  else:
    raise newException(ValueError,
      "float(): operand is not an integer — got " & $sv.kind)

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
    # Phase 15 R1a STUB. Ref/ptr path-merge (an `ite` over the two `Ref_T`
    # consts) lands R5+ (nil-fork) / R7 (alias merge). Never reached in R1a (the
    # walker stubs before any svRef/svPtr is constructed).
    raise newException(ValueError,
      "iteSV: svRef/svPtr merge lands with Cluster R R5/R7")

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
  else:
    raise newException(ValueError,
      "retBindEq: composite-typed proc return not yet wired — got " &
      $retSym.kind)

proc freshRetSym(ty: IRType, name: string, pcOut: var seq[Z3Bool]): SymVal =
  ## Phase 15 G3: allocate a fresh, well-typed symbol for a call's return
  ## value. Replaces the old `bvVar`-only allocation (which asserted
  ## `itInt`) at every call-return site so a generic — or any proc —
  ## returning a `float`/`string`/composite type gets a correctly-typed
  ## placeholder instead of crashing on the int assertion. Routes through
  ## the existing type-aware `allocateSym`; any init-side constraints (the
  ## string byte-range floor, seq-len floor, …) are threaded into `pcOut`.
  allocateSym(ty, name, pcOut)

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

proc mkFloatLitSym(v: float64, width: int): SymVal =
  ## Phase 15 F2: lower a float literal to a Z3 FP numeral, honoring
  ## NaN / ±Inf / -0.0 (ADR-0005) via Nim's `classify`.
  let cls = classify(v)
  if width == 32:
    SymVal(kind: svFloat32, fp32:
      (case cls
       of fcNan:     mkFpNaN[8, 24]()
       of fcInf:     mkFpInf[8, 24](false)
       of fcNegInf:  mkFpInf[8, 24](true)
       of fcNegZero: mkFpZero[8, 24](true)
       else:         mkFloat32(float32(v))))
  else:
    SymVal(kind: svFloat64, fp64:
      (case cls
       of fcNan:     mkFpNaN[11, 53]()
       of fcInf:     mkFpInf[11, 53](false)
       of fcNegInf:  mkFpInf[11, 53](true)
       of fcNegZero: mkFpZero[11, 53](true)
       else:         mkFloat64(v)))

proc cmpFloat(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 F2: IEEE equality via Z3 FP theory (`==`/`!=` on Z3Fp are
  ## IEEE, so NaN == NaN is false). F4 adds ordering (`<` `<=` `>` `>=`).
  doAssert a.kind == b.kind and a.kind in {svFloat32, svFloat64}
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
  ## via Z3 `str.<`) lands in S3; until then ordering ops raise a classified
  ## unsupported-string-op error rather than mis-dispatching to BV compare.
  doAssert a.kind == svString and b.kind == svString
  case op
  of bEq: ofBool(a.str == b.str)
  of bNe: ofBool(a.str != b.str)
  else:
    raise (ref SymexUnsupportedStringOpError)(op: $op,
      msg: "string ordering `" & $op & "` is not modeled until S3")

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

proc lower(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal =
  if e == nil:
    raise newException(ValueError, "lower: nil expression")
  case e.kind
  of iekIntLit:
    if proto.isSome and proto.get.kind != svBool:
      coerceIntLit(proto.get, e.ival)
    else:
      bvConst(tInt(64, true), e.ival)
  of iekFloatLit:
    mkFloatLitSym(e.fval, e.fwidth)
  of iekConvIntToFloat:
    # Phase 15 F5: int -> float. signed-bv -> fp (rmRNE, OQ2). The operand
    # is already a bitvector; `toBv64ForFp` takes its 64-bit pattern directly
    # rather than via `int2bv(bv2int(x))` (which hangs Z3 on ordering goals).
    let sv = lower(env, e.convOperand)
    let bv64 = toBv64ForFp(sv)
    if e.convWidth == 32:
      SymVal(kind: svFloat32, fp32: toFpFromSigned(rmRNE(), bv64, Z3Float32))
    else:
      SymVal(kind: svFloat64, fp64: toFpFromSigned(rmRNE(), bv64, Z3Float64))
  of iekConvFloatToInt:
    # Phase 15 F5: float -> int, rmRTZ truncation (OQ2). In-range is exact;
    # out-of-range overflow -> sxRaised(RangeDefect) is deferred to post-cluster-E
    # (sxRaised does not exist yet) — a documented unsoundness window.
    let sv = lower(env, e.convOperand)
    let bv64 =
      case sv.kind
      of svFloat64: toSbv[11, 53, 64](rmRTZ(), sv.fp64)
      of svFloat32: toSbv[8, 24, 64](rmRTZ(), sv.fp32)
      else: raise newException(ValueError, "int(): operand is not a float")
    SymVal(kind: svInt, zi: bvToZ3Int(SymVal(kind: svBV64, bv64: bv64, signed: true)))
  of iekMathCall:
    lowerMathCall(env, e)
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
    else:
      raise newException(ValueError,
        "iekSeqLen on non-container kind=" & $recv.kind)
  of iekStrLit:
    SymVal(kind: svString, str: mkString(e.sval))
  of iekStrLen:
    # Phase 15 S3. `s.len` → Z3 `(str.len s)`. Under the ≤0xFF byte-faithful
    # constraint (asserted at allocation, ADR-0006) the Z3 character count
    # equals the Nim byte length, so this is exact.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrLen: receiver not svString"
    SymVal(kind: svInt, zi: len(recv.str))
  of iekStrAt:
    # Phase 15 S3. `s[i]` (read) → a Nim `char` (svBV8 unsigned). The Z3 bridge:
    # `at(s, i)` is a 1-char Z3String; `toCode(.)` is its codepoint as Z3Int,
    # which under ≤0xFF is exactly the byte value 0..255 (== Nim byte index ==
    # Z3 position). We narrow that Z3Int to a BV8 char. Out-of-range `i` makes
    # `at` the empty string and `toCode` returns -1 (→ BV8 0xFF); per Z3 spec we
    # do not crash. `char` classifies (Z3c) to unranged tInt(8, unsigned), i.e.
    # svBV8 — so `s[i] == 'c'` compares two svBV8 values via the existing path.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrAt: receiver not svString"
    let idx = lower(env, e.strArgs[1])
    let idxZi = toZ3Int(idx)
    let code = toCode(at(recv.str, idxZi))
    liftBV(intToBv[8](code, Z3BitVec[8]), false)
  of iekStrSubstr:
    # Phase 15 S3. `s[a..b]` → Z3 `(seq.extract s a (b-a+1))` (substr's
    # (offset, length) convention). Byte-offset slice; out-of-range yields the
    # empty string (Z3 spec). The parser already adjusted `..<` to an inclusive
    # `b`. strArgs = [recv, lo, hi].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrSubstr: receiver not svString"
    let lo = toZ3Int(lower(env, e.strArgs[1]))
    let hi = toZ3Int(lower(env, e.strArgs[2]))
    let length = (hi - lo) + mkInt(1)
    SymVal(kind: svString, str: substr(recv.str, lo, length))
  of iekStrContains:
    # Phase 15 S4. `s.contains(sub)` / `sub in s` → Z3 `(seq.contains s sub)`.
    # `sub in s` semchecks to `contains(s, sub)`; the parser's itString call-guard
    # routes BOTH to iekStrContains (NOT iekContains, the seq/table/set path).
    # strArgs = [recv, sub].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrContains: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrContains: arg not svString"
    SymVal(kind: svBool, bo: contains(recv.str, sub.str))
  of iekStrStartsWith:
    # Phase 15 S4. `s.startsWith(prefix)` → Z3 `(seq.prefixof prefix s)`. nim-z3's
    # `startsWith(a, prefix)` arg order already matches Nim's `(s, prefix)`.
    # strArgs = [recv, prefix].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrStartsWith: receiver not svString"
    let prefix = lower(env, e.strArgs[1])
    doAssert prefix.kind == svString, "iekStrStartsWith: arg not svString"
    SymVal(kind: svBool, bo: startsWith(recv.str, prefix.str))
  of iekStrEndsWith:
    # Phase 15 S4. `s.endsWith(suffix)` → Z3 `(seq.suffixof suffix s)`. nim-z3's
    # `endsWith(a, suffix)` arg order matches Nim's `(s, suffix)`.
    # strArgs = [recv, suffix].
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrEndsWith: receiver not svString"
    let suffix = lower(env, e.strArgs[1])
    doAssert suffix.kind == svString, "iekStrEndsWith: arg not svString"
    SymVal(kind: svBool, bo: endsWith(recv.str, suffix.str))
  of iekStrFind:
    # Phase 15 S4. `s.find(sub)` (strutils.find) → Z3 `indexOf(s, sub)`
    # (`Z3_mk_seq_index`), the BYTE offset of the first occurrence, or -1 when
    # absent. Under the ≤0xFF byte-faithful constraint (ADR-0006) a Z3 position
    # offset equals a Nim byte index, so no codepoint adjustment is needed.
    # The absent case (-1) is a valid SMT integer, never a crash. strArgs =
    # [recv, sub]; nim-z3's no-start `indexOf` overload starts at position 0.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrFind: receiver not svString"
    let sub = lower(env, e.strArgs[1])
    doAssert sub.kind == svString, "iekStrFind: arg not svString"
    SymVal(kind: svInt, zi: indexOf(recv.str, sub.str))
  of iekStrReplace:
    # Phase 15 S5. `s.replace(old, new)` → Z3 `(seq.replace s old new)`
    # (`Z3_mk_seq_replace`), FIRST-occurrence semantics. strArgs = [recv, old,
    # new]. (Nim's `strutils.replace` is global, but the byte-faithful Z3 op
    # this cycle models is the first-occurrence primitive per the S5 spec.)
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrReplace: receiver not svString"
    let old = lower(env, e.strArgs[1])
    doAssert old.kind == svString, "iekStrReplace: `old` not svString"
    let neu = lower(env, e.strArgs[2])
    doAssert neu.kind == svString, "iekStrReplace: `new` not svString"
    SymVal(kind: svString, str: replace(recv.str, old.str, neu.str))
  of iekStrReplaceAll:
    # Phase 15 S5. `s.replaceAll(old, new)` → Z3 `(seq.replace_all s old new)`
    # (`Z3_mk_seq_replace_all`) — VERSION-GATED behind `-d:z3WithSeqReplaceAll`
    # (absent on Z3 < 4.15.5). The `replaceAll` proc only EXISTS when the gate
    # is defined, so the call MUST sit inside the `when` (an unguarded call
    # won't compile on a build without the symbol). On a build lacking the
    # gate, raise SymexZ3VersionMissingError → sxUnknown + seZ3VersionMissing
    # (Invariant 3 — classified, never a crash, never a silent UNSAT).
    when defined(z3WithSeqReplaceAll):
      let recv = lower(env, e.strArgs[0])
      doAssert recv.kind == svString, "iekStrReplaceAll: receiver not svString"
      let old = lower(env, e.strArgs[1])
      doAssert old.kind == svString, "iekStrReplaceAll: `old` not svString"
      let neu = lower(env, e.strArgs[2])
      doAssert neu.kind == svString, "iekStrReplaceAll: `new` not svString"
      SymVal(kind: svString, str: replaceAll(recv.str, old.str, neu.str))
    else:
      raise (ref SymexZ3VersionMissingError)(
        msg: "replaceAll requires Z3 >= 4.15.5 (Z3_mk_seq_replace_all absent " &
             "without -d:z3WithSeqReplaceAll)")
  of iekStrJoin:
    # Phase 15 S5. `xs.join(sep)` → Z3 concat of `xs` with `sep` interleaved.
    # strArgs = [recv(seq[string]), sep]. Tractable only over a CONCRETE-length
    # seq (the split special cases produce one); a symbolic-length join would
    # need an unbounded fold — classified seZ3StringIncomplete.
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svSeq and recv.seqElemTy.kind == itString,
      "iekStrJoin: receiver not svSeq[string]"
    let sep = lower(env, e.strArgs[1])
    doAssert sep.kind == svString, "iekStrJoin: sep not svString"
    if getAstKind(recv.seqLen) != akNumeral:
      raise (ref SymexZ3StringIncompleteError)(
        msg: "join over a symbolic-length seq[string] is not bounded-encodable " &
             "(general path → sxUnknown)")
    SymVal(kind: svString, str: joinStrSeq(recv, sep.str))
  of iekStrSplit:
    # Phase 15 S5. `s.split(sep)` → `seq[string]`. Two TRACTABLE special cases
    # only (the general symbolic path is a universal quantifier over a symbolic
    # seq — a Z3 string-solver hang risk — so it is classified, not encoded):
    #   (a) empty-sep: sep is the literal "" → byte-faithful single-BYTE parts
    #       (`split("abc","") == @["a","b","c"]`), computed in Nim.
    #   (b) concrete-inline: receiver AND sep are string LITERALS → compute the
    #       Nim split and emit a concrete `svSeq` of literal parts. No quantifier.
    # Anything else (symbolic receiver or symbolic sep) → seZ3StringIncomplete.
    let recvIR = e.strArgs[0]
    let sepIR  = e.strArgs[1]
    if sepIR.kind == iekStrLit and sepIR.sval.len == 0:
      # (a) empty-sep. Byte-faithful: each Nim byte is one part. Requires the
      # receiver to be concrete so the byte list is known.
      if recvIR.kind != iekStrLit:
        raise (ref SymexZ3StringIncompleteError)(
          msg: "split with empty sep over a symbolic string is not bounded " &
               "(general path → sxUnknown)")
      var parts: seq[string]
      for b in recvIR.sval:           # iterate bytes
        parts.add $b
      mkConcreteStrSeq(parts)
    elif recvIR.kind == iekStrLit and sepIR.kind == iekStrLit:
      # (b) concrete-inline. Both sides literal → split in Nim, emit literals.
      let parts = recvIR.sval.split(sepIR.sval)
      mkConcreteStrSeq(parts)
    else:
      # (c) general symbolic path. The RFC's join(parts,sep)==s + universal
      # `not contains(parts[i],sep)` + seqLen<=maxSplitParts encoding is a
      # universal quantifier over a symbolic seq[string] — the biggest hang
      # risk in Cluster S. Conservatively classified rather than encoded
      # (ADR-0006, Invariant 3 — structured sxUnknown, never a hang).
      raise (ref SymexZ3StringIncompleteError)(
        msg: "general symbolic string.split is not bounded-encodable " &
             "(universal-quantifier hang risk; general path → sxUnknown)")
  of iekStrMatch:
    # Phase 15 S6b. `s.match(re"…")` / `s.contains(re"…")` → byte-faithful Z3
    # regex membership `matches(s, r)` (`Z3_mk_seq_in_re`) → svBool. The raw
    # `re"…"` pattern rides in `strOp`; S6a's parser translates it against the
    # CURRENT Z3 context (set in runSymexImpl). On a parser Err (backreference /
    # lookahead / named group / malformed) raise SymexUnsupportedRegexError →
    # sxUnknown + seUnsupportedRegex (Invariant 3 — never a silent UNSAT). The
    # ≤0xFF free-string constraint (S3) keeps membership in the byte alphabet,
    # so witnesses round-trip to Nim bytes; it did NOT hang (see S6b notes).
    let recv = lower(env, e.strArgs[0])
    doAssert recv.kind == svString, "iekStrMatch: receiver not svString"
    let pr = parseNimRegexToZ3Regex(e.strOp)
    if not pr.isOk:
      raise (ref SymexUnsupportedRegexError)(msg: pr.error)
    SymVal(kind: svBool, bo: matches(recv.str, pr.regex))
  of iekStrFindRe:
    # Phase 15 S6b — DEFERRED. nim-z3 exposes no `indexOf`-on-regex API (only a
    # substring `indexOf`); a regex `find` byte-index has no direct Z3 primitive.
    # Classify seUnsupportedRegex (sxUnknown) rather than guess an unsound
    # encoding. The pattern is still parsed first so a malformed/rejected pattern
    # reports the precise S6a reason; a VALID pattern reports the deferral.
    let pr = parseNimRegexToZ3Regex(e.strOp)
    if not pr.isOk:
      raise (ref SymexUnsupportedRegexError)(msg: pr.error)
    raise (ref SymexUnsupportedRegexError)(
      msg: "regex find(s, re\"…\") is not modeled: nim-z3 has no " &
           "indexOf-on-regex API (documented S6b deferral)")
  of iekStrReplaceRe:
    # Phase 15 S6b. `s.replace(re"…", repl)` → Z3 `(seq.replace_re s r repl)`
    # (`Z3_mk_seq_replace_re`) — VERSION-GATED behind `-d:z3WithSeqReplaceRe`
    # (absent on this Z3 4.15.0 build). Identical gate shape to S5's replaceAll:
    # the `replaceRe` proc only EXISTS when the gate is defined, so the call MUST
    # sit inside the `when`. Without the gate → SymexZ3VersionMissingError →
    # sxUnknown + seZ3VersionMissing (Invariant 3 — classified, never a crash).
    when defined(z3WithSeqReplaceRe):
      let recv = lower(env, e.strArgs[0])
      doAssert recv.kind == svString, "iekStrReplaceRe: receiver not svString"
      let repl = lower(env, e.strArgs[1])
      doAssert repl.kind == svString, "iekStrReplaceRe: replacement not svString"
      let pr = parseNimRegexToZ3Regex(e.strOp)
      if not pr.isOk:
        raise (ref SymexUnsupportedRegexError)(msg: pr.error)
      SymVal(kind: svString, str: replaceRe(recv.str, pr.regex, repl.str))
    else:
      raise (ref SymexZ3VersionMissingError)(
        msg: "regex replace requires Z3 >= 4.15.5 (Z3_mk_seq_replace_re absent " &
             "without -d:z3WithSeqReplaceRe)")
  of iekStrBytes:
    # Phase 15 S7a. `bytes(s)` byte-faithful byte-view. Under the byte-faithful
    # model (ADR-0006), every Z3 string character is ALREADY a single byte (≤0xFF
    # constrained at allocation, S3), so the byte count == char count and this is
    # the TRIVIAL identity view — NOT a multi-byte UTF-8 decode. We materialise a
    # concrete-length `svSeq` of `svBV8`, one element per character position,
    # reusing S3's exact at→toCode→BV8 bridge:
    #   bytes[i] == intToBv[8](toCode(at(s, i)))
    # `seBytesBeyondBMP` is UNREACHABLE here: a free char is ≤0xFF by construction
    # and a literal char is a raw byte 0..255, so toCode always fits BV8 — no
    # multi-byte branch is ever needed. (Omitted as an error kind for that reason.)
    #
    # Concreteness is detected at the IR level (mirroring S5's split): a string
    # LITERAL receiver (`iekStrLit`) has a statically-known byte count; anything
    # else (a bare `string` parameter, a symbolic result) has a symbolic length
    # with no bounded element chain → seBytesSymbolicLength (Invariant 3).
    let recvIR = e.strArgs[0]
    if recvIR.kind != iekStrLit:
      raise (ref SymexBytesSymbolicLengthError)(
        msg: "bytes() over a symbolic-length string is not bounded-encodable " &
             "(receiver is not a string literal; general path → sxUnknown)")
    let concreteLen = recvIR.sval.len   # byte count == char count (byte-faithful)
    if concreteLen > currentMaxBytesEncodingLen:
      raise (ref SymexBytesLengthTooLargeError)(
        msg: "bytes() concrete length " & $concreteLen & " exceeds " &
             "maxBytesEncodingLen=" & $currentMaxBytesEncodingLen &
             " (general path → sxUnknown)")
    # Build the svSeq of BV8 via the at→toCode→BV8 bridge over the literal's Z3
    # string. A const array defaulting to 0 (unstored slots are never read —
    # access is len-bounded), `store`ing each byte at its index; seqLen pinned to
    # concreteLen (EQUAL to len(s), not >=).
    let recvStr = mkString(recvIR.sval)
    var arr = mkConstArray[Z3Int, Z3BitVec[8]](mkBitVec[8](0))
    for i in 0 ..< concreteLen:
      let b = intToBv[8](toCode(at(recvStr, mkInt(i))), Z3BitVec[8])
      arr = store(arr, mkInt(i), b)
    SymVal(kind: svSeq, seqLen: mkInt(concreteLen),
           seqDataRaw: toAnyAst(arr),
           seqElemTy: tInt(8, signed = false))
  of iekStrConcat:
    # Phase 15 S8. `a & b` → Z3 `(seq.++ a b)` (`Z3_mk_seq_concat`), exposed by
    # nim-z3 as `concat` on `Z3String`. Both operands lower to svString (a string
    # literal operand lowers via the iekStrLit → mkString path). Byte-faithful
    # (ADR-0006): concat is byte-wise, so the result length is additive.
    # strArgs = [lhs, rhs].
    let l = lower(env, e.strArgs[0])
    doAssert l.kind == svString, "iekStrConcat: lhs not svString"
    let r = lower(env, e.strArgs[1])
    doAssert r.kind == svString, "iekStrConcat: rhs not svString"
    SymVal(kind: svString, str: concat(l.str, r.str))
  of iekIntToStr:
    # Phase 15 S10a. `$n` (system.`$` on an int) → Z3 `(str.from-int n)`
    # (`Z3_mk_int_to_str`), exposed by nim-z3 as `toStr` on `Z3Int`. Result is a
    # decimal-string svString. (Z3's `int.to.str` is the empty string for a
    # negative `n`; the digits-path SUTs use non-negative `n`.) strArgs = [n].
    let operand = lower(env, e.strArgs[0])
    # An int param is a BV under the abstraction layer (ADR-0001), so coerce to
    # Z3Int via `toZ3Int` (svInt passes through; a BV lifts via bv2int). The
    # surrounding `$n == "lit"` is an equality goal (low F5 mixed-theory hang
    # risk — F5's pathology was ORDERING goals over int2bv(bv2int(x))).
    SymVal(kind: svString, str: toStr(toZ3Int(operand)))
  of iekStrToInt:
    # Phase 15 S10a + S10b. `parseInt(s)` — both the DIGITS-PATH (S10a) and the
    # RAISES-PATH (S10b, now that E1–E6 shipped the exception walker).
    #
    # nim-z3 `toInt` (Z3 `Z3_mk_str_to_int`) returns the NON-NEGATIVE integer the
    # digits of `s` represent, or **−1** for a non-digit string (VERIFIED against
    # `_deps/z3/src/z3/strings.nim:126-128` — this CORRECTS the RFC/recon premise
    # that `str.to_int` is "unconstrained for non-digit"; it is the fixed value
    # −1). Nim negatives have a leading `-`, which is non-digit (so bare `toInt`
    # gives −1), so we fork on `startsWith(s, "-")` (nim-z3's `Z3_mk_seq_prefix`;
    # the RFC named this `prefixOf` — the real proc is `startsWith(a, prefix)`):
    #   posVal   = toInt(s)                          (no leading '-')
    #   negInner = toInt(substr(s, 1, len(s)-1))     (digits after the '-')
    #   result   = ite(startsWith(s,"-"), -negInner, posVal)
    #
    # DIGITS GATE — negative branch ONLY. The positive branch needs NO gate: Z3's
    # `toInt` already returns the faithful value (true digits, or −1 for non-digit
    # — exactly Z3's honest model). The negative branch DOES need a gate: if the
    # suffix after `-` is non-digit, `negInner` is −1 and `-negInner` would be a
    # FALSE `+1`. So gate `isNeg ⇒ negInner >= 0` (`(not isNeg) or negInner>=0`),
    # threaded into `parseIntGateConstraints` (drained in `trySolve`).
    #
    # S10b RAISES-PATH. `parseInt(s)` is an EXPRESSION (→ int), but Nim's runtime
    # RAISES `ValueError` when `s` is not a valid integer. The raise condition is
    # exactly the non-`-`-prefixed non-digit case: `(not isNeg) and (posVal < 0)`
    # (Z3's `toInt` returns −1 there). [The `-`-prefixed non-digit case is handled
    # by the S10a digits gate above, which makes the negative branch UNSAT for a
    # non-digit suffix; modelling its raise too is left to that gate — the spec
    # scopes the S10b raise to the non-`-`-prefixed case, matching
    # `not (toInt(s) >= 0) and not startsWith(s, "-")`.] `lower` cannot itself
    # route a raise (it has no WalkCtx/Path), so we surface the raise predicate to
    # the enclosing statement walk via the `parseIntRaiseConds` threadvar; the
    # statement arm (`isLet`/`isAssign`/`isIf`/`isAssert`) drains it and forks: a
    # RAISES sub-path (constrained by the predicate, routed via E3's `routeRaise`
    # and terminated) and a DIGITS sub-path (constrained by the negation,
    # continuing with this int value). This CLOSES the S10a unsoundness window, so
    # the `seParseIntPreE` hint is NO LONGER emitted. strArgs = [s].
    let s = lower(env, e.strArgs[0])
    doAssert s.kind == svString, "iekStrToInt: operand not svString"
    let dash = mkString("-")
    let isNeg = startsWith(s.str, dash)
    let posVal = toInt(s.str)
    let sLen = len(s.str)
    let negInner = toInt(substr(s.str, mkInt(1), sLen - mkInt(1)))
    let resultInt = ite(isNeg, -negInner, posVal)
    # Digits gate on the NEGATIVE branch only (positive branch is already faithful).
    parseIntGateConstraints.add ((not isNeg) or (negInner >= mkInt(0)))
    # S10b: surface the raise predicate (non-digit, non-`-`-prefixed) for the
    # enclosing statement walk to fork into a routed `ValueError` raise.
    parseIntRaiseConds.add ((not isNeg) and (posVal < mkInt(0)))
    SymVal(kind: svInt, zi: resultInt)
  of StrOpKinds - {iekStrLen, iekStrAt, iekStrSubstr,
                   iekStrContains, iekStrStartsWith, iekStrEndsWith,
                   iekStrFind, iekStrReplace, iekStrReplaceAll,
                   iekStrSplit, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe,
                   iekStrBytes, iekStrConcat,
                   iekIntToStr, iekStrToInt}:
    # Phase 15: string ops not modeled in this cycle. Raise a classified
    # SymexUnsupportedStringOpError; the runSymex boundary maps it to sxUnknown +
    # seUnsupportedStringOp (ADR-0006, Invariant 3 — never a crash/silent UNSAT).
    # S6–S11 replace these with the real Z3 String/Seq/Regex lowering.
    let opName = if e.strOp.len > 0: e.strOp else: $e.kind
    raise (ref SymexUnsupportedStringOpError)(op: opName,
      msg: "string op `" & opName & "` is not modeled until its Cluster-S cycle")
  of iekGetCurrentExnMsg:
    # Phase 15 E8. `getCurrentExceptionMsg()`. Valid only inside an `except`
    # handler body (in-flight exn present). The in-flight msg is mirrored into
    # `currentInFlightMsg` by the handler-body walk; a `none` typeId means we
    # are outside any handler → classified `eeNotInHandler` (Invariant 3).
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(
        msg: "getCurrentExceptionMsg")
    SymVal(kind: svString, str: mkString(currentInFlightMsg.get("")))
  of iekGetCurrentExn:
    # Phase 15 E8. `getCurrentException()`. Returns an opaque `svUninterpRef`
    # keyed by the in-flight type: a FRESH uninterpreted-sort constant whose
    # sort is `Exn_<typeId>`. Fields are not modeled (extraction emits an
    # `eeUninterpRefExtraction` sevHint). Out of a handler → `eeNotInHandler`.
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(
        msg: "getCurrentException")
    let typeId  = currentInFlightTypeId.get
    let srtName = "Exn_" & typeId
    inc currentExnRefCounter
    let constName = srtName & "#" & $currentExnRefCounter
    # Fresh constant of the (per-type) uninterpreted sort, erased to Z3AnyAst.
    let ctx = requireCurrentContext()
    let srt = mkUninterpretedSort(ctx, srtName)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, constName.cstring)
    let rawConst = ctx.checkErr Z3_mk_const(ctx.raw, sym, srt.raw)
    let anyAst = wrap[Z3AnyAst](ctx, rawConst)
    lastGetCurrentExnRef = (sortName: srtName, typeTag: typeId)  ## E8 test hook
    SymVal(kind: svUninterpRef, uninterpAst: anyAst,
           sortName: srtName, typeTag: typeId)
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
      doAssert recv.setElemTy.kind == itInt
      doAssert recv.setElemTy.width == 64
      let bv64Proto = SymVal(kind: svBV64, signed: true,
                             bv64: mkBitVec[64](0'i64))
      let keySV = lower(env, e.key, some(bv64Proto))
      doAssert keySV.kind == svBV64
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
      let inner = ejectBase(lower(env, e.operand, proto))   ## Phase 15 G4
      if inner.kind == svInt: SymVal(kind: svInt, zi: -inner.zi)
      elif inner.kind == svFloat32: SymVal(kind: svFloat32, fp32: -inner.fp32)  # Phase 15 F3
      elif inner.kind == svFloat64: SymVal(kind: svFloat64, fp64: -inner.fp64)  # Phase 15 F3
      else: negBV(inner)
    of uNot:
      let inner = lower(env, e.operand, some(ofBool(mkBool(true))))
      doAssert inner.kind == svBool
      ofBool(not inner.bo)
  of iekBinop:
    case e.bop
    # ---- comparison ops always produce Bool; operand repr from probe ----
    of bEq, bNe, bLt, bLe, bGt, bGe:
      let pp = probeProto(env, e)
      if pp.isSome:
        var l = ejectBase(lower(env, e.lhs, pp))   ## Phase 15 G4: distinct→base
        var r = ejectBase(lower(env, e.rhs, pp))
        # Phase 15 C5: closure ==/!= (nominal-for-site + structural-for-env,
        # ADR-0009 D7). ejectBase passes svClosure through unchanged.
        if l.kind == svClosure and r.kind == svClosure:
          return closureEq(l, r, e.bop)
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        # Reconcile mixed int reps: bv2int both sides.
        if l.kind != r.kind and
           l.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
           r.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
          l = SymVal(kind: svInt, zi: toZ3Int(l))
          r = SymVal(kind: svInt, zi: toZ3Int(r))
        if l.kind == svInt and r.kind != svBool:
          cmpInt(l, r, e.bop)
        elif l.kind == svBool or r.kind == svBool:
          # Bool ==/!= only. Phase 15 G7: a `static bool` literal arrives as an
          # int rep (`IntLit 0/1`); coerce both sides so e.g. `(x>0) == B` (B
          # baked to `IntLit 1`) compares bool-to-bool, not bool-to-int.
          let lb = coerceToBoolSV(l)
          let rb = coerceToBoolSV(r)
          case e.bop
          of bEq: ofBool(lb.bo == rb.bo)
          of bNe: ofBool(lb.bo != rb.bo)
          else:
            raise newException(ValueError,
              "comparison op " & $e.bop & " not valid on bool operands")
        elif l.kind in {svFloat32, svFloat64}:
          cmpFloat(l, r, e.bop)        # Phase 15 F2: IEEE ==/!=; F4 adds ordering
        elif l.kind == svString:
          cmpString(l, r, e.bop)       # Phase 15 S1: Z3 String ==/!= (S3 adds </<=)
        else:
          case e.bop
          of bEq: eqBV(l, r)
          of bNe: neBV(l, r)
          of bLt: cmpBV(l, r, bvslt, bvult)
          of bLe: cmpBV(l, r, bvsle, bvule)
          of bGt: cmpBV(l, r, bvsgt, bvugt)
          of bGe: cmpBV(l, r, bvsge, bvuge)
          else: raise newException(ValueError, "unreachable")
      else:
        # No env-resident var via probe — but the lowered LHS might
        # still be svInt (e.g. `iekSeqLen`). Re-dispatch on its kind.
        let l = ejectBase(lower(env, e.lhs, none(SymVal)))   ## Phase 15 G4
        let r = ejectBase(lower(env, e.rhs, some(l)))
        # Phase 15 C5: closure ==/!= (ADR-0009 D7); probe-miss branch.
        if l.kind == svClosure and r.kind == svClosure:
          return closureEq(l, r, e.bop)
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        if l.kind == svInt:
          cmpInt(l, r, e.bop)
        elif l.kind in {svFloat32, svFloat64}:
          cmpFloat(l, r, e.bop)        # Phase 15 F2
        elif l.kind == svString:
          cmpString(l, r, e.bop)       # Phase 15 S1: Z3 String ==/!=
        else:
          case e.bop
          of bEq: eqBV(l, r)
          of bNe: neBV(l, r)
          of bLt: cmpBV(l, r, bvslt, bvult)
          of bLe: cmpBV(l, r, bvsle, bvule)
          of bGt: cmpBV(l, r, bvsgt, bvugt)
          of bGe: cmpBV(l, r, bvsge, bvuge)
          else: raise newException(ValueError, "unreachable")
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
        # Bitwise on Z3Int is not in Z3's Int theory; promotion proof
        # should have refused this in the first place (cycle 8 ban list).
        raise newException(ValueError,
          "bitwise op on promoted Z3Int — abstraction layer should " &
          "have declined promotion under bit-twiddling")
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
      if l.kind == svInt:
        arithInt(l, r, e.bop)
      elif l.kind in {svFloat32, svFloat64}:
        arithFloat(l, r, e.bop)        # Phase 15 F3
      else:
        case e.bop
        of bAdd: binBV(l, r, `+`)
        of bSub: binBV(l, r, `-`)
        of bMul: binBV(l, r, `*`)
        of bDiv: divBV(l, r)
        of bMod: modBV(l, r)
        else: raise newException(ValueError, "unreachable")
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
      # Comparison borrow → raw svBool from the base comparison. BV dispatch
      # mirrors the iekBinop comparison arm (signed/unsigned op pair).
      if l.kind == svInt:                cmpInt(l, r, e.borrowOp)
      elif l.kind == svBool:
        case e.borrowOp
        of bEq: ofBool(l.bo == r.bo)
        of bNe: ofBool(l.bo != r.bo)
        else: raise newException(ValueError,
          "borrow: comparison op " & $e.borrowOp & " not valid on bool")
      elif l.kind in {svFloat32, svFloat64}: cmpFloat(l, r, e.borrowOp)
      elif l.kind == svString:           cmpString(l, r, e.borrowOp)
      else:
        case e.borrowOp
        of bEq: eqBV(l, r)
        of bNe: neBV(l, r)
        of bLt: cmpBV(l, r, bvslt, bvult)
        of bLe: cmpBV(l, r, bvsle, bvule)
        of bGt: cmpBV(l, r, bvsgt, bvugt)
        of bGe: cmpBV(l, r, bvsge, bvuge)
        else: raise newException(ValueError, "borrow: unreachable cmp")
    of bAdd, bSub, bMul, bDiv, bMod:
      # Arithmetic borrow → apply the base op, then re-box as the distinct type.
      let baseRes =
        if l.kind == svInt:                arithInt(l, r, e.borrowOp)
        elif l.kind in {svFloat32, svFloat64}: arithFloat(l, r, e.borrowOp)
        else:
          case e.borrowOp
          of bAdd: binBV(l, r, `+`)
          of bSub: binBV(l, r, `-`)
          of bMul: binBV(l, r, `*`)
          of bDiv: divBV(l, r)
          of bMod: modBV(l, r)
          else: raise newException(ValueError, "borrow: unreachable arith")
      if e.borrowReturnsDistinct:
        reboxDistinct(e.borrowDistinctName, baseRes)
      else:
        baseRes
    else:
      raise newException(ValueError,
        "borrow: unsupported base operator " & $e.borrowOp)
  of iekLambda:
    # Phase 15 C2a. Closure CONSTRUCTION: snapshot the captured locals from the
    # current env into an `svTuple` envRecord, get-or-create the per-site
    # uninterpreted funcSym (memoized in `currentClosureSyms`), and assemble the
    # `svClosure{closureSite, closureEnv, closureRawFD}`. NO body descent — the
    # lambda body is lowered only at APPLICATION (C2b, the ground per-call
    # axiom). Closure CALL (`iekClosureCall`) stays `ceNotImplemented` below.
    buildClosure(env, e)
  of iekClosureCall:
    # Phase 15 C2b. Closure APPLICATION. Resolve the callee variable to an
    # `svClosure`, descend the lambda body ONCE (reached via the site→body map),
    # collect its return sub-paths, and assert the GROUND per-call-site axiom
    # (ADR-0009 D6): one `implies(callerPC and pc_i, funcSym(env, args) == v_i)`
    # per sub-path, NEVER a `∀env,args` axiom (the G4 hang). The call RESULT is
    # the funcSym application the axioms constrain. The descent uses `walk` via
    # the `currentWalkCtxPtr` threadvar (`lower` has no `WalkCtx`); the body is
    # defined after `walk`, so this dispatches to the forward-declared
    # `lowerClosureCall`.
    lowerClosureCall(env, e)
  of iekSeqLit:
    # Phase 15 C4. A concrete seq literal `@[a, b, c]` → a CONCRETE-length
    # svSeq: store each lowered element at its index in a fresh data array, and
    # pin `seqLen` to the literal count (a numeral). The empty `@[]` yields a
    # length-0 svSeq. Concrete length is what lets a downstream HOF inline.
    lowerSeqLit(env, e)
  of iekHofCall:
    # Phase 15 C4 (ADR-0009). DSL higher-order call. Selects the INLINE path
    # (concrete length ≤ seqInlineThreshold; unroll the closure per element,
    # quantifier-free) or the AXIOM path (symbolic length: map → `mapArray`;
    # fold → raw `Z3_mk_app`; filter → `ceUnsupportedHof`, Phase-16 deferred).
    # Uses `walk` via `currentWalkCtxPtr`, so the body lives after `walk`.
    lowerHofCall(env, e)

proc lowerBool(env: Env, e: IRExpr): Z3Bool =
  let sv = lower(env, e, some(ofBool(mkBool(true))))
  doAssert sv.kind == svBool, "lowerBool: expected Bool, got " & $sv.kind
  sv.bo

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
        extractionErrors.add SymexErrorInfo(kind: feExtractionFailed,
          severity: sevError,
          msg: "float64 witness at '" & path & "' did not resolve to a concrete numeral")
        w.float64Vals[path] = 0.0
  of svFloat32:
    if m.evalBool(isNaN(sv.fp32), modelCompletion = true):
      w.float32Vals[path] = float32(NaN)
    else:
      let opt = m.evalFloat32Opt(sv.fp32, modelCompletion = true)
      if opt.isSome:
        w.float32Vals[path] = opt.get
      else:
        extractionErrors.add SymexErrorInfo(kind: feExtractionFailed,
          severity: sevError,
          msg: "float32 witness at '" & path & "' did not resolve to a concrete numeral")
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
    w.strVals[path] = m.evalStr(sv.str)
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
  of isAssert:
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
  of isTargetLabel, isUnsupported: discard

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
  of isAssert:
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
  of isTargetLabel, isUnsupported: discard

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
  else:
    raise newException(ValueError,
      "extractSeqElements: unsupported element kind " & $sv.seqElemTy.kind)

proc extractSetMembers(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal, candidates: HashSet[int64]) =
  doAssert sv.setElemTy.kind == itInt and sv.setElemTy.width == 64
  let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
    sv.setMembersRaw.ctx, sv.setMembersRaw.raw)
  var present: seq[int64]
  for v in candidates:
    if m.evalBool(select(typed, mkBitVec[64](v))):
      present.add v
  w.setMembers[path] = present

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
    extractionErrors.add SymexErrorInfo(
      kind: eeUninterpRefExtraction, severity: sevHint,
      msg: "exception object fields not modeled symbolically (" &
           sv.typeTag & ")")
  of svClosure:
    # Phase 15 C2a (Invariant 3). A closure as a top-level SUT RESULT is
    # unsupported: the `(funcSym, envRecord)` pair has no concrete witness
    # rendering (a proc value cannot be reconstructed as a literal). Classify
    # it (`ceNotImplemented`, sevError) rather than silently dropping the leaf,
    # and drop the leaf. Drained into the finding's `errors`.
    extractionErrors.add SymexErrorInfo(
      kind: ceNotImplemented, severity: sevError,
      msg: "closure as a top-level SUT result is not supported (no witness " &
           "rendering for a proc value)")
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
        else: discard   ## composite pointee witness lands R3+; no scalar leaf
  else:
    extractLeaf(m, w, path, sv)

proc extractWitness(m: Z3Model, env: Env, params: seq[IRParam],
                    tabKeys: Table[string, HashSet[string]],
                    setMembers: Table[string, HashSet[int64]]
                    ): RawWitness =
  result.paramOrder = newSeq[string](params.len)
  for i, p in params:
    result.paramOrder[i] = p.name
    extractFromSymVal(m, result, p.name, env[p.name], tabKeys, setMembers)

var symexZ3CallCount* {.threadvar.}: int
  ## Phase 13 cycle 1. Increments on every Z3 `s.check()` invocation
  ## inside symex. Always-on (no compile-time gate) — the increment
  ## cost is negligible against a Z3 query and tests observe it to
  ## assert "cache hit, Z3 not called" contracts. Re-exported by
  ## `proptest/symex` so consumers can `import proptest/symex` and
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
  solverParams.set("rlimit", settings.queryRLimit)
  solverParams.set("random_seed", 0'u)
  s.setParams(solverParams)
  for c in path.pc:
    s.add(c)
  # Phase 15 S10a: drain the parseInt digits soundness-gate constraints
  # (`toInt(s) >= 0` on the active branch) into every check. Sound because each
  # clause references the specific param string var's Z3 AST (identical across
  # paths) and only narrows non-digit models.
  for c in parseIntGateConstraints:
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
  inc symexZ3CallCount
  let r = s.check()
  case r
  of zsSat:
    let m = s.model()
    # Use initialEnv when provided — mutations may have rebound params
    # to post-store SymVals; the witness wants the pre-call value.
    let envForExtract = if initialEnv.len > 0: initialEnv else: path.env
    (status: sxSat,
     witness: extractWitness(m, envForExtract, params, tabKeys, setMembers))
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
    distinctSorts: Table[string, Z3Sort[stUninterpreted]]
                        ## Phase 15 G4 (ADR-0008 D4): the per-walker distinct-
                        ## sort cache (one fresh uninterpreted sort per distinct
                        ## type name), shared across all call frames. The LIVE
                        ## populator is the `currentDistinctSorts` threadvar
                        ## (`allocateSym` has no WalkCtx access); this field
                        ## mirrors it after the walk for post-run inspection.
    closureSyms: Table[ClosureSymKey, RawZ3FuncDecl]
                        ## Phase 15 C2a (ADR-0009 Consequences): the per-site
                        ## closure funcSym memo (one uninterpreted decl per
                        ## (site, env/param sorts)), shared across frames. The
                        ## LIVE populator is the `currentClosureSyms` threadvar
                        ## (`lower(iekLambda)` has no WalkCtx); this field mirrors
                        ## it after the walk for post-run inspection.
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
                        ## fresh alloc is always distinct from nil. Mirrored from
                        ## the `currentNilConsts` threadvar after the walk.
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

  CallCacheEntry = object
    ## Function summary: the (callee, argShape) pair maps to the Z3
    ## variable representing the return value plus the constraint
    ## delta added to the returning path. On a cache hit, the entry's
    ## retSym binds to the caller's retName and the pcDelta extends
    ## the current path's pc — no re-walking required.
    retSym:  SymVal
    pcDelta: seq[Z3Bool]

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
  ## Phase 15 Z4 + E2a. Halt once a satisfying finding exists. The stop set is
  ## {sxSat, sxRaised} — a reachable raise is a terminal finding just like a sat
  ## witness. An sxUnknown-only `found` does not halt — a SAT/raise path may
  ## still be found on another branch.
  for r in w.found:
    if r.status == sxSat or r.status == sxRaised: return true
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
# `forkPath` (defined above), which deep-copies the logical-heap state
# (`heaps` + `allocCounters` via `deepCopyHeapState`; `heapDepth` copies by
# value). This is the single enforcement point for fork isolation so a heap
# mutation on one branch can never bleed into a sibling/parent path. The fresh
# ROOT path in `runSymex` (`let initial = Path(...)`) is the ONLY raw `Path(`
# construction — it has no parent and correctly gets empty-default heap fields.
#
# In H1 the tables are empty on every path (the walker neither reads nor writes
# them); the copies are inert until Cluster R populates the heap. They are
# wired now so E/G/C/R need not re-audit the fork sites. New fork sites added
# by E/G/C/R MUST use `forkPath` and be added to this registry; the R-cluster
# walker comment block supersedes this one.
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

proc typeIdToDefectKind(typeId: string): DefectKind =
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

proc walk(stmt: IRStmt, paths: seq[Path], w: var WalkCtx): seq[Path]

proc routeRaise(p: Path, typeId: string, msg: Option[string],
                w: var WalkCtx): seq[Path]

proc drainParseIntRaises(p: Path, w: var WalkCtx): seq[Path] =
  ## Phase 15 S10b. Drain any `parseInt` raise predicates accumulated by the
  ## `iekStrToInt` lowering during the just-completed `lower`/`lowerBool` call on
  ## path `p`, forking each into a routed `ValueError` raise. For each predicate
  ## `rc` (the non-digit, non-`-`-prefixed case): fork a RAISES sub-path
  ## constrained by `rc` and hand it to E3's `routeRaise(…, "ValueError", …)` —
  ## which either transfers it into a surrounding `except` (its continuations
  ## flow out) or surfaces a public `sxRaised{ValueError}` at the SUT boundary,
  ## then terminates the raise path. The DIGITS continuation is `p` constrained by
  ## the conjunction of all negated predicates (so the int value semantics hold
  ## only when no parseInt raised). Returns the surviving (digits-continuation)
  ## path(s) — the caller continues the statement with these. Clears the sink.
  ##
  ## NOTE: callers MUST set `parseIntRaiseConds = @[]` immediately BEFORE the
  ## `lower`/`lowerBool` call so the drained predicates belong to THIS path only.
  if parseIntRaiseConds.len == 0:
    return @[p]
  let conds = parseIntRaiseConds
  parseIntRaiseConds = @[]
  # Route each raise predicate as a `ValueError` raise on its own fork.
  for rc in conds:
    let raisePath = forkPath(p, p.pc & @[rc], p.env, p.uncertain)
    discard routeRaise(raisePath, "ValueError",
                       some("invalid integer: parseInt"), w)
  # The continuation survives only where NO parseInt raised: conjoin the
  # negations of every raise predicate onto the path condition.
  var negated: seq[Z3Bool]
  for rc in conds:
    negated.add(not rc)
  @[forkPath(p, p.pc & negated, p.env, p.uncertain)]

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
    if w.settings.maxFrontierSize > 0 and
       result.len > w.settings.maxFrontierSize:
      var certain, uncertain: seq[Path]
      for p in result:
        if p.uncertain: uncertain.add p
        else:           certain.add p
      var kept: seq[Path]
      for p in certain:
        if kept.len >= w.settings.maxFrontierSize: break
        kept.add p
      for p in uncertain:
        if kept.len >= w.settings.maxFrontierSize: break
        kept.add p
      w.sawUnknown = true
      result = kept

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
      seedCallerHeapThreadvars(p)  ## Phase 15 R1b: closure call in a cond reads this heap
      var cp = p
      var accumNegated: seq[Z3Bool]
      for br in stmt.branches:
        parseIntRaiseConds = @[]   ## Phase 15 S10b: this cond's raises only
        let condBool = lowerBool(cp.env, br.cond)
        let cont = drainParseIntRaises(cp, w)
        if cont.len == 0:
          # The whole cond raised on every path (digits continuation infeasible).
          cp = forkPath(cp, cp.pc, cp.env, cp.uncertain)
        else:
          cp = cont[0]   ## digits-constrained continuation (non-raise pc)
        let armPath = forkPath(cp, cp.pc & accumNegated & @[condBool],
                               cp.env, cp.uncertain)
        survivors.add walk(br.body, @[armPath], w)
        accumNegated.add(not condBool)
        if w.shouldStop: return
      let elsePath = forkPath(cp, cp.pc & accumNegated, cp.env, cp.uncertain)
      if stmt.elseBody != nil:
        survivors.add walk(stmt.elseBody, @[elsePath], w)
      else:
        survivors.add elsePath
    survivors
  of isLet:
    var out2: seq[Path]
    for p in paths:
      parseIntRaiseConds = @[]   ## Phase 15 S10b: this lowering's raises only
      seedCallerHeapThreadvars(p)  ## Phase 15 R1b: closure call in rhs reads this heap
      let lv = lower(p.env, stmt.lvalue)
      for cp in drainParseIntRaises(p, w):   ## Phase 15 S10b: parseInt raise fork
        var newEnv = cp.env
        newEnv[stmt.lname] = lv
        out2.add forkPath(cp, cp.pc, newEnv, cp.uncertain)
    out2
  of isAssign:
    var out2: seq[Path]
    for p in paths:
      parseIntRaiseConds = @[]   ## Phase 15 S10b: this lowering's raises only
      seedCallerHeapThreadvars(p)  ## Phase 15 R1b: closure call in rhs reads this heap
      let av = lower(p.env, stmt.avalue)
      for cp in drainParseIntRaises(p, w):   ## Phase 15 S10b: parseInt raise fork
        var newEnv = cp.env
        newEnv[stmt.aname] = av
        out2.add forkPath(cp, cp.pc, newEnv, cp.uncertain)
    out2
  of isWhile:
    # Phase 6: k-unroll. Each iteration forks on the guard.
    var survivors: seq[Path] = @[]
    var active = paths
    w.loopStack.add LoopFrame(breakPaths: @[], continuePaths: @[])
    let frameIx = w.loopStack.high
    let unwind = w.settings.maxLoopUnwind
    for iter in 0 ..< unwind:
      if w.shouldStop: break
      if active.len == 0: break
      var nextActive: seq[Path]
      for p in active:
        let cond = lowerBool(p.env, stmt.wcond)
        # cond=true: walk body
        let truePath = forkPath(p, p.pc & @[cond], p.env, p.uncertain)
        let afterBody = walk(stmt.wbody, @[truePath], w)
        # Continue-paths from the body merge into next-iter active.
        let cps = w.loopStack[frameIx].continuePaths
        w.loopStack[frameIx].continuePaths = @[]
        for cp in cps: nextActive.add cp
        for ap in afterBody: nextActive.add ap
        # cond=false: exit loop
        survivors.add forkPath(p, p.pc & @[not cond], p.env, p.uncertain)
      active = nextActive
    # Break-paths exit the loop directly (with their accumulated pc/env).
    for bp in w.loopStack[frameIx].breakPaths:
      survivors.add bp
    # Any paths still active after maxLoopUnwind iterations are
    # exhausted: cond=true was still SAT-able. Mark uncertain.
    if active.len > 0:
      w.sawUnknown = true
      for p in active:
        survivors.add forkPath(p, p.pc, p.env, true)
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
      let arrSV = lower(p.env, stmt.ixArr)
      # ---- Phase 5: Table[K, V] indexing ----
      if arrSV.kind == svTable:
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
          survivors.add forkPath(p, p.pc & @[presentCond], newEnv, p.uncertain)
        else:
          raise newException(ValueError,
            "Phase 5: Table value " & $arrSV.tabValTy & " not implemented")
        continue
      # ---- Phase 5: dynamic seq[T] indexing ----
      if arrSV.kind == svSeq:
        # Seq index is Z3Int. Lower with an svInt proto for literals;
        # for env-resident BV-typed Nim ints we coerce via bv2int.
        let intProto = SymVal(kind: svInt, zi: mkInt(0))
        let idxSV = lower(p.env, stmt.ixIdx, some(intProto))
        let lenZi = arrSV.seqLen
        let idxZi = toZ3Int(idxSV)
        let inLoCond = idxZi >= mkInt(0)
        let inHiCond = idxZi <  lenZi
        if w.target.kind == stkIndexError:
          let oobPath = forkPath(p, p.pc & @[not (inLoCond and inHiCond)],
                                 p.env, p.uncertain)
          if oobPath.uncertain:
            w.sawUnknown = true
          else:
            let (st, wit) = trySolve(w.z3, oobPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
            case st
            of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
            of sxUnknown: w.sawUnknown = true
            of sxUnsat:  discard
            of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
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
        else:
          raise newException(ValueError,
            "isIndex/seq: unsupported elem kind " & $arrSV.seqElemTy.kind)
        var newEnv = p.env
        newEnv[stmt.ixRetName] = indexed
        survivors.add forkPath(p, p.pc & @[inLoCond, inHiCond], newEnv, p.uncertain)
        continue
      # ---- Phase 4: static array (the existing path) ----
      doAssert arrSV.kind == svArray,
        "isIndex on non-array kind=" & $arrSV.kind
      let n = arrSV.arrElems.len
      let idxSV = lower(p.env, stmt.ixIdx)
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
      # OOB target check.
      if w.target.kind == stkIndexError:
        let oobPath = forkPath(p, p.pc & @[not (inLoCond and inHiCond)],
                               p.env, p.uncertain)
        if oobPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, oobPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
          of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
      # In-bounds path continues with binding; build the value via ite.
      var indexed = arrSV.arrElems[0]
      for k in 1 ..< n:
        let kSV = coerceIntLit(idxSV, int64(k))
        indexed = iteSV(symEq(idxSV, kSV), arrSV.arrElems[k], indexed)
      var newEnv = p.env
      newEnv[stmt.ixRetName] = indexed
      survivors.add forkPath(p, p.pc & @[inLoCond, inHiCond], newEnv, p.uncertain)
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
      out2.add forkPath(p, p.pc, newEnv, p.uncertain)
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
      let rhsSV = lower(p.env, stmt.vrsRhs)
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
          var newEnv = p.env
          newEnv[stmt.vrsObjName] = newSV
          out2.add forkPath(p, p.pc & @[rhsEq(int64(tag))], newEnv, p.uncertain)
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
          var newEnv = p.env
          newEnv[stmt.vrsObjName] = newSV
          out2.add forkPath(p, p.pc & @[rhsEq(int64(tag))], newEnv, p.uncertain)
      else:
        doAssert false,
          "isVariantReassignSymbolic on non-variant kind=" & $oldSV.kind
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
      let recv = lower(p.env, stmt.vfRecv)
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
      proc discEq(tagOrd: int64): Z3Bool =
        case disc.kind
        of svBV8:  disc.bv8  == mkBitVec[8](tagOrd)
        of svBV16: disc.bv16 == mkBitVec[16](tagOrd)
        of svBV32: disc.bv32 == mkBitVec[32](tagOrd)
        of svBV64: disc.bv64 == mkBitVec[64](tagOrd)
        of svInt:  disc.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
        of svBool: disc.bo   == mkBool(tagOrd != 0)  ## Phase 15 F9c: bool disc
        else:
          raise newException(ValueError,
            "isVariantField: discriminator must be a BV or Z3Int kind")
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
              let neg = not discEq(int64(otherTag))
              if not seeded: conj = neg; seeded = true
              else:          conj = conj and neg
            if not seeded:
              raise newException(ValueError,
                "isVariantField: else-only variant has no non-else " &
                "arms to negate against (degenerate; the parser " &
                "should not have emitted such an IR)")
            conj
          else:
            discEq(int64(tag))
        armEqs.add armEq
        armBindings.add (tag, armFieldsTbl[tag][fieldIx])
      doAssert armEqs.len > 0,
        "isVariantField: parser produced an empty matchingTags list"
      var inArmCond = armEqs[0]
      for k in 1 ..< armEqs.len:
        inArmCond = inArmCond or armEqs[k]
      let outOfArmCond = not inArmCond
      # tFieldDefect — solve the out-of-arm branch.
      if w.target.kind == stkFieldDefect:
        let fdPath = forkPath(p, p.pc & @[outOfArmCond], p.env, p.uncertain)
        if fdPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, fdPath, w.params, w.settings,
                                   w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
          of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
          if w.shouldStop: return
      # In-arm path — bind retName to the ite-chain over arms.
      var bound = armBindings[armBindings.len - 1][1]
      for k in countdown(armBindings.len - 2, 0):
        let eqB = discEq(int64(armBindings[k][0]))
        bound = iteSV(eqB, armBindings[k][1], bound)
      var newEnv = p.env
      newEnv[stmt.vfRetName] = bound
      survivors.add forkPath(p, p.pc & @[inArmCond], newEnv, p.uncertain)
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
          let retVal = lower(p.env, stmt.retExpr,
                             some(w.callStack[frameIx].retSym))
          let retSym = w.callStack[frameIx].retSym
          # Reconcile mixed int reps (e.g. callee returns svInt because
          # of #135 range propagation while retSym was allocated svBV*).
          let retConstraint =
            if retSym.kind != retVal.kind and
               retSym.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
               retVal.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
              # Cross-rep linkage (e.g. #135 propagation): bv2int both.
              toZ3Int(retSym) == toZ3Int(retVal)
            else:
              # Phase 15 G3: same-kind structural binding (BV-wrap semantics
              # preserved; Z3Int = Z3Int when both are Int; float uses a
              # NaN-safe structural eq so a NaN-returning callee is not pruned;
              # string binds natively). This is what wires a value-returning
              # generic instantiated at `float64`/`string` to flow its result
              # into the caller.
              retBindEq(retSym, retVal)
          w.callStack[frameIx].returnedPaths.add forkPath(
            p, p.pc & @[retConstraint], p.env, p.uncertain)
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
        out2.add forkPath(p, p.pc & pcInit, newEnv, true)
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
        out2.add forkPath(p, p.pc & pcInit, newEnv, true)
      return out2
    let sig = w.procs[stmt.callee]
    # Statistics
    if not w.callStats.hasKey(stmt.callee):
      w.callStats[stmt.callee] = CallStat(name: stmt.callee, walked: 0, cacheHits: 0)
    # Depth check
    if w.callStack.len >= w.settings.maxCallDepth:
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
        out2.add forkPath(p, p.pc & pcInit, newEnv, true)
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
        for i, formal in sig.params:
          argVals.add lower(p.env, stmt.cargs[i])
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
          survivors.add forkPath(p, p.pc & pcInit, newEnv, true)
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
          survivors.add forkPath(p, p.pc & entry.pcDelta, newEnv, p.uncertain)
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
                       freshRetSym(stmt.retTy, z3Name, retInit)
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
        let calleePath = forkPath(p, p.pc, calleeEnv, p.uncertain)
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
          let raisePath = forkPath(er.path, er.path.pc, rEnv, er.path.uncertain)
          survivors.add routeRaise(raisePath, er.typeId, er.msg, w)
          if w.shouldStop: return survivors
        let frame = w.callStack[w.callStack.high]
        w.callStack.setLen(w.callStack.high)
        w.activeCalls.excl key
        # Cache: single-return, single-fall-through-free, non-uncertain
        # calls cache for argShape-keyed reuse. Phase 15 E3: a callee that
        # escaped a raise is NOT cached — its summary is incomplete (a cache hit
        # would replay the normal return but silently drop the escaped raise).
        if calleeEscaped.len == 0 and
           frame.returnedPaths.len == 1 and fallThrough.len == 0 and
           not frame.returnedPaths[0].uncertain:
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
          # callee's exit heap state back out (ADR-0010 R1b). `forkPath(cp, ...)`
          # forks from `cp` (the returned CALLEE path), so:
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
          let merged = forkPath(cp, cp.pc & retInit, newEnv,
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
      parseIntRaiseConds = @[]   ## Phase 15 S10b: this cond's raises only
      let cond = lowerBool(p0.env, stmt.acond)
      let cont = drainParseIntRaises(p0, w)   ## Phase 15 S10b: parseInt raise fork
      if cont.len == 0: continue
      let p = cont[0]
      if w.target.kind == stkAssertionViolation:
        let violPath = forkPath(p, p.pc & @[not cond], p.env, p.uncertain)
        if violPath.uncertain:
          w.sawUnknown = true
        else:
          let (st, wit) = trySolve(w.z3, violPath, w.params, w.settings, w.tabKeys, w.setMembers, w.initialEnv)
          case st
          of sxSat:    w.found.add(RawResult(status: sxSat, witness: wit))
          of sxUnknown: w.sawUnknown = true
          of sxUnsat:  discard
          of sxRaised: discard   ## Phase 15 E2a: trySolve never returns sxRaised
      out2.add forkPath(p, p.pc & @[cond], p.env, p.uncertain)
    out2
  of isTargetLabel:
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
  of isDeref:
    # Phase 15 R1 (ADR-0010). `p[]` — a GROUND heap read. For each path:
    #   1. resolve the ref/ptr SymVal `p` (its `Ref_T`-sorted abstract address);
    #   2. lazily materialise `path.heaps[typeId]` to a fresh free
    #      `Z3Array[Ref_T, T_sym]` if this is the first deref of this pointee
    #      type on this path (heap is PER-PATH; the sort is PER-WALKER);
    #   3. `select(heap, p)` → the value-sorted ast → lift into a SymVal;
    #   4. bind it to the fresh let-name `stmt.dRetName`.
    # The select is decidable (QF_AUFLIA-ish); NO quantifier is asserted (the
    # G4 hang lesson). nil-fork lands R5; heapDepth bounding lands R9.
    let ctx = w.z3
    let typeId = refPointeeTypeId(stmt.dElemTy)
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      let refSV = lower(p.env, stmt.dPtr)
      let refAst = case refSV.kind
        of svRef: refSV.refAst
        of svPtr: refSV.ptrAst
        else:
          raise (ref SymexRefUnresolvedError)(
            msg: "deref of non-ref/ptr SymVal kind=" & $refSV.kind &
                 " (Cluster R R1 expects an svRef/svPtr at the deref site)")
      var newEnv = p.env
      # Materialise the per-path heap for this pointee type on first use.
      var heap: Z3AnyAst
      if p.heaps.hasKey(typeId):
        heap = p.heaps[typeId]
      else:
        let refSort = allocRefSort(ctx, stmt.dElemTy)
        heap = mkHeapArrayVar(ctx, refSort, stmt.dElemTy,
                              "heap_" & typeId)
      let valSV = heapSelect(ctx, heap, refAst, stmt.dElemTy)
      newEnv[stmt.dRetName] = valSV
      # R1 witness hook: if the dereffed ptr is a bare PARAM ref, record the
      # heap value under the param name so the witness reader renders `p[]`.
      if stmt.dPtr.kind == iekVar:
        currentHeapDerefVals[stmt.dPtr.vname] = valSV
      # Carry the (possibly freshly-materialised) heap forward on the surviving
      # path so a SECOND deref of the SAME ref reads the SAME array (a genuine
      # functional read — `p[] == 42 and p[] == 43` is unsat).
      var child = forkPath(p, p.pc, newEnv, p.uncertain)
      child.heaps[typeId] = heap
      survivors.add child
    survivors
  of isNew:
    # Phase 15 R2 (ADR-0010). `new T` allocation semantics. Per surviving path:
    #   1. `freshRef` increments `path.allocCounters[typeId]` (per-path; R1b
    #      threads + max-merges it) and mints a fresh `Ref_T` const
    #      `ref_<typeId>_<n>` (n = the new counter value) via raw `Z3_mk_const`;
    #   2. `assertFreshness` asserts the GROUND distinctness inequalities into
    #      `path.pc` — `newRef != nil` (always) + `newRef != prior` for every
    #      prior live ref of this sort on this path (CAPPED by
    #      `settings.maxFreshnessAssertions` → `heFreshnessCapExceeded` sevHint,
    #      a sound over-approximation);
    #   3. the fresh ref is bound in the env under `stmt.nRetName` as an
    #      `svRef`/`svPtr` (so a later `p[]` deref / `p == q` compare resolves
    #      it through the ordinary ref machinery).
    # NO universal-∀ over the uninterpreted sort (the G4 hang lesson); all
    # inequalities are ground and decidable.
    let ctx = w.z3
    # `nRefTy` is the full `itRef`/`itPtr` type; the ref sort keys on the
    # POINTEE (matching `allocateSym(itRef)` and `isDeref`).
    let isPtr = stmt.nRefTy.kind == itPtr
    let pointee = if isPtr: stmt.nRefTy.ptrPointeeTy else: stmt.nRefTy.refPointeeTy
    let typeId = refPointeeTypeId(pointee)
    var survivors: seq[Path]
    for p in paths:
      if w.shouldStop: return survivors
      let refSort = allocRefSort(ctx, pointee)
      var child = forkPath(p, p.pc, p.env, p.uncertain)
      let newRef = freshRef(ctx, refSort, typeId, child)
      assertFreshness(ctx, child, typeId, newRef, w.settings)
      var newEnv = child.env
      if isPtr:
        newEnv[stmt.nRetName] = SymVal(kind: svPtr, ptrAst: newRef,
                                       ptrFamily: true, ptrPointee: pointee)
      else:
        newEnv[stmt.nRetName] = SymVal(kind: svRef, refAst: newRef,
                                       refPointee: pointee)
      child.env = newEnv
      survivors.add child
    survivors
  of isUnsupported:
    w.sawUnknown = true
    paths

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
    unknownExnWarnings.add SymexErrorInfo(kind: eeUnknownExnType,
                                          severity: sevWarning, msg: typeId)
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
    currentClosureCallErrors.add SymexErrorInfo(
      kind: ceClosureUnknownCallee, severity: sevError,
      msg: "closure call through `" & e.ccCallee &
           "` does not resolve to a closure value in scope")
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
  if not currentClosureBodies.hasKey(siteKey):
    # The closure was constructed but its body was never stashed — should not
    # happen (buildClosure always stashes). Classify rather than crash.
    currentClosureCallErrors.add SymexErrorInfo(
      kind: ceClosureUnknownCallee, severity: sevError,
      msg: "closure call through " & label &
           ": lambda body not reachable for descent")
    var fresh: seq[Z3Bool]
    return allocateSym(tInt(64, true), "__closureNoBody", fresh)
  let cb = currentClosureBodies[siteKey]
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
    currentClosureCallErrors.add SymexErrorInfo(
      kind: ceInlineBudgetExceeded, severity: sevError,
      msg: "closure call through " & label &
           " lowered with no active walk context (no body descent)")
    return funcApp
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  template w: untyped = wp[]   ## the live WalkCtx (mutable through the ptr)
  if w.frame.closureInlineCount >= w.settings.maxClosureInlineCount:
    currentClosureCallErrors.add SymexErrorInfo(
      kind: ceInlineBudgetExceeded, severity: sevError,
      msg: "closure-application descent exceeded maxClosureInlineCount (" &
           $w.settings.maxClosureInlineCount & ") at " & label)
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
  # caller's tables. Closure heap WRITES back out (return-merge) are inert until
  # R4 (closures cannot yet mutate the heap).
  let descentBase = Path(pc: @[], env: descentEnv,
                         uncertain: false,
                         heaps: currentCallerHeaps,
                         heapDepth: currentCallerHeapDepth,
                         allocCounters: currentCallerAllocCounters)
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
  for cp in frame.returnedPaths:                       # (a) explicit return
    if cp.pc.len == 0: continue
    sawValue = true
    assertArm(cp.pc[0 ..< cp.pc.high], cp.pc[^1])
  for cp in fallThrough:                                # (b) implicit result
    if cp.env.hasKey("result"):
      sawValue = true
      assertArm(cp.pc, retBindEq(funcApp, cp.env["result"]))
  # If the body produced NO value-bearing sub-path (e.g. an unhandled construct
  # left funcApp unconstrained), mark uncertain so a target reached through this
  # result degrades to sxUnknown rather than emitting a Z3-defaulted value.
  if not sawValue:
    w.sawUnknown = true
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
  else:
    raise newException(ValueError, "storeSeqElem: unsupported elem kind " & $elemTy.kind)

proc lowerSeqLit(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C4. `@[a, b, c]` → a CONCRETE-length svSeq: a fresh data array
  ## with each lowered element stored at its index, and `seqLen` pinned to the
  ## literal count (a numeral). Empty `@[]` → length-0 svSeq.
  let elemTy = e.seqLitElemTy
  var dataRaw = allocateSeqDataRaw(elemTy, "__seqlit.data")
  for i, ce in e.seqLitElems:
    let elemSV = lower(env, ce)
    dataRaw = storeSeqElem(dataRaw, elemTy, mkInt(i), elemSV)
  SymVal(kind: svSeq, seqLen: mkInt(e.seqLitElems.len),
         seqDataRaw: dataRaw, seqElemTy: elemTy)

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
    threshold = wp[].settings.seqInlineThreshold

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
      currentClosureCallErrors.add SymexErrorInfo(
        kind: ceUnsupportedHof, severity: sevError,
        msg: "filter over a symbolic-length seq is not supported (no Z3 " &
             "seqFilter HOF; axiomatize-filter deferred to Phase 16)")
      if currentWalkCtxPtr != nil:
        cast[ptr WalkCtx](currentWalkCtxPtr)[].sawUnknown = true
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(e.hofRetElemTy), "__hofFilterUnsupported", fresh)
    of "map":
      # Axiom path: `mapArray` (Z3_mk_map) — pointwise application of the
      # closure funcSym over the seq's data array. DECIDABLE array-map (no
      # universal quantifier; no G4-style hang). Result is a new seq with the
      # SAME (symbolic) length and a data array `r[i] = f(a[i])`.
      let cb = currentClosureBodies[(cloSV.closureSite.siteHash,
                                     cloSV.closureSite.declOrder)]
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
        currentClosureCallErrors.add SymexErrorInfo(
          kind: ceUnsupportedHof, severity: sevError,
          msg: "map axiom path supports only a capture-free int->int closure " &
               "over a symbolic seq[int]; this shape is deferred")
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
      currentClosureCallErrors.add SymexErrorInfo(
        kind: ceUnsupportedHof, severity: sevError,
        msg: "fold over a symbolic-length seq is modeled as an opaque " &
             "ground result (precise symbolic fold deferred)")
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
  except SymexOwnershipUnsupportedError as e:
    # Phase 15 R1a (ADR-0010, Breadth-LOW-L4): an `owned T` / `WeakRef[T]` /
    # `Atomic[T]` formal was allocated -> sxUnknown + heUnsupportedOwnership
    # (Invariant 3 — classified, out of scope for the cluster).
    RawResult(status: sxUnknown,
              errors: @[SymexErrorInfo(kind: heUnsupportedOwnership,
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

proc runSymexImpl(prog: SymexProgram,
                  target: SymexTarget,
                  settings: SymexSettings): RawResult =
  let ctx = newContext()
  setCurrentContext(ctx)
  extractionErrors = @[]   ## Phase 15 F7: reset per-run float-extraction error sink
  currentMaxBytesEncodingLen = settings.maxBytesEncodingLen  ## Phase 15 S7a
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
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()  ## Phase 15 C2a
  currentClosureBodies = initTable[      ## Phase 15 C2b: reset site→body map
    tuple[siteHash: int64, declOrder: int], ClosureBody]()
  currentClosureCallAxioms = @[]         ## Phase 15 C2b: reset ground-axiom sink
  currentClosureCallAxiomStrs = @[]      ## Phase 15 C2b: reset axiom-string hook
  currentClosureCallErrors = @[]         ## Phase 15 C2b: reset closure-call errors
  currentWalkCtxPtr = nil                ## Phase 15 C2b: set just before the walk
  currentBorrowReboxCounter = 0          ## Phase 15 G5: reset rebox-name counter
  currentRefSorts = initTable[string, RawZ3Sort]()    ## Phase 15 R1
  currentNilConsts = initTable[string, Z3AnyAst]()    ## Phase 15 R1
  currentHeapDerefVals = initTable[string, SymVal]()  ## Phase 15 R1
  currentCallerHeaps = initTable[string, Z3AnyAst]()  ## Phase 15 R1b
  currentCallerHeapDepth = 0                          ## Phase 15 R1b
  currentCallerAllocCounters = initTable[string, int]()  ## Phase 15 R1b
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
      env[p.name] = allocateSym(p.ty, p.name, initialPC)
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
      let promote = promoteLoose or promoteSound
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
        # isLoose: no range constraints, no audit entry — by design,
        # the user is told this is unsound and accepts it.
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
  discard walk(prog.body, @[initial], w)
  currentWalkCtxPtr = nil
  # Phase 15 G4 (ADR-0008 D4): mirror the live distinct-sort cache (populated by
  # `allocateSym` via the `currentDistinctSorts` threadvar) into WalkerStatics
  # for post-run inspection.
  for dn, de in currentDistinctSorts:
    w.statics.distinctSorts[dn] = de.sort
  # Phase 15 C2a (ADR-0009): mirror the live closure-funcSym cache (populated by
  # `lower(iekLambda)` via the `currentClosureSyms` threadvar) into WalkerStatics.
  for ck, fd in currentClosureSyms:
    w.statics.closureSyms[ck] = fd
  # Phase 15 R1 (ADR-0010): mirror the live ref-sort + nil-const caches
  # (populated by `allocateSym(itRef)` / `allocRefSort` via the `currentRefSorts`
  # / `currentNilConsts` threadvars) into WalkerStatics for post-run inspection.
  for tid, srt in currentRefSorts:
    w.statics.refSorts[tid] = srt
  for tid, nc in currentNilConsts:
    w.statics.nilConsts[tid] = nc
  var statsSeq: CallStats
  for name, st in w.callStats:
    statsSeq.add st
  # Phase 15 E4. Drain the unknown-exn-type warning sink, dedup'd by type name.
  # sevWarning never halts a verdict (Invariant 7), so it is appended to the
  # result's errors regardless of which verdict branch is taken below.
  var exnWarnings: seq[SymexErrorInfo]
  if unknownExnWarnings.len > 0:
    var seen: HashSet[string]
    for e in unknownExnWarnings:
      if e.msg notin seen:
        seen.incl e.msg
        exnWarnings.add e
  # Phase 15 G4. Drain the distinct-bijectivity-skipped hint sink, dedup'd by
  # message (one per distinct type whose base was FP/String). sevHint never
  # changes the verdict (Invariant 7), so it rides every branch alongside
  # exnWarnings — appended to `exnWarnings` so the existing append sites carry
  # it on sat/unsat/unknown uniformly.
  if distinctBijectivityHints.len > 0:
    var seenD: HashSet[string]
    for e in distinctBijectivityHints:
      if e.msg notin seenD:
        seenD.incl e.msg
        exnWarnings.add e
  # Phase 15 R2. Drain the freshness-cap hint sink, dedup'd by message (one per
  # ref type whose per-path distinctness inequalities hit the cap). sevHint
  # never changes the verdict (Invariant 7) — rides every branch via
  # `exnWarnings`, exactly the G4 bijectivity-skip drain above.
  if freshnessCapHints.len > 0:
    var seenF: HashSet[string]
    for e in freshnessCapHints:
      if e.msg notin seenF:
        seenF.incl e.msg
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
  let capForcedUnknown = block:
    var any = false
    for e in prog.parseErrors:
      if e.severity == sevError: any = true; break
    any
  # Phase 15 C2b. Drain the closure-call error sink (dedup'd by message). A
  # `ceClosureUnknownCallee`/`ceInlineBudgetExceeded` is `sevError`: the call's
  # semantics were not modeled, so the verdict MUST degrade to `sxUnknown`
  # (Invariant 3 — never a silent sat/unsat). Surface them on every branch.
  var closureErrs: seq[SymexErrorInfo]
  block:
    var seenC: HashSet[string]
    for e in currentClosureCallErrors:
      if e.msg notin seenC:
        seenC.incl e.msg
        closureErrs.add e
  let closureForcedUnknown = block:
    var any = false
    for e in closureErrs:
      if e.severity == sevError: any = true; break
    any
  if w.found.len > 0 and not capForcedUnknown and not closureForcedUnknown:
    var r = w.found[0]   ## Phase 15 Z4/E2a: found holds sxSat/sxRaised findings; take the first
    r.abstractions = log
    r.callStats = statsSeq
    if extractionErrors.len > 0:   ## Phase 15 F7: surface any float-extraction failures
      r.errors.add extractionErrors
    r.errors.add exnWarnings       ## Phase 15 E4
    r.errors.add prog.parseErrors  ## Phase 15 G1c
    r.errors.add closureErrs       ## Phase 15 C2b
    r
  elif w.sawUnknown or capForcedUnknown or closureForcedUnknown:
    RawResult(status: sxUnknown, abstractions: log, callStats: statsSeq,
              errors: exnWarnings & prog.parseErrors & closureErrs)
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

proc readSeqInt*(w: RawWitness, name: string): seq[int] =
  let n = if w.seqLens.hasKey(name): w.seqLens[name] else: 0
  result = newSeq[int](n)
  for i in 0 ..< n:
    let path = name & "." & $i
    if w.intVals.hasKey(path):
      result[i] = int(w.intVals[path])

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
