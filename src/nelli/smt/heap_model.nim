## RFC-0016 review D3c-6: the heap ALGEBRA, a real leaf module.
##
## The ref sorts and their nil consts, the heap keys, the leaf split of a
## compound value (`svLeafAsts` / `svWithLeaves` / `svPartsOf`), `heapSelect`
## and the heap cells (`HeapCell`, `svCellWf`, `heapCellStore`), the decl-kind
## probes that read a store/select chain back (`storedAt`, `peelSelect`,
## `heapChainDepth`), and the value operations the cell model rests on (the
## distinct sort and its rebox, the container cardinality registry, the
## discriminator domains, the int-width bridge).
##
## None of it names `WalkCtx` or `Path`. The walker arm (`walkHeapArm`, the
## nil-deref fork, `freshRef`, `assertFreshness`, the per-path `heapCellArrays`)
## stays in `runtime_heap.nim`, an include of `runtime.nim`, and calls this
## module directly. The two heavy verbs this module needs from `runtime.nim`
## (`allocateSym`, `iteSV`) come through `lowerHooks`; `checkedSelect` and the
## rest of the hot path are direct.
##
## Imports: std, `z3`, `./types`, `./symval`, `./walk_state`, `./z3check` only.
import std/tables
import std/options
import std/sets
import std/strutils
import z3
import ./types
import ./symval
import ./walk_state
import ./z3check

# Forward declarations: the container registry (below, with the runtime half
# of this file) reads the leaf split, whose bodies follow the cell model.
proc svLeafAsts*(sv: SymVal; ty: IRType = nil): seq[RawZ3Ast]

proc mkZ3IntLit*(v: int64): Z3Int {.inline.}
  ## Issue #163 W8 fwd-decl (Phase 14 A6; real definition below, beside
  ## `allocRefSort`'s own fwd-decl just under this proc) —
  ## `rangeCondsIfNeeded`'s `svInt` arm needs it before its real definition
  ## appears.

var allocEnumZeroLegal* {.threadvar.}: bool
  ## RFC-0005 S8z. Set by `freshRetSym` for the duration of its allocation:
  ## a call's return value can hold an enum's ordinal 0 even when no member
  ## has it (Nim zero-fills an untouched `result`, probed), so the range
  ## conditions of an enum without ordinal 0 admit 0 there. Inputs (params)
  ## keep the exact member range: their witness must render as a member.

proc rangeCondsIfNeeded*(v: SymVal, ty: IRType): seq[Z3Bool] =
  ## Issue #163 review R11. The CONSTRAINT half of the two-obligation
  ## contract every `range[lo..hi]`-typed value carries wherever it is
  ## materialized from a backing store: (a) here — assert the symbol lies
  ## in `[lo,hi]` on the solver path, or a free model can pick an illegal
  ## value and produce a false `sxSat`; (b) `clampWitnessField`, below near
  ## `clampToDeclaredRange` — clamp the WITNESS value read back out of an
  ## already-solved model, or an unconstrained/unread cell's default (`0`)
  ## can fall outside the range and raise a real `RangeDefect` reconstructing
  ## it in the caller's own process.
  ##
  ## Before this helper existed, every new backing-store shape re-derived
  ## the guard-and-call by hand, and every one of them shipped the bug at
  ## least once before someone noticed: W2 (seq elements), W4 (ref-object
  ## fields), R3 (ref-to-variant arm fields), R4 (Table values) are the SAME
  ## missing abstraction, found one shape at a time. A NEW materialization
  ## path (another container kind, another heap shape) inherits the
  ## obligation by construction ONLY if it calls this proc instead of
  ## re-deriving the guard — that is the whole reason this exists.
  ##
  ## Signedness comes from the TYPE, matching `cmpBV`'s own split: comparing
  ## an unsigned BV with signed predicates reads `0xFF` as -1 and would
  ## reject a legal value for `range[0'u8..255'u8]`.
  ##
  ## Issue #163 W8: `v` is not always BV-sorted. `allocateSym`'s two
  ## `isIntOffset` arms (bare scan-offset return, traced tuple position)
  ## allocate a Z3-Int-sorted `svInt` directly rather than the type-driven
  ## BV default (`bvVar`) — the exact promotion `runSymexImpl`'s own
  ## top-level-param `isIntOffset` branch already makes, and that branch
  ## re-asserts the declared range as `zi >= lo`/`zi <= hi` (Z3Int
  ## comparisons, since a Z3Int has no BV predicate to reuse). `bvRangeConds`
  ## dispatches on `v.kind` and returns `@[]` for anything that isn't one of
  ## the four BV kinds — by design for a BV-allocated value (dropping a
  ## refinement only over-approximates), but WRONG here: silently applying
  ## that same fallback to an `svInt` would make this call a no-op for
  ## exactly the case it exists to cover. Handle `svInt` here, before
  ## falling through to `bvRangeConds` for the BV kinds.
  if ty.kind == itInt and ty.hasRange:
    let conds =
      if v.kind == svInt:
        @[v.zi >= mkZ3IntLit(ty.rangeLo), v.zi <= mkZ3IntLit(ty.rangeHi)]
      else:
        bvRangeConds(v, ty.rangeLo, ty.rangeHi, ty.signed)
    if allocEnumZeroLegal and ty.enumName.len > 0 and conds.len == 2 and
        not (ty.rangeLo <= 0 and 0 <= ty.rangeHi):
      # RFC-0005 S8z: see `allocEnumZeroLegal`.
      let zero =
        if v.kind == svInt: @[v.zi >= mkZ3IntLit(0), v.zi <= mkZ3IntLit(0)]
        else: bvRangeConds(v, 0, 0, ty.signed)
      if zero.len == 2:
        return @[(conds[0] and conds[1]) or (zero[0] and zero[1])]
    conds
  else:
    @[]

proc mkZ3IntLit*(v: int64): Z3Int =
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

var distinctBijectivityHints* {.threadvar.}: seq[SymexErrorInfo]
  ## Phase 15 G4. Accumulator for `geDistinctBijectivitySkipped` (sevHint),
  ## emitted when a distinct type's base is FP/String (bijectivity elided).
  ## Reset at `runSymexImpl` entry; drained into `RawResult.errors` on every
  ## verdict branch (a hint never changes the verdict). Mirrors E4's
  ## `unknownExnWarnings` threadvar.

var distinctSortNames* {.threadvar.}: seq[string]
  ## Phase 15 G4 test hook: the order distinct sorts were first allocated this
  ## run (so a test can assert "two sorts allocated" for a nested chain).

func cellDomain*(ty: IRType): tuple[bounded: bool, lo, hi: int64] =
  ## RFC-0005 S8z. The cells a `HashSet[ty]` element can occupy, as an
  ## interval of the cell read with `ty`'s signedness: the declared range,
  ## else the width's. `bounded` is false for a full 64-bit type, whose every
  ## cell is a value.
  ## RFC-0005 S8at: a float `Table` key's cell is its IEEE bit pattern
  ## (`floatKeyCell`): every 64-bit cell for a `float64`, the low 32 bits for
  ## a `float32`.
  if ty.kind == itFloat64: (false, 0'i64, 0'i64)
  elif ty.kind == itFloat32: (true, 0'i64, 0xFFFF_FFFF'i64)
  elif ty.kind == itBool: (true, 0'i64, 1'i64)
  elif ty.hasRange: (true, ty.rangeLo, ty.rangeHi)
  elif ty.width == 64: (false, 0'i64, 0'i64)
  elif ty.signed:
    let h = (1'i64 shl (ty.width - 1)) - 1
    (true, -h - 1, h)
  else: (true, 0'i64, (1'i64 shl ty.width) - 1)

func cellDomainSize*(ty: IRType): int64 =
  ## RFC-0005 S8z. The number of cells in `cellDomain(ty)`, capped at
  ## `high(int64)` (only compared against the 1024 size ceiling).
  let d = cellDomain(ty)
  if not d.bounded: return high(int64)
  if (ty.kind == itInt and ty.signed) or (d.lo >= 0 and d.hi >= 0):
    let span = d.hi -% d.lo
    if span < 0 or span == high(int64): high(int64) else: span + 1
  else:
    let span = cast[uint64](d.hi) - cast[uint64](d.lo)
    if span >= uint64(high(int64)): high(int64) else: int64(span) + 1

type ContainerCardRegistry* = object
  ## RFC-0005 S8f. What ties a `Table`'s / `HashSet`'s `len` to its content.
  ##
  ## The model of a `Table[string, int]` is a present array, a data array
  ## and a size integer (`allocateSym`'s `itTable` arm); a `HashSet[int]` is a
  ## member array and a size. Before S8f nothing related the size to the
  ## array: `len` was a free integer in `[0, 1024]`. Two defects followed.
  ##   * The MODEL admitted states no real table has. `t.len == 0 and
  ##     t.hasKey("a")` was a clean, false `sxSat`, and a `[]=`/`incl`
  ##     growing a table/set that already held another key could leave
  ##     `len == 1`.
  ##   * The EXTRACTOR ignored `len`: a `t.len == 2` witness rendered `{:}`,
  ##     a clean `sxSat` whose witness does not reach the target.
  ## Z3 has no cardinality over arrays, but none is needed. The program
  ## observes an array only by `select`ing it at KEY TERMS, and the run
  ## records every one here (`noteTableKey` / `noteSetKey`, at each
  ## `select`/`store` site). A model is realizable iff, for every allocated
  ## table/set (`registerTableBase` / `registerSetBase`, at allocation),
  ## `size >=` the number of DISTINCT key-term values at which the array is
  ## present: the real content is then those keys plus `size - count` keys
  ## no term names, which no `select` can observe. `containerCardConds`
  ## asserts exactly that inequality into every `trySolve`. It is a fact
  ## about every real table for ANY values of the terms, including terms
  ## recorded on another path (their symbols are then free), so it prunes
  ## only unrealizable models -- never a real input, never a false
  ## `sxUnsat`. The extractors (`extractTableEntries` /
  ## `extractSetMembers`) render that same content, so a clean witness
  ## reproduces by construction.
  ##
  ## Registries are global to the run, not per array: a store makes a new
  ## array handle, and the key of every store and select on any array
  ## derived from a base is a select on the base (store(a, k, v)[j] is
  ## a[j] for j != k). Reset at `runSymexImpl` entry. Entries are deduped
  ## by Z3 AST handle (Z3 hash-conses equal terms).
  tabBases*: seq[tuple[present: Z3AnyAst, size: Z3Int]]
  tabKeys*:  seq[Z3String]
  setBases*: seq[tuple[members: Z3AnyAst, size: Z3Int, elemTy: IRType]]
    ## RFC-0005 S8z: `elemTy` bounds the cells a member can occupy
    ## (`cellDomain`) for a narrower element type.
  setKeys*:  seq[Z3BitVec[64]]
  tabTreeBases*: seq[SymVal]
    ## RFC-0005 S8at. Every INPUT table whose value is a container
    ## (`tvTree`): the facts a free value of its value type has
    ## (`svCellWf`) hold at every key, and are stated at every key term.
  seen:      HashSet[pointer]

var containerCard* {.threadvar.}: ContainerCardRegistry
  ## RFC-0005 S8f. The run's `ContainerCardRegistry`. Replaces v65's
  ## per-array `setMembershipKeyTerms`, which keyed on the membership
  ## array's handle and so lost every key tested after an `incl`/`excl`.

proc firstSighting*(raw: pointer): bool =
  ## RFC-0005 S8f. True the first time `raw` is registered this run.
  if raw in containerCard.seen: return false
  containerCard.seen.incl raw
  true

proc registerSetBase*(members: Z3AnyAst; size: Z3Int; elemTy: IRType)

proc registerTableBase*(present: Z3AnyAst; size: Z3Int; keyTy: IRType) =
  ## RFC-0005 S8f. An allocated `Table[string, int]`: its present array and
  ## size (see `ContainerCardRegistry`). RFC-0005 S8ar: a table keyed by a
  ## 64-bit cell (`isTableKeyTy`) has the present array a `HashSet` of its
  ## key type has, and the same facts: it is registered as one.
  if keyTy.kind != itString:
    registerSetBase(present, size, keyTy)
  elif firstSighting(cast[pointer](present.raw)):
    containerCard.tabBases.add (present: present, size: size)

proc registerSetBase*(members: Z3AnyAst; size: Z3Int; elemTy: IRType) =
  ## RFC-0005 S8f. An allocated `HashSet[T]`: its member array and size.
  if firstSighting(cast[pointer](members.raw)):
    containerCard.setBases.add (members: members, size: size, elemTy: elemTy)

proc registerTabTreeBase*(sv: SymVal) =
  ## RFC-0005 S8at. An input table holding container values (see
  ## `ContainerCardRegistry.tabTreeBases`); any other value is ignored.
  if sv.kind == svTable and isTableContainerValTy(sv.tabValTy) and
     firstSighting(cast[pointer](sv.tabDataRaw.raw)):
    containerCard.tabTreeBases.add sv

type
  HeapKeyShape* = object
    ## RFC-0005 S8h. What `mkHeapArrayVar` knew about a heap it introduced.
    valTy*:     IRType  ## the heap's value type: a field's, a discriminator's,
                       ## or a whole scalar pointee's
    variantTy*: IRType  ## the variant object, for its `__@disc` and
                       ## `__@<ord>__<field>` heaps; nil otherwise

var intHeapIsInt* {.threadvar.}: bool
  ## RFC-0005 S8as. A heap of plain `int` (`intHeapCell`) is Int-sorted:
  ## the run's `integerSemantics` is not `isExact` and every signed 64-bit
  ## int parameter is bound to an Int. Cleared by `resetSymexRunState`, set
  ## by `runSymexImpl` once the parameters are bound.

func intHeapCell*(ty: IRType): bool =
  ## RFC-0005 S8as. `ty` is Nim's `int` (64-bit, signed, no declared range)
  ## and the run's ints are Int-sorted (`intHeapIsInt`): its heap -- a
  ## `ref int` / `ptr int` cell, an `int` field -- is `(Array Ref Int)`.
  ## It was `(Array Ref (_ BitVec 64))`, and under `isOptimised` a param
  ## with an asserted range is an Int (`promoteSound`), so storing it went
  ## through `int2bv` and reading it back through `bv2int`: with `v` in
  ## `(-1000, 1000)`, `let r = new int; r[] = v; r[] += 1; r[] != v + 1`
  ## took Z3 55 s for its UNSAT. A width-stamped Int (`ziWidth = 64`) keeps
  ## every overflow obligation (`overflowCondInt`), so the values and the
  ## defects are the bit-vector's. A BV value is stored through `bv2int`
  ## (`heapStoreValue`). Otherwise the heap stays a bit-vector: a BV value
  ## stored through `bv2int` and read back into a BV comparison is the F5
  ## `int2bv(bv2int(v))` shape, which is the slow direction the other way.
  {.cast(noSideEffect).}:
    intHeapIsInt and ty != nil and ty.kind == itInt and ty.signed

var heapKeyShapes* {.threadvar.}: Table[string, HeapKeyShape]
  ## RFC-0005 S8h. Heap key -> `HeapKeyShape`, written by `mkHeapArrayVar`.
  ## `buildHeapSnapshot` renders a cell's fields from the heaps themselves:
  ## the IR pointee of a recursive field is an empty placeholder by
  ## construction (`namedRefPlaceholder`), so it cannot say which fields a
  ## cell has or what their types are. Reset at `runSymexImpl` entry.

proc rawConstOf*(ctx: Z3Context, sort: RawZ3Sort, name: string): RawZ3Ast
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

proc baseIsDecidable*(base: IRType): bool =
  ## Phase 15 G4. The bijectivity-axiom fragment: int / BV / bool. Anything
  ## else (FP, string, and — conservatively — composite bases) is skipped.
  ## A nested distinct base is decidable iff ITS base is (recurse).
  case base.kind
  of itInt, itBool: true
  of itDistinct: baseIsDecidable(base.distinctBase)
  else: false

proc realBaseKind*(base: IRType): IRTypeKind =
  ## RFC-0005 S8bg. `base`'s kind, walked through every `distinct` wrapper
  ## to the first non-`itDistinct` kind: for `Km = distinct Meters`,
  ## `Meters = distinct int` (so `Km`'s own `distinctBase` is `itDistinct`
  ## itself), this is `itInt`, not `itDistinct` -- the kind the
  ## `geDistinctBijectivitySkipped` hint names, and the one
  ## `baseIsDecidable` actually judges.
  case base.kind
  of itDistinct: realBaseKind(base.distinctBase)
  else: base.kind

proc rawConstOf*(ctx: Z3Context, sort: RawZ3Sort, name: string): RawZ3Ast =
  ## Fresh named const of a (possibly uninterpreted) sort.
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  ctx.checkErr Z3_mk_const(ctx.raw, sym, sort)

proc isBijectivityBaseSym*(sv: SymVal): bool {.inline.} =
  ## Phase 15 G4. The SymVal kinds over which the bijectivity axioms are
  ## decidable: bool, the genuine Z3Int, AND the BV families (Nim `int` and the
  ## fixed-width ints allocate as `svBV*` by default — `bvVar`). Anything else
  ## (FP, string, composite) skips bijectivity.
  sv.kind in {svBool, svInt, svBV8, svBV16, svBV32, svBV64}

proc rawAstOf*(sv: SymVal): RawZ3Ast =
  ## The raw ast of a decidable-base primitive SymVal (bool / int / BV).
  case sv.kind
  of svInt:  sv.zi.raw
  of svBool: sv.bo.raw
  of svBV8:  sv.bv8.raw
  of svBV16: sv.bv16.raw
  of svBV32: sv.bv32.raw
  of svBV64: sv.bv64.raw
  else:
    raise newException(ValueError, "rawAstOf: unsupported base kind " & $sv.kind)  # [raise-audited: category-c: bijectivity-guarded (both call sites pre-check isBijectivityBaseSym)]

proc rawSortOf*(sv: SymVal): RawZ3Sort =
  ## The Z3 sort underlying a decidable-base primitive SymVal. Used to declare
  ## the inject/eject domains/ranges and bind the base-side quantified variable.
  let ctx = requireCurrentContext()
  ctx.checkErr Z3_get_sort(ctx.raw, rawAstOf(sv))

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
  ## RFC-0005 S8ca: a seq, table or set (a capture, or a parameter of a
  ## proc value, `paramSorts`) contributes the sort of each of its leaves
  ## (`svLeafAsts`), as a nested tuple does, and an array its elements'. It had no single-leaf sort, and
  ## a proc value taking a seq declined (`seUnsupportedCompoundSortLeaf`).
  let ctx = requireCurrentContext()
  case sv.kind
  of svTuple:
    for f in sv.fields:
      for s in sortOfTuple(f): result.add s
  of svSeq, svTable, svSet:
    for leaf in svLeafAsts(sv):
      result.add ctx.checkErr Z3_get_sort(ctx.raw, leaf)
  of svArray:   # RFC-0005 S8ca: its elements, as a tuple's fields
    for e in sv.arrElems:
      for s in sortOfTuple(e): result.add s
  else:
    result.add ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(sv))

proc ensureDistinctSort*(ty: IRType): DistinctSortEntry =
  ## Phase 15 G4 (ADR-0008 D4), factored out of `allocDistinctSym` by
  ## RFC-0005 S8ad. The "DistinctName" uninterpreted sort, its inject/eject
  ## func-decls, and (decidable base) the bijectivity bookkeeping, created
  ## AT MOST ONCE per (name, run) -- guarded by the `currentDistinctSorts`
  ## cache. `reboxDistinct` calls it too: a borrowed arithmetic result of a
  ## distinct type that no parameter carries (`var m = Meters(0); m = m +
  ## Meters(1)`) found no sort and faulted the walker before S8ad.
  let ctx = requireCurrentContext()
  let name = ty.distinctName
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
    let baseRep = lowerHooks.allocateSym(ty.distinctBase, name & ".__baseSort", scratchPC,
                                          false, @[])
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
      #
      # RFC-0005 S8at: a COMPOSITE base (`distinct seq[int]`, `distinct
      # (int, bool)`, a distinct object) has no single Z3 sort, so no
      # inject/eject decl can be declared over it; deriving one recorded
      # `seUnsupportedCompoundSortLeaf` and declined every such parameter.
      # Neither decl is ever APPLIED for a non-decidable base (only the
      # decidable branch's ground eject pin applies `eject`), so a
      # composite base simply has none: the distinct value is its boxed base
      # (`distinctBaseSym`), which every read ejects to (`ejectBase`).
      var dentry = DistinctSortEntry(sort: sort)
      if baseRep.kind notin {svTable, svSet, svSeq, svArray, svTuple,
                             svVariant, svMultiVariant}:
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
        dentry.inject = inject
        dentry.eject = eject
      currentDistinctSorts[name] = dentry
      # CR-9 Stage 4: also populate WalkerStatics when a walk is active.
      syncDistinctSortEntry(name, dentry)
      # RFC-0005 S8bg: this branch is also reached for a distinct-of-a-
      # distinct whose REAL base is decidable (`Km = distinct Meters`,
      # `Meters = distinct int`): `ty.distinctBase` is itself `itDistinct`,
      # so `isBijectivityBaseSym(baseRep)` above is false (`baseRep` is a
      # nested `svDistinct`, not a primitive) even though
      # `baseIsDecidable` (which recurses) says the chain's true base is
      # fine. No axiom is asserted either way here (the ground eject pin
      # above needs a primitive `baseRep`, which a nested distinct is
      # not -- a precision gap, not fixed by this hint), but the hint
      # claiming a non-decidable base is wrong for that case and is
      # skipped; it still fires for a genuinely non-decidable real base
      # (FP/string) and for a composite one (S8at).
      if not baseIsDecidable(ty.distinctBase):
        let bijHint = SymexErrorInfo(
          kind: geDistinctBijectivitySkipped, severity: severity(geDistinctBijectivitySkipped),
          msg: "bijectivity axiom skipped for distinct `" & name &
               "` over non-decidable base " & $realBaseKind(ty.distinctBase) &
               " (FP/String): the distinct sort is modeled without the " &
               "inject/eject round-trip guarantee")
        distinctBijectivityHints.add bijHint      # threadvar: fallback
        syncDistinctBijectivityHint(bijHint)      # CR-9 Stage 5: also WalkCtx
  currentDistinctSorts[name]

proc discEqBV*[W: static int](bv: Z3BitVec[W]; tagOrd: int64): Z3Bool =
  ## `bv == tagOrd`; a numeral `bv` (a constructed object's own discriminator)
  ## is a Boolean literal, so a merge on it folds (`iteFolded`, `checkedIte`).
  let eq = bv == mkBitVec[W](tagOrd)
  if not isNumeralAst(bv.ctx, bv.raw): return eq
  let ctx = bv.ctx
  let r = ctx.checkErr Z3_simplify(ctx.raw, eq.raw)
  if Z3_get_bool_value(ctx.raw, r) == Z3_L_UNDEF: eq
  else: wrap[Z3Bool](ctx, r)

proc variantDiscEq*(d: SymVal, tagOrd: int64): Z3Bool =
  ## `disc == tagOrd` over a variant discriminator's SymVal, whatever BV
  ## width (or `svInt`/`svBool` fallback) it was allocated at. Round-6 A2
  ## (ADR-0029) extraction: this file previously carried the identical
  ## closure as three separate copies — `allocateSym`'s `itVariant` arm
  ## (arm-disjunction), `isVariantField`'s walker arm (in-arm guard), and
  ## `retBindEq`'s `svVariant` arm (per-arm implication guard) — collapsed
  ## here so a future 4th site does not become a 4th copy.
  case d.kind
  of svBV8:  discEqBV(d.bv8, tagOrd)
  of svBV16: discEqBV(d.bv16, tagOrd)
  of svBV32: discEqBV(d.bv32, tagOrd)
  of svBV64: discEqBV(d.bv64, tagOrd)
  of svInt:  d.zi   == mkZ3IntLit(tagOrd)  ## Phase 14 A6
  of svBool: d.bo   == mkBool(tagOrd != 0)  ## Phase 15 F9c: bool disc
  else:
    raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (allocateSym's itVariant/itMultiVariant arms only ever allocate a BV/Int/Bool discriminator)]
      "variantDiscEq: discriminator must be a BV or Z3Int kind (got " &
      $d.kind & ")")

proc discDomainOf*(arms: seq[VariantArm];
                  discTags: seq[tuple[name: string, ord: int]];
                  discTy: IRType): tuple[minOrd, maxOrd: int64, ordSet: seq[int]] =
  ## The body of `discriminatorDomain` (below), over one `case` section's
  ## arms, enum domain and discriminator type. RFC-0005 S8s split it out so
  ## a multi-variant axis (`axisDiscriminatorDomain`) shares it.
  var hasElse = false
  for arm in arms:
    if arm.isElse:
      hasElse = true
      break
  let rangeAliasElseDomain =
    hasElse and discTags.len == 0 and discTy.hasRange
  if rangeAliasElseDomain:
    return (discTy.rangeLo, discTy.rangeHi, newSeq[int]())
  var minOrd = high(int64)
  var maxOrd = low(int64)
  var ordSet: seq[int]
  for arm in arms:
    if arm.tagOrdinal < 0: continue  # else sentinel
    if int64(arm.tagOrdinal) < minOrd: minOrd = int64(arm.tagOrdinal)
    if int64(arm.tagOrdinal) > maxOrd: maxOrd = int64(arm.tagOrdinal)
    ordSet.add arm.tagOrdinal
  for dt in discTags:
    if int64(dt.ord) < minOrd: minOrd = int64(dt.ord)
    if int64(dt.ord) > maxOrd: maxOrd = int64(dt.ord)
    if dt.ord notin ordSet: ordSet.add dt.ord
  if minOrd == high(int64):
    # No non-else arms AND no discTags -- degenerate.
    minOrd = 0
    maxOrd = 0
  (minOrd, maxOrd, ordSet)

proc discriminatorDomain*(ty: IRType):
    tuple[minOrd, maxOrd: int64, ordSet: seq[int]] =
  ## Issue #163 review R12 extraction. THE single decision of what values a
  ## variant discriminator may legally take -- previously computed
  ## independently in two places: `allocateSym`'s `itVariant` arm (the
  ## BV-disc disjunction) and `runSymexImpl`'s `isOptimised` disc-promotion
  ## (the Z3Int bound + disjunction). Both re-derived the same
  ## `rangeAliasElseDomain` guard by hand, which is how issue #163 W6 (a
  ## range-alias `else:` arm's domain wrongly narrowed to just the explicit
  ## `of N:` literals, making every else-covered value unreachable) had to
  ## be fixed twice.
  ##
  ## `ty` is the *variant's* own IRType (it carries `vArms`, `vDiscTags`,
  ## `vDiscTy`) -- not the discriminator field's IRType.
  ##
  ## Exported (unlike its two callers) specifically so this decision can be
  ## unit-tested directly -- pure, no Z3 context -- see
  ## `tests/tsymex_163rev_disc_domain.nim`.
  ##
  ## `ordSet.len == 0` on return means "assert no explicit per-ordinal
  ## disjunction" -- either because the range-alias-else-domain case
  ## applies (a non-enum, e.g. `range[lo..hi]`, discriminator with an
  ## `else:` arm: its legal domain IS its own declared range, which is
  ## asserted separately by the discriminator's own allocation, so an
  ## explicit disjunction over just the `of N:` literals would falsely
  ## exclude every else-covered value), or because the variant is
  ## degenerate (no arms, no tags -- `minOrd`/`maxOrd` collapse to 0).
  ##
  ## `hasElse` is derived here from `arm.isElse` rather than taken as a
  ## parameter: both call sites already had this fact on hand only by
  ## re-scanning `vArms` themselves (one via `arm.isElse`, the other via
  ## the equivalent `arm.tagOrdinal < 0` sentinel check -- the two are
  ## paired at construction time in `dsl_typebridge.nim` and can't
  ## diverge), so folding the scan in here removes that third small
  ## duplication too.
  discDomainOf(ty.vArms, ty.vDiscTags, ty.vDiscTy)

proc axisDiscriminatorDomain*(ax: VariantAxis):
    tuple[minOrd, maxOrd: int64, ordSet: seq[int]] =
  ## RFC-0005 S8s. `discriminatorDomain` for one axis of a multi-variant.
  ## `allocateSym`'s multi-variant arm used to build its own disjunction
  ## over the axis's arm ordinals, the `else` arm's sentinel (-1) among
  ## them, so an ordinal an `else` arm covers was never a value of an
  ## allocated discriminator (a false `sxUnsat`), and -1 was. The same
  ## decision as a single `case` now, from the same code.
  discDomainOf(ax.arms, ax.discTags, ax.discTy)

proc ejectBase*(sv: SymVal): SymVal =
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

proc degradeAlloc*(ty: IRType, kind: SymexErrorKind, msg: string,
                   tag: string): SymVal =
  ## Fix-slice item 9 (round-6 re-review): pairs `allocDegrade` (the taint
  ## record) with `allocateSym(ty, freshDegradeName(tag), ...)` (the
  ## uniquified fresh placeholder) into ONE call. The two are meant to
  ## ALWAYS travel together at a site shaped like this — the taint record
  ## and the placeholder's collision-safe name are two halves of the same
  ## decline — but nothing enforced the pairing before this slice (item 3/4
  ## of this same re-review found TWO sites where `freshDegradeName` had
  ## been dropped, reverting to a bare fixed name that collides across
  ## repeat hits within one run). `tests/tsymex_r6_n38_degrade_pairing_audit.nim`
  ## (this item's own audit, n36-style) greps the source for exactly this
  ## shape going forward.
  ##
  ## `allocDegrade` remains directly callable on its own for the sites that
  ## do NOT fit this shape:
  ##   - the `.unalloc`-suffixed `baseName` placeholders (the param/witness/
  ##     table/set catch-alls just above this proc in the file) — those key
  ##     off the ALLOCATION's own name, never a fresh counter, so pairing
  ##     with `freshDegradeName` would be a no-op at best and a naming
  ##     regression at worst (losing the `.unalloc` convention downstream
  ##     tooling may key on).
  ##   - the vacuous `mkBool(true)`/forwarded-operand sites (`retBindEq`'s
  ##     svSeq/composite arms, `iteSV`'s svClosure arm, `lowerBorrowOp`'s
  ##     catch-all) — no name is allocated at all; the existing value (or a
  ##     no-op `true`) is reused directly.
  ##   - the ONE documented `rawConstOf` exception (`iteSV`'s `svUninterpRef`
  ##     arm — see the CR-1c table's own doc, above) — still pairs with
  ##     `freshDegradeName`, but through `rawConstOf` rather than
  ##     `allocateSym`, so it does not fit this proc's `ty`-driven signature.
  ##   - `runtime_heap.nim`'s sites, which "handle their own" pairing: heap
  ##     degrades follow `allocDegrade` + a fresh `allocateSym` with an
  ##     env-rebind + `forkPathTainted`/`drainPendingLowerEffects` (`Path`-
  ##     scoped fork/drain machinery), a different taint sink than the bare
  ##     `freshDegradeName` counter this helper wraps.
  allocDegrade(kind, msg)  # [pairing-audited: this IS the pairing helper's own body]
  var fresh: seq[Z3Bool]
  lowerHooks.allocateSym(ty, freshDegradeName(tag), fresh, false, @[])

proc reboxDistinct*(distinctTy: IRType, base: SymVal): SymVal =
  ## Phase 15 G5. Re-box a BASE SymVal as a fresh `svDistinct` of `distinctName`
  ## — the result of a borrowed ARITHMETIC operator (`+`/`-`/`*`/`/` returning
  ## the distinct type). A fresh opaque const of the distinct sort carries the
  ## type-wall identity; the COMPUTED base value is boxed underneath so it ejects
  ## back correctly and the witness renders through the eject-reader chain.
  ##
  ## This operates entirely on the G4 boxed base — it does NOT apply the Z3
  ## `inject_T` function (which HANGS on the uninterpreted-fn-over-BV / MBQI
  ## combination, per the G4 finding).
  ##
  ## RFC-0005 S8ad: the sort comes from `ensureDistinctSort`. It used to be
  ## ASSUMED present because "the operands were already allocated as this
  ## distinct type", but `D(x)` is the parser's identity (S8p), so a local
  ## `var m = Meters(0); m = m + Meters(1)` re-boxes a distinct type no
  ## allocation ever saw: `weInternalWalkerFault` ("distinct sort not
  ## allocated") at the base.
  let ctx = requireCurrentContext()
  let distinctName = distinctTy.distinctName
  let entry = ensureDistinctSort(distinctTy)
  inc currentBorrowReboxCounter
  let constName = "borrow_" & distinctName & "#" & $currentBorrowReboxCounter
  let dAny = wrap[Z3AnyAst](ctx, rawConstOf(ctx, entry.sort.raw, constName))
  let boxed = new(SymVal)
  boxed[] = base
  SymVal(kind: svDistinct, distinctAst: dAny, distinctName: distinctName,
         distinctBaseSym: boxed)

proc bvTermToZ3Int*[W: static int](bv: Z3BitVec[W], signed: bool): Z3Int =
  ## `bv` as a Z3 Int, read as signed or unsigned. RFC-0005 S8o: a NUMERAL
  ## is folded here, to the Int numeral of its Nim value. Z3 builds a signed
  ## `bv2int` of a constant as `ite(bvslt c 0, bv2int c - 2^W, bv2int c)`
  ## and leaves it unevaluated, so every constant string index (`s[3]`)
  ## used to reach the solver in that form (S8k's As-landed note). A
  ## symbolic `bv` keeps Z3's `bv2int`.
  let ctx = bv.ctx
  if isNumeralAst(ctx, bv.raw):
    let u = parseBiggestUInt(getNumeralString(bv))   # 0 ..< 2^W, W <= 64
    let text =
      if signed and W < 64 and u >= (1'u64 shl (W - 1)):
        "-" & $((1'u64 shl W) - u)
      elif signed and W == 64 and u >= (1'u64 shl 63):
        "-" & $((not u) + 1)
      else: $u
    return wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                                      ctx.checkErr Z3_mk_int_sort(ctx.raw)))
  wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, bv.raw, signed))

proc bvToZ3Int*(sv: SymVal): Z3Int =
  ## Z3-level conversion of a typed BV SymVal to Z3Int. Used when a
  ## BV-shaped value (e.g. a Nim `int` param `i`) meets a Z3Int-shaped
  ## operand (e.g. `s.len`). Z3's `bv2int` is the canonical conversion;
  ## a constant is folded first (`bvTermToZ3Int`, RFC-0005 S8o).
  case sv.kind
  of svBV8:  bvTermToZ3Int(sv.bv8, sv.signed)
  of svBV16: bvTermToZ3Int(sv.bv16, sv.signed)
  of svBV32: bvTermToZ3Int(sv.bv32, sv.signed)
  of svBV64: bvTermToZ3Int(sv.bv64, sv.signed)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: bijectivity-guarded (only reached from toZ3Int's own BV-kind-guarded arm)]
      "bvToZ3Int: not a BV — got " & $sv.kind)

proc toZ3Int*(sv: SymVal): Z3Int =
  ## Coerce an int-typed SymVal (svInt or BV) to Z3Int.
  case sv.kind
  of svInt: sv.zi
  of svBV8, svBV16, svBV32, svBV64: bvToZ3Int(sv)
  of svDistinct:
    # RFC-0005 S8bc (item 2): a `distinct` int used at its base (a borrowed
    # `$`/`abs` lowered as the base routine on the unwrapped argument). The
    # ejected base is the value Nim's `T(d)` gives (`ejectBase`).
    toZ3Int(ejectBase(sv))
  else:
    raise newException(ValueError,  # [raise-audited: category-c: int-family-only reachability (every call site pre-guards to svInt/BV kinds)]
      "toZ3Int: not an int-typed SymVal — got " & $sv.kind)

var intOfBV* {.threadvar.}: Table[uint, tuple[zi: Z3Int, bv: SymVal]]
  ## RFC-0005 S8ax. Each Int a bit-vector was converted to at a sort
  ## boundary (`toSvIntPreserving`), keyed by the Int term's address, with
  ## the bit-vector it came from. The entry holds the term, so the address
  ## is not reused for another term while it is listed. `reconcileInt` and
  ## `stampedIntToBV` take the bit-vector back instead of converting the
  ## Int again: `int2bv(bv2int(v))` and `bv2int(r) == bv2int(v)` are exact
  ## but cost Z3 minutes, and since S8ax every signed `int` heap is
  ## Int-sorted (`intHeapCell`), so a bit-vector `int` stored and read back
  ## crosses the boundary twice. Cleared by `resetSymexRunState`.

proc bitSetSV*(raw: Z3AnyAst; elemTy: IRType): SymVal =
  SymVal(kind: svBitSet, bsRaw: raw, bsElemTy: elemTy)

proc bvKindWidth*(k: SVKind): int =
  ## R3 (S2): the fixed width a `svBV*` kind denotes — used by `reconcileInt`
  ## to seed `ziWidth` on a BV operand it converts to `svInt`, so the
  ## converted value stays overflow-checkable at its ORIGINAL static width.
  case k
  of svBV8:  8
  of svBV16: 16
  of svBV32: 32
  of svBV64: 64
  else: raise newException(ValueError, "bvKindWidth: not a BV kind " & $k)  # [raise-audited: category-c: BV-family invariant (bvKindWidth is only called with an already-established BV kind)]

proc toSvIntPreserving*(sv: SymVal): SymVal =
  ## R3 (S2): `reconcileInt`'s per-operand conversion step, width-preserving.
  ## An already-`svInt` operand is returned AS-IS (its own `ziWidth`/
  ## `ziSigned` — possibly 0/unset, possibly a promoted value's real static
  ## type — must survive reconciliation untouched). A BV operand converts via
  ## `toZ3Int` exactly as before, now ALSO stamping `ziWidth`/`ziSigned` from
  ## the BV kind/its own `signed` field, so the converted value remains
  ## overflow-checkable at the width it actually was before the mixed-theory
  ## bridge (e.g. a plain non-promoted `svBV64` operand reconciled against a
  ## promoted `svInt` sibling must not silently lose its own overflow fork).
  if sv.kind == svInt:
    sv
  else:
    let zi = toZ3Int(sv)
    intOfBV[cast[uint](cast[pointer](zi.raw))] = (zi: zi, bv: sv)   # RFC-0005 S8ax
    SymVal(kind: svInt, zi: zi,
           ziWidth: bvKindWidth(sv.kind), ziSigned: sv.signed)

var globalEntryFacts* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8as. The allocation facts of those values (a seq's length is
  ## at least 0, a range's bounds): true of every value of the type, so
  ## asserted into every check (`globalRoots`), as the values are run-wide.

proc sanitizeTypeId*(base: string): string =
  ## The heap/sort-name spelling of a type id: every character outside
  ## `[A-Za-z0-9_]` becomes `_` (split out of `refPointeeTypeId` at RFC-0005
  ## S8bh, whose `fieldHeapKey` spells a declaring type's id the same way).
  result = base
  for i in 0 ..< result.len:
    if result[i] notin {'a'..'z', 'A'..'Z', '0'..'9', '_'}:
      result[i] = '_'

proc refPointeeTypeId*(pointeeTy: IRType): string =
  ## Phase 15 R1; flipped at Cluster H Step B (ADR-0022). A stable
  ## per-pointee-type identifier used to key the `Ref_T` sort + heap array +
  ## nil const (and, via `fieldHeapKey`, the per-field heap arrays — an
  ## object's ref sort and its field-array keys must agree, so the same
  ## preference applies uniformly to `refPointeeTypeId(objTy)` calls too).
  ##
  ## Prefer the pointee's `nominalId` (a canonical, symbol-unique nominal
  ## identity — Cluster H Step A) over the structural `$pointeeTy` rendering
  ## when the pointee is a named object (`itTuple` with a non-empty
  ## `nominalId`). Two `IRType`s for the SAME nominal object can carry
  ## DIFFERENT structural renderings — e.g. a bare ref's full-field pointee
  ## vs. a recursive field's empty-fielded placeholder (`namedRefPlaceholder`,
  ## built to break compile-time self-reference) — yet they denote the same
  ## Nim type and must key the SAME `Ref_T` sort. Keying on `nominalId`
  ## unifies them; keying on `$pointeeTy` (the pre-Step-B behaviour) would
  ## mint two distinct sorts and a Z3 sort mismatch on the first cross-use
  ## (degrading to `sxUnknown`). That unification becomes reachable once a
  ## bare named-ref parameter itself routes through `itRef` (Step C); Step B
  ## proves the mechanism keeps inline-ref sort naming consistent first.
  ## Anonymous tuples and non-object pointees have no `nominalId` and keep
  ## the structural rendering (unchanged behaviour).
  ##
  ## RFC-0005 S8j: a variant pointee keys on its `vNominalId` the same way.
  ## An inline `ref Obj` field's pointee is the empty-fielded placeholder
  ## tuple, keyed on `nominalId(Obj)`; when `Obj` is a case object, every
  ## other position (the nil in `h.v != nil`, the pointee of `h.v.kind`)
  ## carries the full variant. Keyed structurally, the two were distinct
  ## sorts for one Nim type: a Z3 sort error, or a false `sxUnsat`.
  ## RFC-0005 S8l: a multi-variant keys on its `mvNominalId` for the same
  ## reason (an inline `ref MV` field was that sort error).
  ## RFC-0005 S8bh (item 3): a type of an inheritance hierarchy keys on the
  ## hierarchy's ROOT (`inheritChain[0]`): every ref of the hierarchy is an
  ## address of one sort, as in Nim, where `Base(d)` is `d`'s own address.
  let base = if pointeeTy.kind == itTuple and pointeeTy.inheritChain.len > 0:
               pointeeTy.inheritChain[0]
             elif pointeeTy.kind == itVariant and
                  pointeeTy.vInheritChain.len > 0:
               pointeeTy.vInheritChain[0]   # RFC-0005 S8bn (item 8)
             elif pointeeTy.kind == itTuple and pointeeTy.nominalId.len > 0:
               pointeeTy.nominalId
             elif pointeeTy.kind == itVariant and pointeeTy.vNominalId.len > 0:
               pointeeTy.vNominalId
             elif pointeeTy.kind == itMultiVariant and pointeeTy.mvNominalId.len > 0:
               pointeeTy.mvNominalId   # RFC-0005 S8l
             else:
               $pointeeTy
  result = sanitizeTypeId(base)

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
    let nilConst = wrap[Z3AnyAst](ctx, nilRaw)
    currentNilConsts[typeId] = nilConst
    # CR-9 Stage 4: also populate WalkerStatics.refSorts/nilConsts when a walk
    # is active, so the live WalkerStatics is the authoritative source during
    # the walk and the post-walk mirror loop becomes redundant.
    syncRefSortEntry(typeId, sort.raw, nilConst)
  currentRefSorts[typeId]

proc heapStandInTy*(ty: IRType): bool =
  ## RFC-0005 S8ar. A value no cell holds, by a stated, scoped decline: a
  ## by-value case object, a `distinct` over a composite base, and a tuple,
  ## object or array with a part that is not a cell value (`heapCompoundTy`'s
  ## docstring). Every read of such a cell is `liftHeapValue`'s
  ## `heUnsupportedPointeeRead` (a fresh symbol) and every store
  ## `heapCellStore`'s, so the cell's array holds no value of the type and
  ## its sort is a stand-in (`heapValueSort`: Bool). Before S8ar the sort
  ## derivation also recorded `seUnsupportedCompoundSortLeaf` for the same
  ## access, and a store built an ill-sorted term.
  ty != nil and not heapCompoundTy(ty) and
    ty.kind in {itVariant, itMultiVariant, itDistinct, itTuple, itArray}

proc heapWfTy*(ty: IRType): bool =
  ## RFC-0005 S8ap. A heap value whose input cells carry a well-formedness
  ## fact (`heapCellWfConds`): the compound kinds and `string`.
  heapCompoundTy(ty) or (ty != nil and ty.kind == itString)

proc svPartsOf*(sv: SymVal; ty: IRType): seq[SymVal] =
  ## RFC-0005 S8at. The parts of a tree value, in `heapParts` order.
  ## Precondition: `svFitsHeapTy(sv, ty)` (or `sv` a prototype of `ty`).
  case ty.kind
  of itTuple: result = sv.fields
  of itArray: result = sv.arrElems
  of itVariant:
    result.add sv.vDisc[]
    result.add sv.vPlainFields
    for arm in ty.vArms: result.add sv.vArmFields[arm.tagOrdinal]
  of itMultiVariant:
    result.add sv.mvPlainFields
    for xi, ax in ty.mvAxes:
      result.add sv.mvAxes[xi].disc[]
      for arm in ax.arms: result.add sv.mvAxes[xi].armFields[arm.tagOrdinal]
  else: discard

proc svWithParts*(proto: SymVal; ty: IRType; parts: seq[SymVal]): SymVal =
  ## RFC-0005 S8at. `proto` with its parts replaced by `parts`
  ## (`svPartsOf`'s inverse). A discriminator is re-boxed: `vDisc` is a
  ## `ref`, shared with `proto` otherwise.
  result = proto
  var k = 0
  proc next(): SymVal =
    result = parts[k]
    inc k
  case ty.kind
  of itTuple:
    for i in 0 ..< result.fields.len: result.fields[i] = next()
  of itArray:
    for i in 0 ..< result.arrElems.len: result.arrElems[i] = next()
  of itVariant:
    let d = new(SymVal)
    d[] = next()
    result.vDisc = d
    for i in 0 ..< result.vPlainFields.len: result.vPlainFields[i] = next()
    for arm in ty.vArms:
      var fs = newSeq[SymVal](arm.fieldTypes.len)
      for j in 0 ..< fs.len: fs[j] = next()
      result.vArmFields[arm.tagOrdinal] = fs
  of itMultiVariant:
    for i in 0 ..< result.mvPlainFields.len: result.mvPlainFields[i] = next()
    for xi, ax in ty.mvAxes:
      let d = new(SymVal)
      d[] = next()
      result.mvAxes[xi].disc = d
      for arm in ax.arms:
        var fs = newSeq[SymVal](arm.fieldTypes.len)
        for j in 0 ..< fs.len: fs[j] = next()
        result.mvAxes[xi].armFields[arm.tagOrdinal] = fs
  else: discard

proc heapLeafSuffixes*(ty: IRType): seq[string] =
  ## RFC-0005 S8ap. The key suffix of each leaf heap of a value of type `ty`,
  ## in `svLeafAsts` order. `@` cannot begin a Nim identifier, so no field
  ## key collides with a leaf key (and `renderCell`'s field scan skips them:
  ## a suffix holding `__` is never a field).
  ##
  ## RFC-0005 S8ar: a tuple / object / array part `x` holds its leaves under
  ## `__@.x` followed by the part's own suffixes, at every depth -- so no
  ## two paths share a key (`o.inner.x` is `__@.inner__@.x`, `o.x` is
  ## `__@.x`). A `distinct` has its (scalar) base's one leaf.
  if not heapCompoundTy(ty): return @[""]
  case ty.kind
  of itSeq:
    # RFC-0005 S8bc: a tree element's further leaves (`seqDataMore`), one
    # per leaf of the element after its first.
    var r = @["", "__@len"]
    if seqBackedTy(ty) and isTreeSeqElemTy(ty.seqElemTy):
      for i in 1 ..< heapLeafSuffixes(ty.seqElemTy).len: r.add "__@d" & $i
    r
  of itTable:
    # RFC-0005 S8at: a container value's further leaves (`tabDataMore`).
    var r = @["", "__@present", "__@len"]
    if isTableContainerValTy(ty.tabValTy):
      for i in 1 ..< heapLeafSuffixes(ty.tabValTy).len: r.add "__@v" & $i
    r
  of itSet:   @["", "__@len"]
  of itDistinct: heapLeafSuffixes(distinctGround(ty))   ## RFC-0005 S8at
  else:
    var r: seq[string]
    for part in heapParts(ty):
      for sub in heapLeafSuffixes(part.ty):
        r.add "__@." & part.label & sub
    r

proc heapStoreValue*(valSV: SymVal; proto: SymVal; ty: IRType): SymVal

proc heapLeafRaw*(sv: SymVal; ty: IRType): RawZ3Ast =
  ## RFC-0005 S8ar. The term a scalar part `sv` of type `ty` stores: an
  ## `int` part held as a Z3 Int (a promoted value) is the heap's bitvector
  ## of its width (`isDerefWrite`'s own svInt -> BV coercion).
  ##
  ## RFC-0005 batch 3: a signed `int` part of an Int-sorted heap
  ## (`intHeapCell`, S8as; every signed `int` since S8ax) is held as an
  ## Int, the sort `liftHeapValue` reads it back as and `heapValueSort`
  ## gives its leaf heap (from this term), as `heapStoreValue` stores a
  ## scalar cell. Before, S8ar's tree leaves stored the bit-vector while
  ## the read wrapped it as an Int: an ill-sorted term at the first
  ## comparison (`Sorts (_ BitVec 64) and Int are incompatible`).
  if ty.kind == itInt and intHeapCell(ty):
    return heapStoreValue(sv, sv, ty).zi.raw
  if ty.kind == itInt and sv.kind == svInt:
    case ty.width
    of 8:  return intToBv[8](sv.zi, Z3BitVec[8]).raw
    of 16: return intToBv[16](sv.zi, Z3BitVec[16]).raw
    of 32: return intToBv[32](sv.zi, Z3BitVec[32]).raw
    else:  return intToBv[64](sv.zi, Z3BitVec[64]).raw
  rawAnyAstOf(sv)

proc svLeafAsts*(sv: SymVal; ty: IRType = nil): seq[RawZ3Ast] =
  ## RFC-0005 S8ap. The leaf terms of a compound value, in
  ## `heapLeafSuffixes` order. Precondition: `sv.kind` is the compound kind.
  ## RFC-0005 S8ar: a tree value's parts in order (`ty` names the parts'
  ## types; a part that is a scalar stores `heapLeafRaw`). Precondition for
  ## a tree: `svFitsHeapTy(sv, ty)`.
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g): return svLeafAsts(ejectBase(sv), g)  ## RFC-0005 S8at
      return @[heapLeafRaw(ejectBase(sv), g)]
    let parts = heapParts(ty)
    let psvs = svPartsOf(sv, ty)   ## RFC-0005 S8at
    for i, part in parts:
      let psv = psvs[i]
      if heapCompoundTy(part.ty): result.add svLeafAsts(psv, part.ty)
      else: result.add heapLeafRaw(psv, part.ty)
    return
  case sv.kind
  of svSeq:
    # RFC-0005 S8bc: and a tree element's further data arrays.
    var r = @[sv.seqDataRaw.raw, sv.seqLen.raw] # [placeholder-audited]
    for m in sv.seqDataMore: r.add m.raw
    r
  of svTable:
    var r = @[sv.tabDataRaw.raw, sv.tabPresentRaw.raw, sv.tabSize.raw]
    for m in sv.tabDataMore: r.add m.raw   ## RFC-0005 S8at
    r
  of svSet:   @[sv.setMembersRaw.raw, sv.setSize.raw]
  else:       @[rawAnyAstOf(sv)]

proc heapLeafTerm*(sv: SymVal; ty: IRType; pinForm = false): Z3AnyAst =
  ## RFC-0005 S8bc. `heapLeafRaw`, as an owning handle: an `int` part held as
  ## a Z3 Int is converted to the heap's bitvector, a term nothing else
  ## holds, so its raw handle is not valid past the call that made it.
  ##
  ## RFC-0005 batch 4: a signed `int` part (`intHeapCell`, S8ax) is held as
  ## an Int, as `heapLeafRaw` stores it and `svWithLeaves` reads it back
  ## (`liftHeapValue`). S8bc's tree seq data arrays were built from these
  ## terms at the bit-vector sort while every read lifted the select as an
  ## Int: an ill-sorted term at the first comparison, the defect batch 3
  ## fixed in `heapLeafRaw`.
  if pinForm and sv.kind in {svBV8, svBV16, svBV32, svBV64}:
    # RFC-0016 K10b: the value's own bit-vector, not its Int projection
    # (`ubv_to_int` under a sign `ite`): an equality on the projection made
    # every query the second walk's pins joined a mixed-theory one.
    return wrap[Z3AnyAst](requireCurrentContext(), rawAnyAstOf(sv))
  if ty.kind == itInt and intHeapCell(ty):
    return toAnyAst(heapStoreValue(sv, sv, ty).zi)
  if ty.kind == itInt and sv.kind == svInt:
    case ty.width
    of 8:  return toAnyAst(intToBv[8](sv.zi, Z3BitVec[8]))
    of 16: return toAnyAst(intToBv[16](sv.zi, Z3BitVec[16]))
    of 32: return toAnyAst(intToBv[32](sv.zi, Z3BitVec[32]))
    else:  return toAnyAst(intToBv[64](sv.zi, Z3BitVec[64]))
  wrap[Z3AnyAst](requireCurrentContext(), rawAnyAstOf(sv))

proc svLeafTerms*(sv: SymVal; ty: IRType; pinForm = false): seq[Z3AnyAst] =
  ## RFC-0005 S8bc. `svLeafAsts`, as owning handles (`heapLeafTerm`). A seq
  ## element store writes a value's leaves into the seq's data arrays across
  ## several Z3 calls. Precondition for a tree: `svFitsHeapTy(sv, ty)`.
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g): return svLeafTerms(ejectBase(sv), g, pinForm)
      return @[heapLeafTerm(ejectBase(sv), g, pinForm)]
    let psvs = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if heapCompoundTy(part.ty): result.add svLeafTerms(psvs[i], part.ty, pinForm)
      else: result.add heapLeafTerm(psvs[i], part.ty, pinForm)
    return
  # A container's leaves are the value's own fields, alive while `sv` is.
  let ctx = requireCurrentContext()
  for raw in svLeafAsts(sv, ty): result.add wrap[Z3AnyAst](ctx, raw)

proc svFitsHeapTy*(sv: SymVal; ty: IRType): bool =
  ## RFC-0005 S8ar. `sv` has the shape a cell of `ty` stores: a tree value
  ## part by part, a compound value of its kind (not a placeholder seq), a
  ## scalar of its kind (an `int` as a bitvector or a promoted Z3 Int). A
  ## value some upstream degrade produced may not.
  if ty == nil: return false
  case ty.kind
  of itDistinct: svFitsHeapTy(ejectBase(sv), distinctGround(ty))
  of itTuple:
    if sv.kind != svTuple or sv.fields.len != ty.fields.len: return false
    for i, f in ty.fields:
      if not svFitsHeapTy(sv.fields[i], f): return false
    true
  of itArray:
    if sv.kind != svArray or sv.arrElems.len != ty.size: return false
    for e in sv.arrElems:
      if not svFitsHeapTy(e, ty.elemTy): return false
    true
  of itVariant:
    # RFC-0005 S8at. Every arm's slot, of its arity.
    if sv.kind != svVariant or sv.vDisc == nil or
       sv.vPlainFields.len != ty.vPlainFieldTypes.len:
      return false
    for arm in ty.vArms:
      if not sv.vArmFields.hasKey(arm.tagOrdinal) or
         sv.vArmFields[arm.tagOrdinal].len != arm.fieldTypes.len:
        return false
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if not svFitsHeapTy(ps[i], part.ty): return false
    true
  of itMultiVariant:
    if sv.kind != svMultiVariant or sv.mvAxes.len != ty.mvAxes.len or
       sv.mvPlainFields.len != ty.mvPlainFieldTypes.len:
      return false
    for xi, ax in ty.mvAxes:
      if sv.mvAxes[xi].disc == nil: return false
      for arm in ax.arms:
        if not sv.mvAxes[xi].armFields.hasKey(arm.tagOrdinal) or
           sv.mvAxes[xi].armFields[arm.tagOrdinal].len != arm.fieldTypes.len:
          return false
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      if not svFitsHeapTy(ps[i], part.ty): return false
    true
  of itSeq:
    # RFC-0005 S8bc: a placeholder seq type holds a placeholder value, a
    # backed one a backed value with one data array per element leaf.
    if sv.kind != svSeq: return false
    if not seqBackedTy(ty): return sv.isUnsupportedFieldPlaceholder # [placeholder-audited]
    if sv.isUnsupportedFieldPlaceholder: return false # [placeholder-audited]
    let want = if isTreeSeqElemTy(ty.seqElemTy):
                 heapLeafSuffixes(ty.seqElemTy).len else: 1
    1 + sv.seqDataMore.len == want
  of itTable: sv.kind == svTable
  of itSet: sv.kind == svSet
  of itInt:
    case sv.kind
    of svInt: true
    of svBV8: ty.width == 8
    of svBV16: ty.width == 16
    of svBV32: ty.width == 32
    of svBV64: ty.width == 64
    else: false
  of itBool: sv.kind == svBool
  of itFloat32: sv.kind == svFloat32
  of itFloat64: sv.kind == svFloat64
  of itString: sv.kind == svString
  of itRef: sv.kind == svRef
  of itPtr: sv.kind == svPtr
  else: false

proc liftHeapValue*(ctx: Z3Context, valRaw: RawZ3Ast, pointeeTy: IRType): SymVal

proc svWithLeaves*(ctx: Z3Context; proto: SymVal; leaves: seq[Z3AnyAst];
                  ty: IRType = nil): SymVal =
  ## RFC-0005 S8ap. `proto` (a value of the cell's type) with its leaf terms
  ## replaced by `leaves`. The inverse of `svLeafAsts`. The leaves are
  ## OWNING handles: a raw term Z3 has not been asked to keep is only valid
  ## until the next API call, so no caller holds raw leaves across calls.
  ##
  ## RFC-0005 S8ar: a tree value (`ty`) is rebuilt part by part, a scalar
  ## part lifted from its leaf (`liftHeapValue`; a `distinct` is its base
  ## re-boxed, `reboxDistinct`: the distinct constant is opaque, the base is
  ## the value).
  if ty != nil and heapTreeTy(ty):
    if ty.kind == itDistinct:
      let g = distinctGround(ty)
      if heapCompoundTy(g):   ## RFC-0005 S8at: the base's leaves, re-boxed
        return reboxDistinct(ty, svWithLeaves(ctx, ejectBase(proto), leaves, g))
      return liftHeapValue(ctx, leaves[0].raw, ty)
    var pos = 0
    let pprotos = svPartsOf(proto, ty)   ## RFC-0005 S8at
    var rebuilt: seq[SymVal]
    for i, part in heapParts(ty):
      let n = heapLeafSuffixes(part.ty).len
      let sub = leaves[pos ..< pos + n]
      pos += n
      rebuilt.add(
        if heapCompoundTy(part.ty): svWithLeaves(ctx, pprotos[i], sub, part.ty)
        else: liftHeapValue(ctx, sub[0].raw, part.ty))
    return svWithParts(proto, ty, rebuilt)
  result = proto
  case proto.kind
  of svSeq:
    result.seqDataRaw = leaves[0] # [placeholder-audited]
    result.seqLen = wrap[Z3Int](ctx, leaves[1].raw) # [placeholder-audited]
    result.seqDataMore = leaves[2 .. ^1]   ## RFC-0005 S8bc
  of svTable:
    result.tabDataRaw = leaves[0]
    result.tabPresentRaw = leaves[1]
    result.tabSize = wrap[Z3Int](ctx, leaves[2].raw)
    result.tabDataMore = leaves[3 .. ^1]   ## RFC-0005 S8at
  of svSet:
    result.setMembersRaw = leaves[0]
    result.setSize = wrap[Z3Int](ctx, leaves[1].raw)
  else: discard

proc heapValueSort*(ctx: Z3Context, proto: SymVal, pointeeTy: IRType,
                   leaf = 0): RawZ3Sort =
  ## Phase 15 R1. The Z3 value sort of the heap array `Z3Array[Ref_T, T_sym]`
  ## for pointee type `pointeeTy` — i.e. the sort of the SymVal a deref yields.
  ## A throwaway prototype is allocated (its init constraints are discarded —
  ## only the sort is read), mirroring G4's `baseRep` sort probe.
  ## RFC-0005 S8ap: for a compound pointee, the sort of leaf `leaf`
  ## (`heapLeafSuffixes`). The prototype is now the CALLER's
  ## (`mkHeapArrayVar`), which keeps it alive until the array sort is built:
  ## the returned sort is a borrowed handle, and the sort of a table's or a
  ## set's leaf array is referenced by nothing else, so destroying the
  ## prototype here freed it before `Z3_mk_array_sort` read it (Z3: "invalid
  ## array sort definition, parameter is not a sort"). A scalar's sort is
  ## interned and never showed this.
  if intHeapCell(pointeeTy):   # RFC-0005 S8as: Int-sorted `int` heap
    return ctx.checkErr Z3_mk_int_sort(ctx.raw)
  if heapCompoundTy(pointeeTy):
    return ctx.checkErr Z3_get_sort(ctx.raw, svLeafAsts(proto, pointeeTy)[leaf])
  if heapStandInTy(pointeeTy):   ## RFC-0005 S8ar
    return ctx.checkErr Z3_mk_bool_sort(ctx.raw)
  ctx.checkErr Z3_get_sort(ctx.raw, rawAnyAstOf(proto))

proc heapStoreValue*(valSV: SymVal; proto: SymVal; ty: IRType): SymVal =
  ## RFC-0005 S8as. `valSV` in the heap's value sort for pointee/field type
  ## `ty`: an Int for an `intHeapCell` (a BV operand through `bv2int`,
  ## signed), otherwise `proto`'s bit-vector width for an svInt operand
  ## (the `int2bv` coercion every store site carried inline).
  if intHeapCell(ty):
    if valSV.kind in {svBV8, svBV16, svBV32, svBV64}:
      # RFC-0005 S8ax: through `toSvIntPreserving`, which records the
      # conversion (`intOfBV`), so a read meeting the same bit-vector again
      # meets it unconverted.
      var iv = toSvIntPreserving(valSV)
      iv.ziWidth = ty.width
      iv.ziSigned = true
      return iv
    return valSV
  result = valSV
  if valSV.kind == svInt:
    case proto.kind
    of svBV8:  result = liftBV(intToBv[8](valSV.zi, Z3BitVec[8]),  proto.signed)
    of svBV16: result = liftBV(intToBv[16](valSV.zi, Z3BitVec[16]), proto.signed)
    of svBV32: result = liftBV(intToBv[32](valSV.zi, Z3BitVec[32]), proto.signed)
    of svBV64: result = liftBV(intToBv[64](valSV.zi, Z3BitVec[64]), proto.signed)
    else: discard

proc mkHeapArrayVar*(ctx: Z3Context, refSort: RawZ3Sort,
                    pointeeTy: IRType, name: string,
                    variantTy: IRType = nil, leaf = 0): Z3AnyAst =
  ## Phase 15 R1 (ADR-0010). Build a FREE `Z3Array[Ref_T, T_sym]` variable —
  ## the initial heap for one pointee type on one path. The key sort `Ref_T`
  ## is a RUNTIME uninterpreted sort, so the typed `mkArrayVar[K, V]` (which
  ## needs static K/V) cannot express it; we go through raw FFI
  ## (`Z3_mk_array_sort` + `Z3_mk_const`) and erase to `Z3AnyAst`. The result
  ## is a GROUND free array — every `select` on it is decidable (QF_AUFLIA-ish);
  ## NO universal-∀ axiom is ever asserted over the uninterpreted sort (the G4
  ## hang lesson).
  ##
  ## RFC-0005 S8h: records the heap's value type -- and `variantTy`, the
  ## variant object, for a discriminator or branch-field heap -- in
  ## `heapKeyShapes` under the key (`name` less its `heap_` prefix), for
  ## `buildHeapSnapshot`, which renders the witness from the input constant
  ## this builds.
  ##
  ## RFC-0005 S8ap: `leaf` selects one leaf heap of a compound value
  ## (`heapLeafSuffixes`); only leaf 0, whose key is the field's own, records
  ## a shape.
  var key = if name.startsWith("heap_"): name["heap_".len .. ^1] else: name
  # RFC-0005 S8ar: a tree value's leaf 0 is not at the cell's own key
  # (`__@.<part>`); its shape is recorded under the cell's key.
  let suffix0 = heapLeafSuffixes(pointeeTy)[0]
  if leaf == 0 and suffix0.len > 0 and key.endsWith(suffix0):
    key.setLen(key.len - suffix0.len)
  # RFC-0005 S8ax: a havocked heap's constant (`heapInputName`, `@ep<n>`) is
  # not an input heap: the witness renders the input one.
  if leaf == 0 and "@ep" notin key and (not heapKeyShapes.hasKey(key) or
     (variantTy != nil and heapKeyShapes[key].variantTy == nil)):
    heapKeyShapes[key] = HeapKeyShape(valTy: pointeeTy, variantTy: variantTy)
  var scratchPC: seq[Z3Bool]
  let proto = lowerHooks.allocateSym(pointeeTy, "__heapValSort", scratchPC,
                                      false, @[])
  let valSort = heapValueSort(ctx, proto, pointeeTy, leaf)
  let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, refSort, valSort)
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc liftHeapValue*(ctx: Z3Context, valRaw: RawZ3Ast, pointeeTy: IRType): SymVal =
  ## Phase 15 R1. Wrap the raw value-sorted ast produced by a heap `select`
  ## into the SymVal variant for `pointeeTy`, so the dereffed value flows back
  ## into the ordinary `lower`/`symEq`/binop machinery. R1 covers the primitive
  ## pointees the heap-select can yield directly (int/bool/float); composite
  ## pointees (`ref object`, `seq[ref T]`) land R3+.
  case pointeeTy.kind
  of itInt:
    if intHeapCell(pointeeTy):   # RFC-0005 S8as: an Int-sorted `int` heap
      return SymVal(kind: svInt, zi: wrap[Z3Int](ctx, valRaw),
                    ziWidth: pointeeTy.width, ziSigned: true)
    case pointeeTy.width
    of 8:  liftBV(wrap[Z3BitVec[8]](ctx, valRaw),  pointeeTy.signed)
    of 16: liftBV(wrap[Z3BitVec[16]](ctx, valRaw), pointeeTy.signed)
    of 32: liftBV(wrap[Z3BitVec[32]](ctx, valRaw), pointeeTy.signed)
    of 64: liftBV(wrap[Z3BitVec[64]](ctx, valRaw), pointeeTy.signed)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]
        "liftHeapValue: unsupported int width " & $pointeeTy.width)
  of itBool:   ofBool(wrap[Z3Bool](ctx, valRaw))
  of itString:
    # RFC-0005 S8ap. A `string` field is one Z3 string term: its heap was
    # already written (`p.name = "ab"` stored it), and a read is the select
    # itself. Before S8ap the read fell to the `else` arm below and was
    # havocked (`heUnsupportedPointeeRead`). The input cell's byte-range fact
    # is asserted by the read site (`heapCellWfConds`).
    SymVal(kind: svString, str: wrap[Z3String](ctx, valRaw))
  of itFloat32: SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, valRaw))
  of itFloat64: SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, valRaw))
  of itDistinct:
    # RFC-0005 S8ar. A `distinct` cell holds its base's leaves
    # (`heapCompoundTy`), so a scalar base's term is the base value; the
    # distinct constant is opaque and fresh (`reboxDistinct`). Before S8ar a
    # distinct field was havocked (the `else` arm below), as one over a
    # composite base still is (it has no distinct sort to re-box into).
    if heapCompoundTy(pointeeTy):
      reboxDistinct(pointeeTy, liftHeapValue(ctx, valRaw, pointeeTy.distinctBase))
    else:
      degradeAlloc(pointeeTy, heUnsupportedPointeeRead,
        "deref of `ref/ptr " & $pointeeTy & "` (a distinct over a " &
        "composite base) not modeled", "__liftHeapValueUnsupported")
  of itBitSet:   ## RFC-0005 S8bq: a builtin set field is one bit-vector
    bitSetSV(wrap[Z3AnyAst](ctx, valRaw), pointeeTy.bsElemTy)
  of itUninterp:
    # N42 SPOT-PROBE FINDING (temporary — see N42 slice commit for the
    # permanent version of this comment): `itUninterp` had NO arm here,
    # which crashed (uncaught `SymexRefUnresolvedError`) on ANY heap-deref
    # read of a field/pointee whose type degraded to the ownership/
    # unsupported-param/unsupported-witness placeholder family
    # (`allocateSym`'s `itUninterp` arm always allocates that placeholder's
    # VALUE as `svBool` — see its own doc comment — so lifting it back here
    # the same way `itBool` does is the correct, symmetric mirror). This
    # crash was ACCIDENTALLY masking the per-path-taint gap under probe
    # (top-level catch -> sxUnknown either way) — added to make that gap
    # empirically observable.
    ofBool(wrap[Z3Bool](ctx, valRaw))
  of itRef, itPtr:
    # Phase 15 R9 (ADR-0010). A REF-TYPED field (e.g. the recursive `next: Node`
    # of a linked list) — its R6 field-split heap is `Z3Array[Ref_Obj, Ref_T]`,
    # so a `select` yields a `Ref_T`-sorted ast which we lift back into an
    # `svRef`/`svPtr` carrying its pointee. The pointee is the (finite, named)
    # placeholder the field-classifier built (`classifyFieldType`), so a deeper
    # `n.next.next` resolves the ref through the ordinary heap machinery (its
    # `Ref_<name>` sort keys on `refPointeeTypeId(pointee)`). NO heap is read
    # here — the value IS the next address; the deeper deref reads the heap.
    let inner = if pointeeTy.kind == itRef: pointeeTy.refPointeeTy
                else: pointeeTy.ptrPointeeTy
    let valAny = wrap[Z3AnyAst](ctx, valRaw)
    if pointeeTy.kind == itRef:
      SymVal(kind: svRef, refAst: valAny, refPointee: inner)
    else:
      SymVal(kind: svPtr, ptrAst: valAny, ptrFamily: true, ptrPointee: inner)
  else:
    # N46-followup (round-6 re-review, walker v113): was `raise (ref
    # SymexRefUnresolvedError)`, LEDGERED-LIVE. CONFIRMED live by a
    # dedicated probe (a `ref`/`ptr`-to-`string` field deref, the most
    # ordinary shape imaginable): the raise unwinds through
    # `walkHeapArm`/`walk`/`walkBlock` all the way to `runSymexImpl`'s
    # top-level catch, aborting the WHOLE walk. When that catch fires AFTER
    # an unrelated sibling path already reached the target (or BEFORE a
    # later, hazard-free branch gets a chance to), the walk reports
    # `sxUnknown` for a program whose correct verdict is `sxSat` -- the
    # N31/ADR-0023 SND-3 silent-loss class, reproduced RED/GREEN by this
    # slice's own SUT probe (see `tests/tsymex_r6_heap_raise_totality.nim`).
    # In-band degrade instead: `allocDegrade` records the classified
    # kind (`heUnresolvedRef` until S4) and marks the run degraded immediately/globally
    # (Invariant 3), then a FRESH placeholder SymVal of the SAME pointee
    # type keeps the Z3 API call chain type-sound (mirrors `seqElemAt`'s own
    # unsupported-elem-kind idiom, `runtime.nim`) -- its CONTENT is never
    # trustworthy, only its SORT needs to be well-formed. Every
    # `heapSelect`/`liftHeapValue` call site in this file drains the pending
    # degrade into the surviving path's own `uncertain` flag (SND-1)
    # immediately after the select, so a path whose OWN read just degraded
    # can never mint a bogus winning `sxSat`.
    #
    # RFC-0005 S4 (walker v142): this arm is the `allocDegrade` funnel's one
    # FRESH-SYMBOL site, so it records its own kind,
    # `heUnsupportedPointeeRead` (`classOf` = `dcFreshSymbol`: the run keeps
    # `sxUnsat` available, the path is a replay candidate) -- split off
    # `heUnresolvedRef`, whose other sites substitute rather than havoc (see
    # `classOf`'s row for it). That class is licensed ONLY by §2.1's
    # introduction invariant -- the substituted symbol carries NO constraint
    # at introduction -- which the pre-S4 spelling violated:
    # `allocateSym(pointeeTy, "__liftHeapValueUnsupported", ...)` named every
    # occurrence identically, so two reads of two DIFFERENT cells (`a.s`,
    # `b.s`) were the SAME Z3 constant -- an equality reality does not
    # impose, i.e. an under-approximation that proved `a.s != b.s`
    # unreachable (a false `sxUnsat` once the class stopped being ⊤; pinned
    # RED in `tests/tsymex_rfc0005_s4_alloc.nim`). `degradeAlloc` pairs the
    # record with a `freshDegradeName`-uniquified allocation and discards
    # `allocateSym`'s init-side `pcOut` (the byte-faithful char-range /
    # length-ceiling well-formedness facts) -- so each read is a fresh,
    # wholly unconstrained symbol of the pointee's own type.
    #
    # RFC-0005 S8ar: the message states the scope. A by-value case object is
    # not a cell value (`heapCompoundTy`: its fields depend on its
    # discriminator, and the arm-keyed layout a REF case object has does not
    # nest); neither is a tuple or array holding a part that is not one. The
    # pre-S8ar text ("composite pointees land R3+") predated every compound
    # cell.
    let why =
      if pointeeTy.kind in {itVariant, itMultiVariant}:
        "a by-value case object is not a heap cell value: its fields " &
          "depend on its discriminator"
      elif pointeeTy.kind in {itTuple, itArray}:
        "a part of it is not a heap cell value"
      else:
        "not a heap cell value"
    degradeAlloc(pointeeTy, heUnsupportedPointeeRead,
      "deref of `ref/ptr " & $pointeeTy & "` not modeled: " & why &
      " (RFC-0005 S8ar, scoped to this read)",
      "__liftHeapValueUnsupported")

var storeDeclKind* {.threadvar.}: int
  ## RFC-0005 S8ax. The `Z3_decl_kind` ordinal of an array store, read off a
  ## probe term (as `seqCapKinds` does); 0 until first read.

proc storedAt*(ctx: Z3Context; arr, idx: RawZ3Ast): Option[RawZ3Ast] =
  ## RFC-0005 S8ax. The value `arr` holds at `idx` when `arr` is a store at
  ## that same term (`store(h, idx, v)`), or `none`.
  if storeDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let probe = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_store_probe")
    let st = checkedStore(pc, probe.raw, mkInt(pc, 0).raw,
                          mkInt(pc, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, st)))) + 1
  if Z3_get_ast_kind(ctx.raw, arr) != Z3_APP_AST: return none(RawZ3Ast)
  let app = Z3_to_app(ctx.raw, arr)
  if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1 !=
     storeDeclKind or Z3_get_app_num_args(ctx.raw, app) != 3:
    return none(RawZ3Ast)
  if cast[pointer](Z3_get_app_arg(ctx.raw, app, 1)) != cast[pointer](idx):
    return none(RawZ3Ast)
  some(Z3_get_app_arg(ctx.raw, app, 2))

var selectDeclKind* {.threadvar.}: int
  ## RFC-0005 S8bu. The `Z3_decl_kind` ordinal (+ 1) of an array `select`,
  ## read off a probe term as `storeDeclKind` is.

proc peelSelect*(ctx: Z3Context; t: RawZ3Ast): RawZ3Ast =
  ## RFC-0005 S8bu. `t` with each `select(store(a, i, v), i)` (the same
  ## index term) read as `v`: a cell's value read back after it was stored.
  if storeDeclKind == 0:
    discard storedAt(ctx, t, t)   # reads `storeDeclKind`
  if selectDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let probe = mkArrayVar[Z3Int, Z3Int](pc, "__s8bu_select_probe")
    let sel = checkedSelect(pc, probe.raw, mkInt(pc, 0).raw)
    selectDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, sel)))) + 1
  result = t
  for _ in 0 ..< 100_000:
    if Z3_get_ast_kind(ctx.raw, result) != Z3_APP_AST: return
    let app = Z3_to_app(ctx.raw, result)
    if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1 !=
       selectDeclKind or Z3_get_app_num_args(ctx.raw, app) != 2:
      return
    let v = storedAt(ctx, Z3_get_app_arg(ctx.raw, app, 0),
                     Z3_get_app_arg(ctx.raw, app, 1))
    if v.isNone: return
    result = v.get

var constArrayDeclKind* {.threadvar.}: int
  ## RFC-0005 batch 4. The `Z3_decl_kind` ordinal (+ 1) of a constant array
  ## (`(as const ...)`), read off a probe term as `storeDeclKind` is.

proc constFalseStoreKeys*(ctx: Z3Context; arr: RawZ3Ast): Option[seq[RawZ3Ast]] =
  ## RFC-0005 batch 4. The index terms of `arr` when it is a chain of
  ## `store`s over the constant-false array (`store(...store(K false, k1,
  ## v1)..., kn, vn)`, a table's presence array built from the empty table),
  ## or `none`. A term `x` with `select(arr, x)` true is then one of
  ## `k1..kn`: any other reads the base, false. A theorem of the array
  ## theory, so asserting it prunes no model.
  if storeDeclKind == 0:
    discard storedAt(ctx, arr, arr)   # reads `storeDeclKind`
  if constArrayDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let s = pc.checkErr Z3_get_sort(pc.raw, mkInt(pc, 0).raw)
    let probe = pc.checkErr Z3_mk_const_array(pc.raw, s, mkBool(pc, false).raw)
    constArrayDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, probe)))) + 1
  var keys: seq[RawZ3Ast]
  var a = arr
  while true:
    if Z3_get_ast_kind(ctx.raw, a) != Z3_APP_AST: return none(seq[RawZ3Ast])
    let app = Z3_to_app(ctx.raw, a)
    let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1
    if k == storeDeclKind and Z3_get_app_num_args(ctx.raw, app) == 3:
      keys.add Z3_get_app_arg(ctx.raw, app, 1)
      a = Z3_get_app_arg(ctx.raw, app, 0)
    elif k == constArrayDeclKind and Z3_get_app_num_args(ctx.raw, app) == 1:
      if Z3_get_bool_value(ctx.raw, Z3_get_app_arg(ctx.raw, app, 0)) != Z3_L_FALSE:
        return none(seq[RawZ3Ast])
      return some(keys)
    else:
      return none(seq[RawZ3Ast])

var iteDeclKind* {.threadvar.}: int
  ## RFC-0005 S8ax. The `Z3_decl_kind` ordinal of an `ite`, read off a probe
  ## term as `storeDeclKind` is; 0 until first read.

var intCellFactSeen* {.threadvar.}: HashSet[uint]
  ## RFC-0005 S8ax. The `select(base, idx)` terms `intCellRangeFacts` has
  ## bounded this run, by address (each fact holds its term, so the address
  ## is not reused while it is listed). Reset by `resetSymexRunState`.

proc intCellRangeFacts*(ctx: Z3Context; arr, idx: RawZ3Ast; ty: IRType) =
  ## RFC-0005 S8ax. An Int-sorted heap (`intHeapCell`) holds, at every
  ## address, a value of its Nim type, but nothing in the Int sort says so:
  ## an input cell read unchanged was any integer, so `b.n + 1`'s overflow
  ## raise was SAT with `b.n` below `low(int)`, and extracting that model's
  ## witness raised out of the walk, which ended it with nothing recorded (a
  ## false `sxUnsat` on the target the walk never reached). Each heap
  ## constant `arr` reads through -- the input heap, or the fresh one an
  ## opaque call havocs, under any `store` and `ite` the walk built over it
  ## -- gets its type's bounds at `idx` (`globalEntryFacts`): true of every
  ## real heap at every address, so asserting it anywhere prunes no real
  ## execution.
  if storeDeclKind == 0 or iteDeclKind == 0:
    let pc = probeContext()   # RFC-0005 S8bp (batch 7)
    let a = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_chain_probe_a")
    let b = mkArrayVar[Z3Int, Z3Int](pc, "__s8ax_chain_probe_b")
    let st = checkedStore(pc, a.raw, mkInt(pc, 0).raw, mkInt(pc, 0).raw)
    storeDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, st)))) + 1
    let it = checkedIte(pc, mkBoolVar(pc, "__s8ax_chain_probe_c").raw,
                        a.raw, b.raw)
    iteDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, it)))) + 1
  var lo, hi: int64
  if ty.hasRange:
    lo = ty.rangeLo
    hi = ty.rangeHi
  elif ty.width in [8, 16, 32]:
    lo = -(1'i64 shl (ty.width - 1))
    hi = (1'i64 shl (ty.width - 1)) - 1
  else:
    lo = low(int64)
    hi = high(int64)
  var todo = @[arr]
  while todo.len > 0:
    let a = todo.pop()
    if Z3_get_ast_kind(ctx.raw, a) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, a)
    let n = Z3_get_app_num_args(ctx.raw, app)
    if n == 0:
      let sel = checkedSelect(ctx, a, idx)
      let key = cast[uint](cast[pointer](sel))
      if key notin intCellFactSeen:
        intCellFactSeen.incl key
        let v = wrap[Z3Int](ctx, sel)
        globalEntryFacts.add(v >= mkZ3IntLit(lo))
        globalEntryFacts.add(v <= mkZ3IntLit(hi))
      continue
    let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) + 1
    if k == storeDeclKind and n == 3:
      todo.add Z3_get_app_arg(ctx.raw, app, 0)
    elif k == iteDeclKind and n == 3:
      todo.add Z3_get_app_arg(ctx.raw, app, 1)
      todo.add Z3_get_app_arg(ctx.raw, app, 2)

proc heapSelect*(ctx: Z3Context, heap: Z3AnyAst, refAst: Z3AnyAst,
                pointeeTy: IRType): SymVal =
  ## Phase 15 R1 (ADR-0010). The GROUND heap read `select(heap, p)` — a single
  ## `Z3_mk_select` over the free heap array at the abstract address `p`. The
  ## result is the value-sorted ast; lift it into a SymVal. This is the whole
  ## of R1's deref: a decidable array select, NO quantifier (the G4 lesson —
  ## a ∀ over the uninterpreted Ref_T sort would HANG Z3).
  # RFC-0005 S8ax: a read at the address the heap's last store wrote is
  # that store's value, read off the term (`select(store(h, a, v), a)` is
  # `v`), so a value stored and read back is the same term: the bit-vector
  # an Int-sorted heap stored then meets its source unconverted
  # (`intOfBV`).
  let hit = storedAt(ctx, heap.raw, refAst.raw)
  if hit.isNone and intHeapCell(pointeeTy):
    intCellRangeFacts(ctx, heap.raw, refAst.raw, pointeeTy)   # RFC-0005 S8ax
  let valRaw = if hit.isSome: hit.get
               else: checkedSelect(ctx, heap.raw, refAst.raw)
  liftHeapValue(ctx, valRaw, pointeeTy)

type HeapCell* = seq[tuple[key: string; arr: Z3AnyAst]]
  ## RFC-0005 S8ap. The leaf heaps of one cell's value: one entry for a
  ## scalar, one per `heapLeafSuffixes` entry for a compound value.

proc heapCellSelect*(ctx: Z3Context; cell: HeapCell; refAst: Z3AnyAst;
                    valTy: IRType): SymVal =
  ## RFC-0005 S8ap. The value at `refAst`: `heapSelect` for a scalar; for a
  ## compound value, a prototype of `valTy` whose leaves are the selects of
  ## each leaf heap (the prototype's own constants, and its init facts, are
  ## discarded -- only its kind and element types are kept).
  if not heapCompoundTy(valTy):
    return heapSelect(ctx, cell[0].arr, refAst, valTy)
  var scratchPC: seq[Z3Bool]
  let proto = lowerHooks.allocateSym(valTy, "__heapCellProto", scratchPC,
                                      false, @[])
  var leaves: seq[Z3AnyAst]
  for c in cell:
    leaves.add wrap[Z3AnyAst](ctx, checkedSelect(ctx, c.arr.raw, refAst.raw))
  svWithLeaves(ctx, proto, leaves, valTy)

proc svCellWf*(sv: SymVal; ty: IRType; nested: bool; bounded = true): seq[Z3Bool] =
  ## RFC-0005 S8ap (was `heapCellWfConds`' body); S8ar: recursive over a
  ## tree value's parts. The facts a free value of `ty` has (`allocateSym`'s
  ## init facts): a string of bytes, a length or size in `[0, 1024]`, a
  ## table's and a set's size tied to its keys (`ContainerCardRegistry`),
  ## and -- for a NESTED scalar part, which no read site sees -- its declared
  ## range (`rangeCondsIfNeeded`; a cell's own scalar range is the read
  ## site's).
  ##
  ## RFC-0005 S8bc: `bounded = false` drops the `1024` upper bounds, keeping
  ## the rest. A seq ELEMENT's facts are asserted at every read of it, and an
  ## element the body stored may hold a longer seq (`newSeq(n)`), so the
  ## input bound would be a false fact there (a false unsat).
  case sv.kind
  of svString:
    @[matches(sv.str, star(range(mkString("\x00"), mkString("\xff"))))]
  of svSeq:
    if bounded: @[sv.seqLen >= mkInt(0), sv.seqLen <= mkInt(1024)] # [placeholder-audited]
    else: @[sv.seqLen >= mkInt(0)] # [placeholder-audited]
  of svTable:
    registerTableBase(sv.tabPresentRaw, sv.tabSize, ty.tabKeyTy)
    registerTabTreeBase(sv)   ## RFC-0005 S8at
    if bounded: @[sv.tabSize >= mkInt(0), sv.tabSize <= mkInt(1024)]
    else: @[sv.tabSize >= mkInt(0)]
  of svSet:
    registerSetBase(sv.setMembersRaw, sv.setSize, ty.setElemTy)
    if bounded:
      @[sv.setSize >= mkInt(0),
        sv.setSize <= mkInt(min(1024'i64, cellDomainSize(ty.setElemTy)))]
    else:
      @[sv.setSize >= mkInt(0), sv.setSize <= mkInt(cellDomainSize(ty.setElemTy))]
  of svTuple:
    var r: seq[Z3Bool]
    for i, f in sv.fields: r.add svCellWf(f, ty.fields[i], true, bounded)
    r
  of svArray:
    var r: seq[Z3Bool]
    for e in sv.arrElems: r.add svCellWf(e, ty.elemTy, true, bounded)
    r
  of svDistinct:
    svCellWf(ejectBase(sv), distinctGround(ty), nested, bounded)
  of svVariant, svMultiVariant:
    # RFC-0005 S8at. Each part's facts, and each discriminator in its
    # legal domain (`allocateSym`'s clause: an `else` arm's ordinals
    # included, its sentinel not).
    var r: seq[Z3Bool]
    if not heapTreeTy(ty) or not svFitsHeapTy(sv, ty): return r
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty): r.add svCellWf(ps[i], part.ty, true, bounded)
    proc domainClause(d: SymVal; ordSet: seq[int]) =
      if ordSet.len == 0: return
      var clause = variantDiscEq(d, int64(ordSet[0]))
      for k in 1 ..< ordSet.len:
        clause = clause or variantDiscEq(d, int64(ordSet[k]))
      r.add clause
    if sv.kind == svVariant:
      domainClause(sv.vDisc[], discriminatorDomain(ty)[2])
    else:
      for xi, ax in ty.mvAxes:
        domainClause(sv.mvAxes[xi].disc[], axisDiscriminatorDomain(ax)[2])
    r
  else:
    if nested: rangeCondsIfNeeded(sv, ty) else: @[]

proc heapCellWfConds*(ctx: Z3Context; key: string; refSort: RawZ3Sort;
                     valTy: IRType; refAst: Z3AnyAst): seq[Z3Bool] =
  ## RFC-0005 S8ap. The well-formedness of the INPUT cell at `refAst` (see
  ## the section comment above): the facts `allocateSym` gives a free value
  ## of `valTy`, stated of `select(heap_<leaf>, refAst)` for every leaf. A
  ## table's and a set's cell is also registered with the
  ## `ContainerCardRegistry`, which ties its size to the keys present at
  ## every check and is what `extractTableEntries`/`extractSetMembers`
  ## render. Empty for any other type (a scalar's range facts are the read
  ## site's `rangeCondsIfNeeded`, unchanged).
  if not heapWfTy(valTy): return @[]
  var input: HeapCell
  for i, suffix in heapLeafSuffixes(valTy):
    input.add (key & suffix,
               mkHeapArrayVar(ctx, refSort, valTy, "heap_" & key & suffix, nil, i))
  let sv = heapCellSelect(ctx, input, refAst, valTy)
  svCellWf(sv, valTy, false)

proc heapCellStore*(ctx: Z3Context; cell: HeapCell; refAst: Z3AnyAst;
                   valSV: SymVal; valTy: IRType): HeapCell =
  ## RFC-0005 S8ap. `cell` with `valSV` stored at `refAst`, leaf by leaf. A
  ## scalar keeps the pre-S8ap single store (`rawAnyAstOf`, whose own decline
  ## is unchanged). A compound value whose kind does not match `valTy` (a
  ## value some upstream degrade produced: a placeholder seq, a `seq[byte]`
  ## held as a string) has no leaves to store: it is recorded as
  ## `seUnsupportedCompoundSortLeaf` through `allocDegrade` (drained onto the
  ## path by the caller, as the scalar store's decline is) and each leaf
  ## stores a fresh term of its sort.
  if heapStandInTy(valTy):
    # RFC-0005 S8ar: a by-value case object, a distinct over a composite
    # base, or an aggregate with a part that is neither, is not a cell value
    # (`heapStandInTy`; a read of it is `liftHeapValue`'s stated decline).
    # The scalar store below built an ill-sorted term for a distinct
    # (`weInternalWalkerFault`) and `seUnsupportedCompoundSortLeaf` for the
    # others. Declined the same way as the read, and the cell holds a fresh
    # term of its sort.
    let what =
      case valTy.kind
      of itDistinct: "a distinct over a composite base"
      of itTuple, itArray: "a part of it is not a heap cell value"
      else: "a by-value case object"
    allocDegrade(heUnsupportedPointeeRead,
      "heap store into a `" & $valTy & "` cell (" & what & ") not modeled")
    let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, cell[0].arr.raw)
    let fresh = freshOfSort(ctx,
      ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort))
    return @[(cell[0].key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, cell[0].arr.raw, refAst.raw, fresh)))]
  if not heapCompoundTy(valTy):
    # RFC-0005 batch 3: an `int` value in its heap's sort (`heapLeafRaw`:
    # an Int for an Int-sorted heap, else the bit-vector of its width), as
    # a tree value's leaves are; S8at's whole store of a ref case object
    # passed a constructor's bit-vector part into an Int-sorted field heap.
    let raw = if valTy != nil: heapLeafRaw(valSV, valTy)
              else: rawAnyAstOf(valSV)
    return @[(cell[0].key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, cell[0].arr.raw, refAst.raw, raw)))]
  # RFC-0005 S8ar: the shape check is recursive (`svFitsHeapTy`), for a
  # tree value's parts.
  let fits = svFitsHeapTy(valSV, valTy)
  var leaves: seq[Z3AnyAst]
  if fits:
    for raw in svLeafAsts(valSV, valTy): leaves.add wrap[Z3AnyAst](ctx, raw)
  else:
    allocDegrade(seUnsupportedCompoundSortLeaf,
      "heap store of a " & plainEnglishSymValKind(valSV.kind) & " into a `" &
      $valTy & "` cell: the value has no leaves of that type " &
      "(seUnsupportedCompoundSortLeaf)")
    for c in cell:
      let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, c.arr.raw)
      leaves.add wrap[Z3AnyAst](ctx, freshOfSort(ctx,
        ctx.checkErr Z3_get_array_sort_range(ctx.raw, arrSort)))
  for i, c in cell:
    result.add (c.key, wrap[Z3AnyAst](ctx,
      checkedStore(ctx, c.arr.raw, refAst.raw, leaves[i].raw)))

proc heapCellIte*(ctx: Z3Context; cond: Z3Bool; t, e: SymVal;
                 ty: IRType): SymVal =
  ## RFC-0005 S8ap. `if cond: t else: e` for two values of a cell of type
  ## `ty`. `iteSV` havocs a seq / Table / HashSet / string merge
  ## (`feUnsupportedOpHavoc`: its operands are not one term); two cells of
  ## one heap type have the same leaf sorts, so the merge is an `ite` per
  ## leaf. Used where a heap read selects among several arms' cells (an arm
  ## field shared by several tags, a discriminator write's carry).
  # a literal condition (a constructed object's own discriminator) picks its
  # arm, so the merge adds no `ite` for the solver to see through
  case Z3_get_bool_value(ctx.raw, cond.raw)
  of Z3_L_TRUE: return t
  of Z3_L_FALSE: return e
  else: discard
  if t.kind == svString and e.kind == svString:
    return SymVal(kind: svString, str: wrap[Z3String](ctx,
      checkedIte(ctx, cond.raw, t.str.raw, e.str.raw)))
  if not heapCompoundTy(ty) or not svFitsHeapTy(t, ty) or not svFitsHeapTy(e, ty):
    return lowerHooks.iteSV(cond, t, e)
  let tl = svLeafAsts(t, ty)
  let el = svLeafAsts(e, ty)
  var leaves: seq[Z3AnyAst]
  for i in 0 ..< tl.len:
    leaves.add wrap[Z3AnyAst](ctx, checkedIte(ctx, cond.raw, tl[i], el[i]))
  svWithLeaves(ctx, t, leaves, ty)

proc fieldHeapKey*(objTy: IRType, field: string): string =
  ## Phase 15 R6 (ADR-0010). The field-split heap key for `(objTy, field)`. An
  ## object pointee cannot be a single Z3 array VALUE sort (there is no Z3 tuple
  ## sort — C0-ADR), so each field gets its OWN heap array `Z3Array[Ref_T,
  ## <fieldSort>]`, keyed by the object's `refPointeeTypeId` + the field NAME
  ## (unique across the flat inheritance layout — Nim forbids field shadowing).
  ## The `Ref_T` SORT still keys on the OBJECT (`refPointeeTypeId(objTy)`), so
  ## every field of one ref shares a single abstract address (aliasing observed).
  ##
  ## RFC-0005 S8bh (item 3): a field of an inheritance hierarchy keys on the
  ## type that DECLARES it (`ownedFieldIds`), not on the static type it is
  ## read through: `d.x` (static `Derived`) and `b.x` (static `Base`) are one
  ## heap, and siblings' same-named fields are two. A field the type does
  ## not list (a tag level, `@lvl<j>`, or a type without `of`) keeps the
  ## `refPointeeTypeId` key -- the hierarchy's root for a tag level.
  if objTy != nil and objTy.kind == itTuple:
    let i = objTy.ownedFieldNames.find(field)
    if i >= 0 and i < objTy.ownedFieldIds.len:
      return sanitizeTypeId(objTy.ownedFieldIds[i]) & "__" & field
  # RFC-0005 S8bn (item 8): a case-object hierarchy's plain field likewise.
  if objTy != nil and objTy.kind == itVariant:
    let i = objTy.vOwnedFieldNames.find(field)
    if i >= 0 and i < objTy.vOwnedFieldIds.len:
      return sanitizeTypeId(objTy.vOwnedFieldIds[i]) & "__" & field
  refPointeeTypeId(objTy) & "__" & field

proc inheritTagKey*(objTy: IRType, level: int): string =
  ## RFC-0005 S8bh (item 3). The run-type tag heap of depth `level` of
  ## `objTy`'s hierarchy: `<root>__@lvl<level>`. An object of a type of depth
  ## `m` (its `inheritChain.len - 1`) stores `inheritTagCode` of its
  ## ancestor at each depth `1..m` and the sentinel 0 at depth `m + 1`
  ## (`isNew`). A down-conversion to a type `D` of depth `k` from a static
  ## type of depth `s` reads depths `s + 1 .. k` and compares them with `D`'s
  ## chain: depths `<= s` agree by static typing, and an object of depth
  ## `m < k` fails at depth `m + 1` (the sentinel), with no closed-world list
  ## of the hierarchy's types. A parameter's levels are free: its dynamic
  ## type is any subtype of its static one.
  fieldHeapKey(objTy, "@lvl" & $level)

proc variantDiscHeapKey*(objTy: IRType): string =
  ## ADR-0013 D1. The discriminator heap of a ref-to-variant: `<id>__@disc`.
  ## RFC-0005 S8l: an axis view of a multi-variant (`mvAxisView`) keys its
  ## discriminator by name, `<id>__@disc__<discName>` -- one heap per axis.
  ## Its arm and plain field heaps need no such suffix: Nim forbids two
  ## fields of one object sharing a name, so `__@<ord>__<field>` and
  ## `__<field>` are already unique across axes.
  result = refPointeeTypeId(objTy) & "__@disc"
  if objTy.vIsAxisView: result.add "__" & objTy.vDiscName

proc mvAxisView*(mv: IRType; axisIx: int): IRType =
  ## RFC-0005 S8l. Axis `axisIx` of the multi-variant `mv`, as the
  ## single-axis variant the ADR-0013 heap arms already model: the axis's
  ## discriminator and arms, the object's plain fields, and `mv`'s own
  ## `Ref_<id>` (`vNominalId` is `refPointeeTypeId(mv)`, which that proc
  ## returns unchanged). The axes of one object are independent in Nim --
  ## each field, discriminator included, lives at its own slot -- so the
  ## object's heap is exactly the union of its axis views' heaps.
  let ax = mv.mvAxes[axisIx]
  result = tVariant(objectName = mv.mvObjectName, discName = ax.discName,
                    discTy = ax.discTy, arms = ax.arms,
                    plainFieldNames = mv.mvPlainFieldNames,
                    plainFieldTypes = mv.mvPlainFieldTypes,
                    discTags = ax.discTags,
                    nominalId = refPointeeTypeId(mv))
  result.vIsAxisView = true

proc mvAxisOfField*(mv: IRType; field: string): int =
  ## RFC-0005 S8l. The axis whose discriminator or arm declares `field`;
  ## 0 for a plain field (every view carries the plain fields).
  for i, ax in mv.mvAxes:
    if ax.discName == field: return i
    for arm in ax.arms:
      if field in arm.fieldNames: return i
  0

var heapChainKinds* {.threadvar.}: tuple[ready: bool, select, ite: int]
  ## RFC-0005 S8bd. The `Z3_decl_kind` ordinals `heapChainDepth` matches
  ## on, read off terms built once per thread (`seqCapKinds`' discipline).

proc heapChainDepth*(ctx: Z3Context; refAst: Z3AnyAst): int =
  ## RFC-0005 S8bd. How many heap dereferences the ref `refAst` itself was
  ## reached through: 0 for a root (a parameter, a global, a fresh `new`,
  ## a local bound to one), and for a ref read out of a heap cell
  ## (`select(H, r)`, `H` keyed by a `Ref_T` sort) one more than `r`'s.
  ## A merge (`ite`) is its deeper side; a read out of a seq's or array's
  ## backing (`select` at an Int index) is its container's depth. Every
  ## other term is a root.
  if not heapChainKinds.ready:
    let ctx = probeContext()   # RFC-0005 S8bp
    let b = mkBoolVar(ctx, "__s8bd_kind_probe_b")
    let x = mkIntVar(ctx, "__s8bd_kind_probe_x")
    let arr = mkArrayVar[Z3Int, Z3Int](ctx, "__s8bd_kind_probe_arr")
    proc kindOf(a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
    heapChainKinds = (ready: true, select: kindOf(select(arr, x).raw),
                      ite: kindOf(ite(b, x, x + mkInt(ctx, 1)).raw))
  let kinds = heapChainKinds
  var memo: Table[int, int]
  proc go(a: Z3AnyAst; level = 0): int =
    # RFC-0005 S8ct: past the limit, a chain as deep as the limit, which the
    # caller's dereference budget declines.
    if level > termWalkMaxDepth: return termWalkMaxDepth
    if getAstKind(a) != akApp: return 0
    let id = astId(ctx, a.raw)
    if id in memo: return memo[id]
    let (decl, args) = unpackApp(a)
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    var d = 0
    if k == kinds.select and args.len == 2:
      let dom = arrayKey(ctx, ctx.checkErr Z3_get_sort(ctx.raw, args[0].raw))
      d = if getSortKind(ctx, dom) == skUninterpreted: 1 + go(args[1], level + 1)
          else: go(args[0], level + 1)
    elif k == kinds.ite and args.len == 3:
      d = max(go(args[1], level + 1), go(args[2], level + 1))
    memo[id] = d
    d
  go(refAst)

const heapDerefsPerPathCap* = 4096
  ## RFC-0005 S8bd. The hard cap on the dereferences one path makes in all
  ## (`Path.heapDepth` counts them), whatever their depth. The walk of a
  ## path is finite without it (`maxLoopUnwind` and `maxCallDepth` bound
  ## every loop and recursion); it bounds the heap terms one query can hold.

func heapDerefDecline*(chainDepth, derefCount, limit: int): string =
  ## RFC-0005 S8bd. The decline a dereference makes, or "" when it is within
  ## budget. `chainDepth` is the dereference's own depth (one more than its
  ## ref's, `heapChainDepth`), `derefCount` the path's count including it,
  ## `limit` the effective `maxHeapDepth` (`effectiveHeapDepthLimit`).
  ## The budget bounds the depth of a chain (`n.next.next...`), as its name
  ## and its doc say. Before S8bd it was compared with the path's count of
  ## every dereference, so a straight-line SUT that touched one object's
  ## fields nine times declined under the default of 8 (`o.inner.x`, read
  ## and written through a call: S8ba's `hn`, `hr`).
  if limit > 0 and chainDepth >= limit:
    "heap depth budget of " & $limit & " exceeded (maxHeapDepth): a " &
      "dereference " & $chainDepth & " heap reads from its root"
  elif derefCount > heapDerefsPerPathCap:
    "heap dereference hard cap of " & $heapDerefsPerPathCap & " on one " &
      "path exceeded (heapDerefsPerPathCap)"
  else: ""


# ---- the per-run reset ------------------------------------------------------

proc resetHeapModel*() =
  ## RFC-0016 review D3c-6. The per-run reset of the run-state threadvars of
  ## this module, called by `resetSymexRunState`. `storeDeclKind`,
  ## `selectDeclKind`, `constArrayDeclKind`, `iteDeclKind` and `heapChainKinds`
  ## are the linked Z3's decl kinds, the same in every run and read in a probe
  ## context, so they are process-stable and not reset (`probeContext`).
  allocEnumZeroLegal = false
  distinctBijectivityHints = @[]
  distinctSortNames = @[]
  containerCard = ContainerCardRegistry()
  globalEntryFacts = @[]
  currentBorrowReboxCounter = 0
  heapKeyShapes = initTable[string, HeapKeyShape]()
  intHeapIsInt = false
  intOfBV = initTable[uint, tuple[zi: Z3Int, bv: SymVal]]()
  intCellFactSeen = initHashSet[uint]()
