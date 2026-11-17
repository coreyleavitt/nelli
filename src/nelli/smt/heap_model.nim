## RFC-0016 review D3c-6, R2-4: the heap model, a real leaf module: the heap
## algebra, the `iteSV` merge, and the type-directed allocator
## (`allocateSym`/`seqElemAt`), which are mutually recursive.
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
## module directly. The type-directed allocator (`allocateSym`, `seqElemAt`
## and their closure: `defaultZero`, the variant image, the table zero
## builders) and `iteSV` live here too (RFC-0016 review R2-4). That is one file
## of about 4,100 lines on purpose: `allocateSym` and the heap model call each
## other (it calls `allocRefSort` and `inheritTagKey`; the model calls it for
## pointee, distinct-base and cell prototypes), and Nim modules cannot be
## mutually recursive, so no acyclic split of the two exists. Nothing here
## names `WalkCtx`; `checkedSelect` and the rest of the hot path are direct.
##
## Imports: std, `z3`, `./types`, `./abstraction`, `./symval`, `./walk_state`,
## `./z3check`, `./variant_layout` only.
import std/tables
import std/options
import std/sets
import std/strutils
import z3
import ./types
import ./abstraction
import ./symval
import ./walk_state
import ./z3check
import ./variant_layout as vl

# Forward declarations: the container registry (below, with the runtime half
# of this file) reads the leaf split, whose bodies follow the cell model.
proc svLeafAsts*(sv: SymVal; ty: IRType = nil): seq[RawZ3Ast]

proc allocateSym*(ty: IRType, baseName: string, pcOut: var seq[Z3Bool],
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

proc iteSV*(cond: Z3Bool, t, e: SymVal): SymVal
  ## Defined at the end of this module (RFC-0016 review R2-4).

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
    let baseRep = allocateSym(ty.distinctBase, name & ".__baseSort", scratchPC,
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
  allocateSym(ty, freshDegradeName(tag), fresh, false, @[])

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
  let proto = allocateSym(pointeeTy, "__heapValSort", scratchPC,
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
  let proto = allocateSym(valTy, "__heapCellProto", scratchPC,
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
    return iteSV(cond, t, e)
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

# ---- the value merge (RFC-0016 review R2-4) ---------------------------------
# `iteSV` and what it rests on moved down from `runtime.nim`: it needs the
# int-width bridge above (`toSvIntPreserving`, `intOfBV`) and no walker state,
# and this module's own cell store calls it, so it lives here instead of
# behind `lowerHooks` (a `heap_model -> runtime` back-edge).

proc tyOf*(sv: SymVal): IRType =
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
  of svBitSet: tBitSet(sv.bsElemTy)   ## RFC-0005 S8bq
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
    #
    # Round-6 re-review (item 2, walker v115): the plain (shared,
    # always-present) fields ARE fully carried on the SymVal
    # (`vPlainFields`/`vPlainFieldNames`) and must be threaded through to
    # `tVariant` here. Previously they were dropped, so `allocateSym`'s
    # `itVariant` arm built a degrade-placeholder with an EMPTY
    # `vPlainFieldNames` -- a later plain-field read (`iekField`) couldn't
    # find the field on the placeholder and fell through to the "parser
    # should have A-normalised this" `raise`, a real crash-shaped defect
    # (caught at top level as a classified `sxUnknown`, but blaming a
    # nonexistent parser bug instead of naming the actual iteSV merge
    # degrade). Per-arm `tagName` and the disc's full `vDiscTags` domain
    # genuinely are NOT recoverable from the live SymVal (no `vArmTags`/
    # `discTags` storage on `SymVal` at all) -- but that gap is inert for
    # `allocateSym`'s own round-trip: its `hasElse` disc-range expansion
    # only fires when a reconstructed arm's `isElse` is true, and this arm
    # never sets `isElse` (default `false`), so the dropped tags are never
    # consulted by the one caller (`allocateSym`) that matters here.
    var arms: seq[VariantArm]
    for tagOrdinal, fields in sv.vArmFields.pairs:
      var tys: seq[IRType]
      for f in fields: tys.add tyOf(f)
      arms.add VariantArm(tagOrdinal: tagOrdinal,
                          tagName: "",  # not preserved on the SymVal
                          fieldNames: sv.vArmFieldNames[tagOrdinal],
                          fieldTypes: tys)
    var plainTys: seq[IRType]
    for pf in sv.vPlainFields: plainTys.add tyOf(pf)
    tVariant(sv.vObjectName, sv.vDiscName, tyOf(sv.vDisc[]), arms,
             plainFieldNames = sv.vPlainFieldNames,
             plainFieldTypes = plainTys)
  of svMultiVariant:
    # Phase 14 cycle A1c. Diagnostics-only: rebuild the IRType from
    # the SymVal's axes. Tag names are not preserved on the SymVal
    # (same gap as svVariant). Round-6 re-review (item 2, walker v115):
    # plain fields ARE preserved (`mvPlainFields`/`mvPlainFieldNames`) and
    # are threaded through below -- see the `svVariant` arm's comment
    # above for the full rationale (same defect, same fix).
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
    var mvPlainTys: seq[IRType]
    for pf in sv.mvPlainFields: mvPlainTys.add tyOf(pf)
    mkMultiVariant(sv.mvObjectName, axes,
                   plainFieldNames = sv.mvPlainFieldNames,
                   plainFieldTypes = mvPlainTys)

# ---- Prototype probe over the IR --------------------------------------------
#
# Each non-trivial subexpression takes its representation (Z3 BV[W] vs
# Z3Int) from a "prototype" SymVal — the first env-resident variable
# its subtree reaches. Literals coerce to match the prototype; arith
# / comparison ops dispatch on the prototype kind.
#
# When no env-resident var is reachable (e.g. `5 + 6`), no prototype
# exists and the caller defaults to BV[64] signed.

proc bvOfInt*(sv: SymVal): Option[SymVal] =
  ## RFC-0005 S8ax. The bit-vector `sv` (an `svInt`) is the conversion of,
  ## if `intOfBV` lists it and its width and signedness agree.
  if sv.kind != svInt: return none(SymVal)
  let k = cast[uint](cast[pointer](sv.zi.raw))
  if k notin intOfBV: return none(SymVal)
  let e = intOfBV[k]
  if cast[pointer](e.zi.raw) != cast[pointer](sv.zi.raw): return none(SymVal)
  let w = case e.bv.kind
          of svBV8: 8
          of svBV16: 16
          of svBV32: 32
          else: 64
  if sv.ziWidth != 0 and (sv.ziWidth != w or
                          sv.ziSigned != e.bv.signed):
    return none(SymVal)
  some(e.bv)

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
  ## R3 (S2): the conversion step now goes through `toSvIntPreserving` —
  ## width-preserving instead of the former bare `SymVal(kind: svInt, zi:
  ## toZ3Int(...))` reconstruction, which silently dropped `ziWidth`/
  ## `ziSigned` on whichever side was ALREADY `svInt` (both sides were
  ## unconditionally rebuilt from scratch, even the one needing no
  ## conversion at all) — see each proc's own doc comment.
  if a.kind != b.kind and
     a.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
     b.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
    # RFC-0005 S8ax: an Int that is the conversion of a bit-vector of the
    # other operand's kind and signedness (`intOfBV`) meets it as that
    # bit-vector, unconverted.
    if a.kind == svInt:
      let bv = bvOfInt(a)
      if bv.isSome and bv.get.kind == b.kind and bv.get.signed == b.signed:
        return (bv.get, b)
    if b.kind == svInt:
      let bv = bvOfInt(b)
      if bv.isSome and bv.get.kind == a.kind and bv.get.signed == a.signed:
        return (a, bv.get)
    (toSvIntPreserving(a), toSvIntPreserving(b))
  else:
    (a, b)  ## same kind (or non-int) — identity

proc bsIte*(cond: Z3Bool; t, e: Z3AnyAst): Z3AnyAst =
  let c = t.ctx
  wrap[Z3AnyAst](c, checkedIte(c, cond.raw, t.raw, e.raw))

proc seqArrs*(sv: SymVal): seq[Z3AnyAst] =
  ## RFC-0005 S8bc. Every data array of a seq, in leaf order: `seqDataRaw`,
  ## then `seqDataMore` (empty for a scalar element).
  result = @[sv.seqDataRaw] # [placeholder-audited]
  for m in sv.seqDataMore: result.add m

proc withSeqArrsOf*(sv: SymVal; arrs: seq[Z3AnyAst]): SymVal =
  ## RFC-0005 S8bc. `sv` with its data arrays replaced (`seqArrs`' order).
  result = sv
  result.seqDataRaw = arrs[0] # [placeholder-audited]
  result.seqDataMore = arrs[1 .. ^1]

proc heapStepsOf*(sv: SymVal): int =
  ## RFC-0005 S8ar. A ref's or ptr's heap steps from a root (`refSteps`);
  ## 0 for any other value.
  case sv.kind
  of svRef: sv.refSteps
  of svPtr: sv.ptrSteps
  else: 0

# ---------------------------------------------------------------------------
# R1 (walker v89) — placeholder read-totality CHOKEPOINT.
#
# Round-6 (v85-v88) introduced `isUnsupportedFieldPlaceholder`: a marked
# `svSeq` whose element type `allocateSym`'s `itSeq` arm could not back with
# a real Z3 array (e.g. `seq[(string,string)]`) — allocated with `seqLen`
# HARD-FORCED `== 0` and an INERT data array nothing may legitimately select
# from (see the `itSeq` arm of `allocateSym` below, where the placeholder is
# built with `isUnsupportedFieldPlaceholder: true`). A verdict-affecting
# READ of such a value (via its real, forced-0 `seqLen`, or its inert
# `seqDataRaw`) must NEVER be trusted — doing so silently proves a verdict
# against the fake length/content instead of honestly declining. R1 found
# this guard hand-placed and incomplete (`isIndex` only) after two Critical
# false-verdict gaps (`iekSeqLen`, `iekSeqSlice`) were confirmed. This pair —
# `placeholderReadDeclineMsg` (message/kind, shared by EVERY call site) and
# `declinePlaceholderInLower` (the in-`lower()` recording half) — is the
# structural chokepoint every svSeq-consuming lowering arm must call FIRST,
# so a future arm added to `lower()` inherits totality by construction
# instead of needing its own hand-rolled check. The `isIndex` walk-time arm
# (runtime.nim: the `w.degrade(placeholderReadDeclineKind(arrSV), ...
# "index read")` site) is the analogous AT-WALK half — it cannot share
# `declinePlaceholderInLower`'s threadvar-sink recording (it has `w`/`Path`
# and must fork `uncertain = true` on the SURVIVING PATH, not merely flag a
# threadvar for `drainPendingLowerEffects` to pick up later), but shares
# `placeholderReadDeclineMsg` so both halves report the identical
# `seNestedSeqUnsupported` kind and message shape — one decline idiom, not
# two parallel ones.
proc placeholderReadDeclineKind*(recv: SymVal): SymexErrorKind =
  ## N47-followup (walker v110). The classified kind a READ decline for
  ## `recv` should carry: `recv.seqUnsupportedFieldKind` when `recv` was
  ## built via `tUnsupportedFieldSeq` (reason non-empty — a declared-field or
  ## OPERATION-level origin), else the legacy `seNestedSeqUnsupported` a
  ## bare-value placeholder (no reason to carry) has always used.
  if recv.seqUnsupportedFieldReason.len > 0: recv.seqUnsupportedFieldKind
  else: seNestedSeqUnsupported

proc placeholderReadDeclineMsg*(recv: SymVal, loc, what: string): string =
  ## Shared message/kind formatter for every placeholder-seq READ decline
  ## (in-`lower()` and at-walk-time alike). `loc`, when non-empty, is
  ## rendered with the SAME `<loc>: ` prefix idiom `isIndex`'s OTHER
  ## (non-seq) receiver-kind decline already uses (~line 6604) — empty when
  ## the call site's `IRExpr`/`IRStmt` carries no site location.
  ##
  ## Round-6 N12 (message-formatting boundary): this string reaches the user
  ## through `SymexResult.errors` — there is no further rendering step in
  ## this codebase (`.msg` IS the user-facing text) — so it must not leak
  ## internal IR vocabulary. Previously interpolated the bare `IRTypeKind`
  ## (`$elemKind`, e.g. "itTuple") and the raw `SymexErrorKind` identifier
  ## ("seNestedSeqUnsupported") verbatim; now routes through
  ## `plainEnglishTypeKind` and a plain-language decline note. `.kind` (the
  ## structured `SymexErrorKind` field a caller can match on) is UNCHANGED —
  ## only the free-form TEXT changes; internal audit/log strings that never
  ## reach a `SymexResult` may keep using `$elemKind` freely.
  ##
  ## N47-followup (walker v110): when `recv.seqUnsupportedFieldReason` is
  ## set, the placeholder did NOT arise from an unbacked element type — it
  ## arose from a DECLARED-FIELD-level or OPERATION-level decline (e.g.
  ## `iekSeqAdd`'s width/elem-support gap) whose `recv.seqElemTy` may be
  ## perfectly backed in general. Claiming "nested seq element type is not
  ## supported" in that case is FALSE and misleads a reader of
  ## `SymexResult.errors` about the actual defect. Reference the ORIGINAL
  ## decline reason instead — this also lets the drain-time message dedup
  ## (`drainDedupedByMsg`, at `loweringDegradeErrors`'s drain) collapse a
  ## cascade of downstream reads on the same tainted receiver into a small,
  ## honestly-worded set instead of manufacturing new misclassified entries.
  let locPrefix = if loc.len > 0: loc & ": " else: ""
  if recv.seqUnsupportedFieldReason.len > 0:
    locPrefix & what & " of a receiver already declined (" &
      recv.seqUnsupportedFieldReason & ")"
  else:
    locPrefix & what & " of an unsupported-element seq of " &
      plainEnglishTypeKind(recv.seqElemTy.kind) &
      " placeholder (nested seq element type is not supported)"

template declinePlaceholderInLower*(recv: SymVal, loc, what: string) =
  ## IN-`lower()` chokepoint half. `lower(env: Env, e: IRExpr, ...)` has no
  ## `w: var WalkCtx` / `Path` — it is called from deep inside expression
  ## recursion — so taint rides the SAME in-band threadvar sink every other
  ## `lower()`-internal degrade in this file uses (`loweringDegradeErrors`/
  ## `loweringDidDegrade`; SND-3, ADR-0023), drained by
  ## `drainPendingLowerEffects` into the calling PATH's `uncertain = true`
  ## (SND-1's per-path taint). Deliberately NEVER a `raise`: unwinding out of
  ## `lower()` here would propagate past the caller's own `seq[Path]` fork
  ## loop to the top-level `runSymexImpl` catch-all and poison the WHOLE run
  ## — exactly Bug #2's original failure mode, which the placeholder
  ## machinery exists to prevent. Callers build their own type-correct inert
  ## result after calling this (an `svInt`/`svSeq`/etc — the one piece that
  ## cannot be centralised, since each arm's result kind differs).
  lowerDegrade(placeholderReadDeclineKind(recv),
    placeholderReadDeclineMsg(recv, loc, what))

proc iteSV*(cond: Z3Bool, t, e: SymVal): SymVal =
  ## Z3-level if-then-else over SymVals. Both branches must share kind.
  if (t.kind == svDistinct) != (e.kind == svDistinct):
    # RFC-0005 S8ad: one side a boxed `distinct` value, the other its bare
    # base. `D(x)` is the parser's identity (S8p) while a borrowed
    # arithmetic result is re-boxed (`reboxDistinct`), so the two meet
    # wherever a local distinct value is merged: the element fold of
    # `var a = [Meters(1), Meters(2)]; a[0] = a[0] + Meters(2)` read at a
    # symbolic index. The base is the whole observable value (every read
    # ejects, `retBindEq` binds through it), so the merge is of the bases.
    # Before S8ad the assertion below faulted the walker.
    return iteSV(cond, ejectBase(t), ejectBase(e))
  if t.kind != e.kind and t.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
     e.kind in {svInt, svBV8, svBV16, svBV32, svBV64}:
    # RFC-0005 S8aj: one side an Int (`svInt`, which carries its Nim width),
    # the other a bitvector. They meet when an array element is an Int on
    # one path and a bitvector on the other: a loop writing
    # `a[0] = a[0] + x` and `a[2] = a[2] + k` under `symexAssume` on `x`
    # (`var a: array[3, int]` and `var a = [0, 0, 0]` alike; it faulted at
    # the base too). Both are the same Nim integer, so the merge is of
    # their Int values (`reconcileInt`, as every mixed operator does); the
    # assertion below faulted the walker.
    let (rt, re) = reconcileInt(t, e)
    return iteSV(cond, rt, re)
  doAssert t.kind == e.kind, "iteSV: kind mismatch " &
    $t.kind & " vs " & $e.kind
  case t.kind
  of svUninterpRef:
    # N46 (round-6 re-review, ADR-0023/SND-3 class widening): was a raw
    # `raise newException` -- reachable walk-time via the symbolic
    # array-index ite-fold (`isIndex`/`iekIndex` build `iteSV` over every
    # element of an `array[N, T]`; `allocateSym`'s `itArray` arm recurses
    # for ANY element type, so `array[N, SomeUninterpElem]` allocates fine
    # and a non-constant-indexed read reaches here unguarded). In-band
    # degrade instead: one operand is a sound stand-in (both `t`/`e` share
    # `t.kind` by the entry `doAssert`), matching `retBindEq`'s own
    # placeholder-return idiom for an unmodeled composite merge.
    # RFC-0005 S6b: `feUnsupportedOpHavoc` -- the result (below) is a
    # uniquified fresh const of the operands' own sort.
    allocDegrade(feUnsupportedOpHavoc,
      "iteSV: svUninterpRef merge lands with cluster E")
    # Round-6 re-review (item 1, walker v114): was `t` -- a pretend merge
    # that forwarded ONE OPERAND'S CONCRETE VALUE unconditionally, ignoring
    # both `cond` and the accumulator `e`. See the `svString`/`svTable`/…
    # group arm below for the full verification writeup (the index-ite-fold
    # collapse hazard and why per-path taint alone is not enough). Return a
    # FRESH, unconstrained const of `t`'s OWN uninterpreted sort — mirrors
    # `reboxDistinct`/`allocDistinctSym`'s `rawConstOf`-on-an-existing-sort
    # idiom (item 4, walker v115 correction: NOT the `svRef`/`svPtr` arm
    # below, which does a genuine `Z3_mk_ite` value merge over two already-
    # built addresses — a different operation entirely; the real precedent
    # for "raw fresh same-sort const, not routed through `allocateSym`" is
    # `reboxDistinct`, ~line 2808, and `allocDistinctSym`, ~line 1826):
    # `allocateSym`'s `itUninterp` arm only recognises the three synthetic
    # `__ownership:`/`__unsupported:`/`__unsupported_witness:` name prefixes
    # and hard-raises (a genuine walker-invariant Defect) for an ordinary
    # cluster-E sort name like this one, so `allocateSym(tyOf(t), …)` is NOT
    # a safe route here the way it is for the group arm below.
    let ctx = t.uninterpAst.ctx
    let srt = ctx.checkErr Z3_get_sort(ctx.raw, t.uninterpAst.raw)
    # Item 3 (walker v115): uniquify the fresh const name -- Z3 interns
    # consts by (name, sort), so a fixed name would let two DIFFERENT
    # `svUninterpRef` merges in the same run (e.g. two distinct
    # `array[N, SomeUninterpElem]` locals both index-merged) silently share
    # one Z3 symbol. Mirrors `reboxDistinct`'s `currentBorrowReboxCounter`
    # idiom / `runtime_exceptions.nim`'s `currentExnRefCounter`. Item 1
    # (consolidated): routed through the shared `freshDegradeName`.
    let freshAst = wrap[Z3AnyAst](ctx, rawConstOf(ctx, srt,
      freshDegradeName("__iteSVUninterpDegrade")))
    SymVal(kind: svUninterpRef, uninterpAst: freshAst,
           sortName: t.sortName, typeTag: t.typeTag)
  of svFloat32:   ## Phase 15 F9a: IEEE float path-merge over Z3 FP `ite`.
    SymVal(kind: svFloat32, fp32: ite(cond, t.fp32, e.fp32))
  of svFloat64:
    SymVal(kind: svFloat64, fp64: ite(cond, t.fp64, e.fp64))
  of svBool: ofBool(ite(cond, t.bo, e.bo))
  of svBitSet:   ## RFC-0005 S8bq: `ite` of the two bit-vectors
    bitSetSV(bsIte(cond, t.bsRaw, e.bsRaw), t.bsElemTy)
  of svInt:
    ## R3 (S2): propagate width metadata through the merge when both
    ## branches agree (the expected case — a single ternary/if-expression
    ## has one static Nim type, so both arms should carry the same
    ## `ziWidth`/`ziSigned`); a mismatch conservatively drops to "unknown"
    ## (0) rather than guessing, same "skip" `overflowCondInt` already
    ## applies to any unrecognized-width svInt.
    let (rw, rs) = if t.ziWidth == e.ziWidth and t.ziSigned == e.ziSigned:
                      (t.ziWidth, t.ziSigned)
                    else: (0, false)
    SymVal(kind: svInt, zi: ite(cond, t.zi, e.zi), ziWidth: rw, ziSigned: rs)
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
    let merged = checkedIte(ctx, args[0], args[1], args[2])
    let boxed = new(SymVal)
    boxed[] = iteSV(cond, t.distinctBaseSym[], e.distinctBaseSym[])
    SymVal(kind: svDistinct, distinctAst: wrap[Z3AnyAst](ctx, merged),
           distinctName: t.distinctName, distinctBaseSym: boxed)
  of svSeq:
    if t.isUnsupportedFieldPlaceholder or e.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # Round-6 re-review (walker v112): guard-before, routed through the
      # SAME R1 chokepoint `eqBV`/`neBV`/`cmpBV`/`svLeafEq` now use, rather
      # than the generic catch-all below. Item 4 (round-6 re-review):
      # previously hand-inlined `declinePlaceholderInLower`'s two-line body
      # directly (this proc used to sit ABOVE the R1 chokepoint, behind a
      # two-proc forward declaration, because a `template` cannot be
      # forward-declared the way `placeholderReadDeclineKind`/
      # `placeholderReadDeclineMsg` were) — relocated below the chokepoint
      # (pure code motion; nothing between the old and new position calls
      # `iteSV`, so no caller needed a forward declaration either) so this
      # arm can call the template directly, same as `cmpBV`/`eqBV`/`neBV`/
      # `svLeafEq`. Returning `t` here is fine: `t` is itself an INERT
      # placeholder (forced `seqLen == 0`, never selected from — see
      # `allocateSym`'s `itSeq` arm), so no concrete value collapses onto a
      # comparison target the way the genuine-merge branch below could.
      declinePlaceholderInLower(t, "", "array-index merge of")
      t
    else:
      # Round-6 re-review (item 1, walker v115): was `allocDegrade(...); t`
      # -- shared fallthrough with the placeholder branch above, so a GENUINE
      # (non-placeholder) seq element merge still forwarded ONE OPERAND'S
      # CONCRETE VALUE unconditionally, the exact class the `svString`/
      # `svTable`/`svSet`/`svVariant`/`svMultiVariant` group arm below and
      # the `svUninterpRef` arm above were fixed for at walker v114 — this
      # arm's own v114 docstring (removed above) claimed the whole `svSeq`
      # case was closed, but only the placeholder half was.
      #
      # Fix: same fresh-placeholder idiom as the group arm below --
      # `allocateSym(tyOf(t), …)`. `tyOf` is FAITHFUL for `svSeq`: unlike
      # `svVariant`/`svMultiVariant` (which reconstruct field types by
      # recursing through live element SymVals, dropping tag names —
      # diagnostics-only, see item 2), `tyOf`'s `svSeq` arm returns
      # `tSeq(sv.seqElemTy)` from the STORED `seqElemTy` field directly, a
      # lossless round-trip of the type this value was allocated at.
      # `allocateSym`'s own `itSeq` arm already self-guards an elemTy it
      # cannot back (`not isBackedSeqElemTy(ty.seqElemTy)`) by degrading TO
      # an inert `isUnsupportedFieldPlaceholder` result instead of raising
      # (the branch above this `if`), so `allocateSym(tyOf(t), …)` can never
      # raise here regardless of what `seqElemTy` holds.
      # RFC-0005 S6b: `feUnsupportedOpHavoc` -- a lossless `tyOf`, a fresh
      # per-merge name, init facts discarded, both operands already built.
      # RFC-0005 S8at: two seqs whose element arrays share a sort (the
      # same backed element type) merge exactly: an `ite` of the element
      # arrays and of the lengths. A symbolic index into an array of seqs
      # (`a[i].len`, `p.a[i][1]`) is this merge folded over the elements;
      # it was the havoc below for every such read.
      # RFC-0005 S8bc: every data array of a tree element, each an `ite`;
      # the arrays must agree in number and sort.
      let ctx = t.seqDataRaw.ctx # [placeholder-audited]
      let ta = seqArrs(t)
      let ea = seqArrs(e)
      var sameSorts = ta.len == ea.len
      if sameSorts:
        for i in 0 ..< ta.len:
          # hash-consed: identity is equality (`sortFault`)
          if ctx.checkErr(Z3_get_sort(ctx.raw, ta[i].raw)) !=
             ctx.checkErr(Z3_get_sort(ctx.raw, ea[i].raw)):
            sameSorts = false
      if sameSorts:
        var arrs: seq[Z3AnyAst]
        for i in 0 ..< ta.len:
          arrs.add wrap[Z3AnyAst](ctx, checkedIte(ctx, cond.raw,
            ta[i].raw, ea[i].raw))
        var r = withSeqArrsOf(t, arrs)
        r.seqLen = ite(cond, t.seqLen, e.seqLen) # [placeholder-audited]
        r.seqSteps = max(t.seqSteps, e.seqSteps)
        return r
      degradeAlloc(tyOf(t), feUnsupportedOpHavoc,
        "iteSV: not supported for seq value (Phase 5+)", "__iteSVMergeDegrade")
  of svString:
    # RFC-0005 S8bb: a string merge is Z3's `ite` over the two strings --
    # exact, as for every scalar sort above. It was the fresh-symbol havoc
    # of the group arm below, so reading an `array[N, string]` element
    # (the index fold merges every element, a literal index too) was never
    # decided: the captures overloads' `matches` arrays are such arrays.
    SymVal(kind: svString, str: ite(cond, t.str, e.str))
  of svTable, svSet, svVariant, svMultiVariant:
    # N46: same walk-reachable array-index-merge hazard as the
    # `svUninterpRef` arm above -- see its comment. `svSeq` is peeled off
    # above (walker v112) into its own placeholder-aware arm.
    #
    # Round-6 re-review (item 1, walker v114) -- VERIFIED finding, fixed
    # regardless of outcome per the review brief. This arm used to be
    # `allocDegrade(...); t` -- returning ONE OPERAND'S CONCRETE VALUE
    # unconditionally, ignoring both `cond` and the accumulator `e`. Every
    # caller's index-ite-fold is a LEFT FOLD (`res = arrElems[0]; for k in
    # 1..<n: res = iteSV(cond_k, arrElems[k], res)`, runtime.nim's `iekIndex`
    # ~4847 and the walk-level `isIndex` ~7944; `isVariantField`'s
    # arm-fold ~8375 is the same shape over variant arms) that ALWAYS
    # returns `t` at every step, so the fold's final value is the LAST
    # operand touched -- structurally independent of `cond` (the symbolic
    # index / active variant tag), a silent wrong-value substitution.
    #
    # Verification (adversarial, container-run probes over
    # `array[3, string]` with a symbolic index and a target reachable only
    # when the selected element equals the collapsed-to element): the
    # expression-level `iekIndex` arm (~4847) is DEAD CODE -- `mkIndex`
    # (the only constructor for an `iekIndex` IRExpr) has zero callers
    # anywhere in the parser; `nnkBracketExpr` on an `itArray` receiver
    # ALWAYS A-normalises to the `isIndex` STATEMENT via `mkIndexStmt`
    # (dsl_parser.nim, `of itArray:`), so no real SUT can ever reach
    # `iekIndex`'s `lower()` arm. The one LIVE route, the walk-level
    # `isIndex` fold (~7944), calls this arm DIRECTLY -- with no
    # intervening `lower()`/`lowerBoolInExpr` wrapper -- so the
    # `loweringDidDegrade` taint `allocDegrade` deposits is NOT drained onto
    # the surviving path's `uncertain` flag until whatever `lower()`/
    # `lowerBoolInExpr` call happens to run NEXT on that SAME path. Every
    # constructed probe (single-path; two sibling paths merged before a
    # shared `isIndex`+comparison; both orderings of which sibling carries
    # the vulnerable array) reached `isTargetLabel` with `uncertain == true`
    # and a correctly-classified `sxUnknown` -- Nim's own generated control
    # flow always threads a subsequent boolean check through the identical
    # path before a value-dependent target, and `isIf`'s body-walk
    # (`walk(br.body, @[armPath], w)`, one path at a time) means the walker
    # never actually batches multiple live siblings through a shared
    # `isIndex`+consumer pair in practice. So today: ROUTE (a), sound but
    # via a coincidence of caller shape, not by construction -- the taint
    # was racing a "does something else drain the leak before the tainted
    # path resolves its target" bet that nothing currently in this codebase
    # loses, but nothing GUARANTEES either (a future batched-multi-path
    # caller, e.g. a closure/HOF fold merging several call-return paths,
    # could lose that race and let a collapsed value size a verdict).
    #
    # Fix: stop relying on the race. Return a genuinely FRESH, unconstrained
    # placeholder of the operand's OWN kind (the `eqBV`/`neBV` idiom above --
    # `allocateSym` on the operand's reconstructed type via `tyOf`, which
    # round-trips cleanly through `allocateSym` for every kind in this
    # group: `tString()`/`tTable()`/`tSet()`/`tVariant()`/`tMultiVariant()`
    # all have direct, non-raising `allocateSym` arms). A fresh placeholder
    # can never accidentally equal a real comparison target the way the
    # collapsed CONCRETE value could, so soundness no longer depends on the
    # taint being drained before the target resolves -- only on
    # Invariant 3's ordinary sawUnknown backstop (still fired immediately,
    # synchronously, by `allocDegrade` itself). Any init-side constraint
    # `allocateSym` would deposit (e.g. a table/set cardinality floor) is
    # discarded via a throwaway `pcOut` sink -- exactly `eqBV`'s own
    # `var fresh: seq[Z3Bool]` idiom -- because this value is never trusted
    # once the run is marked degraded.
    # Item 3 (walker v115): shares the `"__iteSVMergeDegrade"` tag with the
    # `svSeq` genuine-merge arm above (same "iteSV composite-merge degrade"
    # concept); see that arm's comment and `degradeSymCounter`'s own doc for
    # the collision rationale. Item 9 (round-6 re-review): both sites now go
    # through the shared `degradeAlloc` pairing helper.
    # RFC-0005 S6b: the kind follows what `tyOf(t)` round-trips. For
    # svTable / svSet it is lossless (the stored key / value /
    # element types), so the placeholder is a fresh symbol of the operand's
    # own type: `feUnsupportedOpHavoc`. For svVariant / svMultiVariant it
    # rebuilds the arm-field types from live element SymVals and drops the
    # tag names -- not a faithful round-trip, so it stays `feUnsupportedOp`
    # (dcSubstituted).
    let mergeKind =
      if t.kind in {svVariant, svMultiVariant}: feUnsupportedOp
      else: feUnsupportedOpHavoc
    degradeAlloc(tyOf(t), mergeKind,
      "iteSV: not supported for " & plainEnglishSymValKind(t.kind) & " (Phase 5+)",
      "__iteSVMergeDegrade")
  of svClosure:
    # Phase 15 C1 STUB. Closure path-merge lands with the C2a/C2b walker
    # (an ite over the site-keyed funcSym + a recursive env merge). N46:
    # same walk-reachable array-index-merge hazard as the arms above.
    #
    # Round-6 re-review (item 1, walker v114): UNLIKE the group arm above,
    # a closure cannot express a "fresh unconstrained placeholder of the
    # same kind" -- `closureSite` (which funcSym a call through this value
    # invokes) is a plain Nim `tuple[siteHash, declOrder]` picked at PARSE
    # time per lambda occurrence, not a Z3-modelled value at all, so there
    # is no symbolic const to allocate fresh over: it is fundamentally
    # unmergeable with today's C1-stub representation, not merely
    # inconvenient. Per the review brief, the sanctioned fix for a kind that
    # cannot express a fresh placeholder is to guard BEFORE the fold at its
    # call sites instead (skip the fold, decline the whole index/arm read).
    # No such guard was ADDED here: there is no `itClosure` IRType at all
    # (a closure is the `iekLambda` EXPRESSION, never a storable element/
    # field type -- confirmed by grep: `allocateSym` has no arm that ever
    # constructs an `svClosure`), so neither `isIndex`'s `array[N, T]`
    # element type nor `isVariantField`'s arm-field types can BE a closure
    # in the first place -- this arm is unreachable from either fold today,
    # by construction of the type system, not by an added runtime check.
    # It remains solely for `case t.kind`'s exhaustiveness and as a
    # defensive fallback should Cluster C's C2a/C2b closure-merge work ever
    # let a closure flow into a mergeable position; unchanged (`allocDegrade`
    # + `t`) until that work defines what a sound closure merge even means.
    allocDegrade(feUnsupportedOp,
      "iteSV: svClosure merge lands with Cluster C C2a/C2b")
    t
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
    let mergedRaw = checkedIte(ctx, cond.raw, refT.raw, refE.raw)
    let merged = wrap[Z3AnyAst](ctx, mergedRaw)
    # RFC-0005 S8ar: the merged ref is as many steps from a root as the
    # deeper of the two.
    let steps = max(heapStepsOf(t), heapStepsOf(e))
    if t.kind == svPtr:
      SymVal(kind: svPtr, ptrAst: merged, ptrFamily: t.ptrFamily, ptrPointee: t.ptrPointee,
             ptrSteps: steps)
    else:
      SymVal(kind: svRef, refAst: merged, refPointee: t.refPointee,
             refSteps: steps)


# ---- RFC-0016 review R2-4: the type-directed allocation closure --------------
# `allocateSym` and `seqElemAt`, with everything they reach in the value and
# heap algebra (`defaultZero`, the variant image, the table zero builders, the
# int-width bridge). Moved here from `runtime.nim`; none of it names `WalkCtx`.

proc allocateSeqDataRaw*(elemTy: IRType, name: string): Z3AnyAst =
  ## Dispatch on the element type to instantiate `Z3Array[Z3Int, V]`
  ## with the right typed V, then erase via `toAnyAst`. Cycle 1
  ## supports int/bool elements; more arrive incrementally. RFC-0005 S8ba:
  ## a distinct element is backed by its base (`seqCellTy`).
  let elemTy = seqCellTy(elemTy)
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
      raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always constructed as 8/16/32/64)]
        "allocateSeqDataRaw: unsupported int width " & $elemTy.width)
  else:
    # Round-6 N37 (walker v102) reachability note -- UPGRADED from N36's
    # `known-open`: N36 found this raise reached walk-time from
    # `lowerHofCall`'s two UNGUARDED inline `map`/`filter` call sites (no
    # `isBackedSeqElemTy` guard beforehand). This slice attempted a live
    # repro and found it collides with a PRE-EXISTING, UNRELATED defect
    # (N29, HOF lambda Z3 domain-sort mismatch, ledgered at N16's landing)
    # that fires UPSTREAM of `lowerHofCall`'s `map`/`filter` arms entirely
    # for EVERY inline HOF closure application in the current engine build
    # (confirmed via direct instrumentation, reverted before landing --
    # `tests/tsymex_r6_n37_raise_residue.nim`'s own item-4 honesty note has
    # the full writeup) -- so this specific pair of call sites is not
    # independently demonstrable as a live wrong-verdict RED in isolation.
    # Converted anyway by the MECHANISM argument (N36's own precedent for
    # un-independently-pinnable sites): guard with `isBackedSeqElemTy`
    # BEFORE calling this proc, mirroring the discipline `allocateSym`'s
    # itSeq arm and `defaultZero`'s itSeq arm already use (see their own
    # notes) -- never call this proc for an unbacked element type, rather
    # than catching after the raise (the try/except approach B7r2 already
    # found unsound at non-top-level frames on this backend). A THIRD
    # unguarded caller was found and converted the same way this slice:
    # `lowerSeqLit`'s non-empty-literal branch (the B6 rider above only
    # widened the EMPTY-literal case; that one DOES independently confirm
    # this proc is genuinely reached with the real elemTy, since its own
    # coincidental pre-existing confound is a parser gap, not a Z3-level
    # one, and the two coexist rather than masking reachability).
    #
    # Every caller of `allocateSeqDataRaw` in this file now guards with
    # `isBackedSeqElemTy` (or the equivalent `ty.seqUnsupportedFieldReason.len
    # > 0 or not isBackedSeqElemTy(...)` compound) before calling it:
    # `allocateSym`'s itSeq arm, `defaultZero`'s itSeq arm, `lowerHofCall`'s
    # map/filter inline arms, and `lowerSeqLit`'s non-empty-literal branch.
    # This raise is therefore VERIFIED UNREACHABLE from any call site in this
    # file — kept as a defensive backstop (an internal-consistency invariant,
    # not a valid-DSL-surface shape) rather than removed.
    raise (ref SymexNestedSeqUnsupportedError)(  # [raise-audited: verified-unreachable -- every caller (allocateSym itSeq arm, defaultZero itSeq arm, lowerHofCall map/filter inline, lowerSeqLit non-empty) now guards with isBackedSeqElemTy before calling (N37); defensive backstop only]
      msg: "seq[seq[T]] / seq[complex] not modeled — element kind " &
           plainEnglishTypeKind(elemTy.kind) &
           " (nested seq element type is not supported)")

type TabValLeaf* = enum
  ## RFC-0005 S8ar. The Z3 term a backed `Table` value is held as
  ## (`isTableValTy`): an integer-like value's 64-bit cell, or a term of the
  ## value's own sort.
  ## RFC-0005 S8at: `tvTree`, a container value held leaf-split, one data
  ## array per leaf (`tabValLeaves`).
  tvCell, tvStr, tvF32, tvF64, tvTree

func tabValLeaf*(valTy: IRType): TabValLeaf =
  if isTableContainerValTy(valTy): return tvTree   ## RFC-0005 S8at
  case valTy.kind
  of itString: tvStr
  of itFloat32: tvF32
  of itFloat64: tvF64
  else: tvCell

proc tabTreeDataVars(name: string; keyTy, valTy: IRType): seq[Z3AnyAst]
  ## RFC-0005 S8at fwd-decl (defined after `defaultZero`).

proc tabTreeDataZero(keyTy, valTy: IRType): seq[Z3AnyAst]
  ## RFC-0005 S8at fwd-decl (defined after `defaultZero`).

proc tabDataVarOf[K](name: string; valTy: IRType): Z3AnyAst =
  # RFC-0005 S8at: the live key / value terms that held both sorts across
  # `Z3_mk_array_sort` are gone -- nim-z3's `sortOf(Z3Array[K, V])` now
  # holds them itself (nim-z3 ae509f0, `holdSort`).
  case tabValLeaf(valTy)
  of tvTree: tabTreeDataVars(name, (when K is Z3String: tString() else: tInt()),
                             valTy)[0]
  of tvCell: toAnyAst(mkArrayVar[K, Z3BitVec[64]](name))
  of tvStr:  toAnyAst(mkArrayVar[K, Z3String](name))
  of tvF32:  toAnyAst(mkArrayVar[K, Z3Float32](name))
  of tvF64:  toAnyAst(mkArrayVar[K, Z3Float64](name))

proc tabDataVar(name: string; keyTy, valTy: IRType): Z3AnyAst =
  ## RFC-0005 S8ar. The free data array of a backed `Table[K, V]`, keyed by
  ## the key's term (a string, or a 64-bit cell) and valued by the value's
  ## (`TabValLeaf`). Was `Z3Array[Z3String, Z3BitVec[64]]` for every table.
  if keyTy.kind == itString: tabDataVarOf[Z3String](name, valTy)
  else: tabDataVarOf[Z3BitVec[64]](name, valTy)

proc tabPresentVar(name: string; keyTy: IRType): Z3AnyAst =
  ## RFC-0005 S8ar. The free present array of a backed `Table[K, V]`.
  if keyTy.kind == itString: toAnyAst(mkArrayVar[Z3String, Z3Bool](name))
  else: toAnyAst(mkArrayVar[Z3BitVec[64], Z3Bool](name))

proc tabDataZeroOf[K](valTy: IRType): Z3AnyAst =
  case tabValLeaf(valTy)
  of tvTree: tabTreeDataZero((when K is Z3String: tString() else: tInt()),
                             valTy)[0]
  of tvCell: toAnyAst(mkConstArray[K, Z3BitVec[64]](mkBitVec[64](0'i64)))
  of tvStr:  toAnyAst(mkConstArray[K, Z3String](mkString("")))
  of tvF32:  toAnyAst(mkConstArray[K, Z3Float32](mkFloat32(0'f32)))
  of tvF64:  toAnyAst(mkConstArray[K, Z3Float64](mkFloat64(0.0)))

proc emptyTable(keyTy, valTy: IRType): SymVal =
  ## RFC-0005 S8u (was inline in `defaultZero`); S8ar: of every backed
  ## shape. No key present (a constant `false` array), size 0; the data
  ## array is a constant too, read only at a present key.
  let (data, present) =
    if keyTy.kind == itString:
      (tabDataZeroOf[Z3String](valTy),
       toAnyAst(mkConstArray[Z3String, Z3Bool](mkBool(false))))
    else:
      (tabDataZeroOf[Z3BitVec[64]](valTy),
       toAnyAst(mkConstArray[Z3BitVec[64], Z3Bool](mkBool(false))))
  # RFC-0005 S8at: a container value's further leaves, constant too.
  let more = if tabValLeaf(valTy) == tvTree: tabTreeDataZero(keyTy, valTy)[1 .. ^1]
             else: @[]
  SymVal(kind: svTable, tabDataRaw: data, tabDataMore: more,
         tabPresentRaw: present,
         tabSize: mkInt(0), tabKeyTy: keyTy, tabValTy: valTy)

proc iteFolded*[T: Z3Term](cond: Z3Bool; t, e: T): T =
  ## `ite(cond, t, e)`, or the arm `cond` picks when it is a Boolean literal.
  ## A union-image merge over a constructed object's own discriminator tests
  ## `#x00 == #x00`; left as an `ite`, the solver must see through it before
  ## `bvIntInverseFacts` can pair an `int2bv` with the view it inverts.
  case Z3_get_bool_value(cond.ctx.raw, cond.raw)
  of Z3_L_TRUE: t
  of Z3_L_FALSE: e
  else: ite(cond, t, e)

proc unionImageGate*(ty: IRType): Option[vl.VariantLayout]

proc activeMemberTracked*(ty: IRType): bool

proc unionCellCount*(lay: vl.VariantLayout): int

proc zeroImage*(lay: vl.VariantLayout): seq[Z3BitVec[64]]

proc armImage*(lay: vl.VariantLayout; tag: int; slots: seq[SymVal];
              fill: seq[Z3BitVec[64]]): Option[seq[Z3BitVec[64]]]

proc variantImage(lay: vl.VariantLayout; disc: SymVal;
                  arms: OrderedTable[int, seq[SymVal]];
                  fill: seq[Z3BitVec[64]]): seq[Z3BitVec[64]]

proc activeOf*(disc: SymVal): ref SymVal
  ## RFC-0016 PRC-07 slice B fwd-decls: the union byte image (c) and the
  ## active member (cpp) a value variant carries under `--fieldChecks:off`.

proc seqElemProto*(elemTy: IRType): SymVal =
  ## RFC-0005 S8bc. A value of a tree element type: the shape (kinds, element
  ## types, a placeholder seq's flag) a read rebuilds from the selects of the
  ## data arrays (`svWithLeaves`), and the leaf sorts the arrays are built
  ## at. Its constants and init facts are discarded, as `heapCellSelect`'s
  ## prototype's are. `allocateSym`, not `defaultZero`: it is total (a case
  ## object whose zero is no legal value has no `defaultZero`).
  var scratch: seq[Z3Bool]
  allocateSym(elemTy, "__seqElemProto", scratch)

proc allocateSeqArrs*(elemTy: IRType; name: string): seq[Z3AnyAst] =
  ## RFC-0005 S8bc. The free data arrays of a seq of `elemTy`: one
  ## (`allocateSeqDataRaw`) for a scalar element; one per leaf for a tree
  ## element, `Int -> <the leaf's sort>`, leaf 0 named `name` and leaf `i`
  ## `name.@d<i>`. The sorts are runtime (a seq leaf is itself an array), so
  ## the arrays are built raw, as `tabTreeDataVars`' are; the prototype and
  ## `idxHold` keep the sorts alive across `Z3_mk_array_sort`.
  ## RFC-0005 batch 4: built at the element's cell type (`seqCellTy`).
  let elemTy = seqCellTy(elemTy)
  if not isTreeSeqElemTy(elemTy): return @[allocateSeqDataRaw(elemTy, name)]
  let ctx = requireCurrentContext()
  let proto = seqElemProto(elemTy)
  let idxHold = mkZ3IntLit(0)
  let idxSort = ctx.checkErr Z3_get_sort(ctx.raw, idxHold.raw)
  let leaves = svLeafTerms(proto, elemTy)
  for i, leaf in leaves:
    let valSort = ctx.checkErr Z3_get_sort(ctx.raw, leaf.raw)
    let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, idxSort, valSort)
    let nm = if i == 0: name else: name & ".@d" & $i
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, nm.cstring)
    result.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

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

proc allocDistinctSym(ty: IRType, baseName: string,
                      pcOut: var seq[Z3Bool]): SymVal =
  ## Allocation cost mirrored in allocCostOf's itDistinct arm (types.nim) --
  ## update both together.
  ## Phase 15 G4 (ADR-0008 D4). Allocate a `distinct T` SymVal: a fresh const of
  ## the "DistinctName" uninterpreted sort plus its ejected base. The sort
  ## comes from `ensureDistinctSort`. The base SymVal is bound to
  ## `eject(distinctConst)` so the witness eject-chain (and explicit
  ## conversions) resolve to a concrete base value.
  let ctx = requireCurrentContext()
  let name = ty.distinctName
  # 1. Allocate (or reuse) the distinct sort + inject/eject func-decls + axioms.
  let entry = ensureDistinctSort(ty)
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
      checkedEq(ctx, ejD.raw, rawAstOf(baseSym)))
  let boxed = new(SymVal)
  boxed[] = baseSym
  SymVal(kind: svDistinct, distinctAst: dAny, distinctName: name,
         distinctBaseSym: boxed)

proc allocateSym*(ty: IRType, baseName: string, pcOut: var seq[Z3Bool],
                 stringBacked: bool = false,
                 intOffsetPositions: seq[int] = @[]): SymVal =
  ## Recursively allocate a SymVal for `ty`. Init-side constraints
  ## (like `seqLen ≥ 0`) accumulate into `pcOut`.
  ##
  ## N40 (round-6 fix round 6, walker v104): `allocateSym` is now TOTAL for
  ## every CLASSIFIABLE input -- every arm that used to `raise` a dedicated
  ## classified-decline carrier (`itUninterp`'s three placeholder prefixes,
  ## `itTable`'s key/value-type mismatches, `itSet`'s element-type mismatch)
  ## now calls `allocDegrade` (early-foundations section, above -- see its
  ## own doc comment for the full sink-choice design writeup) and returns a
  ## fresh,
  ## type-plausible PLACEHOLDER value instead of unwinding. The ONLY
  ## remaining raises in this proc are genuine Defect-class walker-invariant
  ## sentinels (the `itUninterp` cluster-E fallback, `itMultiVariant`'s
  ## axis-disc-kind check via `variantDiscEq`/its own arm) -- states
  ## `classifyType`/the parser can never actually produce, out of the
  ## raw-raise-in-lower CLASS's own scope per N36's audit header.
  ##
  ## The placeholder's SORT is deliberately ARBITRARY/UNCONSTRAINED-BEYOND-
  ## INERT (a bare `svBool` for `itUninterp`; a `itTable`/`itSet` value with
  ## its cardinality FORCED to 0, mirroring the `itSeq` placeholder's own
  ## established "forced-empty, structurally never legitimately selected
  ## from" contract, Bug #2/B7r2) -- because the run is ALREADY marked
  ## degraded the instant `allocDegrade` returns (Invariant 3), so no
  ## verdict or witness downstream of this value is ever trusted. This is
  ## deliberately NOT the fuller `isUnsupportedFieldPlaceholder` read-taint
  ## machinery `itSeq` carries (which exists to let paths that never TOUCH
  ## the placeholder stay UNTAINTED, preserving precision for e.g. an
  ## inactive variant arm) -- full read-taint plumbing for `itUninterp`/
  ## `itTable`/`itSet` would be disproportionate machinery for this slice's
  ## scope, and "immediate-degrade-on-alloc" is not a NEW precision loss:
  ## `isVariantConstructSym`/`lowerVariantLit`'s own pre-existing N39 guards
  ## already degrade unconditionally on ALLOCATION (never gated on a later
  ## read) for these exact five shapes, so this matches established,
  ## audited precedent rather than over-declining a shape the engine
  ## previously modeled precisely.
  ##
  ## The pre-walk PARAMETER-entry boundary (`runSymexImpl`, ~line 9841)
  ## keeps its pre-N40 WHOLE-RUN raise semantics unchanged: it pre-checks
  ## every top-level param type with `unallocatableFieldIssue`
  ## (`types.nim`) and raises the classified error itself, by design,
  ## before this proc -- or any walk state -- ever exists (see
  ## `raiseParamAllocIssue`'s own doc comment). Existing pins on param-level
  ## declines are unaffected: the exception TYPE, `kind`, and message text
  ## raised there are unchanged from what `allocateSym` itself used to
  ## raise for the same shape.
  case ty.kind
  of itUninterp:
    # Phase 15 R1a (ADR-0010, Breadth-LOW-L4): classifyType maps `owned T` /
    # `Atomic[T]` to an `__ownership:*` placeholder. Allocating
    # one raises the classified ownership halt (caught at the runSymex boundary
    # → heUnsupportedOwnership → sxUnknown, Invariant 3).
    if ty.uninterpName.startsWith("__ownership:"):
      # N40: was `raise (ref SymexOwnershipUnsupportedError)` -- see
      # `allocDegrade`'s own doc comment (early-foundations section, above)
      # for the full totality design writeup. The pre-walk param-entry boundary
      # (`raiseParamAllocIssue`) raises this SAME classified error, with
      # this SAME message, for a top-level param -- this arm is now reached
      # ONLY at walk time (nested composite allocation).
      allocDegrade(heUnsupportedOwnership,
        "ownership wrapper `" & ty.uninterpName.substr(len("__ownership:")) &
        "` is out of scope for the ref cluster (Breadth-LOW-L4)")
      return SymVal(kind: svBool, bo: mkBoolVar(baseName & ".unalloc"))
    # RFC-chapulin-hardening CR-2b (Cluster 2 — Crash-totality, round-2
    # Option 2): `classifyType`'s parameter-type catch-all
    # (`dsl_typebridge.nim`) maps an unsupported PARAMETER type to an
    # `__unsupported:*` placeholder rather than aborting compilation.
    if ty.uninterpName.startsWith("__unsupported:"):
      # N40: was `raise (ref SymexClassifiedDegradeError)` -- see
      # `allocDegrade`'s own doc comment for the totality design writeup.
      allocDegrade(feUnsupportedParamType,
        "unsupported parameter type `" &
        ty.uninterpName.substr(len("__unsupported:")) &
        "`; the supported fragment is {bool, int, int{8,16,32,64}, " &
        "uint, uint{8,16,32,64}, range[..], Natural, Positive, float, " &
        "float{32,64}, string, char, byte}")
      return SymVal(kind: svBool, bo: mkBoolVar(baseName & ".unalloc"))
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
    # keep their ordinary `itSeq`/`itTable`/`itSet` classification. Kept
    # DISTINCT from `feUnsupportedParamType`: a different macro (post-solve
    # witness-reader codegen, not param-type classify), different call
    # site, per §0's three-classes framing.
    if ty.uninterpName.startsWith("__unsupported_witness:"):
      # N40: was `raise (ref SymexClassifiedDegradeError)` -- see
      # `allocDegrade`'s own doc comment for the totality design writeup.
      allocDegrade(feUnsupportedWitnessType, unsupportedWitnessMsg(
        ty.uninterpName.substr(len("__unsupported_witness:"))))
      return SymVal(kind: svBool, bo: mkBoolVar(baseName & ".unalloc"))
    # RFC-0005 S8z: a proc-valued (`__closure`) slot the walker has no
    # `svClosure` for -- a closure-typed object field, a recursion-cut
    # closure return -- is a scoped decline, not the sentinel below (it was
    # `weInternalWalkerFault`). A closure value the walker BUILT (a lambda,
    # a proc in value position, a callee's returned lambda) never allocates.
    if ty.uninterpName == "__closure":
      allocDegrade(ceUnsupportedHof,
        "a proc-valued value with no lambda the walker built (a closure " &
        "field or an unbound closure result) has no symbolic model")
      return SymVal(kind: svBool, bo: mkBoolVar(baseName & ".unalloc"))
    # Genuine Defect-class walker-invariant sentinel -- `classifyType` only
    # ever builds an `itUninterp` with one of the three prefixes handled
    # above; reaching here means the walker itself produced a malformed
    # `IRType`, not an unmodeled SUT construct. Out of the raw-raise-in-lower
    # CLASS's own scope (N36's audit header) -- left as a raw raise.
    raise newException(ValueError,  # [raise-audited: category-c: documented walker-invariant sentinel (own comment: classifyType only ever builds this itUninterp shape with one of three handled prefixes; explicitly out of the raw-raise-in-lower CLASS's scope per N36's own header)]
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
    if hierChain(pointee).len > 1:
      # RFC-0005 S8bn (item 9). A non-nil ref of a hierarchy type S (depth
      # `s`) addresses an object whose dynamic type is S or one of its
      # descendants: its run-type tags at depths `1..s` are S's own chain
      # (`inheritTagKey`). They were free, so a parameter of static type
      # `Mid` aliasing one of static type `Base` could fail `Mid(b)` (a
      # false `sxSat`, a witness no Nim value realises). The facts are on the
      # INPUT tag heaps (`heap_<key>`), which an allocation never changes
      # (it stores into the path's heap); the depths below `s` stay free:
      # any descendant.
      let tagTy = tInt(64, signed = true)
      let nilAst = currentNilConsts[refPointeeTypeId(pointee)]
      let isNil = wrap[Z3Bool](ctx, checkedEq(ctx, refAny.raw, nilAst.raw))
      let chain = hierChain(pointee)   ## RFC-0005 S8bn: a case object's too
      for lvl in 1 ..< chain.len:
        let key = inheritTagKey(pointee, lvl)
        let arr = mkHeapArrayVar(ctx, refSort, tagTy, "heap_" & key)
        # Each raw term is wrapped (ref-counted) before the next Z3 call:
        # an unwrapped one may be collected under it.
        let tag = wrap[Z3AnyAst](ctx, checkedSelect(ctx, arr.raw, refRaw))
        let code = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_int64(ctx.raw,
          inheritTagCode(chain[lvl]), sortOfRaw(ctx, tag.raw)))
        pcOut.add(isNil or wrap[Z3Bool](ctx, checkedEq(ctx, tag.raw, code.raw)))
    if ty.kind == itRef:
      SymVal(kind: svRef, refAst: refAny, refPointee: pointee)
    else:
      SymVal(kind: svPtr, ptrAst: refAny, ptrFamily: true, ptrPointee: pointee)
  of itFloat32: SymVal(kind: svFloat32, fp32: mkFloat32Var(baseName))
  of itFloat64: SymVal(kind: svFloat64, fp64: mkFloat64Var(baseName))
  of itDistinct:   ## Phase 15 G4 (ADR-0008 D4): fresh uninterpreted sort.
    allocDistinctSym(ty, baseName, pcOut)
  of itVariant:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
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
      # instead supplied by `discriminatorDomain`'s ordinal set below,
      # which folds in the full enum-tag domain whenever an else arm
      # is present (#163 W6's fix, extracted per review R12).
    # Issue #163 review R12: `discriminatorDomain` is the ONE place that
    # decides this variant's legal discriminator domain -- shared with the
    # Promoted-Int path in `runSymexImpl`. An empty `ordSet` means the
    # range-alias-else-domain case applies (see its doc comment): the
    # disc's own declared range, already asserted by the `allocateSym`
    # recursion above, fully describes the domain and no equality
    # disjunction is needed (asserting one over just the explicit `of N:`
    # literals would falsely exclude every else-covered value, #163 W6).
    let (_, _, ordSet) = discriminatorDomain(ty)
    if ordSet.len > 0:
      var clause = variantDiscEq(discInner, int64(ordSet[0]))
      for k in 1 ..< ordSet.len:
        clause = clause or variantDiscEq(discInner, int64(ordSet[k]))
      pcOut.add clause
    var sv = SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: ty.vDiscName,
                    vObjectName: ty.vObjectName,
                    vArmFields: armFields, vArmFieldNames: armNames,
                    vPlainFields: plainFields,
                    vPlainFieldNames: ty.vPlainFieldNames)
    # RFC-0016 PRC-07 slice B: a free variant's padding and tail bytes are
    # free too (fresh cells); the active arm's fields are its slots' bytes.
    let gate = unionImageGate(ty)
    if gate.isSome:
      var fill: seq[Z3BitVec[64]]
      for i in 0 ..< unionCellCount(gate.get):
        fill.add mkBitVecVar[64](baseName & ".@bytes" & $i)
      for i in 0 ..< unionCellCount(gate.get):
        fill.add mkBitVec[64](0'i64)   # a parameter's bytes are all determinate
      sv.vImage = variantImage(gate.get, discInner, armFields, fill)
    if activeMemberTracked(ty): sv.vActive = activeOf(discInner)
    sv
  of itMultiVariant:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
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
      for arm in ax.arms:
        var fields: seq[SymVal]
        for j, ft in arm.fieldTypes:
          let path = baseName & "." & ax.discName &
                     ".@" & arm.tagName & "." & arm.fieldNames[j]
          fields.add allocateSym(ft, path, pcOut)
        armFields[arm.tagOrdinal] = fields
        armNames[arm.tagOrdinal]  = arm.fieldNames
      # RFC-0005 S8s: the axis's legal discriminator domain is
      # `axisDiscriminatorDomain`'s, as for a single `case`. This arm used
      # to disjoin the arm ordinals themselves, so an `else` arm put its
      # sentinel -1 (0xFF on a `u8` disc) in the domain and left out every
      # ordinal it covers: an input with `k` in an `else` arm was
      # unreachable, and a callee's zero-valued result contradicted its
      # own allocation.
      let (_, _, ordSet) = axisDiscriminatorDomain(ax)
      # RFC-0005 S8u: a `bool` axis allocates an svBool discriminator, as a
      # single-case `bool` variant does (Phase 15 F9c); `variantDiscEq` has
      # its arm. This raised `weInternalWalkerFault` before S8u.
      if discInner.kind notin {svBV8, svBV16, svBV32, svBV64, svBool}:
        raise newException(ValueError,  # [raise-audited: category-c: discriminator-kind invariant (multi-variant axis discriminator is always BV- or (bool axis) Bool-allocated)]
          "symex Phase 14: multi-variant axis disc must be a BV or bool kind " &
          "(got " & $discInner.kind & ")")
      if ordSet.len > 0:
        var clause = variantDiscEq(discInner, int64(ordSet[0]))
        for k in 1 ..< ordSet.len:
          clause = clause or variantDiscEq(discInner, int64(ordSet[k]))
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
      # R3 (S2): stamp the promoted value's static Nim type (`ty.width`/
      # `ty.signed` — always populated for `itInt`) so `overflowCondInt` can
      # fork for it downstream; see `SymVal.ziWidth`'s own doc comment.
      let v = SymVal(kind: svInt, zi: mkIntVar(baseName),
                      ziWidth: ty.width, ziSigned: ty.signed)
      # Issue #163 W8: an int-offset-promoted symbol still carries whatever
      # declared range its Nim type has (`ty.hasRange`) -- this arm ignored
      # it, unlike the `else` branch below (issue #162's original fix site).
      # Routed through `rangeCondsIfNeeded`, which now Int-sort-dispatches
      # on `v.kind` (see its own doc comment) rather than assuming BV.
      for c in rangeCondsIfNeeded(v, ty):
        pcOut.add c
      v
    else:
      let v = bvVar(ty, baseName)
      # Issue #162. Assert the declared bounds of a `range[lo..hi]` here, at
      # the ONE place every int is allocated. Top-level params constrain
      # themselves from `IRParam` (which also carries #134's
      # assertion-derived ranges, a non-type fact), but a field, a nested
      # field, an array element and a seq element all arrive through this
      # recursion and had no other route — so an unconstrained model picked a
      # value outside the range and witness construction raised `RangeDefect`
      # out of the caller's process.
      #
      # Issue #163 review R11: routed through `rangeCondsIfNeeded` (beside
      # `bvRangeConds`), which carries the signed/unsigned-dispatch
      # rationale in its own doc comment now.
      for c in rangeCondsIfNeeded(v, ty):
        pcOut.add c
      v
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
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
    var fields: seq[SymVal]
    for i, ft in ty.fields:
      let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                   else: "." & $i
      # Round-6 B5: a traced position allocates svInt directly (only
      # meaningful for an itInt field — any other field kind at a traced
      # position is simply not a scan-offset shape, so it falls through to
      # the ordinary recursive allocation unchanged).
      if i in intOffsetPositions and ft.kind == itInt:
        # R3 (S2): stamp the promoted field's static Nim type (`ft.width`/
        # `ft.signed`) — same rationale as the bare-`itInt` arm above.
        let v = SymVal(kind: svInt, zi: mkIntVar(baseName & suffix),
                        ziWidth: ft.width, ziSigned: ft.signed)
        # Issue #163 W8: same rationale as the bare-itInt arm above.
        for c in rangeCondsIfNeeded(v, ft):
          pcOut.add c
        fields.add v
      else:
        fields.add allocateSym(ft, baseName & suffix, pcOut)
    SymVal(kind: svTuple, fields: fields, fieldNames: ty.fieldNames)
  of itArray:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
    # #142: nested arrays land via the existing recursion. The
    # previous guard was overly cautious — allocateSym recurses
    # naturally through the element type.
    var elems: seq[SymVal]
    for i in 0 ..< ty.size:
      elems.add allocateSym(ty.elemTy, baseName & "." & $i, pcOut)
    SymVal(kind: svArray, arrElems: elems, arrElemTy: ty.elemTy)
  of itSeq:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
    if ty.seqUnsupportedFieldReason.len > 0 or not isBackedSeqElemTy(ty.seqElemTy):
      # Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution
      # 2026-08-15) + B7r2 (walker v88, GENERALIZED beyond record fields —
      # see the `not isBackedSeqElemTy(ty.seqElemTy)` disjunct added this
      # slice): a declared field OR a bare local/param/call-return whose
      # element kind `allocateSeqDataRaw` cannot back (e.g.
      # `seq[(string,string)]`). Force `seqLen == 0` and build an INERT
      # placeholder data array — never selected from (nothing indexes a
      # length-0 seq) — instead of calling `allocateSeqDataRaw(ty.seqElemTy,
      # ...)` (which would raise `SymexNestedSeqUnsupportedError`
      # unconditionally, reintroducing Bug #2's whole-run poison the moment
      # this value is merely ALLOCATED, regardless of whether any path
      # reads it — chapulin's B7-1 BLOCKER (c): a helper proc RETURNING
      # `seq[(string,string)]` poisoned every caller merely binding the
      # call's result, even when the binding was immediately discarded).
      # The element SORT here is arbitrary/fixed (`Z3Int -> Z3Bool`) —
      # never the real `ty.seqElemTy` — because it structurally can never
      # be selected from; a declared-FIELD read is intercepted at PARSE
      # time (`dsl_parser.nim`'s `nnkDotExpr` arm); a bare local/param/
      # return-value INDEXED read is intercepted at WALK time (the `isIndex` arm
      # in runtime.nim, `"index read"` — the generalization this slice adds, since a
      # bare value has no static field-access site for the parser to
      # intercept). `isUnsupportedFieldPlaceholder: true` lets `retBindEq`
      # (below), witness extraction (`extractFromSymVal`), and `isIndex`
      # recognize and special-case this value.
      let lenSym = mkIntVar(baseName & ".len")
      pcOut.add (lenSym == mkInt(0))
      let dataRaw = toAnyAst(mkArrayVar[Z3Int, Z3Bool](baseName & ".data"))
      SymVal(kind: svSeq, seqLen: lenSym, seqDataRaw: dataRaw,
             seqElemTy: ty.seqElemTy, isUnsupportedFieldPlaceholder: true,
             # N47-followup (walker v110): mirror the type-level reason/kind
             # onto the runtime value (empty/default for a bare-value
             # placeholder, since `ty` carries none there) — see
             # `seqUnsupportedFieldReason`'s doc (above) for why the read
             # chokepoint needs this.
             seqUnsupportedFieldReason: ty.seqUnsupportedFieldReason,
             seqUnsupportedFieldKind: ty.seqUnsupportedFieldKind)
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
      # RFC-0005 S8bc: one array per leaf of a tree element; S8ba: of the
      # element's cell type (`seqCellTy`, normalised by both helpers).
      mkSeqSV(lenSym, allocateSeqArrs(ty.seqElemTy, baseName & ".data"),
              ty.seqElemTy)
  of itTable:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
    # Phase 5 cycle 5 narrow scope: Table[string, int]. Other (K, V)
    # pairs land incrementally — the wrap[Z3Array[K, V]] machinery
    # supports them with a per-pair dispatch.
    if not isTableKeyTy(ty.tabKeyTy):   # RFC-0005 S8ar: was `!= itString`
      # N40: was `raise newException(ValueError, ...)` -- an UNTAGGED crash
      # (not even a classified carrier) on ORDINARY user syntax
      # (`Table[int, string]` is unrestricted Nim; `unallocatableFieldIssue`
      # had a false-negative gap for exactly this shape prior to this
      # slice — types.nim). See `allocDegrade`'s own doc comment for the
      # totality design writeup. The inert placeholder below mirrors the
      # itSeq placeholder's own "forced-empty, arbitrary/never legitimately
      # selected from" contract (Bug #2/B7r2, above): `tabSize` is forced
      # `== 0`, and the data/present arrays keep the SAME `Z3String`-keyed
      # shape the real Table[string,*] path uses (the Z3 representation is
      # always string-keyed regardless of the DECLARED Nim key type — see
      # the real allocation arm below — so this is not even a sort lie,
      # merely an unconstrained/inert one).
      allocDegrade(seUnsupportedTableKeyType,
        "Table key type not modeled: " & $ty.tabKeyTy &
        " — only Table[string, V] is supported (seUnsupportedTableKeyType)")
      let lenSym = mkIntVar(baseName & ".len")
      pcOut.add (lenSym == mkInt(0))
      let dataAst = toAnyAst(
        mkArrayVar[Z3String, Z3BitVec[64]](baseName & ".data"))
      let presentAst = toAnyAst(
        mkArrayVar[Z3String, Z3Bool](baseName & ".present"))
      SymVal(kind: svTable, tabDataRaw: dataAst, tabPresentRaw: presentAst,
             tabSize: lenSym, tabKeyTy: ty.tabKeyTy, tabValTy: ty.tabValTy)
    else:
      # N48 (walker v109): the `itInt`-kind arm used to unconditionally
      # `doAssert width == 64 and signed` -- a live AssertionDefect escape
      # from the N40 totality chokepoint for a `Table[string, int32]` (or
      # any other non-canonical-width/unsigned int) VALUE type, caught only
      # generically as `weInternalWalkerFault` instead of the classified
      # `seUnsupportedTableValType` `unallocatableFieldIssue` (types.nim)
      # already promises for exactly this shape -- pinned as a
      # KNOWN-DISPARITY by N43-H2 prior to this fix. Folded into ONE guard
      # covering both "not itInt at all" and "itInt but the wrong width/
      # signedness", so every unsupported value type -- not just the
      # non-itInt kinds N40 originally converted -- reaches the SAME
      # `allocDegrade` + inert-placeholder idiom (mirrors the key-type arm
      # above and the itSet arm below, both of which already combine their
      # kind/width guard into a single condition for the same reason).
      # RFC-0005 S8z: any fixed-width int value type (`isBackedTableTy`),
      # held in the 64-bit cell (`cellOf` / `cellValue`).
      if isBackedTableTy(ty.tabKeyTy, ty.tabValTy):
        # RFC-0005 S8ar: the arrays' sorts follow the key and value types
        # (`tabDataVar`); a narrower key type also bounds the size by its
        # domain, as a `HashSet`'s element type does.
        let dataAst = tabDataVar(baseName & ".data", ty.tabKeyTy, ty.tabValTy)
        # RFC-0005 S8at: a container value's further leaves.
        let moreAsts =
          if tabValLeaf(ty.tabValTy) == tvTree:
            tabTreeDataVars(baseName & ".data", ty.tabKeyTy, ty.tabValTy)[1 .. ^1]
          else: @[]
        let presentAst = tabPresentVar(baseName & ".present", ty.tabKeyTy)
        let sizeSym = mkIntVar(baseName & ".len")
        pcOut.add (sizeSym >= mkInt(0))
        let ceiling = if ty.tabKeyTy.kind == itString: 1024'i64
                      else: min(1024'i64, cellDomainSize(ty.tabKeyTy))
        pcOut.add (sizeSym <= mkInt(ceiling))   ## same ceiling as seqs
        # RFC-0005 S8f: tie `sizeSym` to the present array at every check.
        registerTableBase(presentAst, sizeSym, ty.tabKeyTy)
        let tsv = SymVal(kind: svTable, tabDataRaw: dataAst, tabDataMore: moreAsts,
                         tabPresentRaw: presentAst, tabSize: sizeSym,
                         tabKeyTy: ty.tabKeyTy, tabValTy: ty.tabValTy)
        registerTabTreeBase(tsv)   ## RFC-0005 S8at
        tsv
      else:
        # N40: was `raise (ref SymexUnsupportedTableValTypeError)` -- see
        # `allocDegrade`'s own doc comment for the totality design writeup.
        # Inert placeholder, same contract as the key-type arm above.
        allocDegrade(seUnsupportedTableValType,
          "Table value type not modeled: " & $ty.tabValTy &
          " — only Table[string, V] with V a fixed-width integer, char, " &
          "enum or range is supported (seUnsupportedTableValType)")
        let lenSym = mkIntVar(baseName & ".len")
        pcOut.add (lenSym == mkInt(0))
        let dataAst = toAnyAst(
          mkArrayVar[Z3String, Z3BitVec[64]](baseName & ".data"))
        let presentAst = toAnyAst(
          mkArrayVar[Z3String, Z3Bool](baseName & ".present"))
        SymVal(kind: svTable, tabDataRaw: dataAst, tabPresentRaw: presentAst,
               tabSize: lenSym, tabKeyTy: ty.tabKeyTy, tabValTy: ty.tabValTy)
  of itBitSet:
    # RFC-0005 S8bq: a builtin `set[T]` is one fresh bit-vector with a bit
    # per value of `T`; every value of it is a legal set. Allocation cost
    # mirrored in allocCostOf (types.nim).
    let ctx = requireCurrentContext()
    let srt = ctx.checkErr Z3_mk_bv_sort(ctx.raw,
                                         cuint(bitSetDomain(ty.bsElemTy).size))
    SymVal(kind: svBitSet,
           bsRaw: wrap[Z3AnyAst](ctx, rawConstOf(ctx, srt, baseName)),
           bsElemTy: ty.bsElemTy)
  of itSet:
    # Allocation cost mirrored in allocCostOf (types.nim) -- update both together.
    # RFC-0005 S8z: any fixed-width int element type (`isBackedSetElemTy`),
    # held in the 64-bit cell (`cellOf`); a narrower one also bounds the
    # size by its domain.
    if isBackedSetElemTy(ty.setElemTy):
      let memAst = toAnyAst(
        mkArrayVar[Z3BitVec[64], Z3Bool](baseName & ".members"))
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym >= mkInt(0))
      pcOut.add (sizeSym <= mkInt(min(1024'i64, cellDomainSize(ty.setElemTy))))
      # RFC-0005 S8f: tie `sizeSym` to the member array at every check.
      registerSetBase(memAst, sizeSym, ty.setElemTy)
      SymVal(kind: svSet, setMembersRaw: memAst,
             setSize: sizeSym, setElemTy: ty.setElemTy)
    else:
      # N40: was `raise (ref SymexUnsupportedSetCharInteropError)` -- see
      # `allocDegrade`'s own doc comment for the totality design writeup.
      # Inert placeholder, same "forced-empty, arbitrary sort, never
      # legitimately selected from" contract as the itTable arms above.
      allocDegrade(seUnsupportedSetCharInterop,
        "HashSet element type not modeled: " & $ty.setElemTy &
        " — only HashSet[T] with T a fixed-width integer, char, enum or " &
        "range is supported (seUnsupportedSetCharInterop)")
      let sizeSym = mkIntVar(baseName & ".len")
      pcOut.add (sizeSym == mkInt(0))
      let memAst = toAnyAst(
        mkArrayVar[Z3BitVec[64], Z3Bool](baseName & ".members"))
      SymVal(kind: svSet, setMembersRaw: memAst,
             setSize: sizeSym, setElemTy: ty.setElemTy)

proc svIntToBV*(sv: SymVal, likeKind: SVKind): SymVal =
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
    raise newException(ValueError,  # [raise-audited: category-c: int-family-only reachability (doAssert sv.kind == svInt at entry)]
      "svIntToBV: target kind is not BV — got " & $likeKind)

proc bv64Operand*(v: SymVal): Option[Z3BitVec[64]] =
  ## RFC-0005 S8u. A 64-bit int operand of a `Table[string, int]` value or a
  ## `HashSet[int]` element: the bit-vector itself, or an Int-promoted value
  ## converted (`svIntToBV`, exact for an int64). `none` for any other kind.
  case v.kind
  of svBV64: some(v.bv64)
  of svInt: some(svIntToBV(v, svBV64).bv64)
  else: none(Z3BitVec[64])

proc stampedIntToBV*(sv: SymVal): SymVal =
  ## RFC-0005 S8w: a WIDTH-STAMPED `svInt` (`ziWidth` in 8/16/32/64) is a
  ## Nim int of that width and signedness whose value lies in its type's
  ## window, so `int2bv` at that width is its exact bit pattern, and the
  ## BV it yields carries the Nim type's signedness (so a signed
  ## comparison, `shr`'s arithmetic shift, and the reconcile back are the
  ## Nim ones). `svIntToBV` alone stamps every result unsigned, which is
  ## right for the unstamped `.len`/`find` sentinels it was built for and
  ## wrong for a signed param: `(x and -1) < 0` compared unsigned.
  doAssert sv.kind == svInt and sv.ziWidth in [8, 16, 32, 64]
  let back = bvOfInt(sv)          # RFC-0005 S8ax: a converted bit-vector
  if back.isSome: return back.get
  let k = case sv.ziWidth
          of 8: svBV8
          of 16: svBV16
          of 32: svBV32
          else: svBV64
  result = svIntToBV(sv, k)
  result.signed = sv.ziSigned

proc lowerConvIntWidth*(operandSV: SymVal, tgtWidth: int, tgtSigned: bool): SymVal =
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
  if operandSV.kind == svInt:
    # RFC-0005 S8ax: a narrow cell of an Int-sorted heap (`intHeapCell`)
    # reads as a width-stamped Int. Widening keeps its value, so it is
    # restamped; only a signed source widened to an unsigned target wraps,
    # and that goes through the bit-vector of the source's width.
    if operandSV.ziWidth > 0 and operandSV.ziSigned and not tgtSigned:
      return lowerConvIntWidth(stampedIntToBV(operandSV), tgtWidth, tgtSigned)
    return SymVal(kind: svInt, zi: operandSV.zi, ziWidth: tgtWidth,
                  ziSigned: tgtSigned, ziIvl: operandSV.ziIvl)
  # RFC-0005 S8be. An operand at least as wide as the target is a literal
  # of the narrow source type: `int(high(int32))`'s `high(int32)` lowers
  # through `mkIntLit`, which carries no width, to a 64-bit bit-vector
  # holding 2147483647. The parse widens only from the declared source
  # type, so the value lies in its window, which the target's holds: the
  # target-width low bits are the value. Every form faulted here
  # (`weInternalWalkerFault`, "unsupported operand kind for widening").
  let opWidth =
    case operandSV.kind
    of svBV8: 8
    of svBV16: 16
    of svBV32: 32
    of svBV64: 64
    else: 0
  if opWidth >= tgtWidth:
    if opWidth > tgtWidth: return truncBV(operandSV, tgtWidth, tgtSigned)
    var same = operandSV
    same.signed = tgtSigned
    return same
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

proc cellOf*(v: SymVal; ty: IRType): Option[Z3BitVec[64]] =
  ## RFC-0005 S8z. A `Table` value / `HashSet` element of the fixed-width
  ## int type `ty` (`isContainerIntLeaf`) as its 64-bit container cell:
  ## sign- or zero-extended by its own signedness (the cell of `-1'i8` is
  ## `-1`, of `255'u8` is `255`), so equal values have equal cells and a
  ## cell read back at `ty`'s width (`cellValue`) is the value. `none` for a
  ## kind that is not an int of `ty`'s width or an Int-promoted value.
  if ty.kind == itBool:
    return (if v.kind == svBool:
              some(ite(v.bo, mkBitVec[64](1'i64), mkBitVec[64](0'i64)))
            else: none(Z3BitVec[64]))
  case v.kind
  of svBV8:  (if ty.width == 8:  some(lowerConvIntWidth(v, 64, v.signed).bv64)
              else: none(Z3BitVec[64]))
  of svBV16: (if ty.width == 16: some(lowerConvIntWidth(v, 64, v.signed).bv64)
              else: none(Z3BitVec[64]))
  of svBV32: (if ty.width == 32: some(lowerConvIntWidth(v, 64, v.signed).bv64)
              else: none(Z3BitVec[64]))
  of svBV64, svInt: (if ty.width == 64: bv64Operand(v)
                     else: none(Z3BitVec[64]))
  else: none(Z3BitVec[64])

proc ofByteShift*(n: int): Z3BitVec[64] = mkBitVec[64](int64(n * 8))

proc byteMask*(len: int): Z3BitVec[64] =
  if len >= 8: not mkBitVec[64](0'i64) else: mkBitVec[64]((1'i64 shl (len * 8)) - 1)

proc normSlot*(v: SymVal; ty: IRType): SymVal =
  ## An Int-promoted slot (`svInt`: a literal, a `.len`) of the fixed-width
  ## int type `ty` as the bit-vector of its width, the representation the
  ## bit moves work in; every other slot as it is.
  if ty.kind != itInt: return v
  # a literal reaches a narrow field as the 64-bit bit-vector it was written
  # in: its low `ty.width` bits are the value
  let wide = case v.kind
             of svBV64: 64
             of svBV32: 32
             of svBV16: 16
             else: 0
  if wide > ty.width and ty.width in [8, 16, 32]:
    return truncBV(v, ty.width, ty.signed)
  if v.kind != svInt: return v
  result = svIntToBV(v, case ty.width
                        of 8: svBV8
                        of 16: svBV16
                        of 32: svBV32
                        else: svBV64)
  result.signed = ty.signed

proc unionImageGate*(ty: IRType): Option[vl.VariantLayout] =
  ## The layout a value variant of `ty` carries its byte image under: only a
  ## `--fieldChecks:off` c-backend build, and only a layout derived.
  if ty == nil or ty.kind != itVariant: return
  if coField in buildSemantics.checks or buildSemantics.backend != beC: return
  # A type with lifetime hooks (`not supportsCopyMem`): the discriminator
  # write runs the old arm's destructor/reset, so the old bytes are not the
  # new arm's slots. No image; the write is the `dwmHavoc` model.
  if ty.vNoCopyMem: return
  let lay = vl.variantLayout(ty)
  if lay.ok: some(lay) else: none(vl.VariantLayout)

proc activeMemberTracked*(ty: IRType): bool =
  ## cpp `--fieldChecks:off`: a value variant carries the arm last written.
  ty != nil and ty.kind == itVariant and coField notin buildSemantics.checks and
    buildSemantics.backend == beCpp

proc unionCellCount*(lay: vl.VariantLayout): int =
  (lay.size - lay.unionOff + 7) div 8

proc zeroImage*(lay: vl.VariantLayout): seq[Z3BitVec[64]] =
  ## Every byte the zero of the object's initialisation: data zero, no byte
  ## indeterminate.
  for _ in 0 ..< 2 * unionCellCount(lay): result.add mkBitVec[64](0'i64)

proc activeOf*(disc: SymVal): ref SymVal =
  result = new SymVal
  result[] = disc

proc placeBits*(v: SymVal; p: vl.Place): Option[Z3BitVec[64]] =
  ## The bytes a `p`-typed field value occupies, as the low `p.size` bytes
  ## of a cell: an int or enum by its cell, a bool as 0/1, a float as its
  ## IEEE bits (what C stores).
  case p.ty.kind
  of itFloat64:
    if v.kind == svFloat64: some(toIeeeBv(v.fp64)) else: none(Z3BitVec[64])
  of itFloat32:
    if v.kind == svFloat32: some(zeroExtend(toIeeeBv(v.fp32), 32))
    else: none(Z3BitVec[64])
  else:
    let c = cellOf(normSlot(v, p.ty), p.ty)
    if c.isNone: return
    some(c.get and byteMask(p.size))

proc imgWrite*(img: seq[Z3BitVec[64]]; off, size: int;
              bits: Z3BitVec[64]): seq[Z3BitVec[64]] =
  ## `img` with the low `size` bytes of `bits` at union byte `off`, those
  ## bytes no longer indeterminate.
  result = img
  let half = img.len div 2
  var at = off
  while at < off + size:
    let cell = at div 8
    let inCell = at mod 8
    let n = min(8 - inCell, off + size - at)
    let m = byteMask(n) shl ofByteShift(inCell)
    let ins = ((bits.lshr ofByteShift(at - off)) shl ofByteShift(inCell)) and m
    result[cell] = (result[cell] and (not m)) or ins
    result[half + cell] = result[half + cell] and (not m)
    at += n

proc armImage*(lay: vl.VariantLayout; tag: int; slots: seq[SymVal];
              fill: seq[Z3BitVec[64]]): Option[seq[Z3BitVec[64]]] =
  ## The image of a variant whose active arm is `tag` with `slots`: `fill`
  ## (the bytes no field of the arm covers) with each field's bytes at its
  ## place. `none` when a slot's bytes are not derived.
  if not lay.arms.hasKey(tag) or lay.arms[tag].len != slots.len: return
  var img = fill
  for j, p in lay.arms[tag]:
    let b = placeBits(slots[j], p)
    if b.isNone: return
    img = imgWrite(img, p.off - lay.unionOff, p.size, b.get)
  some(img)

proc variantImage(lay: vl.VariantLayout; disc: SymVal;
                  arms: OrderedTable[int, seq[SymVal]];
                  fill: seq[Z3BitVec[64]]): seq[Z3BitVec[64]] =
  ## The image of a variant whose discriminator is `disc`: the arm it selects
  ## over `fill`. Empty (no image: an out-of-arm read declines) when an arm's
  ## is not derived.
  result = fill
  for tag, slots in arms:
    if tag < 0: continue
    let ai = armImage(lay, tag, slots, fill)
    if ai.isNone: return @[]
    let sel = variantDiscEq(disc, int64(tag))
    for i in 0 ..< result.len:
      result[i] = iteFolded(sel, ai.get[i], result[i])

proc bsRawNum*(ctx: Z3Context; n: int; v: string): Z3AnyAst =
  ## The `n`-bit numeral `v` (decimal).
  let srt = ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(n))
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, v.cstring, srt))

proc bsZero*(ctx: Z3Context; n: int): Z3AnyAst = bsRawNum(ctx, n, "0")

# R2 (walker v90) — zero-default result binding.
#
# `defaultZero` (below) was Phase 14 cycle A5's (ADR-0003 D5) recursive
# type-driven zero-init, originally scoped LOCAL to the `isVariantReassign`
# walker arm (a reassigned variant arm's fields, Nim runtime semantics on
# discriminator reassignment). R2 hoists it here, to module scope, so the
# `isCall` arm's NEW zero-default binding (below, S3) can call the SAME
# constructor instead of inventing a parallel one — `isVariantReassign`'s own
# call site is otherwise unchanged. Every existing arm's behavior is
# unchanged EXCEPT `itSeq`: see that arm's own note.
func variantZeroTotal(t: IRType): bool
  ## RFC-0005 S8n fwd-decl (defined beside `defaultZeroTotal`, below).

func multiVariantZeroTotal(t: IRType): bool
  ## RFC-0005 S8p fwd-decl (defined beside `defaultZeroTotal`, below).

func containerZeroBacked(t: IRType): bool
  ## RFC-0005 S8u fwd-decl (defined beside `defaultZeroTotal`, below).

proc defaultZero*(t: IRType, baseName: string): SymVal =
  ## Recursive type-driven zero-init — Nim's `default(T)` value, expressed as
  ## a Z3 constant (never a fresh symbolic variable: the zero value is fully
  ## known, so no `pcOut`/path-condition threading is needed the way
  ## `allocateSym` needs for a genuinely free symbol). Inherits `allocateSym`'s
  ## scope for containers — Table with non-string keys and HashSet with
  ## non-int64 elements still raise (RFC §A5 sub-deferral; RFC-0005 S8u
  ## builds the empty `Table[string, int]` / `HashSet[int]`, and the zero of
  ## a `distinct` (its base's) and of a `ref`/`ptr` (`nil`); a caller
  ## reaching a raising shape must classified-decline, never bind a wrong
  ## value), as does a
  ## variant (RFC-0005 S8n) or multi-variant (S8p) whose ordinal-0
  ## discriminator is not a legal tag (an explicit arm's, or one an `else`
  ## arm covers). `itFloat*` returns 0.0 since
  ## RFC-0005 S8f (walker 154).
  ## `defaultZeroTotal` (below) says, without calling it, whether this
  ## returns.
  case t.kind
  of itUninterp:
    raise newException(ValueError, "defaultZero(itUninterp): lands with cluster E")  # [raise-audited: category-c: documented out-of-scope invariant (defaultZero's own doc: itUninterp zero-init never wired, out of A5/R2 scope)]
  of itFloat32: SymVal(kind: svFloat32, fp32: mkFloat32(0'f32))
  of itFloat64: SymVal(kind: svFloat64, fp64: mkFloat64(0.0))
  of itBool: SymVal(kind: svBool, bo: mkBool(false))
  of itBitSet:   ## RFC-0005 S8bq: `{}`
    bitSetSV(bsZero(requireCurrentContext(), bitSetDomain(t.bsElemTy).size),
             t.bsElemTy)
  of itInt:
    case t.width
    of 8:  liftBV(mkBitVec[8](0),  t.signed)
    of 16: liftBV(mkBitVec[16](0), t.signed)
    of 32: liftBV(mkBitVec[32](0), t.signed)
    of 64: liftBV(mkBitVec[64](0), t.signed)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]
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
    if t.seqUnsupportedFieldReason.len > 0 or not isBackedSeqElemTy(t.seqElemTy):
      # R2 (walker v90): mirror `allocateSym`'s `itSeq` placeholder arm
      # EXACTLY, rather than calling `allocateSeqDataRaw` (which raises
      # `SymexNestedSeqUnsupportedError` unconditionally for an element type
      # it cannot back). A zero-default seq of an unbacked element type must
      # degrade the SAME way a genuine allocation of that type would —
      # `isUnsupportedFieldPlaceholder: true`, `seqLen` forced `== 0` — never
      # crash the whole walk merely because some untouched sibling path
      # needed this type's zero value. `retBindEq`'s `svSeq` arm already
      # treats an `isUnsupportedFieldPlaceholder` value on EITHER side as a
      # sound no-op bind, so this composes correctly wherever `defaultZero`
      # is reached (top-level `itSeq` return, or nested inside a zero-bound
      # tuple/variant field).
      let lenSym = mkInt(0)
      let dataRaw = toAnyAst(mkArrayVar[Z3Int, Z3Bool](baseName & ".data"))
      SymVal(kind: svSeq, seqLen: lenSym, seqDataRaw: dataRaw,
             seqElemTy: t.seqElemTy, isUnsupportedFieldPlaceholder: true,
             # Round-6 re-review (item 2, walker v114): this arm's own
             # comment claims to mirror `allocateSym`'s `itSeq` placeholder
             # arm EXACTLY, but omitted these two fields -- `retBindEq`'s
             # `svSeq` arm and `placeholderReadDeclineKind`/
             # `placeholderReadDeclineMsg` (the read chokepoint) both key off
             # `seqUnsupportedFieldReason`/`seqUnsupportedFieldKind` to
             # report the ORIGINAL decline reason/kind instead of the
             # generic "nested seq element type is not supported" claim
             # (N47-followup, walker v110). A zero-defaulted placeholder
             # left these empty/default, so a downstream read through a
             # `defaultZero`-built placeholder would misreport a bare-value
             # decline even when `t` carries a real declared-field/
             # operation-level reason. Latent only (no test exercised a read
             # through a `defaultZero`-sourced `itSeq` placeholder yet) --
             # closed to keep the mirror true, matching `allocateSym`'s arm
             # field-for-field.
             seqUnsupportedFieldReason: t.seqUnsupportedFieldReason,
             seqUnsupportedFieldKind: t.seqUnsupportedFieldKind)
    else:
      # Empty seq: len pinned to 0; the data array is allocated
      # so the SymVal shape is well-formed, but never read past
      # len. Mirrors Nim's `default(seq[T]) == @[]`.
      # RFC-0005 S8bc: one array per leaf of a tree element; S8ba: of the
      # element's cell type (`seqCellTy`, normalised by both helpers).
      mkSeqSV(mkInt(0), allocateSeqArrs(t.seqElemTy, baseName & ".data"),
              t.seqElemTy)
  of itSet, itTable:
    # RFC-0005 S8u: the empty container, for the shapes `allocateSym` backs
    # (`Table[string, int]`, `HashSet[int]`): no key present (a constant
    # `false` array) and size 0. The data array is a constant too; it is
    # read only at a present key. `size >= |present keys|` (`containerCard`)
    # holds of it trivially, so it is not registered. Any other shape keeps
    # the A5 sub-deferral raise (`containerZeroBacked` is false for it, so a
    # `defaultZeroTotal` caller never reaches it).
    if containerZeroBacked(t):
      if t.kind == itTable:
        return emptyTable(t.tabKeyTy, t.tabValTy)   # RFC-0005 S8ar
      let members = mkConstArray[Z3BitVec[64], Z3Bool](mkBool(false))
      return SymVal(kind: svSet, setMembersRaw: toAnyAst(members),
                    setSize: mkInt(0), setElemTy: t.setElemTy)
    raise newException(ValueError,  # [raise-audited: category-c: documented out-of-scope invariant (RFC A5 sub-deferral, container zero-init of a shape allocateSym does not back) -- every defaultZero call site now wraps in try/except or checks defaultZeroTotal (N46, S8u)]
      "A5 zero-init: container field " & $t &
      " not yet supported (RFC §A5 sub-deferral)")
  of itVariant, itMultiVariant:
    # RFC-0005 S8n: Nim zero-initialises a variant object's memory, so its
    # discriminator holds ordinal 0 and every field its own zero (the fields
    # of the other arms are unreachable while the discriminator says ordinal
    # 0, so zeroing them too binds nothing observable). Built for a
    # single-case variant where that is a legal value of the type
    # (`variantZeroTotal`); a caller checks `defaultZeroTotal` first or
    # catches the raise below. RFC-0005 S8p: a multi-variant likewise, each
    # axis's discriminator ordinal 0 (`multiVariantZeroTotal`).
    if t.kind == itMultiVariant and multiVariantZeroTotal(t):
      var plainFields: seq[SymVal]
      for i, ft in t.mvPlainFieldTypes:
        plainFields.add defaultZero(ft, baseName & "." & t.mvPlainFieldNames[i])
      var axes: seq[VariantAxisSym]
      for ax in t.mvAxes:
        let discBoxed = new(SymVal)
        discBoxed[] = defaultZero(ax.discTy, baseName & "." & ax.discName)
        var armFields = initOrderedTable[int, seq[SymVal]]()
        var armNames  = initOrderedTable[int, seq[string]]()
        for arm in ax.arms:
          var fields: seq[SymVal]
          for j, ft in arm.fieldTypes:
            fields.add defaultZero(ft, baseName & "." & ax.discName & ".@" &
                                       arm.tagName & "." & arm.fieldNames[j])
          armFields[arm.tagOrdinal] = fields
          armNames[arm.tagOrdinal]  = arm.fieldNames
        axes.add VariantAxisSym(discName: ax.discName, disc: discBoxed,
                                armFields: armFields, armFieldNames: armNames)
      return SymVal(kind: svMultiVariant, mvObjectName: t.mvObjectName,
                    mvAxes: axes, mvPlainFields: plainFields,
                    mvPlainFieldNames: t.mvPlainFieldNames)
    if t.kind == itVariant and variantZeroTotal(t):
      let discBoxed = new(SymVal)
      discBoxed[] = defaultZero(t.vDiscTy, baseName & "." & t.vDiscName)
      var plainFields: seq[SymVal]
      for i, ft in t.vPlainFieldTypes:
        plainFields.add defaultZero(ft, baseName & "." & t.vPlainFieldNames[i])
      var armFields = initOrderedTable[int, seq[SymVal]]()
      var armNames  = initOrderedTable[int, seq[string]]()
      for arm in t.vArms:
        var fields: seq[SymVal]
        for j, ft in arm.fieldTypes:
          fields.add defaultZero(ft, baseName & ".@" & arm.tagName & "." &
                                     arm.fieldNames[j])
        armFields[arm.tagOrdinal] = fields
        armNames[arm.tagOrdinal]  = arm.fieldNames
      var sv = SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: t.vDiscName,
                      vObjectName: t.vObjectName,
                      vArmFields: armFields, vArmFieldNames: armNames,
                      vPlainFields: plainFields,
                      vPlainFieldNames: t.vPlainFieldNames)
      let gate = unionImageGate(t)   # RFC-0016 PRC-07 slice B: all zero
      if gate.isSome: sv.vImage = zeroImage(gate.get)
      if activeMemberTracked(t): sv.vActive = activeOf(discBoxed[])
      return sv
    raise newException(ValueError,  # [raise-audited: category-c: documented out-of-scope invariant (a variant or multi-variant whose zero discriminator is not a legal tag has no default) -- every defaultZero call site now wraps in try/except or checks defaultZeroTotal (N46, S8n)]
      "A5 zero-init: variant " & $t & " has no legal zero value")
  of itDistinct:
    # RFC-0005 S8u: Nim's `default(D)` for `D = distinct B` is B's zero. A
    # distinct value is its base value in the IR (the parser's `D(x)` is
    # the identity, S8p), and `retBindEq` binds a distinct through its
    # ejected base, so the base's zero is the whole value. Before S8u this
    # raised (Phase 15 G4 sub-deferral): an untouched distinct result was
    # `feUnsupportedOpHavoc`.
    defaultZero(t.distinctBase, baseName)
  of itRef, itPtr:
    # RFC-0005 S8u: a `ref`/`ptr` is zero-initialised to `nil`: the per-sort
    # `nilConst` Phase 15 R5's `iekNil` lowers to (an untouched `ref`
    # result). Before S8u this raised (the R1a stub).
    let ctx = requireCurrentContext()
    let isPtr = t.kind == itPtr
    let pointee = if isPtr: t.ptrPointeeTy else: t.refPointeeTy
    discard allocRefSort(ctx, pointee)        ## ensure the sort + nilConst exist
    let nilAst = currentNilConsts[refPointeeTypeId(pointee)]
    if isPtr:
      SymVal(kind: svPtr, ptrAst: nilAst, ptrFamily: true, ptrPointee: pointee)
    else:
      SymVal(kind: svRef, refAst: nilAst, refPointee: pointee)

func defaultZeroTotal*(t: IRType): bool

proc tabKeySortHold(keyTy: IRType): Z3AnyAst =
  ## RFC-0005 S8at. A live term of the key sort a table of `keyTy` is keyed
  ## by (a string, or a 64-bit cell): its sort is read off it, and it keeps
  ## that sort alive across the array-sort construction.
  if keyTy.kind == itString: toAnyAst(mkString(""))
  else: toAnyAst(mkBitVec[64](0'i64))

proc tabTreeDataVars(name: string; keyTy, valTy: IRType): seq[Z3AnyAst] =
  ## RFC-0005 S8at. The free data arrays of a table holding container
  ## values, one per leaf of the value type (`heapLeafSuffixes`), each from
  ## the key sort to the leaf's sort. The sorts are runtime (a seq leaf is
  ## itself an array), so the arrays are built raw, as `mkHeapArrayVar`'s;
  ## the prototype value and the key term hold both sorts alive across
  ## `Z3_mk_array_sort`. Leaf 0 is named `name`, leaf i `name.@v<i>`.
  let ctx = requireCurrentContext()
  let proto = defaultZero(valTy, "__tabValSort")
  let keyHold = tabKeySortHold(keyTy)
  let keySort = ctx.checkErr Z3_get_sort(ctx.raw, keyHold.raw)
  let leaves = svLeafAsts(proto, valTy)
  for i, leaf in leaves:
    let valSort = ctx.checkErr Z3_get_sort(ctx.raw, leaf)
    let arrSort = ctx.checkErr Z3_mk_array_sort(ctx.raw, keySort, valSort)
    let nm = if i == 0: name else: name & ".@v" & $i
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, nm.cstring)
    result.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc tabTreeDataZero(keyTy, valTy: IRType): seq[Z3AnyAst] =
  ## RFC-0005 S8at. The data arrays of an empty table holding container
  ## values: each leaf of the value type's zero, at every key (read only at
  ## a present key).
  let ctx = requireCurrentContext()
  let proto = defaultZero(valTy, "__tabValZero")
  let keyHold = tabKeySortHold(keyTy)
  let keySort = ctx.checkErr Z3_get_sort(ctx.raw, keyHold.raw)
  for leaf in svLeafAsts(proto, valTy):
    result.add wrap[Z3AnyAst](ctx,
      ctx.checkErr Z3_mk_const_array(ctx.raw, keySort, leaf))

func containerZeroBacked(t: IRType): bool =
  ## RFC-0005 S8u. A `Table` / `HashSet` shape whose empty value `defaultZero`
  ## builds: the shapes `allocateSym` backs (`Table[string, int]`,
  ## `HashSet[int]`, 64-bit).
  case t.kind
  of itTable: isBackedTableTy(t.tabKeyTy, t.tabValTy)   # RFC-0005 S8z
  of itSet:   isBackedSetElemTy(t.setElemTy)            # RFC-0005 S8z
  else: false

func variantZeroTotal(t: IRType): bool =
  ## RFC-0005 S8n: true when the all-zero memory of variant `t` is a value
  ## of the type -- the discriminator's type holds 0 and 0 is a legal tag
  ## (an explicit `of` ordinal, or covered by an `else:` arm, which
  ## `discriminatorDomain` folds into `ordSet`; an empty `ordSet` means the
  ## discriminator's own range is the domain) -- and every field has a zero
  ## value. An enum whose first ordinal is not 0 fails the first test.
  doAssert t.kind == itVariant
  if not defaultZeroTotal(t.vDiscTy): return false
  let (_, _, ordSet) = discriminatorDomain(t)
  if ordSet.len > 0 and 0 notin ordSet: return false
  for ft in t.vPlainFieldTypes:
    if not defaultZeroTotal(ft): return false
  for arm in t.vArms:
    for ft in arm.fieldTypes:
      if not defaultZeroTotal(ft): return false
  true

func multiVariantZeroTotal(t: IRType): bool =
  ## RFC-0005 S8p: `variantZeroTotal` per axis. Every axis's discriminator
  ## type holds 0 and 0 is a legal tag of that axis, and every field (plain,
  ## and of every arm) has a zero value. RFC-0005 S8s: "a legal tag" is
  ## `axisDiscriminatorDomain`'s, so an ordinal 0 an `else` arm covers
  ## counts, as it does for a single `case` (S8p required an explicit
  ## ordinal-0 arm, the only tags `allocateSym`'s multi-variant arm then
  ## admitted).
  doAssert t.kind == itMultiVariant
  for ax in t.mvAxes:
    if not defaultZeroTotal(ax.discTy): return false
    let (_, _, ordSet) = axisDiscriminatorDomain(ax)
    if ordSet.len > 0 and 0 notin ordSet: return false
    for arm in ax.arms:
      for ft in arm.fieldTypes:
        if not defaultZeroTotal(ft): return false
  for ft in t.mvPlainFieldTypes:
    if not defaultZeroTotal(ft): return false
  true

func defaultZeroTotal*(t: IRType): bool =
  ## RFC-0005 S8f: true exactly when `defaultZero(t)` returns Nim's
  ## `default(T)` without raising, so a caller with no `try` in scope (the
  ## walker bans non-top-level `try`) can pick `defaultZero` or a classified
  ## decline BEFORE the call. An `itInt` whose `range` excludes 0 is not
  ## total: `defaultZero` would bind 0, a value the type cannot hold.
  case t.kind
  of itBool, itString, itFloat32, itFloat64: true
  of itInt:
    # RFC-0005 S8z: an ENUM's zero is ordinal 0 even when no member has it
    # (`enum a = 1, b = 2`): Nim zero-fills the memory (probed: an untouched
    # result field, result and local all read `ord == 0`). It was not total,
    # so the untouched result became a free `retSym` constrained to the
    # enum's ordinals -- excluding the value Nim returns (a false `sxUnsat`
    # for a label reading it). A `range` excluding 0 stays non-total: Nim
    # rejects its implicit zero at compile time ("requires explicit
    # initialization"), and a variant discriminator must start at 0.
    t.width in {8, 16, 32, 64} and
      (not t.hasRange or (t.rangeLo <= 0 and 0 <= t.rangeHi) or
       t.enumName.len > 0)
  of itTuple:
    for ft in t.fields:
      if not defaultZeroTotal(ft): return false
    true
  of itArray: defaultZeroTotal(t.elemTy)
  of itSeq: true
  of itVariant: variantZeroTotal(t)   # RFC-0005 S8n
  of itMultiVariant: multiVariantZeroTotal(t)   # RFC-0005 S8p
  of itTable, itSet: containerZeroBacked(t)     # RFC-0005 S8u
  of itBitSet: true                             # RFC-0005 S8bq: `{}`
  of itDistinct: defaultZeroTotal(t.distinctBase)   # RFC-0005 S8u
  of itRef, itPtr: true                         # RFC-0005 S8u: nil
  else: false

proc seqElemAt*(seqSV: SymVal, idx: Z3Int): SymVal =
  ## Read element `idx` of a `svSeq` as a SymVal (dispatch on element type).
  ## Mirrors the `isIndex`/seq walker arm. Caller guarantees `idx` in bounds.
  doAssert seqSV.kind == svSeq, "seqElemAt: not an svSeq"
  if isTreeSeqElemTy(seqSV.seqElemTy):
    # RFC-0005 S8bc: a tree element, from the select of every data array at
    # `idx` (each wrapped at once), rebuilt over a prototype of the type.
    let ctx = requireCurrentContext()
    let arrs = seqArrs(seqSV)
    if arrs.len != heapLeafSuffixes(seqSV.seqElemTy).len:
      return degradeAlloc(seqSV.seqElemTy, weInternalWalkerFault,
        "seqElemAt: a seq of " & $seqSV.seqElemTy & " holds " & $arrs.len &
        " data arrays (weInternalWalkerFault)", "__seqElemAtLayout")
    var leaves: seq[Z3AnyAst]
    for a in arrs:
      leaves.add wrap[Z3AnyAst](ctx, checkedSelect(ctx, a.raw, idx.raw))
    return svWithLeaves(ctx, seqElemProto(seqSV.seqElemTy), leaves,
                        seqSV.seqElemTy)
  case seqSV.seqElemTy.kind
  of itInt:
    case seqSV.seqElemTy.width
    of 8:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[8]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 16:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[16]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 32:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[32]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    of 64:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[64]]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
      liftBV(select(t, idx), seqSV.seqElemTy.signed)
    else:
      raise newException(ValueError, "seqElemAt: unsupported int width " & $seqSV.seqElemTy.width)  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]
  of itBool:
    let t = wrap[Z3Array[Z3Int, Z3Bool]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
    ofBool(select(t, idx))
  of itFloat32:
    let t = wrap[Z3Array[Z3Int, Z3Float32]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
    SymVal(kind: svFloat32, fp32: select(t, idx))
  of itFloat64:
    let t = wrap[Z3Array[Z3Int, Z3Float64]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
    SymVal(kind: svFloat64, fp64: select(t, idx))
  of itString:
    let t = wrap[Z3Array[Z3Int, Z3String]](seqSV.seqDataRaw.ctx, seqSV.seqDataRaw.raw) # [placeholder-audited]
    SymVal(kind: svString, str: select(t, idx))
  else:
    # N46 (round-6 re-review, ADR-0023/SND-3 class widening): was a raw
    # `raise newException`. This is a genuine asymmetry bug, not a
    # by-design gap: `isBackedSeqElemTy` (the guard gating every
    # `seqElemAt` caller below) considers `itRef`/`itPtr` BACKED — matching
    # `allocateSeqDataRaw`'s and `storeSeqElem`'s own `itRef`/`itPtr` arms —
    # but `seqElemAt` never got the matching read-side implementation, so
    # `mySeqOfRefNodes.map(fn)`/`.filter(pred)`/`.foldl(...)` inside a loop
    # reaches this `else` unguarded even though the guard says the element
    # type IS supported. In-band degrade (rather than a raw raise) while
    # this read-side gap is closed properly in a follow-up: a fresh
    # symbolic placeholder of the SAME element type keeps evaluation
    # structurally sound (`weInternalWalkerFault` — this is the walker's
    # own implementation gap, not an unsupported user construct).
    #
    # Fix-slice item 9 (round-6 re-review): this site's name argument was a
    # BARE literal (`"__seqElemAtUnsupported"`, not `freshDegradeName(...)`)
    # — the SAME missed-uniquification-sweep bug class items 3/4 fixed
    # elsewhere, discovered here while building item 9's pairing audit. Two
    # DIFFERENT unbacked seq elements read within one run (or one revisited
    # via `.map`/`.filter`/`.foldl`) would have collided on `(name, sort)`.
    # Now routed through `degradeAlloc`, closing both the missing
    # uniquification AND the pairing gap in one move.
    degradeAlloc(seqSV.seqElemTy, weInternalWalkerFault,
      "seqElemAt: unsupported elem kind " & $seqSV.seqElemTy.kind &
      " (weInternalWalkerFault)", "__seqElemAtUnsupported")

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(allocEnumZeroLegal, distinctBijectivityHints,
    distinctSortNames, containerCard, intHeapIsInt, heapKeyShapes,
    currentBorrowReboxCounter, intOfBV, globalEntryFacts, storeDeclKind,
    selectDeclKind, constArrayDeclKind, iteDeclKind, intCellFactSeen,
    heapChainKinds)

registerThreadStateRelease(releaseThreadState)
