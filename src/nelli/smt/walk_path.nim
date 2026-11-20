## RFC-0016 INT-34 B3. Making and forking paths: a leaf cut out of
## `runtime.nim`.
##
## The procedures of `runtime.nim`'s region R0 (`scripts/int34-deps.py`) that
## read none of its threadvars live here, in the order they had there:
##
##   * the fork constructors: `forkPathTaintPrimitive` and its three
##     sanctioned wrappers (`forkPath`, `forkPathTainted`, `forkPathMerged`),
##     `deepCopyHeapState`, `atIteration` and `taintInPlace`, with the H1 test
##     hooks that drive them;
##   * the literal-shaping protos (`bvConst`, `intLitProto`, `envLitProto`,
##     `probeProto`, ...);
##   * the container-cell readers (`cellValue`, `tabValAt`, `tabMoreEq`) and
##     the cardinality facts built from them (`containerCardConds`);
##   * the readers of the live `WalkCtx` through `currentWalkCtxPtr`
##     (`isFollowConcreteWalk`, `programGlobal`, `unwrittenResultZero`, ...);
##   * the leaf-split seq helpers (`constSeqArrs`, `seqElemFits`) and
##     `stampHeapSteps`, `svWithRaw`, the C1 closure PoC.
##
## R0's threadvars stay in `runtime.nim`, with the procedures that read them
## (`checkedNow`, `seedCallerHeapThreadvars`, `pendingEnvWriteIx`, ...). This
## module owns no threadvar, so it has no reset and no thread-state release.
##
## `noteUbAtFork`. The fork templates and `taintInPlace` reach it only on the
## rare path, when a degrade token puts an undefined behaviour on a path that
## did not have it; its body reads the run's target, which `runtime.nim` owns
## (region R4). It is called through `lowerHooks.noteUbAtFork`, and the empty
## test (`newUb != {}`) stays inline, so the common fork makes no call.
##
## The templates bind their symbols here: `deepCopyHeapState`, `sameHeapTerm`
## and `lowerHooks` resolve to this module's and `walk_state`'s wherever a
## fork is expanded. `Path`'s fields are `walk_types`' exported fields.
##
## Every routine is exported so `runtime.nim` can call it; `runtime.nim`
## re-exports exactly the names it exported before (`export walk_path.<name>`),
## never the module.
##
## Imports only std, `z3` and leaves; the census
## (`tests/tsymex_0016_d3_include_census.nim`) pins the list.
import std/tables
import std/options
import z3
import ./types
import ./symval
import ./walk_state
import ./walk_types
import ./heap_model
import ./z3check

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

proc deepCopyHeapState*(src: Path):
    tuple[heaps: Table[string, Z3AnyAst],
          allocCounters: Table[string, int],
          liveRefs: Table[string, seq[Z3AnyAst]]] =
  result.heaps = src.heaps              ## Table assignment = value copy in Nim
  result.allocCounters = src.allocCounters
  # Phase 15 R2: per-path live fresh-ref list. `Table`/`seq` assignment is a
  # value copy in Nim, so the child gets an INDEPENDENT snapshot — the fork
  # isolation that gives disjoint-path counter restart for free.
  result.liveRefs = src.liveRefs

func sameHeapTerm*(a, b: HeapTerm): bool =
  ## RFC-0005 S8ca. The same array term (`HeapTerm`).
  let x = cast[pointer](a.ast.raw)
  let y = cast[pointer](b.ast.raw)
  if x == nil or y == nil: x == nil and y == nil and a.input == b.input
  else: x == y

template forkPathTaintPrimitive*(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                                taintExpr: Taint;
                                undefExpr: set[UbKind];
                                viaOnlyExpr: set[UbKind]): Path =
  ## Phase 15 H1 / R3 hardening / RFC-0005 S1: construct a CHILD `Path` from
  ## `parent`, deep-copying the logical-heap state (heaps / heapDepth /
  ## allocCounters) so the fork is isolated — the single enforcement point for
  ## the ADR-0010 fork deep-copy contract. (The fresh ROOT path in `runSymex`
  ## does NOT use this: it has no parent and correctly gets empty-default
  ## heap fields.)
  ##
  ## PRIMITIVE — NOT FOR SITES. `taintExpr` is a bare `Taint`, so a call here
  ## can silently pass `{}` and drop the parent's taint. Only the three
  ## sanctioned wrappers immediately below call it, and each makes "drop the
  ## taint" unspellable: `forkPath` (propagate), `forkPathTainted` (join a
  ## `Degrade` token), `forkPathMerged` (the isReturn return-merge union).
  ## The writer grep-pin (`tests/tsymex_rfc0005_s1_lattice.nim`) fails if
  ## any other routine calls it.
  let hs = deepCopyHeapState(parent)
  Path(pc: pcExpr, env: envExpr, taint: taintExpr,
       undefined: undefExpr,                             ## RFC-0016 W1-d3
       undefinedViaOnly: viaOnlyExpr,                    ## RFC-0016 W3-z R7
       defectSurvivorPc: parent.defectSurvivorPc,        ## Phase 16 ADR-0012
       heaps: hs.heaps, heapDepth: parent.heapDepth,
       allocCounters: hs.allocCounters,
       liveRefs: hs.liveRefs,                            ## Phase 15 R2
       freshnessAssertCount: parent.freshnessAssertCount,  ## Phase 15 R2
       nilDeref: parent.nilDeref,                        ## RFC-0005 S8k
       addrOwners: parent.addrOwners,                    ## RFC-0005 S8ax
       elemCells: parent.elemCells,                      ## RFC-0005 S8be
       ptrStores: parent.ptrStores,                      ## RFC-0005 S8bz
       loopIters: parent.loopIters,                      ## RFC-0005 S8y
       viewMarks: parent.viewMarks,                      ## RFC-0005 S8ca
       inPlaceSteps: parent.inPlaceSteps)                ## RFC-0005 S8ca

template forkPath*(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env): Path =
  ## R3 hardening: the ONLY spelling ordinary fork sites use to derive a
  ## CHILD `Path` from `parent`. Implicitly PROPAGATES `parent.taint`
  ## (RFC-0005's per-path soundness channels, formerly SND-1's `uncertain`)
  ## to the child — there is no taint parameter to silently drop or forget.
  ## Use `forkPathTainted` at sites that deliberately INTRODUCE taint.
  forkPathTaintPrimitive(parent, pcExpr, envExpr, parent.taint,
                          parent.undefined, parent.undefinedViaOnly)

template forkPathTainted*(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                         d: Degrade): Path =
  ## R3 hardening / RFC-0005 S1: the explicit-INTRODUCE counterpart to
  ## `forkPath`. The child's taint is the JOIN `parent.taint + d.path` —
  ## never a replacement — where `d` is the token `degrade(w, kind, msg)`
  ## returned when it recorded the site's classified error. A site cannot
  ## taint a path without having recorded a kind (the token is the proof),
  ## and one token serves every survivor of a one-error-many-survivors site
  ## (`let d = w.degrade(…)` once, then fork per survivor).
  block:
    # `d` is bound once: a template argument is substituted where it is named,
    # and `asDegrade(takePending())` drains what it reads.
    let tok = d
    let child = forkPathTaintPrimitive(parent, pcExpr, envExpr,
                                       parent.taint + tok.path,
                                       parent.undefined + tok.ub,
                                       parent.undefinedViaOnly - tok.ub)
    # INT-34 B1: the empty test is inline, so the common fork (no new kind)
    # makes no call; `noteUbAtFork` is reached only when a kind arrives.
    let newUb = tok.ub - parent.undefined
    if newUb != {}:
      lowerHooks.noteUbAtFork(parent.taint, cast[pointer](child), newUb)
    child

template forkPathMerged*(callee: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                        caller: Path): Path =
  ## RFC-0005 S1: the isReturn return-MERGE fork (was the one site that
  ## called the internal primitive with a computed `p.uncertain or
  ## cp.uncertain`). Forks from the returned CALLEE path `callee` (so its
  ## exit heap state rides out), with taint `callee.taint + caller.taint`:
  ## the post-call path is tainted by anything either side picked up. Union
  ## replaces OR with no special case (§2.1). RFC-0005 S8k: `nilDeref` is
  ## likewise either side's -- a closure body's descent starts from a fresh
  ## root, so a caller that already passed the nil edge (a caught
  ## `NilAccessDefect`) would otherwise lose the mark on the body's raise.
  block:
    let merged = forkPathTaintPrimitive(callee, pcExpr, envExpr,
                                        callee.taint + caller.taint,
                                        callee.undefined + caller.undefined,
                                        (callee.undefinedViaOnly +
                                         caller.undefinedViaOnly) -
                                        (callee.undefined -
                                         callee.undefinedViaOnly) -
                                        (caller.undefined -
                                         caller.undefinedViaOnly))
    merged.nilDeref = callee.nilDeref or caller.nilDeref
    # RFC-0005 S8y: a closure body's descent starts from a fresh root, so
    # the caller's loop depths are joined back in (the deeper of the two).
    for (loop, n) in caller.loopIters:
      var seen = false
      for e in merged.loopIters.mitems:
        if e.loop == loop:
          e.iters = max(e.iters, n)
          seen = true
      if not seen: merged.loopIters.add (loop: loop, iters: n)
    # RFC-0005 S8ax: likewise the caller's address cells.
    for o in caller.addrOwners:
      var seen = false
      for e in merged.addrOwners:
        if cast[pointer](e.refAst.raw) == cast[pointer](o.refAst.raw):
          seen = true
      if not seen: merged.addrOwners.add o
    # RFC-0005 S8be: and its element cells.
    for o in caller.elemCells:
      var seen = false
      for e in merged.elemCells:
        if e.frame == o.frame and
           cast[pointer](e.refAst.raw) == cast[pointer](o.refAst.raw):
          seen = true
      if not seen: merged.elemCells.add o
    # RFC-0005 S8ca: and its views and in-place steps (a closure body's
    # descent starts from a fresh root).
    for o in caller.viewMarks:
      var seen = false
      for e in merged.viewMarks:
        if e.frame == o.frame and e.local == o.local: seen = true
      if not seen: merged.viewMarks.add o
    for o in caller.inPlaceSteps:
      var seen = false
      for e in merged.inPlaceSteps:
        if e.key == o.key and sameHeapTerm(e.before, o.before) and
           sameHeapTerm(e.after, o.after):
          seen = true
      if not seen: merged.inPlaceSteps.add o
    merged

proc atIteration*(p: Path; loop, n: int) =
  ## RFC-0005 S8y. Record on `p` (a child just forked) that its latest
  ## execution of `loop` has entered the body `n` times.
  for e in p.loopIters.mitems:
    if e.loop == loop:
      e.iters = n
      return
  p.loopIters.add (loop: loop, iters: n)

proc taintInPlace*(p: Path; d: Degrade) =
  ## RFC-0005 S1 (§2.2). The MUTATION-shaped sibling of `forkPathTainted`,
  ## for a site that already holds its own freshly-forked child and taints it
  ## after the fact (`runtime_heap.nim`'s `isNew` zero-write, per unmodelled
  ## field). Joins, never replaces. A halted path needs no carrier at all
  ## (its contribution is run-global by construction), so halt sites call
  ## `w.halted(…)` and do not come here.
  let priorTaint = p.taint
  let priorUb = p.undefined
  p.taint = p.taint + d.path
  p.undefined = p.undefined + d.ub     ## RFC-0016 W1-d3
  p.undefinedViaOnly = p.undefinedViaOnly - d.ub   ## RFC-0016 W3-z R7
  let newUb = d.ub - priorUb   ## INT-34 B1: inline empty test, as `forkPathTainted`
  if newUb != {}:   ## RFC-0016 W3-z R1
    lowerHooks.noteUbAtFork(priorTaint, cast[pointer](p), newUb)

# ---- Phase 15 H1: exported test hooks ---------------------------------------
# `Path` is a private `ref object`, so the H1 RED test cannot name it. These two
# hooks let `tests/tsymex_phase15_H1_path_heap_fields.nim` verify the field
# scaffolding and the fork deep-copy contract WITHOUT exporting the walker
# internals (`Path`, `forkPath`, the env machinery) gratuitously. They exist
# solely for that test and have no role in the walker.

proc h1PathHasHeapFields*(): bool =
  ## True iff `Path` carries the three H1 heap-state fields. Compile-time
  ## `compiles` checks on a constructed Path, so the test breaks at compile
  ## time if a field is renamed or removed.
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
  heapPut(parent, "x", astA, hwInput)
  # Fork a child the way a fork site does (identical heap-state deep-copy path).
  let child = forkPath(parent, parent.pc, parent.env)
  # Child must start with an isolated copy of the parent's heap.
  doAssert child.heaps.hasKey("x")
  # Mutate the child; the parent must NOT observe it (value-copy isolation).
  heapPut(child, "x", astB, hwStore)
  result = parent.heaps["x"].raw == astA.raw and
           child.heaps["x"].raw == astB.raw and
           parent.heaps["x"].raw != child.heaps["x"].raw

# Construct a SymVal from an IRType + a constant Nim integer value.
proc bvConst*(ty: IRType, n: int64): SymVal =
  doAssert ty.kind == itInt
  case ty.width
  of 8:  liftBV(mkBitVec[8](n),  ty.signed)
  of 16: liftBV(mkBitVec[16](n), ty.signed)
  of 32: liftBV(mkBitVec[32](n), ty.signed)
  of 64: liftBV(mkBitVec[64](n), ty.signed)
  else:  raise newException(ValueError,  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always constructed as 8/16/32/64)]
                            "bvConst: unsupported width " & $ty.width)

proc discConst*(ty: IRType, n: int64): SymVal =
  ## RFC-0005 S8u. A discriminator pinned to ordinal `n`: `bvConst` for an
  ## enum / int / range discriminator, a Bool constant for a `bool` one
  ## (Phase 15 F9c allocates that as svBool). `bvConst` asserted `itInt`.
  if ty.kind == itBool: ofBool(mkBool(n != 0))
  else: bvConst(ty, n)

proc intLitProto*(ty: IRType): Option[SymVal] =
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

proc seqElemLitProto*(ty: IRType): Option[SymVal] =
  ## N14 (RFC-chapulin-hardening bucket-2): the literal-shaping proto for a
  ## seq ELEMENT-ASSIGN store site (`xs[i] = v`), extending `intLitProto`'s
  ## itInt-only coverage to every OTHER `isBackedSeqElemTy` kind (mirrors
  ## `storeSeqElem`'s own kind set exactly, minus itRef/itPtr — no `ref`/`ptr`
  ## LITERAL syntax exists for `v` to need shaping). Without this, a bare
  ## `iekBoolLit`/`iekFloatLit`/`iekStrLit` RHS still lowers correctly
  ## un-proto'd (each literal kind's own `lower` arm is proto-INDEPENDENT,
  ## unlike `iekIntLit`'s width-ambiguous default) — this exists so a
  ## non-literal symbolic RHS (an `iekVar`/`iekBinop`/... whose OWN lowering
  ## consults `proto` for ambiguous cases, same as any other typed sink)
  ## gets the SAME width/kind steering `iekLet`/`isAssign` already give
  ## every other typed binding site, per `intLitProto`'s own precedent.
  case ty.kind
  of itInt:     intLitProto(ty)
  of itBool:    some(ofBool(mkBool(false)))
  of itFloat32: some(SymVal(kind: svFloat32, fp32: mkFloat32(0'f32)))
  of itFloat64: some(SymVal(kind: svFloat64, fp64: mkFloat64(0.0)))
  of itString:  some(SymVal(kind: svString, str: mkString("")))
  else:         none(SymVal)

proc envLitProto*(env: Env, name: string): Option[SymVal] =
  ## v69 (sello #1): the literal-shaping proto for an ASSIGNMENT site, where
  ## the IR carries no declared type — the assign target's CURRENT SymVal is
  ## the authoritative representation (`x = 5` must materialize 5 at x's
  ## width). Restricted to the kinds `coerceIntLit` can shape.
  if env.hasKey(name) and env[name].kind in {svInt, svBV8, svBV16, svBV32,
                                             svBV64, svFloat32, svFloat64}:
    some(env[name])
  else:
    none(SymVal)

proc seqStrElemConds*(v: SymVal): seq[Z3Bool] =
  ## RFC-0005 S8ar. The well-formedness of a string read out of a backing
  ## store (a `seq[string]` element): it is a string of bytes, the fact
  ## `allocateSym` gives a free `string` and `heapCellWfConds` a string
  ## heap cell. Empty for any other kind.
  if v.kind == svString:
    @[matches(v.str, star(range(mkString("\x00"), mkString("\xff"))))]
  else: @[]

proc inCellDomain*(c: Z3BitVec[64]; ty: IRType): Option[Z3Bool] =
  ## RFC-0005 S8z. `c` is the cell of a value of `ty`; `none` when every
  ## cell is.
  let d = cellDomain(ty)
  if not d.bounded: return none(Z3Bool)
  let sgn = ty.kind == itInt and ty.signed
  # [range-invariant: container-cell-domain -- the bounds are the element
  # type's whole value domain (width, sign, enum ordinals), which the 64-bit
  # cell is wider than; a membership COUNT, not a value's range fact]
  let conds = bvRangeConds(SymVal(kind: svBV64, signed: sgn, bv64: c),  # [range-invariant: container-cell-domain]
                           d.lo, d.hi, sgn)
  if conds.len != 2: return none(Z3Bool)
  some(conds[0] and conds[1])

proc cellValue*(c: Z3BitVec[64]; ty: IRType): SymVal =
  ## RFC-0005 S8z. The value of type `ty` a 64-bit container cell holds: its
  ## low `ty.width` bits (`cellOf`'s inverse on every cell it builds); a
  ## `bool`'s is `cell != 0`.
  if ty.kind == itBool:
    return SymVal(kind: svBool, bo: not (c == mkBitVec[64](0'i64)))
  let whole = SymVal(kind: svBV64, signed: ty.signed, bv64: c)
  if ty.width == 64: whole else: truncBV(whole, ty.width, ty.signed)

proc tabValAt*(ctx: Z3Context; sv: SymVal; keyRaw: RawZ3Ast): SymVal =
  ## RFC-0005 S8ar (was `tabValOf`). The value table `sv` holds at key term
  ## `keyRaw`: the select of each data array, read back as the value type
  ## (`tabValTerms`' inverse).
  ## RFC-0005 S8at: a container value is rebuilt from its leaves' selects
  ## (`svWithLeaves` over its type's zero, whose leaves are all replaced).
  let valTy = sv.tabValTy
  # owned at once (RFC-0016 int6-z): every arm below makes terms, and a raw
  # select result lives only until the next call that makes one
  let sel0 = wrap[Z3AnyAst](ctx, checkedSelect(ctx, sv.tabDataRaw.raw, keyRaw))
  case tabValLeaf(valTy)
  of tvStr: SymVal(kind: svString, str: wrap[Z3String](ctx, sel0.raw))
  of tvF32: SymVal(kind: svFloat32, fp32: wrap[Z3Float32](ctx, sel0.raw))
  of tvF64: SymVal(kind: svFloat64, fp64: wrap[Z3Float64](ctx, sel0.raw))
  of tvCell: cellValue(wrap[Z3BitVec[64]](ctx, sel0.raw), valTy)
  of tvTree:
    var leaves = @[sel0]
    for m in sv.tabDataMore:
      leaves.add wrap[Z3AnyAst](ctx, checkedSelect(ctx, m.raw, keyRaw))
    svWithLeaves(ctx, defaultZero(valTy, "__tabValProto"), leaves, valTy)

proc noteTableKey*(k: Z3String) =
  ## RFC-0005 S8f. A key term some table array is selected or stored at.
  if firstSighting(cast[pointer](k.raw)):
    containerCard.tabKeys.add k

proc noteSetKey*(k: Z3BitVec[64]) =
  ## RFC-0005 S8f. A key term some set array is selected or stored at.
  if firstSighting(cast[pointer](k.raw)):
    containerCard.setKeys.add k

proc tabMoreEq*(ctx: Z3Context; a, b: SymVal): Z3Bool =
  ## RFC-0005 S8at. A container value's further data arrays equal, pairwise
  ## (`retBindEq`'s table arm); `true` for a scalar value.
  result = mkBool(true)
  for i in 0 ..< min(a.tabDataMore.len, b.tabDataMore.len):
    result = result and wrap[Z3Bool](ctx,
      checkedEq(ctx, a.tabDataMore[i].raw, b.tabDataMore[i].raw))

proc distinctPresentCount*[K](arr: Z3Array[K, Z3Bool]; keys: seq[K]): Z3Int =
  ## RFC-0005 S8f. The number of DISTINCT values among `keys` at which `arr`
  ## holds: key i counts iff it is present and differs from every earlier
  ## key. Quadratic in the key terms, which are few (one per distinct
  ## key expression the run lowered).
  result = mkInt(0)
  for i in 0 ..< keys.len:
    var counts = select(arr, keys[i])
    for j in 0 ..< i:
      counts = counts and (keys[i] != keys[j])
    result = result + ite(counts, mkInt(1), mkInt(0))

proc containerCardConds*(): seq[Z3Bool] =
  ## RFC-0005 S8f. `size >= distinctPresentCount(array, keyTerms)` for every
  ## allocated table and set: see `ContainerCardRegistry` for why this is
  ## both sound (true of every real table) and sufficient (every model
  ## satisfying it is realized by the extractors).
  ## RFC-0005 S8at: first, the facts of every input table's container value
  ## at every key term, `svCellWf`'s (a length and a size in range, a nested
  ## table's and set's size tied to its keys, which registers it, and a
  ## nested container-valued table, appended and so visited too). True of
  ## a real table at every key, present or not.
  var ti = 0
  while ti < containerCard.tabTreeBases.len:
    let b = containerCard.tabTreeBases[ti]
    inc ti
    let ctx = b.tabSize.ctx
    var keys: seq[RawZ3Ast]
    if b.tabKeyTy.kind == itString:
      for k in containerCard.tabKeys: keys.add k.raw
    else:
      for k in containerCard.setKeys: keys.add k.raw
    for k in keys:
      result.add svCellWf(tabValAt(ctx, b, k), b.tabValTy, true)
  # RFC-0005 S8bl: every string key term is a string of bytes. True of
  # every real key, so it prunes no real input; it binds a term recorded on
  # ANOTHER path too, whose symbols are free on this one (a key of another
  # path's `isTabKeys` enumeration). The table extractor renders each present
  # key term (`extractTableEntries`), and such a term, unconstrained, took a
  # codepoint above 255: `evalStrBytes` raised inside the walk, a walker
  # fault (C++) or, lost on the C backend's unwind, a false sxUnsat.
  for k in containerCard.tabKeys:
    result.add seqStrElemConds(SymVal(kind: svString, str: k))
  for b in containerCard.tabBases:
    let present = wrap[Z3Array[Z3String, Z3Bool]](b.present.ctx, b.present.raw)
    result.add (b.size >= distinctPresentCount(present, containerCard.tabKeys))
  for b in containerCard.setBases:
    let members = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      b.members.ctx, b.members.raw)
    if not cellDomain(b.elemTy).bounded:
      result.add (b.size >= distinctPresentCount(members, containerCard.setKeys))
      continue
    # RFC-0005 S8z: a narrower element type. The key terms are global to
    # the run, so a term may be a cell no member of THIS set can occupy;
    # only in-domain terms count. The fresh members the extractor adds are
    # in-domain cells no term names, so there must be enough of them:
    # `size + (named in-domain cells absent) <= |domain|`.
    var present = mkInt(0)
    var absent = mkInt(0)
    let keys = containerCard.setKeys
    for i in 0 ..< keys.len:
      var fresh = inCellDomain(keys[i], b.elemTy).get
      for j in 0 ..< i:
        fresh = fresh and (keys[i] != keys[j])
      let isIn = select(members, keys[i])
      present = present + ite(fresh and isIn, mkInt(1), mkInt(0))
      absent = absent + ite(fresh and not isIn, mkInt(1), mkInt(0))
    result.add (b.size >= present)
    let dsize = cellDomainSize(b.elemTy)
    if dsize < high(int64):
      # RFC-0005 S8at: `mkZ3IntLit`, not `mkInt` (a `cint`): a 32-bit
      # unsigned or `float32` domain has 2^32 cells, which `mkInt` faulted
      # on (`RangeDefect`, every `HashSet[uint32]` / `Table[uint32, V]`).
      result.add (b.size + absent <= mkZ3IntLit(dsize))

proc opSite*(construct, site: string): string =
  ## K10a-float. The trap's site text: the construct, at its source position
  ## when the lowering op carries one.
  if site.len > 0: construct & " at " & site else: construct

proc uncheckedIndexSite*(loc: string): string =
  ## RFC-0016 PRC-07. The omission's text for an out-of-container access.
  opSite("an element access outside its container (no bound check emitted)",
         loc)

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
    # RFC-0005 S8bu: the path's element cells, for a closure call's
    # `bindVarLocs`.
    wp[].callerElemCells = p.elemCells
    # Reset the closure-exit fields (NI-1 fix — mirror of threadvar reset
    # inside seedCallerHeapThreadvars): each lower() call starts clean so
    # a non-heap-writing closure doesn't carry the previous call's exit-heap
    # into the next lower() drain.
    wp[].closureDidMutateHeap = false
    wp[].closureExitHeaps = initTable[string, Z3AnyAst]()
    wp[].closureExitAllocCounters = initTable[string, int]()
    wp[].closureExitLiveRefs = initTable[string, seq[Z3AnyAst]]()

proc isFollowConcreteWalk*(): bool =
  ## RFC-fuzzer-nextgen G3fix. True iff `currentWalkCtxPtr != nil` (a walk is
  ## active) AND the live `WalkCtx.mode == wmFollowConcrete`; false outside an
  ## active walk AND during an ordinary `wmExplore` walk. Lets `lower`'s
  ## `iekVar` free-reference arm mode-gate its havoc degrade without a
  ## `WalkCtx` parameter -- mirrors the `syncXxx`/`currentWalkCtxPtr` idiom
  ## above. RFC-0016 INT-34 B2: `WalkCtx` is `walk_types`', so the body sits
  ## here, where its forward declaration was.
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp.mode == wmFollowConcrete
  else:
    false

proc isConcolicFollowWalk*(): bool =
  ## RFC-0016 W3-z int2. `isFollowConcreteWalk()` and not the whole-run
  ## gate's tail walk (`WalkCtx.tailGate`): a concolic collection replaying an
  ## executed trace. The tail walk is also `wmFollowConcrete`, but it
  ## over-approximates the run as the explore walk does, so it reads a global
  ## as the explore walk does (its entry value); before, the concolic safety
  ## net bound it a 64-bit integer whatever its type, and a case-object
  ## global's field read halted the tail walk (`seVariantFieldOnDeclinedCtor`),
  ## failing a replay-confirmed sxSat closed (`ubTailUnverified`).
  if currentWalkCtxPtr != nil:
    let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
    wp.mode == wmFollowConcrete and not wp.tailGate
  else:
    false

proc programGlobal*(name: string): Option[IRGlobal] =
  ## RFC-0005 S8as. The module-level variable `name` of the program being
  ## walked, when its entry value is modelled: its type reaches no heap cell
  ## (`irTypeRefFree`), so a fresh value of the type is every value it can
  ## hold. none() outside a walk or for any other global.
  if currentWalkCtxPtr == nil: return none(IRGlobal)
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  if not wp.statics.globals.hasKey(name): return none(IRGlobal)
  let g = wp.statics.globals[name]
  if not irTypeRefFree(g.ty): return none(IRGlobal)
  some(g)

proc globalHiddenRoute*(name: string): string =
  ## RFC-0005 S8cs. Why a store the walk does not see may reach the global
  ## `name` (`IRGlobal.hiddenRoute`), or "".
  if currentWalkCtxPtr == nil: return ""
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  if not wp.statics.globals.hasKey(name): return ""
  wp.statics.globals[name].hiddenRoute

proc unwrittenResultZero*(): Option[SymVal] =
  ## RFC-0005 S8n. The value of a callee's `result` read before anything
  ## wrote it: the innermost call frame's return type's zero value (Nim
  ## zero-initialises `result` before the body runs), or `none` outside a
  ## walk, for a void frame, or for a type `defaultZero` cannot build.
  ## `lower`'s `iekVar` arm asks this when
  ## a callee reads `result` that no path statement has bound yet
  ## (`result += 100` as the body's first statement). Before S8n the read
  ## fell to the module-level-global arm, `feGlobalReadUnmodelled`. The
  ## innermost `CallFrame` is the frame being walked: a callee's arguments
  ## are lowered before its frame is pushed. A frame whose return type has
  ## no total zero value keeps the global-read decline. RFC-0005 S8p: the
  ## SUT's own frame has no `CallFrame`; its return type rides in
  ## `statics.sutRetTy`, carried from the parse (`SymexProgram.retTy`).
  if currentWalkCtxPtr == nil: return none(SymVal)
  let wp = cast[ptr WalkCtx](currentWalkCtxPtr)
  if wp.callStack.len == 0:
    let st = wp.statics.sutRetTy
    if st == nil or not defaultZeroTotal(st): return none(SymVal)
    return some(defaultZero(st, "result.unwritten"))
  let t = wp.callStack[wp.callStack.high].retTy
  if t == nil or not defaultZeroTotal(t): return none(SymVal)
  some(defaultZero(t, wp.callStack[wp.callStack.high].retName & ".unwritten"))

proc seqElemFits*(val: SymVal, elemTy: IRType): bool =
  ## RFC-0005 S8ar. True iff `storeSeqElem` can store `val` into a seq of
  ## `elemTy` as it is: the element's own kind, or (for an integer element)
  ## an Int-promoted value, which `storeSeqElem` converts at the width.
  ## RFC-0005 batch 4: on the element's cell type (`seqCellTy`, S8ba) and
  ## the value's base, as `storeSeqElem` / `seqStoreArrs` store them.
  let elemTy = seqCellTy(elemTy)
  var val = val
  while val.kind == svDistinct: val = val.distinctBaseSym[]
  case elemTy.kind
  of itInt:
    val.kind == svInt or
      (case elemTy.width
       of 8: val.kind == svBV8
       of 16: val.kind == svBV16
       of 32: val.kind == svBV32
       else: val.kind == svBV64)
  of itBool: val.kind == svBool
  of itFloat32: val.kind == svFloat32
  of itFloat64: val.kind == svFloat64
  of itString: val.kind == svString
  of itRef: val.kind == svRef
  of itPtr: val.kind == svPtr
  else:
    # RFC-0005 S8bc: a tree element's store checks the value itself
    # (`seqStoreArrs`, which declines a value that does not fit).
    isTreeSeqElemTy(elemTy)

# ---- RFC-0005 S8bc (item 3): a seq of a tree element, held leaf-split ------
#
# A seq whose element is a by-value tuple, object, array, case object or
# distinct of one (`isTreeSeqElemTy`) holds one `Int -> leaf` data array per
# leaf of the element (`heapLeafSuffixes(elemTy)`, the heap's own cell
# layout): leaf 0 in `seqDataRaw`, the rest in `seqDataMore`. A read selects
# every array at the index and rebuilds the element from a prototype
# (`seqElemAt`); a store writes each leaf of the value into its array
# (`seqStoreArrs`). Every operation that builds a seq from another (slice,
# insert, a merge, ...) does to each array what it did to the one. Before
# S8bc a seq of such an element was the inert placeholder in every position
# (`seNestedSeqUnsupported`), and any read of it declined.

proc constSeqArrs*(elemTy: IRType; elem: SymVal): seq[Z3AnyAst] =
  ## RFC-0005 S8bc. Data arrays holding `elem` at every index (one constant
  ## array per leaf): `newSeq[T](n)`'s zero elements.
  ## RFC-0005 batch 4: at the element's cell type (`seqCellTy`), a
  ## `distinct` zero stored as its base.
  let elemTy = seqCellTy(elemTy)
  var elem = elem
  while elem.kind == svDistinct: elem = elem.distinctBaseSym[]
  let ctx = requireCurrentContext()
  let idxHold = mkZ3IntLit(0)
  let idxSort = ctx.checkErr Z3_get_sort(ctx.raw, idxHold.raw)
  let leaves =
    if isTreeSeqElemTy(elemTy): svLeafTerms(elem, elemTy, seqCell = true)
    else: @[wrap[Z3AnyAst](ctx, svLeafAsts(elem, elemTy)[0])]
  for leaf in leaves:
    result.add wrap[Z3AnyAst](ctx,
      ctx.checkErr Z3_mk_const_array(ctx.raw, idxSort, leaf.raw))

proc stampHeapSteps*(sv: var SymVal; steps: int) =
  ## RFC-0005 S8ar. Mark every ref a heap read produced (`sv`, or a ref inside
  ## it) as `steps` heap steps from a root. A seq records `steps` for the
  ## element refs an index read takes out of it (`seqSteps`).
  case sv.kind
  of svRef: sv.refSteps = max(sv.refSteps, steps)
  of svPtr: sv.ptrSteps = max(sv.ptrSteps, steps)
  of svSeq: sv.seqSteps = max(sv.seqSteps, steps)
  of svTuple:
    for f in sv.fields.mitems: stampHeapSteps(f, steps)
  of svArray:
    for f in sv.arrElems.mitems: stampHeapSteps(f, steps)
  of svVariant:
    # RFC-0005 S8at: a case object is a cell value; a ref in any field is a
    # heap step from the cell.
    for f in sv.vPlainFields.mitems: stampHeapSteps(f, steps)
    for _, fs in sv.vArmFields.mpairs:
      for f in fs.mitems: stampHeapSteps(f, steps)
  of svMultiVariant:
    for f in sv.mvPlainFields.mitems: stampHeapSteps(f, steps)
    for ax in sv.mvAxes.mitems:
      for _, fs in ax.armFields.mpairs:
        for f in fs.mitems: stampHeapSteps(f, steps)
  else: discard

proc svWithRaw*(ctx: Z3Context; sv: SymVal; raw: Z3AnyAst): SymVal =
  ## RFC-0005 S8bz (item 3). The scalar or string `sv` holding the term `raw`,
  ## of its own sort: `rawAnyAstOf`'s inverse.
  result = sv
  case sv.kind
  of svBV8: result.bv8 = wrap[Z3BitVec[8]](ctx, raw.raw)
  of svBV16: result.bv16 = wrap[Z3BitVec[16]](ctx, raw.raw)
  of svBV32: result.bv32 = wrap[Z3BitVec[32]](ctx, raw.raw)
  of svBV64: result.bv64 = wrap[Z3BitVec[64]](ctx, raw.raw)
  of svInt: result.zi = wrap[Z3Int](ctx, raw.raw)
  of svBool: result.bo = wrap[Z3Bool](ctx, raw.raw)
  of svFloat32: result.fp32 = wrap[Z3Float32](ctx, raw.raw)
  of svFloat64: result.fp64 = wrap[Z3Float64](ctx, raw.raw)
  of svString: result.str = wrap[Z3String](ctx, raw.raw)
  else:
    ## RFC-0016 K7b (W-11). A composite has no single term to hold: returning
    ## `sv` would hand back the stale value with no record. Its one caller
    ## (`unwrittenLeafSplit`) recurses into composites and asks only for a
    ## leaf, so this is unreachable today; a future caller that reaches it
    ## fails loudly rather than substitute silently.
    doAssert false, "svWithRaw: " & $sv.kind & " is not a scalar or string"

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

# Phase 15 R1: logical-heap array helpers (heapValueSort, mkHeapArrayVar,
# liftHeapValue, heapSelect, fieldHeapKey) moved to runtime_heap.nim
# (CR-7-deeper Stage 8+). Bodies of refPointeeTypeId/allocRefSort/freshRef/
# assertFreshness/pcImpliesNonNil also moved there.

proc probeProto*(env: Env, e: IRExpr): Option[SymVal] =
  if e == nil: return none(SymVal)
  case e.kind
  of iekVar:
    if not env.hasKey(e.vname): return none(SymVal)
    # RFC-0005 S8bu: an Int that is the conversion of a bit-vector
    # (`intOfBV`: an `int` stored in an Int-sorted heap and read back)
    # offers that bit-vector, so a literal beside it lowers as one and
    # `reconcileInt` meets the bit-vector unconverted: `v * 2` stays
    # `bvmul(2, k)`. Lowered at the Int, it was `2 * sbv2int(k)`, which
    # crossed the bridge again where the result met a bit-vector, and Z3
    # did not decide `sbv2int(r) == 2 * sbv2int(k) and r != 2 * k` (its
    # step counter stopped advancing, so `queryRLimit` did not end it).
    let back = bvOfInt(env[e.vname])
    if back.isSome: back else: some(env[e.vname])
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
  of iekVariantLit, iekMultiVariantLit, iekVariantFieldSet:
    # Round-6 A1. Same reasoning as iekTupleLit: a variant literal's own
    # SymVal kind is always `svVariant` (RFC-0005 S8p: `svMultiVariant`;
    # S8s: a field set is its receiver's kind) — no scalar proto to offer.
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
  of iekSeqSlice, iekSeqSplice, iekSeqConcat:
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
  of iekStrFind, iekStrRfind, iekStrCount, iekStrFindRe, iekStrToInt:
    # Phase 15 S4/S6b/S10a: `s.find(sub)` / `s.find(re"…")` / `parseInt(s)` → Z3Int.
    # RFC M3: `s.rfind(sub)` → Z3Int too (same shape, `lastIndexOf` instead of
    # `indexOf`). svInt sentinel so a surrounding comparison (e.g.
    # `s.find("bc") == 1`, `s.rfind("bc") == 1`, `parseInt(s) == 42`) lowers its
    # literal as a Z3Int. (RFC-0005 S8ay: iekStrFindRe is `find` / `matchLen`
    # / a `findBounds` half, all svInt.)
    some(SymVal(kind: svInt, zi: mkInt(0)))
  of iekIntToStr, iekStrReplaceAll, iekStrReplaceRe, iekStrJoin, iekStrConcat,
     iekStrCaptureRe,   # RFC-0005 S8bb: a capture group, a string
     iekStrSetAt, iekStrFromChars,   # RFC-0005 S8ca
     iekStrToLower, iekStrToUpper, iekRadixFmt, iekRuneToStr:
    # Phase 15 S5/S8/S10a: replace/join/concat/`$int` all produce a
    # Z3String. svString sentinel so `s.replace(...) == "lit"` / `xs.join(sep) ==
    # "lit"` / `$n == "42"` lowers its literal as a string and dispatches through
    # cmpString. (replace's version-gate raise happens in lower(), not here —
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
                   iekStrFind, iekStrRfind, iekStrCount, iekStrReplaceAll, iekStrJoin,
                   iekStrMatch, iekStrFindRe, iekStrReplaceRe, iekStrConcat,
                   iekStrCaptureRe, iekStrSetAt, iekStrFromChars,
                   iekIntToStr, iekStrToInt,
                   iekStrToLower, iekStrToUpper, iekRadixFmt, iekRuneToStr}:
    # Phase 15: string ops not modeled in this cycle have no proto. lower()
    # raises SymexUnsupportedStringOpError. (iekStrSplit produces an svSeq,
    # consumed only via `.len`/index — never a direct `==` — so it needs no
    # comparison proto here.)
    none(SymVal)
  of iekContains, iekTabRemovedSince:   # S8bx: a Bool
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
    # RFC-0005 S8g: every target width and signedness.
    case e.convWidth
    of 8:  some(SymVal(kind: svBV8,  signed: e.convSigned, bv8:  mkBitVec[8](0)))
    of 16: some(SymVal(kind: svBV16, signed: e.convSigned, bv16: mkBitVec[16](0)))
    of 32: some(SymVal(kind: svBV32, signed: e.convSigned, bv32: mkBitVec[32](0)))
    else:  some(SymVal(kind: svBV64, signed: e.convSigned, bv64: mkBitVec[64](0'i64)))
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
    of 8:  some(SymVal(kind: svBV8,  signed: e.ciwTgtSigned, bv8:  mkBitVec[8](0)))  # RFC-0005 S8i: range targets
    of 16: some(SymVal(kind: svBV16, signed: e.ciwTgtSigned, bv16: mkBitVec[16](0)))
    of 32: some(SymVal(kind: svBV32, signed: e.ciwTgtSigned, bv32: mkBitVec[32](0)))
    else:  some(SymVal(kind: svBV64, signed: e.ciwTgtSigned, bv64: mkBitVec[64](0'i64)))
  of iekConvIntReinterpret:
    # A1 adjudication (walker v116). SAME mirror as `iekConvIntWidth` directly
    # above: a same-width BV sentinel signed per `e.cirTgtSigned`, so a
    # literal operand meeting a reinterpret gets the correctly-signed proto.
    case e.cirWidth
    of 8:  some(SymVal(kind: svBV8,  signed: e.cirTgtSigned, bv8:  mkBitVec[8](0)))
    of 16: some(SymVal(kind: svBV16, signed: e.cirTgtSigned, bv16: mkBitVec[16](0)))
    of 32: some(SymVal(kind: svBV32, signed: e.cirTgtSigned, bv32: mkBitVec[32](0)))
    else:  some(SymVal(kind: svBV64, signed: e.cirTgtSigned, bv64: mkBitVec[64](0'i64)))
  of iekConvFloatRange:
    # RFC-0016 int6: a float of the range's width, as `lower` returns.
    if e.cfrWidth == 32: some(SymVal(kind: svFloat32, fp32: mkFloat32(0'f32)))
    else: some(SymVal(kind: svFloat64, fp64: mkFloat64(0.0)))
  of iekMathCall:
    # Phase 15 F6: predicates produce svBool; float ops produce a float of
    # the first arg's width; deferred ops have no proto (they raise on lower).
    # Phase 16 A5: classify → svBV64 (signed); copySign → float of first arg's width.
    if e.mathOp in ["signbit", "isNaN"]:
      some(SymVal(kind: svBool, bo: mkBool(false)))
    elif e.mathOp == "toFloat32":
      some(SymVal(kind: svFloat32, fp32: mkFloat32(0'f32)))   # RFC-0016 K2b
    elif e.mathOp == "toFloat64":
      some(SymVal(kind: svFloat64, fp64: mkFloat64(0.0)))
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
    # A closure's representation (the funcSym + env-flattened leaves) is not a
    # single prototype SymVal, so no surrounding subexpression takes its
    # representation from one. No prototype (`lower` builds and applies the
    # closure through `lowerClosureArm`).
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
  of iekZeroValue:
    # RFC-0005 S8u. An empty container: no integer representation.
    none(SymVal)
  of iekSeqNew:
    # RFC-0005 S8bc, S8bi. A seq: no integer representation.
    none(SymVal)
  of iekBitSet:
    # RFC-0005 S8bq. A set, or a bool / card computed from sets.
    none(SymVal)
  of iekPtrCast:
    # RFC-0016 INT-83. An address: compared through `refEq`, not a proto.
    none(SymVal)
