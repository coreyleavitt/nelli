## RFC-0016 INT-34 B4. Lowering an IR expression to a `SymVal`: a leaf cut
## out of `runtime.nim`.
##
## Region R1 of `runtime.nim` (`scripts/int34-deps.py`) lives here whole, in
## the order it had there:
##
##   * `lower`, `lowerExpr` and `lowerBool`, the per-kind arms they dispatch
##     to, and the operator templates (`binBV`, `cmpBV`, `eqBV`, ...);
##   * the union byte image, the builtin `set[T]` bit-vector model and the
##     `newSeqUninit` unwritten-element model;
##   * the interval reasoning over bit-vector terms (`bvIvl*`), the arithmetic
##     lowering (`lowerArith`) and seq equality;
##   * a global's unwritten parts and its entry value (`observeGlobalRead`,
##     `globalEntryVals`);
##   * the C4 literal lowering (`lowerSeqLit`, `lowerTupleLit`,
##     `lowerVariantLit`, ...), which INT-34 B0 placed after `lower`.
##
## With it, the run state of R0 that R1 reads, and the routines over it R1
## calls: `closureEnvWrites`, `loweringReadNames`, the S8ce fault injection,
## `arithFrames`, `checkScopes` (`resetArith`, `checkedNow`), `obligationLog`
## and `pendingEnvWriteIx`. Each threadvar lives at the lowest layer that
## reads it: the walker above reads and writes them through this module's
## export, and `resetLowerExprState` (called by `resetSymexRunState`) resets
## every one of them that is per-run.
##
## `lowerHofCall`. A higher-order call applies its closure per element through
## the walk (region R7, after `walk`), so `lower(iekHofCall)` reaches it
## through `lowerExprHooks.lowerHofCall`, a typed hook this module declares and
## `runtime.nim` fills at module init.
##
## Every routine is exported, so `runtime.nim` can call it; `runtime.nim`
## re-exports by name only what it exported before the cut.

import std/tables
import std/options
from std/typetraits import nil
import std/sets
import std/hashes
import std/algorithm
import std/math
import std/strutils
import z3

from ./buildprofile import buildSemantics
import ./types
import ./admission
import ./arith_regime
import ./definedness
import ./variant_layout as vl
import ./abstraction
import ./symval
import ./walk_state
import ./walk_types
import ./walk_path
import ./stdlib_rows
import ./runtime_floats
import ./runtime_exceptions
import ./z3check
import ./heap_model
import ./string_lower_support
import ./runtime_strings
import ./runtime_closures

type LowerExprHooks* = object
  ## RFC-0016 INT-34 B4. The one upward verb of this leaf, typed.
  lowerHofCall*: proc(env: Env; e: IRExpr): SymVal {.nimcall.}
    ## A DSL higher-order call (`map`, `filter`, `fold`): the inline path
    ## applies the closure per element through the walk's C2b descent, which
    ## `runtime.nim` owns (region R7).

var lowerExprHooks*: LowerExprHooks
  ## Filled once by `runtime.nim` at module init, beside `lowerHooks`; a plain
  ## global like it (no threadvar, so nothing to reset or release).

var closureEnvWrites* {.threadvar.}: seq[(string, SymVal)]
  ## RFC-0005 S8as. The by-reference writes of the closure calls lowered in
  ## the expression in progress -- a module-level variable, or a capture of
  ## a closure applied in the frame that built it -- each as the fresh value
  ## the call's exit axioms define (`applyClosureGround`). In call order; a
  ## later entry for a name supersedes an earlier one. `lower` cannot write
  ## the env it reads, so `drainPendingLowerEffects` binds them on the
  ## calling path, which is where Nim's write lands: the parser hoists every
  ## call operand into a statement of its own ahead of its expression
  ## (`parseAtomicOperand`), so the write precedes the reads that follow.
var loweringReadNames* {.threadvar.}: seq[string]
  ## RFC-0005 S8as. The names `lower`'s `iekVar` arm read in the expression
  ## in progress, in order. A closure call that writes a name already read
  ## there (not as its own argument) declines: which value Nim reads then
  ## depends on an evaluation order the walk does not model.

when defined(symexTestInjectWalkerFault):
  # RFC-0005 S8ce fault injection (compiled out of every normal build;
  # `-d:symexTestInjectWalkerFault` is set for its dedicated test files only,
  # by their `.nim.cfg`). Dispatch reaching the sentinel label
  # `__inject_s8ce_<shape>__` arms one shape; the next operation of that shape
  # raises out of the walker's own code with that operation's Z3 values live
  # (`injectShapeFault`'s call sites name them), and the test checks the raise
  # reaches `runSymexCaught`. The `dispatch` shape fires at the sentinel
  # statement itself. What this shows, and what it does not: the shapes are
  # distinct raise ORIGINS, not distinct swallow sites. The only destroy
  # observed swallowing a raise under nim-z3's old hooks (S8ce: the S8bx case
  # and the probe's two tracebacks) is in `walkBlock`, its reassigned
  # `seq[Path]`; most shapes were probably lost there too. That every other
  # destroy site is safe rests on the generated-C scan (no hook pops the error
  # flag; nim-z3's hooks are raise-free and `quirky`), with these shapes as
  # witnesses, not on the shapes alone.
  var injectedShape* {.threadvar.}: string
    ## The armed shape; cleared when it fires and by `resetSymexRunState`.

  proc injectShapeFault*(shape: string) =
    if injectedShape == shape:
      injectedShape = ""
      raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for the S8ce raise-shape test)]
        "S8ce synthetic " & shape & " fault (symexTestInjectWalkerFault)")

var arithFrames* {.threadvar.}: ArithFrames
  ## RFC-0005 S8w, RFC-0016 W1-d2 / D1a. A lexical stack: the top is the scope
  ## of the routine body being walked. `resetSymexRunState` seeds it with the
  ## build's (`buildRegime()`: `-d:danger`, `--overflowChecks:off`). A routine
  ## body block pushes its `ArithScope` and leaves it on the way out; a leaked
  ## push is caught by `leave`'s assert. Deliberately no try/finally (see the
  ## `runSymexCaught` note): every escape ends the run, which re-seeds the
  ## stack. Read only through `arithFrames.regime` and `emits`.
  ##
  ## Unchecked arithmetic is not a wrap: the C operation is undefined on
  ## overflow, so `lowerArith` deposits the overflow side as an
  ## `ubSignedOverflow` `ArithTrap` and the surviving side carries its negation.
  ## Unsigned results still wrap (`wrapIntToWidth`).

var checkScopes* {.threadvar.}: seq[set[CheckOption]]
  ## RFC-0016 PRC-07, int6. A lexical stack beside `arithScopes`: the top is
  ## the effective set of checks of `rangeChecks`, `boundChecks`,
  ## `fieldChecks`, `objChecks` the routine body being walked is compiled
  ## with (`IRStmt.blkOn`), in either build direction; the root is the
  ## build's. Read only through `checkedNow`.

proc resetArith*() =
  arithFrames = ArithFrames.init()
  checkScopes = @[buildSemantics.checks * {coRange, coBound, coField, coObj}]

proc checkedNow*(co: CheckOption): bool =
  ## Whether the C compiler emitted check `co` for the code being walked: its
  ## routine's effective scope (the build's, less what its position pushed
  ## off, plus what it pushed back on), or the build's outside any.
  if checkScopes.len > 0: co in checkScopes[^1]
  else: co in buildSemantics.checks

var obligationLog* {.threadvar.}: ObligationLog
  ## Issue #161 slice 2. Audit trail, NOT a raise-fork sink — deliberately
  ## NOT reset alongside `overflowConds`. The cond sinks are drained and
  ## cleared per `lower()` call (they hold the predicates one lowering
  ## produced); this log accumulates across the whole run and is reset once,
  ## at `runSymexImpl` entry, before being copied into `SymexResult`.
  ## Appending it to the per-lower reset list would silently truncate it to
  ## whatever the last expression happened to raise.

proc pendingEnvWriteIx*(name: string): int =
  ## RFC-0005 S8as. The index of the latest pending closure write of `name`
  ## (`closureEnvWrites`), or -1.
  result = -1
  for i in countdown(closureEnvWrites.high, 0):
    if closureEnvWrites[i][0] == name: return i

# ---- IR-expr → SymVal -------------------------------------------------------

var sliceViewCounter* {.threadvar.}: int
  ## v67 (dev item 1). Per-run unique-name counter for `iekSeqSlice`'s
  ## lambda bound variable — two slice views must not share the bound
  ## const's NAME (Z3 consts are keyed by name; aliasing two views' bound
  ## vars is not unsound after lambda closure, but distinct names keep
  ## printed models legible and rule the question out entirely). Reset at
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

proc lower*(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal

proc reboxSeqCell*(elemTy: IRType, cell: SymVal): SymVal =
  ## RFC-0005 S8ba. A seq element read at static type `elemTy`: a `distinct`
  ## element's cell holds its base (`seqCellTy`), re-boxed here as a fresh
  ## `svDistinct` over it (each level of a nested chain). Any other type
  ## (or a nil type from a pre-S8ba IR) is the cell itself.
  if elemTy == nil or elemTy.kind != itDistinct: return cell
  reboxDistinct(elemTy, reboxSeqCell(elemTy.distinctBase, cell))

func hasDepthBound*(ty: IRType): bool =
  ## RFC-0005 S8bc. `ty` holds, at some depth, the placeholder seq at a
  ## recursive value object's depth bound (`seRecursiveValueDepth`).
  if ty == nil: return false
  case ty.kind
  of itSeq:
    (ty.seqUnsupportedFieldReason.len > 0 and
     ty.seqUnsupportedFieldKind == seRecursiveValueDepth) or
      hasDepthBound(ty.seqElemTy)
  of itTuple:
    for f in ty.fields:
      if hasDepthBound(f): return true
    false
  of itArray: hasDepthBound(ty.elemTy)
  of itDistinct: hasDepthBound(ty.distinctBase)
  of itTable: hasDepthBound(ty.tabValTy)
  of itVariant, itMultiVariant:
    for part in heapParts(ty):
      if hasDepthBound(part.ty): return true
    false
  else: false

var seqConformCounter* {.threadvar.}: int
  ## RFC-0005 S8bc. Names the bound variable of each `conformSV` lambda.

proc variantShapeOk*(sv: SymVal; ty: IRType): bool =
  ## RFC-0005 S8bc. `sv` has every slot of case object `ty` (the precheck of
  ## `svFitsHeapTy`'s variant arms, without the parts' own fit).
  if ty.kind == itVariant:
    if sv.kind != svVariant or sv.vDisc == nil or
       sv.vPlainFields.len != ty.vPlainFieldTypes.len:
      return false
    for arm in ty.vArms:
      if not sv.vArmFields.hasKey(arm.tagOrdinal) or
         sv.vArmFields[arm.tagOrdinal].len != arm.fieldTypes.len:
        return false
    return true
  if sv.kind != svMultiVariant or sv.mvAxes.len != ty.mvAxes.len or
     sv.mvPlainFields.len != ty.mvPlainFieldTypes.len:
    return false
  for xi, ax in ty.mvAxes:
    if sv.mvAxes[xi].disc == nil: return false
    for arm in ax.arms:
      if not sv.mvAxes[xi].armFields.hasKey(arm.tagOrdinal) or
         sv.mvAxes[xi].armFields[arm.tagOrdinal].len != arm.fieldTypes.len:
        return false
  true

proc conformSV*(sv: SymVal; ty: IRType): Option[SymVal] =
  ## RFC-0005 S8bc. `sv` in the layout of a slot of type `ty`, or none.
  ##
  ## A recursive value object is unrolled to a bounded depth (`typebridge`'s
  ## `maxRecursiveValueDepth`), so one Nim type has an IR type per depth: a
  ## value built in the body has the outermost depth's layout, and a slot one
  ## level down a shallower one (`root.kids.add(leaf)`: `leaf.kids` holds the
  ## next depth's elements, the slot's `kids` the one after). The conversion
  ## TRUNCATES: a part the slot holds as the depth-bound placeholder becomes
  ## that placeholder (keeping the length), every other leaf is kept. That is
  ## sound, since every read of a placeholder declines. A seq of tree
  ## elements converts element-wise under a lambda (no quantifier). The
  ## reverse -- a shallower value into a deeper slot, which needs leaves the
  ## value never had -- is none, and the caller declines
  ## (`seRecursiveValueDepth`). Any other value is returned as it is (a
  ## scalar's width is the store's own reconciliation).
  if ty == nil: return some(sv)
  case ty.kind
  of itTuple:
    if sv.kind != svTuple or sv.fields.len != ty.fields.len: return none(SymVal)
    if not hasDepthBound(ty): return some(sv)
    var r = sv
    for i, f in ty.fields:
      let c = conformSV(sv.fields[i], f)
      if c.isNone: return none(SymVal)
      r.fields[i] = c.get
    some(r)
  of itArray:
    if sv.kind != svArray or sv.arrElems.len != ty.size: return none(SymVal)
    if not hasDepthBound(ty): return some(sv)
    var r = sv
    for i in 0 ..< r.arrElems.len:
      let c = conformSV(sv.arrElems[i], ty.elemTy)
      if c.isNone: return none(SymVal)
      r.arrElems[i] = c.get
    some(r)
  of itVariant, itMultiVariant:
    if not variantShapeOk(sv, ty): return none(SymVal)
    if not hasDepthBound(ty): return some(sv)
    var parts: seq[SymVal]
    let ps = svPartsOf(sv, ty)
    for i, part in heapParts(ty):
      let c = conformSV(ps[i], part.ty)
      if c.isNone: return none(SymVal)
      parts.add c.get
    some(svWithParts(sv, ty, parts))
  of itDistinct:
    if not hasDepthBound(ty): return some(sv)
    let c = conformSV(ejectBase(sv), ty.distinctBase)
    if c.isNone: return none(SymVal)
    some(reboxDistinct(ty, c.get))
  of itSeq:
    if sv.kind != svSeq: return none(SymVal)
    if not seqBackedTy(ty):
      if sv.isUnsupportedFieldPlaceholder: return some(sv) # [placeholder-audited]
      # Truncated to the slot's placeholder; the length is kept.
      var scratch: seq[Z3Bool]
      var r = allocateSym(ty, freshDegradeName("__seqConformTrunc"), scratch)
      r.seqLen = sv.seqLen # [placeholder-audited]
      return some(r)
    if sv.isUnsupportedFieldPlaceholder: return none(SymVal) # [placeholder-audited]
    # RFC-0005 batch 4: a seq value's element type is its cell type
    # (`seqCellTy`, S8ba), so the slot's is compared and conformed as one.
    let cellTy = seqCellTy(ty.seqElemTy)
    if not isTreeSeqElemTy(cellTy) or sv.seqElemTy == cellTy:
      return some(sv)
    if not isTreeSeqElemTy(sv.seqElemTy): return none(SymVal)
    let ctx = requireCurrentContext()
    inc seqConformCounter
    let iVar = mkIntVar("__seqconform_i" & $seqConformCounter)
    let c = conformSV(seqElemAt(sv, iVar), cellTy)
    if c.isNone or not svFitsHeapTy(c.get, cellTy): return none(SymVal)
    var arrs: seq[Z3AnyAst]
    for leaf in svLeafTerms(c.get, cellTy, seqCell = true):
      arrs.add lambdaOver(ctx, iVar, leaf)
    var r = mkSeqSV(sv.seqLen, arrs, cellTy) # [placeholder-audited]
    r.seqSteps = sv.seqSteps
    some(r)
  else: some(sv)

proc seqStoreDeclineKind*(elemTy: IRType): SymexErrorKind =
  ## The classified kind of a store a seq of `elemTy` cannot take
  ## (`seqStoreArrs` none): `seNestedSeqUnsupported` for an element type the
  ## model does not back (a known modelling gap, RFC-0016 K9c-g),
  ## `seRecursiveValueDepth` when the element type holds a depth bound (a
  ## value of another depth's layout), else `feUnsupportedOp`.
  if not isBackedSeqElemTy(elemTy): seNestedSeqUnsupported
  elif hasDepthBound(elemTy): seRecursiveValueDepth
  else: feUnsupportedOp

proc storeSeqElem*(dataRaw: Z3AnyAst, elemTy: IRType, idx: Z3Int,
                  val: SymVal): Z3AnyAst =
  ## Store `val` at index `idx` in the (erased) seq data array, returning the
  ## new erased array. RFC-0005 S8ba: `iekSeqAdd` stores through here too
  ## (it had its own int64/bool-only dispatch), and a distinct element is
  ## stored as its base (`seqCellTy`, `ejectBase`).
  let elemTy = seqCellTy(elemTy)
  let val = ejectBase(val)
  case elemTy.kind
  of itInt:
    # #163 review R22 site 3 prerequisite: reconcile an `svInt`-shaped RHS
    # (a `range[lo..hi]` top-level param promotes to `svInt` under the
    # engine's default `isOptimised` integer semantics, `runSymexImpl`'s
    # `promoteSound`) to the array's BV sort BEFORE storing -- mirroring the
    # EXACT coercion `isDerefWrite`'s plain-field and arm-field write sites
    # already apply (`runtime_heap.nim`). Every seq[T] backing array is
    # BV-sorted by width regardless of whether `T` carries a declared range
    # (`allocateSeqDataRaw`'s itInt arm), so an un-reconciled `svInt` crashes
    # here on ANY int-family element, ranged or not.
    var v = val
    if v.kind == svInt:
      case elemTy.width
      of 8:  v = liftBV(intToBv[8](v.zi, Z3BitVec[8]),   elemTy.signed)
      of 16: v = liftBV(intToBv[16](v.zi, Z3BitVec[16]), elemTy.signed)
      of 32: v = liftBV(intToBv[32](v.zi, Z3BitVec[32]), elemTy.signed)
      of 64: v = liftBV(intToBv[64](v.zi, Z3BitVec[64]), elemTy.signed)
      else: discard
    case elemTy.width
    of 8:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[8]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, v.bv8))
    of 16:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[16]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, v.bv16))
    of 32:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[32]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, v.bv32))
    of 64:
      let t = wrap[Z3Array[Z3Int, Z3BitVec[64]]](dataRaw.ctx, dataRaw.raw)
      toAnyAst(store(t, idx, v.bv64))
    else:
      raise newException(ValueError, "storeSeqElem: unsupported int width " & $elemTy.width)  # [raise-audited: category-c: width-exhaustive (see seqElemAt above)]
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
        # N47 (round-6 raise-class-audit category-d closure): CONVERTED. The
        # ONE identified path into this mismatch — a `.map(fn)` HOF closure
        # returning `ref T`/`ptr T` — was already closed by N46's own
        # `applyClosureGround` hardening: `symValFromRawAst` raises for any
        # non-{int,bool,float32,float64} return type, but that raise is
        # caught in the SAME frame and the fallback now goes through
        # `allocateSym(cb.retTy, ...)` (total since N40), which for
        # itRef/itPtr always produces a correctly-kinded svRef/svPtr — traced
        # end to end above (`applyClosureGround`, ~9608-9650). The OTHER two
        # callers (`lowerSeqLit`'s literal-element store, `filter`'s
        # unchanged-element store via `seqElemAt`) were also traced: both
        # ultimately source the value from an env lookup or `allocateSym`'s
        # itRef/itPtr arm, both of which are kind-consistent by construction.
        # What was NOT fully closed (matching this file's own `lower(iekField)`
        # precedent, just above): whether an `iteSV` merge can still land a
        # degraded/opaque SymVal kind on a nominally ref/ptr-typed element
        # slot via some OTHER, not-yet-traced degrade path — the SAME
        # mechanism `tsymex_r6_heap_raise_totality.nim`'s four
        # `refSV.kind`-not-svRef/svPtr sites were converted under without an
        # independent repro (heap-raise totality slice, walker v113). Same
        # defense-in-depth call: in-band degrade, never worse than the raw
        # raise it replaces, and the array must stay well-sorted regardless —
        # a FRESH symbolic ref/ptr of the declared element type (never the
        # mismatched `val`) keeps `Z3_mk_store`'s value operand sort-correct.
        # Fix-slice item 3: was a bare fixed name — missed the 2385f84
        # uniquification sweep. A repeat store-mismatch within the same run
        # (two DIFFERENT itRef/itPtr seq-literal elements, or a `.filter`/
        # `.map` HOF revisiting this arm) collided on `(name, sort)`. Item 9:
        # routed through the shared `degradeAlloc` pairing helper.
        let placeholder = degradeAlloc(elemTy, weInternalWalkerFault,
          "storeSeqElem(itRef/itPtr): val is not svRef/svPtr, kind=" &
          plainEnglishSymValKind(val.kind) & " (weInternalWalkerFault)",
          "__storeSeqElemKindMismatch")
        if elemTy.kind == itPtr: placeholder.ptrAst else: placeholder.refAst
    let storedRaw = checkedStore(ctx, dataRaw.raw, idx.raw, valAst.raw)
    wrap[Z3AnyAst](ctx, storedRaw)
  else:
    # RFC-0016 K9c-g. An element type the model does not back has no array
    # to store into: a known modelling gap, not a walker fault. `seqStoreArrs`
    # routes it to a clean decline before it gets here; this is the backstop
    # for a direct caller, in-band as the arms above (the data is returned
    # unchanged, the path tainted `seNestedSeqUnsupported`).
    allocDegrade(seNestedSeqUnsupported, "storeSeqElem: a store into a seq " &
      "of " & $elemTy & ", an element type the model does not back " &
      "(seNestedSeqUnsupported)")
    dataRaw

proc seqStoreArrs*(seqSV: SymVal; idx: Z3Int; val: SymVal): Option[seq[Z3AnyAst]] =
  ## RFC-0005 S8bc. The data arrays of `seqSV` with `val` stored at `idx`:
  ## `storeSeqElem` for a scalar element (its callers check
  ## `seqElemFits` first); for a tree element each leaf of `val`, conformed
  ## to the element type (`conformSV`), into its own array. none when the
  ## value does not fit -- a value of another depth's layout, or of a shape
  ## some upstream degrade produced -- and the caller declines
  ## (`seqStoreDecline`). Every leaf's sort is checked against its array's
  ## range first, so no ill-sorted store is ever built.
  let elemTy = seqSV.seqElemTy
  # RFC-0016 K9c-g. An element type the model does not back has no arrays to
  # store into: the store declines (`seqStoreDecline`, `seNestedSeqUnsupported`).
  if not isBackedSeqElemTy(elemTy): return none(seq[Z3AnyAst])
  if not isTreeSeqElemTy(elemTy):
    return some(@[storeSeqElem(seqSV.seqDataRaw, elemTy, idx, val)]) # [placeholder-audited]
  # RFC-0005 batch 4: a `distinct` value is stored as its base (the seq's
  # element type is the cell type, `seqCellTy`).
  let c = conformSV(ejectBase(val), elemTy)
  if c.isNone or not svFitsHeapTy(c.get, elemTy): return none(seq[Z3AnyAst])
  let ctx = requireCurrentContext()
  let arrs = seqArrs(seqSV)
  let leaves = svLeafTerms(c.get, elemTy, seqCell = true)   # RFC-0016 INT-78
  if leaves.len != arrs.len: return none(seq[Z3AnyAst])
  for i in 0 ..< arrs.len:
    let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, arrs[i].raw)
    if ctx.checkErr(Z3_get_array_sort_range(ctx.raw, arrSort)) !=
       ctx.checkErr(Z3_get_sort(ctx.raw, leaves[i].raw)):
      return none(seq[Z3AnyAst])
  var outArrs: seq[Z3AnyAst]
  for i in 0 ..< arrs.len:
    outArrs.add wrap[Z3AnyAst](ctx,
      checkedStore(ctx, arrs[i].raw, idx.raw, leaves[i].raw))
  some(outArrs)

proc seqStoreDecline*(op: string; elemTy: IRType; val: SymVal): SymVal =
  ## RFC-0005 S8bc. The in-band decline of a tree element store that does not
  ## fit (`seqStoreArrs` none): `seRecursiveValueDepth` when the element type
  ## holds a depth bound (a value of another depth's layout), else
  ## `feUnsupportedOp`. Returns a fresh placeholder seq of the declined
  ## kind, so every later read of it declines too.
  let kind = seqStoreDeclineKind(elemTy)
  let msg =
    if kind == seNestedSeqUnsupported:
      op & ": a store into a seq of " & $elemTy & ", an element type the " &
        "model does not back (seNestedSeqUnsupported)"
    else:
      op & ": a " & plainEnglishSymValKind(val.kind) &
        " that does not fit an element of the seq (" & $elemTy & ")" &
        (if kind == seRecursiveValueDepth:
           " -- a recursive value object is unrolled to a bounded depth, " &
           "and this value reaches past it (seRecursiveValueDepth)"
         else: " (feUnsupportedOp)")
  queueDegrade(kind, msg)
  var fresh: seq[Z3Bool]
  allocateSym(tUnsupportedFieldSeq(elemTy, msg, kind = kind),
              freshDegradeName("__seqStoreDecline"), fresh)


proc containerRecvDeclined*(recv: SymVal; want: SVKind; op: string): bool =
  ## RFC-0005 S8u. True, after recording an in-band decline, when a table or
  ## set mutation's receiver did not lower to `want`: the stand-in of an
  ## earlier in-band degrade (an unbound local read as a global). The caller
  ## returns the receiver unchanged. These were `doAssert`s, reported as
  ## `weInternalWalkerFault`.
  ## A table receiver whose key type is not `string` (`allocateSym`'s
  ## declined, inert placeholder) is declined here too, before its key is
  ## lowered against a string prototype (`coerceIntLit` raised on it).
  ## RFC-0005 S8ar: any unbacked table (`isBackedTableTy`), key or value;
  ## each op had its own value-type `else` arm.
  if recv.kind == want:
    if want == svTable and not isBackedTableTy(recv.tabKeyTy, recv.tabValTy):
      if not isTableKeyTy(recv.tabKeyTy):
        queueDegrade(seUnsupportedTableKeyType,
          op & ": " & tableKeyDeclineMsg(recv.tabKeyTy))
      else:
        queueDegrade(seUnsupportedTableValType,
          op & ": " & tableValDeclineMsg(recv.tabValTy))
      return true
    return false
  queueDegrade(feUnsupportedOp,
    op & ": receiver lowered to " & plainEnglishSymValKind(recv.kind) &
    ", not a " & plainEnglishSymValKind(want) & " (feUnsupportedOp)")
  true

proc intWindow*(width: int, signed: bool): tuple[lo, hi: Z3Int,
                                                span: Z3Int,
                                                ivl: Option[Interval]]
  ## RFC-0005 S8aa fwd-decl (`lowerConvIntReinterpret`); defined beside
  ## `wrapIntToWidth`.

proc lowerConvIntReinterpret*(operandSV: SymVal, cirWidth: int,
                              tgtSigned: bool): SymVal =
  ## A1 adjudication (walker v116): SAME-WIDTH signedness reinterpret (e.g.
  ## `uint(x)` from an `int`, `uint32(y)` from an `int32`). Every fixed-width
  ## Nim int allocates as an svBV* whose raw Z3 BV `raw` ast is
  ## signedness-agnostic — only the `signed` TAG steers which downstream
  ## comparison/shift-right variant a later op picks (`lowerCmp`/`arithBV`
  ## dispatch on `.signed`, never re-derive it from the ast). A same-width
  ## reinterpret is therefore a pure tag flip: identical `bvN` field, `signed`
  ## replaced by `tgtSigned`. This is exactly what makes it SOUND for every
  ## input (not merely the A1 cell that discovered the gap): the bit pattern
  ## genuinely does not change under a same-width `int`<->`uint` cast in Nim
  ## either — that's what "reinterpret" means. (Contrast `declineIntWidthConv`'s
  ## remaining NARROWING case, which truly has no modeled primitive: it must
  ## drop bits, not just relabel them.)
  case operandSV.kind
  of svBV8:  SymVal(kind: svBV8,  signed: tgtSigned, bv8:  operandSV.bv8)
  of svBV16: SymVal(kind: svBV16, signed: tgtSigned, bv16: operandSV.bv16)
  of svBV32: SymVal(kind: svBV32, signed: tgtSigned, bv32: operandSV.bv32)
  of svBV64: SymVal(kind: svBV64, signed: tgtSigned, bv64: operandSV.bv64)
  of svInt:
    # RFC-0005 S8aa: an Int-sorted operand (a stamped scan offset, or an
    # unstamped `.len` / `find` / `parseInt` result, a signed 64-bit `int`)
    # has no bit pattern to relabel, but a same-width reinterpret is still
    # a total function of its VALUE: the one integer of the target's window
    # congruent to it modulo `2^width` (two's complement is exactly that).
    # `wrapIntToWidth`'s term reduces it -- `lo + (v - lo) mod 2^w` -- and a
    # value whose interval already lies in the target window (a
    # non-negative `len` to `uint`) is itself. Before S8aa this declined
    # (`feUnsupportedOpHavoc`, a fresh placeholder): `data.len.uint` in an
    # unsigned B4 scan lost the bound on its own path.
    let win = intWindow(cirWidth, tgtSigned)
    let v = operandSV.zi
    let ivl = operandSV.ziIvl
    if ivl.isSome and win.ivl.isSome and ivl.get.lo >= win.ivl.get.lo and
       ivl.get.hi <= win.ivl.get.hi:
      return SymVal(kind: svInt, zi: v, ziWidth: cirWidth,
                    ziSigned: tgtSigned, ziIvl: ivl)
    let inWin = v >= win.lo and v <= win.hi
    SymVal(kind: svInt, zi: ite(inWin, v, win.lo + ((v - win.lo) mod win.span)),
           ziWidth: cirWidth, ziSigned: tgtSigned, ziIvl: win.ivl)
  else:
    raiseAssert "lowerConvIntReinterpret: unsupported operand kind: " &
      $operandSV.kind

proc intBounds*(width: int): (int64, int64)
  ## RFC-0005 S8i fwd-decl (`lowerConvIntRange`); defined beside
  ## `overflowCondInt`.

# ---- RFC-0016 PRC-07 slice B: the union byte image -----------------------------
#
# With `--fieldChecks:off` on the c backend a variant field is a plain union
# member access, defined as the bytes of the union (C11 6.5.2.3 note 95). A
# value variant then carries the union's bytes as one image: a 64-bit cell
# per 8 bytes (`vImage`), the arm fields its views at `variant_layout`'s
# offsets. The per-arm slots stay the representation of the active arm's
# fields (an in-arm read is its slot), and the two are kept coherent by
# construction: a constructor writes the arm's fields over the zero of the
# object's initialisation (a free parameter's padding over fresh cells), every
# write inserts into the image and re-derives the active arm's fields its
# bytes cover, an out-of-arm read extracts from the image. A checked build
# builds no image (`unionImageGate`), so it carries no term for it.
#
# On cpp the same access is defined only through the union's active member,
# the member last written, so a value variant carries that arm (`vActive`)
# and a read through another arm is `ubInactiveVariantField` there.

proc rangeUnchecked*(): bool =
  ## `--rangeChecks:off`: a `range` value is a plain load and store of its
  ## base integer, so foreign bytes are a value of it (the build holds no
  ## range fact for them either).
  coRange notin buildSemantics.checks

# The image is 2n cells: n data cells then n indeterminate-byte mask cells (a
# mask byte of 0xFF marks a byte no write reached: Nim leaves an object that a
# constructor built whole uninitialised before it writes, so those bytes are
# whatever the stack held). A write sets the data and clears the mask over the
# bytes it covers; a read of masked bytes is indeterminate (`imgReadDef`).

proc unwrittenImage*(lay: vl.VariantLayout): seq[Z3BitVec[64]] =
  ## Every byte indeterminate: a constructor Nim emits without zeroing
  ## (`V(k: ka, a: v)` naming every field of the arm), before it writes the
  ## arm's fields.
  for _ in 0 ..< unionCellCount(lay): result.add mkBitVec[64](0'i64)
  for _ in 0 ..< unionCellCount(lay): result.add mkBitVec[64](-1'i64)

proc samePlace*(f, w: vl.Place): bool =
  f.off == w.off and f.size == w.size and f.kind == w.kind and
    f.ty.kind == w.ty.kind and (f.kind == vl.pkBool or f.ty == w.ty)

proc bitsPlace*(bits: Z3BitVec[64]; p: vl.Place;
               writer: Option[(vl.Place, SymVal)]): Option[SymVal] =
  ## The value of a `p`-typed field whose bytes are the low `p.size` bytes of
  ## `bits`. An int is every bit pattern; an enum its raw C value; a float
  ## the value of its IEEE bits. A bool or a `range` holds only its own
  ## values, so arbitrary bytes are no value of it: `none` (the caller
  ## declines), unless `writer`, a field of the same place and kind, just
  ## wrote them: its value then. So is an enum stored wider than its
  ## ordinal width (`pkEnumWide`, RFC-0016 0.10.0 review H6): `ord` of its
  ## four bytes may be a value its width does not hold. A `range` under
  ## `--rangeChecks:off` is every bit pattern of its base integer
  ## (`rangeUnchecked`).
  case p.kind
  of vl.pkBool, vl.pkRestricted, vl.pkEnumWide:
    if writer.isSome and samePlace(p, writer.get[0]):
      return some(normSlot(writer.get[1], p.ty))
    if p.kind == vl.pkRestricted and rangeUnchecked():
      return some(cellValue(bits and byteMask(p.size), p.ty))
    none(SymVal)
  of vl.pkOpaque:
    case p.ty.kind
    of itFloat64:
      some(SymVal(kind: svFloat64, fp64: bvToFpBits(bits, Z3Float64)))
    of itFloat32:
      some(SymVal(kind: svFloat32,
                  fp32: bvToFpBits(extract(bits, 31, 0), Z3Float32)))
    else: none(SymVal)
  of vl.pkInt, vl.pkEnum:
    some(cellValue(bits and byteMask(p.size), p.ty))

proc imgReadAt*(img: seq[Z3BitVec[64]]; base, off, size: int): Z3BitVec[64] =
  result = mkBitVec[64](0'i64)
  var at = off
  while at < off + size:
    let cell = base + at div 8
    let inCell = at mod 8
    let n = min(8 - inCell, off + size - at)
    result = result or (((img[cell].lshr ofByteShift(inCell)) and byteMask(n)) shl
                        ofByteShift(at - off))
    at += n

proc imgRead*(img: seq[Z3BitVec[64]]; off, size: int): Z3BitVec[64] =
  ## The `size` bytes of data at union byte `off`, as the low bytes of a cell.
  imgReadAt(img, 0, off, size)

proc imgReadMask*(img: seq[Z3BitVec[64]]; off, size: int): Z3BitVec[64] =
  ## The indeterminate-byte mask over the same bytes (0xFF per byte).
  imgReadAt(img, img.len div 2, off, size)

proc overlaps*(f, g: vl.Place): bool =
  f.off < g.off + g.size and g.off < f.off + f.size

proc writeExactArm*(lay: vl.VariantLayout; tag: int; written: vl.Place): bool =
  ## Whether a write to `written` while `tag` is the active arm leaves every
  ## field of that arm with a value (`bitsPlace`): an int, enum or float
  ## takes any bytes; a bool or `range` only its own, written as itself.
  if not lay.arms.hasKey(tag): return false
  for f in lay.arms[tag]:
    if overlaps(f, written) and
       f.kind notin {vl.pkInt, vl.pkEnum, vl.pkOpaque} and
       not (f.kind == vl.pkRestricted and rangeUnchecked()) and
       not samePlace(f, written):
      return false
  true

proc floatKeyCell*(k: SymVal; keyTy: IRType): Option[Z3BitVec[64]] =
  ## RFC-0005 S8at. The 64-bit cell of a float `Table` key: the IEEE bit
  ## pattern of the key Nim's table finds it by. `hash(float)` adds `0.0`,
  ## so `-0.0` and `0.0` hash alike, and `==` makes them one key: both are
  ## the cell of `+0.0`. A NaN is never `==` to itself, so a NaN key is
  ## never found (`tabKeyNaN`); its cell is the canonical quiet NaN's, which
  ## a lookup never consults. A `float32` key's 32 bits are zero-extended.
  case keyTy.kind
  of itFloat64:
    if k.kind != svFloat64: return none(Z3BitVec[64])
    let canon = ite(isZero(k.fp64), mkFloat64(0.0), k.fp64)
    some(ite(isNaN(k.fp64), mkBitVec[64](0x7FF8_0000_0000_0000'i64),
             toIeeeBv(canon)))
  of itFloat32:
    if k.kind != svFloat32: return none(Z3BitVec[64])
    let canon = ite(isZero(k.fp32), mkFloat32(0'f32), k.fp32)
    let bits = zeroExtend(toIeeeBv(canon), 32)
    some(ite(isNaN(k.fp32), mkBitVec[64](0x7FC0_0000'i64), bits))
  else: none(Z3BitVec[64])

proc tabKeyNaN*(k: SymVal; keyTy: IRType): Option[Z3Bool] =
  ## RFC-0005 S8at. For a float key, whether it is a NaN: a NaN key is never
  ## found, `t[NaN] = v` adds an entry no lookup reaches (the size grows,
  ## nothing is stored), and `t.del(NaN)` removes nothing. `none` for every
  ## other key type.
  case keyTy.kind
  of itFloat64: (if k.kind == svFloat64: some(isNaN(k.fp64)) else: none(Z3Bool))
  of itFloat32: (if k.kind == svFloat32: some(isNaN(k.fp32)) else: none(Z3Bool))
  else: none(Z3Bool)

proc tabKeyTerm*(k: SymVal; keyTy: IRType): Option[Z3AnyAst] =
  ## RFC-0005 S8ar. The term a backed table holds key `k` at: the string
  ## itself, or its 64-bit cell (`cellOf`); recorded in the run's key terms
  ## (`ContainerCardRegistry`: a cell key among the set keys, the encoding
  ## it shares). `none` for a value that is not of the key type.
  ## RFC-0005 S8at: a float key's cell is `floatKeyCell`'s.
  if keyTy.kind in {itFloat32, itFloat64}:
    let fc = floatKeyCell(k, keyTy)
    if fc.isNone: return none(Z3AnyAst)
    noteSetKey(fc.get)
    return some(toAnyAst(fc.get))
  if keyTy.kind == itString:
    if k.kind != svString: return none(Z3AnyAst)
    noteTableKey(k.str)
    return some(toAnyAst(k.str))
  let c = cellOf(k, keyTy)
  if c.isNone: return none(Z3AnyAst)
  noteSetKey(c.get)
  some(toAnyAst(c.get))

proc tabValTerms*(v: SymVal; valTy: IRType): Option[seq[Z3AnyAst]] =
  ## RFC-0005 S8ar (`tabValTerm`). The terms a backed table stores value
  ## `v` as, one per data array (`TabValLeaf`); `none` for a value that is
  ## not of the value type.
  ## RFC-0005 S8at: a container value is its leaves (`svLeafAsts`), one per
  ## data array; one that does not have its type's shape is `none`.
  case tabValLeaf(valTy)
  of tvTree:
    if not svFitsHeapTy(v, valTy): return none(seq[Z3AnyAst])
    let ctx = requireCurrentContext()
    var r: seq[Z3AnyAst]
    for raw in svLeafAsts(v, valTy): r.add wrap[Z3AnyAst](ctx, raw)
    some(r)
  of tvStr: (if v.kind == svString: some(@[toAnyAst(v.str)]) else: none(seq[Z3AnyAst]))
  of tvF32: (if v.kind == svFloat32: some(@[toAnyAst(v.fp32)]) else: none(seq[Z3AnyAst]))
  of tvF64: (if v.kind == svFloat64: some(@[toAnyAst(v.fp64)]) else: none(seq[Z3AnyAst]))
  of tvCell:
    let c = cellOf(v, valTy)
    if c.isNone: none(seq[Z3AnyAst]) else: some(@[toAnyAst(c.get)])

# ---- RFC-0005 S8bq: Nim's builtin `set[T]` as one bit-vector -----------------
#
# A `set[T]` value (`svBitSet`) is a bit-vector of `n = bitSetDomain(T).size`
# bits, bit `i` standing for the value `lo + i` of `T`. Every operation Nim
# defines on it is a bit-vector term: membership a shifted bit, `incl` /
# `excl` an `or` / `and not` of one bit, `+ - *` the bitwise `or` / `and
# not` / `and`, `<=` an empty difference, `==` equality, `card` the bit
# count. It is exact: `n` is the whole domain, and Z3 decides it without
# quantifiers or arrays. Before S8bq every set-typed value declined.

template bsBin*(f: untyped; a, b: Z3AnyAst): Z3AnyAst =
  let c = a.ctx
  wrap[Z3AnyAst](c, c.checkErr f(c.raw, a.raw, b.raw))

proc bsNot*(a: Z3AnyAst): Z3AnyAst =
  let c = a.ctx
  wrap[Z3AnyAst](c, c.checkErr Z3_mk_bvnot(c.raw, a.raw))

proc bsEqZ*(a, b: Z3AnyAst): Z3Bool =
  let c = a.ctx
  wrap[Z3Bool](c, checkedEq(c, a.raw, b.raw))

proc bsKeyCell*(v: SymVal): Option[Z3BitVec[64]] =
  ## A set element's value as a 64-bit cell, extended by its own
  ## signedness (a `bool` is 0 / 1), so it compares with the domain's bounds
  ## as a signed 64-bit value. `none` for a value that is not an ordinal.
  var v = v
  while v.kind == svDistinct and v.distinctBaseSym != nil:
    v = v.distinctBaseSym[]
  case v.kind
  of svBool: some(ite(v.bo, mkBitVec[64](1'i64), mkBitVec[64](0'i64)))
  of svBV8, svBV16, svBV32: some(lowerConvIntWidth(v, 64, v.signed).bv64)
  of svBV64, svInt: bv64Operand(v)
  else: none(Z3BitVec[64])

proc bsIndex*(cell: Z3BitVec[64]; elemTy: IRType):
    tuple[inDom: Z3Bool, amt: Z3AnyAst] =
  ## The bit of the set a 64-bit `cell` names: whether it is in the
  ## domain, and its index `cell - lo` as an `n`-bit shift amount (the low
  ## `n` bits, or zero-extended to `n`). The amount is meaningful only
  ## in the domain.
  let dom = bitSetDomain(elemTy)
  let n = dom.size
  let lo = mkBitVec[64](dom.lo)
  let hi = mkBitVec[64](dom.lo + int64(n) - 1)
  let inDom = bvsle(lo, cell) and bvsle(cell, hi)
  let idx = cell - lo
  let c = idx.ctx
  let amt =
    if n == 64: toAnyAst(idx)
    elif n < 64:
      wrap[Z3AnyAst](c, c.checkErr Z3_mk_extract(c.raw, cuint(n - 1), 0, idx.raw))
    else:
      wrap[Z3AnyAst](c, c.checkErr Z3_mk_zero_ext(c.raw, cuint(n - 64), idx.raw))
  (inDom, amt)

proc bsBit*(s: Z3AnyAst; amt: Z3AnyAst): Z3Bool =
  ## Bit `amt` of `s` is set.
  let c = s.ctx
  let shifted = bsBin(Z3_mk_bvlshr, s, amt)
  let low = wrap[Z3AnyAst](c, c.checkErr Z3_mk_extract(c.raw, 0, 0, shifted.raw))
  bsEqZ(low, bsRawNum(c, 1, "1"))

proc bsSingle*(ctx: Z3Context; n: int; amt: Z3AnyAst): Z3AnyAst =
  ## The set holding only bit `amt`.
  bsBin(Z3_mk_bvshl, bsRawNum(ctx, n, "1"), amt)

var bitSetCardTerms* {.threadvar.}: seq[Z3BitVec[64]]
  ## RFC-0005 S8bq. Every `card` term lowered in the running walk (held, so
  ## each keeps its id), and their ids. A query that mentions one may be a
  ## pigeonhole-hard bit count (`card(s + {c}) > card(s) + 1` ran past 280
  ## s), so `checkCapped` bounds it (`queryMentionsBitSetCard`). Reset at
  ## `runSymexImpl` entry.
var bitSetCardIds* {.threadvar.}: HashSet[int]
var bitSetCardSets* {.threadvar.}: Table[int, tuple[s: Z3AnyAst, n: int]]
  ## RFC-0005 S8bv. Each `card` term's set and width, by the term's id (the
  ## set held, so its id stays live), for `bitSetCardFacts`.

var walkerWorkUnits* {.threadvar.}: int
  ## RFC-0016 K7. The walker-side work units of this thread, running total:
  ## query construction (`ownContextSolver`) and the per-query fact passes
  ## (`chargeWalkerTerms`). Charged to the same `walkRLimit` budget as the Z3
  ## units, so the budget bounds wall time and not only solver time.

const walkerTermUnits* = 15
  ## RFC-0016 K7. Units charged per term visit: one term, once, by one query
  ## construction (`ownContextSolver`) or one fact pass (`seqLenCaps`,
  ## `seqRangeFacts`, `divRangeFacts`, `bvOffsetLinks`, `bvIntInverseFacts`,
  ## `bitSetCardFacts`, `mergeMemberships`' `holds`/`rewrite`, and the three
  ## site scans). Count-based, a function of the query alone, so a cut walk is
  ## the same on every host. It makes a unit of walker work cost about what a
  ## unit of Z3 work costs, so `walkRLimit` bounds wall time for every shape.
  ##
  ## Calibration (2026-11-09, one host, podman `nelli-dev`, charge set to 1 per
  ## visit so the log's last column counts visits, each test binary timed
  ## whole; Z3 units = log units - visits):
  ##   Z3 seconds per unit, arithmetic-heavy SUTs:
  ##     tsymex_augmented_assign   175.46M units in 46.6 s  = 0.266 us/unit
  ##     tsymex_0016_s8cj_mkunique  20.96M units in  5.07 s = 0.242 us/unit
  ##     tsymex_161_overflow_obligation 59.76M units in 15.1 s = 0.253 us/unit
  ##   (mean 0.254 us/unit, about 3.9M units/s on this host).
  ##   Walker seconds per visit, `tsymex_0016_k7_twosearch` (two binary
  ##   searches over a 450-entry const table; 3 walks, 4.0M Z3 units, 10.02M
  ##   visits, 41.2 s): (41.2 s - 4.0M * 0.254 us) / 10.02M = 4.0 us/visit
  ##   (build ~5.7, divRangeFacts ~4.2, mergeMemberships ~5.9, seqLenCaps ~2.2,
  ##   bvOffsetLinks ~1.7, bvIntInverseFacts ~1.8 us/term in the K7 profile).
  ##   Rate: 4.0 us/visit / 0.254 us/unit = 15.7 units per visit; 15 is used
  ##   (the profile's passes are lighter than the mean in the cheap ones, and
  ##   a pass not yet charged adds slack the other way). Before the charge
  ##   the same walk ran 106k units/s (94 s for 10M units); with it the
  ##   walk's units/s is within the arithmetic shapes' (see
  ##   `tests/tsymex_0016_k7_twosearch.nim`).

const walkerContextUnits* = 20_000
  ## RFC-0016 int6 D1b. Units charged per own-context solver
  ## (`ownContextSolver`): the fixed cost of one check that neither Z3's step
  ## count nor the term visits count -- the fresh Z3 context, the solver and
  ## its parameters, the check's own overhead, the context's teardown, and
  ## the per-query passes' fixed set-up. Count-based (one per solver built),
  ## so a cut walk is the same on every host. On the same scale as
  ## `walkerTermUnits`: a unit is about 0.254 us of wall.
  ##
  ## Why: a k-unroll of small queries is made of that cost. The `filterIt`
  ## over a `seq[seq[int]]` parameter (`tsymex_0016_k9cg_unbacked_p`) is
  ## ~1.5k Z3 units and ~430 term visits a query and ~12x the queries per
  ## unroll step; without this charge it was charged about 1M units a second
  ## of wall against the calibrated 3.9M, so `walkRLimit` was ~1,000 s of
  ## that shape and its unroll-5 walk ran to the 600 s stall backstop.
  ##
  ## Calibration (int6 D1b, 2026-11-19, podman `nelli-dev`, c, walk time
  ## only, one solver per query in both walks): wall = a * solvers + b *
  ## visits + 0.254 us * Z3 units, fitted to two shapes at the two ends of
  ## the visits-per-query range:
  ##   filterIt unroll 3 (`tsymex_0016_int6_d1b_walkbudget`): 426 solvers,
  ##     184,857 visits, 616,699 Z3 units, 3,622 ms
  ##   `tsymex_0016_k7_twosearch`'s third walk: 83 solvers, 659,473 visits,
  ##     219,661 Z3 units, 2,991 ms
  ## gives b = 3.6 us/visit (`walkerTermUnits`' 15 stays: 3.6 / 0.254 =
  ## 14.3) and a = 6.56 ms/solver = 25,800 units; 25,000 is used. The fit
  ## predicts filterIt unroll 4 (3,906 solvers, 2,341,468 visits, 8.65M Z3
  ## units) at 36 s; it ran 42-57 s on a loaded host. In the instrumented
  ## build the context alone (`newContext`) was 2.2 ms of filterIt's 6.6 and
  ## `mergeMemberships`' fixed set-up 1.6 ms.
  ##
  ## Re-measured for int6 D1d (2026-11-19, the same method and host, each
  ## suite run alone): `mergeMemberships` now returns a query holding no
  ## membership literal at once, and a pruning check a kept model satisfies
  ## is not searched (`refuteStatus`), so the walks' solvers are fewer:
  ##   filterIt unroll 3: 270 solvers, 170,863 visits, 338,515 Z3 units,
  ##     2,033 ms
  ##   `tsymex_0016_k7_twosearch`'s third walk: 58 solvers, 563,532 visits,
  ##     167,159 Z3 units, 2,094 ms
  ## gives b = 3.1 us/visit (15 stays) and a = 5.25 ms/solver = 20,666 units;
  ## 20,000 is used. What is left of a solver is Z3's own: a fresh context
  ## and its teardown about 1.8 ms and the default solver's set-up and check
  ## about 1.5 ms on a trivial query (a micro-benchmark, the same image),
  ## the rest the per-query passes. The context stays fresh: it is what
  ## makes a search a function of its query (RFC-0005 S8bm; `refuteStatus`).

template chargeWalkerTerms*(n: int) =
  ## One count-based charge (a function of the query's terms alone, so the
  ## verdict is the same on every host).
  walkerWorkUnits += n * walkerTermUnits

proc isBitSetCard*(ctx: Z3Context; id: int): bool =
  ## RFC-0016 INT-62. `id` is a `card` term of `ctx` (`bsCard`): AST ids
  ## are per context, and the registry is the thread's, so an id alone may
  ## name another context's count. Within a run every lookup is the run's
  ## context and the registry is cleared when that context is made
  ## (`resetSymexRunState`); the check keeps a lookup from any other context
  ## (a probe, a query's own context, a caller's) from reading one.
  id in bitSetCardIds and bitSetCardSets[id].s.ctx.raw == ctx.raw

proc queryMentionsBitSetCard*(ctx: Z3Context; roots: openArray[Z3Bool]): bool =
  ## RFC-0005 S8bq. Some term of `roots` is a builtin set's `card`.
  if bitSetCardIds.len == 0: return false
  var seen: HashSet[int]
  var stack: seq[RawZ3Ast]
  for r in roots: stack.add r.raw
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if isBitSetCard(ctx, id): return true
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, t)
    for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
      stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
  false

proc bsPopcount*(s: Z3AnyAst; n: int): Z3BitVec[64] =
  ## The number of set bits of the `n`-bit `s`, zero-extended to 64 bits: a
  ## balanced adder tree whose width grows by one bit per level (a sum of
  ## `2^k` bits fits in `k + 1`), so a 256-bit set costs a few hundred
  ## narrow adders, not 255 64-bit ones.
  let c = s.ctx
  var terms: seq[Z3AnyAst]
  for i in 0 ..< n:
    terms.add wrap[Z3AnyAst](c, c.checkErr Z3_mk_extract(
      c.raw, cuint(i), cuint(i), s.raw))
  var w = 1
  while terms.len > 1:
    var next: seq[Z3AnyAst]
    var i = 0
    while i < terms.len:
      let a = wrap[Z3AnyAst](c, c.checkErr Z3_mk_zero_ext(c.raw, 1, terms[i].raw))
      if i + 1 < terms.len:
        let b = wrap[Z3AnyAst](c, c.checkErr Z3_mk_zero_ext(
          c.raw, 1, terms[i + 1].raw))
        next.add bsBin(Z3_mk_bvadd, a, b)
      else:
        next.add a
      i += 2
    terms = next
    inc w
  if terms.len == 0: mkBitVec[64](0'i64)
  elif w >= 64: wrap[Z3BitVec[64]](c, terms[0].raw)
  else: wrap[Z3BitVec[64]](c, c.checkErr Z3_mk_zero_ext(c.raw, cuint(64 - w),
                                                       terms[0].raw))

proc bsCard*(s: Z3AnyAst; n: int): Z3BitVec[64] =
  ## `card(s)`: `bsPopcount`, registered (`bitSetCardIds`) with its set
  ## (`bitSetCardSets`, RFC-0005 S8bv) for `checkCapped`.
  result = bsPopcount(s, n)
  let c = s.ctx
  bitSetCardTerms.add result
  bitSetCardIds.incl astId(c, result.raw)
  bitSetCardSets[astId(c, result.raw)] = (s, n)

const maxCardSplitTerms* = 12
  ## RFC-0005 S8bv. The most `card` terms of one query `bitSetCardFacts`
  ## relates pairwise (66 pairs); a query with more relates its first 12.

proc bitSetCardFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8bv (item 3). For every two `card` terms `card(a)`,
  ## `card(b)` of one width in `roots`, the identities
  ##   card(a) == card(a and b) + card(a and not b)
  ##   card(b) == card(a and b) + card(b and not a)
  ## Valid for every `a`, `b` (each bit of `a` is in exactly one part), so
  ## the models are the query's own, as `divRangeFacts`'. They are what a
  ## bit-blasted comparison of two counts lacks: `card(s + {c}) > card(s) +
  ## 1` compares two adder trees over 256 related bits, a pigeonhole the
  ## SAT search does not finish (S8bq bounded it by `seqQueryRLimit`, so it
  ## was `sxUnknown`); with the parts named, the difference is a count of
  ## `{c} - s`, bit-local, and Z3 refutes it at once. Measured on Z3 5.1
  ## and 4.13.4 (RFC "As landed (S8bv)").
  if bitSetCardIds.len == 0: return
  var seen: HashSet[int]
  var stack: seq[RawZ3Ast]
  var found: seq[tuple[k: Z3BitVec[64], s: Z3AnyAst, n: int]]
  for r in roots: stack.add r.raw
  while stack.len > 0 and found.len < maxCardSplitTerms:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if isBitSetCard(ctx, id):
      let (sv, n) = bitSetCardSets[id]
      found.add (wrap[Z3BitVec[64]](ctx, t), sv, n)
      continue
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, t)
    for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
      stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
  for i in 0 ..< found.len:
    for j in i + 1 ..< found.len:
      let (ka, a, n) = found[i]
      let (kb, b, m) = found[j]
      if n != m: continue
      let both = bsPopcount(bsBin(Z3_mk_bvand, a, b), n)
      result.add ka == both + bsPopcount(bsBin(Z3_mk_bvand, a, bsNot(b)), n)
      result.add kb == both + bsPopcount(bsBin(Z3_mk_bvand, b, bsNot(a)), n)

proc lowerPtrCast*(env: Env, e: IRExpr): SymVal =
  ## RFC-0016 INT-83. An address reinterpreted between `pointer` and a typed
  ## sort (`pointerAddrOf` / `pointerAsTyped`, heap_model.nim's section on
  ## `pointer`). A run whose pointers are read as one sort and converted from
  ## or to another declines here (`heUnresolvedRef`, no answer: a
  ## stand-in there may disagree with a later read of the location): such a location would be
  ## read at two types, which the per-sort heap does not follow.
  let v = lower(env, e.pcArg)
  let toPointer = isPointerTy(e.pcTy)
  if v.kind notin {svRef, svPtr} or
     (v.kind == svRef and v.refPointee == nil) or
     (v.kind == svPtr and v.ptrPointee == nil):
    return degradeAlloc(e.pcTy, heUnresolvedRef,
      "`" & render(e) & "`: an address the walk does not hold as a ref or " &
        "ptr (RFC-0016 INT-83; heUnresolvedRef)", "__ptrCastDegrade")
  let ctx = requireCurrentContext()
  let ast = if v.kind == svRef: v.refAst else: v.ptrAst
  let srcPointee = if v.kind == svRef: v.refPointee else: v.ptrPointee
  let srcTid = refPointeeTypeId(srcPointee)
  let dstPointee = if e.pcTy.kind == itRef: e.pcTy.refPointeeTy
                   else: e.pcTy.ptrPointeeTy
  let dstTid = refPointeeTypeId(dstPointee)
  if srcTid == dstTid: return v
  proc punned(tid: string): SymVal =
    degradeAlloc(e.pcTy, heUnresolvedRef,
      "`" & render(e) & "`: pointers of this run are read as one type and " &
        "converted from or to another (`" & tid & "`); a location read at " &
        "two types is not modelled (RFC-0016 INT-83; heUnresolvedRef)",
      "__ptrCastDegrade")
  if toPointer:
    for t in pointerReadSorts:
      if t != srcTid: return punned(srcTid)
    let whole = v.kind == svRef and pointerWholeObject(ctx, ast.raw)
    crossSortEnter(srcTid)   # RFC-0016 INT-90 (`pointerSortsUsed`)
    SymVal(kind: svPtr, ptrFamily: true, ptrPointee: pointerPointeeTy(),
           ptrAst: pointerAddrOf(ctx, ast, srcPointee, whole))
  elif srcTid == pointerTypeId:
    for t in pointerSortsUsed:
      if t != dstTid: return punned(dstTid)
    crossSortEnter(dstTid)   # RFC-0016 INT-90 (`pointerSortsUsed`)
    pointerReadSorts.incl dstTid
    let typed = pointerAsTyped(ctx, ast, dstPointee)
    if e.pcTy.kind == itRef:
      SymVal(kind: svRef, refAst: typed, refPointee: dstPointee)
    else:
      SymVal(kind: svPtr, ptrAst: typed, ptrFamily: true, ptrPointee: dstPointee)
  else:
    punned(dstTid)

proc lowerBitSet*(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8bq (item 2). An `iekBitSet` operation. The arguments are
  ## lowered in order; an element is already converted to `T` (its range
  ## check is its own node). A set operand that did not lower to a builtin
  ## set (the stand-in of an earlier in-band decline) declines in-band.
  let elemTy = e.bsSetTy.bsElemTy
  let n = bitSetDomain(elemTy).size
  let ctx = requireCurrentContext()
  template fault(what: string): SymVal =
    queueDegrade(weInternalWalkerFault,
      "builtin set " & $e.bsOp & ": " & what & " (weInternalWalkerFault)")
    var fresh: seq[Z3Bool]
    let rty = case e.bsOp
              of bsoContains, bsoLe, bsoLt, bsoEq: tBool()
              of bsoCard: tInt()
              else: e.bsSetTy
    allocateSym(rty, freshDegradeName("__bitSetDegrade"), fresh)
  var sets: seq[Z3AnyAst]
  case e.bsOp
  of bsoLit:
    var acc = bsZero(ctx, n)
    var i = 0
    while i + 1 < e.bsArgs.len:
      let loCell = bsKeyCell(lower(env, e.bsArgs[i]))
      let hiCell =
        if e.bsArgs[i + 1] == e.bsArgs[i]: loCell
        else: bsKeyCell(lower(env, e.bsArgs[i + 1]))
      if loCell.isNone or hiCell.isNone:
        return fault("an element is not an ordinal")
      let (loIn, loAmt) = bsIndex(loCell.get, elemTy)
      if e.bsArgs[i + 1] == e.bsArgs[i]:
        acc = bsBin(Z3_mk_bvor, acc,
                    bsIte(loIn, bsSingle(ctx, n, loAmt), bsZero(ctx, n)))
      else:
        # `lo..hi`: the bits from `lo` up to `hi`, none when `hi < lo`.
        let (hiIn, hiAmt) = bsIndex(hiCell.get, elemTy)
        let ones = bsNot(bsZero(ctx, n))
        let fromLo = bsBin(Z3_mk_bvshl, ones, loAmt)
        let top = bsBin(Z3_mk_bvsub, bsRawNum(ctx, n, $(n - 1)), hiAmt)
        let toHi = bsBin(Z3_mk_bvlshr, ones, top)
        let nonEmpty = loIn and hiIn and bvsle(loCell.get, hiCell.get)
        acc = bsBin(Z3_mk_bvor, acc,
                    bsIte(nonEmpty, bsBin(Z3_mk_bvand, fromLo, toHi),
                          bsZero(ctx, n)))
      i += 2
    return bitSetSV(acc, elemTy)
  of bsoContains, bsoIncl, bsoExcl:
    let s = lower(env, e.bsArgs[0])
    let k = bsKeyCell(lower(env, e.bsArgs[1]))
    if s.kind != svBitSet: return fault("the set lowered to a " &
                                        plainEnglishSymValKind(s.kind))
    if k.isNone: return fault("the element is not an ordinal")
    let (inDom, amt) = bsIndex(k.get, elemTy)
    case e.bsOp
    of bsoContains:
      # Out of the domain a value is not a member (the key of a literal
      # set is not range-checked: `70000 in {1, 3}` is false).
      return SymVal(kind: svBool, bo: inDom and bsBit(s.bsRaw, amt))
    of bsoIncl:
      return bitSetSV(bsIte(inDom, bsBin(Z3_mk_bvor, s.bsRaw,
                                         bsSingle(ctx, n, amt)), s.bsRaw),
                      elemTy)
    else:
      return bitSetSV(bsIte(inDom, bsBin(Z3_mk_bvand, s.bsRaw,
                                         bsNot(bsSingle(ctx, n, amt))),
                            s.bsRaw), elemTy)
  else: discard
  for a in e.bsArgs:
    let sv = lower(env, a)
    if sv.kind != svBitSet:
      return fault("an operand lowered to a " & plainEnglishSymValKind(sv.kind))
    sets.add sv.bsRaw
  case e.bsOp
  of bsoUnion: bitSetSV(bsBin(Z3_mk_bvor, sets[0], sets[1]), elemTy)
  of bsoDiff:
    bitSetSV(bsBin(Z3_mk_bvand, sets[0], bsNot(sets[1])), elemTy)
  of bsoInter: bitSetSV(bsBin(Z3_mk_bvand, sets[0], sets[1]), elemTy)
  of bsoLe:
    SymVal(kind: svBool, bo: bsEqZ(bsBin(Z3_mk_bvand, sets[0], bsNot(sets[1])),
                                   bsZero(ctx, n)))
  of bsoLt:
    SymVal(kind: svBool,
           bo: bsEqZ(bsBin(Z3_mk_bvand, sets[0], bsNot(sets[1])),
                     bsZero(ctx, n)) and not bsEqZ(sets[0], sets[1]))
  of bsoEq: SymVal(kind: svBool, bo: bsEqZ(sets[0], sets[1]))
  of bsoCard: SymVal(kind: svBV64, signed: true, bv64: bsCard(sets[0], n))
  of bsoLit, bsoContains, bsoIncl, bsoExcl: fault("unreachable")

# ---- RFC-0005 S8bq (item 4): newSeqUninit's unwritten elements -------------
#
# `newSeqUninit[T](n)`'s elements are whatever the allocation held: a fresh
# data array (a base registered here) stands for them. Until S8bq the whole
# path was tainted at the call. Now a READ of an element is tainted, on the
# path where that element was never written: whether element `k` of a data
# array is an unwritten one is read off the array's term (`uninitAt`) --
# the base itself, a `store` (the slot written, holding a value that may
# itself be an unwritten element moved there, as `del`'s swap does) or an
# `ite` (a merge); any other term that mentions a base (a slice's lambda, a
# mapped array, a heap select) counts as unwritten, conservatively. Every
# element read goes through `isIndex`, `isSeqPop` (a path fork each) or
# `seqElemAt` (the inline HOFs, an in-band taint); a value bound by
# equality instead (`retBindEq`) declines.

var uninitSeqBases* {.threadvar.}: seq[Z3AnyAst]
  ## RFC-0005 S8bq. The data arrays `newSeqUninit` allocated in the running
  ## walk (held, so each keeps its id), and their ids. Reset at
  ## `runSymexImpl` entry.
var uninitSeqBaseIds* {.threadvar.}: HashSet[int]
var uninitSeqAliases* {.threadvar.}: Table[int, seq[tuple[guard: Z3Bool, data: Z3AnyAst]]]
  ## RFC-0005 S8bq. A call's result seq whose returned data mentions a base:
  ## the per-call `retSym` data symbol's id, and per return path the
  ## returned data with a fact that path's caller continuation implies (its
  ## branch conditions). `retBindEq` makes the two equal there, so element
  ## `k` of `retSym` is unwritten exactly where it is in the data returned.
var uninitAliasHeld* {.threadvar.}: seq[Z3AnyAst]
var uninitArrKinds* {.threadvar.}: tuple[ready: bool, store, ite, select, map: int]
  ## The linked Z3's decl kinds of `store`, `ite` and `select` (probed once
  ## per thread, as `seqCapKinds` does: the wrapper's enum binds only a
  ## subset).

const uninitReadKind* = feUnsupportedOpHavoc
  ## RFC-0005 S8bq. A read of an unwritten `newSeqUninit` element: a fresh
  ## value per evaluation (the base is fresh per call), a superset of what
  ## the allocation held; nothing is dropped (`dcFreshSymbol`).
const uninitReadMsg* = "newSeqUninit element read before it is written: " &
  "its value is unspecified — degraded to sxUnknown on that path"
const uninitReturnMsg* = "a call result holding a newSeqUninit seq in a shape the " &
  "walker does not match (a multi-axis variant) is not bound (its " &
  "unwritten elements would read as written) — path degraded to sxUnknown"

proc noteUninitSeqBase*(a: Z3AnyAst) =
  uninitSeqBases.add a
  uninitSeqBaseIds.incl astId(a.ctx, a.raw)

proc uninitKinds*(): tuple[store, ite, select, map: int] =
  if not uninitArrKinds.ready:
    let ctx = probeContext()   # RFC-0005 S8bp (batch 7)
    proc kindOf(ctx: Z3Context; a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
    let arr = mkArrayVar[Z3Int, Z3Int](ctx, "__s8bq_kind_probe_arr")
    let i = mkIntVar(ctx, "__s8bq_kind_probe_i")
    let b = mkBoolVar(ctx, "__s8bq_kind_probe_b")
    let st = store(arr, i, i)
    let sel = select(arr, i)
    let it = ite(b, i, i)
    # RFC-0005 S8bv: an array map (`mapArray`, the axiom-path `map`).
    var intSort = ctx.checkErr Z3_mk_int_sort(ctx.raw)
    let f = ctx.checkErr Z3_mk_func_decl(ctx.raw,
      Z3_mk_string_symbol(ctx.raw, "__s8bv_kind_probe_f"), 1,
      cast[ptr UncheckedArray[RawZ3Sort]](addr intSort), intSort)
    var arrRaw = arr.raw
    let mp = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_map(ctx.raw, f, 1,
      cast[ptr UncheckedArray[RawZ3Ast]](addr arrRaw)))
    uninitArrKinds = (true, kindOf(ctx, st.raw), kindOf(ctx, it.raw),
                      kindOf(ctx, sel.raw), kindOf(ctx, mp.raw))
  (uninitArrKinds.store, uninitArrKinds.ite, uninitArrKinds.select,
   uninitArrKinds.map)

proc termDepth*(ctx: Z3Context; t: RawZ3Ast; cap = termWalkMaxDepth): int =
  ## RFC-0005 S8ct. The levels of applications in `t` (a leaf is 0), or `cap + 1`
  ## as soon as a path is known to pass `cap`. Takes no stack: this is what tells
  ## a recursive walk whether it can run.
  type Open = tuple[a: RawZ3Ast; id: int; next, height: int]
  proc numArgs(a: RawZ3Ast): int =
    if Z3_get_ast_kind(ctx.raw, a) == Z3_APP_AST:
      int(Z3_get_app_num_args(ctx.raw, Z3_to_app(ctx.raw, a)))
    else: 0
  var heights: Table[int, int]
  var open: seq[Open] = @[(a: t, id: astId(ctx, t), next: 0, height: 0)]
  while open.len > 0:
    if open.len > cap + 1: return cap + 1
    let i = open.high
    if open[i].next < numArgs(open[i].a):
      let arg = Z3_get_app_arg(ctx.raw, Z3_to_app(ctx.raw, open[i].a),
                               cuint(open[i].next))
      inc open[i].next
      let id = astId(ctx, arg)
      if id in heights:
        open[i].height = max(open[i].height, heights[id] + 1)
      else:
        open.add (a: arg, id: id, next: 0, height: 0)
    else:
      let done = open.pop()
      heights[done.id] = done.height
      if open.len > 0:
        open[^1].height = max(open[^1].height, done.height + 1)
      else:
        result = done.height

proc termTooDeep*(ctx: Z3Context; t: RawZ3Ast): bool =
  ## RFC-0005 S8ct. `t` is past what a recursive walk may take.
  termDepth(ctx, t) > termWalkMaxDepth


proc mentionsUninitBase*(sc: var UninitScan; root: RawZ3Ast): bool =
  ## Some subterm of `root` (a quantifier's body included: a slice is a
  ## lambda over its base) is a `newSeqUninit` base.
  if uninitSeqBaseIds.len == 0: return false
  let ctx = sc.ctx
  let rootId = astId(ctx, root)
  if rootId in sc.mentions: return sc.mentions[rootId]
  var seen: HashSet[int]
  var stack = @[root]
  result = false
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    if id in uninitSeqBaseIds or id in uninitSeqAliases or
       sc.mentions.getOrDefault(id, false):
      result = true
      break
    case Z3_get_ast_kind(ctx.raw, t)
    of Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, t)
      for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
        stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
    of Z3_QUANTIFIER_AST:
      stack.add Z3_get_quantifier_body(ctx.raw, t)
    else: discard
  sc.mentions[rootId] = result

proc uninitAt*(sc: var UninitScan; arr: RawZ3Ast; k: Z3Int): Z3Bool

proc uninitVal*(sc: var UninitScan; v: RawZ3Ast): Z3Bool =
  ## The stored value `v` is an unwritten element moved verbatim (a select
  ## of one, as `del`'s swap stores). A value computed from elements was
  ## computed by reads, each tainted where it read an unwritten one.
  let ctx = sc.ctx
  if Z3_get_ast_kind(ctx.raw, v) == Z3_APP_AST:
    let app = Z3_to_app(ctx.raw, v)
    if ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app))) ==
         uninitKinds().select and
       Z3_get_app_num_args(ctx.raw, app) == 2 and
       sc.mentionsUninitBase(Z3_get_app_arg(ctx.raw, app, 0)):
      let ix = wrap[Z3Int](ctx, Z3_get_app_arg(ctx.raw, app, 1))
      return sc.uninitAt(Z3_get_app_arg(ctx.raw, app, 0), ix)
  mkBool(ctx, false)

proc uninitAt*(sc: var UninitScan; arr: RawZ3Ast; k: Z3Int): Z3Bool =
  ## Element `k` of the data array `arr` is an unwritten `newSeqUninit`
  ## element.
  let ctx = sc.ctx
  if not sc.mentionsUninitBase(arr): return mkBool(ctx, false)
  let key = (astId(ctx, arr), astId(ctx, k.raw))
  if key in sc.at: return sc.at[key]
  result = mkBool(ctx, true)
  # RFC-0005 S8ct: a chain past the limit may hold an unwritten element.
  if sc.depth >= termWalkMaxDepth: return
  inc sc.depth
  defer: dec sc.depth
  if key[0] in uninitSeqAliases:
    var acc = mkBool(ctx, false)
    for (g, d) in uninitSeqAliases[key[0]]:
      acc = acc or (g and sc.uninitAt(d.raw, k))
    result = acc
  elif key[0] notin uninitSeqBaseIds and
     Z3_get_ast_kind(ctx.raw, arr) == Z3_APP_AST:
    let app = Z3_to_app(ctx.raw, arr)
    let kind = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app)))
    let kinds = uninitKinds()
    if Z3_get_app_num_args(ctx.raw, app) == 3:
      if kind == kinds.store:
        let j = wrap[Z3Int](ctx, Z3_get_app_arg(ctx.raw, app, 1))
        result = ite(k == j, sc.uninitVal(Z3_get_app_arg(ctx.raw, app, 2)),
                     sc.uninitAt(Z3_get_app_arg(ctx.raw, app, 0), k))
      elif kind == kinds.ite:
        let c = wrap[Z3Bool](ctx, Z3_get_app_arg(ctx.raw, app, 0))
        result = ite(c, sc.uninitAt(Z3_get_app_arg(ctx.raw, app, 1), k),
                     sc.uninitAt(Z3_get_app_arg(ctx.raw, app, 2), k))
    elif kind == kinds.map:
      # RFC-0005 S8bv: an array map (the axiom-path `map`): element `k` is
      # `f` of element `k` of each operand, unwritten where one is.
      var acc = mkBool(ctx, false)
      for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
        acc = acc or sc.uninitAt(Z3_get_app_arg(ctx.raw, app, cuint(i)), k)
      result = acc
    elif kind == kinds.select and Z3_get_app_num_args(ctx.raw, app) == 2:
      # RFC-0005 S8bv: a heap cell (a ref object's seq field): `select(H,
      # r)` over the field's heap array, read through its stores and merges
      # to the data array stored for `r`.
      let h = Z3_get_app_arg(ctx.raw, app, 0)
      let r = Z3_get_app_arg(ctx.raw, app, 1)
      if Z3_get_ast_kind(ctx.raw, h) == Z3_APP_AST:
        let happ = Z3_to_app(ctx.raw, h)
        let hk = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, happ)))
        template cell(hh: RawZ3Ast): RawZ3Ast =
          let t = wrap[Z3AnyAst](ctx, checkedSelect(ctx, hh, r))
          sc.held.add t
          t.raw
        if hk == kinds.store and Z3_get_app_num_args(ctx.raw, happ) == 3:
          let r1 = Z3_get_app_arg(ctx.raw, happ, 1)
          let same = wrap[Z3Bool](ctx, checkedEq(ctx, r, r1))
          result = ite(same,
                       sc.uninitAt(Z3_get_app_arg(ctx.raw, happ, 2), k),
                       sc.uninitAt(cell(Z3_get_app_arg(ctx.raw, happ, 0)), k))
        elif hk == kinds.ite and Z3_get_app_num_args(ctx.raw, happ) == 3:
          let c = wrap[Z3Bool](ctx, Z3_get_app_arg(ctx.raw, happ, 0))
          result = ite(c, sc.uninitAt(cell(Z3_get_app_arg(ctx.raw, happ, 1)), k),
                       sc.uninitAt(cell(Z3_get_app_arg(ctx.raw, happ, 2)), k))
  elif key[0] notin uninitSeqBaseIds and
       Z3_get_ast_kind(ctx.raw, arr) == Z3_QUANTIFIER_AST and
       Z3_is_lambda(ctx.raw, arr):
    # RFC-0005 S8bv: a slice, `lambda j. select(base, j + lo)`: element `k`
    # is the body at `j = k`, an element of the base moved verbatim.
    var kRaw = k.raw
    let body = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_substitute_vars(ctx.raw,
      Z3_get_quantifier_body(ctx.raw, arr), 1,
      cast[ptr UncheckedArray[RawZ3Ast]](addr kRaw)))
    sc.held.add body
    result = sc.uninitVal(body.raw)
  sc.at[key] = result

proc uninitReadCond*(seqSV: SymVal; idx: Z3Int): Option[Z3Bool] =
  ## RFC-0005 S8bq. When reading element `idx` of `seqSV` may read an
  ## unwritten `newSeqUninit` element: the condition under which it does.
  ## `none` when it certainly does not.
  if uninitSeqBaseIds.len == 0: return none(Z3Bool)
  var sc = UninitScan(ctx: seqSV.seqDataRaw.ctx) # [placeholder-audited]
  if not sc.mentionsUninitBase(seqSV.seqDataRaw.raw): # [placeholder-audited]
    return none(Z3Bool)
  let u = sc.uninitAt(seqSV.seqDataRaw.raw, idx) # [placeholder-audited]
  if $simplify(u) == "false": none(Z3Bool) else: some(u)

proc svMentionsUninit*(sv: SymVal): bool

proc noteUninitReturn*(retSym, retVal: SymVal; pc: seq[Z3Bool]): bool =
  ## RFC-0005 S8bq. Binding the call result `retSym` to the returned
  ## `retVal` by equality: for each seq in `retVal` whose data mentions a
  ## `newSeqUninit` base, record the matching seq of `retSym` as its alias
  ## on this return path (`uninitSeqAliases`). RFC-0005 S8bv: the seqs are
  ## matched through tuples, objects, arrays, variants and distinct types
  ## (S8bq matched a seq result only, and declined one nested in a
  ## composite). True when every such seq was matched (and at least one
  ## was); false when none mentions a base, or one has no counterpart in
  ## `retSym` (the caller declines that binding).
  if uninitSeqBaseIds.len == 0: return false
  let ctx = requireCurrentContext()
  var sc = UninitScan(ctx: ctx)
  var g = mkBool(ctx, true)
  for c in pc: g = g and c
  var noted = false
  proc pairUp(a, b: SymVal): bool =
    ## `a` (of `retSym`) and `b` (of `retVal`): every base-mentioning seq
    ## of `b` aliased by its counterpart in `a`.
    case b.kind
    of svSeq:
      if not sc.mentionsUninitBase(b.seqDataRaw.raw): return true # [placeholder-audited]
      if a.kind != svSeq: return false
      let id = astId(ctx, a.seqDataRaw.raw) # [placeholder-audited]
      uninitAliasHeld.add a.seqDataRaw # [placeholder-audited]
      uninitSeqAliases.mgetOrPut(id, @[]).add (g, b.seqDataRaw) # [placeholder-audited]
      noted = true
      true
    of svTuple:
      if a.kind != svTuple or a.fields.len != b.fields.len: return false
      for i in 0 ..< b.fields.len:
        if not pairUp(a.fields[i], b.fields[i]): return false
      true
    of svArray:
      if a.kind != svArray or a.arrElems.len != b.arrElems.len: return false
      for i in 0 ..< b.arrElems.len:
        if not pairUp(a.arrElems[i], b.arrElems[i]): return false
      true
    of svVariant:
      if a.kind != svVariant or a.vPlainFields.len != b.vPlainFields.len:
        return false
      for i in 0 ..< b.vPlainFields.len:
        if not pairUp(a.vPlainFields[i], b.vPlainFields[i]): return false
      for tag, fs in b.vArmFields:
        if not a.vArmFields.hasKey(tag) or a.vArmFields[tag].len != fs.len:
          return false
        for i in 0 ..< fs.len:
          if not pairUp(a.vArmFields[tag][i], fs[i]): return false
      true
    of svDistinct:
      if b.distinctBaseSym == nil: return true
      if a.kind != svDistinct or a.distinctBaseSym == nil: return false
      pairUp(a.distinctBaseSym[], b.distinctBaseSym[])
    else:
      # A multi-axis variant (or anything else) holding one: not matched.
      not svMentionsUninit(b)
  pairUp(retSym, retVal) and noted

proc svMentionsUninit*(sv: SymVal): bool =
  ## RFC-0005 S8bq. Some data array of `sv` (a seq, or one inside a
  ## composite) mentions a `newSeqUninit` base. A call result bound to such
  ## a value by equality (`retBindEq`) would lose the base, so its reads
  ## would no longer see the unwritten elements: those bindings decline.
  if uninitSeqBaseIds.len == 0: return false
  var sc = UninitScan(ctx: requireCurrentContext())
  var stack = @[sv]
  while stack.len > 0:
    let v = stack.pop()
    case v.kind
    of svSeq:
      if sc.mentionsUninitBase(v.seqDataRaw.raw): return true # [placeholder-audited]
    of svTuple: stack.add v.fields
    of svArray: stack.add v.arrElems
    of svVariant:
      for fs in v.vArmFields.values: stack.add fs
      stack.add v.vPlainFields
    of svMultiVariant:
      for ax in v.mvAxes:
        for fs in ax.armFields.values: stack.add fs
      stack.add v.mvPlainFields
    of svDistinct: stack.add v.distinctBaseSym[]
    else: discard
  false

proc shiftCountBV*(r: SymVal, lhsKind: SVKind): SymVal =
  ## RFC-0005 S8ac. The count of a Nim `shl`/`shr` as the C backend really
  ## applies it. Nim 2.2.10's codegen masks the count with the operand
  ## width: `x shl n` emits `x << (n & (W-1))` and a signed `shr` emits
  ## `x >> (n & (W-1))` (probed, c and cpp, debug and release: `5 shl 64
  ## == 5`, `5 shl 65 == 10`, `n = -1` shifts by `W-1`; int8/16/32 mask by
  ## 7/15/31). Z3's `bvshl`/`bvlshr`/`bvashr` instead saturate a count
  ## `>= W` (to 0 / the sign fill), which let a witness `x shl 64 == 0`
  ## through that the compiled program never reaches. The mask is taken on
  ## the count's own bit pattern, whose low `log2 W` bits are exactly
  ## `n & (W-1)` for any count width and sign, and the masked value
  ## (0..63) is then moved to the operand's width without loss.
  let w = case lhsKind
          of svBV8: 8
          of svBV16: 16
          of svBV32: 32
          else: 64
  let m = int64(w - 1)
  let masked = case r.kind
    of svBV8:  SymVal(kind: svBV8,  signed: false, bv8:  r.bv8  and mkBitVec[8](m))
    of svBV16: SymVal(kind: svBV16, signed: false, bv16: r.bv16 and mkBitVec[16](m))
    of svBV32: SymVal(kind: svBV32, signed: false, bv32: r.bv32 and mkBitVec[32](m))
    of svBV64: SymVal(kind: svBV64, signed: false, bv64: r.bv64 and mkBitVec[64](m))
    else: raiseAssert "shiftCountBV: non-BV shift count: " & $r.kind
  let rw = case r.kind
           of svBV8: 8
           of svBV16: 16
           of svBV32: 32
           else: 64
  if rw == w: masked
  elif rw > w: truncBV(masked, w, false)
  else: lowerConvIntWidth(masked, w, false)

proc lowerConvIntTrunc*(sv: SymVal, tgtWidth: int, tgtSigned: bool): SymVal =
  ## RFC-0005 S8j. An unchecked narrowing conversion -- an unsigned target
  ## (`uint8(x)`, `byte(x)`, `uint32(x)` of a wider int). Nim keeps the low
  ## `tgtWidth` bits and never raises (probed: `uint8(300) == 44`,
  ## `uint16(-1) == 65535`). A BV operand truncates (`truncBV`). An
  ## Int-sorted operand (an `isIntOffset`-promoted param) has no bit
  ## pattern; its low bits are the value modulo `2^tgtWidth`, which Z3's
  ## `mod` (Euclidean: non-negative for a positive divisor) gives exactly.
  ## Anything else is a placeholder with nothing to convert.
  case sv.kind
  of svBV64, svBV32, svBV16:
    let w = case sv.kind
            of svBV64: 64
            of svBV32: 32
            else: 16
    if tgtWidth < w: truncBV(sv, tgtWidth, tgtSigned)
    else: lowerConvIntReinterpret(sv, tgtWidth, tgtSigned)
  of svInt:
    SymVal(kind: svInt, zi: sv.zi mod mkZ3IntLit(1'i64 shl tgtWidth),
           ziWidth: tgtWidth, ziSigned: tgtSigned)
  else:
    sv

proc lowerConvIntRange*(sv: SymVal, e: IRExpr): SymVal =
  ## RFC-0005 S8i. An integer conversion to a `range` (or enum) target:
  ## `Natural(x)`, `Positive(x)`, `range[a..b](x)`, `R(x)` for a subrange
  ## `R`, `E(x)` for an enum `E`. Nim checks the operand's VALUE against the
  ## target's bounds and raises `RangeDefect` outside them ("value out of
  ## range: -1 notin 0 .. 9223372036854775807" for `Natural(-1)`; probed on
  ## the pinned toolchain, c and cpp), then converts. The check's negation
  ## goes to the `rangeDefectConds` sink (acRange-gated in its drain, as
  ## S8g's float -> range check is); the value is converted to the target's
  ## width, which is exact wherever the check passes. Before S8i the whole
  ## conversion was an identity pass-through: no check, and an out-of-range
  ## value flowed on as the target type.
  ##
  ## The bounds are clamped to the operand's own type first, so each
  ## literal fits the width it is compared at (`Positive(x)` of an `int8`
  ## compares against 1 .. 127, never a truncated `high(int)`).
  let bvW = case sv.kind
            of svBV8: 8
            of svBV16: 16
            of svBV32: 32
            of svBV64: 64
            else: 0
  let (w, sgn) =
    if sv.kind == svInt and sv.ziWidth != 0: (sv.ziWidth, sv.ziSigned)
    elif bvW != 0: (bvW, sv.signed)
    else: (e.ciwSrcWidth, e.ciwSrcSigned)
  let (sMin, sMax) =
    if sgn: intBounds(w)
    elif w < 64: (0'i64, (1'i64 shl w) - 1)
    else: (0'i64, high(int64))   # a u64 above this still needs the check
  let lo = max(e.ciwLo, sMin)
  let hi = min(e.ciwHi, sMax)
  var conds: seq[Z3Bool]
  if lo > hi:
    conds = @[mkBool(false)]
  elif sv.kind == svInt:
    conds = @[sv.zi >= mkZ3IntLit(lo), sv.zi <= mkZ3IntLit(hi)]
  elif lo != sMin or hi != sMax or (not sgn and w == 64):
    # [range-invariant: range-defect-check -- the target's bounds are the
    # conversion's defect CONDITION, not a path constraint on a stored
    # value, so `rangeCondsIfNeeded` is not the applicable helper]
    conds = bvRangeConds(sv, lo, hi, sgn)  # [range-invariant: range-defect-check]
  if e.ciwHoley: enumHolesMade = true   # RFC-0016 INT-84: a hole may result
  if conds.len > 0:
    when defined(symexTestInjectWalkerFault):
      injectShapeFault("conds")  # RFC-0005 S8ce: a local seq[Z3Bool] held
    var inRange = conds[0]
    for i in 1 ..< conds.len: inRange = inRange and conds[i]
    syncRangeDefectCond(not inRange)
  let tw = e.ciwTgtWidth
  if sv.kind == svInt:
    SymVal(kind: svInt, zi: sv.zi, ziWidth: tw, ziSigned: e.ciwTgtSigned,
           ziIvl: sv.ziIvl)
  elif bvW == 0:
    sv    # a non-integer placeholder: nothing to convert (honest-incomplete)
  elif tw > w:
    lowerConvIntWidth(sv, tw, e.ciwTgtSigned)
  elif tw < w:
    truncBV(sv, tw, e.ciwTgtSigned)
  else:
    lowerConvIntReinterpret(sv, tw, e.ciwTgtSigned)

proc symEq*(a, b: SymVal): Z3Bool =
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
    raise newException(ValueError,  # [raise-audited: category-c: index-must-be-int invariant (both call sites are the same array-index ite-fold, operands always int-family)]
      "symEq: not a primitive — got " & $a.kind)

func isClosureTy*(t: IRType): bool =
  ## RFC-0005 S8z. The proc-valued type `classifyType` maps to the
  ## `__closure` placeholder.
  t != nil and t.kind == itUninterp and t.uninterpName == "__closure"

func retCarriesClosure*(t: IRType): bool =
  ## RFC-0005 S8be. A return type holding a closure: the closure itself
  ## (S8z) or a tuple with one in some element. The call hands the
  ## returned value itself to the caller, per returned path; there is no
  ## symbol to bind it to (a closure has none).
  if isClosureTy(t): return true
  if t != nil and t.kind == itTuple:
    for f in t.fields:
      if retCarriesClosure(f): return true
  false

func closureValueBuilt*(v: SymVal; t: IRType): bool =
  ## RFC-0005 S8be. `v`, a value of the closure-carrying type `t`, holds a
  ## closure the walker built in every closure slot.
  if isClosureTy(t): return v.kind == svClosure
  if t != nil and t.kind == itTuple:
    if v.kind != svTuple or v.fields.len != t.fields.len: return false
    for i, f in t.fields:
      if retCarriesClosure(f) and not closureValueBuilt(v.fields[i], f):
        return false
  true

const retBindWiredKinds* = {svBool, svInt, svBV8, svBV16, svBV32, svBV64,
                           svFloat32, svFloat64, svString, svTuple, svVariant,
                           svMultiVariant, svSeq, svDistinct, svArray,
                           svRef, svPtr, svTable, svSet, svBitSet}
  ## The value kinds `retBindEq` binds structurally; the two call-return
  ## drains (`completeReturn`, the `isCall` fall-through) decline any other
  ## (`feUnsupportedOpHavoc`). RFC-0005 S8p added `svMultiVariant`, `svSeq`
  ## and `svDistinct`, and made it one set (each drain had its own copy).
  ## RFC-0005 S8s added `svArray`; S8u `svRef`, `svPtr`, `svTable`, `svSet`;
  ## S8bq `svBitSet`.

proc armSelected*(disc: SymVal; tagOrd: int;
                 arms: OrderedTable[int, seq[SymVal]]): Z3Bool =
  ## RFC-0005 S8s. `disc` selects the arm keyed `tagOrd` among a `case`
  ## section's arms (`arms`, keyed by tag ordinal). An `else` arm is keyed by the
  ## sentinel -1 and selected exactly when no explicit arm is -- the same
  ## membership `isVariantField` reads an else-arm field under. A bare
  ## `variantDiscEq(disc, -1)` is never true for a legal discriminator.
  if tagOrd >= 0: return variantDiscEq(disc, int64(tagOrd))
  result = mkBool(true)
  for t in arms.keys:
    if t >= 0: result = result and not variantDiscEq(disc, int64(t))

proc retBindKindsAgree*(retSym, retVal: SymVal): bool =
  ## RFC-0005 S8u. True when `retBindEq` can bind `retVal` to `retSym` at the
  ## top level: the same kind once a `distinct` is ejected and mixed int
  ## representations are reconciled. The call-return drains check it with
  ## `retBindWiredKinds`, so a disagreeing pair takes their path-level
  ## `feUnsupportedOpHavoc` decline (the path is forked tainted) instead of
  ## `retBindEq`'s lowering-sink backstop.
  let a = if retSym.kind == svDistinct: ejectBase(retSym) else: retSym
  let b = if retVal.kind == svDistinct: ejectBase(retVal) else: retVal
  let (ra, rb) = reconcileInt(a, b)
  ra.kind == rb.kind

proc retBindEq*(retSym, retVal: SymVal): Z3Bool =
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
  ## Round-6 N3 (Low, defensive hardening, walker v106): `lowerArith`/
  ## `lowerCmp` both reconcile mixed svInt/svBV operand pairs via
  ## `reconcileInt` at their own top (B4, ADR-0028 Leg 1) before doing
  ## anything else with `.kind` — this proc's tuple/variant arms below
  ## already call `reconcileInt` per-field for exactly that reason, but the
  ## SCALAR entry point (reached directly for a bare, non-tuple/variant
  ## return — e.g. B3's plain `return i` scan-offset shape, whose `retSym`
  ## is allocated `svInt` via `freshRetSym`'s `intOffsetPositions = @[0]`)
  ## had no equivalent bridge: a `retVal` that arrived BV-represented
  ## instead of the `svInt` `retSym` expected would hit the bare kind check
  ## below and abort via `doAssert` (an uncatchable-by-`CatchableError`
  ## `AssertionDefect`) rather than degrading like every neighboring arm's
  ## own `raise newException(ValueError, ...)`. PROVEN UNREACHABLE in valid
  ## Nim today — the counter feeding an offset-shaped return is always
  ## int-typed, `collectIntOffsetParams`/`collectIntOffsetLiteralLocals`
  ## only ever trace a bare `nnkSym` (never introducing a representation
  ## mismatch on their own), and `iekConvIntWidth` is strictly widening
  ## (never narrows into a mismatched kind) — added defensively, for
  ## symmetry with `lowerArith`/`lowerCmp`'s own bridge, with no repro
  ## constructed (see the round's test file for the "defensive, no repro
  ## possible" note). `reconcileInt` is an identity no-op whenever the two
  ## kinds already match (including every non-int-family kind — bool,
  ## float, string, tuple, variant, …), so this is a pure addition: no
  ## existing call site's observed behavior changes.
  if retSym.kind == svDistinct or retVal.kind == svDistinct:
    # RFC-0005 S8p: a `distinct T` binds through its ejected base. `D(3)` is
    # the parser's identity pass-through (a plain base value), and every
    # read of a distinct value ejects to the base (`ejectBase`, `svLeafEq`),
    # so the base is the whole observable value. Before S8p a callee
    # assigning `result = D(3)` met the `svDistinct` `retSym` here with a
    # base-kinded value: the kind-mismatch raise below, reported as
    # `weInternalWalkerFault`.
    return retBindEq(ejectBase(retSym), ejectBase(retVal))
  let (retSym, retVal) = reconcileInt(retSym, retVal)
  if retSym.kind != retVal.kind:
    # N3: a classified decline (mirrors the `svSeq`/final-`else` arms below),
    # not the `doAssert` this replaces — a genuine, still-mismatched kind
    # after reconciliation is exactly as "should never happen" as before,
    # but now fails the same catchable way every neighboring arm does.
    #
    # RFC-0005 S8u: in-band now, as the composite catch-all below. It was
    # reachable: a callee whose `result` was an in-band degrade's stand-in
    # (a field write on a `result` with no modelled zero value read the
    # unmodelled global `result`, an int) met a composite `retSym` here, and
    # the raise surfaced as `weInternalWalkerFault`. The stand-in's own
    # degrade already taints the path; this records the unbound return.
    allocDegrade(feUnsupportedOpHavoc,
      "retBindEq: returned value's kind " & plainEnglishSymValKind(retVal.kind) &
      " does not match the result's " & plainEnglishSymValKind(retSym.kind) &
      " — result left unbound (feUnsupportedOpHavoc)")
    return mkBool(true)
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
    ## read-taint owns honesty). A GENUINE (non-placeholder) `svSeq` binds
    ## its length and data (RFC-0005 S8p, below).
    if retSym.isUnsupportedFieldPlaceholder or retVal.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      mkBool(true)
    else:
      # RFC-0005 S8p: a genuine seq binds its length and its data array.
      # `retSym` is a fresh seq per call (or per closure occurrence), so
      # equating the whole data array constrains nothing but its own
      # leaves; the elements past the length are never read. Before S8p
      # this was an in-band `feUnsupportedOp` decline (N46): a seq-returning
      # callee, or a closure returning a seq, could not return a value.
      # RFC-0005 S8bc: every data array of a tree element, pairwise (a
      # value of another depth's layout is conformed first, `conformSV`).
      let ctx = retSym.seqLen.ctx # [placeholder-audited]
      let rv = conformSV(retVal, tSeq(retSym.seqElemTy))
      let ra = seqArrs(retSym)
      if rv.isNone or seqArrs(rv.get).len != ra.len:
        degradeAlloc(tBool(), seRecursiveValueDepth,
          "retBindEq: a seq value of another layout than the result's (" &
          $retSym.seqElemTy & ") -- seRecursiveValueDepth",
          "__retBindSeqLayout").bo
      else:
        let va = seqArrs(rv.get)
        var acc = (retSym.seqLen == retVal.seqLen) # [placeholder-audited]
        for i in 0 ..< ra.len:
          acc = acc and wrap[Z3Bool](ctx, checkedEq(ctx, ra[i].raw, va[i].raw))
        acc
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
      # RFC-0005 S8s: `armSelected`, not `variantDiscEq(disc, tagOrd)`: an
      # `else` arm's key is -1, which no discriminator equals, so its fields
      # were never bound (a free result wherever the else arm was active).
      acc = acc and armSelected(retSym.vDisc[], tagOrd,
                                retSym.vArmFields).implies(armEq)
    doAssert retSym.vPlainFields.len == retVal.vPlainFields.len,
      "retBindEq: variant plain-field arity mismatch " &
      $retSym.vPlainFields.len & " vs " & $retVal.vPlainFields.len
    for i in 0 ..< retSym.vPlainFields.len:
      let (fs, fv) = reconcileInt(retSym.vPlainFields[i], retVal.vPlainFields[i])
      acc = acc and retBindEq(fs, fv)
    # RFC-0016 PRC-07 slice B: the union's bytes bind too, data and which of
    # them no write reached (`freshRetSym` made the result's mask free).
    if retSym.vImage.len > 0 and retSym.vImage.len == retVal.vImage.len:
      for i in 0 ..< retSym.vImage.len:
        acc = acc and (retSym.vImage[i] == retVal.vImage[i])
    acc
  of svMultiVariant:
    ## RFC-0005 S8p: the `svVariant` encoding, once per axis -- each axis's
    ## discriminator equal, and each of its arms' fields equal under that
    ## axis's `disc == tag` -- plus the shared plain fields. Before S8p a
    ## multi-variant fell to the composite catch-all below
    ## (`feUnsupportedOp`), so a callee could not return one.
    doAssert retSym.mvObjectName == retVal.mvObjectName and
             retSym.mvAxes.len == retVal.mvAxes.len,
      "retBindEq: multi-variant mismatch " & retSym.mvObjectName & " vs " &
      retVal.mvObjectName
    var acc = mkBool(true)
    for ai, sAx in retSym.mvAxes:
      let vAx = retVal.mvAxes[ai]
      let (sDisc, vDisc) = reconcileInt(sAx.disc[], vAx.disc[])
      acc = acc and retBindEq(sDisc, vDisc)
      for tagOrd, symFields in sAx.armFields:
        let valFields = vAx.armFields[tagOrd]
        doAssert symFields.len == valFields.len,
          "retBindEq: multi-variant arm arity mismatch on axis " &
          sAx.discName & " tag " & $tagOrd
        var armEq = mkBool(true)
        for i in 0 ..< symFields.len:
          let (fs, fv) = reconcileInt(symFields[i], valFields[i])
          armEq = armEq and retBindEq(fs, fv)
        acc = acc and armSelected(sAx.disc[], tagOrd,
                                  sAx.armFields).implies(armEq)   # RFC-0005 S8s
    doAssert retSym.mvPlainFields.len == retVal.mvPlainFields.len,
      "retBindEq: multi-variant plain-field arity mismatch"
    for i in 0 ..< retSym.mvPlainFields.len:
      let (fs, fv) = reconcileInt(retSym.mvPlainFields[i], retVal.mvPlainFields[i])
      acc = acc and retBindEq(fs, fv)
    acc
  of svArray:
    ## RFC-0005 S8s: element-wise, as a tuple binds per field. An array
    ## value is a fixed list of element values (`arrElems`, one per index),
    ## and both sides come from the same `array[N, T]` type. Before S8s an
    ## array fell to the catch-all below: an array-returning callee's result
    ## was `feUnsupportedOpHavoc`.
    doAssert retSym.arrElems.len == retVal.arrElems.len,
      "retBindEq: array length mismatch " & $retSym.arrElems.len & " vs " &
      $retVal.arrElems.len
    var acc = mkBool(true)
    for i in 0 ..< retSym.arrElems.len:
      let (es, ev) = reconcileInt(retSym.arrElems[i], retVal.arrElems[i])
      acc = acc and retBindEq(es, ev)
    acc
  of svRef, svPtr:
    ## RFC-0005 S8u: a `ref` / `ptr` binds its address. The heap it points
    ## into is the path's (`heaps`, carried out of the callee by the return
    ## merge), so the caller reads what the callee wrote. `checkedEq` records
    ## a sort fault rather than build an ill-sorted equality. Before S8u a
    ## ref result was `feUnsupportedOpHavoc`, and a callee's `new(result)`
    ## a `weInternalWalkerFault` (the statement was not modelled).
    let (a, b) = if retSym.kind == svRef: (retSym.refAst, retVal.refAst)
                 else: (retSym.ptrAst, retVal.ptrAst)
    wrap[Z3Bool](a.ctx, checkedEq(a.ctx, a.raw, b.raw))
  of svTable:
    ## RFC-0005 S8u: a `Table[string, int]` binds its present and data
    ## arrays and its size (the whole value; `retSym` is fresh per call).
    let ctx = retSym.tabSize.ctx
    (retSym.tabSize == retVal.tabSize) and
      wrap[Z3Bool](ctx, checkedEq(ctx, retSym.tabPresentRaw.raw,
                                  retVal.tabPresentRaw.raw)) and
      wrap[Z3Bool](ctx, checkedEq(ctx, retSym.tabDataRaw.raw,
                                  retVal.tabDataRaw.raw)) and
      tabMoreEq(ctx, retSym, retVal)   ## RFC-0005 S8at
  of svBitSet:
    ## RFC-0005 S8bq: a builtin set binds its bit-vector.
    bsEqZ(retSym.bsRaw, retVal.bsRaw)
  of svSet:
    ## RFC-0005 S8u: a `HashSet[int]` binds its member array and size.
    let ctx = retSym.setSize.ctx
    (retSym.setSize == retVal.setSize) and
      wrap[Z3Bool](ctx, checkedEq(ctx, retSym.setMembersRaw.raw,
                                  retVal.setMembersRaw.raw))
  else:
    # N46 (round-6 re-review): was a raw `raise newException`. Reached for
    # a proc returning `Table[K,V]`/`HashSet[T]`/`ref`/`ptr` (RFC-0005 S8p
    # and S8s wired the multi-variant and the array, S8u the ref, ptr, table
    # and set) -- all ordinary Nim return-type
    # shapes, called from inside a loop reaches this unguarded. In-band
    # degrade: `mkBool(true)` mirrors the svSeq arm's own placeholder
    # idiom immediately above (sound vacuous binding).
    allocDegrade(feUnsupportedOp,
      "retBindEq: composite-typed proc return not yet wired — got " &
      plainEnglishSymValKind(retSym.kind))
    mkBool(true)

# ---------------------------------------------------------------------------


proc guardLiteral*(cond: Z3Bool): GuardLiteral =
  ## RFC-0005 S8bl. `cond` simplified to a literal, decided without the
  ## solver as `loopArmInfeasible` decides a loop guard. With a ground scan
  ## (a pinned input, a callee's ground result) most `if` guards fold, and
  ## walking the side a literal rules out forked every `if` in two: five
  ## folded guards in a loop body were 32 copies of one path per iteration.
  ## Sound: the side dropped carries a `false` conjunct, so no query on it
  ## is satisfiable.
  ## RFC-0005 S8bv: read off the term, not its printed form: printing a guard
  ## over a builtin set's unrolled counter (an `ite` chain sharing each step
  ## twice) did not finish in 400 s.
  let s = simplify(cond)
  case Z3_get_bool_value(s.ctx.raw, s.raw)
  of Z3_L_TRUE: glTrue
  of Z3_L_FALSE: glFalse
  else: glOpen

proc presenceRemoved*(cur, base: Z3AnyAst): Z3Bool =
  ## RFC-0005 S8bx (item 4). Whether a key present at `base` was taken out on
  ## the way to the presence array `cur`, through `ite` merges. RFC-0005 S8cn:
  ## as a term: a store of `false` removes a key only if the array under it
  ## holds it (Nim's `del` of an absent key is a no-op, `ra_live`); `true` when
  ## `cur` is reached otherwise (a fresh array, a callee's havoc), so the
  ## caller's "not removed" arm holds only on an all-`true` chain. Literally
  ## `false` when every store is `true`.
  let ctx = cur.ctx
  proc kindOf(a: RawZ3Ast): int =
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
  # The decl kinds of a store and an `ite`, read off well-sorted probes (as
  # `seqCapKinds` reads its kinds).
  let probeArr = mkArrayVar[Z3Bool, Z3Bool](ctx, "__s8bx_kind_probe_arr")
  let probeC = mkBoolVar(ctx, "__s8bx_kind_probe_c")
  let probeStore = wrap[Z3AnyAst](ctx, checkedStore(ctx, probeArr.raw,
    probeC.raw, probeC.raw))
  let probeIte = wrap[Z3AnyAst](ctx, checkedIte(ctx, probeC.raw,
    probeArr.raw, probeStore.raw))
  let storeKind = kindOf(probeStore.raw)
  let iteKind = kindOf(probeIte.raw)
  var steps = 0
  var memo: Table[RawZ3Ast, Z3Bool]
  proc go(t: RawZ3Ast): Z3Bool =
    if t == base.raw: return mkBool(ctx, false)
    if memo.hasKey(t): return memo[t]
    inc steps
    if steps > 100_000 or Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST:
      return mkBool(ctx, true)
    let app = Z3_to_app(ctx.raw, t)
    let k = kindOf(t)
    if k == storeKind and Z3_get_app_num_args(ctx.raw, app) == 3:
      let below = Z3_get_app_arg(ctx.raw, app, 0)
      let lit = guardLiteral(wrap[Z3Bool](ctx, Z3_get_app_arg(ctx.raw, app, 2)))
      let under = go(below)
      if lit == glTrue: result = under
      elif lit == glFalse:
        let held = wrap[Z3Bool](ctx, checkedSelect(ctx, below,
          Z3_get_app_arg(ctx.raw, app, 1)))
        result = if guardLiteral(under) == glFalse: held else: under or held
      else: result = mkBool(ctx, true)
    elif k == iteKind and Z3_get_app_num_args(ctx.raw, app) == 3:
      let a = go(Z3_get_app_arg(ctx.raw, app, 1))
      let b = go(Z3_get_app_arg(ctx.raw, app, 2))
      if guardLiteral(a) == glFalse and guardLiteral(b) == glFalse: result = a
      else:
        result = wrap[Z3Bool](ctx, checkedIte(ctx, Z3_get_app_arg(ctx.raw, app, 0),
                                              a.raw, b.raw))
    else:
      result = mkBool(ctx, true)
    memo[t] = result
  go(cur.raw)

proc freshRetSym*(ty: IRType, name: string, pcOut: var seq[Z3Bool],
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
  ## RFC-0005 S8z: an enum without ordinal 0 may hold 0 here
  ## (`allocEnumZeroLegal`).
  let saved = allocEnumZeroLegal
  allocEnumZeroLegal = true
  # RFC-0016 INT-84: a callee the walk does not see may return a hole.
  if hasHoleyEnum(ty): enumHolesMade = true
  result = allocateSym(ty, name, pcOut, intOffsetPositions = intOffsetPositions)
  allocEnumZeroLegal = saved
  # RFC-0016 PRC-07 slice B: which bytes of a returned variant no write
  # reached is the callee's to say (`retBindEq`), not determinate by default.
  if result.kind == svVariant and result.vImage.len > 0:
    let half = result.vImage.len div 2
    for i in 0 ..< half:
      result.vImage[half + i] = mkBitVecVar[64](name & ".@mask" & $i)

proc coerceIntLit*(proto: SymVal, ival: int64): SymVal =
  ## Build a SymVal representing literal `ival` at `proto`'s
  ## representation. Used when an `iekIntLit`'s Z3 representation
  ## must match a surrounding variable.
  # N47 (round-6 raise-class-audit category-d closure): the three non-numeric
  # `proto.kind` arms below (svUninterpRef, svBool, the composite list) are
  # RECLASSIFIED category-c under a single argument, the "typed-macro
  # invariant": `symexFind`/`symexFindAllWitnesses` (`symex.nim`) declare
  # their SUT parameter `fn: typed` — Nim fully sem-checks the procedure
  # (including every operator's operand types) BEFORE the macro body ever
  # runs, so `dsl_parser.nim`'s `classifyType`/`parseExpr` only ever see an
  # ALREADY TYPE-CHECKED Nim AST. `coerceIntLit`'s `proto` argument is, at
  # every one of its 4 call sites (enumerated: `lower`'s own `iekIntLit` arm,
  # ~4546 below, plus the three `isIndex`-family array-index sites,
  # ~5192/8268/8290, which are independently proven int-only by this SAME
  # file's own `index-must-be-int` category-c markers a few hundred lines
  # down, ~8276/8283), the SymVal of whatever Nim expression sits in the SAME static
  # position as the integer literal it is shaping. For Nim to have accepted
  # that program at all, the literal's position must have a type the literal
  # implicitly unifies with — and Nim's implicit literal-conversion rules
  # admit exactly {int8..int64, uint8..uint64, float32, float64} (floats
  # route to `iekFloatLit`, never reaching this proc) plus, transitively, a
  # `distinct` type whose OWN base resolves through that same numeric family
  # (the `svDistinct` arm just below recurses on exactly this). A `bool`,
  # any composite (seq/array/tuple/table/set/variant/closure/ref/ptr), or an
  # uninterpreted-ref value can NEVER be the well-typed counterpart of a bare
  # integer literal in Nim — not "not yet observed", but excluded by the
  # compiler pass that runs before this DSL ever sees the AST. (The
  # `iekIntLit` caller's own `proto.get.kind != svBool` guard, ~4530, predates
  # this argument and is now provably-redundant defense-in-depth, not
  # evidence the case was ever live — left in place rather than removed, to
  # avoid touching unrelated code this slice does not need to change.)
  case proto.kind
  of svUninterpRef:
    raise newException(ValueError, "symLit: svUninterpRef has no integer form (cluster E)")  # [raise-audited: category-c: verified-unreachable: typed-macro invariant (see this proc's own header comment above for the full argument)]
  of svFloat32:   ## Phase 15 F5: int literal in a float context -> float numeral
    SymVal(kind: svFloat32, fp32: mkFloat32(float32(ival)))
  of svFloat64:
    SymVal(kind: svFloat64, fp64: mkFloat64(float64(ival)))
  of svBV8:  liftBV(mkBitVec[8](ival),  proto.signed)
  of svBV16: liftBV(mkBitVec[16](ival), proto.signed)
  of svBV32: liftBV(mkBitVec[32](ival), proto.signed)
  of svBV64: liftBV(mkBitVec[64](ival), proto.signed)
  of svInt:
    ## R3 (S2): propagate the proto's width metadata onto the literal —
    ## e.g. a promoted counter `pos` used as `pos + 1`'s proto shapes the
    ## literal `1` at `pos`'s own `svInt` representation (`probeProto`);
    ## without this the literal operand would silently lose the width the
    ## surrounding expression needs to stay overflow-checkable.
    ## Issue #161 slice 2: a literal's interval is the singleton `[v, v]`
    ## — the one exact fact the analysis always has. It is what makes the
    ## common shapes (`pos + 1`, `i * 4`, `n - 1`) dischargeable at all:
    ## without it every increment on a promoted counter pays a solver fork.
    ## RFC-0005 S8aa: a `uint64` literal above `high(int64)` arrives as its
    ## two's-complement `int64` (`high(uint)` is -1). At an unsigned 64-bit
    ## proto its value is `ival + 2^64`, which no `Interval` holds. It was
    ## the negative numeral: `s.find('a').uint == high(uint)` was a false
    ## `sxUnsat` and `s.len.uint > high(uint) - 2` a false `sxSat`.
    if ival < 0 and proto.ziWidth == 64 and not proto.ziSigned:
      return SymVal(kind: svInt, zi: mkZ3IntLit(ival) + intWindow(64, false).span,
                    ziWidth: 64, ziSigned: false, ziIvl: none(Interval))
    SymVal(kind: svInt, zi: mkZ3IntLit(ival),
           ziWidth: proto.ziWidth, ziSigned: proto.ziSigned,
           ziIvl: some(interval(ival, ival)))
  of svBool:
    raise newException(ValueError,  # [raise-audited: category-c: verified-unreachable: typed-macro invariant (see coerceIntLit's first site above)]
      "coerceIntLit: bool prototype for integer literal")
  of svDistinct:   ## Phase 15 G4: coerce against the distinct's ejected base.
    coerceIntLit(proto.distinctBaseSym[], ival)
  of svTuple, svArray, svString, svSeq, svTable, svSet, svVariant,
     svMultiVariant, svClosure, svRef, svPtr, svBitSet:
    ## svClosure: Phase 15 C1; svRef/svPtr: Phase 15 R1a (never an int proto)
    raise newException(ValueError,  # [raise-audited: category-c: verified-unreachable: typed-macro invariant (see coerceIntLit's first site above)]
      "coerceIntLit: composite prototype for integer literal kind=" & $proto.kind)

proc bvIndexWindow*(idx: SymVal): tuple[mn, mx: int64] =
  ## RFC-0005 S8z. The values a BV index can hold under its signedness
  ## (an unsigned 64-bit one capped at `high(int64)`: no array spans more).
  let w = case idx.kind
    of svBV8: 8
    of svBV16: 16
    of svBV32: 32
    else: 64
  if idx.signed:
    (if w == 64: (low(int64), high(int64))
     else: (-(1'i64 shl (w - 1)), (1'i64 shl (w - 1)) - 1))
  else:
    (0'i64, (if w == 64: high(int64) else: (1'i64 shl w) - 1))

proc coerceArrayBoolIndex*(idx: SymVal): SymVal =
  ## RFC-0005 S8am (S8z's remainder, item 6): `array[bool, T]`'s index
  ## lowers to `svBool` (there is no other Nim value a `bool`-typed
  ## expression can produce), but `arrayIndexConds`/`arraySelect`/
  ## `arrayStore` only ever took an int-family `SymVal` -- every OTHER
  ## array index type lowers straight to one. Rather than teach those three
  ## shared helpers a fourth kind (they are also the `seq` index path's
  ## helpers, where a bool index can never arrive — `itSeq`'s index type is
  ## always int-family, enforced at classify time), coerce AT THE TWO
  ## CALLERS (`isIndex`/`isIndexAssign`, immediately below) before the
  ## index ever reaches them: `false`/`true` to Nim's own ordinal values
  ## 0/1, matching `arrayIndexBounds`'s `of itBool: lo = 0; hi = 1`.
  if idx.kind == svBool:
    SymVal(kind: svInt, zi: ite(idx.bo, mkZ3IntLit(1), mkZ3IntLit(0)))
  else:
    idx

proc arrayIndexConds*(idx: SymVal; lo: int64; n: int): tuple[inLo, inHi: Z3Bool] =
  ## RFC-0005 S8z. The in-bounds conditions of an array read or write at
  ## `idx` over the index range `lo .. lo + n - 1`. The zero-based signed
  ## case keeps the exact formulas `isIndex` has always built (`0 <= i`,
  ## `i < n`), so no existing query changes. Any other case -- a nonzero
  ## first index (`array[1..3, T]`), or an unsigned index -- compares with
  ## the index's own signedness over the bounds clamped to its window (a
  ## bound past the window is always met; an empty intersection is never
  ## in bounds). An unsigned index compared signed read `0xC8` as -56.
  case idx.kind
  of svInt:
    (mkZ3IntLit(lo) <= idx.zi, idx.zi < mkZ3IntLit(lo + int64(n)))
  of svBV8, svBV16, svBV32, svBV64:
    if lo == 0 and idx.signed:
      let loSV = coerceIntLit(idx, 0)
      let hiSV = coerceIntLit(idx, int64(n))
      case idx.kind
      of svBV8:  (bvsle(loSV.bv8,  idx.bv8),  bvslt(idx.bv8,  hiSV.bv8))
      of svBV16: (bvsle(loSV.bv16, idx.bv16), bvslt(idx.bv16, hiSV.bv16))
      of svBV32: (bvsle(loSV.bv32, idx.bv32), bvslt(idx.bv32, hiSV.bv32))
      else:      (bvsle(loSV.bv64, idx.bv64), bvslt(idx.bv64, hiSV.bv64))
    else:
      let (mn, mx) = bvIndexWindow(idx)
      let hi = lo + int64(n) - 1
      if hi < mn or lo > mx:
        (mkBool(false), mkBool(false))
      else:
        # [range-invariant: index-defect-check -- the array's index range
        # is the IndexDefect CONDITION, not the index value's own type range]
        let c = bvRangeConds(idx, max(lo, mn), min(hi, mx), idx.signed)  # [range-invariant: index-defect-check]
        ((if lo <= mn: mkBool(true) else: c[0]),
         (if hi >= mx: mkBool(true) else: c[1]))
  else:
    raise newException(ValueError, "isIndex: non-int index kind")  # [raise-audited: category-c: index-must-be-int invariant (Nim array/seq indexing typing rules)]

proc literalPosition*(idx: SymVal; lo: int64; n: int): int =
  ## RFC-0005 S8ct. The position (`0 ..< n`) a literal index names, or -1 when
  ## the index does not fold to a numeral or names no position. Finding it by
  ## asking each position whether it is the one cost a simplify per element:
  ## a store into `array[4096, int]` at `pad[3]`, in a recursion inlined 24
  ## deep, took three minutes of walking.
  if idx.kind notin {svInt, svBV8, svBV16, svBV32, svBV64}: return -1
  let ctx = requireCurrentContext()
  let folded = ctx.checkErr Z3_simplify(ctx.raw, rawAstOf(idx))
  if not Z3_is_numeral_ast(ctx.raw, folded): return -1
  var v: int64
  if idx.kind == svInt:
    if not Z3_get_numeral_int64(ctx.raw, folded, addr v): return -1
  else:
    var u: uint64
    if not Z3_get_numeral_uint64(ctx.raw, folded, addr u): return -1
    let w = case idx.kind
      of svBV8: 8
      of svBV16: 16
      of svBV32: 32
      else: 64
    if idx.signed and w < 64 and u >= (1'u64 shl (w - 1)):
      v = int64(u) - (1'i64 shl w)
    else:
      v = cast[int64](u)
  if v < lo or v - lo >= int64(n): return -1
  int(v - lo)

proc symbolicPositions*(idx: SymVal; lo: int64; n: int): int =
  ## RFC-0005 S8ct. How many positions an access at `idx` merges: 0 for a
  ## literal index, else those of `0 ..< n` the index's type can hold. Past
  ## `termWalkMaxDepth` the access declines (`arrayAccessTooWide`).
  if literalPosition(idx, lo, n) >= 0: return 0
  let (mn, mx) = if idx.kind in {svBV8, svBV16, svBV32, svBV64}:
                   bvIndexWindow(idx)
                 else: (low(int64), high(int64))
  for k in 0 ..< n:
    let v = lo + int64(k)
    if v >= mn and v <= mx: inc result

proc arrayAccessTooWide*(idx: SymVal; lo: int64; n: int): bool =
  ## RFC-0005 S8ct. An access at a symbolic index merges every position its
  ## index may name: a term as deep as the array is long, built a position at a
  ## time. Past `termWalkMaxDepth` positions it is deeper than the term walks
  ## take, and the walk itself is unbounded by any budget (`array[4096, int]`
  ## behind a recursion inlined 24 deep walked for seven minutes), so the
  ## access declines instead: a read is a fresh value, a write is dropped.
  symbolicPositions(idx, lo, n) > termWalkMaxDepth

proc arraySelect*(elems: seq[SymVal]; idx: SymVal; lo: int64): SymVal =
  ## RFC-0005 S8z. Element `idx` of an array whose first index is `lo`, as
  ## an ite chain over the positions (element `k` is Nim's index `lo + k`),
  ## under the caller's in-bounds conditions. A position whose index the
  ## index's type cannot hold is never selected.
  ##
  ## RFC-0005 S8ar: an index that folds to a position (a literal, `a[1]`)
  ## selects that element with no merge. The ite chain merged every
  ## element, and a merge of two seq values is `iteSV`'s havoc
  ## (`feUnsupportedOpHavoc`), so `a[1].len` of an `array[N, seq[T]]` read
  ## a fresh seq even at a constant index.
  let at = literalPosition(idx, lo, elems.len)   # RFC-0005 S8ct
  if at >= 0: return elems[at]
  let (mn, mx) = if idx.kind in {svBV8, svBV16, svBV32, svBV64}:
                   bvIndexWindow(idx)
                 else: (low(int64), high(int64))
  for k in 0 ..< elems.len:
    let v = lo + int64(k)
    if v < mn or v > mx: continue
    if $simplify(symEq(idx, coerceIntLit(idx, v))) == "true": return elems[k]
  result = elems[0]
  for k in 1 ..< elems.len:
    let v = lo + int64(k)
    if v < mn or v > mx: continue
    result = iteSV(symEq(idx, coerceIntLit(idx, v)), elems[k], result)

proc arrayStore*(elems: seq[SymVal]; idx: SymVal; lo: int64;
                val: SymVal): seq[SymVal] =
  ## RFC-0005 S8z. The array `elems` with element `idx` replaced by `val`:
  ## each position becomes `ite(idx == lo + k, val, old[k])`. Under the
  ## caller's in-bounds conditions exactly one position is written.
  let at = literalPosition(idx, lo, elems.len)   # RFC-0005 S8ct
  if at >= 0:
    result = elems
    result[at] = val
    return
  let (mn, mx) = if idx.kind in {svBV8, svBV16, svBV32, svBV64}:
                   bvIndexWindow(idx)
                 else: (low(int64), high(int64))
  for k in 0 ..< elems.len:
    let v = lo + int64(k)
    if v < mn or v > mx: result.add elems[k]
    else:
      # RFC-0005 S8ar: a position the index folds to (or away from) takes
      # the value (or keeps its own) with no merge -- see `arraySelect`.
      let eq = symEq(idx, coerceIntLit(idx, v))
      case $simplify(eq)
      of "true": result.add val
      of "false": result.add elems[k]
      else: result.add iteSV(eq, val, elems[k])

# Width-uniform BV arithmetic. Both operands must be the same width.
template binBV*(a, b: SymVal, op: untyped): SymVal =
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
    raise newException(ValueError, "binBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (Nim has no structural arithmetic operators for tuple/seq/table/set/variant without operator overloading, which this DSL subset does not support)]

template placeholderBoolDecline*(recv: SymVal, opDesc, tag: string): SymVal =
  ## Item 4 (round-6 re-review): the DECLINE-ACTION half of the placeholder-
  ## comparison chokepoint, split out of `placeholderCmpDecline` below so a
  ## caller that already knows which single operand to decline (`svLeafEq`'s
  ## `svSeq` arm, further below — its own guard already checked BOTH `a`/`b`
  ## and always declines `a`) can compose it directly instead of hand-
  ## rewriting "record the decline, then allocate a fresh bool placeholder"
  ## itself. Record the R1 chokepoint decline for `recv` (an ALREADY-SELECTED
  ## placeholder operand) and return a fresh, unconstrained bool placeholder
  ## — the comparison/equality result is never trusted once the run
  ## degrades. `tag` is the caller's own fresh-const base name, kept
  ## per-site (not unified) so each degrade class stays independently
  ## greppable in a witness dump.
  declinePlaceholderInLower(recv, "", opDesc)
  var freshPCD: seq[Z3Bool]
  # Fix-slice item 4: `tag` used to name the Z3 const directly — a repeat
  # hit of the SAME call site (or of the two different call sites sharing
  # this template, `cmpBV`'s `__placeholderCmpDecline` and `svLeafEq`'s
  # `__svLeafEqPlaceholderDecline`) within one run collided on `(name,
  # sort)`, the exact hazard `freshDegradeName`/`degradeSymCounter` exists
  # to close (missed by the 2385f84 uniquification sweep). `tag` remains
  # the per-site BASE name; `freshDegradeName` appends the run-unique
  # `#<counter>` suffix.
  allocateSym(tBool(), freshDegradeName(tag), freshPCD)

template placeholderCmpDecline*(a, b: SymVal, opDesc: string): SymVal =
  ## Round-6 re-review (walker v112): R1's placeholder-decline discipline
  ## (S1/N1/iekSeqAdd's `placeholderReadDeclineMsg`/`declinePlaceholderInLower`
  ## chokepoint), extended to the comparison machinery. GUARD-BEFORE, not
  ## catch-after (B7r2 precedent): `cmpBV`/`eqBV`/`neBV` each call this BEFORE
  ## their own kind-`case` dispatch when either operand is an
  ## `isUnsupportedFieldPlaceholder`-flagged `svSeq` (both operands share
  ## `kind == svSeq` here — the caller's own `doAssert a.kind == b.kind` above
  ## already established that). Routes through the SAME chokepoint every
  ## other placeholder READ uses: `seNestedSeqUnsupported` with the
  ## ORIGINATING kind/reason, never the generic `feUnsupportedOp`/"non-BV
  ## SymVal" catch-all a genuinely-unsupported (non-placeholder, e.g. tuple
  ## ordering) kind still falls through to below. N46's conversion of the
  ## catch-all's raw `raise` to an in-band `allocDegrade` was correct on its
  ## own terms (SND-3/ADR-0023) — this is a REFINEMENT of that fix for the
  ## placeholder case specifically: a placeholder-operand comparison is not
  ## merely "not yet wired" (the catch-all's framing), it is the SAME honest
  ## "content was never modeled" decline every other placeholder access
  ## already gives, and deserves the SAME classified error + message.
  ##
  ## Item 4 (consolidated): the guard-check (which operand to decline) and
  ## the decline-action (record + fresh placeholder) are now two composable
  ## pieces — see `placeholderBoolDecline` immediately above.
  let recv = if a.isUnsupportedFieldPlaceholder: a else: b # [placeholder-audited]
  placeholderBoolDecline(recv, opDesc, "__placeholderCmpDecline")

template cmpBV*(a, b: SymVal, sop, uop: untyped): SymVal =
  ## Apply signed/unsigned comparison and lift to SymVal Bool.
  doAssert a.kind == b.kind, "cmpBV: width mismatch"
  let useSigned = a.signed
  if a.kind == svSeq and (a.isUnsupportedFieldPlaceholder or b.isUnsupportedFieldPlaceholder): # [placeholder-audited]
    placeholderCmpDecline(a, b, "ordering comparison of")
  else:
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
      # N46 (round-6 re-review): was a raw `raise newException`. `cmpBV` is
      # reached, unguarded, from `lowerCmp`'s catch-all `else` dispatch
      # (bLt/bLe/bGt/bGe) for ANY operand kind not already peeled off by
      # `cmpString`/`cmpFloat`/bool-eq above it -- ordinary Nim generates
      # tuple ordering (`<`/`<=`) structurally, so `myTuple1 < myTuple2`
      # inside a loop guard reaches here with a.kind == svTuple. In-band
      # degrade: a fresh unconstrained bool is sound (the comparison result
      # is never trusted once the run degrades). The placeholder-svSeq case
      # is peeled off above (walker v112) — this arm now only sees a
      # genuinely-unsupported (non-placeholder) kind.
      # RFC-0005 S6b: stays `feUnsupportedOp` (dcSubstituted), not
      # `feUnsupportedOpHavoc`. The bool is fresh, but the parser maps `<`
      # BY NAME (`binopForInfix`), and on a composite operand the resolved
      # operator is typically a user overload (or system's generic tuple
      # `<`, which calls the fields' own, possibly user, operators): a raise
      # inside it is dropped with the op.
      degradeAlloc(tBool(), feUnsupportedOp,
        "cmpBV on non-BV SymVal (kind=" & plainEnglishSymValKind(a.kind) & ")",
        "__cmpBVDegrade")

template divBV*(a, b: SymVal): SymVal =
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
    raise newException(ValueError, "divBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (see binBV)]

template modBV*(a, b: SymVal): SymVal =
  ## RFC-0005 S8i: Nim's signed `mod` is C's `%`, the TRUNCATED remainder,
  ## whose sign is the dividend's (`-7 mod 2 == -1`, `7 mod -2 == 1`,
  ## probed on the pinned toolchain) -- `bvsrem`. It was `bvsmod` (the sign
  ## of the divisor): `-7 mod 2` modelled as 1, a false `sxUnsat`/`sxSat`
  ## for every negative operand of mixed sign.
  doAssert a.kind == b.kind
  let s = a.signed
  case a.kind
  of svBV8:
    liftBV((if s: bvsrem(a.bv8,  b.bv8)  else: bvurem(a.bv8,  b.bv8)), s)
  of svBV16:
    liftBV((if s: bvsrem(a.bv16, b.bv16) else: bvurem(a.bv16, b.bv16)), s)
  of svBV32:
    liftBV((if s: bvsrem(a.bv32, b.bv32) else: bvurem(a.bv32, b.bv32)), s)
  of svBV64:
    liftBV((if s: bvsrem(a.bv64, b.bv64) else: bvurem(a.bv64, b.bv64)), s)
  else:
    raise newException(ValueError, "modBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (see binBV)]

template shrBV*(a, b: SymVal): SymVal =
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
    raise newException(ValueError, "shrBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (see binBV)]

template negBV*(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(-a.bv8,  a.signed)
  of svBV16: liftBV(-a.bv16, a.signed)
  of svBV32: liftBV(-a.bv32, a.signed)
  of svBV64: liftBV(-a.bv64, a.signed)
  else: raise newException(ValueError, "negBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (see binBV)]

template notBV*(a: SymVal): SymVal =
  case a.kind
  of svBV8:  liftBV(not a.bv8,  a.signed)
  of svBV16: liftBV(not a.bv16, a.signed)
  of svBV32: liftBV(not a.bv32, a.signed)
  of svBV64: liftBV(not a.bv64, a.signed)
  else: raise newException(ValueError, "notBV on non-BV SymVal")  # [raise-audited: category-c: BV-arithmetic-only reachability (see binBV)]

# ---- Equality across BV widths is uniform -----------------------------------

template eqBV*(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  if a.kind == svSeq and (a.isUnsupportedFieldPlaceholder or b.isUnsupportedFieldPlaceholder): # [placeholder-audited]
    placeholderCmpDecline(a, b, "equality (==) of")
  else:
    case a.kind
    of svBV8:  ofBool(a.bv8  == b.bv8)
    of svBV16: ofBool(a.bv16 == b.bv16)
    of svBV32: ofBool(a.bv32 == b.bv32)
    of svBV64: ofBool(a.bv64 == b.bv64)
    else:
      # N46 (round-6 re-review): was a raw `raise newException`. `eqBV` is
      # reached, unguarded, from `lowerCmp`'s catch-all `bEq` dispatch for
      # ANY operand kind not already peeled off above it -- ordinary Nim
      # generates structural `==` for tuples/objects/seqs, so
      # `myTuple1 == myTuple2` inside a loop guard reaches here with
      # a.kind == svTuple. In-band degrade: a fresh unconstrained bool is
      # sound (the comparison result is never trusted once the run degrades).
      # The placeholder-svSeq case is peeled off above (walker v112) — this
      # arm now only sees a genuinely-unsupported (non-placeholder) kind.
      # Item 3 (walker v115): uniquify -- same Z3 name-interning collision
      # class as `__iteSVMergeDegrade` (see `degradeSymCounter`'s doc). Item 9
      # (round-6 re-review): routed through the shared `degradeAlloc` pairing
      # helper. RFC-0005 S6b: stays `feUnsupportedOp` (dcSubstituted) --
      # the same by-name operator resolution as `cmpBV` above: a user `==`
      # on an object (or on a field type system's structural `==` calls)
      # may raise, and that raise is dropped with the op.
      degradeAlloc(tBool(), feUnsupportedOp,
        "eqBV on non-BV SymVal (kind=" & plainEnglishSymValKind(a.kind) & ")",
        "__eqBVDegrade")

template neBV*(a, b: SymVal): SymVal =
  doAssert a.kind == b.kind
  if a.kind == svSeq and (a.isUnsupportedFieldPlaceholder or b.isUnsupportedFieldPlaceholder): # [placeholder-audited]
    placeholderCmpDecline(a, b, "inequality (!=) of")
  else:
    case a.kind
    of svBV8:  ofBool(a.bv8  != b.bv8)
    of svBV16: ofBool(a.bv16 != b.bv16)
    of svBV32: ofBool(a.bv32 != b.bv32)
    of svBV64: ofBool(a.bv64 != b.bv64)
    else:
      # N46: same walk-reachable structural-`!=` hazard as `eqBV` above --
      # see its comment. The placeholder-svSeq case is peeled off above
      # (walker v112) — this arm now only sees a genuinely-unsupported
      # (non-placeholder) kind.
      # Item 3 (walker v115): uniquify -- same rationale as `eqBV` above.
      # Item 9 (round-6 re-review): routed through the shared `degradeAlloc`
      # pairing helper. RFC-0005 S6b: stays `feUnsupportedOp`, as `eqBV`.
      degradeAlloc(tBool(), feUnsupportedOp,
        "neBV on non-BV SymVal (kind=" & plainEnglishSymValKind(a.kind) & ")",
        "__neBVDegrade")

var pendingPtrCompares* {.threadvar.}: seq[Z3AnyAst]
  ## RFC-0005 S8ax. The `ptr` operands `refEq` compared since the last
  ## `drainPendingLowerEffects`, which declines the path when one may be a
  ## dead frame's address cell (`danglingCompareTaint`).

proc refNilAst*(v: SymVal): Z3AnyAst =
  ## RFC-0016 INT-65. The nil of `v`'s pointee sort (`allocRefSort` mints it).
  let ctx = requireCurrentContext()
  let pointee = (if v.kind == svRef: v.refPointee else: v.ptrPointee)
  discard allocRefSort(ctx, pointee)
  currentNilConsts[refPointeeTypeId(pointee)]

proc refEq*(a, b: SymVal, op: IRBinop): SymVal
proc refCrossSortEq*(a, b: SymVal, op: IRBinop): SymVal =
  ## RFC-0016 INT-65. `==`/`!=` over two addresses of different pointee
  ## sorts: a `pointer` holds the `ptr`/`ref` it was converted from, so
  ## `pointer(addr i) == pointer(addr f)` meets `Ref_i64` and `Ref_float64`.
  ## Nil is one address in every sort, so a side that is ground nil decides
  ## the comparison as the other side's nil test. Two non-nil addresses of
  ## different sorts are distinct variables natively, but a `cast` may name
  ## one location at two types, which the walk does not track: declined.
  let ctx = requireCurrentContext()
  let aAst = (if a.kind == svRef: a.refAst else: a.ptrAst)
  let bAst = (if b.kind == svRef: b.refAst else: b.ptrAst)
  let aNil = refNilAst(a)
  let bNil = refNilAst(b)
  let aIsNil = wrap[Z3Bool](ctx, checkedEq(ctx, aAst.raw, aNil.raw))
  let bIsNil = wrap[Z3Bool](ctx, checkedEq(ctx, bAst.raw, bNil.raw))
  if aAst.raw == aNil.raw or bAst.raw == bNil.raw:
    let eq = if aAst.raw == aNil.raw: bIsNil else: aIsNil
    case op
    of bEq: return ofBool(eq)
    of bNe: return ofBool(not eq)
    else: return refEq(a, a, op)   # the ordering decline, sorts aside
  degradeAlloc(tBool(), heUnresolvedRef,
    "ref/ptr " & $op & " between addresses of different pointee types (" &
      $(if a.kind == svRef: a.refPointee else: a.ptrPointee) & ", " &
      $(if b.kind == svRef: b.refPointee else: b.ptrPointee) & "): a `cast` " &
      "may name one location at both, which the walk does not track " &
      "(heUnresolvedRef)",
    "__refCrossSortDegrade")

proc closureMixedCmpDecline*(a, b: SymVal, op: IRBinop): SymVal =
  ## RFC-0016 INT-65. A proc value compared with a value the walk holds only
  ## as a placeholder (a proc-typed parameter, a havocked proc variable): it
  ## may be nil or any routine.
  degradeAlloc(tBool(), ceUnsupportedHof,
    "a proc value " & $op & " a " & plainEnglishSymValKind(
      (if a.kind == svClosure: b.kind else: a.kind)) &
      " operand the walk does not hold as a proc value (ceUnsupportedHof)",
    "__closureMixedCmpDegrade")

proc refEq*(a, b: SymVal, op: IRBinop): SymVal =
  ## Phase 15 R2 (ADR-0010). `==`/`!=` over two ref/ptr SymVals — a GROUND
  ## equality of the two `Ref_T`-sorted address consts (`Z3_mk_eq`, negated for
  ## `!=`). With the per-path freshness inequalities asserted at each `new T`,
  ## two distinct fresh refs are provably non-equal (so `if p == q` over two
  ## fresh allocations is an unreachable branch). No heap read happens here.
  let aAst = (if a.kind == svRef: a.refAst else: a.ptrAst)
  let bAst = (if b.kind == svRef: b.refAst else: b.ptrAst)
  if a.kind == svPtr: pendingPtrCompares.add aAst   # RFC-0005 S8ax
  if b.kind == svPtr: pendingPtrCompares.add bAst
  let ctx = requireCurrentContext()
  # RFC-0016 INT-65: addresses of different pointee sorts (a `pointer`).
  if sortOfRaw(ctx, aAst.raw) != sortOfRaw(ctx, bAst.raw):   # hash-consed
    return refCrossSortEq(a, b, op)
  let eq = wrap[Z3Bool](ctx, checkedEq(ctx, aAst.raw, bAst.raw))
  case op
  of bEq: ofBool(eq)
  of bNe: ofBool(not eq)
  else:
    # N46 (round-6 re-review): was a raw `raise newException`. Reached,
    # unguarded, when `op` is an ordering comparator (bLt/bLe/bGt/bGe) on
    # two `svRef`/`svPtr` SymVals -- callers pass `e.bop` through from the
    # same unrestricted comparison-op dispatch that reaches `bEq`/`bNe`
    # here, and Nim defines pointer ordering for raw `ptr` types, so a
    # `ptr`-typed SUT comparison can plausibly reach this arm from a loop
    # guard. In-band degrade: a fresh unconstrained bool is sound.
    # RFC-0005 S6b: stays `feUnsupportedOp` -- `ref T` has no system
    # ordering, so an ordering `<` on refs IS a user overload (by-name
    # mapping, as `cmpBV`): its raises are dropped.
    #
    # RFC-0016 K10a-axis (STY-03): the kind and the reason are the definedness
    # axis's `order/pointer` row, a `never` cell.
    let ordRow = admitDefined(aoOrder, ocPointer, dsOrder)
    let (ordKind, ordWhy) = ordRow.decline
    degradeAlloc(tBool(), ordKind.get(feUnsupportedOp),
      "ref/ptr comparison op " & $op & " not valid (only ==/!=): " & ordWhy,
      "__refEqOrderDegrade")

proc refMixedCmpDecline*(a, b: SymVal, op: IRBinop): SymVal =
  ## RFC-0005 S8m. A comparison with a ref/ptr on ONE side only. Nim types
  ## both operands of a ref `==` alike, so the other side lowered to a
  ## non-address `SymVal` only because something upstream already failed to
  ## model it (a declined expression's dummy). This fell through to
  ## `lowerCmp`, whose `eqBV` asserted `a.kind == b.kind` and aborted the
  ## whole run as `weInternalWalkerFault`. Record it as the unresolved ref it
  ## is and hand back a fresh bool: the path is tainted, never a verdict.
  degradeAlloc(tBool(), heUnresolvedRef,
    "ref/ptr " & $op & " against a " & plainEnglishSymValKind(
      (if a.kind in {svRef, svPtr}: b.kind else: a.kind)) &
      " operand the model did not resolve to an address (heUnresolvedRef)",
    "__refMixedCmpDegrade")

proc mixedBitwiseDecline*(a, b: SymVal, op: IRBinop): SymVal =
  ## RFC-0005 S8bc. An `and`/`or`/`xor` with a bool on ONE side only. Nim
  ## types both operands alike (both `bool`, or both one integer type), so
  ## one side lowered to a bool only because something upstream already
  ## declined it: a value of a type the model does not classify (a plain
  ## alias such as `hashes.Hash = int`) is `allocDegrade`'s tainted bool
  ## placeholder. The arm asserted `r.kind == svBool` and aborted the run as
  ## `weInternalWalkerFault` (`hc and maxHash(t)` inside the stdlib
  ## `getOrDefault`'s walked body). Record the unresolved operand and hand
  ## back a fresh value of the integer side's type: the path is tainted,
  ## never a verdict.
  let intSide = if a.kind == svBool: b else: a
  degradeAlloc(tyOf(intSide), feUnsupportedOp,
    "`" & $op & "` of a bool and a " & plainEnglishSymValKind(intSide.kind) &
    " operand: one side is a value the model did not resolve to its " &
    "declared type (feUnsupportedOp)",
    "__mixedBitwiseDegrade")

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

proc alignIntKind*(v: SymVal; like: SVKind): Option[SymVal] =
  ## RFC-0005 S8z. `v` in the representation `like` of the element it is
  ## stored over (an array element write): unchanged when the kinds agree,
  ## an Int-promoted value converted to the element's bit-vector width
  ## (`svIntToBV`, exact for a value of the element's own type) or a
  ## bit-vector to an Int (`toSvIntPreserving`). `none` for any other
  ## mismatch; the caller declines it.
  if v.kind == like: some(v)
  elif v.kind == svInt and like in {svBV8, svBV16, svBV32, svBV64}:
    some(svIntToBV(v, like))
  elif v.kind in {svBV8, svBV16, svBV32, svBV64} and like == svInt:
    some(toSvIntPreserving(v))
  else: none(SymVal)

proc cmpFloat*(a, b: SymVal, op: IRBinop): SymVal =
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
    else: raise newException(ValueError, "cmpFloat: not a comparison op")  # [raise-audited: category-c: op-narrowed by caller dispatch (cmpFloat's op set is pre-restricted by lowerCmp before dispatch)]
  else:
    case op
    of bEq: ofBool(a.fp64 == b.fp64)
    of bNe: ofBool(a.fp64 != b.fp64)
    of bLt: ofBool(a.fp64 <  b.fp64)   # Phase 15 F4: IEEE ordering (false on NaN)
    of bLe: ofBool(a.fp64 <= b.fp64)
    of bGt: ofBool(a.fp64 >  b.fp64)
    of bGe: ofBool(a.fp64 >= b.fp64)
    else: raise newException(ValueError, "cmpFloat: not a comparison op")  # [raise-audited: category-c: op-narrowed by caller dispatch (see cmpFloat above)]

proc arithFloat*(a, b: SymVal, op: IRBinop): SymVal =
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
       of bMod: raise (ref SymexUnsupportedOpError)(op: "math.mod",
         msg: "math.mod is not modeled by the symex engine -- " &
              floatCallDecline("mod", 2))   # RFC-0016 K4c (PRC-09): `mod` on floats is `math.mod` (fmod), a row
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))  # [raise-audited: category-c: op-narrowed by caller dispatch; Nim also has no mod for floats]
  else:
    SymVal(kind: svFloat64, fp64:
      (case op
       of bAdd: a.fp64 + b.fp64
       of bSub: a.fp64 - b.fp64
       of bMul: a.fp64 * b.fp64
       of bDiv: a.fp64 / b.fp64
       of bMod: raise (ref SymexUnsupportedOpError)(op: "math.mod",
         msg: "math.mod is not modeled by the symex engine -- " &
              floatCallDecline("mod", 2))
       else: raise newException(ValueError, "arithFloat: " & $op & " not a float arith op")))  # [raise-audited: category-c: op-narrowed by caller dispatch (see arithFloat above)]

proc truncDivInt*(a, b: Z3Int): tuple[q, r: Z3Int] =
  ## RFC-0005 S8i. Nim's `div`/`mod` on a signed integer are C's: the
  ## quotient truncates toward zero and the remainder takes the dividend's
  ## sign (`-7 div 2 == -3`, `-7 mod 2 == -1`, `7 mod -2 == 1`; probed on the
  ## pinned toolchain). Z3's Int `div`/`mod` are EUCLIDEAN (`0 <= r < |b|`),
  ## which agrees only for a non-negative dividend. From the Euclidean pair
  ## `(qe, re)`: a negative dividend with a non-zero `re` moves the quotient
  ## one step toward zero (`qe + sign(b)`) and the remainder by `|b|`.
  ## Before S8i the svInt arm used Z3's pair directly (the `bMod` gap
  ## recorded in `tsymex_phase15_A1_arithmetic.nim`).
  let qe = a div b
  let re = a mod b
  let zero = mkInt(0)
  let adjust = a < zero and re != zero
  let step = ite(b > zero, mkInt(1), mkInt(-1))
  let absB = ite(b >= zero, b, zero - b)
  (q: ite(adjust, qe + step, qe), r: ite(adjust, re - absB, re))

proc arithInt*(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  ## R3 (S2): propagate width metadata to the result so CHAINED arithmetic
  ## on a promoted value keeps the overflow fork alive (e.g. `(pos + 1) *
  ## bound` — the inner `pos + 1`'s own result must still carry `pos`'s
  ## width, or the outer `* bound` would see `ziWidth == 0` and silently
  ## stop forking). Prefers `a`'s width (the operand `lowerArith`'s fork
  ## check itself reads); falls back to `b`'s when `a` has none — Nim
  ## binops require both operands share one static type, so either side
  ## carrying it is equally authoritative.
  let (rw, rs) = if a.ziWidth != 0: (a.ziWidth, a.ziSigned)
                 elif b.ziWidth != 0: (b.ziWidth, b.ziSigned)
                 else: (0, false)
  ## Issue #161 slice 2: propagate the interval alongside the width, by the
  ## same argument — an inner `pos + 1` must carry its own bound or the
  ## outer `* bound` has nothing to prove with and pays a fork it does not
  ## owe. `none` on either operand (or an analysis-overflowing bound) yields
  ## `none`, which is ⊤ and merely keeps the obligation live.
  ## div/mod are deliberately ⊤: sound bounds there depend on whether the
  ## divisor straddles zero, which `tryEvalInterval` also declines to model.
  let ri = if a.ziIvl.isSome and b.ziIvl.isSome:
             case op
             of bAdd: add(a.ziIvl.get, b.ziIvl.get)
             of bSub: sub(a.ziIvl.get, b.ziIvl.get)
             of bMul: mul(a.ziIvl.get, b.ziIvl.get)
             else: none(Interval)
           else: none(Interval)
  case op
  of bAdd: SymVal(kind: svInt, zi: a.zi + b.zi, ziWidth: rw, ziSigned: rs, ziIvl: ri)
  of bSub: SymVal(kind: svInt, zi: a.zi - b.zi, ziWidth: rw, ziSigned: rs, ziIvl: ri)
  of bMul: SymVal(kind: svInt, zi: a.zi * b.zi, ziWidth: rw, ziSigned: rs, ziIvl: ri)
  of bDiv: SymVal(kind: svInt, zi: truncDivInt(a.zi, b.zi).q, ziWidth: rw, ziSigned: rs)
  of bMod: SymVal(kind: svInt, zi: truncDivInt(a.zi, b.zi).r, ziWidth: rw, ziSigned: rs)
  else: raise newException(ValueError, "arithInt: not an arithmetic op")  # [raise-audited: category-c: op-narrowed by caller dispatch (arithInt's op set is pre-restricted by lowerArith before dispatch)]

proc cmpInt*(a, b: SymVal, op: IRBinop): SymVal =
  doAssert a.kind == svInt and b.kind == svInt
  case op
  of bEq: ofBool(a.zi == b.zi)
  of bNe: ofBool(a.zi != b.zi)
  of bLt: ofBool(a.zi <  b.zi)
  of bLe: ofBool(a.zi <= b.zi)
  of bGt: ofBool(a.zi >  b.zi)
  of bGe: ofBool(a.zi >= b.zi)
  else: raise newException(ValueError, "cmpInt: not a comparison op")  # [raise-audited: category-c: op-narrowed by caller dispatch (cmpInt's op set is pre-restricted by lowerCmp before dispatch)]

proc cmpString*(a, b: SymVal, op: IRBinop): SymVal =
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
  # RFC-0016 INT-57: two renderings of bit-vectors (`$t <= $u`), or two
  # values each one of a few literals (a merged `$b`), compare as formulas
  # over the values, not as strings (`renderCmp`, `litCmp`).
  let byValue = renderCmp(a.str, b.str, op)
  if byValue.isSome: return ofBool(byValue.get)
  let byCases = litCmp(a.str, b.str, op)
  if byCases.isSome: return ofBool(byCases.get)
  case op
  of bEq: ofBool(a.str == b.str)
  of bNe: ofBool(a.str != b.str)
  else:
    # RFC-0005 S8cb (item 5): Z3's `str.<` is the lexicographic order of the
    # code points, and under ADR-0006 a code point is the byte `cmpStrings`
    # compares, a prefix ordered first.
    case op
    of bLt: ofBool(a.str < b.str)
    of bLe: ofBool(a.str <= b.str)
    of bGt: ofBool(b.str < a.str)
    else: ofBool(b.str <= a.str)    # bGe

proc svLeafEq*(a, b: SymVal): Z3Bool =
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
  of svSeq:
    if a.isUnsupportedFieldPlaceholder or b.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # Round-6 re-review (walker v112): a captured closure-environment field
      # that is itself an unbacked-element-seq PLACEHOLDER -- guard-before,
      # routed through the SAME R1 chokepoint the comparison-machinery
      # siblings (`eqBV`/`neBV`/`cmpBV`) now use, rather than the generic
      # catch-all below. Item 4 (consolidated): composes the chokepoint's
      # decline-action half directly (`placeholderBoolDecline`, above `cmpBV`)
      # instead of hand-rewriting its "decline, then allocate a fresh bool"
      # body -- this arm already knows its own single operand to decline (the
      # guard above checks BOTH `a`/`b`, but always declines `a`, matching
      # `placeholderCmpDecline`'s own a-before-b selection), so it composes
      # the decline-action directly rather than going through the two-operand
      # guard-check `placeholderCmpDecline` itself performs.
      placeholderBoolDecline(a, "closure-environment structural equality of",
        "__svLeafEqPlaceholderDecline").bo
    else:
      # A GENUINE (non-placeholder) captured seq field: general seq equality
      # is not yet wired (same residual gap `eqBV`'s catch-all still owns for
      # a bare `seq == seq`) -- falls through to the shared degrade below.
      # RFC-0005 S6b: a fresh per-evaluation conjunct of an AND -- the
      # environment equality it sits in can still take both values, and
      # Nim's closure `==` runs no user code, so nothing is dropped:
      # `feUnsupportedOpHavoc`.
      degradeAlloc(tBool(), feUnsupportedOpHavoc,
        "svLeafEq: closure-environment field of kind seq is not supported " &
        "for structural equality (C5)", "__svLeafEqDegrade").bo
  else:
    # N46 (round-6 re-review): was a raw `raise newException`. Reached from
    # `svTupleEq`'s recursive field walk (`closureEq`) when a captured
    # closure-environment field is svTable/svSet/svVariant/
    # svMultiVariant/svClosure/svRef/svPtr/svUninterpRef -- a closure that
    # captures a local Table/variant/ref and is compared for equality
    # (`==`/`!=`) inside a loop reaches this unguarded. In-band degrade:
    # a fresh unconstrained bool is sound (the comparison result is never
    # trusted once the run degrades). `svSeq` is peeled off above (walker
    # v112) into its own placeholder-aware arm. RFC-0005 S6b:
    # `feUnsupportedOpHavoc`, as the svSeq arm above.
    degradeAlloc(tBool(), feUnsupportedOpHavoc,
      "svLeafEq: closure-environment field of kind " & plainEnglishSymValKind(a.kind) &
      " is not supported for structural equality (C5)", "__svLeafEqDegrade").bo

proc svTupleEq*(a, b: SymVal): Z3Bool =
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

proc closureEq*(c1, c2: SymVal, op: IRBinop): SymVal =
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

proc coerceToBoolSV*(sv: SymVal): SymVal =
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

proc divisorIsZero*(b: SymVal): Z3Bool =
  ## R16-3: build divisor==0 predicate in the operand's NATIVE sort.
  ## Uses NO bv2int / int2bv — mixed-theory conversions hang Z3.
  case b.kind
  of svInt:  b.zi == mkZ3IntLit(0)
  of svBV8:  b.bv8  == mkBitVec[8](0)
  of svBV16: b.bv16 == mkBitVec[16](0)
  of svBV32: b.bv32 == mkBitVec[32](0)
  of svBV64: b.bv64 == mkBitVec[64](0)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: op-narrowed by caller dispatch]
      "divisorIsZero: unexpected divisor kind " & $b.kind)

proc mulOverflowSplit*(a, b: SymVal): Option[Z3Bool]  ## RFC-0016 S8cg fwd decl

proc overflowCond*(a, b: SymVal, op: IRBinop): Z3Bool =
  ## R16-4: build "this signed BV arithmetic op overflows" predicate.
  ## Returns true (raise) when the operation overflows OR underflows.
  ## Only called for signed BV operands — caller guards `a.signed == true` and
  ## `a.kind in {svBV8, svBV16, svBV32, svBV64}`.
  ## Unsigned BV is skipped (Nim wraps silently — no OverflowDefect).
  ## R3 (S2, walker v91): svInt used to be skipped ENTIRELY here (the BV
  ## overflow predicates above hang Z3 on Int terms) — but that blanket skip
  ## meant a WIDTH-TYPED Nim int promoted to `svInt` (this round's int-offset
  ## machinery, `IRParam.isIntOffset`/`IRStmt.isLet.lIsIntOffsetLocal`) could
  ## NEVER fork `OverflowDefect`, a false-`sxUnsat` hole for any
  ## defect-reachability search touching a promoted value. The BV-predicate
  ## hang concern does not apply to Int terms: for linear Integer arithmetic,
  ## overflow of a width-typed value is a plain post-hoc RANGE CHECK — see
  ## `overflowCondInt` below, svInt's sibling to this proc, dispatched
  ## alongside it from `lowerArith`.
  # RFC-0016 S8cg: a product whose operand takes a few literal values.
  if op == bMul:
    let split = mulOverflowSplit(a, b)
    if split.isSome: return split.get
  case a.kind
  of svBV8:
    case op
    of bAdd: not addNoOverflow(a.bv8, b.bv8, true) or not addNoUnderflow(a.bv8, b.bv8)
    of bSub: not subNoOverflow(a.bv8, b.bv8) or not subNoUnderflow(a.bv8, b.bv8, true)
    of bMul: not mulNoOverflow(a.bv8, b.bv8, true) or not mulNoUnderflow(a.bv8, b.bv8)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)  # [raise-audited: category-c: op-narrowed by caller dispatch (own doc: caller-guarded)]
  of svBV16:
    case op
    of bAdd: not addNoOverflow(a.bv16, b.bv16, true) or not addNoUnderflow(a.bv16, b.bv16)
    of bSub: not subNoOverflow(a.bv16, b.bv16) or not subNoUnderflow(a.bv16, b.bv16, true)
    of bMul: not mulNoOverflow(a.bv16, b.bv16, true) or not mulNoUnderflow(a.bv16, b.bv16)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)  # [raise-audited: category-c: op-narrowed by caller dispatch (see overflowCond above)]
  of svBV32:
    case op
    of bAdd: not addNoOverflow(a.bv32, b.bv32, true) or not addNoUnderflow(a.bv32, b.bv32)
    of bSub: not subNoOverflow(a.bv32, b.bv32) or not subNoUnderflow(a.bv32, b.bv32, true)
    of bMul: not mulNoOverflow(a.bv32, b.bv32, true) or not mulNoUnderflow(a.bv32, b.bv32)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)  # [raise-audited: category-c: op-narrowed by caller dispatch (see overflowCond above)]
  of svBV64:
    case op
    of bAdd: not addNoOverflow(a.bv64, b.bv64, true) or not addNoUnderflow(a.bv64, b.bv64)
    of bSub: not subNoOverflow(a.bv64, b.bv64) or not subNoUnderflow(a.bv64, b.bv64, true)
    of bMul: not mulNoOverflow(a.bv64, b.bv64, true) or not mulNoUnderflow(a.bv64, b.bv64)
    else: raise newException(ValueError, "overflowCond: unexpected op " & $op)  # [raise-audited: category-c: op-narrowed by caller dispatch (see overflowCond above)]
  else:
    raise newException(ValueError,  # [raise-audited: category-c: op-narrowed by caller dispatch (see overflowCond above)]
      "overflowCond: unexpected kind " & $a.kind)

proc intBounds*(width: int): (int64, int64) =
  ## R3 (S2): `[low(T), high(T)]` for the static Nim signed integer type of
  ## `width` bits — the exact bounds `overflowCondInt` compares the
  ## unbounded Z3 Int arithmetic result against. Numerals only (no
  ## bv2int/int2bv); every bound here is exactly representable in `int64`,
  ## including width 64's own `low(int64)`/`high(int64)`.
  case width
  of 8:  (int64(low(int8)),  int64(high(int8)))
  of 16: (int64(low(int16)), int64(high(int16)))
  of 32: (int64(low(int32)), int64(high(int32)))
  of 64: (low(int64), high(int64))
  else:
    raise newException(ValueError, "intBounds: unsupported width " & $width)  # [raise-audited: category-c: width-exhaustive (IRType.width for itInt is always 8/16/32/64)]

var bvIvlDeclKinds* {.threadvar.}:
    tuple[ready: bool, add, sub, ite, sext, zext: int]
  ## RFC-0005 S8bv. The decl kinds `bvSignedInterval` reads, taken from the
  ## linked Z3 (as `seqCapKinds` does): the wrapper binds only part of the
  ## C enum.

const bvIvlNodeBudget* = 4096
  ## RFC-0005 S8bv. The most distinct subterms one `bvSignedInterval` call
  ## visits before it answers "any value of the width".

proc bvSignedInterval*(ctx: Z3Context; t: RawZ3Ast): Interval =
  ## RFC-0005 S8bv. An over-approximation of the values the signed
  ## bit-vector term `t` (at most 64 bits) can take, read off its
  ## structure: a numeral is itself, `bvadd` / `bvsub` the interval sum /
  ## difference when it cannot wrap, `ite` the hull of its arms, a sign
  ## extension its operand, a zero extension its operand's unsigned range;
  ## anything else is the whole width. Sound by construction: every rule
  ## contains every value the term takes. Memoised per call only (an AST id
  ## outlives no call here, so it is never reused for another term).
  if not bvIvlDeclKinds.ready:
    proc kindOf(a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
    let v = mkBitVecVar[8](ctx, "__s8bv_ivl_probe")
    let c = mkBoolVar(ctx, "__s8bv_ivl_probe_c")
    bvIvlDeclKinds = (ready: true, add: kindOf((v + v).raw),
      sub: kindOf((v - v).raw), ite: kindOf(ite(c, v, v).raw),
      sext: kindOf(ctx.checkErr Z3_mk_sign_ext(ctx.raw, 8, v.raw)),
      zext: kindOf(ctx.checkErr Z3_mk_zero_ext(ctx.raw, 8, v.raw)))
  let kinds = bvIvlDeclKinds
  var memo: Table[int, Interval]
  var budget = bvIvlNodeBudget
  proc widthOf(a: RawZ3Ast): int =
    int(Z3_get_bv_sort_size(ctx.raw, Z3_get_sort(ctx.raw, a)))
  proc full(w: int): Interval =
    if w >= 64: interval(low(int64), high(int64))
    else: interval(-(1'i64 shl (w - 1)), (1'i64 shl (w - 1)) - 1)
  proc fits(r: Option[Interval]; w: int): bool =
    r.isSome and r.get.lo >= full(w).lo and r.get.hi <= full(w).hi
  proc go(a: RawZ3Ast): Interval =
    let w = widthOf(a)
    if w < 1 or w > 64: return interval(low(int64), high(int64))
    let id = astId(ctx, a)
    if id in memo: return memo[id]
    if budget <= 0: return full(w)
    dec budget
    result = full(w)
    case Z3_get_ast_kind(ctx.raw, a)
    of Z3_NUMERAL_AST:
      var u: uint64
      if Z3_get_numeral_uint64(ctx.raw, a, addr u):
        let v = if w >= 64: cast[int64](u)
                elif u >= (1'u64 shl (w - 1)): int64(u) - (1'i64 shl w)
                else: int64(u)
        result = interval(v, v)
    of Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, a)
      let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app)))
      let n = int(Z3_get_app_num_args(ctx.raw, app))
      template arg(i: int): RawZ3Ast = Z3_get_app_arg(ctx.raw, app, cuint(i))
      if k == kinds.ite and n == 3:
        let x = go(arg(1))
        let y = go(arg(2))
        result = interval(min(x.lo, y.lo), max(x.hi, y.hi))
      elif k == kinds.add and n >= 1:
        var acc = some(go(arg(0)))
        for i in 1 ..< n:
          if acc.isNone: break
          acc = add(acc.get, go(arg(i)))
        if fits(acc, w): result = acc.get
      elif k == kinds.sub and n == 2:
        let r = sub(go(arg(0)), go(arg(1)))
        if fits(r, w): result = r.get
      elif k == kinds.sext and n == 1:
        result = go(arg(0))
      elif k == kinds.zext and n == 1:
        let aw = widthOf(arg(0))
        let x = go(arg(0))
        if x.lo >= 0: result = x
        elif aw < 63: result = interval(0, (1'i64 shl aw) - 1)
    else: discard
    memo[id] = result
  go(t)

const mulSplitLeafBudget* = 16
  ## RFC-0016 S8cg. The most literal values `mulOverflowSplit` splits a
  ## product's operand on.

proc mulOverflowSplit*(a, b: SymVal): Option[Z3Bool] =
  ## RFC-0016 S8cg. `overflowCond(a, b, bMul)` split on an operand that is a
  ## choice among a few literals (`ite` arms ending in numerals, read
  ## through `Z3_simplify` when it is an array `select`: a `Table`'s keys
  ## from a literal domain, `isTabKeys`). For a literal `c`, `c * o`
  ## overflows exactly when `o` lies outside `[low div c, high div c]` (the
  ## bounds swapped for a negative `c`; `c` in {0, 1} never, `-1` at `low`
  ## alone), a comparison where `bvsmul_noovfl` / `noudfl` over two free
  ## terms is a multiplier circuit: `ti_tuple`'s `s += k * v` cost 121M
  ## units in a context of its own (batch 7), past a tainted path's 20M.
  ## The same predicate, spelled differently; `none` when neither operand is
  ## such a choice.
  let w = case a.kind
          of svBV8: 8
          of svBV16: 16
          of svBV32: 32
          of svBV64: 64
          else: return none(Z3Bool)
  if b.kind != a.kind: return none(Z3Bool)
  let ctx = requireCurrentContext()
  discard bvSignedInterval(ctx, rawAnyAstOf(a))   # reads `bvIvlDeclKinds`
  let kinds = bvIvlDeclKinds
  if selectDeclKind == 0:
    discard peelSelect(ctx, rawAnyAstOf(a))       # reads `selectDeclKind`
  var hold: seq[Z3AnyAst]   # every term built here, referenced until wrapped
  proc keep(r: RawZ3Ast): RawZ3Ast =
    hold.add wrap[Z3AnyAst](ctx, r)
    r
  proc declOf(t: RawZ3Ast): int =
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: return -1
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, t))))
  proc numeral(t: RawZ3Ast; v: var int64): bool =
    if Z3_get_ast_kind(ctx.raw, t) != Z3_NUMERAL_AST: return false
    var u: uint64
    if not Z3_get_numeral_uint64(ctx.raw, t, addr u): return false
    v = if w >= 64: cast[int64](u)
        elif u >= (1'u64 shl (w - 1)): int64(u) - (1'i64 shl w)
        else: int64(u)
    true
  proc leaves(t: RawZ3Ast; budget: var int): bool =
    ## `t` is an `ite` tree over numerals of at most `budget` leaves.
    var v: int64
    if numeral(t, v):
      dec budget
      return budget >= 0
    if declOf(t) != kinds.ite: return false
    let app = Z3_to_app(ctx.raw, t)
    if Z3_get_app_num_args(ctx.raw, app) != 3: return false
    leaves(Z3_get_app_arg(ctx.raw, app, 1), budget) and
      leaves(Z3_get_app_arg(ctx.raw, app, 2), budget)
  proc choice(sv: SymVal): Option[RawZ3Ast] =
    ## The operand as an `ite` tree over numerals, or `none`.
    var t = rawAnyAstOf(sv)
    if declOf(t) + 1 == selectDeclKind:
      t = keep(ctx.checkErr Z3_simplify(ctx.raw, t))
    var budget = mulSplitLeafBudget
    if leaves(t, budget): some(t) else: none(RawZ3Ast)
  var c = choice(a)
  var o = rawAnyAstOf(b)
  if c.isNone:
    c = choice(b)
    o = rawAnyAstOf(a)
  if c.isNone: return none(Z3Bool)
  let srt = ctx.checkErr Z3_get_sort(ctx.raw, o)
  let (lo, hi) = intBounds(w)
  proc lit(v: int64): RawZ3Ast = keep(ctx.checkErr Z3_mk_int64(ctx.raw, v, srt))
  proc orOf(x, y: RawZ3Ast): RawZ3Ast =
    var args = @[x, y]
    keep(ctx.checkErr Z3_mk_or(ctx.raw, 2,
      cast[ptr UncheckedArray[RawZ3Ast]](args[0].addr)))
  proc ovf(t: RawZ3Ast): RawZ3Ast =
    var v: int64
    if numeral(t, v):
      if v == 0 or v == 1: return keep(ctx.checkErr Z3_mk_false(ctx.raw))
      if v == -1: return keep(checkedEq(ctx, o, lit(lo)))
      if v > 1:
        return orOf(keep(ctx.checkErr Z3_mk_bvsgt(ctx.raw, o, lit(hi div v))),
                    keep(ctx.checkErr Z3_mk_bvslt(ctx.raw, o, lit(lo div v))))
      return orOf(keep(ctx.checkErr Z3_mk_bvslt(ctx.raw, o, lit(hi div v))),
                  keep(ctx.checkErr Z3_mk_bvsgt(ctx.raw, o, lit(lo div v))))
    let app = Z3_to_app(ctx.raw, t)
    keep(checkedIte(ctx, Z3_get_app_arg(ctx.raw, app, 0),
                    ovf(Z3_get_app_arg(ctx.raw, app, 1)),
                    ovf(Z3_get_app_arg(ctx.raw, app, 2))))
  some(wrap[Z3Bool](ctx, ovf(c.get)))

proc bvOverflowDischarged*(a, b: SymVal, op: IRBinop): bool =
  ## RFC-0005 S8bv. `overflowCond(a, b, op)` is unsatisfiable on structural
  ## grounds: the operands' `bvSignedInterval`s combine to an interval that
  ## fits the width. `lowerArith` then pushes no `OverflowDefect` fork for
  ## the op. A counter a joined loop step increments (`k = ite(g, k + 1,
  ## k)`, `for x in s: inc k` over a builtin set) is bounded by its step
  ## count, so its forks were all infeasible, and each one's boundary query
  ## re-solved the whole chain: a `set[char]` loop ran for minutes.
  let ctx = requireCurrentContext()
  let w = case a.kind
          of svBV8: 8
          of svBV16: 16
          of svBV32: 32
          else: 64
  let x = bvSignedInterval(ctx, rawAnyAstOf(a))
  let y = bvSignedInterval(ctx, rawAnyAstOf(b))
  let r = case op
          of bAdd: add(x, y)
          of bSub: sub(x, y)
          of bMul: mul(x, y)
          else: none(Interval)
  let (lo, hi) = intBounds(w)
  r.isSome and r.get.lo >= lo and r.get.hi <= hi

proc overflowCondInt*(a, b: SymVal, op: IRBinop): Z3Bool =
  ## R3 (S2, walker v91): the Int-sort counterpart to `overflowCond`, for a
  ## WIDTH-TYPED `svInt` operand (`a.ziWidth != 0 and a.ziSigned`). For
  ## linear Integer arithmetic, overflow of a width-typed value is just a
  ## RANGE CHECK: compute the exact (unbounded) result via `a.zi op b.zi`,
  ## then test it against the static Nim type's `[low(T), high(T)]` —
  ## Int comparisons against numerals, cheap for Z3 (no mixed-theory
  ## conversion, unlike the BV predicates `overflowCond` builds — that hang
  ## concern is specific to bv2int/int2bv, not present here). Only called
  ## for `op in {bAdd, bSub, bMul}` — the caller guards this, mirroring
  ## `overflowCond`'s own op restriction (parity with the BV path; the one
  ## division overflow, `low(T) div -1`, is `divLowByMinusOne`'s -- RFC-0005
  ## S8i -- and the R16-3 `divisorIsZero` sink owns the div/mod-by-zero
  ## raise).
  let (lo, hi) = intBounds(a.ziWidth)
  let c = case op
          of bAdd: a.zi + b.zi
          of bSub: a.zi - b.zi
          of bMul: a.zi * b.zi
          else: raise newException(ValueError,  # [raise-audited: category-c: documented caller-guarded invariant (own doc note)]
            "overflowCondInt: unexpected op " & $op)
  c < mkZ3IntLit(lo) or c > mkZ3IntLit(hi)

proc divLowByMinusOne*(a, b: SymVal): Z3Bool =
  ## RFC-0005 S8i. `a == low(T) and b == -1` for a signed operand pair, in
  ## the operands' NATIVE sort (a signed BV, or a width-stamped svInt): the
  ## one signed division whose quotient `-low(T)` is unrepresentable. Nim's
  ## `div` raises `OverflowDefect` there at every width (its check precedes
  ## the division); the C division itself, which `mod` reaches unchecked,
  ## traps (SIGFPE) at 32 and 64 bits -- narrower operands are promoted to
  ## C `int` first, so `low(int8) mod -1 == 0`. Probed on the pinned
  ## toolchain, c and cpp. The caller guards the kind and signedness.
  case a.kind
  of svBV8:  a.bv8  == mkBitVec[8](low(int8))  and b.bv8  == mkBitVec[8](-1)
  of svBV16: a.bv16 == mkBitVec[16](low(int16)) and b.bv16 == mkBitVec[16](-1)
  of svBV32: a.bv32 == mkBitVec[32](low(int32)) and b.bv32 == mkBitVec[32](-1)
  of svBV64: a.bv64 == mkBitVec[64](low(int64)) and b.bv64 == mkBitVec[64](-1)
  of svInt:
    let (lo, _) = intBounds(a.ziWidth)
    a.zi == mkZ3IntLit(lo) and b.zi == mkZ3IntLit(-1)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: kind-narrowed by caller dispatch (own doc: caller-guarded)]
      "divLowByMinusOne: unexpected kind " & $a.kind)

proc divOperandWidth*(a: SymVal): int =
  ## RFC-0005 S8i. The static width of a signed division's operand, or 0
  ## when it has none (an unstamped svInt -- the unbounded `isUnbounded`
  ## integer semantics, where no division overflows).
  case a.kind
  of svBV8: 8
  of svBV16: 16
  of svBV32: 32
  of svBV64: 64
  of svInt: a.ziWidth
  else: 0

proc tryDischargeOverflowInt*(a, b: SymVal, op: IRBinop): Option[Interval] =
  ## Issue #161 slice 2 — the static half of the ADR-0001 amendment.
  ##
  ## `overflowCondInt` builds the predicate `a op b < low(T) or a op b >
  ## high(T)`. This proc tries to prove that predicate FALSE without the
  ## solver, by composing the operands' intervals and testing the result
  ## against the SAME `intBounds(width)` the predicate compares to — so
  ## "discharged" here means exactly "the cond `lowerArith` would have
  ## pushed is unsatisfiable", not something weaker that happens to
  ## correlate. Returns the proven result interval, or `none` when the
  ## proof does not go through (unknown operand, an analysis bound that
  ## overflows `int64`, or a result genuinely outside the type).
  ##
  ## A `none` return is never a soundness event — it just means the fork
  ## gets built and Z3 decides, which is what always happened before.
  if a.ziWidth notin {8, 16, 32, 64}: return none(Interval)
  if a.ziIvl.isNone or b.ziIvl.isNone: return none(Interval)
  let r = case op
          of bAdd: add(a.ziIvl.get, b.ziIvl.get)
          of bSub: sub(a.ziIvl.get, b.ziIvl.get)
          of bMul: mul(a.ziIvl.get, b.ziIvl.get)
          else: none(Interval)
  if r.isNone: return none(Interval)
  let (lo, hi) = intBounds(a.ziWidth)
  if r.get.lo >= lo and r.get.hi <= hi: r else: none(Interval)

proc intWindow*(width: int, signed: bool): tuple[lo, hi: Z3Int,
                                                span: Z3Int,
                                                ivl: Option[Interval]] =
  ## RFC-0005 S8w. The value window of a Nim integer type of `width` bits as
  ## Z3 Int numerals, its size `2^width`, and the window as an `Interval`
  ## when `int64` can hold it (every signed width; unsigned below 64). The
  ## unsigned 64-bit bounds exceed `int64`, so they are built by
  ## arithmetic on numerals rather than read from a literal.
  let two32 = mkZ3IntLit(1'i64 shl 32)
  let span = if width == 64: two32 * two32
             else: mkZ3IntLit(1'i64 shl width)
  if signed:
    let (lo, hi) = intBounds(width)
    (mkZ3IntLit(lo), mkZ3IntLit(hi), span, some(interval(lo, hi)))
  elif width == 64:
    (mkZ3IntLit(0), span - mkZ3IntLit(1), span, none(Interval))
  else:
    let hi = (1'i64 shl width) - 1
    (mkZ3IntLit(0), mkZ3IntLit(hi), span, some(interval(0, hi)))

proc wrapIntToWidth*(r: SymVal): SymVal =
  ## RFC-0005 S8w. A width-stamped `svInt` arithmetic result reduced into
  ## its type's window the way the machine does: `lo + (r - lo) mod 2^w`
  ## (Z3's `mod` is Euclidean, non-negative for a positive divisor), which
  ## is two's-complement wrap-around for a signed type and modular
  ## arithmetic for an unsigned one. An in-window result is itself, so the
  ## term is `ite(lo <= r <= hi, r, <wrapped>)`, and a result whose
  ## propagated interval (`ziIvl`) already lies inside the window is
  ## returned as it is. Before S8w an unbounded `svInt` result never
  ## wrapped: an unsigned or unchecked-signed value computed past its
  ## type's end (`high(int) + 1`, unchecked) was a large positive integer
  ## where the program holds `low(int)` -- a false `sxUnsat` for any
  ## branch on the wrapped value.
  let win = intWindow(r.ziWidth, r.ziSigned)
  if r.ziIvl.isSome and win.ivl.isSome and
     r.ziIvl.get.lo >= win.ivl.get.lo and r.ziIvl.get.hi <= win.ivl.get.hi:
    return r
  let inWin = r.zi >= win.lo and r.zi <= win.hi
  let wrapped = win.lo + ((r.zi - win.lo) mod win.span)
  SymVal(kind: svInt, zi: ite(inWin, r.zi, wrapped), ziWidth: r.ziWidth,
         ziSigned: r.ziSigned, ziIvl: win.ivl)

proc checked*(ac: ArithCheck): bool =
  ## RFC-0016 W1-d2c / D1a, K10d. Is `ac`'s check emitted? The build decides;
  ## a routine that pushed `overflowChecks: on` in a checks-off build raises
  ## `OverflowDefect` and `DivByZeroDefect` all the same: the routine is not
  ## the build. A check the build does not compile in is not forked: the
  ## unchecked operation is undefined and the definedness axis answers it.
  ## RFC-0016 int6: the range check is the code region's (`checkedNow`), so a
  ## conversion's `RangeDefect` follows the routine's own scope.
  if ac == acRange: checkedNow(coRange) else: arithFrames.emits(ac)

proc defProfile*(): DefProfile =
  ## RFC-0016 K10a-axis. The build's arithmetic, as the definedness axis keys
  ## it, for the regime the walk now stands in.
  profile(arithFrames.regime)

func arithOpOf*(op: IRBinop): ArithOp =
  case op
  of bAdd: aoAdd
  of bSub: aoSub
  of bMul: aoMul
  of bDiv: aoDiv
  else: aoMod

proc depositSignedOverflow*(oc: Z3Bool; width: int; op: IRBinop; site: string) =
  ## RFC-0016 W1-d2 (W-07). A signed `+`, `-` or `*` overflow side. With the
  ## build's overflow checks on it is Nim's `OverflowDefect` fork
  ## (`overflowConds`). With them off (the unchecked regime) the C operation is
  ## undefined, so it is the `ubSignedOverflow` trap `drainArithTraps` decides
  ## at the op: an unreachable side is pruned, any other halts.
  ##
  ## RFC-0016 WA-B (P1). Below `int`'s width (8 and 16 bits) the operation is
  ## NOT undefined: Nim emits `(NI8)(a op b)`, the arithmetic happens in C's
  ## promoted `int`, which cannot overflow, and the narrowing wraps (modular on
  ## every supported compiler). There is no undefined side: the result is
  ## wrapped to the width by `lowerArith` and nothing halts.
  ## RFC-0016 K10a-axis: which of the three is the definedness axis's
  ## `(op, signed 8/16 or 32/64)` row at the build's profile. `-d:nelliFwrapv`
  ## (K5a) defines the 32 and 64 bit wrap as well.
  let ans = definedness(arithOpOf(op), arithClass(width in {32, 64}),
                        defProfile())
  case ans.kind
  of dkDefined: return
  of dkUndefined:
    let tr = ArithTrap(cond: oc, ub: some(ans.ub),
                       site: opSite("signed `+`, `-` or `*` overflow", site))
    syncArithTrapCond(tr)
  of dkDefect:
    syncOverflowCond(oc)

proc depositFloatChecks*(r: SymVal; on: set[CheckOption]) =
  ## RFC-0016 PRC-07 (float half). What the C code generator emits after a
  ## float `+ - * /` in a routine compiled with `nanChecks` / `infChecks` on
  ## (read from the generated C of the pinned toolchain): the NaN check first,
  ## `if (r != r) raiseFloatInvalidOp()`, then `if (r != 0.0 && r*0.5 == r)
  ## raiseFloatOverflow(r)`, which holds exactly for an infinite `r`.
  ## `raiseFloatOverflow` (system/integerops.nim) raises `FloatOverflowDefect`
  ## for `r > 0.0` and `FloatUnderflowDefect` otherwise: `-inf` underflows.
  let nan = if r.kind == svFloat32: isNaN(r.fp32) else: isNaN(r.fp64)
  let inf = if r.kind == svFloat32: isInf(r.fp32) else: isInf(r.fp64)
  let neg = if r.kind == svFloat32: isNegative(r.fp32) else: isNegative(r.fp64)
  for (co, cond, name, msg) in [
      (coNan, nan, "FloatInvalidOpDefect", "FPU operation caused a NaN result"),
      (coInf, inf and not neg, "FloatOverflowDefect",
       "FPU operation caused an overflow"),
      (coInf, inf and neg, "FloatUnderflowDefect",
       "FPU operations caused an underflow")]:
    if co in on:
      let t = ArithTrap(cond: cond, site: msg, raiseName: name)
      syncArithTrapCond(t)

proc lowerArith*(a, b: SymVal, op: IRBinop, site = "";
                floatChecks: set[CheckOption] = {}): SymVal =
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
  ## Issue #163 audit W9: the overflow-obligation guards below key on `a`'s
  ## OWN stamp only (`a.ziWidth`/`a.ziSigned`) -- sound when the LEFT operand
  ## of a Nim binop happens to be the one carrying width metadata, but that
  ## metadata is a property of the OPERAND, not of its POSITION. `.len`'s
  ## lowering (`iekSeqLen`, above) builds a bare width-less `svInt` with no
  ## promotion site touching it, so `s.len - x`/`s.len * x` for a promoted
  ## range-typed `x` left the guard permanently unarmed when `x * s.len`
  ## (same values, swapped) already worked -- a silent false-`sxUnsat` for
  ## exactly the shape #161's obligation machinery exists to close. Nim's
  ## typing already guarantees both operands of a binop share one static
  ## width/signedness (the same argument `arithInt`'s own a-then-b width
  ## fallback, just below, and `toSvIntPreserving`'s doc comment both make),
  ## so borrowing `b`'s stamp onto `a` here is a fallback, never a merge:
  ## when both sides are stamped (the common case) or neither is, this is a
  ## no-op and changes nothing.
  if a.kind == svInt and a.ziWidth == 0 and
     b.kind == svInt and b.ziWidth != 0:
    a.ziWidth = b.ziWidth
    a.ziSigned = b.ziSigned
  ##
  ## R16-3: for bDiv/bMod on non-float types, push `divisorIsZero(b)` to the
  ## `divByZeroConds` sink BEFORE dispatching. `arithInt`/`divBV`/`modBV` are
  ## unchanged; the cond fires from the pre-lower path in `drainDivByZeroRaises`.
  ## R16-4: for bAdd/bSub/bMul on signed BV operands, push `overflowCond(a,b,op)`
  ## to the `overflowConds` sink BEFORE dispatching. `binBV` is unchanged; the
  ## cond fires from the pre-lower path in `drainOverflowRaises`.
  ## R3 (S2, walker v91): the svInt sibling — for bAdd/bSub/bMul on a
  ## WIDTH-TYPED svInt operand (`a.ziWidth != 0`, static Nim type known) and
  ## `a.ziSigned` (Nim wraps unsigned silently — no OverflowDefect, mirroring
  ## the BV branch's own `a.signed` guard), push `overflowCondInt(a,b,op)` to
  ## the SAME `overflowConds` sink — `arithInt` is unchanged; the cond fires
  ## from the same pre-lower path in `drainOverflowRaises`, kind-agnostic.
  if op in {bDiv, bMod} and a.kind notin {svFloat32, svFloat64}:
    let c = divisorIsZero(b)
    let unsignedDiv = (a.kind in {svBV8, svBV16, svBV32, svBV64} and
                       not a.signed) or
                      (a.kind == svInt and a.ziWidth != 0 and not a.ziSigned)
    # RFC-0016 K10a-axis: the divisor row of the definedness axis. Unsigned,
    # Nim has no check and the C division is undefined. Signed, the zero
    # check is Nim's (a `DivByZeroDefect` fork below) and with the checks off
    # (WA-B, S3) the C division by zero is undefined as the unsigned one is:
    # the zero side halts, it is not a definite trap.
    let zeroAns = definedness(arithOpOf(op),
      (if unsignedDiv: ocZeroDivisorUnsigned else: ocZeroDivisorSigned),
      defProfile())
    let divTrap =
      if zeroAns.kind == dkUndefined:
        ArithTrap(cond: c, ub: some(zeroAns.ub),
                  site: opSite(if unsignedDiv:
                           (if op == bDiv: "`x div 0'u`" else: "`x mod 0'u`")
                         else:
                           (if op == bDiv: "`x div 0`" else: "`x mod 0`"), site))
      else: ArithTrap(cond: c)
    if arithFrames.regime == rgUnchecked:
      # RFC-0005 S8aa: Nim's zero-divisor check is part of its overflow
      # checks (the C code generator emits it only under `overflowChecks`),
      # so with them off -- `acOverflow` excluded, the unchecked regime --
      # `x div 0` and `x mod 0` reach the C division itself, which traps
      # (x86 `idiv` / `div`, SIGFPE) at every width and signedness. Probed
      # on the pinned toolchain in the debug build a test replays under, c
      # and cpp, with `{.push overflowChecks: off.}`: `5 div 0` and
      # `5 mod 0` abort with "SIGFPE: Arithmetic error", and no `except`
      # arm runs. So it is the survivor-only trap sink, as `low(T) div -1`
      # is below, and never a `DivByZeroDefect` raise, whatever
      # `acDivByZero` says. Before S8aa the raise was forked (its witness
      # aborts the process on replay) and, with `acDivByZero` off too, the
      # continuation carried Z3's `x div 0` value, a state Nim never
      # reaches.
      syncArithTrapCond(divTrap)
    elif unsignedDiv:
      # RFC-0016 W1-d1b: Nim's zero-divisor check covers the signed types
      # only; an unsigned `x div 0` / `x mod 0` reaches the C division and
      # traps (SIGFPE, probed c and cpp, default build), so it is no
      # `DivByZeroDefect` and no `except` arm runs. The C division is
      # undefined there, so the zero side halts (section 9.1 item 1).
      syncArithTrapCond(divTrap)
    else:
      syncDivByZeroCond(c)
  if op in {bAdd, bSub, bMul} and a.kind in {svBV8, svBV16, svBV32, svBV64} and
     a.signed and not bvOverflowDischarged(a, b, op):   # RFC-0005 S8bv
    depositSignedOverflow(overflowCond(a, b, op),
                          case a.kind
                          of svBV8: 8
                          of svBV16: 16
                          of svBV32: 32
                          else: 64, op, site)
  elif op in {bAdd, bSub, bMul} and a.kind == svInt and a.ziWidth != 0 and a.ziSigned:
    # Issue #161 slice 2. The obligation is raised unconditionally; what
    # varies is who discharges it. Try the static proof first, and record
    # the outcome either way — `obligationLog` is the audit trail that
    # makes "we proved this" checkable rather than asserted.
    let proven = tryDischargeOverflowInt(a, b, op)
    if proven.isSome:
      obligationLog.add ObligationEntry(
        op: op, width: a.ziWidth, signed: a.ziSigned,
        disposition: odDischargedStatic, bound: proven)
    else:
      obligationLog.add ObligationEntry(
        op: op, width: a.ziWidth, signed: a.ziSigned,
        disposition: odLive, bound: none(Interval))
      depositSignedOverflow(overflowCondInt(a, b, op), a.ziWidth, op, site)
  # RFC-0005 S8i: signed `div`/`mod` of `low(T)` by `-1`. `div` raises
  # `OverflowDefect` (Nim's check, at every width) -- the `overflowConds`
  # sink, acOverflow-gated like add/sub/mul. At 32 and 64 bits the C
  # division itself traps (SIGFPE, an uncatchable abort): `mod` always
  # reaches it (Nim has no check there), and so does `div` with overflow
  # checks off -- the survivor-only `arithTrapConds` sink, drained after the
  # overflow raises. Before S8i neither was modelled: `low(int) div -1`
  # continued as `low(int)`, `low(int) mod -1` as 0.
  if op in {bDiv, bMod}:
    let signedOp = (a.kind in {svBV8, svBV16, svBV32, svBV64} and a.signed) or
                   (a.kind == svInt and a.ziWidth != 0 and a.ziSigned)
    let width = divOperandWidth(a)
    let loExcluded = a.kind == svInt and a.ziIvl.isSome and width != 0 and
                     a.ziIvl.get.lo > intBounds(width)[0]
    if signedOp and width in {8, 16, 32, 64} and not loExcluded:
      let tc = divLowByMinusOne(a, b)
      # RFC-0016 K10a-axis: the `low(T) by -1` row of the definedness axis.
      let lowAns = definedness(arithOpOf(op),
        (if width in {32, 64}: ocLowByMinusOneWide
         else: ocLowByMinusOneNarrow), defProfile())
      if lowAns.kind == dkDefect:
        syncOverflowCond(tc)
      if width in {32, 64}:
        # RFC-0016 W1-d1a: `mod` has no Nim check, and `div` has none with
        # the overflow checks off, so the C division is UNDEFINED there
        # (section 9.1); with the checks on, `div` is the `OverflowDefect`
        # fork above and the survivor is merely confined.
        let tr =
          if lowAns.kind == dkUndefined:
            ArithTrap(cond: tc, ub: some(lowAns.ub),
                      site: opSite(if op == bMod: "`low(T) mod -1`"
                                   else: "`low(T) div -1`", site))
          else:
            ArithTrap(cond: tc)
        syncArithTrapCond(tr)
  if a.kind == svInt:
    # RFC-0005 S8w: a width-stamped result wraps where the machine's does:
    # always for an unsigned type (Nim's unsigned arithmetic is modular),
    # and for a signed one when the build's arithmetic is unchecked
    # (the unchecked regime). With checked signed arithmetic the value never
    # leaves the window on a surviving path (`overflowCondInt` forks the
    # raise), so there is nothing to wrap. `div` joins for the signed
    # case: `low(T) div -1` at 8 and 16 bits yields `-low(T)` in C's
    # promoted `int` and wraps back to `low(T)` (32 and 64 bits trap,
    # `arithTrapConds` above).
    let r = arithInt(a, b, op)
    if r.ziWidth in {8, 16, 32, 64} and r.ziSigned and
       arithFrames.regime == rgUnchecked and op == bDiv:
      # RFC-0005 S8ac: a truncated quotient is never further from zero than
      # its dividend, so the one quotient outside the window is `low(T) div
      # -1` (`-low(T)`), which wraps back to `low(T)` (at 32 and 64 bits the
      # path is confined off it by the trap above, so either value is
      # exact). Selecting it directly keeps the wrap linear. `wrapIntToWidth`
      # reduced the whole NONLINEAR quotient `mod 2^w` instead, and an exact
      # `start div y` (a stamped offset over a bitvector parameter) ran out
      # of `seqQueryRLimit` or past 900 s on that one term.
      let win = intWindow(r.ziWidth, true)
      SymVal(kind: svInt, zi: ite(divLowByMinusOne(a, b), win.lo, r.zi),
             ziWidth: r.ziWidth, ziSigned: true, ziIvl: win.ivl)
    elif r.ziWidth in {8, 16, 32, 64} and
       (not r.ziSigned and op in {bAdd, bSub, bMul}):
      # RFC-0016 W1-d2: a signed result needs no wrap here. Checked, the
      # raise fork leaves the survivors in the window; unchecked, the
      # `ubSignedOverflow` trap does.
      wrapIntToWidth(r)
    elif r.ziWidth in {8, 16, 32, 64} and r.ziSigned and
         op in {bAdd, bSub, bMul} and
         wrapDefined(arithFrames.regime, arithOpOf(op), r.ziWidth):
      # RFC-0016 WA-B (P1): a signed 8 or 16 bit result is computed in `int`
      # and narrowed back, a defined wrap (`depositSignedOverflow` halts
      # nothing there). K5a: so is a 32 or 64 bit one under `-fwrapv`.
      wrapIntToWidth(r)
    else:
      r
  elif a.kind in {svFloat32, svFloat64}:
    let r = arithFloat(a, b, op)        # Phase 15 F3
    if floatChecks != {} and op in {bAdd, bSub, bMul, bDiv}:
      depositFloatChecks(r, floatChecks)
    r
  else:
    case op
    of bAdd: binBV(a, b, `+`)
    of bSub: binBV(a, b, `-`)
    of bMul: binBV(a, b, `*`)
    of bDiv: divBV(a, b)
    of bMod: modBV(a, b)
    else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]

const seqEqUnrollMax* = 64
  ## RFC-0016 PRC-34. The longest length bound `seqEqZ3` unrolls over; a seq
  ## with no bound this small declines.

proc seqLenUpperBound*(l: Z3Int): Option[int] =
  ## RFC-0016 PRC-34. A sound upper bound on the length term `l`, read off
  ## its structure alone: a numeral is its own bound, an `ite` the larger of
  ## its two arms' (a seq merged across a branch). Anything else (an input's
  ## length, a computed one) has none here: the path condition's facts are
  ## not in reach of a lowering (`lowerCmp` has no path), and the solver's
  ## `maxSeqLen` cap is a search bound, not a fact about the program.
  let ctx = l.ctx
  proc kindOf(a: RawZ3Ast): int =
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
  let probeC = mkBoolVar(ctx, "__s8cpr_len_probe_c")
  let probeI = mkIntVar(ctx, "__s8cpr_len_probe_i")
  let iteKind = kindOf(ite(probeC, probeI, probeI).raw)
  proc bound(a: Z3AnyAst; depth: int): Option[int] =
    if depth > 16: return none(int)
    case getAstKind(a)
    of akNumeral:
      try: some(parseInt(getNumeralString(a)))
      except CatchableError: none(int)
    of akApp:
      if kindOf(a.raw) != iteKind: return none(int)
      let (_, args) = unpackApp(a)
      if args.len != 3: return none(int)
      let x = bound(args[1], depth + 1)
      let y = bound(args[2], depth + 1)
      if x.isNone or y.isNone: none(int) else: some(max(x.get, y.get))
    else: none(int)
  bound(toAnyAst(simplify(l)), 0)

proc maskedSeqData*(ctx: Z3Context; data: Z3AnyAst; len: Z3Int;
                   dflt: Z3AnyAst): Z3AnyAst =
  ## RFC-0016 PRC-34. The data array of a seq with every index outside
  ## `0 ..< len` mapped to `dflt`: the term
  ## `lambda i. ite(0 <= i and i < len, data[i], dflt)`. A lambda is an
  ## array term, not an axiom: Z3 beta-reduces a `select` of it, and a
  ## disequality of two of them is one skolem witness (array
  ## extensionality), so no universal over the array is asserted (the G4
  ## hang lesson).
  let i = mkIntVar(ctx, "__seqEqMaskI")
  let inRange = (mkInt(0) <= i) and (i < len)
  # Each raw term is wrapped (owned) before the next API call.
  let sel = wrap[Z3AnyAst](ctx, checkedSelect(ctx, data.raw, i.raw))
  let body = wrap[Z3AnyAst](ctx, checkedIte(ctx, inRange.raw, sel.raw, dflt.raw))
  var bound = [Z3_to_app(ctx.raw, i.raw)]
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_lambda_const(ctx.raw, cuint(1),
    cast[ptr UncheckedArray[RawZ3App]](addr bound[0]), body.raw))

proc seqEqMasked*(a, b: SymVal): Option[Z3Bool] =
  ## RFC-0016 PRC-34. Whole-seq `==` with no length bound: equal lengths and
  ## equal masked data arrays (`maskedSeqData`). Exact where the element's
  ## `==` is Z3's equality of its term: an integer, a `bool`, a `char`, a
  ## `string`. A float's IEEE `==` is not (a NaN is unequal to itself, and
  ## `0.0 == -0.0`), so a float element declines here. The default outside
  ## the length is one value for both sides, so which value it is cannot
  ## matter once the lengths are equal.
  if a.seqElemTy.kind in {itFloat32, itFloat64}: return none(Z3Bool)
  let ctx = a.seqLen.ctx # [placeholder-audited]
  let sa = sortOfRaw(ctx, a.seqDataRaw.raw) # [placeholder-audited]
  if sa != sortOfRaw(ctx, b.seqDataRaw.raw): return none(Z3Bool) # [placeholder-audited]
  let rng = ctx.checkErr Z3_get_array_sort_range(ctx.raw, sa)
  let dflt = wrap[Z3AnyAst](ctx,
    case Z3_get_sort_kind(ctx.raw, rng)
    of Z3_BOOL_SORT: ctx.checkErr Z3_mk_false(ctx.raw)
    of Z3_BV_SORT, Z3_INT_SORT: ctx.checkErr Z3_mk_int(ctx.raw, 0, rng)
    else:
      if a.seqElemTy.kind != itString: return none(Z3Bool)
      ctx.checkErr Z3_mk_string(ctx.raw, ""))
  let ma = maskedSeqData(ctx, a.seqDataRaw, a.seqLen, dflt) # [placeholder-audited]
  let mb = maskedSeqData(ctx, b.seqDataRaw, b.seqLen, dflt) # [placeholder-audited]
  some((a.seqLen == b.seqLen) and # [placeholder-audited]
       wrap[Z3Bool](ctx, checkedEq(ctx, ma.raw, mb.raw)))

proc seqEqZ3*(a, b: SymVal): Option[Z3Bool] =
  ## RFC-0016 PRC-34. System's `==` on two seqs of a scalar element (the
  ## parser admits only an element type whose `==` is system's own): equal
  ## lengths, and each element equal under the element's `==` (IEEE on a
  ## float, so a NaN element is unequal to itself). Quantifier free (the G4
  ## hang lesson, `docs/SYMEX_PLAN.md`: no universal over an array): when
  ## either length has a sound upper bound `n` of at most `seqEqUnrollMax`
  ## (`seqLenUpperBound`), the elements are compared at `0 ..< n`, each
  ## conjunct guarded by its index being below the length. none when there
  ## is no such bound, or the model has no exact form: a placeholder, a tree
  ## element, or a seq that may hold an unwritten `newSeqUninit` element
  ## (native `==` reads it); the caller then declines (`eqBV`).
  if a.isUnsupportedFieldPlaceholder or b.isUnsupportedFieldPlaceholder: # [placeholder-audited]
    return none(Z3Bool)
  if a.seqElemTy == nil or b.seqElemTy == nil or
     a.seqElemTy.kind notin {itInt, itBool, itFloat32, itFloat64, itString} or
     a.seqElemTy.kind != b.seqElemTy.kind or isTreeSeqElemTy(a.seqElemTy) or
     a.seqDataMore.len > 0 or b.seqDataMore.len > 0:
    return none(Z3Bool)
  if a.seqElemTy.kind == itInt and a.seqElemTy.width != b.seqElemTy.width:
    return none(Z3Bool)
  if svMentionsUninit(a) or svMentionsUninit(b): return none(Z3Bool)
  let la = seqLenUpperBound(a.seqLen) # [placeholder-audited]
  let lb = seqLenUpperBound(b.seqLen) # [placeholder-audited]
  let n =
    if la.isSome and lb.isSome: some(min(la.get, lb.get))
    elif la.isSome: la
    else: lb
  if n.isNone or n.get > seqEqUnrollMax: return seqEqMasked(a, b)
  var acc = a.seqLen == b.seqLen # [placeholder-audited]
  for i in 0 ..< n.get:
    acc = acc and implies(mkInt(i) < a.seqLen, # [placeholder-audited]
      svLeafEq(seqElemAt(a, mkInt(i)), seqElemAt(b, mkInt(i))))
  some(acc)

proc lowerCmp*(a, b: SymVal, op: IRBinop): SymVal =
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
      # RFC-0005 S8cb (item 5): system's order on bool, `false < true` (it
      # was a fresh bool, `feUnsupportedOpHavoc`, since RFC-0005 S6b).
      # (`lowerCmp` is reached with comparison operators only, and raises
      # nothing: see `loweringDidDegrade`.)
      case op
      of bLt: ofBool((not lb.bo) and rb.bo)
      of bLe: ofBool((not lb.bo) or rb.bo)
      of bGt: ofBool(lb.bo and (not rb.bo))
      else: ofBool(lb.bo or (not rb.bo))    # bGe
  elif a.kind in {svFloat32, svFloat64}:
    cmpFloat(a, b, op)        # Phase 15 F2: IEEE ==/!=; F4 adds ordering
  elif a.kind == svString:
    cmpString(a, b, op)       # Phase 15 S1: Z3 String ==/!= (S3 adds </<=)
  elif a.kind == svSeq and b.kind == svSeq and op in {bEq, bNe}:
    # RFC-0016 PRC-34: whole-seq `==` (`seqEqZ3`); a seq it has no exact
    # form for keeps `eqBV`'s / `neBV`'s decline.
    let eq = seqEqZ3(a, b)
    if eq.isSome: ofBool(if op == bEq: eq.get else: not eq.get)
    elif op == bEq: eqBV(a, b)
    else: neBV(a, b)
  else:
    case op
    of bEq: eqBV(a, b)
    of bNe: neBV(a, b)
    of bLt: cmpBV(a, b, bvslt, bvult)
    of bLe: cmpBV(a, b, bvsle, bvule)
    of bGt: cmpBV(a, b, bvsgt, bvugt)
    of bGe: cmpBV(a, b, bvsge, bvuge)
    else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]


proc degradeStrArm*(e: IRExpr, kind: SymexErrorKind, msg: string): SymVal =
  ## Round-6 N36 (walker v101, ADR-0023/SND-3 chokepoint). Shared in-band
  ## degrade converter for every classified raise `lowerStrArm`
  ## (`runtime_strings.nim`) can produce: `SymexUnsupportedStringOpError`,
  ## `SymexZ3VersionMissingError`, `SymexZ3StringIncompleteError`,
  ## `SymexUnsupportedRegexError`. Called from the SINGLE
  ## `lowerStrArm(env, e)` call site in `lower`'s dispatch (immediately
  ## below) rather than at each of `lowerStrArm`'s ~18 individual raw-raise
  ## sites (`requireStr`, `needleAsStr`, the join/split/regex/radix/
  ## case-fold arms, the "not modeled" catch-all). This is the SAME hazard
  ## N31 fixed for the single `iekStrSubstr` CR-17 site: a raw `raise`
  ## reached from inside nested `walkBlock` frames is silently LOST by
  ## Nim's C-backend goto-exception unwind — `lower()` returns as if
  ## nothing happened, `w.sawUnknown` is never set, and the walker's
  ## default-to-UNSAT fallback can report a false `sxUnsat` for a
  ## concretely reachable target.
  ##
  ## SOUNDNESS OF THE CHOKEPOINT PLACEMENT: the unwind from ANY raise inside
  ## `lowerStrArm` to this `except` crosses ONLY plain proc frames
  ## (`lowerStrArm` itself, `requireStr`, `needleAsStr`, `mkConcreteStrSeq`,
  ## `joinStrSeq`, `runeToUtf8Sym`) — none of which is a `walkBlock` frame.
  ## `lowerStrArm` calls `lower()` recursively for its operand sub-exprs, but
  ## never calls `walk`/`walkBlock` itself (it has no `WalkCtx`/`Path` in
  ## scope — see its own doc comment). So the raise-to-catch path here is
  ## ALWAYS exactly one level deep, REGARDLESS of how many `walkBlock` frames
  ## sit above this `lower()` call in the walker's own call chain — the
  ## hazard the C-backend goto-exception model exposes only grows with
  ## intervening `walkBlock` frames on the unwind path, and there are never
  ## any between a `lowerStrArm` raise and this catch.
  ##
  ## Converts exactly like `iekStrSubstr`'s pre-existing CR-17 in-band
  ## degrade (N31): record the classified error, taint the lowering
  ## (`loweringDidDegrade`), and manufacture a FRESH unconstrained symbol of
  ## the arm's INTENDED result kind — determined from `e.kind` alone, since
  ## the caught exception carries no static result-type information.
  ## `drainPendingLowerEffects` (the mandatory drain at every `lower()` call
  ## site inside `walk`) forks the path `uncertain` and sets `w.sawUnknown`
  ## regardless of nesting depth once this returns, so the verdict is
  ## `sxUnknown` at ANY nesting depth — never a silently-lost raise.
  queueDegrade(kind, msg)
  var fresh: seq[Z3Bool]
  case e.kind
  of iekStrLen, iekStrFind, iekStrRfind, iekStrCount, iekStrToInt, iekStrFindRe:
    # Successful-path result is svInt (Z3Int) — e.g. `s.len`/`s.find(...)`
    # build `SymVal(kind: svInt, ...)` directly. Force `allocateSym(itInt)`'s
    # bare (non-tuple) svInt allocation via `intOffsetPositions = @[0]`
    # (its own doc comment: "0 addresses a bare (non-tuple) `itInt`
    # allocation") rather than its type-driven BV default.
    allocateSym(tInt(), freshDegradeName("__strArmDegrade"), fresh, intOffsetPositions = @[0])
  of iekStrAt:
    # Successful-path result is svBV8 unsigned (a Nim `char`).
    allocateSym(tInt(8, signed = false), freshDegradeName("__strArmDegrade"), fresh)
  of iekStrContains, iekStrStartsWith, iekStrEndsWith, iekStrMatch,
     iekStrInOptionRegion:
    allocateSym(tBool(), freshDegradeName("__strArmDegrade"), fresh)
  of iekStrSplit:
    allocateSym(tSeq(tString()), freshDegradeName("__strArmDegrade"), fresh)
  of iekStrChars:   # RFC-0005 S8ca: a seq of chars
    allocateSym(tSeq(tInt(8, signed = false)),
                freshDegradeName("__strArmDegrade"), fresh)
  of iekStrUnsupported:
    # S10b adjudication (walker v116) + fix-slice item 5 (round-6 re-review):
    # `iekStrUnsupported`'s callers span string/int/float/bool-ish contexts
    # (parseFloat, toOct, string mutation, $ on a float, an unrecognized
    # stdlib string-method name, …) but the placeholder this arm manufactures
    # was ALWAYS svString regardless — correct for callers whose successful
    # path really does return a string, but WRONG for any int/bool/float
    # caller. That mismatch was silent until a downstream op touched the
    # placeholder: `parseFloat(s) == 1.5` compares the fabricated svString
    # against an svFloat64 RHS, and `cmpString` (called because the LHS
    # reports svString) doesn't expect a non-string operand — the resulting
    # crash/assertion escapes uncaught to the whole-run catch-all and reports
    # `weInternalWalkerFault`, masking the classified `seUnsupportedStringOp`
    # this proc already recorded two lines above. The SAME class reproduces
    # for any unmodeled int/bool-returning stdlib string call reaching the
    # generic name-lookup fallback (`dsl_parser.nim`'s `getStdlibModelFor`
    # `smkUnregistered` arm) — `parseFloat` was only the first-discovered
    # instance, not the only one, so keying on `e.strOp` (a per-name allow-
    # list that a NEW unmodeled int/bool-returning call would silently miss)
    # was never total. `e.strRetTy` (parser-threaded, `types.nim`) is the
    # call EXPRESSION's own classified static type — total by construction,
    # never a per-name lookup — so this now dispatches on the type directly.
    case e.strRetTy.kind
    of itFloat32: allocateSym(tFloat32(), freshDegradeName("__strArmDegrade"), fresh)
    of itFloat64: allocateSym(tFloat64(), freshDegradeName("__strArmDegrade"), fresh)
    of itBool:    allocateSym(tBool(), freshDegradeName("__strArmDegrade"), fresh)
    of itInt:
      # Mirrors this proc's OWN `iekStrLen`/`iekStrFind`/… arm above: force
      # the bare (non-tuple) `svInt` allocation via `intOffsetPositions =
      # @[0]` rather than `allocateSym`'s type-driven BV default.
      allocateSym(tInt(e.strRetTy.width, e.strRetTy.signed),
                  freshDegradeName("__strArmDegrade"), fresh,
                  intOffsetPositions = @[0])
    of itSeq, itTuple:
      # RFC-0005 S8ay: a declined `std/re` call -- `findAll` / `split`
      # (seq[string]), `findBounds` (tuple[first, last: int]). A string
      # placeholder there is the wrong sort for the enclosing expression.
      allocateSym(e.strRetTy, freshDegradeName("__strArmDegrade"), fresh)
    else:
      # itString and every other (seq/table/…) shape: the pre-existing
      # svString default. Sound over-approximation even for a genuinely
      # composite return — the placeholder's CONTENT is never trustworthy
      # once the run has degraded, only its sort needs to be well-formed,
      # and a composite `iekStrUnsupported` caller is not a traced live
      # shape (every currently-known stdlib string-method return type is
      # itString/itInt/itBool/itFloat*).
      allocateSym(tString(), freshDegradeName("__strArmDegrade"), fresh)
  else:
    # iekStrLit, iekStrSubstr, iekStrReplaceAll, iekStrJoin,
    # iekStrReplaceRe, iekIntToStr, iekRadixFmt, iekStrToLower, iekStrToUpper,
    # iekRuneToStr, iekStrStrip, iekStrConcat all have svString on their
    # successful path — the least-surprising default for anything landing
    # here. (`iekStrUnsupported`, the genuine "not modeled" catch-all whose
    # callers are NOT uniformly string-shaped, has its own arm above.)
    allocateSym(tString(), freshDegradeName("__strArmDegrade"), fresh)


# ---- RFC-0005 S8bw (item 2): a global's unwritten parts ---------------------
#
# A module-level global is bound in the walk's env at its first write (S8an).
# A tuple, object or array global is written a part at a time: `g.a = v`
# rebuilds `g` from `v` and copies of its other parts (`valueFieldWrite`).
# Before any write those parts hold whatever the program left there, which
# the walk does not know. The value a read of an unbound global gives is its
# INITIAL value: one constant per leaf of its declared type, the same for
# every read in the run (`globalInitValue`). Each such constant is an
# UNWRITTEN leaf (`glUnwritten`). Copying one is no observation: a rebuild's
# copies (`iekVar.vCopy`) carry the leaves back into `g`, and a later write
# replaces them. Every other read -- the outermost access of a chain over a
# global (`g`, `g.b`, `g.arr[i]`), an element read, a pointer's dereference,
# a discriminator's reassignment -- declines (`feGlobalReadUnmodelled`, as a
# scalar global read before any write does) when its value mentions one.

var glUnwrittenCtx* {.threadvar.}: RawZ3Context
var glUnwritten* {.threadvar.}: Table[int, string]
  ## Ast id of each unwritten leaf -> the part it stands for (`gArr[2]`).
var glPartHavoc* {.threadvar.}: Table[string, bool]
  ## RFC-0005 batch 6. Each unwritten part -> whether its global's entry
  ## value is modelled (S8as, `programGlobal`): observing it then taints
  ## the path `feGlobalHavoc` (a SAT is replayed, an UNSAT stands); any
  ## other global's part declines (`feGlobalReadUnmodelled`, S8bw).
var glWatched* {.threadvar.}: HashSet[string]
  ## RFC-0005 S8bz (item 3). The names that are no global but may hold an
  ## unwritten part, whose reads therefore observe: a `var` formal whose
  ## actual holds one, an element read's temporary (the access on it picks
  ## the part), a `{.noinit.}` local.
var glVarGlobal* {.threadvar.}: Table[string, string]
  ## RFC-0005 batch 11 (S8bz over S8cs). A `var` formal -> the global its actual
  ## names (through a field or index chain, or another such formal). S8bz reads
  ## the actual as a copy-in (`vCopy`), which observes nothing; the formal's
  ## read is where the global's value enters, so S8cs's route check runs there.
var glUnwrittenAsts* {.threadvar.}: seq[Z3AnyAst]
  ## The unwritten leaves themselves (`unwrittenIndependent` renames them).
var lowerAsReceiver* {.threadvar.}: bool
  ## Set by an access arm (`iekField`, `iekIndex`, `isIndex`) right before
  ## it lowers its receiver; consumed at `lower`'s entry. A receiver's value
  ## is not observed by itself: the access's result is.

proc glUnwrittenFresh*(ctx: Z3Context) =
  ## A new context is a new run: no unwritten leaf is live.
  if glUnwrittenCtx != ctx.raw:
    glUnwrittenCtx = ctx.raw
    glUnwritten = initTable[int, string]()
    glPartHavoc = initTable[string, bool]()
    glUnwrittenAsts = @[]
    glWatched = initHashSet[string]()
    glVarGlobal = initTable[string, string]()

proc svAsts*(sv: SymVal; acc: var seq[RawZ3Ast]) =
  ## Every Z3 term a value holds, compound or not.
  case sv.kind
  of svBV8, svBV16, svBV32, svBV64, svInt, svBool, svFloat32, svFloat64,
     svString, svRef, svPtr, svBitSet:
    acc.add rawAnyAstOf(sv)
  of svTuple:
    for f in sv.fields: svAsts(f, acc)
  of svArray:
    for f in sv.arrElems: svAsts(f, acc)
  of svSeq:
    # RFC-0005 batch 6: every leaf array of a leaf-split seq (S8bc), not
    # only the first -- an unwritten leaf held in a later one is seen.
    for a in seqArrs(sv): acc.add a.raw
    acc.add sv.seqLen.raw # [placeholder-audited]
  of svTable:
    acc.add sv.tabDataRaw.raw
    for m in sv.tabDataMore: acc.add m.raw   ## RFC-0005 batch 6 (S8at)
    acc.add sv.tabPresentRaw.raw
    acc.add sv.tabSize.raw
  of svSet:
    acc.add sv.setMembersRaw.raw
    acc.add sv.setSize.raw
  of svVariant:
    svAsts(sv.vDisc[], acc)
    for fs in sv.vArmFields.values:
      for f in fs: svAsts(f, acc)
    for f in sv.vPlainFields: svAsts(f, acc)
    for c in sv.vImage: acc.add c.raw             # RFC-0016 PRC-07 slice B
    if sv.vActive != nil: svAsts(sv.vActive[], acc)
  of svMultiVariant:
    for ax in sv.mvAxes:
      svAsts(ax.disc[], acc)
      for fs in ax.armFields.values:
        for f in fs: svAsts(f, acc)
    for f in sv.mvPlainFields: svAsts(f, acc)
  of svDistinct:
    acc.add sv.distinctAst.raw
    if sv.distinctBaseSym != nil: svAsts(sv.distinctBaseSym[], acc)
  of svUninterpRef:
    acc.add sv.uninterpAst.raw
  of svClosure:
    if sv.closureEnv != nil: svAsts(sv.closureEnv[], acc)

proc registerUnwritten*(ctx: Z3Context; sv: SymVal; part: string;
                        havoc: bool) =
  ## Record each leaf of the initial value `sv` of `part` as unwritten.
  ## `havoc`: the global's entry value is modelled (`glPartHavoc`).
  case sv.kind
  of svTuple:
    for i, f in sv.fields:
      registerUnwritten(ctx, f, part & "." &
        (if i < sv.fieldNames.len: sv.fieldNames[i] else: $i), havoc)
  of svArray:
    for i, f in sv.arrElems:
      registerUnwritten(ctx, f, part & "[" & $i & "]", havoc)
  else:
    # RFC-0005 S8bz (items 3, 4): written-ness per part. A scalar part of a
    # global whose whole entry value is not modelled (an object holding a
    # `ref` beside it) still holds some value of its type.
    glPartHavoc[part] = havoc or sv.kind in {svBV8, svBV16, svBV32, svBV64,
      svInt, svBool, svFloat32, svFloat64, svString}
    var acc: seq[RawZ3Ast]
    svAsts(sv, acc)
    for a in acc:
      glUnwritten[astId(ctx, a)] = part
      glUnwrittenAsts.add wrap[Z3AnyAst](ctx, a)

var globalEntryVals* {.threadvar.}: Table[string, SymVal]
  ## RFC-0005 S8as. The entry value of each `var` global (or computed `let`)
  ## read before the walk wrote it: one fresh value per run, shared by every
  ## path and frame (`entryValueOf`). Reset per run. RFC-0005 batch 6: also
  ## S8bw's initial value of a global whose entry value is not modelled
  ## (`globalInitValue`); one store, one set of unwritten leaves.
proc globalInitValue*(name: string; ty: IRType): SymVal =
  ## The value the global `name` of declared type `ty` holds before its
  ## first write in the walk: its unwritten leaves. RFC-0005 batch 6: a
  ## global whose entry value S8as does not model (`programGlobal` is
  ## none); an observation of one of its leaves declines.
  let ctx = requireCurrentContext()
  glUnwrittenFresh(ctx)
  if globalEntryVals.hasKey(name): return globalEntryVals[name]
  var facts: seq[Z3Bool]
  result = allocateSym(ty, "__glInit_" & displayName(name), facts)
  globalEntryVals[name] = result
  block:   # RFC-0016 INT-82: a global's entry value is entry state
    var acc: seq[RawZ3Ast]
    svAsts(result, acc)
    notePreExistingTerms(ctx, acc)
  registerUnwritten(ctx, result, displayName(name), havoc = false)

var noinitSerial* {.threadvar.}: int
  ## RFC-0005 S8bz (item 7). Numbers the initial values of `{.noinit.}`
  ## locals: every evaluation of the declaration is its own.

proc noinitValue*(e: IRExpr): SymVal =
  ## RFC-0005 S8bz (item 7). The initial value of a `{.noinit.}` local: one
  ## fresh constant per leaf, each unwritten. Nim leaves the local's bytes as
  ## they were, so any value of the type is possible, and a read of a part no
  ## write reached taints the path (`feGlobalHavoc`: a SAT is replayed, and an
  ## UNSAT holds for every value). A rebuild's copy observes nothing.
  let ctx = requireCurrentContext()
  glUnwrittenFresh(ctx)
  let local = e.vname[noinitReadPrefix.len .. ^1]
  inc noinitSerial
  var facts: seq[Z3Bool]
  result = allocateSym(e.vGlobalTy, "__noinit_" & local & "_" & $noinitSerial,
                       facts)
  for f in facts: globalEntryFacts.add f
  registerUnwritten(ctx, result, noinitReadPrefix & local, havoc = true)
  glWatched.incl local

proc unwrittenIn*(sv: SymVal; simplified = false): string =
  ## The part an unwritten leaf `sv` mentions stands for, or "" when it
  ## mentions none. `simplified`: an element read's `ite` over every
  ## element is simplified first, so a constant index picks its element.
  if glUnwritten.len == 0: return ""
  let ctx = currentContext()
  if ctx == nil or glUnwrittenCtx != ctx.raw: return ""
  var roots: seq[RawZ3Ast]
  svAsts(sv, roots)
  var keep: seq[Z3AnyAst]
  if simplified:
    for i in 0 ..< roots.len:
      keep.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_simplify(ctx.raw, roots[i]))
      roots[i] = keep[^1].raw
  var seen: HashSet[int]
  var stack = roots
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    let part = glUnwritten.getOrDefault(id, "")
    if part.len > 0: return part
    case Z3_get_ast_kind(ctx.raw, t)
    of Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, t)
      for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
        stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
    of Z3_QUANTIFIER_AST:
      stack.add Z3_get_quantifier_body(ctx.raw, t)
    else: discard
  ""

proc unwrittenReadMsg*(part: string): string =
  ## The decline of a read that observes the unwritten part `part` (a
  ## global, or a part of one, before any write in the walk).
  "module-level global '" & part & "' is read but not modelled by the " &
    "symbolic walker -- remove it from the reachable computation or pass " &
    "it as an explicit parameter (feGlobalReadUnmodelled)"

proc unwrittenKind*(part: string): SymexErrorKind =
  ## RFC-0005 batch 6. What observing the unwritten part `part` costs the
  ## path: `feGlobalHavoc` when its global's entry value is modelled
  ## (S8as: any value of its type, so a SAT is replayed and an UNSAT
  ## stands), else a decline (S8bw).
  if glPartHavoc.getOrDefault(part, false): feGlobalHavoc
  else: feGlobalReadUnmodelled

func unwrittenUb*(part: string): set[UbKind] =
  ## RFC-0016 W1-d3. What reading the unwritten part `part` is undefined
  ## through: a `{.noinit.}` local holds an indeterminate value (the walk
  ## models it as any value of its type and replays the hit); a module-level
  ## global does not (it is zero-initialised).
  if part.startsWith(noinitReadPrefix): {readUb()} else: {}

const variantBytesPart* = noinitReadPrefix & "<variant bytes>"

const noinitResultPart* = noinitReadPrefix & "result"
  ## RFC-0016 0.10.0 review H5. The part a `{.noinit.}` routine's `result`
  ## starts as (`dsl_parser.noinitResultPrologue`).


proc unwrittenMsg*(part: string): string =
  ## RFC-0005 batch 6. `unwrittenKind`'s message.
  if part == variantBytesPart:
    "a variant's union bytes no write reached are read through a field " &
      "view: the object was built without zeroing, so they hold whatever " &
      "the stack held and a hit through them is replayed (feGlobalHavoc)"
  elif part.startsWith(noinitReadPrefix):
    "`{.noinit.}` variable '" & part[noinitReadPrefix.len .. ^1] & "' is " &
      "read before it is written: it may hold any value of its type, so a " &
      "hit through it is replayed (feGlobalHavoc)"
  elif glPartHavoc.getOrDefault(part, false):
    "module-level variable '" & part & "' is read before the walk writes " &
      "it: it may hold any value of its type when the property runs, so a " &
      "hit through it is replayed (feGlobalHavoc)"
  else: unwrittenReadMsg(part)

proc imgReadDef*(img: seq[Z3BitVec[64]]; off, size: int): Z3BitVec[64] =
  ## RFC-0016 PRC-07 slice B: the `size` bytes at union byte `off`, where a
  ## byte no write reached is indeterminate: `ite(mask == 0, data, U)` with
  ## `U` a fresh unwritten leaf, so a read that can observe one taints the
  ## path (`unwrittenIn`). The data itself when the mask folds to zero.
  let data = imgRead(img, off, size)
  let mask = imgReadMask(img, off, size)
  let ctx = requireCurrentContext()
  let folded = ctx.checkErr Z3_simplify(ctx.raw, mask.raw)
  if Z3_is_numeral_ast(ctx.raw, folded):
    var u: uint64
    if Z3_get_numeral_uint64(ctx.raw, folded, addr u) and u == 0: return data
  glUnwrittenFresh(ctx)
  let fresh = mkBitVecVar[64](freshDegradeName("__variantBytes"))
  registerUnwritten(ctx, SymVal(kind: svBV64, bv64: fresh, signed: false),
                    variantBytesPart, havoc = true)
  ite(mask == mkBitVec[64](0'i64), data, fresh)

proc globalChainRoot*(e: IRExpr): IRExpr =
  ## The `iekVar` an access chain (`g.a.b`, `g.arr[i]`) is rooted at, or nil.
  var cur = e
  while cur != nil:
    case cur.kind
    of iekVar: return cur
    of iekField: cur = cur.obj
    of iekIndex: cur = cur.arr
    else: return nil
  nil

proc globalReadPart*(e: IRExpr; v: SymVal; simplified = false): string =
  ## The unwritten part `v`, the value of the outermost access `e` of a
  ## chain over a global (not a rebuild's copy), mentions, or "".
  if glUnwritten.len == 0: return ""
  let root = globalChainRoot(e)
  if root == nil or root.vCopy or
     not (isGlobalEnvName(root.vname) or root.vname in glWatched):
    return ""
  unwrittenIn(v, simplified)

proc observeGlobalRead*(e: IRExpr; v: SymVal; simplified = false) =
  ## `lower`'s observation: decline in-band when the read `e` of a global
  ## mentions an unwritten part.
  let part = globalReadPart(e, v, simplified)
  if part.len > 0:
    queueDegrade(unwrittenKind(part), unwrittenMsg(part), unwrittenUb(part))

var callGuardedNames* {.threadvar.}: seq[string]
  ## RFC-0005 S8an. The globals and captures that an ACTIVE walked call
  ## withholds from its callee because they are also the root of one of its
  ## `var`/`addr` actuals (`isCall`). A read of one inside the callee (or
  ## anything it calls) is not bound, and `lower`'s `iekVar` arm declines it
  ## as aliasing instead of as an unmodelled global. Pushed and popped
  ## around each callee walk.

# ---- Phase 15 C4: literal lowering (seq, tuple and variant constructors) --

proc lowerSeqLit*(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C4. `@[a, b, c]` → a CONCRETE-length svSeq: a fresh data array
  ## with each lowered element stored at its index, and `seqLen` pinned to the
  ## literal count (a numeral). Empty `@[]` → length-0 svSeq.
  ##
  ## Round-6 B6 rider (AMENDED by N29, walker v120 — see `dataRaw`'s own
  ## comment below for the full writeup): the EMPTY literal
  ## (`e.seqLitElems.len == 0`) skips `allocateSeqDataRaw` and uses an inert
  ## Bool-sorted placeholder array ONLY when `elemTy` is genuinely UNBACKED
  ## (a kind `allocateSeqDataRaw` does not support at all, e.g. `itTuple` —
  ## the `seq[(string,string)]` gap the rider was written to unblock:
  ## `var pairs: seq[(string,string)] = @[]`, chapulin's own `readOptions`
  ## accumulator declaration). For a BACKED `elemTy` (the common case, e.g.
  ## `seq[int]`), the empty literal now allocates a REAL, correctly-sorted
  ## empty backing array instead — the placeholder's original soundness
  ## argument ("a length-0 seq's data is never read on any live path")
  ## holds for READS but not for a later `.add`/`.insert` MUTATION, which
  ## reinterprets `seqDataRaw` at the DECLARED element sort with no
  ## validation (N29's actual mechanism). This does NOT touch
  ## `allocateSym`'s itSeq arm (fresh/symbolic-length seqs, where a
  ## genuinely-reachable index needs REAL element content) — declining
  ## classified there is unchanged; only the ALREADY-KNOWN-EMPTY literal
  ## case is affected, and only its BACKED-elemTy half changed behaviour.
  let elemTy = seqCellTy(e.seqLitElemTy)   # RFC-0005 S8ba: a distinct elem's base
  if e.seqLitElems.len > 0 and not isBackedSeqElemTy(elemTy):
    # Round-6 N37: a NON-EMPTY literal (the B6 rider above only widened the
    # EMPTY case) whose element type `allocateSeqDataRaw` cannot back --
    # e.g. `@[("a","b")]` : seq[(string,string)]` -- was a THIRD unguarded
    # caller of the same raw-raise site N36 marked `known-open` (alongside
    # `lowerHofCall`'s inline map/filter, converted just above). Guard
    # BEFORE touching `dataRaw`/the element loop at all, mirroring the
    # empty-literal rider's own reasoning and `allocateSym`'s itSeq
    # placeholder discipline -- never call the unsafe function, never
    # attempt to `storeSeqElem` real (unbacked-typed) content into a
    # placeholder array.
    queueDegrade(seNestedSeqUnsupported,
      "seq[seq[T]] / seq[complex] not modeled — element kind " &
           plainEnglishTypeKind(elemTy.kind) &
           " (nested seq element type is not supported)")
    var fresh: seq[Z3Bool]
    return allocateSym(tSeq(elemTy), freshDegradeName("__seqLitUnsupportedDegrade"), fresh)
  # N29 fix (round-6 bucket-2, walker v120): the B6 rider's empty-literal
  # placeholder below is sound ONLY for a seq whose element type
  # `allocateSeqDataRaw` cannot back (its own doc argument: a length-0 seq's
  # data is never READ on any live path, since `isIndex`'s bound is
  # unsatisfiable for every index). That argument does not extend to
  # MUTATION: `.add`/`.insert` (`iekSeqAdd` et al.) unconditionally `wrap()`
  # `seqDataRaw` as `Z3Array[Z3Int, <elemTy's own backed sort>]` with no
  # sort check, so `var xs: seq[int] = @[]; xs.add(a)` -- the ordinary
  # build-a-seq-by-appending idiom, exercised by this file's own C4-1/C4-1b
  # SUTs -- reinterpreted the rider's inert `Array[Int, Bool]` placeholder
  # as `Array[Int, BitVec 64]` and Z3 (correctly) rejected the resulting
  # `store()` with "domain sort ... and parameter sort ... do not match".
  # This was the actual mechanism behind the long-ledgered "N29 HOF lambda
  # domain-sort mismatch" finding: the crash fires on the FIRST post-`@[]`
  # mutation, before `buildClosure`/`lowerHofCall` are ever reached --
  # confirmed by direct stack instrumentation (reverted before landing; the
  # closure/HOF machinery was never entered in any repro). The fix: for a
  # BACKED element type (the overwhelming common case), allocate the REAL
  # typed empty array instead of the generic Bool placeholder -- costs
  # nothing extra (`allocateSeqDataRaw` only ever declares a fresh Z3 array
  # CONSTANT; it never touches element count, exactly like the non-empty
  # branch below), and every subsequent mutation site's unchecked `wrap()`
  # is now sound because the underlying sort genuinely matches. The
  # placeholder survives UNCHANGED for a genuinely UNBACKED element type
  # (e.g. `seq[(string,string)]`), preserving the rider's original purpose
  # (`allocateSeqDataRaw` would raise for those) -- `.add` on such a seq
  # already declines classified via `iekSeqAdd`'s own unbacked-elem `else`
  # arm rather than reaching the unchecked-wrap fast path, so this widening
  # introduces no new unsoundness there.
  # RFC-0005 S8bc: one array per leaf of a tree element.
  var arrs =
    if e.seqLitElems.len == 0:
      if isBackedSeqElemTy(elemTy):
        allocateSeqArrs(elemTy, "__seqlit.data")
      else:
        @[toAnyAst(mkArrayVar[Z3Int, Z3Bool]("__seqlit.emptyPlaceholder"))]
    else:
      allocateSeqArrs(elemTy, "__seqlit.data")
  # RFC-0005 S8s. Each element lowers against the element type's prototype,
  # as `lowerTupleLit`'s fields do: an int literal with no prototype lowers
  # to a signed 64-bit value, and `storeSeqElem` then read the `bv8` of that
  # `svBV64` element of a `seq[uint8]` (`@[x, 1'u8]`, a
  # `weInternalWalkerFault` on every such literal, with or without an input).
  let elemProto =
    if elemTy.kind == itInt: some(bvConst(elemTy, 0))
    elif elemTy.kind == itBool: some(ofBool(mkBool(false)))
    else: none(SymVal)
  for i, ce in e.seqLitElems:
    let elemSV = lower(env, ce, elemProto)
    let cur = mkSeqSV(mkInt(i), arrs, elemTy)
    let stored = seqStoreArrs(cur, mkInt(i), elemSV)
    if stored.isNone: return seqStoreDecline("seq literal", elemTy, elemSV)
    arrs = stored.get
  mkSeqSV(mkInt(e.seqLitElems.len), arrs, elemTy)

proc seqNewZeroArrs*(elemTy: IRType): seq[Z3AnyAst] =
  ## RFC-0005 batch 6. The data arrays of a zeroed `newSeq` of `elemTy`:
  ## one constant array per leaf of the element's zero (S8bc's leaf split),
  ## so the element at any index reads the zero. `lowerSeqNew` builds a
  ## `newSeq` from them and S8bl's `setLen` (`isSetLen`) reads a grown
  ## slot from them: one notion of a fresh element. The caller has checked
  ## `isBackedSeqElemTy` and `defaultZeroTotal`.
  constSeqArrs(elemTy, defaultZero(elemTy, "__newSeqZero"))

proc lowerSeqNew*(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8bc (item 5) and S8bi, one lowering since batch 5.
  ## `newSeq[T](n)` / `newSeq(s, n)` (`snZeroed`): a seq of length `n` whose
  ## every element is `T`'s zero -- each data array is the constant array
  ## of that zero's leaf (`constSeqArrs`, S8bc's leaf split), as an empty
  ## table's container values are (`tabTreeDataZero`), so the element at
  ## any index below `n` reads the zero. `newSeqOfCap[T](n)` (`snOfCap`):
  ## length 0, `n` only reserves. `newSeqUninit[T](n)`: length `n`, elements
  ## Nim leaves unset -- free arrays (`allocateSeqArrs`), and the path is
  ## tainted (`feUnsupportedOpHavoc`): a witness may depend on an element a
  ## run does not reproduce, and whether one is read is not tracked.
  ##
  ## The parser has already forked a negative `n` (`RangeDefect`, the
  ## `Natural` conversion) and declined one above `maxModelledInitialSize`
  ## (`parseNewSeqLen`), so neither is checked again here. An element type
  ## the seq does not back declines as a seq literal of it does, and so
  ## does a zeroed one with no modelled zero.
  let elemTy = e.snElemTy
  let lenSV = lower(env, e.snArg)
  let op = if e.snOfCap: "newSeqOfCap" elif e.snZeroed: "newSeq"
           else: "newSeqUninit"
  let needZero = e.snZeroed and not e.snOfCap
  if not isBackedSeqElemTy(elemTy) or
     (needZero and not defaultZeroTotal(elemTy)) or
     lenSV.kind notin {svInt, svBV8, svBV16, svBV32, svBV64}:
    queueDegrade(seNestedSeqUnsupported,
      op & " of a " & plainEnglishTypeKind(elemTy.kind) &
        " element (or a non-integer length) not modelled")
    var fresh: seq[Z3Bool]
    return allocateSym(tSeq(elemTy), freshDegradeName("__newSeqDegrade"), fresh)
  if e.snOfCap:
    # Length 0: no element is ever read below the length, so the arrays
    # are any arrays of the element's leaf sorts.
    return mkSeqSV(mkInt(0), allocateSeqArrs(elemTy,
                     freshDegradeName("__newSeqOfCap.data")), elemTy)
  if not e.snZeroed:
    let arrs = allocateSeqArrs(elemTy, freshDegradeName("__newSeqUninit.data"))
    if arrs.len == 1:
      # RFC-0005 S8bq: registered as a `newSeqUninit` base, so only a READ
      # of an element no write has reached is tainted (`uninitReadCond`).
      noteUninitSeqBase(arrs[0])
    else:
      # Batch 6: S8bq tracks one data array (`seqDataRaw`). A tree element
      # (S8bc's leaf split) has one array per leaf, and a write of one
      # leaf would read as a write of the element, so the whole path stays
      # tainted, as before S8bq.
      queueDegrade(feUnsupportedOpHavoc,
        "newSeqUninit element values are unspecified — degraded to sxUnknown")
    return mkSeqSV(toZ3Int(lenSV), arrs, elemTy)
  mkSeqSV(toZ3Int(lenSV), seqNewZeroArrs(elemTy), elemTy)

proc lowerTupleLit*(env: Env, e: IRExpr): SymVal =
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

proc variantLitArms*(env: Env, arms: seq[VariantArm], tagOrd: int,
                     activeExprs: seq[IRExpr], objName: string):
    tuple[fields: OrderedTable[int, seq[SymVal]],
          names: OrderedTable[int, seq[string]]] =
  ## The per-arm fields of a literal-discriminant variant (one axis of a
  ## multi-variant): the active arm's are the lowered constructor exprs,
  ## every other arm's are fresh (see `lowerVariantLit`'s soundness note).
  ## Extracted from `lowerVariantLit` by RFC-0005 S8p, which reuses it per
  ## axis in `lowerMultiVariantLit`.
  ## RFC-0005 S8u: `tagOrd` is the discriminator's value. When no explicit
  ## arm names it, the active arm is the `else` arm (key -1), which the
  ## parser only admits for an ordinal that arm covers.
  var activeKey = -1
  for arm in arms:
    if not arm.isElse and arm.tagOrdinal == tagOrd: activeKey = tagOrd
  var armFields = initOrderedTable[int, seq[SymVal]]()
  var armNames  = initOrderedTable[int, seq[string]]()
  for arm in arms:
    armNames[arm.tagOrdinal] = arm.fieldNames
    if arm.tagOrdinal == activeKey:
      var fields: seq[SymVal]
      for fe in activeExprs:
        fields.add lower(env, fe)
      armFields[arm.tagOrdinal] = fields
    else:
      var fields: seq[SymVal]
      for j, ft in arm.fieldTypes:
        inc variantLitFreshCounter
        let path = "__variantLit." & objName & ".@" & arm.tagName &
                   "." & arm.fieldNames[j] & "." & $variantLitFreshCounter
        # N39 (round-6 fix round 5). GUARD-BEFORE-CALL: `classifyFieldType`
        # (dsl_typebridge.nim) legitimately classifies an INACTIVE arm's
        # field as an `itUninterp` `__ownership:`/`__unsupported:`/
        # `__unsupported_witness:` placeholder or an unsupported
        # `itTable`/`itSet` shape (`scopedDeclineFieldTy`'s Bug #2 scoped
        # decline only special-cases `itSeq`) — allocating one raw-raises a
        # classified `Symex*Error` from INSIDE `lower()` (no `WalkCtx`/
        # `Path` in scope here, called via `lowerInExpr` while a loop's live
        # `seq[Path]` may be on the caller's stack), the exact C-backend
        # goto-exception hazard ADR-0023/SND-3 exists to ban. Degrade
        # IN-BAND via the SAME `loweringDegradeErrors`/`loweringDidDegrade`
        # sink ADR-0023 established for exactly this "lower()-reachable,
        # no Path in scope" shape, instead of calling `allocateSym` at all.
        # The substitute value is a bare fresh unconstrained `svBool` —
        # deliberately NOT an attempt to reconstruct `ft`'s own kind: this
        # doc comment's own soundness note (above) already establishes an
        # INACTIVE arm's field is reachable ONLY through `isVariantField`'s
        # out-of-arm `FieldDefect` fork, so no live SAT path ever reads this
        # value regardless of its kind (mirrors `tyOf`'s own "diagnostics
        # only" tolerance for a `SymVal.kind` that doesn't match the
        # original declared field type). `drainPendingLowerEffects` taints
        # the whole STATEMENT once `loweringDidDegrade` is observed — an
        # honest over-approximation (a variant literal with SOME unsupported
        # inactive-arm field type always degrades, even on paths that never
        # touch that field), the safe direction per Invariant 3.
        let ftIssue = unallocatableFieldIssue(ft)
        if ftIssue.isSome:
          queueDegrade(ftIssue.get.kind,
            "variant literal inactive-arm field `" & objName &
                 "." & arm.fieldNames[j] & "` allocation unmodeled — " &
                 ftIssue.get.msg & " (arm-field allocation, not param-entry)")
          fields.add SymVal(kind: svBool, bo: mkBoolVar(path & ".unalloc"))
        else:
          var scratchPC: seq[Z3Bool]
          fields.add allocateSym(ft, path, scratchPC)
      armFields[arm.tagOrdinal] = fields
  (armFields, armNames)

proc lowerVariantLit*(env: Env, e: IRExpr): SymVal =
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
  discBoxed[] = discConst(ty.vDiscTy, int64(e.vlTagOrd))
  var plainFields: seq[SymVal]
  for fe in e.vlPlainFields:
    plainFields.add lower(env, fe)
  let (armFields, armNames) = variantLitArms(env, ty.vArms, e.vlTagOrd,
                                             e.vlArmFields, ty.vObjectName)
  var sv = SymVal(kind: svVariant, vDisc: discBoxed, vDiscName: ty.vDiscName,
                  vObjectName: ty.vObjectName, vArmFields: armFields,
                  vArmFieldNames: armNames, vPlainFields: plainFields,
                  vPlainFieldNames: ty.vPlainFieldNames)
  # RFC-0016 PRC-07 slice B: the union's bytes are the arm's fields over what
  # the constructor started from: zero when it omits a field (Nim zeroes the
  # object first), else nothing (the bytes are indeterminate until written).
  let gate = unionImageGate(ty)
  if gate.isSome and armFields.hasKey(e.vlTagOrd):
    sv.vImage = armImage(gate.get, e.vlTagOrd, armFields[e.vlTagOrd],
                         (if e.vlZeroFilled: zeroImage(gate.get)
                          else: unwrittenImage(gate.get))).get(@[])
  if activeMemberTracked(ty): sv.vActive = activeOf(discBoxed[])
  sv


proc lowerMultiVariantLit*(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8p. `T(k: tagLit, ..., j: tagLit2, ...)` over an
  ## `itMultiVariant` -> svMultiVariant: `lowerVariantLit` once per axis
  ## (the discriminator a const pinned to its literal tag, the active arm's
  ## fields the lowered constructor exprs, the other arms' fields fresh),
  ## plus the shared plain fields.
  let ty = e.mvlTy
  var plainFields: seq[SymVal]
  for fe in e.mvlPlainFields:
    plainFields.add lower(env, fe)
  var axes: seq[VariantAxisSym]
  for ai, ax in ty.mvAxes:
    let discBoxed = new(SymVal)
    discBoxed[] = discConst(ax.discTy, int64(e.mvlAxisTags[ai]))
    let (armFields, armNames) = variantLitArms(env, ax.arms, e.mvlAxisTags[ai],
                                               e.mvlAxisFields[ai],
                                               ty.mvObjectName & "." & ax.discName)
    axes.add VariantAxisSym(discName: ax.discName, disc: discBoxed,
                            armFields: armFields, armFieldNames: armNames)
  SymVal(kind: svMultiVariant, mvObjectName: ty.mvObjectName, mvAxes: axes,
         mvPlainFields: plainFields, mvPlainFieldNames: ty.mvPlainFieldNames)

proc lowerVariantFieldSet*(env: Env, e: IRExpr): SymVal =
  ## RFC-0005 S8s. `v.f = x` on a value variant or multi-variant: `v`'s new
  ## value is its old one with field `f` replaced by `x`. A plain field has
  ## one slot. An arm field has a slot in every arm that declares it
  ## (`of a, b: f` is two arms), and all of them are replaced: the parser's
  ## preceding `isVariantField` read of `v.f` has already forked the
  ## out-of-arm `FieldDefect` (Nim checks the field before it writes, and
  ## leaves `v` unchanged when it raises), so on this path the
  ## discriminator selects one of those arms. The other arms' slots are
  ## unreachable while it does. The new value lowers against the old one's
  ## prototype, so a literal takes the field's width.
  let recv = lower(env, e.vfsRecv)
  proc replaced(old: SymVal): SymVal =
    let proto =
      if old.kind in {svBool, svInt, svBV8, svBV16, svBV32, svBV64}: some(old)
      else: none(SymVal)
    lower(env, e.vfsVal, proto)
  case recv.kind
  of svVariant:
    result = recv
    let pix = recv.vPlainFieldNames.find(e.vfsFieldName)
    if pix >= 0:
      result.vPlainFields[pix] = replaced(recv.vPlainFields[pix])
      return
    var newVal: Option[SymVal]
    for tag in e.vfsTags:
      if not recv.vArmFieldNames.hasKey(tag): continue
      let ix = recv.vArmFieldNames[tag].find(e.vfsFieldName)
      if ix < 0: continue
      if newVal.isNone: newVal = some(replaced(recv.vArmFields[tag][ix]))
      result.vArmFields[tag][ix] = newVal.get
    if newVal.isSome:
      if e.vfsVariantTy != nil:
        # RFC-0016 PRC-07 slice B (c): the write is into the union's bytes;
        # every field of the active arm those bytes cover takes its value
        # from the image (an arm the write leaves without a value in some
        # field was declined upstream, `isVariantField`'s write side).
        if result.vImage.len > 0:
          let lay = vl.variantLayout(e.vfsVariantTy)
          let tp = vl.accessPlace(lay, e.vfsTags, e.vfsFieldName)
          let bits = if lay.ok and tp.isSome: placeBits(newVal.get, tp.get)
                     else: none(Z3BitVec[64])
          if bits.isNone:
            result.vImage = @[]   # no image: a later out-of-arm read declines
          else:
            result.vImage = imgWrite(result.vImage, tp.get.off - lay.unionOff,
                                     tp.get.size, bits.get)
            for tag, slots in recv.vArmFields:
              if tag < 0 or tag in e.vfsTags or not lay.arms.hasKey(tag) or
                 slots.len != lay.arms[tag].len:
                continue
              let isActive = variantDiscEq(recv.vDisc[], int64(tag))
              for j, f in lay.arms[tag]:
                if not overlaps(f, tp.get): continue
                let nv = bitsPlace(imgReadDef(result.vImage,
                                              f.off - lay.unionOff, f.size),
                                   f, some((tp.get, newVal.get)))
                if nv.isNone: continue
                result.vArmFields[tag][j] =
                  iteSV(isActive, nv.get, normSlot(slots[j], f.ty))
        # slice B (cpp): the member written is now the active one.
        if result.vActive != nil and e.vfsTags.len > 0:
          var act = discConst(e.vfsVariantTy.vDiscTy, int64(e.vfsTags[0]))
          for k in 1 ..< e.vfsTags.len:
            let t = int64(e.vfsTags[k])
            act = iteSV(variantDiscEq(recv.vDisc[], t),
                        discConst(e.vfsVariantTy.vDiscTy, t), act)
          result.vActive = activeOf(act)
      return
  of svMultiVariant:
    result = recv
    let pix = recv.mvPlainFieldNames.find(e.vfsFieldName)
    if pix >= 0:
      result.mvPlainFields[pix] = replaced(recv.mvPlainFields[pix])
      return
    var newVal: Option[SymVal]
    for ai, ax in recv.mvAxes:
      for tag in e.vfsTags:
        if not ax.armFieldNames.hasKey(tag): continue
        let ix = ax.armFieldNames[tag].find(e.vfsFieldName)
        if ix < 0: continue
        if newVal.isNone: newVal = some(replaced(ax.armFields[tag][ix]))
        result.mvAxes[ai].armFields[tag][ix] = newVal.get
      if newVal.isSome: return
  else:
    discard
  # The receiver is not a variant (its construction already declined and
  # bound a stand-in: `seVariantFieldOnDeclinedCtor`, as `isVariantField`
  # reports it), or no slot holds the field. Taint the path and keep the
  # old value: no verdict on this path is trusted. RFC-0005 review R1-13:
  # the path goes on without the write, a dropped write, so the kind is
  # `feUnsupportedOp` (`dcSubstituted`, which taints the path). It was
  # `seVariantFieldOnDeclinedCtor`, the READ arm's halt kind (`dcOmitted`,
  # no path taint), right only where the path ends.
  queueDegrade(feUnsupportedOp,
    "variant field '" & e.vfsFieldName & "' written on a receiver with no " &
    "such field slot (SymVal kind=" & $recv.kind & "): the write is " &
    "dropped (feUnsupportedOp)")
  recv

# ---- RFC-0005 S8as: a module-level variable's entry value -----------------

proc entryValueOf*(name: string): SymVal =
  ## RFC-0005 S8as. The entry value of the module-level variable `name`
  ## (`programGlobal(name)` is some): what it holds when the property runs.
  ## An immutable `let` initialised by a literal holds that literal, always:
  ## read exactly. Anything else may hold any value of its type by then (a
  ## `var` that other code, or an earlier test, assigned): one fresh value
  ## per run (`globalEntryVals`), shared by every read, so two reads before
  ## any write agree. A hit through it may need a value the property never
  ## meets, so the reading path carries `feGlobalHavoc` (`dcFreshSymbol`):
  ## a SAT is replayed, and an UNSAT holds for every entry value, so it
  ## stands.
  ##
  ## RFC-0005 batch 6 (S8bw on S8as): the taint is the OBSERVATION's, not
  ## the read's. Each leaf of the value is an unwritten part
  ## (`registerUnwritten`); a rebuild's copy (`g.a = v` carries `g.b`) or a
  ## receiver observes nothing, and every read that does observe one
  ## (`observeGlobalRead`, an element read, a pointer's dereference, a
  ## discriminator's reassignment) taints the path `feGlobalHavoc`
  ## (`unwrittenKind`). `g.a = v` then `g.a` is exact, as S8bw made it.
  let g = programGlobal(name).get
  if g.init != nil:
    return lower(initOrderedTable[string, SymVal](), g.init,
                 (if g.ty.kind == itInt: some(bvConst(g.ty, 0))
                  else: none(SymVal)))
  let ctx = requireCurrentContext()
  glUnwrittenFresh(ctx)
  if not globalEntryVals.hasKey(name):
    var facts: seq[Z3Bool]
    globalEntryVals[name] =
      allocateSym(g.ty, "__glEntry_" & displayName(name), facts)
    for f in facts: globalEntryFacts.add f
    block:   # RFC-0016 INT-82: a global's entry value is entry state
      var acc: seq[RawZ3Ast]
      svAsts(globalEntryVals[name], acc)
      notePreExistingTerms(ctx, acc)
    registerUnwritten(ctx, globalEntryVals[name], displayName(name),
                      havoc = true)
  globalEntryVals[name]

proc lowerExpr*(env: Env, e: IRExpr, proto: Option[SymVal]): SymVal =
  ## `lower`'s body: `lower` itself observes a global read's value
  ## (RFC-0005 S8bw).
  if e == nil:
    raise newException(ValueError, "lower: nil expression")  # [raise-audited: category-c: documented defensive invariant (nil-expression entry guard; moderate confidence, no specific unreachability argument beyond the general defensive pattern)]
  case e.kind
  of iekIntLit:
    if proto.isSome and proto.get.kind in {svUninterpRef, svTuple, svArray,
        svString, svSeq, svTable, svSet, svVariant, svMultiVariant, svClosure,
        svRef, svPtr, svBitSet}:
      # RFC-0016 W3-z P6. Nim never types a written integer literal against a
      # composite slot, but the parser's own placeholder for a declined `nil`
      # (`cstring`, `pointer`: `g = (if c: cstring"a" else: nil)`) is the
      # literal 0, and it is lowered against its sibling arm's prototype.
      # `coerceIntLit` raised on it (weInternalWalkerFault); the parse-time
      # decline marker already owns the verdict, so degrade in-band here and
      # hand back the prototype as the inert value of that slot.
      queueDegrade(feUnsupportedExprKind,
        "a placeholder for a declined literal met a " & $proto.get.kind &
        " slot (a `nil` of a type the walk holds no nil for) -- degraded " &
        "to sxUnknown (feUnsupportedExprKind)")
      proto.get
    elif proto.isSome and proto.get.kind != svBool:
      coerceIntLit(proto.get, e.ival)
    else:
      bvConst(tInt(64, true), e.ival)
  of iekFloatLit, iekConvIntToFloat, iekConvFloatToInt, iekMathCall,
     iekConvFloatRange:
    # Stage 7 (CR-7) Cluster F: float literal, int→float, float→int, math
    # arms extracted into `lowerFloatArm` (defined above, before this proc body).
    lowerFloatArm(env, e)
  of iekConvIntWidth:
    # Round-6 B2: WIDENING-only int-family width conversion.
    if e.ciwHasRange:   # RFC-0005 S8i: a range-checked conversion
      lowerConvIntRange(lower(env, e.ciwOperand), e)
    elif e.ciwTgtWidth < e.ciwSrcWidth:   # RFC-0005 S8j: unchecked narrowing
      lowerConvIntTrunc(lower(env, e.ciwOperand), e.ciwTgtWidth, e.ciwTgtSigned)
    else:
      lowerConvIntWidth(lower(env, e.ciwOperand), e.ciwTgtWidth, e.ciwTgtSigned)
  of iekConvIntReinterpret:
    # A1 adjudication (walker v116): same-width signedness reinterpret.
    lowerConvIntReinterpret(lower(env, e.cirOperand), e.cirWidth, e.cirTgtSigned)
  of iekBoolLit:
    ofBool(mkBool(e.bval))
  of iekVar:
    loweringReadNames.add e.vname      ## RFC-0005 S8as
    # RFC-0005 S8cs: THE point where a global's value enters a verdict. A store
    # the walk does not see may reach it, so whatever the walk holds for it may
    # be stale: an entry value, a value the walk wrote, an opaque call's fresh
    # one. A rebuild's copy (`vCopy`) carries the value back and observes nothing.
    if not e.vCopy and not isConcolicFollowWalk():   # int2: the tail walk too
      let anyValue = globalHiddenRoute(routeAnyValue)
      let hidden = if anyValue.len > 0: anyValue
                   elif isGlobalEnvName(e.vname): globalHiddenRoute(e.vname)
                   elif e.vname in glVarGlobal:
                     globalHiddenRoute(glVarGlobal[e.vname])
                   else: ""
      if hidden.len > 0:
        queueDegrade(feGlobalRouteUnproved,
          "variable '" & displayName(e.vname) & "' is read, and a store the " &
          "walk does not see may reach it: " & hidden &
          " (feGlobalRouteUnproved)")
    if pendingEnvWriteIx(e.vname) >= 0:
      # RFC-0005 S8as: a closure call earlier in this same expression wrote
      # the name. Nim reads the variable after every call of the
      # expression has run; the walk reads it here, in operand order, and
      # the two differ when a later call writes it again. Read the latest
      # write and decline.
      queueDegrade(ceCaptureByRefUnmodelled,
        "`" & displayName(e.vname) & "` is read in the same expression as " &
             "a closure call that writes it; the order of that read and " &
             "the write is not modelled (ceCaptureByRefUnmodelled)")
      closureEnvWrites[pendingEnvWriteIx(e.vname)][1]
    elif env.hasKey(e.vname):
      # RFC-0005 S9: a closure read here carries its by-reference captures
      # as they stand now (a no-op for every other value).
      refreshByRefCaptures(env[e.vname], env)
    elif e.vname == "result" and unwrittenResultZero().isSome:
      # RFC-0005 S8n: a callee's `result` read before its first write is
      # the zero value Nim initialised it to (was `feGlobalReadUnmodelled`).
      unwrittenResultZero().get
    elif e.vname.startsWith(noinitReadPrefix):
      noinitValue(e)   ## RFC-0005 S8bz (item 7)
    elif not isConcolicFollowWalk() and e.vname notin callGuardedNames and
         isGlobalEnvName(e.vname) and programGlobal(e.vname).isSome:
      # RFC-0005 S8as: a global read before the walk wrote it holds its
      # ENTRY value -- what it holds when the property runs. An immutable
      # `let` initialised by a literal holds that literal, always: read
      # exactly. Anything else may hold any value of its type by then (a
      # `var` that other code, or an earlier test, assigned): one fresh
      # value per run (`globalEntryVals`), shared by every read, so two
      # reads before any write agree. A hit through it may need a value
      # the property never meets, so the path carries `feGlobalHavoc`
      # (`dcFreshSymbol`): a SAT is replayed, and an UNSAT holds for every
      # entry value, so it stands. Before S8as the read declined
      # (`feGlobalReadUnmodelled`).
      entryValueOf(e.vname)
    elif not isConcolicFollowWalk():
      # Issues #161/#163 handoff: `wmExplore` (the default whole-proc
      # symbolic walker) reaching a name absent from `env` is NEVER a
      # parser/walker gap -- the parser deliberately lets a free/global
      # name through as a bare `iekVar` (every local/param it emits is
      # bound before its first read; see `isInertOpaqueCall`'s doc comment,
      # `dsl_parser.nim`), and the walker does not model module-level
      # globals at all. This used to be a bare `env[e.vname]`, letting
      # Nim's `Table.[]` `KeyError` escape uncaught and get reported by the
      # run-level backstop as `weInternalWalkerFault` -- an internal-bug
      # attribution for an ordinary, everywhere-applicable modeling gap.
      #
      # Degrades IN-BAND instead of raising: this arm sits inside `lower()`'s
      # own recursion, reachable from arbitrarily many nested `walkBlock`
      # frames (any global read inside a loop body or branch), which is
      # EXACTLY the C-backend goto-exception hazard ADR-0023/SND-3 exists to
      # ban -- a raw `raise` reached from inside nested `walkBlock` frames is
      # silently LOST by Nim's C-backend goto-exception unwind (`lower()`
      # returns as if nothing happened, `w.sawUnknown` never set, and the
      # walker's default-to-UNSAT fallback can report a false `sxUnsat` for a
      # concretely reachable target -- N31's original bug, generalized by
      # N36/N40/N46 for every OTHER walk-reachable raw-raise site; see
      # `degradeStrArm`'s own doc comment, above, for the fullest writeup of
      # this exact mechanism). So this follows THAT idiom, not the
      # `SymexClassifiedDegradeError` raise idiom the param-boundary/
      # verified-unreachable/converted-at-chokepoint sites use (none of
      # those unwind through a live `walkBlock` frame the way this arm
      # does): record the classified decline via the same
      # `loweringDegradeErrors`/`loweringDidDegrade` threadvar sink every
      # other `lower()`-internal degrade in this file uses, then hand back a
      # fresh unconstrained symbol of the best-known type (mirrors the
      # `wmFollowConcrete` havoc construction immediately below) so lowering
      # can continue -- `drainPendingLowerEffects` (the mandatory drain at
      # every `lower()` call site inside `walk`) forks the path `uncertain`
      # and sets `w.sawUnknown` regardless of nesting depth once this
      # returns, so the verdict is `sxUnknown` at ANY nesting depth, naming
      # the global so the caller knows what to remove from the reachable
      # computation (or thread through as an explicit parameter) -- the
      # soundness argument #163 slice 4's opaque-call inertness proof rests
      # on needs this to be a genuine classified decline, not an accident of
      # an escaping exception.
      if e.vname in callGuardedNames:
        # RFC-0005 S8an: a callee (or one it calls) reads a global or a
        # capture that is also a `var`/`addr` actual of an enclosing call.
        # The walk passes that location by copy-in/copy-out, so the direct
        # read would see the value from before the call's writes through
        # the parameter: the name is withheld from the callee (`isCall`)
        # and the read declines here.
        queueDegrade(feUnsupportedOp,
          "`" & displayName(e.vname) & "` is reached by a callee both " &
               "through a `var`/`addr` argument and directly; the walk " &
               "passes the argument by copy-in/copy-out, so the direct " &
               "access is not modelled (feUnsupportedOp)")
      elif isGlobalEnvName(e.vname) and e.vGlobalTy != nil:
        # RFC-0005 S8bw (item 2): a global of a known type, read before
        # its first write in the walk, holds its initial value -- one
        # unwritten constant per leaf. `lower` declines an observation of
        # one (a read of `g` or of an unwritten part); a rebuild's copy or
        # a receiver is no observation, so `g.a = v` binds `g` with its
        # other parts unwritten, and a later read of `g.a` decides.
        return globalInitValue(e.vname, e.vGlobalTy)
      elif isGlobalEnvName(e.vname):
        queueDegrade(feGlobalReadUnmodelled, unwrittenReadMsg(displayName(e.vname)))
      elif e.vname.startsWith("__sym_"):
        # RFC-0005 S8ba: a parser temporary (`freshSynth`; no Nim
        # identifier starts with `_`) is bound by the statement the parser
        # emitted before its read, so reaching it unbound is a walker
        # inconsistency (a declining arm that dropped its result), never a
        # global. It was reported as `feGlobalReadUnmodelled` naming the
        # temporary.
        queueDegrade(weInternalWalkerFault,
          "parser temporary '" & e.vname & "' is read but no statement " &
               "bound it (weInternalWalkerFault)")
      else:
        # RFC-0005 S8an: module-level globals are `__gl:`-named; any other
        # unbound name is a variable the walk does not bind where it is
        # read (a `{.global.}` local, or one only an unmodelled path
        # reaches) -- the same decline, not mislabelled a module global.
        queueDegrade(feGlobalReadUnmodelled,
          "'" & e.vname & "' is read where the symbolic walker has not " &
               "bound it (not a parameter or a local of the walked " &
               "routines it reaches) (feGlobalReadUnmodelled)")
      var fresh: seq[Z3Bool]
      # RFC-0005 S8bw (item 1): a global's stand-in is a value of its
      # declared type (`vGlobalTy`). It was `tInt(64)` when no prototype was
      # in scope, whatever the type, and a later array, seq or tuple
      # operation on it faulted (`gArr[2] = k`, `gSeq.map(f)`).
      let ty = if e.vGlobalTy != nil: e.vGlobalTy
               elif proto.isSome: tyOf(proto.get)
               else: tInt(64, true)
      allocateSym(ty, "__globalReadHavoc_" & e.vname, fresh)
    else:
      # RFC-fuzzer-nextgen G3fix safety net (only reached in
      # `wmFollowConcrete` — concolic collection replaying an ALREADY-
      # EXECUTED concrete trace, G1b/G2). `env` has no binding for a
      # free/global/threadvar reference (e.g. nelli's own `coverageMode`,
      # `coverage.nim` — though the PRIMARY fix, `{.symexOpaque.}` on
      # `recordEdge`, keeps the walker from ever reaching that specific
      # one; this is the net for any OTHER such reference reachable from a
      # concolic replay). Degrade to a fresh unconstrained symbolic havoc —
      # same "PARAM refs stay free/havoc" precedent as Cluster H — rather
      # than crash: the value is provably immaterial to constraint
      # collection at THIS point (nothing bound it), and Track E's
      # re-verify gate (ADR-0031 D3) is what keeps any resulting admission
      # sound, not this walker's soundness.
      var fresh: seq[Z3Bool]
      let ty = if proto.isSome: tyOf(proto.get) else: tInt(64, true)
      allocateSym(ty, "__freeRefHavoc_" & e.vname, fresh)
  of iekField:
    # Lower the receiver, then pick the field by index (tuple) or
    # by name (variant — Phase 11).
    # RFC-0005 S8at: a distinct over a tuple / object is read through its
    # base (`(int, bool)(d)[0]`; the conversion is the parser's identity).
    lowerAsReceiver = true   ## RFC-0005 S8bw: the field is the read
    let recv = ejectBase(lower(env, e.obj))
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
        raise newException(ValueError,  # [raise-audited: category-c: documented parser-invariant (own comment: parser should have A-normalised this)]
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
          raise newException(ValueError,  # [raise-audited: category-c: documented parser-invariant (see iekField arm above)]
            "symex Phase 14: arm-specific field `" & e.fieldName &
            "` reached lower(iekField) on svMultiVariant — parser " &
            "should have A-normalised this through isVariantField")
    else:
      # N47 (round-6 raise-class-audit category-d closure): CONVERTED.
      # Reachability was traced (not just asserted): the parser only ever
      # constructs an `iekField` node when the receiver's STATICALLY
      # CLASSIFIED type is itTuple/itVariant/itMultiVariant (`dsl_parser.nim`'s
      # `nnkDotExpr`/`nnkBracketExpr` arms, every `mkField(...)` call site
      # gated on `lhsCls.ty.kind in {itTuple, itVariant, itMultiVariant}`) — a
      # `ref`/`ptr` receiver is routed through the ENTIRELY SEPARATE
      # `mkFieldDeref`/heap-arm IR instead (an early `return` before any
      # `mkField` call is reached, ~dsl_parser.nim:2831-2852), so a receiver
      # whose DECLARED type is itRef/itPtr can never produce an `iekField`
      # node in the first place. What was NOT fully closed: whether the
      # WALK-TIME value at that env slot can still diverge from its declared
      # STATIC kind — the exact "an `iteSV` merge lands a degraded/opaque
      # SymVal kind on a nominally [X]-typed variable" mechanism
      # `tsymex_r6_heap_raise_totality.nim`'s four `refSV.kind`-not-svRef/svPtr
      # sites were converted under (heap-raise totality slice, walker v113),
      # without an independently constructed repro for those four either.
      # Same defense-in-depth call here: identical hazard shape (a raw raise
      # inside `lower()`, walk-reachable, ADR-0023/SND-3), identical fix, and
      # an in-band degrade is never worse than the raw raise it replaces even
      # if this arm turns out to be truly dead. The field's declared type is
      # not available on this `IRExpr` (only `fieldIx`/`fieldName`, no
      # `fieldTy` — the parser resolves the type from the RECEIVER's static
      # classification, not stored on the node), so — mirroring
      # `lowerClosureCall`'s own `ceClosureUnknownCallee` fallback just above
      # (a plain `int64` placeholder when the correct result type cannot be
      # recovered at the failure site) — the placeholder is a generic int64;
      # its CONTENT is never trustworthy, only well-formed enough that a
      # downstream `Z3_get_sort`/consumer does not crash (the taint below
      # already forces sxUnknown regardless of what this settles to).
      degradeAlloc(tInt(64, true), feUnsupportedExprKind,
        "iekField on unsupported SymVal kind " & plainEnglishSymValKind(recv.kind) &
        " (expected tuple/variant/multi-variant) — degraded to sxUnknown " &
        "(feUnsupportedExprKind)", "__iekFieldUnsupportedDegrade")
  of iekSeqLen:
    # RFC-0005 S8at: a distinct over a container's `len` is its base's.
    let recv = ejectBase(lower(env, e.lenObj))
    case recv.kind
    of svSeq:
      if recv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
        # R1 (walker v89) S1 fix: `recv.seqLen` is the placeholder's
        # HARD-FORCED-`== 0` decoy symbol (`allocateSym`'s `itSeq` arm) —
        # returning it directly (the pre-v89 behavior) let a
        # `p.options.len > 0`-style query get silently PROVEN against the
        # fake length (a false `sxUnsat`). Decline through the chokepoint
        # instead; never trust `seqLen` for a flagged receiver.
        declinePlaceholderInLower(recv, e.lenLoc, "length read (.len)")
        var fresh: seq[Z3Bool]
        allocateSym(tInt(64, true), "__seqLenPlaceholderDecline", fresh)
      else:
        SymVal(kind: svInt, zi: recv.seqLen) # [placeholder-audited]
    of svTable: SymVal(kind: svInt, zi: recv.tabSize)
    of svSet:   SymVal(kind: svInt, zi: recv.setSize)
    of svString:
      # Round-6 B1 (ADR-0028 Leg 1) totality backstop: a string-backed
      # `seq[byte]` param's `.len` reaching here with an `svString`
      # receiver — SND-4 mirror of `iekStrLen`'s lowering
      # (`runtime_strings.nim`), same byte-faithful `str.len` read. Makes
      # `data.len` WORK (not merely decline) even through a call-chain hop
      # whose OWN parse never routed the dispatch through `iekStrLen`.
      SymVal(kind: svInt, zi: strLenOf(recv.str))   # RFC-0016 INT-57
    else:
      # Round-6 B1 backstop: was a bare `ValueError` (a live crash gap) —
      # a mis-classified receiver now declines classified instead of
      # crashing (SND-4 mirror: the existing generic
      # `SymexClassifiedDegradeError` carrier, CR-1c/CR-2b precedent).
      #
      # Round-6 N37 (walker v102) adjudication -- UPGRADED from N36's
      # `known-open` to VERIFIED UNREACHABLE. Gate: the parser only ever
      # constructs an `iekSeqLen` node when `classifyType` resolves the
      # receiver to `itSeq`/`itTable`/`itSet` (`dsl_parser.nim`'s
      # `nnkDotExpr` `.len` arm restricts to `itSeq`; the call-form
      # `len`/`card` arm restricts to `{itSeq, itTable, itSet}` — every
      # OTHER classified type either has no `.len` field-access arm at all
      # (parse-time `feUnsupportedExprKind` decline, this same file's
      # `else` catch-all a few hundred lines up in `dsl_parser.nim`) or, for
      # a demoted/witness-unrenderable Table, is reclassified `itUninterp`
      # BEFORE this dispatch ever runs). At WALK time, every allocation/
      # binding path for an `itSeq`/`itTable`/`itSet`-classified value
      # produces the MATCHING `svSeq`/`svTable`/`svSet` kind, with exactly
      # ONE documented cross-representation exception: a string-backed
      # `seq[byte]` receiver arrives as `svString` (the arm immediately
      # above), reachable via the SAME call-boundary no-representation-
      # bridge gap this slice converted for `iekSeqSlice`. EMPIRICALLY
      # PROBED this slice: the identical call-boundary construction
      # (a Q1-scan caller passing its string-backed `data` into a
      # `.len`-reading helper with no consuming loop of its own) resolves
      # cleanly through the `svString` arm above (a correct answer, not
      # even a decline) — it is the ONLY reachable kind mismatch, and it is
      # already handled. `svTable`/`svSet` have no analogous alternate
      # representation anywhere in this engine (always allocated uniformly),
      # so no comparable mismatch exists for them either. No construction
      # from valid DSL surface was found that reaches THIS arm; the
      # mechanism argument (identical mismatch surface to `iekSeqSlice`,
      # exhaustively probed) is relied on per the class description's own
      # allowance. Kept as a defensive backstop, not converted.
      let locPrefix = if e.lenLoc.len > 0: e.lenLoc & ": " else: ""
      raise (ref SymexClassifiedDegradeError)(  # [raise-audited: verified-unreachable -- parser only emits iekSeqLen for itSeq/itTable/itSet receivers; the one cross-representation mismatch (string-backed seq[byte]) already lands on the svString arm above (N37)]
        kind: feUnsupportedExprKind,
        msg: locPrefix & "iekSeqLen: unsupported receiver kind " &
             plainEnglishSymValKind(recv.kind) & " (expected seq/table/set/string) — degraded " &
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
      # Round-6 N37: was a raw `raise (ref SymexClassifiedDegradeError)` --
      # reached from inside nested `walkBlock` frames via a call-boundary
      # representation mismatch (a callee's own `itSeq`-classified param
      # receiving a caller's svString-backed argument through `isCall`'s
      # no-bridge env binding — the SAME gap `iekSeqLen`'s `svString` arm
      # exists to handle, but `iekSeqSlice` has no matching arm) — the exact
      # C-backend goto-exception hazard N36 closed elsewhere in this file.
      # Empirically CONFIRMED this slice (stash method): a block-wrapped
      # repro (a Q1-scan caller passing its string-backed `data` into a
      # slicing helper with no consuming loop of its own) proved a FALSE
      # `sxUnsat` with ZERO errors pre-fix; the identical shape without the
      # block was already an honest classified `sxUnknown`. In-band
      # lowering-level degrade instead, matching `degradeStrArm`'s idiom.
      queueDegrade(feUnsupportedOp,
        "iekSeqSlice: base lowered to " & plainEnglishSymValKind(recv.kind) &
             " — expected svSeq (→ sxUnknown, Invariant 3)")
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(tInt()), freshDegradeName("__seqSliceBaseKindDegrade"), fresh)
    if recv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # R1 (walker v89) N1 fix: pre-v89 this fell straight through to the OOB
      # arithmetic below using `recv.seqLen` — the placeholder's FORCED-`==0`
      # decoy — so a `ps[0 .. 0]`-style slice's `hi < lenZ` conjunct was
      # TAUTOLOGICALLY violated, forking a guaranteed-spurious `IndexDefect`
      # (false `sxRaised`/pruned continuation) on every path, EVEN THOUGH the
      # base is never truly indexed. WORSE, the returned `SymVal` omitted
      # `isUnsupportedFieldPlaceholder`, so any further consumer of the slice
      # result (another slice, an index, a `.len`) was blind to the taint and
      # could itself compute a false verdict. Decline through the chokepoint
      # BEFORE touching `seqLen`/`seqDataRaw` or depositing any OOB fork, and
      # return `recv` UNCHANGED — a slice of a placeholder is itself exactly
      # as unbacked/untrusted as the base, so propagating the same flagged
      # value is both the simplest and the most honest result (sound
      # over-approximation: every downstream chokepoint that inspects
      # `isUnsupportedFieldPlaceholder` still catches it).
      declinePlaceholderInLower(recv, "", "slice read ([lo..hi])")
      return recv
    # ADR-0027 bound discipline: svInt proto so literals/adaptables arrive
    # Int-sorted; a genuinely BV-allocated bound would bv2int-bridge — the
    # empirical Z3 non-termination shape — and declines classified.
    let intProto = some(SymVal(kind: svInt, zi: mkInt(0)))
    let loSV = lower(env, e.ssLo, intProto)
    let hiSV = lower(env, e.ssHi, intProto)
    # RFC-0005 S8bu: a `toOpenArray` view's bounds are the caller's own
    # `int`s, almost always bit-vectors; they take the signed Int bridge,
    # which S8bu's inverse facts (`bvIntInverseFacts`) let Z3 decide and
    # the query bounds (`queryRLimit`, `queryTimeoutMs`) end either way.
    # A slice's keep ADR-0027's decline.
    let bridged = e.ssView and
      loSV.kind in {svInt, svBV8, svBV16, svBV32, svBV64} and
      hiSV.kind in {svInt, svBV8, svBV16, svBV32, svBV64}
    if not bridged and (loSV.kind != svInt or hiSV.kind != svInt):
      # Round-6 N37: was a raw `raise (ref SymexClassifiedDegradeError)` --
      # reached from inside nested `walkBlock` frames via the SAME two-hop
      # literal-seeded-local trick N36 section 1 demonstrated for
      # `iekStrInOptionRegion` (`collectIntOffsetParams`/
      # `collectIntOffsetLiteralLocals` only trace a formal-param root or a
      # ONE-hop literal seed; a local seeded from ANOTHER local evades both,
      # landing the BV64 type-driven default instead of svInt) — applied
      # here to a SEQ slice bound instead of a string one. Empirically
      # CONFIRMED this slice (stash method): a block-wrapped repro proved a
      # FALSE `sxUnsat` with ZERO errors pre-fix; the identical shape
      # without the block was already an honest classified `sxUnknown`.
      # In-band lowering-level degrade instead, matching `degradeStrArm`'s
      # idiom (and N31's own `iekStrSubstr` CR-17 fix).
      queueDegrade(feUnsupportedOp,
        "iekSeqSlice: slice bound lowered as " & plainEnglishSymValKind(loSV.kind) & "/" &
             plainEnglishSymValKind(hiSV.kind) & " — a bitvector-represented bound would " &
             "bv2int-bridge into the array query (ADR-0027 non-termination " &
             "class; bounds from find/len/literals prove) " &
             "(→ sxUnknown, Invariant 3)")
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(tInt()), freshDegradeName("__seqSliceBoundDegrade"), fresh)
    let lo = if bridged: toZ3Int(loSV) else: loSV.zi
    let hi = if bridged: toZ3Int(hiSV) else: hiSV.zi
    # A real Nim slice raises IndexDefect outside `lo >= 0 ∧ hi < len ∧
    # lo <= hi + 1` (the last conjunct admits the empty slice). Deposit the
    # OOB predicate into the SND-4 sink — `drainStrIndexRaises` routes an
    # IndexDefect fork at the statement boundary; the sink is string-NAMED
    # but its routed defect type is exactly right for container slices too.
    # The view below is only ever OBSERVED on the in-bounds survivor path.
    #
    # RFC-0005 S8g: the defect CLASS is Nim's (probe, `d = @[1, 2, 3]`):
    # system's `[]`(s, HSlice) computes `L = hi - lo + 1` as a `Natural`
    # (`newSeq(L)`), so `L < 0` raises `RangeDefect` (`d[4 .. ^1]`,
    # `d[2 .. 0]`), and then copies `s[i + lo]` for `i in 0 ..< L`, so an
    # out-of-bounds bound raises `IndexDefect` only when `L > 0`; an empty
    # slice (`L == 0`, `d[3 .. ^1]`, `d[5 .. 4]`) never raises. Every one
    # of those was an `IndexDefect` (`not (lo >= 0 and hi < len and
    # lo <= hi + 1)`), including the empty slice past the end.
    #
    # RFC-0005 S8ca: a `toOpenArray` view (`ssView`) is checked otherwise
    # (probed on the pinned toolchain, a 4-element seq): `IndexDefect` iff
    # its length is not 0 and either bound is outside `0 ..< len` -- (2, -1),
    # (4, 1), (1, -2) raise; (2, 0) and (3, 0) do not, and make a view of
    # negative length (-1, -2) that no index reaches (every `a[i]` raises,
    # as the walk's index check does for a negative length) and no loop
    # enters. Nothing raises `RangeDefect`. S8bu declined a negative length.
    let lenZ = recv.seqLen # [placeholder-audited]
    let sliceLen = (hi - lo) + mkInt(1)
    let idxOob =
      if e.ssView:
        (sliceLen != mkInt(0)) and
          ((lo < mkInt(0)) or (lo >= lenZ) or (hi < mkInt(0)) or (hi >= lenZ))
      else: (sliceLen > mkInt(0)) and ((lo < mkInt(0)) or (hi >= lenZ))
    let negLen = sliceLen < mkInt(0)
    when not defined(symexSliceNoOobFork):
      syncStrIndexOobCond(idxOob)
      if not e.ssView:
        syncRangeDefectCond(negLen)
    inc sliceViewCounter
    let zctx = recv.seqDataRaw.ctx # [placeholder-audited]
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
    # RFC-0005 S8bc: one view per data array of a tree element.
    var lams: seq[Z3AnyAst]
    for arr in seqArrs(recv):
      let sel = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, arr.raw, shifted.raw))
      lams.add lambdaOver(zctx, iVar, sel)
    mkSeqSV((hi - lo) + mkInt(1), lams, recv.seqElemTy)
  of iekSeqSplice:
    # RFC-0005 S8bu: `base` with `part` written over it from `at` (a `var
    # openArray` view of a `toOpenArray` slice, written back). The parser
    # builds it only after the slice was taken in bounds, of the length
    # `part` has (an openArray's length never changes): an array-lambda
    # `ite(at <= i < at + part.len, part[i - at], base[i])`.
    let base = lower(env, e.spBase)
    let part = lower(env, e.spPart)
    let atSV = lower(env, e.spAt, some(SymVal(kind: svInt, zi: mkInt(0))))
    if base.kind != svSeq or part.kind != svSeq or
       atSV.kind notin {svInt, svBV8, svBV16, svBV32, svBV64} or
       base.isUnsupportedFieldPlaceholder or # [placeholder-audited]
       part.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      queueDegrade(feUnsupportedOp,
        "iekSeqSplice: the storage, the view or the offset lowered as " &
             plainEnglishSymValKind(base.kind) & "/" &
             plainEnglishSymValKind(part.kind) & "/" &
             plainEnglishSymValKind(atSV.kind) &
             " — expected a seq, a seq and an Int (→ sxUnknown, Invariant 3)")
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(tInt()), freshDegradeName("__seqSpliceDegrade"), fresh)
    let at = toZ3Int(atSV)   # the view's bridge (`ssView`)
    inc sliceViewCounter
    let zctx = base.seqDataRaw.ctx # [placeholder-audited]
    let iVar = mkIntVar("__spliceview_i" & $sliceViewCounter)
    let inPart = (iVar >= at) and (iVar < at + part.seqLen) # [placeholder-audited]
    let shifted = iVar - at
    let bArrs = seqArrs(base)
    let pArrs = seqArrs(part)
    if bArrs.len != pArrs.len:
      queueDegrade(feUnsupportedOp,
        "iekSeqSplice: the storage and the view have different element " &
             "shapes (→ sxUnknown, Invariant 3)")
      var fresh: seq[Z3Bool]
      return allocateSym(tSeq(tInt()), freshDegradeName("__seqSpliceDegrade"), fresh)
    var lams: seq[Z3AnyAst]
    for k in 0 ..< bArrs.len:
      let fromPart = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, pArrs[k].raw, shifted.raw))
      let fromBase = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, bArrs[k].raw, iVar.raw))
      let body = wrap[Z3AnyAst](zctx,
        checkedIte(zctx, inPart.raw, fromPart.raw, fromBase.raw))
      lams.add lambdaOver(zctx, iVar, body)
    mkSeqSV(base.seqLen, lams, base.seqElemTy) # [placeholder-audited]
  of iekSeqConcat:
    # RFC-0016 INT-80: system's `&` over two seqs (an element operand is a
    # one-element literal by now). Nim builds a fresh seq of length
    # `len(a) + len(b)` and copies `a`'s elements, then `b`'s, into it. The
    # model is an array-lambda per data array, `ite(i < len(a), a[i],
    # b[i - len(a)])`, as `iekSeqSplice`'s: each part keeps the sort its
    # array has (INT-78), the lambda captures the operands' arrays as they
    # are here (a later write to either is a new store chain and does not
    # show through, Nim's copy), and a read stays quantifier-free: Z3
    # beta-reduces a select over the lambda to the `ite`.
    let left = lower(env, e.scLeft)
    let right = lower(env, e.scRight)
    if left.kind == svSeq and left.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      declinePlaceholderInLower(left, "", "concatenation (`&`)")
      return left
    if right.kind == svSeq and right.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      declinePlaceholderInLower(right, "", "concatenation (`&`)")
      return right
    if left.kind != svSeq or right.kind != svSeq or
       seqArrs(left).len != seqArrs(right).len:
      # Unreachable for a typed Nim `&` (both operands are `seq[T]`); a
      # value some upstream degrade produced declines in-band.
      let declineMsg = "iekSeqConcat: the operands lowered as " &
        plainEnglishSymValKind(left.kind) & "/" &
        plainEnglishSymValKind(right.kind) &
        " — expected two seqs of one element shape (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg,
          kind = weInternalWalkerFault),
        freshDegradeName("__seqConcatMismatch"), fresh)
    if not isBackedSeqElemTy(left.seqElemTy):
      # A seq of an element the model does not back (`seq[seq[T]]`) that
      # is not a placeholder (an empty literal's): as `iekSeqAdd` declines.
      let declineMsg = "iekSeqConcat: a seq of " & $left.seqElemTy &
        ", an element type the model does not back (seNestedSeqUnsupported)"
      queueDegrade(seNestedSeqUnsupported, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(tUnsupportedFieldSeq(left.seqElemTy, declineMsg),
                         freshDegradeName("__seqConcatUnbacked"), fresh)
    let lenL = left.seqLen # [placeholder-audited]
    inc sliceViewCounter
    let zctx = left.seqDataRaw.ctx # [placeholder-audited]
    let iVar = mkIntVar("__concatview_i" & $sliceViewCounter)
    let inLeft = iVar < lenL
    let shifted = iVar - lenL
    let lArrs = seqArrs(left)
    let rArrs = seqArrs(right)
    var lams: seq[Z3AnyAst]
    for k in 0 ..< lArrs.len:
      let fromLeft = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, lArrs[k].raw, iVar.raw))
      let fromRight = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, rArrs[k].raw, shifted.raw))
      let body = wrap[Z3AnyAst](zctx,
        checkedIte(zctx, inLeft.raw, fromLeft.raw, fromRight.raw))
      lams.add lambdaOver(zctx, iVar, body)
    mkSeqSV(lenL + right.seqLen, lams, left.seqElemTy) # [placeholder-audited]
  of iekStrLit, StrOpKinds:
    # Stage 7 (CR-7) Cluster S: all string literal and string-op arms are
    # extracted into `lowerStrArm` (defined above, before this proc body).
    #
    # Round-6 N36 (walker v101, ADR-0023/SND-3 chokepoint): `lowerStrArm`'s
    # raw `raise`s of the six classified string-family carriers below are
    # the exact C-backend goto-exception hazard N31 fixed for ONE site
    # (`iekStrSubstr`'s CR-17 guard) — a raise reached from inside nested
    # `walkBlock` frames unwinds silently on the `c` backend, losing the
    # classified error and leaving `w.sawUnknown` false, which can produce a
    # false `sxUnsat` on a reachable target. Rather than hand-convert every
    # raw-raise site inside `lowerStrArm` (~18 of them), catch every
    # classified carrier it can raise HERE, at the single call site every
    # one of them must pass through — see `degradeStrArm`'s own doc comment
    # (immediately above `lower`'s definition) for the full soundness
    # argument for why this ONE catch point is sufficient regardless of how
    # deep the CALLER's own `walkBlock` nesting goes.
    try:
      lowerStrArm(env, e)
    except SymexUnsupportedStringOpError as ex:
      degradeStrArm(e, seUnsupportedStringOp, ex.msg)
    except SymexZ3VersionMissingError as ex:
      degradeStrArm(e, seZ3VersionMissing, ex.msg)
    except SymexZ3StringIncompleteError as ex:
      degradeStrArm(e, seZ3StringIncomplete, ex.msg)
    except SymexUnsupportedRegexError as ex:
      degradeStrArm(e, seUnsupportedRegex, ex.msg)
    except Z3FeatureUnavailableError as ex:
      # RFC-0005 S8aq: nim-z3's OWN runtime guard (not one of nelli's
      # classified carriers above) for a Z3-build-optional C constructor
      # whose compile-time gate is on but the loaded Z3 lacks the symbol
      # (`replaceAll`'s `Z3_mk_seq_replace_all`, absent below Z3 4.16, is
      # the only such call this walker reaches -- `iekStrReplaceAll`,
      # `runtime_strings.nim`, under this project's opt-in
      # `-d:z3WithSeqReplaceAll`). Classified the SAME as the compile-time
      # gate being off (`seZ3VersionMissing`, `dcFreshSymbol`): a Z3 build
      # too old for the real op degrades exactly like a build the define
      # never targeted, never an uncaught exception.
      degradeStrArm(e, seZ3VersionMissing, ex.msg)
  of iekGetCurrentExnMsg, iekGetCurrentExn:
    # Stage 7 (CR-7) Cluster E: exception expression arms extracted into
    # `lowerExnArm` (defined above, before this proc body).
    lowerExnArm(env, e)
  of iekSeqAdd:
    let recv = lower(env, e.mutRecv)
    if recv.kind != svSeq:
      # Round-6 R4 (W2b), defense in depth: `dsl_parser.nim` only ever
      # emits `iekSeqAdd` for a receiver classified `itSeq`, so this
      # SHOULD be unreachable once W2a's mutation-veto widening
      # (`scanShapeReceiverMutated`) closes the one confirmed route (a
      # var-aliased helper-call mutation misclassifying the receiver
      # string-backed, so an `svString` arrives here instead) — but that
      # veto is a syntactic heuristic on the CLASSIFIER side, not a
      # machine-checked guarantee that every representation-mismatch route
      # is closed. The raw `doAssert` this replaces native-crashed
      # (AssertionDefect masked to `weInternalWalkerFault`) the instant any
      # such gap was hit — exactly Bug #2's original whole-run-poison
      # failure mode. Mirrors `lowerBool`'s v64 doAssert -> classified-
      # decline idiom (in-band SND-3 taint via the threadvar sink) and
      # reuses Bug #2/B7r2's own `tUnsupportedFieldSeq`/`allocateSym`
      # placeholder machinery for the type-correct inert result, rather
      # than hand-rolling a parallel dummy-construction path.
      # N47-followup (walker v110): `declineMsg` is passed VERBATIM as both
      # the immediate error's `msg` AND the placeholder's `tUnsupportedFieldSeq`
      # reason (below) — a downstream read of the rebound receiver then
      # references this EXACT decline via `placeholderReadDeclineMsg`
      # instead of fabricating an unrelated (and here false) nested-seq
      # claim. See `seqUnsupportedFieldKind`'s doc (types.nim) for the full
      # mechanism.
      let declineMsg = "iekSeqAdd: receiver lowered to " & plainEnglishSymValKind(recv.kind) &
             " — expected svSeq (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg,
          kind = weInternalWalkerFault),
        "__seqAddKindMismatch", fresh)
    if recv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # R1 (walker v89) N6 audit: `.add` on a placeholder parses unconditionally
      # (`dsl_parser.nim`'s `.add` arm dispatches on receiver KIND only, not
      # element backedness) — pre-v89 this fell through to the `case
      # recv.seqElemTy.kind` dispatch below, whose `else` arm `raise`s a bare
      # `ValueError` for any unbacked element kind (e.g. itTuple). Uncaught
      # this deep, that unwound all the way to `runSymexImpl`'s generic
      # catch-all and poisoned the WHOLE run (`weInternalWalkerFault`) —
      # exactly Bug #2's original failure mode. Decline through the
      # chokepoint instead and propagate the flag (mirrors `iekSeqSlice`'s
      # N1 fix: a mutation of untrusted content is itself untrusted).
      declinePlaceholderInLower(recv, "", "mutation (.add)")
      return recv
    # RFC-0005 S8ar: the element is lowered at the element type's width (a
    # literal into a `seq[int8]` is an 8-bit value) and stored through
    # `storeSeqElem`, the store every other seq write uses, which backs
    # every element kind `isBackedSeqElemTy` admits. This arm had its own
    # copy of the store covering only `int` and `bool`: any other element
    # (`string`, `float`, a narrower int, a ref) was "iekSeqAdd: unsupported
    # elem/width" (`weInternalWalkerFault`), and an Int-promoted `int`
    # stored the constant 0 in its place (RFC-0005 S8ba fixed the same arm:
    # `var s: seq[int]; s.add(x); s[0] == 7` with `x: range[0..10]` was a
    # false `sxUnsat`). RFC-0005 S8ba: a distinct element is stored as its
    # base (`seqCellTy`, `ejectBase`).
    let val = lower(env, e.mutArg, intLitProto(recv.seqElemTy))
    let oldLen = recv.seqLen # [placeholder-audited]
    let newLen = oldLen + mkInt(1)
    if not isBackedSeqElemTy(recv.seqElemTy):
      # RFC-0005 S8bl (item 3). A seq of an element the model does not back
      # (`seq[seq[T]]`) that is not a placeholder: a local built from an
      # empty literal (`var p: seq[seq[T]] = @[]`), whose length is exact
      # but whose elements have no arrays to store into. The add declines
      # as such a seq does everywhere else (`seNestedSeqUnsupported`, a
      # placeholder decline); it was the in-band element mismatch below,
      # filed as `weInternalWalkerFault`. The argument is lowered first, so
      # its raises are kept (S5).
      let declineMsg = "iekSeqAdd: an element added to a seq of " &
        $recv.seqElemTy & ", an element type the model does not back " &
        "(seNestedSeqUnsupported)"
      queueDegrade(seNestedSeqUnsupported, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(tUnsupportedFieldSeq(recv.seqElemTy, declineMsg),
                         freshDegradeName("__seqAddUnbacked"), fresh)
    if not seqElemFits(ejectBase(val), seqCellTy(recv.seqElemTy)):
      # Unreachable for a typed Nim `add` (its argument has the element
      # type); a value some upstream degrade produced keeps the in-band
      # decline this arm always had for a representation mismatch.
      let declineMsg = "iekSeqAdd: element lowered to " &
        plainEnglishSymValKind(val.kind) & " for a seq[" &
        plainEnglishTypeKind(recv.seqElemTy.kind) & "] (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg,
          kind = weInternalWalkerFault),
        freshDegradeName("__seqAddElemMismatch"), fresh)
    # RFC-0005 S8bc: every leaf of a tree element (`seqStoreArrs`).
    let stored = seqStoreArrs(recv, oldLen, val)
    if stored.isNone: return seqStoreDecline("iekSeqAdd", recv.seqElemTy, val)
    mkSeqSV(newLen, stored.get, recv.seqElemTy)
  of iekTableSet:
    let recv = lower(env, e.tabRecv)
    if containerRecvDeclined(recv, svTable, "`t[k] = v`"): return recv
    # RFC-0005 S8z: a literal value is shaped at the value type's width.
    # RFC-0005 S8ar: the key and value as the terms the table holds
    # (`tabKeyTerm` / `tabValTerm`), for every backed key and value type
    # (was a string key and a 64-bit cell value, every other value an
    # in-band decline).
    let keySV = lower(env, e.tabKey, seqElemLitProto(recv.tabKeyTy))
    let val = lower(env, e.tabVal, seqElemLitProto(recv.tabValTy))
    let kOpt = tabKeyTerm(keySV, recv.tabKeyTy)
    let vOpt = tabValTerms(val, recv.tabValTy)   ## RFC-0005 S8at: per leaf
    if kOpt.isNone or vOpt.isNone:
      # Unreachable for a typed Nim `[]=`; a value some upstream degrade
      # produced keeps the in-band decline this arm always had.
      queueDegrade(feUnsupportedOp,
        "iekTableSet: key lowered to " & plainEnglishSymValKind(keySV.kind) &
        " and value to " & plainEnglishSymValKind(val.kind) & " — expected a " &
        $recv.tabKeyTy & " key and a " & $recv.tabValTy & " value " &
        "(feUnsupportedOp)")
      return recv
    let ctx = recv.tabSize.ctx
    let k = kOpt.get
    let tru = mkBool(true)
    let wasPresent = wrap[Z3Bool](ctx,
      checkedSelect(ctx, recv.tabPresentRaw.raw, k.raw))
    let vs = vOpt.get
    let newData = wrap[Z3AnyAst](ctx,
      checkedStore(ctx, recv.tabDataRaw.raw, k.raw, vs[0].raw))
    # RFC-0005 S8at: a container value's further leaves, each in its array.
    var newMore: seq[Z3AnyAst]
    for i, m in recv.tabDataMore:
      newMore.add wrap[Z3AnyAst](ctx, checkedStore(ctx, m.raw, k.raw, vs[i + 1].raw))
    let newPresent = wrap[Z3AnyAst](ctx,
      checkedStore(ctx, recv.tabPresentRaw.raw, k.raw, tru.raw))
    # size += 1 if !wasPresent
    let nanOpt = tabKeyNaN(keySV, recv.tabKeyTy)
    if nanOpt.isSome:
      # RFC-0005 S8at: a NaN key adds an entry no lookup finds.
      let nan = nanOpt.get
      var keptMore: seq[Z3AnyAst]
      for i, m in recv.tabDataMore:
        keptMore.add wrap[Z3AnyAst](ctx, checkedIte(ctx, nan.raw, m.raw,
                                                     newMore[i].raw))
      return SymVal(kind: svTable,
        tabDataRaw: wrap[Z3AnyAst](ctx, checkedIte(ctx, nan.raw,
          recv.tabDataRaw.raw, newData.raw)),
        tabDataMore: keptMore,
        tabPresentRaw: wrap[Z3AnyAst](ctx, checkedIte(ctx, nan.raw,
          recv.tabPresentRaw.raw, newPresent.raw)),
        tabSize: ite(nan or not wasPresent, recv.tabSize + mkInt(1),
                     recv.tabSize),
        tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
    SymVal(kind: svTable,
      tabDataRaw: newData,
      tabDataMore: newMore,
      tabPresentRaw: newPresent,
      tabSize: ite(wasPresent, recv.tabSize, recv.tabSize + mkInt(1)),
      tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
  of iekTableDel:
    let recv = lower(env, e.mutRecv)
    if containerRecvDeclined(recv, svTable, "`t.del(k)`"): return recv
    let keySV = lower(env, e.mutArg, seqElemLitProto(recv.tabKeyTy))
    let kOpt = tabKeyTerm(keySV, recv.tabKeyTy)   ## RFC-0005 S8ar
    if kOpt.isNone:
      queueDegrade(feUnsupportedOp,
        "iekTableDel: key lowered to " & plainEnglishSymValKind(keySV.kind) &
        " — expected a " & $recv.tabKeyTy & " (feUnsupportedOp)")
      return recv
    let ctx = recv.tabSize.ctx
    let k = kOpt.get
    let fls = mkBool(false)
    let wasPresent = wrap[Z3Bool](ctx,
      checkedSelect(ctx, recv.tabPresentRaw.raw, k.raw))
    let newPresent = wrap[Z3AnyAst](ctx,
      checkedStore(ctx, recv.tabPresentRaw.raw, k.raw, fls.raw))
    let nanOpt = tabKeyNaN(keySV, recv.tabKeyTy)
    if nanOpt.isSome:
      # RFC-0005 S8at: `t.del(NaN)` finds nothing to remove.
      let nan = nanOpt.get
      return SymVal(kind: svTable,
        tabDataRaw: recv.tabDataRaw,
        tabDataMore: recv.tabDataMore,   ## RFC-0005 S8at
        tabPresentRaw: wrap[Z3AnyAst](ctx, checkedIte(ctx, nan.raw,
          recv.tabPresentRaw.raw, newPresent.raw)),
        tabSize: ite(wasPresent and not nan, recv.tabSize - mkInt(1),
                     recv.tabSize),
        tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
    SymVal(kind: svTable,
      tabDataRaw: recv.tabDataRaw,
      tabDataMore: recv.tabDataMore,   ## RFC-0005 S8at
      tabPresentRaw: newPresent,
      tabSize: ite(wasPresent, recv.tabSize - mkInt(1), recv.tabSize),
      tabKeyTy: recv.tabKeyTy, tabValTy: recv.tabValTy)
  of iekSetIncl:
    let recv = lower(env, e.mutRecv)
    if containerRecvDeclined(recv, svSet, "`s.incl(x)`"): return recv
    # RFC-0005 S8z: the element at its own width, into its 64-bit cell.
    let elemSV = lower(env, e.mutArg, intLitProto(recv.setElemTy))
    let elemOpt = cellOf(elemSV, recv.setElemTy)   ## RFC-0005 S8u
    if elemOpt.isNone:
      queueDegrade(feUnsupportedOp,
        "iekSetIncl: element lowered to " & plainEnglishSymValKind(elemSV.kind) &
        " — expected a " & $recv.setElemTy & " (feUnsupportedOp)")
      return recv
    let elem = elemOpt.get
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    noteSetKey(elem)   ## RFC-0005 S8f
    let wasMember = select(typed, elem)
    let newMembers = store(typed, elem, mkBool(true))
    let newSize = ite(wasMember, recv.setSize, recv.setSize + mkInt(1))
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSetExcl:
    let recv = lower(env, e.mutRecv)
    if containerRecvDeclined(recv, svSet, "`s.excl(x)`"): return recv
    # RFC-0005 S8z: the element at its own width, into its 64-bit cell.
    let elemSV = lower(env, e.mutArg, intLitProto(recv.setElemTy))
    let elemOpt = cellOf(elemSV, recv.setElemTy)   ## RFC-0005 S8u
    if elemOpt.isNone:
      queueDegrade(feUnsupportedOp,
        "iekSetExcl: element lowered to " & plainEnglishSymValKind(elemSV.kind) &
        " — expected a " & $recv.setElemTy & " (feUnsupportedOp)")
      return recv
    let elem = elemOpt.get
    let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
      recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
    noteSetKey(elem)   ## RFC-0005 S8f
    let wasMember = select(typed, elem)
    let newMembers = store(typed, elem, mkBool(false))
    let newSize = ite(wasMember, recv.setSize - mkInt(1), recv.setSize)
    SymVal(kind: svSet,
      setMembersRaw: toAnyAst(newMembers),
      setSize: newSize, setElemTy: recv.setElemTy)
  of iekSeqDel:
    # N14 (RFC-chapulin-hardening bucket-2): `mySeq.del(i)` — Nim's O(1)
    # unordered removal (`system.delete`/`del`: swap the target slot with the
    # LAST element, then shrink by one). `mySeq.del(i)` A-normalises to
    # `mkAssign(recvName, mkSeqDel(mkVar(recvName), idx))` (dsl_parser.nim) —
    # an ordinary `isAssign` whose value is THIS expression, evaluated inside
    # the exception-free `lower()` — so the OOB `IndexDefect` check can't
    # `forkDefect` directly (no `Path`/`WalkCtx` fork access here, same
    # constraint `iekStrAt`'s SND-4 fix hit for `s[i]`). Routed through the
    # SAME sink -> drain-fork pattern: push the OOB predicate to
    # `seqOobConds` (`syncSeqOobCond`), drained by `drainSeqOobRaises` (via
    # `drainScalarRaiseForks`, already called by `isAssign`'s own walker arm)
    # into an unconditional `IndexDefect` fork — parity with `isIndex`'s own
    # unconditional Phase 16 D1a fork on the READ side.
    let recv = lower(env, e.delSeq)
    if recv.kind != svSeq:
      # Defense in depth (W2b precedent) — SHOULD be unreachable given the
      # parse-time itSeq gate; decline in-band rather than a raw crash.
      let declineMsg = "iekSeqDel: receiver lowered to " & plainEnglishSymValKind(recv.kind) &
             " — expected svSeq (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg, kind = weInternalWalkerFault),
        "__seqDelKindMismatch", fresh)
    if recv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      declinePlaceholderInLower(recv, "", "mutation (.del)")
      return recv
    let idxSV = lower(env, e.delIdx, some(SymVal(kind: svInt, zi: mkInt(0))))
    let idxZi = toZ3Int(idxSV)
    let lenZi = recv.seqLen # [placeholder-audited]
    # RFC-0005 S8g: `del`'s index is a `Natural` (`proc del*[T](x: var
    # seq[T], i: Natural)`), so a negative `i` raises `RangeDefect` at the
    # call's conversion, before any indexing; only `i >= len` is the
    # `IndexDefect` (probe: `@[1,2,3].del(-1)` -> RangeDefect, `.del(3)` ->
    # IndexDefect). Both were `IndexDefect`.
    let oob = idxZi >= lenZi
    syncSeqOobCond(oob)
    let negIdx = idxZi < mkInt(0)
    syncRangeDefectCond(negIdx)
    # Swap-with-last: data' = store(data, idx, data[len-1]); len' = len-1.
    # `idxZi` may equal `lenZi - 1` (deleting the last element) — the store
    # then writes the SAME value back to the SAME slot, a harmless no-op
    # overwrite; no special-case needed. The OOB predicate above is asserted
    # (never gates this computation) — on the OOB sub-path the drain forks a
    # raise BEFORE any consumer observes this result (mirrors `iekStrAt`'s
    # own "value computed unconditionally, only ever OBSERVED on the
    # in-bounds survivor" doc precedent).
    if e.delShift:
      # RFC-0005 S8bl: `delete(s, i)` -- every element after `i` moves down
      # one (`movingCopy(x[j], x[j+1])`, then `setLen(len - 1)`): each data
      # array is `lambda j. ite(j < i, a[j], a[j + 1])`. The defects are
      # `del`'s (a `Natural` index; `i > high(x)` raises IndexDefect).
      let ctx = requireCurrentContext()
      inc sliceViewCounter
      let jVar = mkIntVar("__delete_j" & $sliceViewCounter)
      let below = jVar < idxZi
      let next = jVar + mkInt(1)
      var arrs: seq[Z3AnyAst]
      for arr in seqArrs(recv):
        let here = wrap[Z3AnyAst](ctx, checkedSelect(ctx, arr.raw, jVar.raw))
        let after = wrap[Z3AnyAst](ctx, checkedSelect(ctx, arr.raw, next.raw))
        arrs.add lambdaOver(ctx, jVar, wrap[Z3AnyAst](ctx,
          checkedIte(ctx, below.raw, here.raw, after.raw)))
      return mkSeqSV(lenZi - mkInt(1), arrs, recv.seqElemTy)
    if not isBackedSeqElemTy(recv.seqElemTy):
      # RFC-0016 K9c follow-up: a seq of an element type the model does not
      # back, not a placeholder (an empty literal, or the stand-in a declined
      # field read binds). The swap-with-last has no arrays to read or store
      # (`seqElemAt`/`storeSeqElem` raised, a `weInternalWalkerFault`). Its
      # defects are modelled above. An empty seq always raises, so its
      # in-bounds value is never observed: the receiver is returned as is.
      # Otherwise the in-bounds side declines, as `iekSeqAdd`'s S8bl arm.
      # `lower` cannot query the solver (`unbackedElemSurvivor`), so empty
      # is decided on the length term itself.
      if $simplify(lenZi) == "0": return recv
      let declineMsg = "iekSeqDel: an element removed from a seq of " &
        $recv.seqElemTy & ", an element type the model does not back " &
        "(seNestedSeqUnsupported)"
      queueDegrade(seNestedSeqUnsupported, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(tUnsupportedFieldSeq(recv.seqElemTy, declineMsg),
                         freshDegradeName("__seqDelUnbacked"), fresh)
    let lastVal = seqElemAt(recv, lenZi - mkInt(1)) # [placeholder-audited]
    # RFC-0005 S8bc: every leaf of a tree element (`seqStoreArrs`).
    let stored = seqStoreArrs(recv, idxZi, lastVal)
    if stored.isNone: return seqStoreDecline("iekSeqDel", recv.seqElemTy, lastVal)
    mkSeqSV(lenZi - mkInt(1), stored.get, recv.seqElemTy)
  of iekSeqInsert:
    # RFC-0005 S8ar. `insert(x, item, i)` (system.nim): `i` is a `Natural`
    # (a negative `i` raises RangeDefect at the call, before any change);
    # then `setLen(x, len + 1)` (the new last element is T's zero), the
    # elements at `i ..< len` move up one, and `x[i] = item` -- which raises
    # IndexDefect for `i > len`, AFTER the seq has grown (probed:
    # `@[1,2,3].insert(9, 5)` caught leaves `@[1, 2, 3, 0]`). The parser
    # emits the call as two assignments to the receiver, the grow phase
    # (`insGrow`) and then the place phase, so each phase's defect forks
    # with the state Nim raises it in. N14 had declined `insert` as needing
    # a quantifier; the shift is the array lambda `iekSeqSlice` already
    # builds (beta-reduced by Z3 at every select).
    let recv = lower(env, e.insSeq)
    if recv.kind != svSeq:
      # Defense in depth (W2b precedent): the parser emits `insert` only for
      # an itSeq receiver.
      let declineMsg = "iekSeqInsert: receiver lowered to " &
        plainEnglishSymValKind(recv.kind) & " — expected svSeq (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg, kind = weInternalWalkerFault),
        freshDegradeName("__seqInsertKindMismatch"), fresh)
    if recv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      declinePlaceholderInLower(recv, "", "mutation (.insert)")
      return recv
    let idxZi = toZ3Int(lower(env, e.insIdx, some(SymVal(kind: svInt, zi: mkInt(0)))))
    let lenZi = recv.seqLen # [placeholder-audited]
    if e.insGrow:
      let negIdx = idxZi < mkInt(0)
      syncRangeDefectCond(negIdx)
      if not defaultZeroTotal(recv.seqElemTy):
        # A backed element type whose all-zero memory is not a value of
        # the type (a variant whose ordinal-0 tag is illegal) has no
        # `setLen` element to model.
        let declineMsg = "iekSeqInsert: the element type " &
          plainEnglishTypeKind(recv.seqElemTy.kind) &
          " has no zero value for insert's setLen (feUnsupportedOp)"
        queueDegrade(feUnsupportedOp, declineMsg)
        var fresh: seq[Z3Bool]
        return allocateSym(
          tUnsupportedFieldSeq(recv.seqElemTy, declineMsg, kind = feUnsupportedOp),
          freshDegradeName("__seqInsertNoZero"), fresh)
      let zero = defaultZero(recv.seqElemTy, freshDegradeName("__seqInsertZero"))
      # RFC-0005 S8bc: every leaf of a tree element (`seqStoreArrs`).
      let grown = seqStoreArrs(recv, lenZi, zero)
      if grown.isNone: return seqStoreDecline("iekSeqInsert", recv.seqElemTy, zero)
      return mkSeqSV(lenZi + mkInt(1), grown.get, recv.seqElemTy)
    let val = lower(env, e.insVal, intLitProto(recv.seqElemTy))
    if not seqElemFits(val, recv.seqElemTy):
      let declineMsg = "iekSeqInsert: element lowered to " &
        plainEnglishSymValKind(val.kind) & " for a seq[" &
        plainEnglishTypeKind(recv.seqElemTy.kind) & "] (weInternalWalkerFault)"
      queueDegrade(weInternalWalkerFault, declineMsg)
      var fresh: seq[Z3Bool]
      return allocateSym(
        tUnsupportedFieldSeq(tInt(8, false), declineMsg, kind = weInternalWalkerFault),
        freshDegradeName("__seqInsertElemMismatch"), fresh)
    # The grow phase made `lenZi` the new length, so `x[i]` is out of
    # bounds exactly when `i >= lenZi` (`i > ` the length at the call).
    let oob = idxZi >= lenZi
    syncSeqOobCond(oob)
    # data'[j] = (j <= i ? store(data, i, item)[j] : data[j - 1]).
    let zctx = recv.seqDataRaw.ctx # [placeholder-audited]
    # RFC-0005 S8bc: every leaf of a tree element (`seqStoreArrs`), and one
    # shift lambda per data array.
    let storedOpt = seqStoreArrs(recv, idxZi, val)
    if storedOpt.isNone: return seqStoreDecline("iekSeqInsert", recv.seqElemTy, val)
    let stored = storedOpt.get
    let orig = seqArrs(recv)
    inc sliceViewCounter
    let jVar = mkIntVar("__insertview_j" & $sliceViewCounter)
    let below = jVar <= idxZi
    let jPrev = jVar - mkInt(1)
    # OWNERSHIP DISCIPLINE: every intermediate wrapped on creation (see
    # `iekSeqSlice`).
    var lams: seq[Z3AnyAst]
    for k in 0 ..< stored.len:
      let selStored = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, stored[k].raw, jVar.raw))
      let selPrev = wrap[Z3AnyAst](zctx,
        checkedSelect(zctx, orig[k].raw, jPrev.raw))
      let body = wrap[Z3AnyAst](zctx,
        checkedIte(zctx, below.raw, selStored.raw, selPrev.raw))
      lams.add lambdaOver(zctx, jVar, body)
    mkSeqSV(lenZi, lams, recv.seqElemTy)
  of iekSeqPop:
    # `iekSeqPop` is DEAD CODE: no parse site constructs it. N14 modeled
    # `.pop()` via a dedicated statement (`isSeqPop`, mirroring `isIndex`),
    # since `.pop()` needs a FRESH return-value bind alongside the receiver
    # rebind, a shape this single-result expression arm cannot carry.
    let recv = lower(env, e.popSeq)
    queueDegrade(feUnsupportedOp,
      "Phase 5+: " & $e.kind & " lowering arrives with #143 " &
           "follow-up (feUnsupportedOp)")
    return recv
  of iekTabRemovedSince:
    # RFC-0005 S8bx (item 4). Whether a key was removed from the table since
    # it was `trBase`, read off the term: the presence array is `trBase`'s
    # under a chain of stores (`[]=` stores `true`, `del` / `pop` / `take`
    # store `false`, `clear` is a fresh array), so a `false` store of a key
    # held there, or any other shape between the two, is a removal -- or one
    # this cannot rule out, which is the same answer (the slot walk is then
    # declined). RFC-0005 S8cn: a term (`presenceRemoved`).
    let cur = lower(env, e.trCur)
    let base = lower(env, e.trBase)
    if cur.kind != svTable or base.kind != svTable:
      SymVal(kind: svBool, bo: mkBool(true))
    else:
      SymVal(kind: svBool, bo: presenceRemoved(cur.tabPresentRaw,
                                               base.tabPresentRaw))
  of iekContains:
    let recv = lower(env, e.container)
    case recv.kind
    of svTable:
      if containerRecvDeclined(recv, svTable, "`k in t`"):
        # RFC-0005 S8u: a non-string-keyed table (declined at allocation).
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), freshDegradeName("__tabKeyDegrade"), fresh)
      # RFC-0005 S8ar: every backed key type (`tabKeyTerm`).
      let keySV = lower(env, e.key, seqElemLitProto(recv.tabKeyTy))
      let kOpt = tabKeyTerm(keySV, recv.tabKeyTy)   ## RFC-0005 S8f: noted
      if kOpt.isNone:
        queueDegrade(feUnsupportedOp,
          "`k in t`: key lowered to " & plainEnglishSymValKind(keySV.kind) &
          " — expected a " & $recv.tabKeyTy & " (feUnsupportedOp)")
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), freshDegradeName("__tabKeyDegrade"), fresh)
      let ctx = recv.tabSize.ctx
      let found = wrap[Z3Bool](ctx,
        checkedSelect(ctx, recv.tabPresentRaw.raw, kOpt.get.raw))
      let nanOpt = tabKeyNaN(keySV, recv.tabKeyTy)   ## RFC-0005 S8at
      ofBool(if nanOpt.isSome: found and not nanOpt.get else: found)
    of svSet:
      # For HashSet[int]: key is BV[64]; select(members, key) → Bool.
      # Phase 16 INV: non-int64 element types (e.g. set[char] / HashSet[uint8])
      # are not modeled — classify rather than crash (seUnsupportedSetCharInterop).
      # SND-3 (ADR-0023, walker v58): degrade IN-BAND (never `raise`) — this
      # arm is inside `lower`, reachable evaluating `x in mySet` inside a loop
      # guard, the same C-backend silent-loss hazard as the CR-17(a) site
      # above. See `loweringDidDegrade`'s doc comment for the full mechanism.
      if not isBackedSetElemTy(recv.setElemTy):   # RFC-0005 S8z
        queueDegrade(seUnsupportedSetCharInterop,
          "HashSet membership not modeled — element type " &
               $recv.setElemTy & " is not an integer or bool " &
               "(seUnsupportedSetCharInterop)")   # RFC-0005 S8z: read `.width` of any kind
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), freshDegradeName("__setContainsDegrade"), fresh)
      # RFC-0005 S8z: the key at the element type's width, into its 64-bit
      # cell (`cellOf`; was a 64-bit prototype for every element type).
      let keySV = lower(env, e.key, intLitProto(recv.setElemTy))
      # v64 (sibling audit, chapulin catalog #3 class): an svInt key is a
      # LEGITIMATE arrival — `.len`/`.find`/`parseInt` results lower
      # unconditionally to svInt (CR-1a), so `s.len in myIntSet` reached the
      # former `doAssert keySV.kind == svBV64` and native-crashed. Bridge
      # svInt→BV64 via `svIntToBV` (CR-1a precedent, inside `cellOf`);
      # anything else degrades IN-BAND per SND-3 instead of asserting.
      let keyCell = cellOf(keySV, recv.setElemTy)
      if keyCell.isNone:
        queueDegrade(weInternalWalkerFault,
          "HashSet membership key lowered to " & plainEnglishSymValKind(keySV.kind) &
               " — expected a " & $recv.setElemTy & " (weInternalWalkerFault)")
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), freshDegradeName("__setKeyDegrade"), fresh)
      # v65 / RFC-0005 S8f: record the key TERM (see
      # `ContainerCardRegistry`): the cardinality constraint counts it, and
      # the extractor renders its model value -- a symbolically-keyed
      # membership can be satisfied by a const-true model array, leaving
      # nothing else to enumerate the witness from.
      noteSetKey(keyCell.get)
      let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
        recv.setMembersRaw.ctx, recv.setMembersRaw.raw)
      ofBool(select(typed, keyCell.get))
    else:
      # N46 (round-6 re-review, ADR-0023/SND-3 class widening): was a raw
      # `raise newException`. `x in mySeq`/`x in myArray`/`x in myString`
      # (linear membership) is idiomatic, common Nim -- this arm only
      # handles svTable/svSet receivers, falling through unguarded for
      # svSeq/svArray/svString. In-band degrade: mirrors the svSet arm's
      # own `__setContainsDegrade` idiom two cases above.
      # RFC-0005 S6b: stays `feUnsupportedOp` (dcSubstituted): `e.key` is
      # never lowered (its raise forks are dropped), and system's
      # `contains(openArray)` calls the element type's `==`, which may be
      # a raising user overload.
      queueDegrade(feUnsupportedOp,
        "iekContains on unsupported kind " & plainEnglishSymValKind(recv.kind) &
             " (feUnsupportedOp)")
      var freshContains: seq[Z3Bool]
      return allocateSym(tBool(), freshDegradeName("__containsUnsupportedDegrade"), freshContains)
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
    lowerAsReceiver = true   ## RFC-0005 S8bw: the element is the read
    let recv = lower(env, e.arr)
    if recv.kind != svArray or recv.arrElems.len == 0:
      # RFC-0005 S8bw (item 1): a receiver that did not lower to an array
      # (the stand-in of an earlier in-band decline: a global read before
      # any write was an int) declines in-band. This was a `doAssert`, a
      # `weInternalWalkerFault` (`gArr[2] = k` then `gArr[2]`).
      return degradeAlloc(
        (if proto.isSome: tyOf(proto.get) else: tInt(64, true)),
        feUnsupportedExprKind,
        "iekIndex: receiver lowered to " & plainEnglishSymValKind(recv.kind) &
          (if recv.kind == svArray: " of no elements" else: "") &
          ", not an array -- degraded to sxUnknown (feUnsupportedExprKind)",
        "__indexRecvDegrade")
    if e.idx.kind == iekIntLit:
      # Fast path: concrete index. No fork; direct element lookup.
      let ix = int(e.idx.ival)
      if ix < 0 or ix >= recv.arrElems.len:
        raise newException(ValueError,  # [raise-audited: category-c: literal-index-OOB invariant -- Nim's compiler statically rejects an out-of-bounds LITERAL array index (arr[10] on array[5,int] is a compile error), so a well-formed SUT the harness has type-checked can never reach this arm with an OOB constant]
          "Phase 4: literal index " & $ix & " out of bounds 0..<" &
          $recv.arrElems.len)
      recv.arrElems[ix]
    else:
      # Symbolic index: ite-chain over each element. Z3 picks an i.
      # The "default" branch (i below first match) falls through to
      # element[0] — for OOB-handling cycle 8, the OOB path forks
      # before this point and adds the OOB constraint to its pc.
      let idxSV = lower(env, e.idx)
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
      #
      # RFC-0005 S8g: a SIGNED integer negation is `0 - x` through
      # `lowerArith`, so it carries the same overflow obligation as a binary
      # `-` (R16-4 for BV, issue #161 for a width-typed svInt): Nim raises
      # `OverflowDefect` for `-low(T)` (probe: `-low(int)`, `-low(int32)`,
      # `-low(int8)`, and `abs(low(int))`, whose body is `-x`). It was a
      # plain two's-complement negate, so `-low(int)` wrapped to itself and
      # never raised. An svInt with no static width (`ziWidth == 0`: an
      # unbounded mathematical Int, e.g. a `.len`-derived value) cannot
      # overflow and stays a plain negation, as do floats; an unsigned BV
      # has no unary minus in Nim, so `negBV` there is unchanged.
      let inner = ejectBase(lower(env, e.operand, proto))   ## Phase 15 G4
      if inner.kind == svInt and inner.ziWidth != 0 and inner.ziSigned:
        let zero = SymVal(kind: svInt, zi: mkInt(0), ziWidth: inner.ziWidth,
                          ziSigned: true, ziIvl: some(interval(0, 0)))
        lowerArith(zero, inner, bSub, e.usite)
      elif inner.kind == svInt: SymVal(kind: svInt, zi: -inner.zi)
      elif inner.kind == svFloat32: SymVal(kind: svFloat32, fp32: -inner.fp32)  # Phase 15 F3
      elif inner.kind == svFloat64: SymVal(kind: svFloat64, fp64: -inner.fp64)  # Phase 15 F3
      elif inner.kind in {svBV8, svBV16, svBV32, svBV64} and inner.signed:
        let zero = case inner.kind
          of svBV8:  liftBV(mkBitVec[8](0), true)
          of svBV16: liftBV(mkBitVec[16](0), true)
          of svBV32: liftBV(mkBitVec[32](0), true)
          else:      liftBV(mkBitVec[64](0'i64), true)
        lowerArith(zero, inner, bSub, e.usite)
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
        queueDegrade(weInternalWalkerFault,
          "uNot on unsupported operand kind " & plainEnglishSymValKind(inner.kind) &
               " — expected svBool or a BV (weInternalWalkerFault)")
        var fresh: seq[Z3Bool]
        allocateSym(tBool(), freshDegradeName("__uNotDegrade"), fresh)
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
        queueDegrade(seUnsupportedStringOp,
          "ordering comparison on s[i] (char) is not modeled " &
               "(CR-17: String+Int+BV ordering — latent Z3 hang shape; " &
               "use == / != for char comparisons)")
        var fresh: seq[Z3Bool]
        return allocateSym(tBool(), freshDegradeName("__strCmpOrderingDegrade"), fresh)
      let pp = probeProto(env, e)
      if pp.isSome:
        var l = ejectBase(lower(env, e.lhs, pp))   ## Phase 15 G4: distinct→base
        var r = ejectBase(lower(env, e.rhs, pp))
        # Phase 15 C5: closure ==/!= (nominal-for-site + structural-for-env,
        # ADR-0009 D7). ejectBase passes svClosure through unchanged.
        # MUST return before lowerCmp (short-circuit; lowerCmp has no closure branch).
        if l.kind == svClosure and r.kind == svClosure:
          return closureEq(l, r, e.bop)
        if l.kind == svClosure or r.kind == svClosure:
          return closureMixedCmpDecline(l, r, e.bop)   ## RFC-0016 INT-65
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        # MUST return before lowerCmp (short-circuit; lowerCmp has no ref/ptr branch).
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        if l.kind in {svRef, svPtr} or r.kind in {svRef, svPtr}:
          return refMixedCmpDecline(l, r, e.bop)   ## RFC-0005 S8m
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
        if l.kind == svClosure or r.kind == svClosure:
          return closureMixedCmpDecline(l, r, e.bop)   ## RFC-0016 INT-65
        # Phase 15 R2: ref/ptr ==/!= → ground address-const equality.
        # MUST return before lowerCmp (short-circuit).
        if l.kind in {svRef, svPtr} and r.kind in {svRef, svPtr}:
          return refEq(l, r, e.bop)
        if l.kind in {svRef, svPtr} or r.kind in {svRef, svPtr}:
          return refMixedCmpDecline(l, r, e.bop)   ## RFC-0005 S8m
        # CR-9(c) D3: delegate to lowerCmp.  reconcileInt is a no-op when
        # kinds match (probe-miss: both sides lowered without width steering).
        lowerCmp(l, r, e.bop)
    # ---- boolean / bitwise dispatch by operand type ----
    of bAnd, bOr, bXor:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r = lower(env, e.rhs, pp)
      if (l.kind == svBool) != (r.kind == svBool):
        return mixedBitwiseDecline(l, r, e.bop)   ## RFC-0005 S8bc
      if l.kind == svBool:
        case e.bop
        of bAnd: ofBool(l.bo and r.bo)
        of bOr:  ofBool(l.bo or  r.bo)
        of bXor: ofBool(l.bo xor r.bo)
        else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]
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
        # RFC-0005 S8w: a width-stamped operand bridges at its own width
        # and signedness (`stampedIntToBV`); the other side follows it.
        let lStamped = l.ziWidth in [8, 16, 32, 64]
        let targetKind =
          if r.kind in {svBV8, svBV16, svBV32, svBV64}: r.kind
          elif lStamped: stampedIntToBV(l).kind
          elif r.kind == svInt and r.ziWidth in [8, 16, 32, 64]:
            stampedIntToBV(r).kind
          else: svBV64
        # An UNSTAMPED Int (`.len`/`find`/`indexOf`/`parseInt`) is a Nim
        # `int`: bridged at 64 bits it is SIGNED, so `find(..) and -2` of
        # an absent `find` (-1) compares negative. `svIntToBV` stamps its
        # result unsigned, which made `(s.find('a') and -2) < 0` a false
        # `sxUnsat` (RFC-0005 S8w). Against a BV operand it takes that
        # operand's signedness, as the Nim operation does.
        let unstampedSigned =
          if r.kind in {svBV8, svBV16, svBV32, svBV64}: r.signed
          elif lStamped: l.ziSigned
          else: true
        var lb =
          if lStamped and stampedIntToBV(l).kind == targetKind:
            stampedIntToBV(l)
          else: svIntToBV(l, targetKind)
        if not (lStamped and stampedIntToBV(l).kind == targetKind):
          lb.signed = unstampedSigned
        var rb =
          if r.kind == svInt and r.ziWidth in [8, 16, 32, 64] and
             stampedIntToBV(r).kind == targetKind:
            stampedIntToBV(r)
          elif r.kind == svInt: svIntToBV(r, targetKind)
          else: r
        if r.kind == svInt and not (r.ziWidth in [8, 16, 32, 64] and
                                    stampedIntToBV(r).kind == targetKind):
          rb.signed = lb.signed
        case e.bop
        of bAnd: binBV(lb, rb, `and`)
        of bOr:  binBV(lb, rb, `or`)
        of bXor: binBV(lb, rb, `xor`)
        else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]
      else:
        case e.bop
        of bAnd: binBV(l, r, `and`)
        of bOr:  binBV(l, r, `or`)
        of bXor: binBV(l, r, `xor`)
        else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]
    # ---- bit shifts (always BV; cycle 8 ban list applies) ----
    of bShl, bShr:
      let pp = probeProto(env, e)
      let l = lower(env, e.lhs, pp)
      let r0 = lower(env, e.rhs, some(l))
      # RFC-0005 S8w: an `isIntOffset` param the ban scan turned down is
      # now a width-stamped `svInt` (`runSymexImpl`), and a shift on it is
      # exactly the shift of its bit pattern (`stampedIntToBV`). An
      # UNSTAMPED Int (`.len`/`find`/`indexOf`/`parseInt`) is a Nim `int`
      # and shifts as a signed 64-bit one (it failed this arm's assertion,
      # a walker fault, before S8w).
      let lStamped = l.kind == svInt and l.ziWidth in [8, 16, 32, 64]
      doAssert l.kind != svBool, "shift on a bool"
      if e.bop == bShr and l.kind == svInt and not lStamped and
         e.rhs.kind == iekIntLit and e.rhs.ival in 0'i64 .. 62'i64:
        # RFC-0005 S8w2: `x shr k` by a literal `k` on an unstamped Int
        # stays in Int arithmetic. Nim's `shr` on a signed int is
        # arithmetic, i.e. floor division by 2^k, and Z3's Int `div` by a
        # positive divisor IS floor division (Euclidean), so this is the
        # same value as the bridge below without its `int2bv`: over a
        # `find` on a string that bridge cost Z3 4.13.4 the whole
        # `seqQueryRLimit` (`s8w_findshift`, symex-mingw).
        return SymVal(kind: svInt, zi: l.zi div mkInt(1'i64 shl e.rhs.ival))
      var lb =
        if lStamped: stampedIntToBV(l)
        elif l.kind == svInt: svIntToBV(l, svBV64)
        else: l
      if l.kind == svInt and not lStamped: lb.signed = true
      # RFC-0005 S8ac: the count is masked to the operand width, as the C
      # backend does (`shiftCountBV`), and so may be any int width: an
      # `int8 shl int` failed `binBV`'s width assertion before (a walker
      # fault).
      var r =
        if r0.kind == svInt:
          (if r0.ziWidth in [8, 16, 32, 64]: stampedIntToBV(r0)
           else: svIntToBV(r0, lb.kind))
        else: r0
      r = shiftCountBV(r, lb.kind)
      r.signed = lb.signed
      case e.bop
      of bShl: binBV(lb, r, `shl`)
      of bShr: shrBV(lb, r)
      else: raise newException(ValueError, "unreachable")  # [raise-audited: category-c: op-narrowed by caller dispatch (own label: unreachable)]
    # ---- arithmetic — all preserve representation ----
    of bAdd, bSub, bMul, bDiv, bMod:
      let pp = probeProto(env, e)
      let l = ejectBase(lower(env, e.lhs, pp))   ## Phase 15 G4: distinct→base
      let r = ejectBase(lower(env, e.rhs, pp))
      when defined(symexTestInjectWalkerFault):
        injectShapeFault("term")   # RFC-0005 S8ce: both operands built
      lowerArith(l, r, e.bop, e.bsite, e.bFloatChecks)
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
      let baseRes = lowerArith(l, r, e.borrowOp, e.borrowSite)
      if e.borrowReturnsDistinct:
        reboxDistinct(e.borrowDistinctTy, baseRes)
      else:
        baseRes
    else:
      # N46 (round-6 re-review, ADR-0023/SND-3 class widening): was a raw
      # `raise newException`. `{.borrow.}` interception (`dsl_parser.nim`)
      # computes `borrowOp` from the raw operator token with no
      # restriction to arithmetic/comparison, so `proc `and`*(a, b: Flags)
      # {.borrow.}` on a `distinct int` (a common bitflag idiom) reaches
      # this arm unguarded. In-band degrade: the already-ejected base
      # value `l` stands in unchanged (sound over-approximation once the
      # run is forced to `sxUnknown`).
      allocDegrade(feUnsupportedOp,
        "borrow: unsupported base operator " & $e.borrowOp)
      l
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
  of iekMultiVariantLit:
    lowerMultiVariantLit(env, e)   ## RFC-0005 S8p
  of iekVariantFieldSet:
    lowerVariantFieldSet(env, e)   ## RFC-0005 S8s
  of iekHofCall:
    # Phase 15 C4 (ADR-0009). DSL higher-order call. Selects the INLINE path
    # (concrete length ≤ seqInlineThreshold; unroll the closure per element,
    # quantifier-free) or the AXIOM path (symbolic length: map → `mapArray`;
    # fold → raw `Z3_mk_app`; filter → `ceUnsupportedHof`, Phase-16 deferred).
    # Uses `walk` via `currentWalkCtxPtr`, so the body lives after `walk`.
    lowerExprHooks.lowerHofCall(env, e)
  of iekNil:
    # Phase 15 R5 (Cluster R, ADR-0010). The `nil` ref/ptr literal. Lower it to an
    # `svRef`/`svPtr` carrying the per-sort distinguished `nilConst` (`nil_<typeId>`,
    # allocated + cached by `allocRefSort`). `nilPointee` is the FULL `itRef`/`itPtr`
    # type of the ref/ptr `nil` is compared against; key the sort on its POINTEE
    # (matching `isNew`/`allocateSym`). `refEq` then decides `p == nil` as a ground
    # equality of the two `Ref_T` consts.
    let ctx = requireCurrentContext()
    # RFC-0016 INT-65: a nil proc value (`nilClosureSite`, no body).
    if e.nilPointee.kind == itUninterp:
      return nilClosure()
    let isPtr = e.nilPointee.kind == itPtr
    let pointee = if isPtr: e.nilPointee.ptrPointeeTy else: e.nilPointee.refPointeeTy
    discard allocRefSort(ctx, pointee)        ## ensure the sort + nilConst exist
    let typeId = refPointeeTypeId(pointee)
    let nilAst = currentNilConsts[typeId]
    if isPtr:
      SymVal(kind: svPtr, ptrAst: nilAst, ptrFamily: true, ptrPointee: pointee)
    else:
      SymVal(kind: svRef, refAst: nilAst, refPointee: pointee)
  of iekZeroValue:
    # RFC-0005 S8u. An uninitialised `var t: Table[K, V]` / `HashSet[T]`
    # local: Nim's `default(T)`, the empty container (`defaultZero`). A
    # shape the walker does not back (`Table[int, V]`, `HashSet[string]`)
    # has no zero value here: allocate it as `allocateSym` does, whose
    # classified in-band decline taints the path.
    if defaultZeroTotal(e.zvTy):
      defaultZero(e.zvTy, "__zeroValue")
    else:
      var scratch: seq[Z3Bool]
      let sv = allocateSym(e.zvTy, freshDegradeName("__zeroValueUnmodelled"),
                           scratch)
      queueDegrade(feUnsupportedOpHavoc,
        "zero value of " & $e.zvTy & " not modelled — degraded to sxUnknown")
      sv
  of iekBitSet:
    # RFC-0005 S8bq (item 2). A builtin `set[T]` operation.
    lowerBitSet(env, e)
  of iekPtrCast:
    lowerPtrCast(env, e)   # RFC-0016 INT-83
  of iekSeqNew:
    lowerSeqNew(env, e)

proc lower*(env: Env, e: IRExpr, proto: Option[SymVal] = none(SymVal)): SymVal =
  ## Lower `e` under `env` (`lowerExpr`). RFC-0005 S8bw (item 2): the value
  ## of a read of a global -- the outermost access of a chain over it, not
  ## a receiver of one -- declines in-band when it mentions an unwritten
  ## part (`observeGlobalRead`); an element read is simplified first, so a
  ## constant index picks its element.
  let asReceiver = lowerAsReceiver
  lowerAsReceiver = false
  result = lowerExpr(env, e, proto)
  if not asReceiver and e != nil and e.kind in {iekVar, iekField, iekIndex}:
    observeGlobalRead(e, result, simplified = e.kind == iekIndex)

proc lowerBool*(env: Env, e: IRExpr): Z3Bool =
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
    queueDegrade(weInternalWalkerFault,
      "lowerBool: expected Bool, got " & plainEnglishSymValKind(sv.kind) &
           " (weInternalWalkerFault)")
    var fresh: seq[Z3Bool]
    allocateSym(tBool(), freshDegradeName("__lowerBoolDegrade"), fresh).bo

# ---- the per-run reset ----------------------------------------------------

proc resetLowerExprState*() =
  ## RFC-0016 INT-34 B4. The per-run reset of every threadvar of this module
  ## that holds run state, called by `resetSymexRunState` (the statements it
  ## held for them, in their order there). Three are not per-run:
  ## `walkerWorkUnits` is the thread's running total (a run reads its own
  ## share against `walkerWorkBase`), and `uninitArrKinds` and
  ## `bvIvlDeclKinds` are the linked Z3's decl kinds, probed once per thread.
  when defined(symexTestInjectWalkerFault):
    injectedShape = ""     ## RFC-0005 S8ce: a prior run's unfired shape
  callGuardedNames = @[]   ## RFC-0005 S8an: a run that raised mid-callee
  obligationLog = @[]      ## #161 slice 2: PER-RUN, not per-lower — see the
                           ## threadvar's own doc comment for why it must not
                           ## join the raise-cond sinks' reset list.
  resetArith()                                                     ## RFC-0016 W1-d2
  # RFC-0005 review R1-12: the rest of the per-expression lowering state.
  # Each is consumed by the drain that follows its `lower`, so a run that
  # aborted between the two (a raise out of the walk) left it set, and the
  # next run's first drain or lowering read it: `ptr` operands and closure
  # writes holding Z3 terms of the freed context, a receiver flag that
  # skipped the first read's global observation.
  pendingPtrCompares = @[]               ## RFC-0005 S8ax
  closureEnvWrites = @[]                 ## RFC-0005 S8as
  loweringReadNames = @[]                ## RFC-0005 S8as
  lowerAsReceiver = false                ## RFC-0005 S8bw
  glUnwrittenCtx = default(RawZ3Context) ## RFC-0005 batch 6: the run's
                                         ## context is new (`glUnwrittenFresh`)
  seqConformCounter = 0                  ## RFC-0005 S8bc: bound-var names
  bitSetCardTerms = @[]                  ## RFC-0005 S8bq: reset card terms
  bitSetCardIds.clear()
  bitSetCardSets.clear()                 ## RFC-0005 S8bv
  uninitSeqBases = @[]                   ## RFC-0005 S8bq: newSeqUninit bases
  uninitSeqBaseIds.clear()
  uninitSeqAliases.clear()
  uninitAliasHeld = @[]
  sliceViewCounter = 0                   ## v67: reset slice-view bound-var counter
  variantLitFreshCounter = 0             ## Round-6 A1: reset variant-lit fresh-field counter
  variantConstructSymFreshCounter = 0    ## Round-6 A3: reset per-fork fresh-field counter
  globalEntryVals = initTable[string, SymVal]()  ## RFC-0005 S8as
  glUnwritten = initTable[int, string]()   ## RFC-0005 batch 6: their
  glPartHavoc = initTable[string, bool]()  ## unwritten leaves with them
  glUnwrittenAsts = @[]
  glWatched = initHashSet[string]()   ## RFC-0005 S8bz
  glVarGlobal = initTable[string, string]()   ## RFC-0005 batch 11
  noinitSerial = 0                    ## RFC-0005 S8bz

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(closureEnvWrites, loweringReadNames, arithFrames,
    checkScopes, obligationLog, sliceViewCounter, variantLitFreshCounter,
    variantConstructSymFreshCounter, seqConformCounter, bitSetCardTerms,
    bitSetCardIds, bitSetCardSets, walkerWorkUnits, uninitSeqBases,
    uninitSeqBaseIds, uninitSeqAliases, uninitAliasHeld, uninitArrKinds,
    pendingPtrCompares, bvIvlDeclKinds, glUnwrittenCtx, glUnwritten,
    glPartHavoc, glWatched, glVarGlobal, glUnwrittenAsts, lowerAsReceiver,
    globalEntryVals, noinitSerial, callGuardedNames)
  when defined(symexTestInjectWalkerFault):
    releaseToDefault(injectedShape)

registerThreadStateRelease(releaseThreadState)
