## RFC-0016 INT-34 B5. Solving a path: a leaf cut out of `runtime.nim`.
##
## Region R2 of `runtime.nim` (`scripts/int34-deps.py`) lives here whole, in
## the order it had there:
##
##   * the witness a model gives (`extractWitness`, `modelPins`): the leaf and
##     container reads, the heap snapshot (`buildHeapSnapshot`, `renderCell`)
##     and the pointer families' keys (`ptrSelKey`, `ptrIdxKey`, `ptrKeyKey`,
##     `ptrObjKey`, `ptrTargetCode`);
##   * the solver's work accounting and budget (`ownContextUnits`,
##     `symexZ3CallCount`, the stall backstop, the query timeout, the walk and
##     tail work caps) and the `-d:symexQueryStats` instrumentation;
##   * the facts a query is issued with (`seqRangeFacts`, `divRangeFacts`,
##     `bvOffsetLinks`, `bvIntInverseFacts`, `fpIntervalRefutes`, ...), the
##     exact and capped checks (`checkExact`, `checkCapped`) and the kept
##     models (`satModels`);
##   * a path's query (`globalRoots`, `pathRoots`), its answer (`trySolve`)
##     and the loop and branch pruning checks (`pathInfeasible`,
##     `loopArmInfeasible`, `unwrittenIndependent`, `unwrittenLeafSplit`).
##
## With it, the run state of R0 that R2 reads: `currentVariantHeaps`,
## `currentWinningGlobals`, `heapWitnessNominalRegistry` and
## `currentClosureCallAxioms`. Each threadvar lives at the lowest layer that
## reads it: the walker above reads and writes them through this module's
## export, and `resetWalkSolveState` (called by `resetSymexRunState`) resets
## every one of them that is per-run.
##
## R2 calls nothing above it, so this leaf declares no hooks.
##
## Every routine is exported, so `runtime.nim` can call it; `runtime.nim`
## re-exports by name only what it exported before the cut.

import std/tables
import std/options
import std/sets
import std/hashes
import std/algorithm
import std/math
import std/monotimes
import std/strutils
import z3

import ./walk_log
import ./types
import ./abstraction
import ./symval
import ./walk_state
import ./walk_types
import ./walk_path
import ./lower_expr
import ./regex_parser
import ./z3check
import ./heap_model
import ./string_lower_support
import ./runtime_strings
from std/importutils import privateAccess
privateAccess(RawWitness)     ## its fields stay private to walk_types (see its header)

var currentVariantHeaps* {.threadvar.}: Table[string, Z3AnyAst]
  ## ADR-0013 D5 (Slice 2). The WINNING path's logical-heap arrays, snapshotted
  ## just before `extractWitness` (in `trySolve`'s sat branch) so the witness
  ## serializer can `select` a ref-to-variant pointee's ACTIVE-arm field values
  ## out of the per-(arm,field) heaps (`<typeId>__@<ord>__<field>`) at the ref's
  ## abstract address — emitting only the active arm's observed fields (D5).
  ## Keyed by the same `heapKey` strings the walk used. Reset at
  ## `runSymexImpl` entry. RFC-0005 S8h: `buildHeapSnapshot` uses it to know
  ## WHICH heaps the winning path materialised; it reads their input
  ## constants (`heap_<key>`), not these end-of-path terms.

var currentWinningGlobals* {.threadvar.}: seq[string]
  ## RFC-0005 S8bn (item 2). The globals bound in the WINNING path's env,
  ## snapshotted beside `currentVariantHeaps`: the witness is extracted from
  ## the initial env, which holds none, and `buildHeapSnapshot` matches a
  ## pointer's `sel` against each (`ptrTargets`' variable candidates).
  ## Reset at `runSymexImpl` entry.

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
  ## RFC-0005 S8h: `renderCell` reads it only to list a cell's fields in
  ## declaration order in its `pointsTo`; the fields themselves (and their
  ## values) come from the heaps the path materialised (`heapKeyShapes`), so
  ## a lookup miss loses the order, never a field.
  ## Reset at `runSymexImpl` entry alongside `currentRefSorts`.

var currentClosureCallAxioms* {.threadvar.}: seq[Z3Bool]
  ## Phase 15 C2b (ADR-0009 D6). The GROUND per-call-site closure axioms
  ## (`implies(callerPC and pc_i, funcSym(env, args) == v_i)`), one per body
  ## return sub-path of each closure call lowered this run. Each is a CLOSED
  ## implication (vacuously true off its call occurrence's path), so it is
  ## drained into EVERY `trySolve` globally. RFC-0005 S7: the implied value is
  ## a per-occurrence fresh constant, not the funcSym application (see
  ## `trySolve`'s drain comment for the admission rule). NEVER a `∀env,args` axiom (that HANGS Z3 — the G4 MBQI lesson);
  ## the function is applied at the GROUND `(env, args)` of THIS occurrence and
  ## equated to a value, identical in shape to G4's decidable eject-pin. Reset
  ## at `runSymexImpl` entry.
  ## CR-9 A0: intentionally LEFT as a threadvar. It is a global-by-design solver
  ## axiom pool drained into every `trySolve` check — soundness-critical and just
  ## stabilised by ADR-0012 slice 1. Migrating it to a WalkCtx field yields no
  ## verdict benefit and risks the closure-soundness machinery.

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

proc evalStrBytes*(m: Z3Model, a: Z3String): string =
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
  when defined(symexTestInjectWalkerFault):
    injectShapeFault("eval")   # RFC-0005 S8ce: the evaluated term live
  let codepoints = getStringContents(ev)
  result = newString(codepoints.len)
  for i, cp in codepoints:
    if cp < 0 or cp > 255:
      raise newException(ValueError,  # [raise-audited: category-c: documented byte-range invariant (own doc: every itString free variable is constrained to [0,255] at allocation, so a model-evaluated codepoint outside that range cannot occur)]
        "evalStrBytes: model codepoint " & $cp & " at index " & $i &
        " outside nelli's byte-string invariant [0, 255]")
    result[i] = char(cp)

when defined(symexTestInjectWalkerFault):
  proc injectedExtractionFaultTerms*(s: Z3String): seq[Z3String] =
    ## RFC-0005 S8bx fault injection (see `extractLeaf`): raises with a Z3
    ## term in its result, which the caller destroys on the raise path.
    result = @[s]
    raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for the S8bx extraction-raise test)]
      "S8bx synthetic swallowed extraction fault (symexTestInjectWalkerFault)")

proc extractLeaf*(m: Z3Model, w: var RawWitness, path: string, sv: SymVal) =
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
        let exErr64 = SymexErrorInfo(kind: feExtractionFailed, severity: severity(feExtractionFailed),
          msg: "float64 witness at '" & path & "' did not resolve to a concrete numeral",
          scope: walkSite())   # RFC-0005 S8: recorded at the hit that extracts
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
        let exErr32 = SymexErrorInfo(kind: feExtractionFailed, severity: severity(feExtractionFailed),
          msg: "float32 witness at '" & path & "' did not resolve to a concrete numeral",
          scope: walkSite())   # RFC-0005 S8: recorded at the hit that extracts
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
    # RFC-0005 S8ax: `evalInt` raises on a value outside `int64`, and a
    # raise out of the walk ends it with nothing recorded (a false
    # `sxUnsat`). Every cell an Int-sorted heap read is bounded
    # (`intCellRangeFacts`); one the query never read is only the model's,
    # and is recorded as not extracted instead.
    let ev = m.eval(sv.zi, modelCompletion = true)
    var v: int64
    if not Z3_get_numeral_int64(ev.ctx.raw, ev.raw, addr v):
      let exErrI = SymexErrorInfo(kind: feExtractionFailed, severity: severity(feExtractionFailed),
        msg: "integer witness at '" & path & "' is not an int64 numeral (" &
             $ev & ")",
        scope: walkSite())
      extractionErrors.add exErrI     # threadvar: fallback
      syncExtractionError(exErrI)     # CR-9 Stage 5: LIVE WalkCtx field
      v = 0
    w.intVals[path] = v
    # Phase 14 A6: a promoted variant discriminator lands in svInt
    # but the witness reader for its underlying `itInt(unsigned)`
    # disc type reads from `uintVals`. Mirror into both maps so
    # whichever reader path the emitter picks finds the value.
    if v >= 0: w.uintVals[path] = uint64(v)
  of svString:
    when defined(symexTestInjectWalkerFault):
      # RFC-0005 S8bx fault injection (compiled out of every normal build;
      # `-d:symexTestInjectWalkerFault` is set for its dedicated test files
      # only, by their `.nim.cfg`): witness extraction fails on a string
      # parameter named for the shape. `injectExtractionFault` raises
      # straight out of extraction; `injectSwallowedExtractionFault` raises
      # in a callee whose result -- holding a Z3 term -- the C backend
      # destroys on the raise path, which loses the raise inside extraction
      # itself at base (S8ce's nim-z3 fix keeps it).
      if path == "injectExtractionFault":
        raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for the S8bx extraction-raise test)]
          "S8bx synthetic extraction fault (symexTestInjectWalkerFault)")
      if path == "injectSwallowedExtractionFault":
        var held = @[sv.str]   # reassigned, as `walkBlock` reassigns
        held = injectedExtractionFaultTerms(sv.str)
        discard held
    w.strVals[path] = m.evalStrBytes(sv.str)
  of svTuple, svArray, svSeq, svTable, svSet, svVariant, svMultiVariant,
     svDistinct, svClosure, svRef, svPtr, svBitSet:
    ## svClosure: Phase 15 C1; svRef/svPtr: Phase 15 R1a (no witness leaf yet —
    ## the heap-snapshot witness format lands R11b/R12).
    raise newException(ValueError,  # [raise-audited: category-c: witness extraction -- runs inside the walk since S1c (trySolve); it reaches runSymexCaught as weInternalWalkerFault on both backends (RFC-0005 S8ce)]
      "extractLeaf called on non-primitive kind=" & $sv.kind)

proc clampToDeclaredRange*(v: int64, ty: IRType): int64 =
  ## Issue #163 wiring-audit W2/W4 (+ review R4, the Table sibling below).
  ## `ty.hasRange`'s ONE verdict-side consumer (`allocateSym`'s `itInt` arm)
  ## only ever runs for a value that passed through ordinary per-element
  ## allocation — a seq element (raw Z3 array), a ref-object field
  ## (field-split heap array), and a Table value (string-keyed Z3 array)
  ## never do, so an element/field/value the walker never READ on the
  ## winning path stays entirely unconstrained in-solver (documented,
  ## sound-for-verdicts limitation — see the `isIndex`/svSeq and
  ## `isIndex`/svTable arms' own comments). Left alone, the model is free
  ## to pick ANY value for it, and witness reconstruction assigning that
  ## value into the SUT's own `range[lo..hi]`-typed slot raises a real
  ## `RangeDefect` out of the caller's process (empirically confirmed: an
  ## unread `seq[range[50..60]]` element, an unread sibling `ref object`
  ## field sharing another instance's field-split heap, and an unread
  ## `Table[string, range[lo..hi]]` key all extract as the solver's default
  ## `0`). Clamping to the nearest bound at EXTRACTION time is sound here
  ## specifically because the value has no effect on the verdict already
  ## reached (unread), so any in-range substitute is exactly as valid a
  ## witness as any other.
  if v < ty.rangeLo: ty.rangeLo
  elif v > ty.rangeHi: ty.rangeHi
  else: v

proc clampWitnessField*(w: var RawWitness, path: string, fty: IRType) =
  ## Issue #163 review R11. The WITNESS-CLAMP half of the two-obligation
  ## contract — see `rangeCondsIfNeeded`'s doc comment (beside `bvRangeConds`)
  ## for the solver-side CONSTRAINT half and the full bug-family rationale
  ## (W2/W4/R3/R4/R17 all independently hand-wrote this exact guard plus
  ## signed/unsigned dispatch at a different backing-store shape).
  ##
  ## Patches an ALREADY-KEYED witness map entry at `path` in place — it does
  ## NOT fabricate one. If `fty` declares no range, or `path` was never
  ## written (the cell was never observed on the winning path), this is a
  ## no-op (Invariant 3: never fabricate a witness value the walker never
  ## wrote).
  ##
  ## Preserve the signed/unsigned split exactly: `fty.signed` selects
  ## `w.intVals`, otherwise `w.uintVals` — cross-wiring it would silently
  ## clamp the wrong map (a no-op on the real one) or corrupt the other.
  if fty.kind == itInt and fty.hasRange:
    if fty.signed and w.intVals.hasKey(path):
      w.intVals[path] = clampToDeclaredRange(w.intVals[path], fty)
    elif not fty.signed and w.uintVals.hasKey(path):
      w.uintVals[path] = uint64(clampToDeclaredRange(int64(w.uintVals[path]), fty))
  elif fty.kind in {itFloat32, itFloat64} and fty.floatRange:
    # RFC-0016 INT-77: an unread float-range cell, as an unread int one; a
    # value outside the interval is replaced by its low bound. NaN is a value
    # of the range (int6: Nim's check, `x < lo or x > hi`, passes it).
    template clampF(x, lo, hi: untyped): untyped =
      (if x < lo or x > hi: lo else: x)
    if fty.kind == itFloat64 and w.float64Vals.hasKey(path):
      w.float64Vals[path] = clampF(w.float64Vals[path], fty.floatLo, fty.floatHi)
    elif fty.kind == itFloat32 and w.float32Vals.hasKey(path):
      w.float32Vals[path] = clampF(w.float32Vals[path], float32(fty.floatLo),
                                   float32(fty.floatHi))

proc renderedSize*(m: Z3Model; size: Z3Int): int =
  ## RFC-0005 S8f. A table/set size under the model. Allocation bounds it to
  ## `[0, 1024]`; the clamp only guards a malformed model.
  int(max(0'i64, min(m.evalInt(size), 1024'i64)))

func cellModelValue*(c: int64; ty: IRType): int64 =
  ## RFC-0005 S8z. The value a container cell's model value `c` holds at
  ## `ty` (`cellValue`, concretely): its low `ty.width` bits, sign- or
  ## zero-extended by `ty`'s signedness.
  if ty.kind == itBool: (if c != 0: 1'i64 else: 0'i64)
  elif ty.width >= 64: c
  elif ty.signed: ashr(c shl (64 - ty.width), 64 - ty.width)
  else: c and ((1'i64 shl ty.width) - 1)

func cellInDomain*(c: int64; ty: IRType): bool =
  ## RFC-0005 S8z. `inCellDomain`, concretely.
  let d = cellDomain(ty)
  if not d.bounded: true
  elif (ty.kind == itInt and ty.signed) or d.lo >= 0 and d.hi >= 0 and c >= 0:
    c >= d.lo and c <= d.hi
  else: cast[uint64](c) >= cast[uint64](d.lo) and
        cast[uint64](c) <= cast[uint64](d.hi)

proc evalStrBytesOrEmpty*(m: Z3Model, a: Z3String): Option[string]
  ## RFC-0005 S8ar fwd-decl (defined below, by `renderHeapCompound`).
  ## `extractSeqElements` renders a `seq[string]` element with it.

proc extractFromSymVal*(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal)
  ## RFC-0005 S8at fwd-decl: a container `Table` value is extracted as one.

proc extractTreeValue*(m: Z3Model, w: var RawWitness, path: string,
                      sv: SymVal, ty: IRType)
  ## RFC-0005 S8bz fwd-decl (defined below).

proc extractTableEntries*(m: Z3Model, w: var RawWitness, path: string,
                         sv: SymVal) =
  ## RFC-0005 S8f (was: the present keys among a static scan of string
  ## LITERALS, for a top-level param only, `len` ignored -- `{:}` for
  ## `t.len == 2`, for a symbolic key, and for a table in an object field).
  ## Renders the content `containerCardConds` proves exists (see
  ## `ContainerCardRegistry`): the model value of every key term the run
  ## lowered at which the table is present, then fresh keys that no term's
  ## value names until there are `len` entries. A select at any term sees
  ## exactly the model's answer, and no select can see a fresh key, so the
  ## real table behaves as the model on the winning path.
  ## RFC-0005 S8ar: every backed key and value type. A cell key renders as
  ## the decimal of its cell (`witnessIntAs` reads it back), from the run's
  ## set keys in the key type's domain, filled from the domain's low end as
  ## `extractSetMembers` fills; a value as the leaf its type has (a cell in
  ## `intVals`, a string in `strVals`, a float through `extractLeaf`). Was
  ## string keys and integer values only: any other value rendered no
  ## entry at all.
  let ctx = sv.tabSize.ctx
  let kty = sv.tabKeyTy
  let vty = sv.tabValTy
  var keyList: seq[string]
  proc emit(w: var RawWitness; k: string; keyRaw: RawZ3Ast) =
    let vpath = path & "." & k
    let v = tabValAt(ctx, sv, keyRaw)
    case tabValLeaf(vty)
    of tvCell:
      let c = case v.kind
              of svBool: (if m.evalBool(v.bo): 1'i64 else: 0'i64)
              else: int64(m.evalInt(cellOf(v, vty).get))
      var x = cellModelValue(c, vty)   # RFC-0005 S8z
      # Issue #163 review R4: a value no read on the winning path
      # range-constrained (a key read on an untaken branch, or a fresh fill
      # key) is the model's free choice and may fall outside a
      # `range[lo..hi]` value type -- see `clampToDeclaredRange`.
      if vty.kind == itInt and vty.hasRange:   # S8z: bool
        x = clampToDeclaredRange(x, vty)
      w.intVals[vpath] = x
    of tvStr:
      w.strVals[vpath] = evalStrBytesOrEmpty(m, v.str).get("")
    of tvF32, tvF64:
      extractLeaf(m, w, vpath, v)
    of tvTree:
      # RFC-0005 S8at: a container value is written as a by-value param of
      # its type is (`seqLens` + elements, `setMembers`, `tabKeys`).
      # RFC-0005 S8bz (item 2): an aggregate as a seq's tree element is, in
      # the heap's cell layout.
      if heapTreeTy(vty): extractTreeValue(m, w, vpath, v, vty)
      else: extractFromSymVal(m, w, vpath, v)
  let present = sv.tabPresentRaw
  if kty.kind == itString:
    var named: HashSet[string]   ## every term's value, present or not
    for t in containerCard.tabKeys:
      let k = m.evalStrBytes(t)
      if k in named: continue
      named.incl k
      if m.evalBool(wrap[Z3Bool](ctx, checkedSelect(ctx, present.raw, t.raw))):
        keyList.add k
        emit(w, k, t.raw)
    let n = renderedSize(m, sv.tabSize)
    var fill = 0
    while keyList.len < n:
      let k = "k" & $fill
      inc fill
      if k notin named:
        keyList.add k
        let ks = mkString(k)
        emit(w, k, ks.raw)
  else:
    var named: HashSet[int64]
    for t in containerCard.setKeys:
      let c = int64(m.evalInt(t))
      if c in named: continue
      named.incl c
      if cellInDomain(c, kty) and
         m.evalBool(wrap[Z3Bool](ctx, checkedSelect(ctx, present.raw, t.raw))):
        keyList.add $c
        emit(w, $c, t.raw)
    let n = renderedSize(m, sv.tabSize)
    let d = cellDomain(kty)
    var fill = if d.bounded: d.lo else: 0'i64
    while keyList.len < n:
      if not cellInDomain(fill, kty): break   # unreachable: the size bound
      if fill notin named:
        keyList.add $fill
        let kc = mkBitVec[64](fill)
        emit(w, $fill, kc.raw)
      if d.bounded and fill == d.hi: break
      inc fill
  w.tabKeys[path] = keyList

proc extractSeqElements*(m: Z3Model, w: var RawWitness, path: string,
                        sv: SymVal, n: int)
proc extractSetMembers*(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal)
proc evalDiscOrdinal*(m: Z3Model, disc: SymVal): int64
  ## RFC-0005 S8bc fwd-decls, for `extractTreeValue`.

const maxWitnessSeqLen* = int(maxModelledInitialSize)
  ## RFC-0005 S8bl (item 4). The longest nested seq (a seq inside a seq
  ## element or a heap cell, which has no allocation bound) a witness
  ## renders at its model length -- `newSeq`'s modelled size bound
  ## (`types.maxModelledInitialSize`; batch 7 made it that constant rather
  ## than a second `1 shl 20`). Was 1024.

proc witnessSeqLen*(raw: int64): int =
  ## RFC-0005 S8bl (item 4). A nested seq's rendered length: its model
  ## length within `[0, maxWitnessSeqLen]`, else 0 (an unread length is
  ## free, and the path does not depend on it).
  if raw >= 0 and raw <= maxWitnessSeqLen: int(raw) else: 0

proc extractTreeValue*(m: Z3Model, w: var RawWitness, path: string,
                      sv: SymVal, ty: IRType) =
  ## RFC-0005 S8bc (item 3). Write the tree value `sv` of type `ty` -- an
  ## element of a leaf-split seq -- under `path`, in the layout the heap's
  ## cell values have (`renderHeapValue`): each part at `<path>.<label>`
  ## (`heapPartLabel`: a field's name, an anonymous tuple's `Field<i>`, an
  ## array's position), a case object's discriminator and the fields of the
  ## arm it selects (and the plain fields) at `<path>.<name>`. That is the
  ## layout `readCellField`'s `fieldPairs` walk reads, which the witness
  ## reader of a seq of such elements uses (`readSeqAs`). A ref or ptr part
  ## writes nothing (no position is collected for it, and a parameter whose
  ## seq element holds one is not renderable, `isRenderableWitnessTy`). A
  ## scalar part no path read is free in the model and is clamped into its
  ## range, as a cell's is (`clampWitnessField`).
  if ty == nil: return
  case ty.kind
  of itDistinct:
    extractTreeValue(m, w, path, ejectBase(sv), distinctGround(ty))
  of itInt, itBool, itFloat32, itFloat64:
    extractLeaf(m, w, path, sv)
    clampWitnessField(w, path, ty)
  of itString:
    if sv.kind == svString:
      w.strVals[path] = evalStrBytesOrEmpty(m, sv.str).get("")
  of itTuple, itArray:
    for i, part in heapParts(ty):
      let psv = if sv.kind == svTuple: sv.fields[i] else: sv.arrElems[i]
      extractTreeValue(m, w, path & "." & part.label, psv, part.ty)
  of itVariant, itMultiVariant:
    if not svFitsHeapTy(sv, ty): return
    template axis(discName: string; discTy: IRType; disc: SymVal;
                  arms: seq[VariantArm];
                  armFields: OrderedTable[int, seq[SymVal]]) =
      let dp = path & "." & discName
      extractLeaf(m, w, dp, disc)
      clampWitnessField(w, dp, discTy)
      let ord = evalDiscOrdinal(m, disc)
      var active = -1
      for i, arm in arms:
        if not arm.isElse and int64(arm.tagOrdinal) == ord: active = i
      if active < 0:
        for i, arm in arms:
          if arm.isElse: active = i
      if active >= 0:
        let arm = arms[active]
        for j, fname in arm.fieldNames:
          extractTreeValue(m, w, path & "." & fname,
            armFields[arm.tagOrdinal][j], arm.fieldTypes[j])
    if ty.kind == itVariant:
      axis(ty.vDiscName, ty.vDiscTy, sv.vDisc[], ty.vArms, sv.vArmFields)
      for i, fname in ty.vPlainFieldNames:
        extractTreeValue(m, w, path & "." & fname, sv.vPlainFields[i],
                         ty.vPlainFieldTypes[i])
    else:
      for xi, ax in ty.mvAxes:
        axis(ax.discName, ax.discTy, sv.mvAxes[xi].disc[], ax.arms,
             sv.mvAxes[xi].armFields)
      for i, fname in ty.mvPlainFieldNames:
        extractTreeValue(m, w, path & "." & fname, sv.mvPlainFields[i],
                         ty.mvPlainFieldTypes[i])
  of itSeq:
    if sv.kind != svSeq: return
    if sv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # A placeholder's content is never modelled (a read of it declines).
      w.seqLens[path] = 0
      return
    # An element's nested length has no `1024` bound (`svCellWf`'s
    # `bounded = false`). RFC-0005 S8bl (item 4): it renders at its model
    # length up to `maxWitnessSeqLen` (was 1024: a path that needs a longer
    # nested seq rendered it empty, and the replay refuted the witness);
    # past that -- an unread length is free -- it renders empty.
    let n = witnessSeqLen(m.evalInt(sv.seqLen)) # [placeholder-audited]
    w.seqLens[path] = n
    extractSeqElements(m, w, path, sv, n)
  of itTable:
    if sv.kind == svTable: extractTableEntries(m, w, path, sv)
  of itSet:
    if sv.kind == svSet: extractSetMembers(m, w, path, sv)
  else: discard

proc extractSeqElements*(m: Z3Model, w: var RawWitness, path: string,
                        sv: SymVal, n: int) =
  ## Read elements 0..<n from the seq's Z3Array, dispatching on the
  ## element type to wrap/select with the right typed handle.
  ## RFC-0005 S8bd: on the CELL type (`seqCellTy`): a `seq[distinct T]`
  ## holds `T`'s sort and renders as `T`'s leaves, converted back by the
  ## reader (`emitTyAndReader`).
  let cellTy = seqCellTy(sv.seqElemTy)
  if isTreeSeqElemTy(cellTy):
    # RFC-0005 S8bc: a tree element, rebuilt from every data array
    # (`seqElemAt`) and written in the heap's cell layout.
    for i in 0 ..< n:
      extractTreeValue(m, w, path & "." & $i, seqElemAt(sv, mkInt(i)),
                       cellTy)
    return
  case cellTy.kind
  of itInt:
    case cellTy.width
    of 8:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[8]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
      for i in 0 ..< n:
        var v = m.evalInt(select(typed, mkInt(i)))
        if cellTy.hasRange: v = clampToDeclaredRange(v, cellTy)
        if cellTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 16:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[16]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
      for i in 0 ..< n:
        var v = m.evalInt(select(typed, mkInt(i)))
        if cellTy.hasRange: v = clampToDeclaredRange(v, cellTy)
        if cellTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 32:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[32]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
      for i in 0 ..< n:
        var v = m.evalInt(select(typed, mkInt(i)))
        if cellTy.hasRange: v = clampToDeclaredRange(v, cellTy)
        if cellTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    of 64:
      let typed = wrap[Z3Array[Z3Int, Z3BitVec[64]]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
      for i in 0 ..< n:
        var v = m.evalInt(select(typed, mkInt(i)))
        if cellTy.hasRange: v = clampToDeclaredRange(v, cellTy)
        if cellTy.signed: w.intVals[path & "." & $i] = int64(v)
        else: w.uintVals[path & "." & $i] = uint64(v)
    else:
      raise newException(ValueError,  # [raise-audited: category-c: witness extraction (RFC-0005 S8ce; see extractLeaf above)]
        "extractSeqElements: unsupported int width " & $cellTy.width)
  of itBool:
    let typed = wrap[Z3Array[Z3Int, Z3Bool]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
    for i in 0 ..< n:
      w.boolVals[path & "." & $i] = m.evalBool(select(typed, mkInt(i)))
  of itFloat32:   ## Phase 15 F9b: delegate to extractLeaf for NaN handling.
    let typed = wrap[Z3Array[Z3Int, Z3Float32]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
    for i in 0 ..< n:
      let elem = SymVal(kind: svFloat32, fp32: select(typed, mkInt(i)))
      extractLeaf(m, w, path & "." & $i, elem)
  of itFloat64:   ## Phase 15 F9b
    let typed = wrap[Z3Array[Z3Int, Z3Float64]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
    for i in 0 ..< n:
      let elem = SymVal(kind: svFloat64, fp64: select(typed, mkInt(i)))
      extractLeaf(m, w, path & "." & $i, elem)
  of itString:
    # RFC-0005 S8ar: a `seq[string]` witness. An element no path read is
    # unconstrained in the model (the byte facts are its reads',
    # `seqStrElemConds`), so a non-byte value renders "" -- any byte string
    # is a correct rendering of an element nothing observed.
    let typed = wrap[Z3Array[Z3Int, Z3String]](
      sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
    for i in 0 ..< n:
      w.strVals[path & "." & $i] =
        evalStrBytesOrEmpty(m, select(typed, mkInt(i))).get("")
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
    raise newException(ValueError,  # [raise-audited: category-c: witness extraction (RFC-0005 S8ce; see extractLeaf above)]
      "extractSeqElements: unsupported element kind " & $cellTy.kind)

proc bitSetModelMembers*(m: Z3Model; sv: SymVal): seq[int64] =
  ## RFC-0005 S8bq. The members of a builtin set under `m`, ascending: the
  ## value `lo + i` of each set bit `i`. The bit-vector is read 64 bits at a
  ## time (a numeral of at most 2^64 per chunk).
  let dom = bitSetDomain(sv.bsElemTy)
  let ctx = sv.bsRaw.ctx
  var lo = 0
  while lo < dom.size:
    let hi = min(lo + 63, dom.size - 1)
    let chunk = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_extract(
      ctx.raw, cuint(hi), cuint(lo), sv.bsRaw.raw))
    let v = m.eval(chunk)
    let bits = parseBiggestUInt($Z3_get_numeral_string(ctx.raw, v.raw))
    for i in 0 .. hi - lo:
      if ((bits shr uint64(i)) and 1'u64) == 1'u64:
        result.add dom.lo + int64(lo + i)
    lo += 64

proc extractSetMembers*(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal) =
  ## RFC-0005 S8f (was: literal candidates, a harvest of the model array's
  ## store chain and v65's per-array membership terms, `len` ignored -- a
  ## `s.len == 3` witness rendered `{}`). Same rendering as
  ## `extractTableEntries`: the present values of the run's key terms, then
  ## fresh members no term's value names until there are `len`. A store-
  ## chain key that no term names is not rendered: no select observes it,
  ## and counting it could exceed `len`.
  ## RFC-0005 S8z: a narrower element type renders only the terms whose
  ## cells are in its domain (`containerCardConds` counts only those), and
  ## fills from the domain's low end.
  doAssert isBackedSetElemTy(sv.setElemTy)
  let ety = sv.setElemTy
  let typed = wrap[Z3Array[Z3BitVec[64], Z3Bool]](
    sv.setMembersRaw.ctx, sv.setMembersRaw.raw)
  var present: seq[int64]
  var named: HashSet[int64]   ## every term's value, present or not
  for t in containerCard.setKeys:
    let v = int64(m.evalInt(t))
    if v in named: continue
    named.incl v
    if cellInDomain(v, ety) and m.evalBool(select(typed, t)):
      present.add v
  let n = renderedSize(m, sv.setSize)
  let d = cellDomain(ety)
  var fill = if d.bounded: d.lo else: 0'i64
  while present.len < n:
    if not cellInDomain(fill, ety): break   # unreachable: the size bound
    if fill notin named: present.add fill
    if d.bounded and fill == d.hi: break
    inc fill
  w.setMembers[path] = present

proc evalDiscOrdinal*(m: Z3Model, disc: SymVal): int64 =
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

proc extractFromSymVal*(m: Z3Model, w: var RawWitness, path: string,
                       sv: SymVal) =
  case sv.kind
  of svTuple:
    for i, f in sv.fields:
      let suffix = if sv.fieldNames[i].len > 0: "." & sv.fieldNames[i]
                   else: "." & $i
      extractFromSymVal(m, w, path & suffix, f)
  of svArray:
    for i, e in sv.arrElems:
      # RFC-0005 S8h: a ref/ptr element is the position `path[i]`, rendered
      # by `buildHeapSnapshot` (the svRef/svPtr arm below writes nothing).
      extractFromSymVal(m, w, path & "." & $i, e)
  of svSeq:
    if sv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # Round-6 Bug #2 (scoped decline): `seqLen` was forced `== 0` at
      # allocation time and `seqElemTy` is an UNBACKED kind (e.g. itTuple)
      # `extractSeqElements`'s dispatch does not cover — calling it would
      # raise regardless of `n`. Content is never modeled or trusted for
      # this field (any SUT read was already intercepted at parse time), so
      # record the length only.
      w.seqLens[path] = 0
    else:
      let lenVal = int(m.evalInt(sv.seqLen)) # [placeholder-audited]
      # RFC-0005 S8f: every element (was cut at 64, so a `s.len == 100`
      # witness had 64). Allocation bounds `seqLen` to `[0, 1024]`.
      let n = max(0, lenVal)
      w.seqLens[path] = n
      extractSeqElements(m, w, path, sv, n)
      # RFC-0005 S8h: a `seq[ref T]` element is the position `path[i]`,
      # rendered by `buildHeapSnapshot`.
  of svTable:
    extractTableEntries(m, w, path, sv)
  of svSet:
    extractSetMembers(m, w, path, sv)
  of svBitSet:
    # RFC-0005 S8bq: the members are the set bits, as values of `T`.
    w.setMembers[path] = bitSetModelMembers(m, sv)
  of svVariant:
    # Discriminator goes under the standard `.kind` path; arm
    # fields land under `.@<armTag>.<fieldName>`. Cycle 7's
    # witness emitter consumes them via a case dispatch on the
    # discriminator value.
    extractFromSymVal(m, w, path & "." & sv.vDiscName, sv.vDisc[])
    # Plain fields under direct sub-paths (no @tag prefix).
    for i, f in sv.vPlainFields:
      let sub = path & "." & sv.vPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f)
    for tagOrdinal, fields in sv.vArmFields.pairs:
      let armNames = sv.vArmFieldNames[tagOrdinal]
      for j, f in fields:
        # Use a tag-ordinal-keyed subpath so cycle 7 can resolve
        # by discriminator value rather than by tag name.
        let sub = path & ".@" & $tagOrdinal & "." & armNames[j]
        extractFromSymVal(m, w, sub, f)
  of svMultiVariant:
    # Phase 14 cycle A1c. Same shape as svVariant extraction but
    # iterates each axis: extract per-axis disc + arm fields. Plain
    # fields are emitted once (shared across all axes).
    for i, f in sv.mvPlainFields:
      let sub = path & "." & sv.mvPlainFieldNames[i]
      extractFromSymVal(m, w, sub, f)
    for ax in sv.mvAxes:
      extractFromSymVal(m, w, path & "." & ax.discName, ax.disc[])
      for tagOrdinal, fields in ax.armFields.pairs:
        let armNames = ax.armFieldNames[tagOrdinal]
        for j, f in fields:
          let sub = path & "." & ax.discName &
                    ".@" & $tagOrdinal & "." & armNames[j]
          extractFromSymVal(m, w, sub, f)
  of svDistinct:
    # Phase 15 G4 (Breadth-CRIT-1). The witness for a `distinct T` param goes
    # through ejection: extract the BASE SymVal (`== eject_T(distinctConst)`) at
    # the SAME path, so the emitter's eject-then-base-reader chain reads a real
    # base value instead of a silent empty leaf.
    extractFromSymVal(m, w, path, sv.distinctBaseSym[])
  of svUninterpRef:
    # Phase 15 E8. An opaque exception ref (`getCurrentException()`): its fields
    # are not modeled symbolically, so there is no witness leaf to extract.
    # Emit an informational `eeUninterpRefExtraction` (sevHint, NOT halting) and
    # drop the leaf. Drained into the sat finding's `errors` alongside F7's
    # extraction errors.
    let uninterpHint = SymexErrorInfo(
      kind: eeUninterpRefExtraction, severity: severity(eeUninterpRefExtraction),
      msg: "exception object fields not modeled symbolically (" & sv.typeTag & ")")
    extractionErrors.add uninterpHint    # threadvar: fallback
    syncExtractionError(uninterpHint)    # CR-9 Stage 5: LIVE WalkCtx field
  of svClosure:
    # Phase 15 C2a / R13 (Invariant 3). A closure as a top-level SUT RESULT has
    # no concrete proc-value rendering (a proc cannot be reconstructed as a
    # literal), so the closure VALUE itself is still classified `ceNotImplemented`
    # (sevError) rather than silently dropped. BUT R13 (sub-track A) lets a
    # closure CAPTURE a `ref T`/`ptr T` free variable; those captured refs DO
    # have a sound heap witness. RFC-0005 S8h: each captured `svRef`/`svPtr`
    # is a position under the field's sub-path, rendered (with its cell) by
    # `buildHeapSnapshot` -- `collectRefPositions`'s svClosure arm. The
    # closure-value rendering degrades gracefully (classified note).
    let cloErr = SymexErrorInfo(kind: ceNotImplemented, severity: severity(ceNotImplemented),
      msg: "closure as a top-level SUT result is not supported (no witness " &
           "rendering for a proc value)",
      scope: walkSite())   # RFC-0005 S8: recorded at the hit that extracts
    extractionErrors.add cloErr          # threadvar: fallback
    syncExtractionError(cloErr)          # CR-9 Stage 5: LIVE WalkCtx field
  of svRef, svPtr:
    # RFC-0005 S8h. A `ref`/`ptr` is a POSITION, not a leaf: nil, an alias of
    # another position, or a cell whose fields are read from the model's
    # input heap. `buildHeapSnapshot` renders all three for every position
    # (and every cell reachable from one) once the leaves are extracted; the
    # typed witness resolves them through `resolveRef`. (Before S8h this arm
    # wrote a cell's leaves here from the LAST value any path had read through
    # the param's name -- the end-of-path heap, not the input -- or a zero
    # prototype, and a nil or aliased ref was not representable.)
    discard
  else:
    extractLeaf(m, w, path, sv)

proc pointeeRendering*(w: RawWitness, path: string): Option[string] =
  ## Phase 15 R12. The heap-snapshot rendering of the scalar leaf at `path`.
  ## RFC-0005 S8h: only ever asked about a leaf `buildHeapSnapshot` has just
  ## written (a cell's scalar field or pointee, a discriminator), so the
  ## structural `"<object>"` fallback for a composite pointee's sub-leaves is
  ## gone with the composite callers it served.
  if w.intVals.hasKey(path):     return some($w.intVals[path])
  if w.uintVals.hasKey(path):    return some($w.uintVals[path])
  if w.boolVals.hasKey(path):    return some($w.boolVals[path])
  if w.float64Vals.hasKey(path): return some($w.float64Vals[path])
  if w.float32Vals.hasKey(path): return some($w.float32Vals[path])
  if w.strVals.hasKey(path):     return some(w.strVals[path])
  none(string)

# --- RFC-0005 S8h: the heap snapshot is the model's INPUT heap ----------------
# (Supersedes Cluster H H_witness's depth-first descent over the winning
# path's end-of-path heaps.) The snapshot records the heap the SUT is CALLED
# with, which is the only heap a witness can hand it. Every heap array is
# introduced as the free constant `heap_<key>` (`mkHeapArrayVar`); a path's
# `heaps[key]` is that constant under the stores and merges the path made, so
# reading the end-of-path array rendered what the SUT had WRITTEN -- `p.v ==
# 0` followed by `p.v = 1` rendered `v: 1`, a witness that does not reach the
# branch it was solved for. Selecting from `heap_<key>` itself reads the
# input.
#
# Positions. A position is any place a `ref`/`ptr` value sits in the input: a
# param; a field or element of a by-value param (`h.n`, `t.1`, `a[0]`, `s[2]`,
# a variant field `v.f`/`v.@<ord>.f`), named exactly as the witness emitter
# names it; and a ref field of a cell (`p.next`). Every position of a param
# gets an entry. A cell's field gets one unless it is nil, which renders
# inline as "nil" in the cell's `pointsTo` (an absent position reads nil).
#
# Cells. One cell per model address, named by the first position found to
# hold it: among bare params the lexicographically-first name (R12,
# unchanged), then by-value positions in param order, then fields
# breadth-first. Every other position holding the address carries
# `aliasRef = <cell>`. The walk is over model addresses, and a model's
# universe for an uninterpreted `Ref_T` sort is finite, so it ends -- a cycle
# is an alias back to a cell already named -- without a depth cut. (There was
# one, at the walker's heap-depth budget; the budget bounds the derefs a path
# makes, not the cells an input holds, and a position past the cut read nil.)
#
# A cell's fields are read from the heaps the winning path materialised
# (`currentVariantHeaps` names them). A cell's IR type does not have to list
# them: the recursive field's pointee is an empty placeholder by construction
# (`namedRefPlaceholder`), and `heapKeyShapes` records each heap's value type
# (and, for a variant's `__@disc`/`__@<ord>__f` heaps, the variant) when the
# walker introduces it. A field leaf is written at `<cell>.<field>` -- for a
# variant, the discriminator at `<cell>.<discName>` and the ACTIVE branch's
# fields at `<cell>.<field>` -- and a scalar pointee at `<cell>`, which is
# where `resolveRef` reads them.


proc registerNominalIfFull*(ty: IRType) =
  ## Learn `ty`'s field structure under its `nominalId`, but only if `ty` is a
  ## genuinely fielded (non-placeholder) named object -- a
  ## `namedRefPlaceholder` must never overwrite a real entry. Used only to
  ## ORDER a cell's `pointsTo` fields as declared; the fields themselves come
  ## from the heaps.
  if ty != nil and ty.kind == itTuple and not ty.isPlaceholder and
     ty.nominalId.len > 0 and not heapWitnessNominalRegistry.hasKey(ty.nominalId):
    heapWitnessNominalRegistry[ty.nominalId] = ty

proc collectRefPositions*(m: Z3Model, path: string, sv: SymVal,
                         acc: var seq[RefPos])
  ## RFC-0005 S8bl fwd decl (defined below `collectTreeRefPositions`).

proc collectTreeRefPositions*(m: Z3Model, path: string, sv: SymVal,
                             ty: IRType, acc: var seq[RefPos]) =
  ## RFC-0005 S8bl (item 4). The `ref`/`ptr` positions inside the tree value
  ## `sv` of type `ty` -- an element of a leaf-split seq -- named in the
  ## heap's cell layout (`extractTreeValue`, `heapPartLabel`), which is the
  ## layout the witness reader resolves them in (`readSeqAs` ->
  ## `readCellField`: a part at `<path>.<label>`, a seq's ref element at
  ## `<path>[<i>]` and its tree element at `<path>.<i>`). Before S8bl no
  ## position was collected inside a seq element, and a parameter whose
  ## element held a ref was not witness-renderable. A ref inside a Table or
  ## HashSet stays unrenderable (`treeRefPartInContainer`).
  if ty == nil: return
  case ty.kind
  of itDistinct:
    collectTreeRefPositions(m, path, ejectBase(sv), distinctGround(ty), acc)
  of itRef, itPtr:
    collectRefPositions(m, path, sv, acc)
  of itTuple, itArray:
    for i, part in heapParts(ty):
      let psv = if sv.kind == svTuple: sv.fields[i] else: sv.arrElems[i]
      collectTreeRefPositions(m, path & "." & part.label, psv, part.ty, acc)
  of itVariant, itMultiVariant:
    if not svFitsHeapTy(sv, ty): return
    template axis(disc: SymVal; arms: seq[VariantArm];
                  armFields: OrderedTable[int, seq[SymVal]]) =
      let ord = evalDiscOrdinal(m, disc)
      var active = -1
      for i, arm in arms:
        if not arm.isElse and int64(arm.tagOrdinal) == ord: active = i
      if active < 0:
        for i, arm in arms:
          if arm.isElse: active = i
      if active >= 0:
        let arm = arms[active]
        for j, fname in arm.fieldNames:
          collectTreeRefPositions(m, path & "." & fname,
            armFields[arm.tagOrdinal][j], arm.fieldTypes[j], acc)
    if ty.kind == itVariant:
      axis(sv.vDisc[], ty.vArms, sv.vArmFields)
      for i, fname in ty.vPlainFieldNames:
        collectTreeRefPositions(m, path & "." & fname, sv.vPlainFields[i],
                                ty.vPlainFieldTypes[i], acc)
    else:
      for xi, ax in ty.mvAxes:
        axis(sv.mvAxes[xi].disc[], ax.arms, sv.mvAxes[xi].armFields)
      for i, fname in ty.mvPlainFieldNames:
        collectTreeRefPositions(m, path & "." & fname, sv.mvPlainFields[i],
                                ty.mvPlainFieldTypes[i], acc)
  of itSeq:
    if sv.kind != svSeq or sv.isUnsupportedFieldPlaceholder: return # [placeholder-audited]
    if sv.seqElemTy.kind in {itRef, itPtr}:
      collectRefPositions(m, path, sv, acc)
    elif isTreeSeqElemTy(sv.seqElemTy):
      let n = witnessSeqLen(m.evalInt(sv.seqLen)) # [placeholder-audited]
      for i in 0 ..< n:
        collectTreeRefPositions(m, path & "." & $i, seqElemAt(sv, mkInt(i)),
                                sv.seqElemTy, acc)
  else: discard

proc pointerViewPos*(m: Z3Model; path: string; p: Z3AnyAst): RefPos =
  ## RFC-0016 INT-83. The `pointer` position `path` seen as the typed
  ## address of the first cast of the run (`pointerViews`) the model gives
  ## its address: as that typed position it aliases every other position of
  ## the address, and its cell holds the value a `cast[ptr T]` read saw. One
  ## no cast relates to a typed address is a cell of its own (or nil).
  let v = $m.eval(p)
  for view in pointerViews:
    if $m.eval(view.addrAst) == v:
      return RefPos(name: path, addrAst: view.typedAst, pointee: view.pointee)
  RefPos(name: path, addrAst: p, pointee: pointerPointeeTy())

proc collectRefPositions*(m: Z3Model, path: string, sv: SymVal,
                         acc: var seq[RefPos]) =
  ## RFC-0005 S8h. The `ref`/`ptr` positions inside the input value `sv` at
  ## `path`, named as `emitTyAndReader` names them (`.<field>`/`.<i>` for a
  ## tuple or object, `.<i>` for an array element that is not a ref and
  ## `[<i>]` for one that is, `[<i>]` for a `seq` element, the variant layout
  ## of `extractFromSymVal`, a `distinct` at its own path).
  case sv.kind
  of svRef:
    if sv.refPointee != nil:
      acc.add RefPos(name: path, addrAst: sv.refAst, pointee: sv.refPointee,
                     isRef: true)
  of svPtr:
    if sv.ptrPointee != nil and
       refPointeeTypeId(sv.ptrPointee) == pointerTypeId:
      acc.add pointerViewPos(m, path, sv.ptrAst)   # RFC-0016 INT-83
    elif sv.ptrPointee != nil:
      acc.add RefPos(name: path, addrAst: sv.ptrAst, pointee: sv.ptrPointee)
  of svTuple:
    for i, f in sv.fields:
      let suffix = if sv.fieldNames[i].len > 0: "." & sv.fieldNames[i]
                   else: "." & $i
      collectRefPositions(m, path & suffix, f, acc)
  of svArray:
    for i, e in sv.arrElems:
      let sub = if e.kind in {svRef, svPtr}: path & "[" & $i & "]"
                else: path & "." & $i
      collectRefPositions(m, sub, e, acc)
  of svSeq:
    if isTreeSeqElemTy(sv.seqElemTy) and treeHasRefPart(sv.seqElemTy) and
       not sv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      # RFC-0005 S8bl (item 4): a tree element's ref parts.
      let n = witnessSeqLen(m.evalInt(sv.seqLen)) # [placeholder-audited]
      for i in 0 ..< n:
        collectTreeRefPositions(m, path & "." & $i, seqElemAt(sv, mkInt(i)),
                                sv.seqElemTy, acc)
    elif sv.seqElemTy.kind in {itRef, itPtr} and
       not sv.isUnsupportedFieldPlaceholder: # [placeholder-audited]
      let ctx = sv.seqDataRaw.ctx # [placeholder-audited]
      # Allocation bounds `seqLen` to `[0, 1024]`.
      let n = max(0, int(m.evalInt(sv.seqLen))) # [placeholder-audited]
      let isPtr = sv.seqElemTy.kind == itPtr
      let pointee = if isPtr: sv.seqElemTy.ptrPointeeTy
                    else: sv.seqElemTy.refPointeeTy
      for i in 0 ..< n:
        # `Ref_T` is a RUNTIME uninterpreted sort the typed `select` cannot
        # express -- raw FFI, as `storeSeqElem` does. GROUND select.
        let raw = checkedSelect(ctx, sv.seqDataRaw.raw, # [placeholder-audited]
                                            mkInt(i).raw)
        acc.add RefPos(name: path & "[" & $i & "]",
                       addrAst: wrap[Z3AnyAst](ctx, raw), pointee: pointee,
                       isRef: not isPtr)
  of svVariant:
    for i, f in sv.vPlainFields:
      collectRefPositions(m, path & "." & sv.vPlainFieldNames[i], f, acc)
    for tagOrdinal, fields in sv.vArmFields.pairs:
      let armNames = sv.vArmFieldNames[tagOrdinal]
      for j, f in fields:
        collectRefPositions(m, path & ".@" & $tagOrdinal & "." & armNames[j],
                            f, acc)
  of svMultiVariant:
    for i, f in sv.mvPlainFields:
      collectRefPositions(m, path & "." & sv.mvPlainFieldNames[i], f, acc)
    for ax in sv.mvAxes:
      for tagOrdinal, fields in ax.armFields.pairs:
        let armNames = ax.armFieldNames[tagOrdinal]
        for j, f in fields:
          collectRefPositions(m, path & "." & ax.discName & ".@" &
                              $tagOrdinal & "." & armNames[j], f, acc)
  of svDistinct:
    collectRefPositions(m, path, sv.distinctBaseSym[], acc)
  of svClosure:
    # Phase 15 R13: a closure's captured `ref`/`ptr` free variables.
    if sv.closureEnv != nil and sv.closureEnv.kind == svTuple:
      let env = sv.closureEnv[]
      for i, f in env.fields:
        if f.kind in {svRef, svPtr}:
          let suffix = if env.fieldNames[i].len > 0: "." & env.fieldNames[i]
                       else: "." & $i
          collectRefPositions(m, path & suffix, f, acc)
  else:
    discard

proc inputHeapNamed*(key, name: string): Z3AnyAst =
  ## The free constant `name` over the sort of heap `key`'s array.
  let post = currentVariantHeaps[key]
  let ctx = post.ctx
  let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, post.raw)
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, name.cstring)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc inputHeap*(key: string): Z3AnyAst =
  ## RFC-0005 S8h. The INPUT heap for `key`: the free constant `heap_<key>`
  ## every path's `heaps[key]` is built on (`mkHeapArrayVar`), re-made by
  ## name and sort -- Z3 constants are identified by both, so this is the
  ## same term, not a new one.
  let post = currentVariantHeaps[key]
  let ctx = post.ctx
  let arrSort = ctx.checkErr Z3_get_sort(ctx.raw, post.raw)
  let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, ("heap_" & key).cstring)
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, arrSort))

proc heapKeyValTy*(key: string): IRType =
  ## The value type `mkHeapArrayVar` recorded for `key`, or nil.
  if heapKeyShapes.hasKey(key): heapKeyShapes[key].valTy else: nil

# RFC-0005 S8bh (item 2): the key and code helpers of the ptr target model
# (`ptrTargets`, runtime_heap.nim), here for `buildHeapSnapshot`.

proc ptrTargetCode*(id: string): int64 =
  ## RFC-0005 S8bh. The `sel` code of the target named `id` (a heap key, or
  ## an env name); never 0, the own cell's code.
  inheritTagCode("ptr:" & id)

proc ptrSelMatches*(selV: string; code: int64): bool =
  ## RFC-0005 S8bh. The model's rendering of a `sel` value (`selV`, decimal
  ## or a 64-bit `#x` literal) is `code`.
  selV == $code or selV == "#x" & toHex(code, 16).toLowerAscii

const ptrAimPrefix* = "@aim:"
  ## RFC-0005 S8bn (item 2). The `aliasRef` of a `ptr` position whose input
  ## target is a variable (a global, a `var` parameter): `@aim:<IR name>`.

proc ptrSelKey*(typeId: string): string = typeId & "__@ptrsel"
proc ptrIdxKey*(typeId: string): string = typeId & "__@ptridx"
proc ptrKeyKey*(typeId: string): string = typeId & "__@ptrkey"
  ## RFC-0005 S8bn (item 4). The input array `Ref_T -> String` naming the
  ## key of a pointer whose target is a `Table[string, V]` value.
  ## RFC-0005 S8bn (item 4). The input array `Ref_T -> Int` naming the
  ## element a `ptr T` of unknown origin addresses when its target is an
  ## element of a seq (`ptrTargets`): the snapshot index of the element
  ## identity (root, path, index).


var ptrLeafAims* {.threadvar.}: Table[int64, PtrLeafAim]
  ## RFC-0005 S8bn (item 4). Every `sel` code `ptrTargets` gave a part of a
  ## variable or a heap-held seq element this run; reset at run entry.

proc ptrLeafPathStr*(path: seq[int]; seqIdx: bool): string =
  for i in path: result.add "/" & $i
  if seqIdx: result.add "/*"
proc ptrLeafPathStr*(steps: seq[string]; seqIdx: bool): string =
  ## RFC-0005 S8bw (item 3). The steps as the witness names them.
  for s in steps: result.add "/" & s
  if seqIdx: result.add "/*"
proc ptrObjKey*(typeId, famKey: string): string = typeId & "__@ptrobj__" & famKey

proc ptrScalarPointee*(t: IRType): bool =
  ## RFC-0005 S8bh. The pointees whose `ptr` this model retargets: a scalar
  ## or a string (held in one whole-pointee heap cell).
  t != nil and t.kind in {itInt, itBool, itFloat32, itFloat64, itString}

proc ptrFamilyKey*(key: string): bool =
  ## RFC-0005 S8bh. `key` is a field-split heap of a field (a plain field,
  ## `<O>__<f>`, or a variant branch field, `<O>__@<ord>__<f>`), not an
  ## internal one (a discriminator, a compound leaf, a tag level, this
  ## model's own arrays).
  let at = key.find("__@")
  if at < 0: return "__" in key
  let rest = key[at + 3 .. ^1]
  # RFC-0005 S8bw (item 3): an `else` branch's field (`__@-1__<f>`) too; it
  # was no target, so a pointer to one was never seen to write it.
  rest.len > 0 and (rest[0] in {'0'..'9'} or rest.startsWith("-1__")) and
    "__" in rest

proc addrSpaceKey*(m: Z3Model; typeId, rendering: string): string =
  ## RFC-0016 INT-88. The address-space key of the non-nil typed address
  ## `rendering` of the sort `typeId`. Addresses are global across sorts:
  ## INT-83's `@toAddr_T` maps each typed address the run cast into the
  ## `pointer` space, so two typed positions (a `ptr int` and a `ptr float`)
  ## the model puts at one `pointer` address are one allocation, keyed
  ## `pointer|<address>`. A typed address no cast relates to the `pointer`
  ## space keeps its own sort's key (two such addresses of different sorts
  ## are unrelated in the model, so apart), as does a `pointer` itself.
  if typeId == pointerTypeId: return pointerTypeId & "|" & rendering
  for view in pointerViews:
    if refPointeeTypeId(view.pointee) == typeId and
       $m.eval(view.typedAst) == rendering:
      return pointerTypeId & "|" & $m.eval(view.addrAst)
  typeId & "|" & rendering

proc refAddrOf*(m: Z3Model, addrAst: Z3AnyAst, pointee: IRType): string =
  ## RFC-0005 S8h. The model address of a ref, "" for nil. Prefixed with the
  ## pointee's type id: addresses of different `Ref_T` sorts never alias,
  ## unless the run related them through the `pointer` space (RFC-0016
  ## INT-88, `addrSpaceKey`).
  let typeId = refPointeeTypeId(pointee)
  let rendering = $m.eval(addrAst)
  if currentNilConsts.hasKey(typeId) and
     $m.eval(currentNilConsts[typeId]) == rendering:
    ""
  else:
    addrSpaceKey(m, typeId, rendering)


proc heapSortObserved*(typeId: string): bool =
  ## RFC-0016 INT-88. The walk materialised a heap of the sort `typeId` (its
  ## whole-pointee heap, a field's, or a model array of its own), so a cell
  ## of the sort may hold a value the path constrains.
  for key in currentVariantHeaps.keys:
    if key == typeId or key.startsWith(typeId & "__"): return true
  false

proc crossSortCellFidelity*(b: SnapshotBuild, w: RawWitness) =
  ## RFC-0016 INT-88. A cell held at two sorts (a `ptr int` and a `ptr float`
  ## at one address) is one allocation, which the witness builds as its
  ## owner's type and hands every other position as a typed view of it
  ## (`resolveRef`). That is the model's input only when the bytes the views
  ## share say one thing: no `ref` holds it (its object is sized by its own
  ## type, which a larger view would overrun), the walk constrained the
  ## content of at most one of its sorts (each sort's heap is a separate
  ## array, so two constrained sorts may give one location two values no
  ## bytes hold), and that sort is the owner's (whose leaves the cell is
  ## filled from). Otherwise the rendered witness is not the model's, and it
  ## is recorded lossy (`feExtractionFailed`): the replay settles it.
  var sorts: Table[string, seq[int]]   # cell -> entry indexes
  for k, e in b.entries:
    if e.value == "nil": continue
    let cell = if e.aliasRef.isSome: e.aliasRef.get else: e.name
    if not b.entryOf.hasKey(cell): continue   # a field's address, an aim
    sorts.mgetOrPut(cell, @[]).add k
  for cell, idxs in sorts:
    var held: seq[string]
    var anyRef = false
    for k in idxs:
      let e = b.entries[k]
      if e.sort notin held: held.add e.sort
      if e.name in b.refPos: anyRef = true
    if held.len < 2: continue
    var observed: seq[string]
    for srt in held:
      if heapSortObserved(srt["Ref_".len .. ^1]): observed.add srt
    let ownerSort = b.entries[b.entryOf[cell]].sort
    # RFC-0016 INT-90: a cell held only at view sorts the walk relates
    # byte-wise (`crossSortLink`) IS the model's: the witness writes every
    # view's leaves into the one allocation (`renderCrossSortViews`,
    # `resolveRef`), a view wider than its owner included. A desynced run
    # is not.
    let exactViews = not anyRef and crossSortExactCell(held)
    # CR4-M2: the model's float has ONE NaN, which the witness renders as
    # Nim's canonical NaN; the bytes the cell's integer view reads (a NaN
    # payload) are then not the model's, so a NaN float leaf in a cell held
    # at several sorts is not reproducible by the witness.
    var nanLeaf = ""
    if held.len >= 2:
      for k in idxs:
        let nm = b.entries[k].name
        for tbl in [0, 1]:
          if nanLeaf.len > 0: break
          if tbl == 0:
            for path, v in w.float64Vals:
              if v != v and (path == nm or path.startsWith(nm & ".")):
                nanLeaf = path; break
          else:
            for path, v in w.float32Vals:
              if v != v and (path == nm or path.startsWith(nm & ".")):
                nanLeaf = path; break
    let why =
      if anyRef: "a `ref` shares it"
      elif nanLeaf.len > 0:
        "its float leaf '" & nanLeaf & "' is NaN in the model, and the " &
        "witness renders one canonical NaN (the payload of a NaN another " &
        "view reads is lost)"
      elif exactViews: ""
      elif observed.len > 1: "the walk constrained " & $observed.len &
                             " of its sorts (" & observed.join(", ") & ")"
      elif observed.len == 1 and observed[0] != ownerSort:
        "its constrained sort " & observed[0] & " is not its owner's (" &
        ownerSort & ")"
      else: ""
    if why.len == 0: continue
    let err = SymexErrorInfo(kind: feExtractionFailed,
      severity: severity(feExtractionFailed),
      msg: "witness cell '" & cell & "' is one address held at " &
           held.join(", ") & ", and " & why &
           ": the rendered cell is not the model's (RFC-0016 INT-88)",
      scope: walkSite())
    extractionErrors.add err     # threadvar: fallback
    syncExtractionError(err)     # CR-9 Stage 5: LIVE WalkCtx field

proc renderCell*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                cell: RefPos): Option[string]

proc renderCrossSortViews*(b: var SnapshotBuild, m: Z3Model,
                          w: var RawWitness) =
  ## RFC-0016 INT-90. Each position holding a cell at another view sort than
  ## its owner's (`a: ptr int32` beside `b: ptr int64` at one address) has
  ## its own leaves rendered under its name from its sort's input heap, so
  ## the witness writes them into the shared allocation (`resolveRef`): the
  ## bytes of a view wider than its owner, or over its owner's padding, are
  ## the model's, not the allocation's zeros. Only view sorts (`viewLeaves`;
  ## no `ref`, whose object a view cannot outgrow).
  for pos in b.aliases:
    if pos.isRef or pos.name in b.refPos: continue
    var owner = ""
    for e in b.entries:
      if e.name == pos.name and e.aliasRef.isSome: owner = e.aliasRef.get
    if not b.entryOf.hasKey(owner): continue
    let sortName = "Ref_" & refPointeeTypeId(pos.pointee)
    if b.entries[b.entryOf[owner]].sort == sortName: continue
    if viewLeaves(pos.pointee, refPointeeTypeId(pos.pointee)).len == 0: continue
    discard renderCell(b, m, w, pos)

proc addPosition*(b: var SnapshotBuild, m: Z3Model, pos: RefPos,
                 inlineNil: bool): string =
  ## RFC-0005 S8h. Record the position `pos`: its entry (unless it is nil and
  ## `inlineNil`), and, the first time its address is seen, a new cell. The
  ## result is the `pointsTo` fragment a parent cell renders for it.
  let sortName = "Ref_" & refPointeeTypeId(pos.pointee)
  let address = refAddrOf(m, pos.addrAst, pos.pointee)
  if address.len == 0:
    if not inlineNil and not b.seenPos.containsOrIncl(pos.name):
      b.entries.add HeapSnapshotEntry(name: pos.name, sort: sortName,
        value: "nil", pointsTo: none(string), aliasRef: none(string))
    return "nil"
  # RFC-0016 INT-81: a cell rendered again (`buildHeapSnapshot`) meets its
  # positions again; each is recorded once.
  if b.seenPos.containsOrIncl(pos.name): return "@" & pos.name
  if pos.isRef: b.refPos.incl pos.name   # RFC-0016 INT-88
  # RFC-0016 INT-81: the cell's floor, the deepest static type holding it.
  block:
    let cname = b.cellOf.getOrDefault(address, pos.name)
    if hierChain(pos.pointee).len > hierChain(b.floor.getOrDefault(cname)).len:
      b.floor[cname] = pos.pointee
  let rendering = $m.eval(pos.addrAst)
  if b.cellOf.hasKey(address) and b.cellOf[address] != pos.name:
    b.entries.add HeapSnapshotEntry(name: pos.name, sort: sortName,
      value: rendering, pointsTo: none(string),
      aliasRef: some(b.cellOf[address]))
    b.aliases.add pos   # RFC-0016 INT-90
  else:
    b.cellOf[address] = pos.name
    b.entryOf[pos.name] = b.entries.len
    b.entries.add HeapSnapshotEntry(name: pos.name, sort: sortName,
      value: rendering, pointsTo: none(string), aliasRef: none(string))
    b.queue.add pos
  "@" & pos.name

proc renderHeapLeaf*(m: Z3Model, w: var RawWitness, key, leafPath: string,
                    addrAst: Z3AnyAst, valTy: IRType): string =
  ## RFC-0005 S8h. Write the input-heap value of a scalar heap `key` at
  ## `addrAst` as the leaf `leafPath`; the `pointsTo` fragment for it.
  let sv = heapSelect(addrAst.ctx, inputHeap(key), addrAst, valTy)
  extractLeaf(m, w, leafPath, sv)
  # Issue #163 W4 / review R11: the field-split heap is shared by every cell
  # of the type, so a cell whose field the path never read has a free value
  # in it; clamp a ranged field (sound: the value bears on no verdict).
  clampWitnessField(w, leafPath, valTy)
  pointeeRendering(w, leafPath).get("<unobserved>")

proc evalStrBytesOrEmpty*(m: Z3Model, a: Z3String): Option[string] =
  ## RFC-0005 S8ap. `evalStrBytes` for a string the model may leave outside
  ## the byte range: a heap cell no path read is unconstrained (the byte
  ## facts are asserted of the cells a path READS, `heapCellWfConds`), so its
  ## model value may hold any codepoint. `none` for such a value; the caller
  ## renders a well-formed stand-in, sound because no read observed it.
  let ev = m.eval(a, modelCompletion = true)
  let codepoints = getStringContents(ev)
  var r = newString(codepoints.len)
  for i, cp in codepoints:
    if cp < 0 or cp > 255: return none(string)
    r[i] = char(cp)
  some(r)

proc renderHeapValue*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                     ctx: Z3Context; leafPath: string, sv: SymVal,
                     valTy: IRType): string

proc renderHeapCompound*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                        key, leafPath: string, addrAst: Z3AnyAst,
                        valTy: IRType): string =
  ## RFC-0005 S8ap. Write the INPUT value of the string or leaf-split
  ## compound cell `key` at `addrAst` under `leafPath`, exactly as
  ## `extractFromSymVal` writes a by-value param of the type (`strVals`,
  ## `seqLens` + `.<i>` element leaves, `tabKeys`, `setMembers`); the
  ## `pointsTo` fragment for it. A `seq[ref T]` element is the position
  ## `<leafPath>[<i>]`, added as a ref field is (a nil one inline).
  ##
  ## A cell no path read is unconstrained in the model (the well-formedness
  ## facts are the reads', `heapCellWfConds`), so a length outside `[0,
  ## 1024]` renders empty and a non-byte string renders "" -- any
  ## well-formed value is a correct rendering of a cell nothing observed.
  let ctx = addrAst.ctx
  if valTy.kind == itString:
    let sv = heapSelect(ctx, inputHeap(key), addrAst, valTy)
    if sv.kind != svString: return "<unsupported>"
    let s = evalStrBytesOrEmpty(m, sv.str).get("")
    w.strVals[leafPath] = s
    return s.escape
  var leaves: seq[Z3AnyAst]
  for suffix in heapLeafSuffixes(valTy):
    if not currentVariantHeaps.hasKey(key & suffix): return "<unobserved>"
    leaves.add wrap[Z3AnyAst](ctx,
      checkedSelect(ctx, inputHeap(key & suffix).raw, addrAst.raw))
  var scratchPC: seq[Z3Bool]
  let proto = allocateSym(valTy, "__heapRenderProto", scratchPC)
  let sv = svWithLeaves(ctx, proto, leaves, valTy)
  renderHeapValue(b, m, w, ctx, leafPath, sv, valTy)

proc renderHeapValue*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                     ctx: Z3Context; leafPath: string, sv: SymVal,
                     valTy: IRType): string =
  ## RFC-0005 S8ap (was `renderHeapCompound`'s tail); S8ar: recursive over a
  ## tree value (`heapCompoundTy`'s tuple / object, array, `distinct`), each
  ## part written at `<leafPath>.<label>` (`heapPartLabel`, the name
  ## `readCellField`'s `fieldPairs` walk reads) and a scalar part as a
  ## scalar field is (`extractLeaf`, clamped -- an unread part is free).
  case valTy.kind
  of itDistinct:
    return renderHeapValue(b, m, w, ctx, leafPath, ejectBase(sv), distinctGround(valTy))
  of itInt, itBool, itFloat32, itFloat64:
    extractLeaf(m, w, leafPath, sv)
    clampWitnessField(w, leafPath, valTy)
    return pointeeRendering(w, leafPath).get("<unobserved>")
  of itString:
    if sv.kind != svString: return "<unsupported>"
    let s = evalStrBytesOrEmpty(m, sv.str).get("")
    w.strVals[leafPath] = s
    return s.escape
  of itRef, itPtr:
    let (childAddr, childPointee) =
      if sv.kind == svRef: (sv.refAst, sv.refPointee)
      else: (sv.ptrAst, sv.ptrPointee)
    return addPosition(b, m, RefPos(name: leafPath, addrAst: childAddr,
                                    pointee: childPointee,
                                    isRef: sv.kind == svRef), inlineNil = true)
  of itTuple, itArray:
    var parts: seq[string]
    for i, part in heapParts(valTy):
      let psv = if sv.kind == svTuple: sv.fields[i] else: sv.arrElems[i]
      let r = renderHeapValue(b, m, w, ctx, leafPath & "." & part.label, psv,
                              part.ty)
      parts.add(if valTy.kind == itTuple: part.label & ": " & r else: r)
    return (if valTy.kind == itTuple: "(" else: "[") & parts.join(", ") &
           (if valTy.kind == itTuple: ")" else: "]")
  of itVariant, itMultiVariant:
    # RFC-0005 S8at. A case object cell: each discriminator at
    # `<leafPath>.<disc>` and the fields of the arm it selects (an `else`
    # arm when no explicit one does) and the plain fields at
    # `<leafPath>.<field>`, the paths `readCellField`'s `fieldPairs` walk
    # reads (discriminator first). The other arms' slots are not rendered:
    # Nim holds no value for them.
    if not svFitsHeapTy(sv, valTy): return "<unsupported>"
    var parts: seq[string]
    template axis(discName: string; discTy: IRType; disc: SymVal;
                  arms: seq[VariantArm];
                  armFields: OrderedTable[int, seq[SymVal]]) =
      let dp = leafPath & "." & discName
      extractLeaf(m, w, dp, disc)
      clampWitnessField(w, dp, discTy)
      parts.add discName & ": " & pointeeRendering(w, dp).get("?")
      let ord = evalDiscOrdinal(m, disc)
      var active = -1
      for i, arm in arms:
        if not arm.isElse and int64(arm.tagOrdinal) == ord: active = i
      if active < 0:
        for i, arm in arms:
          if arm.isElse: active = i
      if active >= 0:
        let arm = arms[active]
        for j, fname in arm.fieldNames:
          parts.add fname & ": " & renderHeapValue(b, m, w, ctx,
            leafPath & "." & fname, armFields[arm.tagOrdinal][j], arm.fieldTypes[j])
    if valTy.kind == itVariant:
      axis(valTy.vDiscName, valTy.vDiscTy, sv.vDisc[], valTy.vArms, sv.vArmFields)
      for i, fname in valTy.vPlainFieldNames:
        parts.add fname & ": " & renderHeapValue(b, m, w, ctx,
          leafPath & "." & fname, sv.vPlainFields[i], valTy.vPlainFieldTypes[i])
    else:
      for xi, ax in valTy.mvAxes:
        axis(ax.discName, ax.discTy, sv.mvAxes[xi].disc[], ax.arms,
             sv.mvAxes[xi].armFields)
      for i, fname in valTy.mvPlainFieldNames:
        parts.add fname & ": " & renderHeapValue(b, m, w, ctx,
          leafPath & "." & fname, sv.mvPlainFields[i], valTy.mvPlainFieldTypes[i])
    return "(" & parts.join(", ") & ")"
  else: discard
  # RFC-0005 S8ap: the svSeq reads below run only past this guard (N27).
  if sv.kind == svSeq and sv.isUnsupportedFieldPlaceholder: return "<unsupported>" # [placeholder-audited]
  case sv.kind
  of svSeq:
    let n = witnessSeqLen(m.evalInt(sv.seqLen)) # [placeholder-audited]
    w.seqLens[leafPath] = n
    var parts: seq[string]
    case sv.seqElemTy.kind
    of itRef, itPtr:
      let isPtr = sv.seqElemTy.kind == itPtr
      let pointee = if isPtr: sv.seqElemTy.ptrPointeeTy
                    else: sv.seqElemTy.refPointeeTy
      for i in 0 ..< n:
        let elem = wrap[Z3AnyAst](ctx, checkedSelect(ctx,
          sv.seqDataRaw.raw, mkInt(i).raw)) # [placeholder-audited]
        parts.add addPosition(b, m, RefPos(name: leafPath & "[" & $i & "]",
                                           addrAst: elem, pointee: pointee,
                                           isRef: not isPtr),
                              inlineNil = true)
    of itString:
      let typed = wrap[Z3Array[Z3Int, Z3String]](
        sv.seqDataRaw.ctx, sv.seqDataRaw.raw) # [placeholder-audited]
      for i in 0 ..< n:
        let e = evalStrBytesOrEmpty(m, select(typed, mkInt(i))).get("")
        w.strVals[leafPath & "." & $i] = e
        parts.add e.escape
    else:
      if isTreeSeqElemTy(sv.seqElemTy):
        # RFC-0005 S8bc: a tree element, rebuilt from every data array and
        # rendered as a tree cell value is (a ref part is a position).
        for i in 0 ..< n:
          parts.add renderHeapValue(b, m, w, ctx, leafPath & "." & $i,
                                    seqElemAt(sv, mkInt(i)), sv.seqElemTy)
      else:
        extractSeqElements(m, w, leafPath, sv, n)
        for i in 0 ..< n:
          parts.add pointeeRendering(w, leafPath & "." & $i).get("?")
    "@[" & parts.join(", ") & "]"
  of svTable:
    extractTableEntries(m, w, leafPath, sv)
    var parts: seq[string]
    for k in w.tabKeys.getOrDefault(leafPath):
      parts.add k.escape & ": " &
                pointeeRendering(w, leafPath & "." & k).get("?")
    "{" & parts.join(", ") & "}"
  of svSet:
    extractSetMembers(m, w, leafPath, sv)
    var parts: seq[string]
    for v in w.setMembers.getOrDefault(leafPath): parts.add $v
    "{" & parts.join(", ") & "}"
  else: "<unsupported>"

proc renderCellField*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                     cell: RefPos, key, fname: string, declTy: IRType): string =
  ## RFC-0005 S8h. One field of `cell`, from its input heap `key`.
  ## RFC-0005 S8ar: a tree value's first leaf is not at `key` itself
  ## (`heapLeafSuffixes`), so the observed test is of that leaf.
  let valTy = block:
    let t = heapKeyValTy(key)
    if t != nil: t else: declTy
  if valTy == nil: return "<unobserved>"
  if not currentVariantHeaps.hasKey(key & heapLeafSuffixes(valTy)[0]):
    return "<unobserved>"
  case valTy.kind
  of itInt, itBool, itFloat32, itFloat64:
    renderHeapLeaf(m, w, key, cell.name & "." & fname, cell.addrAst, valTy)
  of itRef, itPtr:
    let sv = heapSelect(cell.addrAst.ctx, inputHeap(key), cell.addrAst, valTy)
    let (childAddr, childPointee) =
      if sv.kind == svRef: (sv.refAst, sv.refPointee)
      else: (sv.ptrAst, sv.ptrPointee)
    addPosition(b, m, RefPos(name: cell.name & "." & fname,
                             addrAst: childAddr, pointee: childPointee,
                             isRef: sv.kind == svRef),
                inlineNil = true)
  of itString, itSeq, itTable, itSet, itTuple, itArray, itDistinct,
     itVariant, itMultiVariant:   ## RFC-0005 S8at: + a by-value case object
    # RFC-0005 S8ap: a string field, and a leaf-split compound field
    # (`heapCompoundTy`); an unbacked one keeps `<unsupported>`. RFC-0005
    # S8ar: a by-value tuple / object, array and `distinct` too.
    if valTy.kind == itString or heapCompoundTy(valTy):
      renderHeapCompound(b, m, w, key, cell.name & "." & fname, cell.addrAst,
                         valTy)
    else: "<unsupported>"
  else:
    # A kind the logical heap does not model (`liftHeapValue` degrades a
    # read of it): no leaf, the typed witness keeps the zero value.
    "<unsupported>"

proc cellDynamicType*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                     cell: RefPos): seq[int64] =
  ## RFC-0016 INT-81. The run-type tags of the hierarchy object `cell`, at
  ## depths `1 ..`, written as the leaves `<cell>.@lvl<j>` with its floor
  ## (`<cell>.@floor`) for the witness (`cellDynBuild`); empty outside a
  ## hierarchy. The depths down to the floor -- the deepest static type of
  ## a position holding the cell -- are that type's chain: Nim's static
  ## typing, which a parameter's facts state (`allocateSym`) and a field's
  ## do not. Each deeper depth is the model's input tag where the walk read
  ## that level's heap (an `of`, a down-conversion, a dispatch) and is
  ## unobserved, the sentinel, where it did not: a type no read names is
  ## one no test of the path told apart from the deepest one it did.
  let floorTy = b.floor.getOrDefault(cell.name, cell.pointee)
  let fc = hierChain(floorTy)
  if fc.len == 0: return
  for j in 1 ..< fc.len: result.add inheritTagCode(fc[j])
  var j = fc.len
  while true:
    let key = inheritTagKey(floorTy, j)
    if not currentVariantHeaps.hasKey(key): break
    var tmp: RawWitness
    extractLeaf(m, tmp, "t", heapSelect(cell.addrAst.ctx, inputHeap(key),
                                        cell.addrAst, tInt(64, signed = true)))
    let v = tmp.intVals.getOrDefault("t", 0)
    if v == 0: break
    result.add v
    inc j
  w.intVals[cell.name & ".@floor"] = int64(fc.len - 1)
  for i, v in result: w.intVals[cell.name & ".@lvl" & $(i + 1)] = v

proc renderCell*(b: var SnapshotBuild, m: Z3Model, w: var RawWitness,
                cell: RefPos): Option[string] =
  ## RFC-0005 S8h. Write `cell`'s leaves and return its `pointsTo`.
  let typeId = refPointeeTypeId(cell.pointee)
  # RFC-0016 INT-81: a hierarchy object's dynamic type (its tags).
  let lvls = cellDynamicType(b, m, w, cell)
  b.renderedLvls[cell.name] = lvls
  # RFC-0005 S8at: an anonymous tuple pointee is held whole (`isNew`'s
  # `anonTuple`), its elements the leaves `<cell>.Field<i>`.
  var anonTuple = false
  if cell.pointee.kind == itTuple and not cell.pointee.isPlaceholder:
    for fname in cell.pointee.fieldNames:
      if fname.len == 0: anonTuple = true
  if cell.pointee.kind notin {itTuple, itVariant, itMultiVariant} or anonTuple:   # RFC-0005 S8l: + MV
    # A scalar pointee (`ref int`) lives in the whole-pointee heap `<typeId>`.
    let valTy = block:
      let t = heapKeyValTy(typeId)
      if t != nil: t else: cell.pointee
    # RFC-0005 S8at: a tree pointee's first leaf is not at `<typeId>` itself
    # (`heapLeafSuffixes`); the observed test is of that leaf.
    if not currentVariantHeaps.hasKey(typeId & heapLeafSuffixes(valTy)[0]):
      return none(string)
    # RFC-0005 S8ap: a string or leaf-split compound pointee (`ref seq[int]`)
    # too, written at `<cell>` itself.
    if valTy.kind == itString or heapCompoundTy(valTy):
      return some(renderHeapCompound(b, m, w, typeId, cell.name,
                                     cell.addrAst, valTy))
    if valTy.kind notin {itInt, itBool, itFloat32, itFloat64}:
      return none(string)
    return some(renderHeapLeaf(m, w, typeId, cell.name, cell.addrAst, valTy))
  # An object or variant. The heaps materialised for this type, by suffix.
  let prefix = typeId & "__"
  var observed: seq[string]
  for key in currentVariantHeaps.keys:
    if key.len > prefix.len and key.startsWith(prefix):
      let suffix = key[prefix.len .. ^1]
      # A Nim identifier never contains `__`; a suffix that does belongs to
      # a different type whose id extends this one's. RFC-0005 S8ar: or is a
      # leaf of a tree-valued field, `<field>__@.<part>...`.
      let fieldPart = block:
        let at = suffix.find("__@.")
        if at > 0: suffix[0 ..< at] else: suffix
      if fieldPart[0] != '@' and "__" notin fieldPart and fieldPart notin observed:
        observed.add fieldPart
  sort(observed)
  var parts: seq[string]
  var done: seq[string]
  # The discriminator and the active branch of a variant. RFC-0005 S8l: of
  # each axis of a multi-variant (its `mvAxisView`s, one discriminator heap
  # each); a placeholder pointee (a recursive field's) learns its axes from
  # the discriminator heaps the path materialised.
  var axes: seq[tuple[discKey: string; variantTy: IRType]]
  if cell.pointee.kind == itVariant:
    axes.add (prefix & "@disc", cell.pointee)
  elif cell.pointee.kind == itMultiVariant:
    for ai in 0 ..< cell.pointee.mvAxes.len:
      let view = mvAxisView(cell.pointee, ai)
      axes.add (variantDiscHeapKey(view), view)
  else:
    var discKeys: seq[string]
    for key in heapKeyShapes.keys:
      if key.startsWith(prefix & "@disc") and heapKeyShapes[key].variantTy != nil and
         variantDiscHeapKey(heapKeyShapes[key].variantTy) == key:
        discKeys.add key
    sort(discKeys)
    for key in discKeys: axes.add (key, heapKeyShapes[key].variantTy)
  for (discKey, variantTy) in axes:
    if not currentVariantHeaps.hasKey(discKey): continue
    let discTy = block:
      let t = heapKeyValTy(discKey)
      if t != nil: t else: variantTy.vDiscTy
    let discSV = heapSelect(cell.addrAst.ctx, inputHeap(discKey), cell.addrAst,
                            discTy)
    let discPath = cell.name & "." & variantTy.vDiscName
    extractLeaf(m, w, discPath, discSV)
    parts.add variantTy.vDiscName & "=" & pointeeRendering(w, discPath).get("?")
    done.add variantTy.vDiscName
    let ord = evalDiscOrdinal(m, discSV)
    var active = -1
    for i, arm in variantTy.vArms:
      if not arm.isElse and int64(arm.tagOrdinal) == ord: active = i
    if active < 0:
      for i, arm in variantTy.vArms:
        if arm.isElse: active = i
    if active >= 0:
      let arm = variantTy.vArms[active]
      for j, fname in arm.fieldNames:
        let key = prefix & "@" & $arm.tagOrdinal & "__" & fname
        parts.add fname & "=" & renderCellField(b, m, w, cell, key, fname,
                                                arm.fieldTypes[j])
        done.add fname
  # Plain fields: in declaration order when the type is known, then any
  # other field the path materialised.
  let declared =
    if cell.pointee.kind == itTuple:
      if cell.pointee.isPlaceholder and cell.pointee.nominalId.len > 0 and
         heapWitnessNominalRegistry.hasKey(cell.pointee.nominalId):
        heapWitnessNominalRegistry[cell.pointee.nominalId]
      else: cell.pointee
    else: nil
  if declared != nil:
    for i, fname in declared.fieldNames:
      if fname.len == 0 or fname in done: continue
      # RFC-0005 S8bh: an inherited field lives in its declaring type's
      # heap (`fieldHeapKey`), not under this cell's root-keyed prefix.
      parts.add fname & "=" & renderCellField(b, m, w, cell,
                                              fieldHeapKey(declared, fname),
                                              fname, declared.fields[i])
      done.add fname
  elif cell.pointee.kind == itVariant:
    for i, fname in cell.pointee.vPlainFieldNames:
      if fname in done: continue
      parts.add fname & "=" & renderCellField(b, m, w, cell, prefix & fname,
        fname, cell.pointee.vPlainFieldTypes[i])
      done.add fname
  elif cell.pointee.kind == itMultiVariant:   # RFC-0005 S8l
    for i, fname in cell.pointee.mvPlainFieldNames:
      if fname in done: continue
      parts.add fname & "=" & renderCellField(b, m, w, cell, prefix & fname,
        fname, cell.pointee.mvPlainFieldTypes[i])
      done.add fname
  for fname in observed:
    if fname in done: continue
    parts.add fname & "=" & renderCellField(b, m, w, cell, prefix & fname,
                                            fname, nil)
    done.add fname
  # RFC-0016 INT-81. A field a type below the root declares keys on that
  # type (`fieldHeapKey`), outside this cell's prefix: each the walk read
  # whose declaring type is on the cell's dynamic chain.
  if lvls.len > 0:
    var owned: seq[string]
    for key, o in heapFieldOwners:
      if o.depth >= 1 and o.depth <= lvls.len and lvls[o.depth - 1] == o.code:
        owned.add key
    sort(owned)
    for key in owned:
      let fname = key[key.rfind("__") + 2 .. ^1]
      if fname in done: continue
      let r = renderCellField(b, m, w, cell, key, fname, nil)
      if r == "<unobserved>": continue
      parts.add fname & "=" & r
      done.add fname
  some("{" & parts.join(", ") & "}")

proc buildHeapSnapshot*(m: Z3Model, w: var RawWitness, env: Env,
                       params: seq[IRParam]): seq[HeapSnapshotEntry] =
  ## Phase 15 R12 (ADR-0010, witness-format-v3.md); Cluster H H_witness;
  ## RFC-0005 S8h (see the section comment above): every `ref`/`ptr`
  ## position of the input and every cell reachable from one, rendered from
  ## the model's INPUT heap. Empty when the input holds no ref or ptr.
  var top: seq[RefPos]
  for p in params:
    if env.hasKey(p.name): collectRefPositions(m, p.name, env[p.name], top)
  for pos in top: registerNominalIfFull(pos.pointee)
  var b: SnapshotBuild
  # R12: among bare params sharing an address, the lexicographically-first
  # name is the cell.
  var paramNames: seq[string]
  for p in params: paramNames.add p.name
  # RFC-0016 INT-88: one address held at two sorts (`addrSpaceKey`) is
  # owned by a `ref` (a managed object no raw allocation can stand in for),
  # else by a position of a sort the walk read or wrote (whose leaves the
  # cell is rendered from), and only then by name.
  var ownerRank: Table[string, int]
  for pos in top:
    if pos.name notin paramNames: continue
    let address = refAddrOf(m, pos.addrAst, pos.pointee)
    if address.len == 0: continue
    let rank = if pos.isRef: 0
               elif heapSortObserved(refPointeeTypeId(pos.pointee)): 1
               else: 2
    if not b.cellOf.hasKey(address) or rank < ownerRank[address] or
       (rank == ownerRank[address] and pos.name < b.cellOf[address]):
      b.cellOf[address] = pos.name
      ownerRank[address] = rank
  for pos in top:
    discard addPosition(b, m, pos, inlineNil = false)
  var i = 0
  while true:
    while i < b.queue.len:
      let cell = b.queue[i]
      let pointsTo = renderCell(b, m, w, cell)
      b.entries[b.entryOf[cell.name]].pointsTo = pointsTo
      inc i
    # RFC-0016 INT-81. A position found after its cell was rendered (a
    # field of a later cell) may be of a deeper static type, which deepens
    # the cell's dynamic type: such a cell is rendered again, for the fields
    # its deeper type declares (a position is recorded once, so its ref
    # fields add no entry twice).
    var again = false
    for k in 0 ..< b.queue.len:
      let cell = b.queue[k]
      var probe: RawWitness
      let lvls = cellDynamicType(b, m, probe, cell)
      if lvls != b.renderedLvls.getOrDefault(cell.name):
        b.entries[b.entryOf[cell.name]].pointsTo = renderCell(b, m, w, cell)
        again = true
    if not again and i >= b.queue.len: break
  renderCrossSortViews(b, m, w)   # RFC-0016 INT-90
  crossSortCellFidelity(b, w)   # RFC-0016 INT-88
  # RFC-0005 S8bh (item 2). A `ptr` cell whose input target (`sel`, see
  # `ptrTargets`) is a field of an object the snapshot holds as a cell
  # aliases that field: `aliasRef = "&<cell>.<field>"`, which the typed
  # witness resolves to the field's address (`resolveRef`). A target the
  # snapshot holds no cell for (a global, a `var` parameter, an object no
  # position reaches) keeps the pointer's own cell; the replay of such a
  # witness may then refute it (the pointer is not handed the location).
  for pos in b.queue:
    if not ptrScalarPointee(pos.pointee): continue
    let typeId = refPointeeTypeId(pos.pointee)
    let sk = ptrSelKey(typeId)
    if not currentVariantHeaps.hasKey(sk): continue
    let ctx = pos.addrAst.ctx
    let selV = $m.eval(wrap[Z3AnyAst](ctx, checkedSelect(ctx, inputHeap(sk).raw,
                                                         pos.addrAst.raw)))
    let prefix = ptrObjKey(typeId, "")
    var fams: seq[string]
    for key in currentVariantHeaps.keys:
      if key.startsWith(prefix): fams.add key[prefix.len .. ^1]
    sort(fams)
    var aimed = false
    for fam in fams:
      if not currentVariantHeaps.hasKey(fam): continue
      # RFC-0005 S8bn (item 4): an element of a seq held in the family.
      var seqCode = ptrTargetCode(fam & "/*")
      # RFC-0005 S8bz (item 1): or a part of its aggregate element.
      for code, la in ptrLeafAims:
        if la.fam == fam and la.seqIdx and la.typeId == typeId and
           la.elemSteps.len > 0 and ptrSelMatches(selV, code):
          seqCode = code
      let isSeqFam = ptrSelMatches(selV, seqCode) and
                     ptrLeafAims.hasKey(seqCode)
      var tabCode = ptrTargetCode(fam & "/#")
      for code, la in ptrLeafAims:   # RFC-0005 S8bz (item 2)
        if la.fam == fam and la.tabKey and la.typeId == typeId and
           la.elemSteps.len > 0 and ptrSelMatches(selV, code):
          tabCode = code
      let isTabFam = ptrSelMatches(selV, tabCode) and
                     ptrLeafAims.hasKey(tabCode)
      if not isSeqFam and not isTabFam and
         not ptrSelMatches(selV, ptrTargetCode(fam)): continue
      let objMap = inputHeap(ptrObjKey(typeId, fam))
      let objAddr = wrap[Z3AnyAst](ctx, checkedSelect(ctx, objMap.raw,
                                                      pos.addrAst.raw))
      let objSort = ctx.checkErr Z3_get_sort(ctx.raw, objAddr.raw)
      var oid = ""
      for tid, srt in currentRefSorts:
        if srt == objSort: oid = tid
      let address = addrSpaceKey(m, oid, $m.eval(objAddr))   # RFC-0016 INT-88
      # RFC-0005 S8bz (item 1): a by-value part's leaf heap
      # (`<O>__<f>__@.<part>`) is the field, then its parts.
      let leafAt = fam.find("__@.")
      let famBase = if leafAt >= 0: fam[0 ..< leafAt] else: fam
      let fsep = famBase.rfind("__")
      if oid.len > 0 and fsep >= 0 and b.cellOf.hasKey(address):
        var aim = "&" & b.cellOf[address] & "." & famBase[fsep + 2 .. ^1]
        if leafAt >= 0: aim.add fam[leafAt .. ^1].replace("__@.", ".")
        if isSeqFam:
          let ik = ptrIdxKey(typeId)
          if currentVariantHeaps.hasKey(ik):
            aim.add "." & $m.eval(wrap[Z3AnyAst](ctx, checkedSelect(ctx,
              inputHeap(ik).raw, pos.addrAst.raw)))
            for st in ptrLeafAims[seqCode].elemSteps: aim.add "." & st
          else: aim = ""
        elif isTabFam:
          let kk = ptrKeyKey(typeId)
          if currentVariantHeaps.hasKey(kk):
            aim.add "." & m.evalStrBytes(wrap[Z3String](ctx, checkedSelect(ctx,
              inputHeap(kk).raw, pos.addrAst.raw)))
            for st in ptrLeafAims[tabCode].elemSteps: aim.add "." & st
          else: aim = ""
        if aim.len > 0:
          b.entries[b.entryOf[pos.name]].aliasRef = some(aim)
      aimed = true
      break
    if aimed: continue
    # RFC-0005 S8bn (item 2). A target that is a variable -- a global, or a
    # `var` parameter of the SUT (`ptrTargets`' env candidates) -- has no
    # cell in the snapshot: the position is aimed at the variable by name
    # (`aliasRef = "@aim:<name>"`), and the replay's splat hands the
    # pointer that variable's address (`ptrAimsAt`, `emitWitnessSplat`).
    var names: seq[string]
    for p in params:
      if p.isVar: names.add p.name
    for k in currentWinningGlobals: names.add k
    sort(names)
    for nm in names:
      if ptrSelMatches(selV, ptrTargetCode(nm)):
        b.entries[b.entryOf[pos.name]].aliasRef = some(ptrAimPrefix & nm)
        aimed = true
        break
    if aimed: continue
    # RFC-0005 S8bn (item 4): a part of a variable -- a field, an array
    # element, a seq element (`@aim:<name>/<step>/.../<index>`).
    for code, la in ptrLeafAims:
      if la.fam.len > 0 or la.typeId != typeId: continue
      if la.name notin names or not ptrSelMatches(selV, code): continue
      var aim = ptrAimPrefix & la.name & ptrLeafPathStr(la.steps, false)
      if la.seqIdx:
        let ik = ptrIdxKey(typeId)
        if not currentVariantHeaps.hasKey(ik): break
        aim.add "/" & $m.eval(wrap[Z3AnyAst](ctx, checkedSelect(ctx,
          inputHeap(ik).raw, pos.addrAst.raw)))
      elif la.tabKey:
        # A table key: `k` and its bytes in hex (a key may hold a `/`).
        let kk = ptrKeyKey(typeId)
        if not currentVariantHeaps.hasKey(kk): break
        aim.add "/k" & toHex(m.evalStrBytes(wrap[Z3String](ctx, checkedSelect(
          ctx, inputHeap(kk).raw, pos.addrAst.raw))))
      aim.add ptrLeafPathStr(la.elemSteps, false)
      b.entries[b.entryOf[pos.name]].aliasRef = some(aim)
      break
  b.entries

proc extractWitness*(m: Z3Model, env: Env, params: seq[IRParam]): RawWitness =
  result.paramOrder = newSeq[string](params.len)
  for i, p in params:
    result.paramOrder[i] = p.name
    extractFromSymVal(m, result, p.name, env[p.name])
  # Phase 15 R12: the heap-snapshot witness. RFC-0005 S8h: it is also where
  # every cell's leaves are written (`<cell>.<field>`, `<cell>` for a scalar
  # pointee) -- the typed witness's `resolveRef` reads them there.
  result.heapSnapshot = buildHeapSnapshot(m, result, env, params)

proc modelPins*(m: Z3Model, env: Env, params: seq[IRParam]):
    tuple[pins: seq[Z3Bool], complete: bool] =
  ## RFC-0016 K10b. `RawWitness.pins`: `leaf == model(leaf)` for every leaf
  ## term of every parameter's initial value the model can evaluate. A
  ## parameter whose value does not fit its type's leaf split (a placeholder
  ## some upstream degrade left) or a leaf the model cannot evaluate is left
  ## free, which only widens what the second walk must show defined, and
  ## clears `complete`: a lossy winner is tail-checked only when it is set.
  result.complete = true
  # Building a leaf term may degrade in-band (`allocDegrade`: a compound value
  # with no single-leaf sort, say), which records into the lowering sinks the
  # verdict drains. A pin is not part of the program: its degrade must not
  # taint the explore verdict (`tsymex_r6_n13_reassign_seqarm`), it only leaves
  # the pins incomplete.
  let base = checkpoint()
  defer:
    if rollback(base):
      result.complete = false
  for p in params:
    if not env.hasKey(p.name):
      result.complete = false
      continue
    let sv = env[p.name]
    # A builtin set parameter is one bit-vector (`svBitSet`), which
    # `svFitsHeapTy` (a heap cell's fit test) does not name; its leaf is the
    # vector itself, so the witness pins it like any scalar.
    let bitSetParam = p.ty != nil and p.ty.kind == itBitSet and
                      sv.kind == svBitSet
    # A string-backed `seq[byte]` parameter (round-6 B1) is one Z3 String,
    # which `svFitsHeapTy` (a seq cell's data-array fit) does not name; its
    # leaf is the string itself. Left free, every branch on its bytes was
    # open under the pins: the tail walk asked each one twice at the
    # scratch-check cap and, since W3-z R6, forked it both ways, so a
    # pair-loop over the receiver multiplied capped checks past any test
    # bound (`tsymex_r6_b7r_bytescan` B7R-6, `tsymex_r6_b7r2_pathscope`
    # B7r2-1a).
    let stringBackedParam = p.isStringBacked and sv.kind == svString
    if not bitSetParam and not stringBackedParam and not svFitsHeapTy(sv, p.ty):
      result.complete = false
      continue
    var leaves: seq[Z3AnyAst]
    try:
      leaves = if bitSetParam or stringBackedParam:
                 @[wrap[Z3AnyAst](requireCurrentContext(), rawAnyAstOf(sv))]
               else: svLeafTerms(sv, p.ty, pinForm = true)
    except CatchableError:
      result.complete = false
      continue
    for leaf in leaves:
      try:
        result.pins.add bsEqZ(leaf, m.eval(leaf))
      except CatchableError:
        result.complete = false
  # Each ref sort's `nil` constant. A pinned ref leaf (`p == Ref!val!0`) says
  # nothing of `p != nil` unless `nil` is pinned too: the tail walk's
  # `p != nil` read as undecided. A `nil` the explore model never mentions is
  # unconstrained, so any value is consistent with the witness and it is
  # pinned by model completion, as the mentioned ones are (the witness reader
  # completes the same way, so a ref parameter's own nil-ness agrees with the
  # replay). Only a constant the model cannot evaluate at all stays free.
  for tid, nc in currentNilConsts:
    try:
      let v = m.eval(nc)
      if $v != $nc: result.pins.add bsEqZ(nc, v)
    except CatchableError:
      discard
  # The parameters' heaps. A ref parameter's pointee fields are cells of the
  # run's free `heap_*` arrays, not leaves of the parameter's value, so a
  # branch on `p.v` read as undecided under the pins. Each free heap array
  # the model interprets is pinned whole (an array equality over the model's
  # own store term). Only the initial arrays are constants: a write the walk
  # makes is a `store` over them and follows from them.
  # RFC-0016 0.10.0 review H3: only the INPUT array `heap_<k>`. An opaque
  # call's havoc epoch `heap_<k>@ep<n>` (`havocOpaqueHeaps`) is a constant
  # too, but it is what a callee the walk does not model left in the heap,
  # not an input: the tail walk recreates the same-named constant, so a pin
  # on it fixed the callee's effect to the explore model's choice, and a tail
  # the real callee drives into undefined behaviour read as defined. Left
  # free it is a superset of what the callee writes, as on the explore walk.
  # Driven from the heaps the walk created, not from every model constant:
  # enumerating the model's declarations (`constDecl` per constant) kept the
  # run's whole Z3 context alive past the run (`tsymex_0016_s8cj_runctx`).
  for k in currentVariantHeaps.keys:
    try:
      let c = inputHeapNamed(k, "heap_" & k)
      let v = m.eval(c, modelCompletion = false)
      if $v != $c: result.pins.add bsEqZ(c, v)
    except CatchableError:
      result.complete = false

var symexTargetSolveStats* {.threadvar.}:
    tuple[budgetOut, declined, slowSat, units: int]
  ## RFC-0005 S8y. `solveTargetHit`'s own tally, never reset by the engine
  ## (tests reset it around a measured run): `budgetOut` counts target-hit
  ## solves, clean or tainted, that ran out of their budget; `declined`
  ## counts tainted hits declined unsolved because an earlier tainted hit
  ## at most as deep had run out. RFC-0005 S8ag: `slowSat` counts tainted
  ## hits whose model was found only after at least half their budget was
  ## spent (`checkCapped`'s capped step 1 ran out and the uncapped step 3
  ## found one), which bound later hits as a budget-out does; `units` is
  ## the `rlimit` every target-hit solve spent. Deterministic, like the
  ## `rlimit` it is read from.

var ownContextUnits* {.threadvar.}: int
  ## RFC-0005 S8bm. The Z3 units every search spent in a context of its
  ## own (`ownContextSolver`), running total for the thread. RFC-0005
  ## S8bp: that is every `checkCapped` search, so a walker query's spend
  ## (`solveTargetHit`, `recordQueryStat`) is what this total grew by; the
  ## walk context's `rlimit count` sees none of it.

var symexZ3CallCount* {.threadvar.}: int
  ## Phase 13 cycle 1. Increments on every Z3 `s.check()` invocation
  ## inside symex. Always-on (no compile-time gate) — the increment
  ## cost is negligible against a Z3 query and tests observe it to
  ## assert "cache hit, Z3 not called" contracts. Re-exported by
  ## `nelli/symex` so consumers can `import nelli/symex` and
  ## reach it directly.

when defined(symexQueryStats):
  ## N45 instrumentation (RFC-0001). OFF unless `-d:symexQueryStats`.
  ##
  ## Deliberately gated: N45 is an investigation INTO per-query cost, so
  ## measuring it must not itself add per-query cost to ordinary runs.
  ##
  ## Why not wall-clock: whole-file wall time carries a ~19s compile floor
  ## that buries this engine's per-query cost on Linux entirely (measured
  ## 2026-08-31 -- a 2x2 over walker version x dep set landed inside noise).
  ## `rlimit` is Z3's own deterministic logical-step count: machine- and
  ## load-independent, so it is comparable across a bisect in a way seconds
  ## are not. `trySolve`'s own comment already relies on that property to
  ## make verdicts reproducible; this reads the counter instead of bounding
  ## it.
  ##
  ## The point is to make N45's two hypotheses DISCRIMINABLE:
  ##   * assertion/query counts up  -> the WALKER is generating more work
  ##   * counts flat, rlimit up     -> the SOLVER is doing more per query
  ## Wall time cannot separate those; this can.
  type SymexQueryStat* = object
    assertions*:   int     ## constraints handed to this solver instance
    rlimit*:       int     ## Z3's step count after the check, cumulative
                           ## over every walker query of the thread
                           ## (RFC-0005 S8ac; S8bp: `ownContextUnits`,
                           ## every query's searches being in contexts of
                           ## their own), not this query's cost -- that
                           ## is `rlimitDelta`.
    rlimitDelta*:  int     ## RFC-0005 S8ac: the steps THIS query spent,
                           ## every solver `checkCapped` ran for it
                           ## included (deterministic).
    conflicts*:    int
    decisions*:    int
    propagations*: int
    memoryMb*:     float
    status*:       string
    query*:        string  ## the answering solver's assertions, SMT-LIB
                           ## text (RFC-0005 S8w2: pins a query's SHAPE,
                           ## which no verdict shows)

  var symexQueryStats* {.threadvar.}: seq[SymexQueryStat]
  var symexQueryStatsPaused* {.threadvar.}: bool
    ## RFC-0005 S8ac. While set, `trySolve` neither reads the step counter
    ## nor records a stat, so a walk runs exactly as in a build without
    ## `-d:symexQueryStats`. A suite compares a walk with it set against
    ## the same walk recorded, to pin that the measurement leaves Z3's
    ## search alone.
    ## One entry per `check()`, in call order. Reset it yourself before a
    ## measured region -- nothing clears it implicitly.
  var symexFactsFirstOff* {.threadvar.}: bool
    ## RFC-0005 S8bm. While set, `checkCapped` skips its facts-first check
    ## (RFC-0005 S8ay), so a suite can walk a program with and without it
    ## and pin that step 1's search does not depend on it
    ## (`tsymex_rfc0005_s8bm_stability`). Only in this instrumented build.
  type SymexStepStat* = object
    ## RFC-0005 S8bp. One `checkCapped` step's search: which step
    ## (`"plain"`, `"factsFirst"`, `"1"`, `"1b"`, `"1c"`, `"1c-capped"`,
    ## `"2"`, `"3"`), its answer, and the Z3 units its check spent.
    step*:   string
    status*: string
    units*:  int
  var symexStepStats* {.threadvar.}: seq[SymexStepStat]
    ## RFC-0005 S8bp. Every `checkCapped` step's search, in call order.
    ## Reset it yourself before a measured region.
  var symexPerturbConsts* {.threadvar.}: int
    ## RFC-0005 S8bp. While positive, `checkCapped` first makes that many
    ## fresh Int constants, which no query mentions, in the walk's context:
    ## unrelated walk state (S8bm's probe, which moved a step-1 search
    ## 30x). A suite walks a program with and without it and pins that no
    ## step's search moves (`tsymex_rfc0005_s8bp_isolation`).
  var perturbSerial* {.threadvar.}: int

  proc statInt*(st: Z3Stats, key: string): int =
    ## Z3 omits keys it has nothing to say about (a trivially-unsat query
    ## reports no conflicts), so every read is guarded. Absent reads 0.
    if st.contains(key):
      if st.isInt(key): st.getInt(key) else: int(st.getFloat(key))
    else: 0

  proc recordQueryStat*(s: Z3Solver, nAsserts: int, status: string,
                       unitsBefore: int) =
    ## Called immediately after `check()`. Statistics are valid for
    ## sat/unsat/UNKNOWN alike -- the truncated-by-rlimit case is precisely
    ## the one N45 cares about (B5-4's trip-wire query), so it must not be
    ## skipped. RFC-0005 S8bp: every search `checkCapped` runs is in a
    ## context of its own, its units added to `ownContextUnits`, so the
    ## query's units are what that total grew by since `unitsBefore`, read
    ## when `trySolve` began the query. (S8ac read the walk context's
    ## counter from the query's first solver, built there; none is now.)
    let st = s.getStatistics()
    symexQueryStats.add SymexQueryStat(
      assertions:   nAsserts,
      rlimit:       ownContextUnits,
      rlimitDelta:  ownContextUnits - unitsBefore,
      conflicts:    statInt(st, "conflicts"),
      decisions:    statInt(st, "decisions"),
      propagations: statInt(st, "propagations"),
      memoryMb:     (if st.contains("memory"): st.getFloat("memory") else: 0.0),
      status:       status,
      query:        $s)

  proc symexQueryStatsSummary*(): string =
    ## Compact, greppable one-liner per query plus a total -- the shape a
    ## `git bisect run` script wants to threshold on.
    var totR, totA, totD = 0
    result = ""
    for i, q in symexQueryStats:
      result.add "  q" & $i & " " & q.status & " asserts=" & $q.assertions &
                 " rlimit=" & $q.rlimit & " drlimit=" & $q.rlimitDelta &
                 " conflicts=" & $q.conflicts &
                 " decisions=" & $q.decisions & " props=" & $q.propagations &
                 " memMB=" & $q.memoryMb & "\n"
      totR += q.rlimit
      totD += q.rlimitDelta
      totA += q.assertions
    result.add "  TOTAL queries=" & $symexQueryStats.len &
               " asserts=" & $totA & " rlimit=" & $totR &
               " drlimit=" & $totD & "\n"

  proc symexQueryStatsTotals*(): tuple[queries, asserts, rlimit,
                                       rlimitDelta: int] =
    ## The numbers a bisect thresholds on, without parsing prose.
    ## `rlimitDelta` (RFC-0005 S8ac) is the walk's real step total;
    ## `rlimit` sums the cumulative counter and over-counts.
    for q in symexQueryStats:
      result.queries += 1
      result.asserts += q.assertions
      result.rlimit  += q.rlimit
      result.rlimitDelta += q.rlimitDelta

  import std/exitprocs
  addExitProc(proc() =
    ## Dump at process exit so ANY suite compiled with -d:symexQueryStats
    ## reports its totals without being edited. That is what makes this
    ## usable as a `git bisect run` oracle: compile the one suite under
    ## test, grep one line, threshold it. Editing each revision's tests
    ## mid-bisect would defeat the purpose.
    let t = symexQueryStatsTotals()
    if t.queries > 0:
      echo "N45STATS queries=", t.queries, " asserts=", t.asserts,
           " rlimit=", t.rlimit, " drlimit=", t.rlimitDelta)

# ---- RFC-0005 S8k: the per-term seq length cap (`maxSeqLen`) ---------------
#
# Z3's sequence solver explores string / seq lengths upward, and past ~100
# elements each step's work grows super-linearly; past ~250 a single step
# can run for minutes without polling the resource counter, so neither
# `rlimit` nor a wall-clock `timeout` bounds it (measured, see
# `ResourceBudget.maxSeqLen`). Every walker query with a string / seq leaf
# is therefore solved with each such leaf capped at `maxSeqLen` elements
# (`checkCapped`). Under the cap the counter IS polled, but slowly, so such
# a query also runs under `seqQueryRLimit`. Deterministic: no wall clock is
# consulted anywhere.


var seqCapDeclKinds* {.threadvar.}: tuple[ready: bool, k: SeqCapKinds]
  ## Read off terms built once per thread: the wrapper's `Z3DeclKindFFI`
  ## binds only the proof-rule subset of the C enum, and the header's values
  ## are positional, so they are taken from the linked Z3 itself rather
  ## than restated here.

proc seqCapKinds*(): SeqCapKinds =
  if not seqCapDeclKinds.ready:
    let ctx = probeContext()   # RFC-0005 S8bp
    proc kindOf(ctx: Z3Context; a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
    let c = mkIntVar(ctx, "__s8k_kind_probe")
    let arr = mkArrayVar[Z3Int, Z3Int](ctx, "__s8k_kind_probe_arr")
    let str = mkStringVar(ctx, "__s8o_kind_probe_str")
    let ch = at(str, c)
    # RFC-0005 S8ai: the regex constructors, over the string regex sort.
    let lit = mkString(ctx, "a")
    let reA = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_seq_to_re(ctx.raw, lit.raw))
    let reR = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_re_range(ctx.raw, lit.raw,
                                                               lit.raw))
    var rePair = [reA.raw, reR.raw]
    template reN(mk: untyped): int =
      kindOf(ctx, ctx.checkErr mk(ctx.raw, 2,
        cast[ptr UncheckedArray[RawZ3Ast]](rePair[0].addr)))
    let replaceProbe = parseSmt2String(ctx,
      "(declare-const __s8ai_kind_probe_str String)" &
      "(assert (= __s8ai_kind_probe_str (str.replace_all " &
      "__s8ai_kind_probe_str __s8ai_kind_probe_str __s8ai_kind_probe_str)))")
    let replaceAllTerm = Z3_get_app_arg(ctx.raw,
      Z3_to_app(ctx.raw, replaceProbe[0].raw), 1)
    var k = SeqCapKinds(
      strConcat:     kindOf(ctx, (str & str).raw),
      strFromInt:    kindOf(ctx, toStr(c).raw),
      strReplaceAll: kindOf(ctx, replaceAllTerm),
      reToRe:    kindOf(ctx, reA.raw),
      reRange:   kindOf(ctx, reR.raw),
      reConcat:  reN(Z3_mk_re_concat),
      reUnion:   reN(Z3_mk_re_union),
      reInter:   reN(Z3_mk_re_intersect),
      rePlus:    kindOf(ctx, ctx.checkErr Z3_mk_re_plus(ctx.raw, reA.raw)),
      reOpt:     kindOf(ctx, ctx.checkErr Z3_mk_re_option(ctx.raw, reA.raw)),
      reLoop:    kindOf(ctx, ctx.checkErr Z3_mk_re_loop(ctx.raw, reA.raw, 1, 2)),
      rePower:   kindOf(ctx, ctx.checkErr Z3_mk_re_power(ctx.raw, reA.raw, 2)),
      reAllChar: kindOf(ctx, ctx.checkErr Z3_mk_re_allchar(ctx.raw,
                   Z3_get_sort(ctx.raw, reA.raw))),   # CRH-07: the sort of the live `reA`
      uninterp: kindOf(ctx, c.raw),
      select:   kindOf(ctx, select(arr, mkInt(ctx, 0)).raw),
      int2bv:   kindOf(ctx, intToBv[8](c, Z3BitVec[8]).raw),
      toCode:   kindOf(ctx, toCode(ch).raw),
      strAt:    kindOf(ctx, ch.raw),
      inRe:     kindOf(ctx, matches(str, star(range(mkString(ctx, "\x00"),
                                                   mkString(ctx, "\xff")))).raw),
      strLen:   kindOf(ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, str.raw)),
      strIndex: kindOf(ctx, ctx.checkErr Z3_mk_seq_index(ctx.raw, str.raw,
                                                         str.raw, c.raw)),
      strExtract:  kindOf(ctx, substr(str, c, c).raw),
      strToInt:    kindOf(ctx, toInt(str).raw),
      strContains: kindOf(ctx, contains(str, ch).raw),
      strPrefix:   kindOf(ctx, startsWith(str, ch).raw),
      strSuffix:   kindOf(ctx, endsWith(str, ch).raw),
      strFromCode: kindOf(ctx, ctx.checkErr Z3_mk_string_from_code(ctx.raw,
                                                                   c.raw)),
      iteK:        kindOf(ctx, checkedIte(ctx, (c == c).raw, str.raw,
                                          str.raw)))
    # RFC-0005 S8ai: disable an S8ai kind that is not unique. A power that
    # shares the loop's ordinal is read by the loop arm (`regexLenBounds`),
    # so only the power is dropped.
    if k.rePower == k.reLoop: k.rePower = -2
    let lastIndexKind = kindOf(ctx, ctx.checkErr Z3_mk_seq_last_index(ctx.raw,
                                                  str.raw, str.raw))
    let all = [k.uninterp, k.select, k.int2bv, k.toCode, k.strAt, k.inRe,
               k.strLen, k.strIndex, k.strExtract, k.strToInt, k.strContains,
               k.strPrefix, k.strSuffix, lastIndexKind, k.strConcat,
               k.strFromInt, k.strReplaceAll, k.reToRe, k.reRange, k.reConcat,
               k.reUnion, k.reInter, k.rePlus, k.reOpt, k.reLoop, k.rePower,
               k.reAllChar, k.strFromCode, k.iteK]
    template unique(f: untyped) =
      var uses = 0
      for a in all:
        if a == f: inc uses
      if uses > 1: f = -2
    unique(k.strConcat)
    unique(k.strFromInt)
    unique(k.strReplaceAll)
    unique(k.reToRe)
    unique(k.reRange)
    unique(k.reConcat)
    unique(k.reUnion)
    unique(k.reInter)
    unique(k.rePlus)
    unique(k.reOpt)
    unique(k.reLoop)
    if k.rePower != -2: unique(k.rePower)
    unique(k.reAllChar)
    unique(k.strFromCode)
    unique(k.iteK)
    seqCapDeclKinds = (ready: true, k: k)
  seqCapDeclKinds.k

const maxLenBoundFacts* = 64
  ## RFC-0016 INT-61. The most `str.len` terms `seqLenBoundFacts` bounds in
  ## one query.

proc seqLenBoundFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0016 INT-61. For every `str.len(x)` in `roots` whose argument has a
  ## length bound its own structure gives, `str.len(x) <= n`:
  ##   - a literal: its length;
  ##   - `str.from_code(k)`, `str.at(s, i)`: 1;
  ##   - `str.++(a, b, ...)`: the sum of the parts' bounds;
  ##   - `str.substr(s, i, n)`: `s`'s bound;
  ##   - `ite(c, a, b)`: the larger of the arms' bounds.
  ## Anything else (an input, a `select`, `str.from_int`) has none, and a
  ## term with an unbounded part gets no fact. Each holds in every model of
  ## the sequence theory, so the query's models are its own (as
  ## `bitSetCardFacts`'). They are what the arithmetic around a length
  ## lacks: an `int` addition's overflow side over `len($chr(t + 128))`
  ## asks whether `str.len(str.from_code(k))` leaves the `int` range, which
  ## Z3's sequence solver did not refute in 12.4M units (`sxUnknown`, about
  ## 25 s on c); with `<= 1` beside it the arithmetic refutes it at once.
  let kinds = seqCapKinds()
  var memo = initTable[int, int]()   # ast id -> bound, -1 none
  proc bound(t: RawZ3Ast; depth: int): int =
    let id = astId(ctx, t)
    if id in memo: return memo[id]
    result = -1
    chargeWalkerTerms(1)
    if Z3_is_string(ctx.raw, t):
      result = int(Z3_get_string_length(ctx.raw, t))
    elif depth < 32 and Z3_get_ast_kind(ctx.raw, t) == Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, t)
      let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app)))
      let n = int(Z3_get_app_num_args(ctx.raw, app))
      template arg(i: int): RawZ3Ast = Z3_get_app_arg(ctx.raw, app, cuint(i))
      if k == kinds.strFromCode or k == kinds.strAt:
        result = 1
      elif k == kinds.strConcat:
        var sum = 0
        for i in 0 ..< n:
          let b = bound(arg(i), depth + 1)
          if b < 0: (sum = -1; break)
          sum += b
        result = sum
      elif k == kinds.strExtract and n == 3:
        result = bound(arg(0), depth + 1)
      elif k == kinds.iteK and n == 3:
        let x = bound(arg(1), depth + 1)
        let y = bound(arg(2), depth + 1)
        if x >= 0 and y >= 0: result = max(x, y)
    memo[id] = result
  var seen: HashSet[int]
  var stack: seq[RawZ3Ast]
  for r in roots: stack.add r.raw
  while stack.len > 0 and result.len < maxLenBoundFacts:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, t)
    let n = int(Z3_get_app_num_args(ctx.raw, app))
    if n == 1 and ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw,
        app))) == kinds.strLen:
      let x = Z3_get_app_arg(ctx.raw, app, 0)
      let b = bound(x, 0)
      if b >= 0 and not Z3_is_string(ctx.raw, x):
        result.add wrap[Z3Int](ctx, t) <= mkInt(ctx, b)
    for i in 0 ..< n:
      stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))


proc cNextAfter*(x, y: cdouble): cdouble {.importc: "nextafter",
                                           header: "<math.h>".}
  ## RFC-0016 INT-59: C99's `nextafter` (`fpIntervalRefutes` widens by it).

var fpIntervalDeclKinds* {.threadvar.}: tuple[ready: bool, k: FpIntervalKinds]

proc fpIntervalKinds*(): FpIntervalKinds =
  ## Each kind is read off a term built through the C API in a probe
  ## context, every operand held by a wrapper. (A first version built
  ## them from bare handles: in a reference-counted context Z3 keeps an
  ## unreferenced result only until the next API call, so the bit-vector
  ## operand of `Z3_mk_fpa_to_fp_signed` was already freed when it ran,
  ## Z3 rejected the call ("rm and float sorts expected") and the null it
  ## returned crashed `Z3_get_app_decl`. The binding is right.)
  if not fpIntervalDeclKinds.ready:
    let ctx = probeContext()
    let c = ctx.raw
    template held(x: RawZ3Ast): Z3AnyAst = wrap[Z3AnyAst](ctx, ctx.checkErr x)
    proc kindOf(a: Z3AnyAst): int =
      ord(Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, a.raw))))
    let v = mkBitVec[8](ctx, 3)
    let rm = rmRTZ(ctx)
    let x = toFpFromSigned(rm, v, Z3Float64)
    let y = toFpFromUnsigned(rm, v, Z3Float64)
    let lt = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_fpa_lt(c, x.raw, y.raw))
    let gt = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_fpa_gt(c, x.raw, y.raw))
    var k = FpIntervalKinds(
      toFpS: kindOf(held x.raw), toFpU: kindOf(held y.raw),
      fdiv: kindOf(held Z3_mk_fpa_div(c, rm.raw, x.raw, y.raw)),
      fmul: kindOf(held Z3_mk_fpa_mul(c, rm.raw, x.raw, y.raw)),
      fadd: kindOf(held Z3_mk_fpa_add(c, rm.raw, x.raw, y.raw)),
      fsub: kindOf(held Z3_mk_fpa_sub(c, rm.raw, x.raw, y.raw)),
      fneg: kindOf(held Z3_mk_fpa_neg(c, x.raw)),
      rti: kindOf(held Z3_mk_fpa_round_to_integral(c, rm.raw, x.raw)),
      leq: kindOf(held Z3_mk_fpa_leq(c, x.raw, y.raw)),
      lt: kindOf(held lt.raw),
      geq: kindOf(held Z3_mk_fpa_geq(c, x.raw, y.raw)),
      gt: kindOf(held gt.raw),
      sext: kindOf(held Z3_mk_sign_ext(c, 8, v.raw)),
      zext: kindOf(held Z3_mk_zero_ext(c, 8, v.raw)),
      notK: kindOf(held (not lt).raw),
      andK: kindOf(held (lt and gt).raw),
      orK: kindOf(held (lt or gt).raw))
    let all = [k.toFpS, k.toFpU, k.fdiv, k.fmul, k.fadd, k.fsub, k.fneg,
               k.rti, k.leq, k.lt, k.geq, k.gt, k.sext, k.zext, k.notK,
               k.andK, k.orK]
    k.ok = true
    for i in 0 ..< all.len:
      for j in i + 1 ..< all.len:
        if all[i] == all[j]: k.ok = false
    fpIntervalDeclKinds = (ready: true, k: k)
  fpIntervalDeclKinds.k

const fpIntervalMagnitude* = 1e300
  ## RFC-0016 INT-59. The largest bound `fpIntervalRefutes` keeps: far
  ## enough below `high(float64)` (about 1.8e308) that one ulp of
  ## widening and the rounding of a bounded result never reach infinity.
var fpUnderflowProbe* {.volatile.} = 2.2250738585072014e-308
  ## RFC-0016 INT-59: the least positive normal `float64`, read at run time
  ## (`volatile`, so the C compiler cannot fold the probe below).

proc hostGradualUnderflow*(): bool =
  ## Whether this thread's `float64` arithmetic underflows gradually (IEEE
  ## 754): neither flushes a subnormal result to zero (FTZ) nor reads a
  ## subnormal operand as zero (DAZ). A process built with `-ffast-math`
  ## (`crtfastmath`) sets both, and the one-ulp argument of
  ## `fpIntervalRefutes` assumes neither.
  let m = fpUnderflowProbe
  let half = m / 2.0                     # subnormal; 0 under FTZ
  half != 0.0 and half * 2.0 == m        # the operand read as 0 under DAZ

proc fpIntervalRefutes*(ctx: Z3Context; roots: openArray[Z3Bool]): bool =
  ## RFC-0016 INT-59. Whether an interval argument shows some root of
  ## `roots` false, so the query is UNSAT without a solve (`checkExact`
  ## then asks `false`). What it is for: the range check of a float-to-int
  ## conversion (`decideUndefined`'s `ubFloatToIntRange` side, `not (f > lo
  ## - 1 and f < hi + 1)`) over `int(trunc(float(t) / 3.0))`; Z3 refuted it
  ## only by bit-blasting the division (11.6M units, twice a walk), and a
  ## fact `lo <= x <= hi` beside the query did not shorten that (10.6M).
  ##
  ## Shapes. Only `Float64` terms (11 exponent, 53 significand bits) get an
  ## interval `[lo, hi]` of reals, each bound a finite `float64` in
  ## `[-1e300, 1e300]`:
  ##   - `to_fp`/`to_fp_unsigned` of a bit-vector of width <= 64 under any
  ##     rounding mode: the integer range of its width (a sign extension
  ##     under a signed conversion, or a zero extension that adds bits,
  ##     narrows it to the operand's);
  ##   - a numeral that is neither NaN nor infinite;
  ##   - `fp.neg`, `fp.roundToIntegral`, `fp.add`, `fp.sub`, `fp.mul`, and
  ##     `fp.div` whose divisor's interval excludes zero, over bounded
  ##     operands, under any rounding mode.
  ## Anything else (a variable, `ite`, `sqrt`, a bit-pattern `to_fp`, another
  ## sort) gets none, and so does everything above it. Truth is three-valued
  ## over `fp.leq/lt/geq/gt` of two bounded terms, `not`, `and`, `or`; a root
  ## evaluated false refutes. Every other connective is undecided.
  ##
  ## Soundness: claim (I) every value the term takes in any model is a
  ## finite float (not NaN, not infinite) whose real value lies in `[lo,
  ## hi]`. By induction on the term:
  ##   - Conversion: for any of the five rounding modes, the result of
  ##     rounding an integer `v` lies between `RD(v)` and `RU(v)` (round
  ##     down / up), and rounding is monotone, so the result is in
  ##     `[RD(min), RU(max)]` of the integer range; `|v| <= 2^64` never
  ##     overflows.
  ##   - Numeral: its real value (`fp.to_real`, simplified to a rational)
  ##     converted to `float64` and checked by rebuilding the numeral from
  ##     that double: the same term (hash-consed, one id) is the same value,
  ##     so the conversion lost
  ##     nothing (a subnormal's rational, whose denominator exceeds the
  ##     double range, fails that check and gets no interval). A zero is
  ##     taken as `[0, 0]` either sign: `-0` and `+0` are the real 0.
  ##   - `+ - * /`: the exact real result `e` of operands in their intervals
  ##     is monotone in each operand separately (`*` is linear in each;
  ##     `/` is too, its divisor's sign fixed by an interval that excludes
  ##     zero), so it is bounded by the four corner values; each corner
  ##     computed in `float64` is that corner rounded to nearest, and
  ##     rounding is monotone, so the least computed corner is `RN(emin)`.
  ##     Any rounding mode gives `RD(e) <= result <= RU(e)`, and `RD(emin)
  ##     >= nextafter(RN(emin), -inf)` (if `emin` is not representable
  ##     `RN` is one of its two neighbours `RD`, `RU`, and the step below
  ##     `RU` is `RD`; if it is, all three agree). Symmetrically above. So
  ##     widening the computed bounds one ulp outward contains every
  ##     rounding mode's result. Division by an interval holding zero (or
  ##     a zero of either sign) is refused, so `x/0` (an infinity or NaN)
  ##     never arises; finite operands and a nonzero divisor give no NaN
  ##     (`inf - inf`, `0 * inf`, `0/0`, `inf/inf` need an infinite or zero
  ##     operand).
  ##   - `fp.neg` is exact; `fp.roundToIntegral` under any mode returns
  ##     `floor(x)` or `ceil(x)`, in `[floor(lo), ceil(hi)]`.
  ##   - Overflow: a bound past `1e300` is refused (as is a NaN or infinite
  ##     computed bound). A result within one ulp of a bound under `1e300`
  ##     is finite, so no operation over bounded operands overflows to
  ##     infinity.
  ##   - Subnormals: the bounds are computed in the host's `float64`, which
  ##     must be IEEE 754 with gradual underflow for the one-ulp argument
  ##     (a subnormal result is still correctly rounded, one subnormal ulp
  ##     from the exact value). A thread that flushes subnormals to zero or
  ##     reads them as zero (`-ffast-math`) is detected at the call
  ##     (`hostGradualUnderflow`) and gets no refutation.
  ##   - Exact bounds are not widened: a numeral's value, a conversion of a
  ##     bit-vector of width <= 53 (every integer of its range is a
  ##     `float64`, so `RD` and `RU` of a bound are the bound), `fp.neg`'s
  ##     negation and `fp.roundToIntegral`'s `floor`/`ceil`.
  ##   - The rounding-mode argument is never read: the bounds hold for all
  ##     five modes, so a symbolic mode is covered too.
  ## Claim (II), the comparisons: `fp.leq(a, b)` is true iff neither is NaN
  ## and `a <= b` as reals (`-0 = +0`); by (I) neither is NaN, so `a.hi <=
  ## b.lo` makes it true and `a.lo > b.hi` false in every model (`fp.lt`
  ## with `<` and `>=`; `geq`/`gt` swapped). `not`, `and`, `or` combine
  ## decided parts by their truth tables and leave the rest undecided. A
  ## root decided false holds in no model, so the conjunction of `roots` is
  ## UNSAT: the answer is the query's own. Pinned differentially against
  ## Z3 by `tsymex_0016_int59_fpinterval`.
  let k = fpIntervalKinds()
  if not k.ok or not hostGradualUnderflow(): return false
  let c = ctx.raw
  var memo = initTable[int, tuple[ok: bool, lo, hi: float64]]()
  proc exact(a, b: float64): tuple[ok: bool, lo, hi: float64] =
    # Written so a NaN bound fails too.
    if a >= -fpIntervalMagnitude and b <= fpIntervalMagnitude and a <= b:
      (true, a, b)
    else: (false, 0.0, 0.0)
  proc widen(lo, hi: float64): tuple[ok: bool, lo, hi: float64] =
    exact(float64(cNextAfter(lo, NegInf)), float64(cNextAfter(hi, Inf)))
  proc isDouble(t: RawZ3Ast): bool =
    let so = Z3_get_sort(c, t)
    Z3_get_sort_kind(c, so) == Z3_FLOATING_POINT_SORT and
      Z3_fpa_get_ebits(c, so) == 11 and Z3_fpa_get_sbits(c, so) == 53
  proc bvRange(t: RawZ3Ast; signed: bool): tuple[ok: bool, lo, hi: float64] =
    var w = int(Z3_get_bv_sort_size(c, Z3_get_sort(c, t)))
    var sgn = signed
    if Z3_get_ast_kind(c, t) == Z3_APP_AST:
      let app = Z3_to_app(c, t)
      let kd = ord(Z3_get_decl_kind(c, Z3_get_app_decl(c, app)))
      if Z3_get_app_num_args(c, app) == 1 and (kd == k.sext or kd == k.zext):
        let inner = Z3_get_app_arg(c, app, 0)
        let iw = int(Z3_get_bv_sort_size(c, Z3_get_sort(c, inner)))
        # A zero extension by 0 bits is the operand itself, read signed by
        # a signed conversion: it narrows only when it adds a bit.
        if kd == k.zext and iw < w: (w = iw; sgn = false)
        elif kd == k.sext and signed: w = iw
    if w < 1 or w > 64: return (false, 0.0, 0.0)
    let (lo, hi) = if sgn: (-pow(2.0, float64(w - 1)), pow(2.0, float64(w - 1)) - 1.0)
                   else: (0.0, pow(2.0, float64(w)) - 1.0)
    if w <= 53: exact(lo, hi) else: widen(lo, hi)
  proc iv(t: RawZ3Ast; depth: int): tuple[ok: bool, lo, hi: float64] =
    let id = astId(ctx, t)
    if id in memo: return memo[id]
    result = (false, 0.0, 0.0)
    chargeWalkerTerms(1)
    if depth < 24 and Z3_get_ast_kind(c, t) == Z3_APP_AST and isDouble(t):
      let app = Z3_to_app(c, t)
      let kd = ord(Z3_get_decl_kind(c, Z3_get_app_decl(c, app)))
      let n = int(Z3_get_app_num_args(c, app))
      template arg(i: int): RawZ3Ast = Z3_get_app_arg(c, app, cuint(i))
      if n == 0:
        # A numeral (an uninterpreted constant's real value is not a
        # numeral, so it gets none).
        if Z3_is_numeral_ast(c, t) and not Z3_fpa_is_numeral_nan(c, t) and
           not Z3_fpa_is_numeral_inf(c, t):
          let real = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_fpa_to_real(c, t))
          let r = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_simplify(c, real.raw))
          if Z3_get_ast_kind(c, r.raw) == Z3_NUMERAL_AST:
            let v = float64(Z3_get_numeral_double(c, r.raw))
            if v == 0.0:
              if Z3_fpa_is_numeral_zero(c, t): result = exact(0.0, 0.0)
            elif v == v:
              let back = wrap[Z3AnyAst](ctx, ctx.checkErr(
                Z3_mk_fpa_numeral_double(c, cdouble(v), Z3_get_sort(c, t))))
              if astId(ctx, back.raw) == id: result = exact(v, v)
      elif (kd == k.toFpS or kd == k.toFpU) and n == 2 and
           Z3_get_sort_kind(c, Z3_get_sort(c, arg(1))) == Z3_BV_SORT:
        result = bvRange(arg(1), kd == k.toFpS)
      elif kd == k.fneg and n == 1:
        let a = iv(arg(0), depth + 1)
        if a.ok: result = exact(-a.hi, -a.lo)
      elif kd == k.rti and n == 2:
        let a = iv(arg(1), depth + 1)
        if a.ok: result = exact(floor(a.lo), ceil(a.hi))
      elif n == 3 and (kd == k.fadd or kd == k.fsub or kd == k.fmul or
                       kd == k.fdiv):
        let a = iv(arg(1), depth + 1)
        let b = iv(arg(2), depth + 1)
        if a.ok and b.ok:
          if kd == k.fadd: result = widen(a.lo + b.lo, a.hi + b.hi)
          elif kd == k.fsub: result = widen(a.lo - b.hi, a.hi - b.lo)
          elif kd == k.fdiv and b.lo <= 0.0 and b.hi >= 0.0:
            discard   # the divisor may be zero: no interval
          else:
            let ps = if kd == k.fmul:
                       [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
                     else:
                       [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi]
            result = widen(min(ps), max(ps))
    memo[id] = result
  # Three-valued: 1 true, 0 false, -1 not decided by the intervals.
  proc truth(t: RawZ3Ast; depth: int): int =
    result = -1
    chargeWalkerTerms(1)
    if depth >= 24 or Z3_get_ast_kind(c, t) != Z3_APP_AST: return
    let app = Z3_to_app(c, t)
    let kd = ord(Z3_get_decl_kind(c, Z3_get_app_decl(c, app)))
    let n = int(Z3_get_app_num_args(c, app))
    template arg(i: int): RawZ3Ast = Z3_get_app_arg(c, app, cuint(i))
    if kd == k.notK and n == 1:
      let a = truth(arg(0), depth + 1)
      if a >= 0: result = 1 - a
    elif kd == k.andK:
      result = 1
      for i in 0 ..< n:
        let a = truth(arg(i), depth + 1)
        if a == 0: return 0
        if a < 0: result = -1
    elif kd == k.orK:
      result = 0
      for i in 0 ..< n:
        let a = truth(arg(i), depth + 1)
        if a == 1: return 1
        if a < 0: result = -1
    elif n == 2 and (kd == k.leq or kd == k.lt or kd == k.geq or kd == k.gt):
      if not (isDouble(arg(0)) and isDouble(arg(1))): return
      var a = iv(arg(0), 0)
      var b = iv(arg(1), 0)
      if not (a.ok and b.ok): return
      if kd == k.geq or kd == k.gt: swap(a, b)   # now `a <= b` / `a < b`
      if kd == k.leq or kd == k.geq:
        if a.hi <= b.lo: result = 1
        elif a.lo > b.hi: result = 0
      else:
        if a.hi < b.lo: result = 1
        elif a.lo >= b.hi: result = 0
  for r in roots:
    if truth(r.raw, 0) == 0: return true

proc byteLeafIds*(ctx: Z3Context; roots: openArray[Z3Bool]): HashSet[int] =
  ## The AST ids of the string leaves whose byte-domain constraint `s in
  ## (\x00..\xff)*` is itself one of `roots`: built as the walker builds it
  ## (`allocateSym`'s `itString` arm), so it is the same hash-consed AST.
  ## Every character of such a leaf has a code in 0..255 in every model of
  ## `roots`. Used by `seqLenCaps` (its byte tests) and, RFC-0005 S8ae, by
  ## `seqRangeFacts` (`str.to_code`'s upper bound).
  ##
  ## RFC-0016 INT-87: also a `cstring`'s bytes, whose constraint is `s in
  ## (\x01..\xff)*` (`allocateSym`'s `tCString` pair, no NUL): every code
  ## is in 1..255, so in 0..255 as well.
  let kinds = seqCapKinds()
  let byteRe = star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff")))
  let byteReId = astId(ctx, byteRe.raw)
  let cstrRe = star(range(mkString(ctx, "\x01"), mkString(ctx, "\xff")))
  let cstrReId = astId(ctx, cstrRe.raw)
  for r in roots:
    let ra = toAnyAst(r)
    if getAstKind(ra) == akApp and
       ord(Z3_get_decl_kind(ctx.raw, unpackApp(ra).decl)) == kinds.inRe:
      let args = unpackApp(ra).args
      let reId = astId(ctx, args[1].raw)
      if (reId == byteReId or reId == cstrReId) and getAstKind(args[0]) == akApp and
         ord(Z3_get_decl_kind(ctx.raw, unpackApp(args[0]).decl)) == kinds.uninterp:
        result.incl astId(ctx, args[0].raw)

proc seqLenCaps*(ctx: Z3Context; roots: openArray[Z3Bool]; cap: int):
    tuple[caps: seq[Z3Bool], lastIndex: bool,
          byteEqs: seq[tuple[old, new: Z3Bool]], lens: seq[Z3Int]] =
  ## RFC-0005 S8k. `len(t) <= cap` for every seq-sorted (string or seq)
  ## term `t` in `roots` that is an uninterpreted constant or application
  ## (an input, a fresh return, a closure/UF result) or an array `select`
  ## (a heap cell). Every other seq-sorted term is built from these by
  ## interpreted operations, so bounding the leaves bounds the query's
  ## search space. Quantifier bodies are not entered (their seq terms are
  ## bound, not chosen). Each distinct AST is visited once. `lastIndex`
  ## reports a `seq.last_indexof` anywhere in `roots` (see `checkCapped`);
  ## it is matched by name, because its decl kind is Z3's catch-all
  ## internal ordinal, which other operators share (and which moved
  ## between Z3 4.13.4 and 5.1: 45100, then 49165). Its name is the same
  ## on both. Every other operator here is matched by decl kind
  ## (`SeqCapKinds`, RFC-0005 S8o): names are not stable across Z3
  ## releases.
  ##
  ## `byteEqs` pairs each byte test `int2bv[8](str.to_code(c)) == n`
  ## (either operand order, `n` a numeral, `c = str.at(s, i)`), where `s`
  ## is a string leaf whose byte-domain constraint `s in (\x00..\xff)*`
  ## is itself one of `roots` (RFC-0005 S8bm: or a `str.substr` of one), with `c == "\xNN"` (for `n = 255`, also
  ## `c == ""`: `str.at` past the end is `""`, whose code -1 wraps to
  ## 0xFF). Under that constraint every character of `s` has a code in
  ## 0..255, so the two agree in every model of `roots`. The same holds
  ## (RFC-0005 S8o) for two byte tests, `c == d` or one of them `""` and
  ## the other `"\xff"`; and for a byte test against an 8-bit input `x`,
  ## `c == str.from_code(bv2nat(x))` or `x == 0xFF` and `c == ""`
  ## (measured, Z3 4.13.4, each from its own text: `s[39] == s[3] and
  ## s[3] == s[20]` 2.5M units lowered, 51k in character form; `s[39] ==
  ## x and s[2] == x` 8.5M against 185k). Only an input: `bv2nat` of a
  ## computed term is not measured here. `s[i] == 'a'`
  ## lowers to the first form, and Z3 decides it slowly: `s[0..2] ==
  ## "aaa"` needed 41M units (103 s) in the first form, 3.8k in the
  ## second; the `parseInt("-x")` raise query 23.6M against 12k (measured
  ## on the pinned Z3, each in a fresh context). The other exact
  ## rewrite, `x mod 256 == n`, fixed the first and made the second
  ## 110M.
  ##
  ## RFC-0005 S8ba: `lens` holds the length of each leaf above and each
  ## `str.len` term in `roots`, for `checkCapped`'s `len <= high(int)`
  ## facts (`nimLenFacts`). Only the terms: the facts are built where they
  ## are asserted, so they reach the walk's shared context only on that
  ## path (see `seqRangeFacts`' note on context cost).
  ##
  ## RFC-0005 S8cd: a leaf a root conjunct equates to a string literal
  ## (`symexAssume(s == "abcdefghijkl")`) takes no cap. The cap bounds a
  ## search, and that leaf has one value: every model holds it at the
  ## literal's length, so its cap could only refute the query, reading as
  ## a cap decline however the literal compares with `maxSeqLen`.
  let kinds = seqCapKinds()
  let capInt = mkInt(ctx, cap)
  proc kindOf(ctx: Z3Context; a: Z3AnyAst): int =
    ## -1 for a non-application (a numeral, a variable, a quantifier).
    if getAstKind(a) == akApp: ord(Z3_get_decl_kind(ctx.raw, unpackApp(a).decl))
    else: -1
  let byteLeaves = byteLeafIds(ctx, roots)
  proc byteBuilt(ctx: Z3Context; src: Z3AnyAst): bool =
    ## `src` is a byte leaf, a string literal whose every character is at
    ## most 0xFF, or a `str.substr` or `str.++` of such terms: every one
    ## of its characters has a code in 0..255. RFC-0016 INT-87: a
    ## `cstring`'s `c[i]` reads `str.at(bytes ++ "\x00", i)` (its NUL
    ## terminator is readable), which Z3 decided no faster in the first
    ## form than a string's `s[i]` did.
    if astId(ctx, src.raw) in byteLeaves: return true
    if Z3_is_string(ctx.raw, src.raw):
      let n = Z3_get_string_length(ctx.raw, src.raw)
      if n == 0: return true
      var cps = newSeq[cuint](int(n))
      Z3_get_string_contents(ctx.raw, src.raw, n, cps[0].addr)
      for c in cps:
        if c > 0xFF'u32: return false
      return true
    let k = kindOf(ctx, src)
    if k == kinds.strExtract: return byteBuilt(ctx, unpackApp(src).args[0])
    if k >= 0 and k == kinds.strConcat:
      for a in unpackApp(src).args:
        if not byteBuilt(ctx, a): return false
      return true
    false
  proc byteTestChar(ctx: Z3Context; conv: Z3AnyAst):
      tuple[ok: bool, ch: Z3AnyAst] =
    ## `str.at(s, i)` when `conv` is `int2bv[8](str.to_code(str.at(s, i)))`
    ## over a byte leaf `s`, or (RFC-0005 S8bm) over a `str.substr` of one,
    ## at any depth: every character of a substring of `s` is one of `s`'s,
    ## so its code is in 0..255 too (and `str.at` past its end is `""`, as
    ## past `s`'s). A slice's element (`data[4 .. ^1][0]`, B1-1's byte
    ## test) lowers to that form: 5,711,742 units lowered against 24,467
    ## in character form (Z3 5.1, step 1 in a fresh context).
    if kindOf(ctx, conv) != kinds.int2bv or
       Z3_get_bv_sort_size(ctx.raw, Z3_get_sort(ctx.raw, conv.raw)) != 8:
      return
    let code = unpackApp(conv).args[0]
    if kindOf(ctx, code) != kinds.toCode: return
    let ch = unpackApp(code).args[0]
    if kindOf(ctx, ch) != kinds.strAt: return
    if not byteBuilt(ctx, unpackApp(ch).args[0]): return
    (true, ch)
  var literalLeaves: HashSet[int]   # RFC-0005 S8cd
  block:
    var conjuncts: seq[Z3AnyAst]
    for r in roots: conjuncts.add toAnyAst(r)
    while conjuncts.len > 0:
      let c = conjuncts.pop()
      if getAstKind(c) != akApp: continue
      let (decl, args) = unpackApp(c)
      let name = declName(ctx, decl)
      if name == "and":
        for a in args: conjuncts.add a
      elif name == "=" and args.len == 2:
        for (leaf, other) in [(args[0], args[1]), (args[1], args[0])]:
          if getSortKind(leaf) == skSeq and
             Z3_is_string(ctx.raw, other.raw) and
             kindOf(ctx, leaf) in [kinds.uninterp, kinds.select]:
            literalLeaves.incl astId(ctx, leaf.raw)
  var seen: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    if k == kinds.strLen:   # RFC-0005 S8ba
      result.lens.add wrap[Z3Int](ctx, t.raw)
    if getSortKind(t) == skSeq and (k == kinds.uninterp or k == kinds.select):
      let lenT = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, t.raw))
      if id notin literalLeaves:   # RFC-0005 S8cd
        result.caps.add lenT <= capInt
      result.lens.add lenT   # RFC-0005 S8ba
    elif byteLeaves.len > 0 and args.len == 2 and declName(ctx, decl) == "=":
      let empty = mkString(ctx, "")
      let ff = mkString(ctx, "\xff")
      let (okA, chA) = byteTestChar(ctx, args[0])
      let (okB, chB) = byteTestChar(ctx, args[1])
      var eqv: Z3Bool
      var found = true
      if okA and okB:
        # Byte against byte: equal codes, or `""` (code -1) against 0xFF.
        let a = wrap[Z3String](ctx, chA.raw)
        let b = wrap[Z3String](ctx, chB.raw)
        eqv = (a == b) or ((a == empty) and (b == ff)) or
              ((a == ff) and (b == empty))
      elif okA or okB:
        let a = wrap[Z3String](ctx, (if okA: chA else: chB).raw)
        let other = if okA: args[1] else: args[0]
        if getAstKind(other) == akNumeral:
          let n = parseInt($Z3_get_numeral_string(ctx.raw, other.raw))
          eqv = a == mkString(ctx, $chr(n))
          if n == 255: eqv = eqv or (a == empty)
        elif kindOf(ctx, other) == kinds.uninterp:
          # Byte against an 8-bit input (a `char` / `uint8` parameter or
          # draw): the character whose code is its unsigned value.
          let x = wrap[Z3BitVec[8]](ctx, other.raw)
          let code = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw, false))
          eqv = (a == fromCode(ctx, code)) or
                ((x == mkBitVec[8](ctx, 255)) and (a == empty))
        else: found = false
      else: found = false
      if found:
        result.byteEqs.add (old: wrap[Z3Bool](ctx, t.raw), new: eqv)
    elif not result.lastIndex and declName(ctx, decl) == "seq.last_indexof":
      result.lastIndex = true
    elif not result.lastIndex and args.len == 0 and k == kinds.uninterp:
      # RFC-0005 S8au: an `rfind` split stands for `seq.last_indexof`, and
      # its query keeps that term's regime (no capped verdict; the uncapped
      # one-shot step 3 after a capped UNSAT), so the split changes the
      # cost of a verdict and never which verdict is reached
      # (`tsymex_rfc0005_s8o_termination` (4): without this, its capped-out
      # rfind query is a cap decline instead of `sxSat`).
      let sp = registeredIndexSplit(ctx, t.raw)
      if sp >= 0 and indexSplits[sp].last: result.lastIndex = true
    for a in args: stack.add a

proc nimLenFacts*(ctx: Z3Context; lens: openArray[Z3Int]): seq[Z3Bool] =
  ## RFC-0005 S8ba. `len <= high(int)` for each length term `seqLenCaps`
  ## collected (`lens`). Nim's `len` is an `int`, so every real string and
  ## seq satisfies it; the sequence theory alone admits longer ones, and an
  ## index bounded by a length (`i < len(s)`, then `i + 1`) could overflow
  ## in a model no real input has: S8au's `readCStr` raise query and its
  ## unbounded `rfind` label declined on the cap for exactly that. True of
  ## every real input rather than of the theory, so not in `seqRangeFacts`
  ## (whose facts are pinned valid in the theory); asserted beside them in
  ## `checkCapped`'s step 1c, where an UNSAT is still the query's own. The
  ## bit-vector encoding reads a length through these Int terms
  ## (`int2bv`), so one fact covers both.
  if lens.len == 0: return
  let highInt = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw,
    cstring($high(int64)), Z3_get_sort(ctx.raw, lens[0].raw)))
  for l in lens: result.add l <= highInt


proc regexLenBounds*(ctx: Z3Context; kinds: SeqCapKinds; re: Z3AnyAst):
    tuple[lo, hi: int] =
  ## RFC-0005 S8ai. Bounds on the length of every word of the regex `re`,
  ## for `seqRangeFacts`' `str.in_re` fact: every word is at least `lo`
  ## long and, unless `hi` is -1 (unbounded), at most `hi`. Read off the
  ## constructors (`SeqCapKinds`): a literal `str.to_re` its length, a
  ## range or any character 1, a concatenation the sums, a union the
  ## widest, an intersection the narrowest, `*` `0..`, `+` `lo..`, `opt`
  ## `0..hi`, a loop or power its counts times its body's. Any other
  ## constructor (a complement, a non-literal `str.to_re`) is `0..`, which
  ## claims nothing. An empty language has no word, so any bound holds of
  ## it. Each count is clamped at a million (a lower bound clamped down, an
  ## upper bound past it unbounded), so the arithmetic cannot overflow.
  const big = 1_000_000
  proc sumHi(a, b: int): int =
    if a < 0 or b < 0 or a + b > big: -1 else: a + b
  proc mulHi(a, n: int): int =
    if a < 0: -1 elif n == 0 or a == 0: 0 elif a > big div n: -1 else: a * n
  proc mulLo(a, n: int): int =
    if n == 0 or a == 0: 0 elif a > big div n: big else: a * n
  result = (lo: 0, hi: -1)
  if getAstKind(re) != akApp: return
  let (decl, args) = unpackApp(re)
  let k = ord(Z3_get_decl_kind(ctx.raw, decl))
  if k == kinds.reToRe and args.len == 1:
    if Z3_is_string(ctx.raw, args[0].raw):
      let n = getStringLength(wrap[Z3String](ctx, args[0].raw))
      result = (lo: min(n, big), hi: (if n > big: -1 else: n))
  elif (k == kinds.reRange and args.len == 2) or
       (k == kinds.reAllChar and args.len == 0):
    result = (lo: 1, hi: 1)
  elif k == kinds.reConcat and args.len >= 1:
    result = (lo: 0, hi: 0)
    for a in args:
      let b = regexLenBounds(ctx, kinds, a)
      result = (lo: min(big, result.lo + b.lo), hi: sumHi(result.hi, b.hi))
  elif k == kinds.reUnion and args.len >= 1:
    result = regexLenBounds(ctx, kinds, args[0])
    for a in args[1 .. ^1]:
      let b = regexLenBounds(ctx, kinds, a)
      result = (lo: min(result.lo, b.lo),
                hi: (if result.hi < 0 or b.hi < 0: -1 else: max(result.hi, b.hi)))
  elif k == kinds.reInter and args.len >= 1:
    result = regexLenBounds(ctx, kinds, args[0])
    for a in args[1 .. ^1]:
      let b = regexLenBounds(ctx, kinds, a)
      result = (lo: max(result.lo, b.lo),
                hi: (if result.hi < 0: b.hi elif b.hi < 0: result.hi
                     else: min(result.hi, b.hi)))
  elif k == kinds.rePlus and args.len == 1:
    result = (lo: regexLenBounds(ctx, kinds, args[0]).lo, hi: -1)
  elif k == kinds.reOpt and args.len == 1:
    result = (lo: 0, hi: regexLenBounds(ctx, kinds, args[0]).hi)
  elif (k == kinds.reLoop or k == kinds.rePower) and args.len == 1:
    # `(_ re.loop lo hi)`, `(_ re.loop lo)` (no upper count) and `(_ re.^
    # n)` carry their counts as the decl's integer parameters. A loop whose
    # upper count is below its lower one (an empty language) is left at
    # `0..`, as is any other parameter shape.
    let np = int Z3_get_decl_num_parameters(ctx.raw, decl)
    let b = regexLenBounds(ctx, kinds, args[0])
    let lo = if np >= 1: int Z3_get_decl_int_parameter(ctx.raw, decl, 0) else: -1
    if k == kinds.rePower and np == 1 and lo >= 0:
      result = (lo: mulLo(b.lo, lo), hi: mulHi(b.hi, lo))
    elif k == kinds.reLoop and np == 2 and lo >= 0:
      let hi = int Z3_get_decl_int_parameter(ctx.raw, decl, 1)
      # Z3's API takes an upper count of 0 for "no upper count": read it
      # so, which claims less if the build meant `{""}` or no word.
      if hi == 0: result = (lo: mulLo(b.lo, lo), hi: -1)
      elif hi >= lo: result = (lo: mulLo(b.lo, lo), hi: mulHi(b.hi, hi))
    elif k == kinds.reLoop and np == 1 and lo >= 0:
      result = (lo: mulLo(b.lo, lo), hi: -1)
  elif k == kinds.reLoop and args.len in 2 .. 3:
    # The same loop with its counts as integer ARGUMENTS (`(re.loop r lo
    # hi)`, SMT-LIB 2.5's form, which Z3's parser builds that way). Only
    # numeral counts are read; an upper count below the lower one (an
    # empty language) is left at `0..`.
    proc count(a: Z3AnyAst): int =
      if getAstKind(a) != akNumeral: return -1
      let txt = $Z3_get_numeral_string(ctx.raw, a.raw)
      if txt.len > 9 or txt.startsWith("-"): -1 else: parseInt(txt)
    let b = regexLenBounds(ctx, kinds, args[0])
    let lo = count(args[1])
    let hi = if args.len == 3: count(args[2]) else: -2
    if lo >= 0 and hi == -2:
      result = (lo: mulLo(b.lo, lo), hi: -1)
    elif lo >= 0 and hi >= lo:
      result = (lo: mulLo(b.lo, lo), hi: mulHi(b.hi, hi))

proc seqRangeFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8v. The range the sequence theory gives each length and
  ## index term in `roots`, for `checkCapped`'s step 1c. There the query
  ## runs with no sequence theory (`querySolver`'s `seqTheory = false`),
  ## so those functions are uninterpreted and take any integer:
  ##   - `str.len(x) >= 0`;
  ##   - `r = str.indexof(s, t, i)`: `r = -1`, or `0 <= r`, `i <= r` and
  ##     `r + str.len(t) <= str.len(s)`;
  ##   - `r = str.last_indexof(s, t)`: `r = -1`, or `0 <= r` and
  ##     `r + str.len(t) <= str.len(s)`.
  ## Each holds in every model of the sequence theory (an empty `t` at
  ## `i = len(s)` gives `r = len(s)`, so the bound is `r + len(t) <=
  ## len(s)`, not `r < len(s)`); pinned against the theory by
  ## `tests/tsymex_rfc0005_s8v_termination.nim`. So asserting them keeps
  ## every real model. They let step 1c see a cap's conflict that runs
  ## through one of these values. S8r's range-checked search asked for `idx` outside
  ## `0..1000` with `idx = str.indexof(s, ":", 0)`, `idx != -1` and `idx <
  ## len(s)`: under the 128 cap only `idx <= -2` is left, which the
  ## theory-free query admitted, so `checkCapped`'s step 1c was SAT and
  ## step 2 ran the sequence theory. On Z3 4.13.4 that was a string search
  ## of 58 s and 1.2 GB. Step 1b does not take them. Its UNSAT would stay
  ## sound with them, but the terms they build stay in the walk's shared
  ## context, and Z3's cost follows what the context holds (see
  ## `checkCapped`): with them in step 1b, a SAT query of
  ## `tsymex_r6_b1_stringbacked` B1-1 at 18.8M units ran out its 20M
  ## budget on Z3 5.1, and the suite's total went from 60M units to 116M.
  ## They are built only after step 1 came back UNSAT and step 1b found no
  ## theory-free refutation, so these terms reach the context only on the
  ## path to a cap decline or step 2. There they are checked twice: first
  ## without the caps, where an UNSAT is the query's own, then with them
  ## (step 1c). Quantifier bodies are not entered (their terms
  ## are bound), and each distinct AST is visited once. `str.len` and
  ## `str.indexof` are matched by decl kind (`SeqCapKinds`),
  ## `seq.last_indexof` by name (see `seqLenCaps`).
  ##
  ## RFC-0005 S8ae adds, each as valid in the theory as the above (pinned
  ## by `tests/tsymex_rfc0005_s8ae_remainder.nim`: the negation is never
  ## SAT with the theory, and the fact is `true` on every small ground
  ## instance under Z3's own rewriter):
  ##   - `c = str.at(s, i)`: `len(c) = 1` if `0 <= i < len(s)`, else 0;
  ##   - `r = str.substr(s, i, n)`: `len(r) = min(n, len(s) - i)` if `0 <=
  ##     i < len(s)` and `0 < n`, else 0;
  ##   - `k = str.to_code(c)`: `k >= -1`, `k >= 0` iff `len(c) = 1`, and `k
  ##     <= 255` when `c` is `str.at` of a byte leaf (`byteLeafIds`: its
  ##     byte-domain constraint is a root, so the bound holds in every model
  ##     of `roots`, not of the theory alone);
  ##   - `v = str.to_int(x)`: `v >= -1`;
  ##   - `x = y` over sequences: `len(x) = len(y)`. Theory-free, the
  ##     rewriter folds `str.len` of a literal (and of `a ++ b`, so `str.++`
  ##     needs no fact of its own), so `str.at(s, 200) == "x"` reached no
  ##     length without it;
  ##   - `str.contains(s, t)`, `str.prefixof(t, s)`, `str.suffixof(t, s)`:
  ##     `len(t) <= len(s)`;
  ## and, linking two functions over the same haystack `s` and needle `t`
  ## when both terms are in `roots` (no term the query does not hold is
  ## built for them):
  ##   - `str.indexof(s, t, i) >= 0` implies `str.contains(s, t)`, and with
  ##     `i = 0` the converse; a prefix `t` has `str.indexof(s, t, 0) = 0`;
  ##   - a prefix or suffix is contained;
  ##   - a piece `p` of `s` at `i` (`str.at(s, i)`, `str.substr(s, i, n)`)
  ##     with `p = t` a root equality: `t` is contained in `s`, and with `0
  ##     <= i < len(s)`, `0 <= str.indexof(s, t, j) <= i` for `0 <= j <= i`.
  ## Before S8r step 2's unsat core decided a query refuted only through
  ## such a relation (`str.indexof(s, ":", 0) > 200 and not str.contains(s,
  ## ":")`); since, the range facts let step 1c see only the cap's
  ## refutation, and it declined. The links make the uncapped fact check
  ## refute it: the query's own UNSAT, with no string search. A running
  ## step 2 behind step 1c was measured instead and rejected: its core
  ## named the cap on the prefix and slice shapes too, and `rlimit` does
  ## not bound it on a query SAT only past the cap (49 s and 1.2 GB under
  ## 200k units on Z3 5.1, 9.3 GB under 1M on Z3 4.13.4).
  ##
  ## RFC-0005 S8ai. The links are semantic. S8ae matched a haystack and a
  ## needle by AST (a char needle by the literal it folds to), so a needle
  ## equal to another only through `y = t`, or a computed `"a" ++ "b"`
  ## against `"ab"`, got no link. Terms are now grouped into the query's
  ## equality classes: every sequence equality in `roots` joins its sides,
  ## and a term joins the class of what Z3's simplifier folds it to. A link
  ## between two terms whose haystacks or needles differ in AST is guarded
  ## by their equality (`implies(y == t, ...)`), so it stays valid in the
  ## theory on its own: theory-free, the guard follows from the query's
  ## equalities by congruence, or from the rewriter. `seq.last_indexof` is
  ## linked too, since a query holding one now takes step 1c (`checkCapped`).
  ## And, each valid in the theory (pinned by
  ## `tests/tsymex_rfc0005_s8ai_semantic.nim`, the two checks above, which
  ## the same file shows catch a broken fact of each kind):
  ##   - two `str.indexof(s, t, _)` from `0 <= j <= i`: `r_j >= i` implies
  ##     `r_i = r_j`, and `r_i >= 0` implies `0 <= r_j <= r_i` (a nonzero
  ##     start, the converse direction); a suffix `t` is found from any `0
  ##     <= i <= len(s) - len(t)`, at most at `len(s) - len(t)`;
  ##   - `L = seq.last_indexof(s, t)`: `L >= 0` iff `str.contains(s, t)`;
  ##     a prefix gives `L >= 0`, a suffix `L = len(s) - len(t)`, a piece
  ##     equal to `t` at `i` in range `L >= i`; and (RFC-0005 S8aw) `L` is
  ##     at least every found `str.indexof(s, t, i)`.
  ## A LINK is held to the bar S8ai set (the negation is never SAT with the
  ## theory, and the fact is true on every small ground instance), not to
  ## S8v's "the negation is UNSAT" bar for the single-function ranges: a
  ## link is sound because it is TRUE of the theory, and whether Z3 refutes
  ## its negation is a question of the solver's completeness. Neither Z3
  ## refutes the pairwise, piece or join links' negations within 1M units
  ## (RFC-0005 S8aw's As-landed note); each is pinned true by exhaustive
  ## enumeration instead (`tests/tsymex_rfc0005_s8aw_remainder.nim`).
  ##   - `r = str.replace_all(s, t, u)`: `r = s` for an empty `t` or with no
  ##     occurrence (`not str.contains(s, t)`); `len(r)` against `len(s)`
  ##     as `len(t)` against `len(u)`; with literal `t`, `u` (`len(t) >=
  ##     1`) the growth bound `len(t) * len(r) <= len(u) * len(s)` (or `>=`
  ##     when `u` is the shorter);
  ##   - `str.in_re(s, R)`: `len(s)` within `R`'s word lengths
  ##     (`regexLenBounds`), when they bound it;
  ##   - `x = str.from_int(n)`: `len(x)` is 0 for `n < 0`, else the number
  ##     of decimal digits of `n` (exact below 10^20, at least 21 above),
  ##     and `str.to_int(x)` is `n` for `n >= 0`, else -1;
  ##   - a word equation, `h` equal to `a_1 ++ ... ++ a_k` (`str.++`): a
  ##     part equal to (or a literal holding) the needle, or containing it,
  ##     makes `h` contain it, found from `0 <= i <= offset` at most within
  ##     that part, with `L` at least the part's offset; a prefix of the
  ##     first part (a suffix of the last) is one of `h`; and for a needle of
  ##     length at most 1, `h` contains it only if some part does.
  let kinds = seqCapKinds()
  let zero = mkInt(ctx, 0)
  let minusOne = mkInt(ctx, -1)
  proc lenOf(ctx: Z3Context; a: Z3AnyAst): Z3Int =
    wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, a.raw))
  proc eqOf(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool =
    # Two terms of one equality class, so of one sort (an equality's sides
    # and a term's simplified form share it).
    wrap[Z3Bool](ctx, checkedEq(ctx, a.raw, b.raw))
  var byteLeaves: HashSet[int]
  # RFC-0005 S8ae / S8ai: the terms the relational facts below link.
  type Rel = tuple[s, t: Z3AnyAst, p: Z3Bool]
    ## `str.contains(s, t)`, `str.prefixof(t, s)`, `str.suffixof(t, s)`.
  var containsL, prefixL, suffixL: seq[Rel]
  var indexOfs: seq[tuple[s, t: Z3AnyAst, i, r: Z3Int]]
  var lastIdxs: seq[tuple[s, t: Z3AnyAst, r: Z3Int]]
  var pieces: seq[tuple[s, x: Z3AnyAst, i: Z3Int]]
    ## `str.at(s, i)` and `str.substr(s, i, n)`: a piece of `s` at `i`.
  var concats: seq[tuple[c: Z3AnyAst, parts: seq[Z3AnyAst]]]
  var replaces: seq[tuple[s, t: Z3AnyAst, r: Z3AnyAst]]
  var fromInts: seq[tuple[n: Z3Int, x: Z3AnyAst]]
  var toInts: seq[tuple[x: Z3AnyAst, v: Z3Int]]
  # RFC-0005 S8ai: the query's equality classes, a union-find over the ids
  # of the terms' simplified forms. `simpOf` holds each simplified AST, so
  # its id is not reused while this runs.
  var simpOf: Table[int, Z3AnyAst]
  var parent: Table[int, int]
  proc simp(a: Z3AnyAst): Z3AnyAst =
    let id = astId(ctx, a.raw)
    if id notin simpOf:
      simpOf[id] =
        if getAstKind(a) == akApp and unpackApp(a).args.len > 0:
          wrap[Z3AnyAst](ctx, ctx.checkErr Z3_simplify(ctx.raw, a.raw))
        else: a
    simpOf[id]
  proc cls(a: Z3AnyAst): int =
    result = astId(ctx, simp(a).raw)
    while parent.getOrDefault(result, result) != result:
      result = parent[result]
  proc join(a, b: Z3AnyAst) =
    let ra = cls(a)
    let rb = cls(b)
    if ra != rb: parent[ra] = rb
  proc same(g: var seq[Z3Bool]; a, b: Z3AnyAst) =
    ## The guard that `a` and `b` (one class) are equal, unless one AST.
    if astId(ctx, a.raw) != astId(ctx, b.raw): g.add eqOf(ctx, a, b)
  proc guarded(g: seq[Z3Bool]; f: Z3Bool): Z3Bool =
    if g.len == 0: return f
    var all = g[0]
    for k in 1 ..< g.len: all = all and g[k]
    implies(all, f)
  proc litLen(a: Z3AnyAst): int =
    ## The length of the string literal `a` folds to, or -1.
    let f = simp(a)
    if Z3_is_string(ctx.raw, f.raw): getStringLength(wrap[Z3String](ctx, f.raw))
    else: -1
  proc litHolds(rel: LitRel; a, b: Z3AnyAst): int =
    ## `str.contains(a, b)` / `str.prefixof(a, b)` / `str.suffixof(a, b)`
    ## over the literals `a` and `b` fold to: 1 true, 0 false, -1 when
    ## either is not a literal.
    if litLen(a) < 0 or litLen(b) < 0: return -1
    # CRH-07: owned for the call; a `.raw` of each temporary relied on
    # `simp`'s memo table to keep the term alive.
    let x = simp(a)
    let y = simp(b)
    let term = case rel
      of lrContains: ctx.checkErr Z3_mk_seq_contains(ctx.raw, x.raw, y.raw)
      of lrPrefix: ctx.checkErr Z3_mk_seq_prefix(ctx.raw, x.raw, y.raw)
      of lrSuffix: ctx.checkErr Z3_mk_seq_suffix(ctx.raw, x.raw, y.raw)
    let v = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_simplify(ctx.raw, term))
    case $Z3_ast_to_string(ctx.raw, v.raw)
    of "true": 1
    of "false": 0
    else: -1
  proc flatten(a: Z3AnyAst; into: var seq[Z3AnyAst]) =
    # RFC-0005 S8ct: takes no stack, however long the concatenation.
    var open = @[a]
    while open.len > 0:
      let t = open.pop()
      if getAstKind(t) == akApp and
         ord(Z3_get_decl_kind(ctx.raw, unpackApp(t).decl)) == kinds.strConcat:
        let args = unpackApp(t).args
        for i in countdown(args.high, 0): open.add args[i]
      else: into.add t
  proc pow10(d: int): Z3Int =
    var txt = "1"
    for _ in 1 .. d: txt.add '0'
    wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, txt.cstring,
                                                Z3_get_sort(ctx.raw, zero.raw)))
  var seen: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    let split = if k == kinds.uninterp and args.len == 0:
                  registeredIndexSplit(ctx, t.raw)
                else: -1
    if split >= 0:
      # RFC-0005 S8ag: a split's Int is `str.indexof(s, c, start)` in every
      # model of a query that holds it (`indexSplitRoots` asserts its axioms
      # wherever it is reached), so it takes that term's range and links.
      let sp = indexSplits[split]
      # RFC-0005 S8au: any needle (its length, not 1), and a `last` split
      # is `seq.last_indexof`'s term, with that term's range and links.
      let nc = literalLen(sp.c)
      let lc = if nc >= 0: mkInt(ctx, nc) else: lenOf(ctx, toAnyAst(sp.c))
      if sp.last:
        result.add (sp.ix == minusOne) or
          ((zero <= sp.ix) and (sp.ix + lc <= len(sp.s)))
        lastIdxs.add (s: toAnyAst(sp.s), t: toAnyAst(sp.c), r: sp.ix)
      else:
        result.add (sp.ix == minusOne) or
          ((zero <= sp.ix) and (sp.start <= sp.ix) and
           (sp.ix + lc <= len(sp.s)))
        indexOfs.add (s: toAnyAst(sp.s), t: toAnyAst(sp.c), i: sp.start,
                      r: sp.ix)
    elif k == kinds.strLen:
      result.add wrap[Z3Int](ctx, t.raw) >= zero
    elif k == kinds.strIndex and args.len == 3:
      let r = wrap[Z3Int](ctx, t.raw)
      let i = wrap[Z3Int](ctx, args[2].raw)
      result.add (r == minusOne) or
        ((zero <= r) and (i <= r) and
         (r + lenOf(ctx, args[1]) <= lenOf(ctx, args[0])))
      indexOfs.add (s: args[0], t: args[1], i: i, r: r)
    elif args.len == 2 and getSortKind(t) == skInt and
         declName(ctx, decl) == "seq.last_indexof":
      let r = wrap[Z3Int](ctx, t.raw)
      result.add (r == minusOne) or
        ((zero <= r) and (r + lenOf(ctx, args[1]) <= lenOf(ctx, args[0])))
      lastIdxs.add (s: args[0], t: args[1], r: r)
    elif k == kinds.strContains and args.len == 2:
      # RFC-0005 S8ae: `str.contains(s, t)`.
      let c = wrap[Z3Bool](ctx, t.raw)
      result.add implies(c, lenOf(ctx, args[1]) <= lenOf(ctx, args[0]))
      containsL.add (s: args[0], t: args[1], p: c)
    elif (k == kinds.strPrefix or k == kinds.strSuffix) and args.len == 2:
      # RFC-0005 S8ae: `str.prefixof(t, s)` / `str.suffixof(t, s)`, the
      # needle first.
      let p = wrap[Z3Bool](ctx, t.raw)
      result.add implies(p, lenOf(ctx, args[0]) <= lenOf(ctx, args[1]))
      if k == kinds.strPrefix: prefixL.add (s: args[1], t: args[0], p: p)
      else: suffixL.add (s: args[1], t: args[0], p: p)
    elif k == kinds.strAt and args.len == 2:
      # RFC-0005 S8ae: `str.at(s, i)` is one character in range, else "".
      let i = wrap[Z3Int](ctx, args[1].raw)
      pieces.add (s: args[0], x: t, i: i)
      result.add lenOf(ctx, t) ==
        ite((zero <= i) and (i < lenOf(ctx, args[0])), mkInt(ctx, 1), zero)
    elif k == kinds.strExtract and args.len == 3:
      # RFC-0005 S8ae: `str.substr(s, i, n)` is "" unless `0 <= i < len(s)`
      # and `0 < n`; then its length is `min(n, len(s) - i)`.
      let i = wrap[Z3Int](ctx, args[1].raw)
      let n = wrap[Z3Int](ctx, args[2].raw)
      pieces.add (s: args[0], x: t, i: i)
      let rest = lenOf(ctx, args[0]) - i
      result.add lenOf(ctx, t) ==
        ite((zero <= i) and (i < lenOf(ctx, args[0])) and (zero < n),
            ite(n <= rest, n, rest), zero)
    elif k == kinds.toCode and args.len == 1:
      # RFC-0005 S8ae: -1 unless the argument is one character; at most
      # 255 when that character is read off a byte leaf (`byteLeafIds`).
      let code = wrap[Z3Int](ctx, t.raw)
      result.add code >= minusOne
      result.add (code >= zero) == (lenOf(ctx, args[0]) == mkInt(ctx, 1))
      let c = args[0]
      if getAstKind(c) == akApp and
         ord(Z3_get_decl_kind(ctx.raw, unpackApp(c).decl)) == kinds.strAt:
        if byteLeaves.len == 0: byteLeaves = byteLeafIds(ctx, roots)
        if astId(ctx, unpackApp(c).args[0].raw) in byteLeaves:
          result.add code <= mkInt(ctx, 255)
    elif k == kinds.strToInt and args.len == 1:
      # RFC-0005 S8ae: -1 for a non-numeral, else its non-negative value.
      result.add wrap[Z3Int](ctx, t.raw) >= minusOne
      toInts.add (x: args[0], v: wrap[Z3Int](ctx, t.raw))
    elif k == kinds.strConcat and args.len >= 2:
      # RFC-0005 S8ai: a word, for the word-equation links below.
      var parts: seq[Z3AnyAst]
      flatten(t, parts)
      concats.add (c: t, parts: parts)
    elif k == kinds.strReplaceAll and args.len == 3:
      # RFC-0005 S8ai: `r = str.replace_all(s, a, b)` replaces every
      # (leftmost, non-overlapping) occurrence of a non-empty `a`, and is
      # `s` for an empty one. Each of the `m` replacements changes the
      # length by `len(b) - len(a)`, and `m * len(a) <= len(s)`.
      let sL = lenOf(ctx, args[0])
      let aL = lenOf(ctx, args[1])
      let bL = lenOf(ctx, args[2])
      let rL = lenOf(ctx, t)
      result.add implies(aL == zero, eqOf(ctx, t, args[0]))
      result.add implies(aL == bL, rL == sL)
      result.add implies(aL <= bL, sL <= rL)
      result.add implies(bL <= aL, rL <= sL)
      let la = litLen(args[1])
      let lb = litLen(args[2])
      if la >= 1 and lb >= 0:
        if lb >= la: result.add mkInt(ctx, la) * rL <= mkInt(ctx, lb) * sL
        else: result.add mkInt(ctx, la) * rL >= mkInt(ctx, lb) * sL
      replaces.add (s: args[0], t: args[1], r: t)
    elif k == kinds.strFromInt and args.len == 1:
      # RFC-0005 S8ai: `str.from_int(n)` is "" for `n < 0`, else the
      # decimal digits of `n` with no leading zero.
      let n = wrap[Z3Int](ctx, args[0].raw)
      var digits = ite(n < pow10(19), mkInt(ctx, 19), mkInt(ctx, 20))
      for d in countdown(18, 1): digits = ite(n < pow10(d), mkInt(ctx, d), digits)
      result.add implies(n < pow10(20),
                         lenOf(ctx, t) == ite(n < zero, zero, digits))
      result.add implies(n >= pow10(20), lenOf(ctx, t) >= mkInt(ctx, 21))
      fromInts.add (n: n, x: t)
    elif k == kinds.inRe and args.len == 2:
      # RFC-0005 S8ai: a member of `R` is as long as some word of `R`.
      # RFC-0005 S8ct: `0..` claims nothing.
      let b = if termTooDeep(ctx, args[1].raw): (lo: 0, hi: -1)
              else: regexLenBounds(ctx, kinds, args[1])
      let m = wrap[Z3Bool](ctx, t.raw)
      if b.lo > 0: result.add implies(m, lenOf(ctx, args[0]) >= mkInt(ctx, b.lo))
      if b.hi >= 0: result.add implies(m, lenOf(ctx, args[0]) <= mkInt(ctx, b.hi))
    elif args.len == 2 and getSortKind(args[0]) == skSeq and
         declName(ctx, decl) == "=":
      # RFC-0005 S8ae: equal sequences have equal lengths. Without the
      # theory, `str.len` of a literal is folded to a numeral by the
      # rewriter, so `str.at(s, 200) == "x"` would not otherwise reach the
      # length of `str.at(s, 200)` and its fact above.
      result.add implies(wrap[Z3Bool](ctx, t.raw),
                         lenOf(ctx, args[0]) == lenOf(ctx, args[1]))
      join(args[0], args[1])
    for a in args: stack.add a
  # RFC-0005 S8ae: facts that link two of the theory's functions over one
  # haystack and needle, each valid in the theory. Only terms already in
  # `roots` are linked (no `str.contains` is built that the query does not
  # hold), so a fact can only take part in a refutation through them.
  # RFC-0005 S8ai: "one" is one equality class, and a link between terms
  # whose haystacks or needles differ in AST is guarded by their equality.
  proc pairGuard(s1, s2, t1, t2: Z3AnyAst): seq[Z3Bool] =
    same(result, s1, s2)
    same(result, t1, t2)
  proc sameKey(s1, s2, t1, t2: Z3AnyAst): bool =
    cls(s1) == cls(s2) and cls(t1) == cls(t2)
  # RFC-0005 S8aq tried "`L` (`seq.last_indexof(s, t)`) is at least every
  # found `str.indexof(s, t, i)`" and declined it: neither Z3 refutes its
  # negation (S8aq and S8aw tried twelve forms, up to 10M units). RFC-0005
  # S8aw emits it, under the links' bar (the doc above): it is true -- a
  # found `r = str.indexof(s, t, i) >= 0` is an occurrence of `t` at `r`,
  # and `L` is the greatest occurrence; emitted in the `lastIdxs` loop
  # below, and enumerated true by `tsymex_rfc0005_s8aw_remainder`.
  for e in indexOfs:
    let atZero = e.i == zero
    for c in containsL:
      if sameKey(e.s, c.s, e.t, c.t):
        # Found anywhere is contained; contained is found from 0.
        let g = pairGuard(e.s, c.s, e.t, c.t)
        result.add guarded(g, implies(e.r >= zero, c.p))
        result.add guarded(g, implies(c.p and atZero, e.r >= zero))
    for p in prefixL:
      if sameKey(e.s, p.s, e.t, p.t):
        # A prefix is first found at 0.
        result.add guarded(pairGuard(e.s, p.s, e.t, p.t),
                           implies(p.p and atZero, e.r == zero))
    for p in suffixL:
      if sameKey(e.s, p.s, e.t, p.t):
        # RFC-0005 S8ai: a suffix is found from any start up to its own.
        let lastStart = lenOf(ctx, e.s) - lenOf(ctx, e.t)
        result.add guarded(pairGuard(e.s, p.s, e.t, p.t),
          implies(p.p and (zero <= e.i) and (e.i <= lastStart),
                  (e.i <= e.r) and (e.r <= lastStart)))
    for f in indexOfs:
      if astId(ctx, e.r.raw) != astId(ctx, f.r.raw) and
         sameKey(e.s, f.s, e.t, f.t):
        # RFC-0005 S8ai: from `0 <= e.i <= f.i`, a first index at or past
        # `f.i` is also the first from `f.i`, and one found from `f.i` is
        # found from `e.i`, no later.
        let g = pairGuard(e.s, f.s, e.t, f.t)
        let ordered = (zero <= e.i) and (e.i <= f.i)
        result.add guarded(g, implies(ordered and (e.r >= f.i), f.r == e.r))
        result.add guarded(g, implies(ordered and (f.r >= zero),
                                      (zero <= e.r) and (e.r <= f.r)))
  for l in lastIdxs:
    # RFC-0005 S8ai: `seq.last_indexof` is -1 exactly when not contained; a
    # prefix is found, and a suffix is the last occurrence.
    for e in indexOfs:
      if sameKey(l.s, e.s, l.t, e.t):
        # RFC-0005 S8aw: the join. `e.r >= 0` is an occurrence at `e.r`
        # (an empty `t` occurs at every `0..len(s)`), and `L` is the last.
        result.add guarded(pairGuard(l.s, e.s, l.t, e.t),
                           implies(e.r >= zero, e.r <= l.r))
    for c in containsL:
      if sameKey(l.s, c.s, l.t, c.t):
        result.add guarded(pairGuard(l.s, c.s, l.t, c.t), (l.r >= zero) == c.p)
    for p in prefixL:
      if sameKey(l.s, p.s, l.t, p.t):
        result.add guarded(pairGuard(l.s, p.s, l.t, p.t),
                           implies(p.p, l.r >= zero))
    for p in suffixL:
      if sameKey(l.s, p.s, l.t, p.t):
        result.add guarded(pairGuard(l.s, p.s, l.t, p.t),
          implies(p.p, l.r == lenOf(ctx, l.s) - lenOf(ctx, l.t)))
  for p in prefixL:
    for c in containsL:
      if sameKey(p.s, c.s, p.t, c.t):
        result.add guarded(pairGuard(p.s, c.s, p.t, c.t), implies(p.p, c.p))
  for p in suffixL:
    for c in containsL:
      if sameKey(p.s, c.s, p.t, c.t):
        result.add guarded(pairGuard(p.s, c.s, p.t, c.t), implies(p.p, c.p))
  # A piece of `s` equal to a needle `t` (`s[5] == ':'`, `s[1..2] == "ab"`):
  # `t` is contained in `s`, first found at or before the piece's start,
  # and (RFC-0005 S8ai) last found at or after it.
  for pc in pieces:
    let inRange = (zero <= pc.i) and (pc.i < lenOf(ctx, pc.s))
    for c in containsL:
      if sameKey(pc.s, c.s, pc.x, c.t):
        result.add guarded(pairGuard(pc.s, c.s, pc.x, c.t), c.p)
    for e in indexOfs:
      if sameKey(pc.s, e.s, pc.x, e.t):
        result.add guarded(pairGuard(pc.s, e.s, pc.x, e.t),
          implies(inRange and (zero <= e.i) and (e.i <= pc.i),
                  (zero <= e.r) and (e.r <= pc.i)))
    for l in lastIdxs:
      if sameKey(pc.s, l.s, pc.x, l.t):
        result.add guarded(pairGuard(pc.s, l.s, pc.x, l.t),
                           implies(inRange, l.r >= pc.i))
  # RFC-0005 S8ai: word equations. `cc.c` is `a_1 ++ ... ++ a_k`; a term
  # over a haystack of its class sees each part at its offset.
  for cc in concats:
    let kc = cls(cc.c)
    var offs = newSeq[Z3Int](cc.parts.len)
    var o = zero
    for k, p in cc.parts:
      offs[k] = o
      o = o + lenOf(ctx, p)
    for c in containsL:
      if cls(c.s) != kc: continue
      var gh: seq[Z3Bool]
      same(gh, c.s, cc.c)
      var direct = false      # some part is known to hold the needle
      var complete = true     # every part's containment is known
      var gAll = gh
      var disj: seq[Z3Bool]
      for p in cc.parts:
        if cls(p) == cls(c.t):
          var g = gh
          same(g, p, c.t)
          result.add guarded(g, c.p)
          direct = true
          continue
        let lit = litHolds(lrContains, p, c.t)
        if lit == 1:
          result.add guarded(gh, c.p)
          direct = true
          continue
        if lit == 0: continue
        var known = false
        for c2 in containsL:
          if sameKey(c2.s, p, c2.t, c.t):
            var g = gh
            same(g, c2.s, p)
            same(g, c2.t, c.t)
            result.add guarded(g, implies(c2.p, c.p))
            if not known:
              same(gAll, c2.s, p)
              same(gAll, c2.t, c.t)
              disj.add c2.p
              known = true
        if not known: complete = false
      if complete and not direct:
        # A needle of at most one element lies within one part.
        var oneOf = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_false(ctx.raw))
        for d in disj: oneOf = oneOf or d
        result.add guarded(gAll, implies(c.p and (lenOf(ctx, c.t) <= mkInt(ctx, 1)),
                                         oneOf))
    for first in [true, false]:
      let lst = if first: prefixL else: suffixL
      let p = if first: cc.parts[0] else: cc.parts[^1]
      let rel = if first: lrPrefix else: lrSuffix
      for pr in lst:
        if cls(pr.s) != kc: continue
        var gh: seq[Z3Bool]
        same(gh, pr.s, cc.c)
        if cls(p) == cls(pr.t):
          var g = gh
          same(g, p, pr.t)
          result.add guarded(g, pr.p)
        elif litHolds(rel, pr.t, p) == 1:
          result.add guarded(gh, pr.p)
        for pr2 in lst:
          if sameKey(pr2.s, p, pr2.t, pr.t):
            var g = gh
            same(g, pr2.s, p)
            same(g, pr2.t, pr.t)
            result.add guarded(g, implies(pr2.p, pr.p))
    for k, p in cc.parts:
      let endK = offs[k] + lenOf(ctx, p)
      for e in indexOfs:
        if cls(e.s) != kc: continue
        var gh: seq[Z3Bool]
        same(gh, e.s, cc.c)
        let from0 = (zero <= e.i) and (e.i <= offs[k])
        if cls(p) == cls(e.t):
          var g = gh
          same(g, p, e.t)
          result.add guarded(g, implies(from0, (zero <= e.r) and (e.r <= offs[k])))
        elif litHolds(lrContains, p, e.t) == 1:
          result.add guarded(gh, implies(from0, (zero <= e.r) and
                                         (e.r + lenOf(ctx, e.t) <= endK)))
        for c2 in containsL:
          if sameKey(c2.s, p, c2.t, e.t):
            var g = gh
            same(g, c2.s, p)
            same(g, c2.t, e.t)
            result.add guarded(g, implies(c2.p and from0, (zero <= e.r) and
                                          (e.r + lenOf(ctx, e.t) <= endK)))
      for l in lastIdxs:
        if cls(l.s) != kc: continue
        var gh: seq[Z3Bool]
        same(gh, l.s, cc.c)
        if cls(p) == cls(l.t):
          var g = gh
          same(g, p, l.t)
          result.add guarded(g, l.r >= offs[k])
        elif litHolds(lrContains, p, l.t) == 1:
          result.add guarded(gh, l.r >= offs[k])
        for c2 in containsL:
          if sameKey(c2.s, p, c2.t, l.t):
            var g = gh
            same(g, c2.s, p)
            same(g, c2.t, l.t)
            result.add guarded(g, implies(c2.p, l.r >= offs[k]))
  # RFC-0005 S8ai: no occurrence, no replacement.
  for rp in replaces:
    for c in containsL:
      if sameKey(rp.s, c.s, rp.t, c.t):
        result.add guarded(pairGuard(rp.s, c.s, rp.t, c.t),
                           implies(not c.p, eqOf(ctx, rp.r, rp.s)))
  # RFC-0005 S8ai: `str.to_int(str.from_int(n))` is `n`, or -1 (`""`).
  for f in fromInts:
    for v in toInts:
      if cls(v.x) == cls(f.x):
        var g: seq[Z3Bool]
        same(g, v.x, f.x)
        result.add guarded(g, v.v == ite(f.n >= zero, f.n, minusOne))

var byteDomainKinds* {.threadvar.}: tuple[ready: bool, concat, extract, andK,
                                         eq, notK, orK, impliesK, iteK: int]
  ## RFC-0005 S8y. The decl kinds `dropImpliedByteDomains` matches, read off
  ## terms built once per thread (as `seqCapKinds`: by kind, never by name).
  ## RFC-0005 S8bp: and `not`, for `mergeMemberships`. RFC-0005 S8by: and
  ## `or`, `=>` and `ite`, the polarity `mergeMemberships` reads below the
  ## top level.

proc ensureByteDomainKinds*() =
  if byteDomainKinds.ready: return
  let ctx = probeContext()   # RFC-0005 S8bp
  proc kindOf(a: RawZ3Ast): int =
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
  let s = mkStringVar(ctx, "__s8y_kind_probe_str")
  let b = mkBoolVar(ctx, "__s8y_kind_probe_b")
  byteDomainKinds = (ready: true,
    concat: kindOf((s & mkStringVar(ctx, "__s8y_kind_probe_t")).raw),
    extract: kindOf(substr(s, mkIntVar(ctx, "__s8y_kind_probe_i"),
                           mkIntVar(ctx, "__s8y_kind_probe_n")).raw),
    andK: kindOf((b and mkBoolVar(ctx, "__s8y_kind_probe_c")).raw),
    eq: kindOf((s == mkStringVar(ctx, "__s8y_kind_probe_u")).raw),
    notK: kindOf((not b).raw),
    orK: kindOf((b or mkBoolVar(ctx, "__s8by_kind_probe_d")).raw),
    impliesK: kindOf(implies(b, mkBoolVar(ctx, "__s8by_kind_probe_e")).raw),
    iteK: kindOf(ite(b, mkBoolVar(ctx, "__s8by_kind_probe_f"),
                     mkBoolVar(ctx, "__s8by_kind_probe_g")).raw))

proc dropImpliedByteDomains*(ctx: Z3Context; roots: openArray[Z3Bool]):
    seq[Z3Bool] =
  ## RFC-0005 S8y. `roots` without each byte-domain constraint
  ## `x in (\x00..\xff)*` (`allocateSym`'s `itString` arm) that the rest of
  ## `roots` implies: `x` is defined -- by a root, or a conjunct of a root's
  ## top-level `and` -- equal to a term built by `str.++`, `str.substr` and
  ## `str.at` from string literals whose every character is at most 0xFF
  ## and from strings whose own byte-domain constraint stays in the result.
  ## Every character of such a term is one of those characters, so in every
  ## model of the result `x`'s are too: the two sets have the same models.
  ## A string that justifies a drop is never dropped itself, so no two
  ## constraints are each other's justification.
  ##
  ## Why: a call's string return is allocated with the constraint and then
  ## bound to the callee's closed form -- every readCString key and value of
  ## a pair loop is `k == "" ++ str.substr(s, i, j - i)` -- and Z3 decides
  ## each such membership on its own. In `tsymex_r6_n36_raise_degrade`'s
  ## four-pairs-and-an-empty-key query that was the difference between
  ## running out of 10M units and SAT in 2.5M (fresh context, Z3 5.1).
  ensureByteDomainKinds()
  let bk = byteDomainKinds
  let kinds = seqCapKinds()
  proc kindOf(a: Z3AnyAst): int =
    if getAstKind(a) == akApp: ord(Z3_get_decl_kind(ctx.raw, unpackApp(a).decl))
    else: -1
  proc isStrConst(a: Z3AnyAst): bool =
    getAstKind(a) == akApp and getSortKind(a) == skSeq and
      kindOf(a) == kinds.uninterp and unpackApp(a).args.len == 0
  let byteRe = star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff")))
  let byteReId = astId(ctx, byteRe.raw)
  # The byte-domain roots, by the constrained constant's AST id.
  var domainRoot: seq[tuple[x: int, root: int]]
  var constrained: HashSet[int]
  for i, r in roots:
    let ra = toAnyAst(r)
    if kindOf(ra) == kinds.inRe:
      let args = unpackApp(ra).args
      if astId(ctx, args[1].raw) == byteReId and isStrConst(args[0]):
        let x = astId(ctx, args[0].raw)
        if x notin constrained:
          constrained.incl x
          domainRoot.add (x: x, root: i)
  if domainRoot.len == 0: return @roots
  # Definitions `x == t` among the roots' top-level conjuncts.
  var defs: Table[int, seq[Z3AnyAst]]
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let k = kindOf(t)
    if k == bk.andK:
      for a in unpackApp(t).args: stack.add a
    elif k == bk.eq:
      let args = unpackApp(t).args
      if args.len == 2:
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])]:
          if isStrConst(lhs) and astId(ctx, lhs.raw) in constrained:
            defs.mgetOrPut(astId(ctx, lhs.raw), @[]).add rhs
  proc leaves(t: Z3AnyAst; acc: var seq[int]): bool =
    ## The string constants `t` is built from by `str.++` / `str.substr` /
    ## `str.at` and byte literals; false for any other shape.
    if isStrConst(t):
      acc.add astId(ctx, t.raw)
      return true
    if Z3_is_string(ctx.raw, t.raw):
      let n = Z3_get_string_length(ctx.raw, t.raw)
      if n == 0: return true
      var cps = newSeq[cuint](int(n))
      Z3_get_string_contents(ctx.raw, t.raw, n, cps[0].addr)
      for c in cps:
        if c > 0xFF'u32: return false
      return true
    let k = kindOf(t)
    if k == bk.concat:
      for a in unpackApp(t).args:
        if not leaves(a, acc): return false
      return true
    if k == bk.extract or k == kinds.strAt:
      return leaves(unpackApp(t).args[0], acc)
    false
  var dropped, pinned, dropRoot: HashSet[int]
  for (x, root) in domainRoot:
    if x in pinned: continue
    for t in defs.getOrDefault(x):
      var acc: seq[int]
      # RFC-0005 S8ct: too deep reads as any other shape, which keeps the root.
      if termTooDeep(ctx, t.raw) or not leaves(t, acc): continue
      var ok = true
      for y in acc:
        if y == x or y notin constrained or y in dropped:
          ok = false
          break
      if ok:
        dropped.incl x
        dropRoot.incl root
        for y in acc: pinned.incl y
        break
  for i, r in roots:
    if i notin dropRoot: result.add r

var deepTermsLeftAlone* {.threadvar.}: seq[int]
  ## RFC-0005 S8ct. The depth of each conjunct `mergeMemberships` left as it is
  ## because a recursive walk could not take it.

proc mergeMemberships*(ctx: Z3Context; roots: openArray[Z3Bool]):
    seq[Z3Bool] =
  ## RFC-0005 S8bp. `roots` with the regex memberships of one string term
  ## `x` among the roots' top-level conjuncts -- two or more, one of them
  ## negated: `x in R1`, `not (x in R2)`, .. -- replaced by the one
  ## membership `x in (R1 & comp(R2) & ..)`. `not (x in R)` is `x in
  ## comp(R)` and the conjuncts are removed from their roots, so the
  ## result has the same models. A byte-domain constraint `x in
  ## (\x00..\xff)*` stays as it is, as do roots holding no such group.
  ##
  ## Why: Z3 decides each membership on its own. S8ay's `s.endsWith(re"b+")
  ## and not s.contains(re"b")` (empty: a string ending in `b` contains
  ## one) ran out of 20M units with no length bound on Z3 4.13.4, and took
  ## 6.7M to refute under the length cap, with the cap in step 2's core
  ## (`sxUnknown`); as one membership of the intersection it is UNSAT in
  ## 1,392 units (a fresh context; 5.1 as well).
  ##
  ## RFC-0005 S8by: and below the top level, where a membership sits under
  ## a disjunction, an `ite`, a negation or an implication (`a or not
  ## s.contains(re"b")`). There a membership literal of `x` is merged with
  ## those of the same `x` that hold wherever it is evaluated: the other
  ## conjuncts of each `and` above it, the roots' top-level ones included
  ## (their intersection `I`). Where those and the literals of `x` in its
  ## own conjunction number two or more, one of them negated as it is
  ## read, the conjunction's literals (their intersection `A`) become one:
  ## `x in (A & I)` where they are asserted, `not (x in (comp(A) & I))`
  ## where they are denied (under a `not`, or left of a `=>`), so that
  ## either way Z3 meets one membership of an intersection. Where `x` lies
  ## in `I`, both terms are true exactly when the literals are, and each
  ## `and` above is false wherever a conjunct of it is: every root keeps
  ## its value under every assignment, so the models are the same. A
  ## literal read both ways (an `ite` condition, an argument of `=`) is
  ## left as it is.
  ensureByteDomainKinds()
  let bk = byteDomainKinds
  let kinds = seqCapKinds()
  proc kindOf(a: Z3AnyAst): int =
    if getAstKind(a) == akApp: ord(Z3_get_decl_kind(ctx.raw, unpackApp(a).decl))
    else: -1
  # RFC-0016 CRH-07: held, so its id is not recycled by a later term (the
  # id of a released temporary could name a new `merged` literal).
  let byteRe = star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff")))
  let byteReId = astId(ctx, byteRe.raw)
  # RFC-0016 int6 D1d: a query holding no membership literal anywhere is its
  # own result (no group forms, and `holds` is false on every term, so every
  # root is left as it is); one pass over its terms, each once, says so,
  # where the passes below walk each top-level conjunct's depth on its own.
  block:
    var seen: HashSet[int]
    var stack: seq[Z3AnyAst]
    for r in roots: stack.add toAnyAst(r)
    var found = false
    while stack.len > 0:
      let t = stack.pop()
      let id = astId(ctx, t.raw)
      if id in seen: continue
      seen.incl id
      chargeWalkerTerms(1)
      if getAstKind(t) != akApp: continue
      let k = kindOf(t)
      let args = unpackApp(t).args
      if k == kinds.inRe and args.len == 2 and
         astId(ctx, args[1].raw) != byteReId:
        found = true
        break
      if k == bk.notK and args.len == 1 and kindOf(args[0]) == kinds.inRe:
        found = true
        break
      for a in args: stack.add a
    if not found: return @roots
  type
    Lit = tuple[root, id: int, re: Z3AnyAst, neg: bool]
    Held = seq[tuple[re: Z3AnyAst, neg: bool]]
      ## RFC-0005 S8by. The membership literals of one `x` that hold in a
      ## context: `re` the set they put `x` in (complemented for a negated
      ## one), `neg` whether the literal was negated.
    Pol = enum polPos, polNeg, polBoth
      ## RFC-0005 S8by. How a term is read: asserted, denied, or both.
  proc conjuncts(r: Z3AnyAst): seq[Z3AnyAst] =
    ## `r`'s top-level conjuncts, in order. RFC-0005 S8ct: takes no stack, so a
    ## nest of `and`s as deep as a term gets is read.
    var open = @[r]
    while open.len > 0:
      let t = open.pop()
      if kindOf(t) == bk.andK:
        let args = unpackApp(t).args
        for i in countdown(args.high, 0): open.add args[i]
      else: result.add t
  proc literal(t: Z3AnyAst): tuple[ok: bool, x, re: Z3AnyAst, neg: bool] =
    ## `t` as a membership literal `x in re` or `not (x in re)`; a
    ## byte-domain constraint is none.
    let neg = kindOf(t) == bk.notK
    let m = if neg: unpackApp(t).args[0] else: t
    if kindOf(m) != kinds.inRe: return
    let args = unpackApp(m).args
    if not neg and astId(ctx, args[1].raw) == byteReId: return
    (true, args[0], args[1], neg)
  # Every term made here is wrapped (and so referenced) at once: Z3 keeps
  # an unreferenced result only until its next call.
  proc mk(raw: RawZ3Ast): Z3AnyAst = wrap[Z3AnyAst](ctx, ctx.checkErr raw)
  proc comp(re: Z3AnyAst): Z3AnyAst =
    mk Z3_mk_re_complement(ctx.raw, re.raw)
  proc inter(res: seq[Z3AnyAst]): Z3AnyAst =
    if res.len == 1: return res[0]
    var rs = newSeq[RawZ3Ast](res.len)
    for i, r in res: rs[i] = r.raw
    mk Z3_mk_re_intersect(ctx.raw, cuint(rs.len),
                          cast[ptr UncheckedArray[RawZ3Ast]](rs[0].addr))
  proc member(x, re: Z3AnyAst): Z3AnyAst =
    mk Z3_mk_seq_in_re(ctx.raw, x.raw, re.raw)
  proc held(re: Z3AnyAst; neg: bool): tuple[re: Z3AnyAst, neg: bool] =
    result = (re: re, neg: neg)
    if neg: result.re = comp(re)
  proc andOf(outs: seq[Z3AnyAst]): Z3AnyAst =
    if outs.len == 1: return outs[0]
    var rs = newSeq[RawZ3Ast](outs.len)
    for i, r in outs: rs[i] = r.raw
    mk Z3_mk_and(ctx.raw, cuint(rs.len),
                 cast[ptr UncheckedArray[RawZ3Ast]](rs[0].addr))
  var groups: OrderedTable[int, tuple[x: Z3AnyAst, lits: seq[Lit]]]
  for i, r in roots:
    for t in conjuncts(toAnyAst(r)):
      let l = literal(t)
      if not l.ok: continue
      groups.mgetOrPut(astId(ctx, l.x.raw), (x: l.x, lits: @[])).lits.add(
        (root: i, id: astId(ctx, t.raw), re: l.re, neg: l.neg))
  var merged: seq[Z3Bool]
  var gone, touched: HashSet[int]
  var top: Table[int, Held]   # RFC-0005 S8by: what holds everywhere
  for xId, g in groups:
    var anyNeg = false
    for l in g.lits: anyNeg = anyNeg or l.neg
    if g.lits.len < 2 or not anyNeg:
      for l in g.lits: top.mgetOrPut(xId, @[]).add held(l.re, l.neg)
      continue
    var res = newSeq[Z3AnyAst](g.lits.len)
    for i, l in g.lits:
      res[i] = held(l.re, l.neg).re
      gone.incl l.id
      touched.incl l.root
    let one = inter(res)
    top[xId] = @[(re: one, neg: true)]
    merged.add wrap[Z3Bool](ctx, member(g.x, one).raw)
  var flat: seq[Z3Bool]
  if merged.len == 0: flat = @roots
  else:
    for i, r in roots:
      if i notin touched: flat.add r
      else:
        for t in conjuncts(toAnyAst(r)):
          if astId(ctx, t.raw) notin gone: flat.add wrap[Z3Bool](ctx, t.raw)
    flat.add merged
  # RFC-0005 S8by: below the top level. Only a term holding a membership
  # literal is rebuilt (`holds`), each once per context and reading.
  var hasLit: Table[int, bool]
  proc holds(t: Z3AnyAst): bool =
    let id = astId(ctx, t.raw)
    if id in hasLit: return hasLit[id]
    chargeWalkerTerms(1)   ## RFC-0016 K7
    result = literal(t).ok
    if not result and getAstKind(t) == akApp:
      for a in unpackApp(t).args:
        if holds(a):
          result = true
          break
    hasLit[id] = result
  var memo: Table[(int, int, Pol, bool), Z3AnyAst]
  var serial = 0
  proc flip(p: Pol): Pol =
    case p
    of polPos: polNeg
    of polNeg: polPos
    of polBoth: polBoth
  proc rewrite(t: Z3AnyAst; env: Table[int, Held]; envId: int; pol: Pol;
               conj: bool): Z3AnyAst =
    ## `t` read as `pol` where `env` holds. `conj`: `t` (a Bool term) as a
    ## conjunction -- its own membership literals merged with `env`, the
    ## rest rewritten with those literals held too; otherwise each of its
    ## arguments rewritten, read as its operator reads it.
    if pol == polBoth or getAstKind(t) != akApp or not holds(t): return t
    let key = (astId(ctx, t.raw), envId, pol, conj)
    if key in memo: return memo[key]
    chargeWalkerTerms(1)   ## RFC-0016 K7
    if not conj:
      let (decl, args) = unpackApp(t)
      let k = kindOf(t)
      var raws = newSeq[RawZ3Ast](args.len)
      var keep = newSeq[Z3AnyAst](args.len)
      var changed = false
      for i, a in args:
        let p =
          if k == bk.notK: flip(pol)
          elif k == bk.andK or k == bk.orK: pol
          elif k == bk.impliesK: (if i == 0: flip(pol) else: pol)
          elif k == bk.iteK: (if i == 0: polBoth else: pol)
          else: polBoth
        let b = rewrite(a, env, envId, p, getSortKind(a) == skBool)
        keep[i] = b
        raws[i] = b.raw
        changed = changed or b.raw != a.raw
      result = if not changed: t
               else: mk(Z3_mk_app(ctx.raw, decl, cuint(raws.len),
                                  cast[ptr UncheckedArray[RawZ3Ast]](raws[0].addr)))
      memo[key] = result
      return
    let cs = conjuncts(t)
    var own: OrderedTable[int, tuple[x: Z3AnyAst, lits: Held, ids: seq[int]]]
    for c in cs:
      let l = literal(c)
      if l.ok:
        let xId = astId(ctx, l.x.raw)
        if xId notin own: own[xId] = (x: l.x, lits: @[], ids: @[])
        own[xId].lits.add held(l.re, l.neg)
        own[xId].ids.add astId(ctx, c.raw)
    var inner = env
    var innerId = envId
    if own.len > 0:
      inc serial
      innerId = serial
      for xId, g in own:
        for h in g.lits: inner.mgetOrPut(xId, @[]).add h
    var drop: HashSet[int]
    var add: seq[Z3AnyAst]
    for xId, g in own:
      let above = env.getOrDefault(xId)
      # Negated as read: a negated literal asserted, or a plain one denied.
      var anyNeg = false
      for h in above: anyNeg = anyNeg or h.neg
      for h in g.lits: anyNeg = anyNeg or (h.neg != (pol == polNeg))
      if above.len + g.lits.len < 2 or not anyNeg: continue
      var a, i: seq[Z3AnyAst]
      for h in g.lits: a.add h.re
      for h in above: i.add h.re
      for id in g.ids: drop.incl id
      add.add(
        if pol == polPos: member(g.x, inter(a & i))
        else: mk(Z3_mk_not(ctx.raw,
                           member(g.x, inter(@[comp(inter(a))] & i)).raw)))
    var outs: seq[Z3AnyAst]
    var changed = add.len > 0
    for c in cs:
      if astId(ctx, c.raw) in drop: continue
      let b = if literal(c).ok: c else: rewrite(c, inner, innerId, pol, false)
      changed = changed or b.raw != c.raw
      outs.add b
    outs.add add
    result = if not changed: t else: andOf(outs)
    memo[key] = result
  for r in flat:
    # A root's top-level literals are the top level's (above); the rest of
    # it is rewritten with them held.
    var outs: seq[Z3AnyAst]
    var changed = false
    for c in conjuncts(toAnyAst(r)):
      # RFC-0005 S8ct: `holds` and `rewrite` recurse a level at a time, and a
      # conjunct left as it is has the same models. Only the merge is lost, so
      # at worst Z3 meets the memberships separately and answers unknown.
      var b = c
      if not literal(c).ok:
        if termTooDeep(ctx, c.raw):
          deepTermsLeftAlone.add termDepth(ctx, c.raw, cap = 100_000_000)
        else:
          b = rewrite(c, top, 0, polPos, false)
      changed = changed or b.raw != c.raw
      outs.add b
    result.add(if not changed: r else: wrap[Z3Bool](ctx, andOf(outs).raw))

var theoryFreeNeedsSimple* {.threadvar.}: tuple[ready: bool, simple: bool]
  ## RFC-0005 S8r. Whether `querySolver`'s `seqTheory = false` must use
  ## Z3's simple solver: probed once per thread against the linked Z3
  ## (`theoryFreeSimple`).

proc theoryFreeSimple*(): bool =
  ## RFC-0005 S8r. True when the linked Z3's default solver ignores
  ## `smt.string_solver = none` set as a solver parameter. Z3 4.13.4 (the
  ## symex-mingw leg's build) does: its default (combined) solver keeps the
  ## sequence theory, so `checkCapped`'s step 1b ran the UNCAPPED string
  ## query -- the search `maxSeqLen` exists to avoid, which does not poll
  ## `rlimit` -- and on `tsymex_163rev_intoffset_range` it grew past 10 GB
  ## (the corpus shard 2 runner loss since S8k). Z3 5.1's default solver
  ## honours the parameter; the simple solver honours it on both. Probe:
  ## `str.len(x) < 0` is UNSAT only under the sequence theory's length
  ## axiom, so a theory-free solver answers SAT.
  if not theoryFreeNeedsSimple.ready:
    let ctx = probeContext()   # RFC-0005 S8bp
    let x = mkStringVar(ctx, "__s8r_theory_free_probe")
    let lenX = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_seq_length(ctx.raw, x.raw))
    let s = newSolver(ctx)
    let p = newParams(ctx)
    p.set("rlimit", 100_000'u)
    p.set("random_seed", 0'u)
    p.set("smt.string_solver", "none")
    s.setParams(p)
    s.add lenX < mkInt(ctx, 0)
    theoryFreeNeedsSimple = (ready: true, simple: s.check() != zsSat)
  theoryFreeNeedsSimple.simple

const stallBackstopMs* {.intdefine: "nelliStallBackstopMs".} = 600_000
  ## RFC-0016 INT-57. The solver stall backstop: the wall-clock bound, in
  ## milliseconds, on the step-bounded solves (`rlimit` non-zero) of ONE run
  ## that has no run clock (`queryTimeoutMs = 0`, the pin settings). A step
  ## bound ends a search only while Z3 advances its step counter, and Z3 can
  ## stop advancing it (`len($t) + t + 129 <= 3` over the sequence solver,
  ## S8bu's mixed Int / bit-vector query); `walkRLimit` cannot end it either,
  ## since a check is charged only once it returns (`chargeWalkWork`). So the
  ## pin settings, which turn the run clock off, left such a solve unbounded:
  ## the walk was killed at 900 s. Z3 offers no thread-safe read of the
  ## counter during a check (`rlimit count` is a statistic, collected from
  ## the solver's own state), so a monitor cannot tell a stalled counter from
  ## a slow one; the backstop is Z3's own `timeout` (a timer thread that
  ## cancels the search, as `Z3_interrupt` does). It is a DEADLINE for the
  ## run, not a per-solve figure (`beginStallDeadline`): each solve gets what
  ## is left of it (`stallTimeoutMs`), so a walk of many stalling solves ends
  ## within it too, and once a solve is cut the walk stops (`walkStalled`,
  ## `shouldStop`). `600_000` is past where the step bounds end a search
  ## whose counter advances (the slowest measured, the sequence solver at
  ## 40-55k units/s, spends `seqQueryRLimit`'s 20M in about 6-8 minutes) and
  ## inside the 900 s a sweep allows a suite. A solve it ends is never a
  ## verdict: `zsUnknown`, `beSolverUndef` naming the backstop
  ## (`undefReason`), and the run is marked `rdQueryTimeout`
  ## (`solveBounded`), so its verdict is not cached, as a wall-clock cut
  ## never is; a sat or unsat answer never depends on it. A step-unbounded
  ## solve (`rlimit = 0`: the caller opted out of every step bound and
  ## `walkRLimit`) is left alone. `-d:nelliStallBackstopMs=N` lowers it for
  ## a suite that exercises it.


var stallDeadline* {.threadvar.}: StallDeadline
var walkStalled* {.threadvar.}: bool
  ## RFC-0016 INT-57. A solve of the current run was cut by the stall
  ## backstop; reset by `resetSymexRunState`. `shouldStop` ends the walk and
  ## `runSymexImpl` records the halt.

proc beginStallDeadline*(timeoutMs: uint): StallDeadline =
  ## RFC-0016 INT-57. Starts the run's stall deadline (no run clock only) and
  ## returns the one it replaces, for the run's exit to restore
  ## (`endStallDeadline`). A run begun inside another keeps the earlier of
  ## the two deadlines.
  result = stallDeadline
  if timeoutMs == 0'u and stallBackstopMs > 0:
    let t = getMonoTime().ticks + int64(stallBackstopMs) * 1_000_000'i64
    stallDeadline = StallDeadline(on: true,
      ticks: (if result.on: min(result.ticks, t) else: t))
  else:
    stallDeadline = StallDeadline(on: false)

proc endStallDeadline*(prev: StallDeadline) =
  ## RFC-0016 INT-57. The run is over: the deadline it replaced is back.
  stallDeadline = prev

proc stallTimeoutMs*(): uint =
  ## RFC-0016 INT-57. The `timeout` a step-bounded solve runs under with no
  ## run clock: what is left of the run's deadline (at least 1 ms: the
  ## deadline passed, the solve is cut at once), or outside a run the whole
  ## backstop.
  if not stallDeadline.on: return uint(stallBackstopMs)
  let left = (stallDeadline.ticks - getMonoTime().ticks) div 1_000_000'i64
  uint(max(1'i64, min(left, int64(stallBackstopMs))))

var queryTimeoutMsCur* {.threadvar.}: uint
  ## RFC-0005 S8bu. The run's `queryTimeoutMs`, set by `resetSymexRunState`:
  ## every solver `querySolver` builds runs under it. `0` (none) outside a
  ## run.
var nativeStackCutFlag* {.threadvar.}: bool
  ## RFC-0005 S8ca. Some call of the current run declined because the
  ## native stack left was under the walk's reserve (`nativeStackShort`);
  ## reset by `resetSymexRunState`. Like a clock cut-off its verdict is the
  ## machine's (the thread's stack), not only the program's: `runSymex` puts
  ## it on the result (`rdNativeStack`), which is what a save reads.

var queryTimedOutFlag* {.threadvar.}: bool
  ## RFC-0005 S8bu. Some solve of the current run was cut off by the clock
  ## (`solveBounded`); reset by `resetSymexRunState`. `runSymex` puts it on
  ## the result (`rdQueryTimeout`), which is what a save reads.

var walkerWorkBase* {.threadvar.}: int
  ## RFC-0016 K7. `walkerWorkUnits` when the current run began.
var walkUnitsBase* {.threadvar.}: int
  ## RFC-0016 K7. `ownContextUnits` when the current run began
  ## (`resetSymexRunState`): the walk's spend is the total's growth since.
var walkRLimitCur* {.threadvar.}: uint
  ## RFC-0016 K7. The run's `walkRLimit`, set by `resetSymexRunState`.
var walkWorkExhausted* {.threadvar.}: bool
  ## RFC-0016 K7. The run's solver checks together spent `walkRLimitCur`
  ## (`chargeWalkWork`); reset by `resetSymexRunState`. `shouldStop` reads it,
  ## `runSymexImpl` records the `ckWalkWork` halt.

var tailUnitsCeil* {.threadvar.}: int
  ## RFC-0016 W3-z R9. While a tail walk runs (`verifyTailDefined`), the
  ## `walkUnitsSpent` at which its own budget (`tailWalkCappedChecks`) is
  ## spent; `0` otherwise (no tail budget).
var tailWorkExhausted* {.threadvar.}: bool
  ## RFC-0016 W3-z R9. The running tail walk spent `tailUnitsCeil`
  ## (`chargeWalkWork`): `shouldStop` ends it and the tail fails closed.
var tailUnitsRun* {.threadvar.}: int
  ## RFC-0016 W3-z int4r. The units every tail walk of the current run has
  ## spent so far (`verifyTailDefinedKinds`); reset by `resetSymexRunState`.
  ## The tail budget (`tailWalkCappedChecks`) is the run's, not each walk's:
  ## a run walks one tail per replay candidate, and a per-walk budget let N
  ## candidates spend N budgets.

proc walkUnitsSpent*(): int {.inline.} =
  ## RFC-0016 K7. The Z3 units every own-context check of this run has spent.
  ownContextUnits - walkUnitsBase + walkerWorkUnits - walkerWorkBase

proc workLeftRLimit*(rlimit: uint): uint =
  ## RFC-0016 K7 / W3-z R9. `rlimit` (`0` none) lowered to what the walk has
  ## left under `walkRLimit` and, in a tail walk, under its own budget (at
  ## least 1: the work is spent and the walk stops, so a check decides
  ## nothing it need not), so one check cannot overshoot either total.
  result = rlimit
  let spent = walkUnitsSpent()
  if walkRLimitCur != 0:
    let left = if spent < 0 or uint(spent) >= walkRLimitCur: 1'u
               else: walkRLimitCur - uint(spent)
    if result == 0 or left < result: result = left
  if tailUnitsCeil != 0:
    let left = if spent >= tailUnitsCeil: 1'u else: uint(tailUnitsCeil - spent)
    if result == 0 or left < result: result = left

proc chargeWalkWork*() =
  ## RFC-0016 K7. Called after every own-context check (`ownContextCheck`,
  ## the one place a walk's Z3 units are counted): once the run's spend
  ## reaches `walkRLimit` the walk is out of work budget.
  let spent = walkUnitsSpent()
  if walkRLimitCur != 0 and spent >= 0 and uint(spent) >= walkRLimitCur:
    walkWorkExhausted = true
  if tailUnitsCeil != 0 and spent >= tailUnitsCeil:   ## RFC-0016 W3-z R9
    tailWorkExhausted = true

proc logWalkUnits*(target, status: string) =
  ## RFC-0016 K7. Hands the walk that just finished to the walk-units log
  ## sink (`walk_log`, which owns the destination and the format): the units
  ## it spent (its Z3 checks AND the walker-side charge, the budget
  ## `walkRLimit` bounds) and the part of them that is the walker-side charge.
  appendWalkUnits(WalkUnitsLine(
    units: walkUnitsSpent(), target: target, status: status,
    walkerUnits: walkerWorkUnits - walkerWorkBase, hasWalkerUnits: true))

proc solveBounded*(s: Z3Solver; assumptions: openArray[Z3Bool] = []): Z3Status =
  ## RFC-0005 S8bu. `s.check()` (under `assumptions`, `checkWith`), noting
  ## a solve the wall clock cut off (`queryTimeoutMs`).
  result = if assumptions.len == 0: s.check() else: s.checkWith(assumptions)
  if result == zsUnknown and s.reasonUnknown() == "timeout":
    queryTimedOutFlag = true
    # RFC-0016 INT-57: with no run clock it was the stall backstop; the run's
    # deadline is spent, so the walk stops (`shouldStop`).
    if queryTimeoutMsCur == 0'u: walkStalled = true

proc undefReason*(s: Z3Solver; timeoutMs: uint): string =
  ## RFC-0005 S8bu. Z3's `reason_unknown`, naming `queryTimeoutMs` when
  ## the clock ended the solve. RFC-0016 INT-59: with the units the solve
  ## had spent at the cut. A cut does not show that Z3 stopped advancing its
  ## step count: INT-59's trunc row, cut by a 15 s clock, was counting
  ## about 1M units a second (12,066,441 in 11.8 s on c) and was short of
  ## its bound. So the message claims only what it measured.
  result = "Z3: " & s.reasonUnknown()
  if result == "Z3: timeout":
    var units = -1'i64
    let st = s.getStatistics()
    if st.contains("rlimit count"):
      units = if st.isInt("rlimit count"): int64(st.getInt("rlimit count"))
              else: int64(st.getFloat("rlimit count"))
    let spent = (if units >= 0: " after " & $units & " rlimit units" else: "")
    if queryTimeoutMsCur == 0'u:
      # RFC-0016 INT-57: no run clock, so the stall backstop ended it.
      result.add " (solver stall backstop: the run had no answer within " &
        $stallBackstopMs & " ms with queryTimeoutMs = 0" & spent &
        ", and the step bound had not ended the solve; the run's, not " &
        "the program's)"
    else:
      result.add " (queryTimeoutMs = " & $timeoutMs & ": the run clock " &
        "ended the solve" & spent & ", before its step bound did)"

proc querySolver*(ctx: Z3Context; roots: openArray[Z3Bool];
                 rlimit: uint; seqTheory = true): Z3Solver =
  ## A fresh solver holding `roots`. Z3 bound: deterministic logical-step
  ## count (NOT wall-clock) so the same SUT + Z3 build produces identical
  ## outcomes across machines. `rlimit = 0` is Z3's documented
  ## "unbounded"; non-zero truncates to `Z3_L_UNDEF` (sxUnknown).
  ## `random_seed = 0'u` overrides any caller's `setGlobalParam` so the
  ## verdict cache's determinism guarantee doesn't depend on undocumented
  ## Z3 defaults. `seqTheory = false` (RFC-0005 S8k, `checkCapped`) runs
  ## the query with no sequence theory registered (`smt.string_solver =
  ## none`): every string / seq operation Z3's rewriter does not evaluate
  ## is an uninterpreted function, so the query's models are a SUPERSET of
  ## the real ones -- its UNSAT is the query's own, and it never searches
  ## for a string at all. RFC-0005 S8r: on a Z3 whose default solver
  ## ignores that parameter (4.13.4, `theoryFreeSimple`) it runs on the
  ## simple solver, which honours it.
  result = if not seqTheory and theoryFreeSimple(): newSimpleSolver(ctx)
           else: newSolver(ctx)
  let solverParams = newParams(ctx)
  solverParams.set("rlimit", rlimit)
  # RFC-0005 S8bu: and the run's wall-clock backstop (`queryTimeoutMs`).
  if queryTimeoutMsCur > 0'u: solverParams.set("timeout", queryTimeoutMsCur)
  elif rlimit > 0'u and stallBackstopMs > 0:
    # RFC-0016 INT-57: no run clock; the run's stall deadline bounds it.
    solverParams.set("timeout", stallTimeoutMs())
  solverParams.set("random_seed", 0'u)
  if not seqTheory:
    solverParams.set("smt.string_solver", "none")
  result.setParams(solverParams)
  for c in roots: result.add(c)

proc queryTermCount*(ctx: Z3Context; roots: openArray[Z3Bool]): int =
  ## RFC-0016 S8ci. The number of distinct terms of `roots`: what
  ## translating them into a context of their own visits, each once
  ## (`ownContextSolver`'s K7 charge). A function of the query alone.
  var done: HashSet[int]
  var stack: seq[Z3AnyAst]
  for c in roots: stack.add toAnyAst(c)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in done: continue
    done.incl id
    inc result
    if getAstKind(t) == akApp:
      for a in unpackApp(t).args: stack.add a

const eqsSplitShare* = (num: 7'u, den: 8'u)
  ## RFC-0016 S8ci. The share of an own-context search's bound that Z3's
  ## defaults get before `ownContextCheck` searches on without the cheap
  ## equality search: seven eighths, the least share tried (one half, three
  ## quarters, seven eighths) that loses no pinned UNSAT (see
  ## `ownContextCheck`).

proc eqsSplitFirst*(rlimit: uint): uint =
  ## The part of `rlimit` Z3's defaults get: at least `eqsSplitShare` of
  ## it, rounded up, and never more than `rlimit`. Written so a large
  ## bound cannot overflow.
  rlimit - (rlimit div eqsSplitShare.den) * (eqsSplitShare.den - eqsSplitShare.num)

var eqsSplitCaps* {.threadvar.}: Table[pointer, uint]
  ## RFC-0016 S8ci. The whole bound of each `ownContextSolver` solver not
  ## yet checked, keyed by the solver: the solver itself carries only its
  ## first share (`eqsSplitFirst`, see `ownContextSolver`), and
  ## `ownContextCheck` gives a search that share did not decide the rest.
  ## Removed when it is checked.

when defined(symexQueryStats):
  var symexEqsSplits* {.threadvar.}: int
    ## RFC-0016 S8ci. The own-context checks whose first share ran out undecided
    ## and were searched on without Z3's cheap equality search
    ## (`ownContextCheck`). Never reset by the engine.

proc ownContextSolver*(ctx: Z3Context; roots: openArray[Z3Bool];
                      rlimit: uint; seqTheory = true): Z3Solver =
  ## RFC-0005 S8bm. `querySolver`'s solver for `roots`, in a fresh Z3
  ## context of its own: `roots` (terms of the walk's context `ctx`) are
  ## translated into it, so its search starts from the query's text alone
  ## and not from what the walk's shared context already holds (see
  ## `checkCapped`). A model is translated back with `translate(m, ctx)`.
  ## `newContext` makes the new context the thread's current one; the
  ## walk's is restored. RFC-0005 S8bp: every `checkCapped` step's solver,
  ## the theory-free ones (`seqTheory = false`) included.
  ##
  ## RFC-0016 S8ci: the roots are translated as one vector (one cache), so
  ## the query's terms are made in the new context in Z3's own translation
  ## order, a function of the query alone. The order moves the search, so
  ## the units as well as the wall time a unit costs (and the units follow
  ## the process's Z3 memory too, RFC-0016 S8cj). Three orders were
  ## measured over 54 (suite, Z3) cells, the heaviest solver-bound tsymex
  ## suites on Z3 5.1 and 4.13.4: S8by's (the roots in order, each term's
  ## arguments last to first) 1,992.7M Z3 units; the walk context's
  ## creation order (ids ascending) 1,540.9M; Z3's 1,464.7M, the least,
  ## and the least summed CPU time (967 s against 1,138 s and 990 s). The
  ## creation order won some cells, but no choice between the two earns a
  ## rule: picking the better of them per cell would save 2.6%. Z3's
  ## order costs `r4_strip` wall time (118.7 s against S8by's 108.5 s and
  ## S8bm's 86.7 s, Z3 5.1, side by side); its units are the same in
  ## every order (a budget-out step).
  let prev = currentContext()
  let own = newContext()
  setCurrentContext(prev)
  chargeWalkerTerms(queryTermCount(ctx, roots))   ## RFC-0016 K7: one translate visit per term
  walkerWorkUnits += walkerContextUnits            ## RFC-0016 int6 D1b: the solver's fixed cost
  let terms = newAstVector(ctx)
  for c in roots: terms.add toAnyAst(c)
  let made = translate(terms, own)
  var inOwn = newSeq[Z3Bool](roots.len)
  for i in 0 ..< roots.len: inOwn[i] = wrap[Z3Bool](own, made[i])
  result = querySolver(own, inOwn, rlimit, seqTheory)
  # RFC-0016 S8ci: Z3's defaults get the first share of the bound; the
  # rest is `ownContextCheck`'s, without the cheap equality search.
  if rlimit > 1'u and eqsSplitFirst(rlimit) < rlimit:
    let first = newParams(own)
    first.set("rlimit", eqsSplitFirst(rlimit))
    result.setParams(first)
    eqsSplitCaps[cast[pointer](result)] = rlimit

when defined(symexTestInjectWalkerFault):
  proc injectedSolveFaultTerms*(s: Z3Solver): seq[Z3Bool] =
    ## RFC-0005 batch 8 fault injection (see `ownContextCheck`): raises with a
    ## Z3 term in its result, which the caller destroys on the raise path.
    result = @[mkBool(s.ctx, true)]
    raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for the batch 8 own-context solve test)]
      "batch 8 synthetic swallowed solve fault (symexTestInjectWalkerFault)")

proc ownContextCheck*(s: Z3Solver;
                     assumptions: openArray[Z3Bool] = []): Z3Status =
  ## RFC-0005 S8bm. `s.check()` (RFC-0005 S8bp: under `assumptions`, terms
  ## of `s`'s context, when there are any) for an `ownContextSolver`, its
  ## context's whole step count (nothing else ran there) added to
  ## `ownContextUnits`. RFC-0005 batch 7: the check is S8bu's
  ## `solveBounded`, so a solve the clock cut off is noted here too.
  ##
  ## RFC-0016 S8ci. With `smt.arith.propagate_eqs` on (Z3's default), every
  ## LP bound propagation runs `lp_bound_propagator::cheap_eq_on_nbase` over
  ## the touched rows and explains each equality it finds by walking its
  ## row (`lar_solver::explain_fixed_in_row`); none of that advances
  ## `rlimit`, so a unit's wall time grows with the tableau's rows, which
  ## follow the order the query's terms were made in (`r4_strip`'s
  ## budget-out step 3: 228 of 300 stack samples there, Z3 5.1.0; 45 s in
  ## S8bm's term order, 71 s in S8bp's, the same units). Turning it off
  ## everywhere bounds that, but loses what it decides cheaply
  ## (`s8bb_replace_d` 3.8M units to 26.5M and red). So the search is
  ## split: Z3's defaults under the first share of the bound
  ## (`eqsSplitShare`, `ownContextSolver`), and only a search that share ran
  ## out on goes on, on the same solver, without the equality search, under
  ## what the bound has left. A query decided within its first share is
  ## searched exactly as before; one that spends its whole bound spends the
  ## rest where a unit costs about the same wall time in any term order. The
  ## units counted are the context's whole step count, both parts.
  ##
  ## The share is seven eighths, by measurement: at one half,
  ## `s8aq_rfind_before_piece` and `grow_stale_dead` (UNSATs Z3's defaults
  ## reach only past half the bound) were lost; at three quarters the first
  ## still was. At seven eighths `r4_strip` runs 82.0 s / 81.6 s against the
  ## unsplit 108.2 s / 107.5 s and S8bm's 84.0 s / 83.8 s (eos, Z3 5.1, side
  ## by side, 2 reps; units unchanged).
  when defined(symexTestInjectWalkerFault):
    # RFC-0005 batch 8 fault injection (compiled out of every normal build):
    # a query over a parameter named for the shape raises, as `extractLeaf`'s
    # for extraction: straight out of the solve, or in a callee whose result
    # the C backend destroys on the raise path, which loses it here.
    let shown = $s
    if "injectSolveFault" in shown:
      raise newException(ValueError,  # [raise-audited: category-c: test-injection-only (compiled out of every normal build; only present under -d:symexTestInjectWalkerFault, wired for the batch 8 own-context solve test)]
        "batch 8 synthetic solve fault (symexTestInjectWalkerFault)")
    if "injectSwallowedSolveFault" in shown:
      var held = @[mkBool(s.ctx, false)]
      held = injectedSolveFaultTerms(s)
      discard held
  result = solveBounded(s, assumptions)
  var st = s.getStatistics()
  proc spentIn(st: Z3Stats): uint =
    if not st.contains("rlimit count"): 0'u
    elif st.isInt("rlimit count"): uint(st.getInt("rlimit count"))
    else: uint(st.getFloat("rlimit count"))
  var cap: uint
  if eqsSplitCaps.pop(cast[pointer](s), cap) and result == zsUnknown:
    let spent = spentIn(st)
    if spent >= eqsSplitFirst(cap) and spent < cap:
      let rest = newParams(s.ctx)
      rest.set("rlimit", cap - spent)
      rest.set("smt.arith.propagate_eqs", false)
      s.setParams(rest)
      when defined(symexQueryStats): inc symexEqsSplits
      result = solveBounded(s, assumptions)
      st = s.getStatistics()
  ownContextUnits += int(spentIn(st))
  chargeWalkWork()   ## RFC-0016 K7

var intDivDeclKinds* {.threadvar.}:
    tuple[ready: bool, idiv, imod, bv2nat, sbv2int, bvneg, bvsub, bvadd: int]
  ## RFC-0005 S8ad. The `Z3_decl_kind` ordinals `divRangeFacts` matches on
  ## (Int `div` and `mod`, unsigned and signed `bv2int`, `bvneg`, `bvsub`),
  ## read off
  ## terms built once per thread, as `seqCapKinds` does: the header's values
  ## are positional, so they are taken from the linked Z3 itself. A signed
  ## `bv2int` that Z3 expands (to an `ite` over the unsigned one, as Z3 5.1
  ## does) has the `ite`'s kind; `divRangeFacts` only matches it with one
  ## argument, which an `ite` never has, and meets the unsigned one inside.
  ## RFC-0005 S8bd: and `bvadd`, for `bvOffsetLinks`.

proc ensureIntDivDeclKinds*() =
  if intDivDeclKinds.ready: return
  let ctx = probeContext()   # RFC-0005 S8bp
  proc kindOf(ctx: Z3Context; a: RawZ3Ast): int =
    ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, Z3_to_app(ctx.raw, a))))
  let x = mkIntVar(ctx, "__s8ad_kind_probe_a")
  let y = mkIntVar(ctx, "__s8ad_kind_probe_b")
  let v = mkBitVecVar[8](ctx, "__s8ad_kind_probe_v")
  intDivDeclKinds = (ready: true, idiv: kindOf(ctx, (x div y).raw),
    imod: kindOf(ctx, (x mod y).raw),
    bv2nat: kindOf(ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, v.raw, false)),
    sbv2int: kindOf(ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, v.raw, true)),
    bvneg: kindOf(ctx, (-v).raw), bvsub: kindOf(ctx, (v - v).raw),
    bvadd: kindOf(ctx, (v + v).raw))

proc divRangeFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8ad. Linear bounds on every Int quotient `e = a div b` and
  ## remainder `r = a mod b` in `roots`. Z3's Int `div`/`mod` are Euclidean
  ## (`a = b*e + r`, `0 <= r < |b|`); for a divisor of known sign both lie
  ## between linear functions of the operands:
  ##   b >= 1:           0 <= r <= b - 1
  ##   b <= -1:          0 <= r <= -b - 1
  ##   b != 0, a >= 0:   r <= a
  ##   b >= 1, a >= 0:   0 <= e <= a,     and  2e <= a      when b >= 2
  ##   b >= 1, a <  0:   a <= e <= -1,    and  a <= 2e + 1  when b >= 2
  ##   b <= -1, a >= 0:  -a <= e <= 0,    and  -a <= 2e     when b <= -2
  ##   b <= -1, a <  0:  1 <= e <= -a,    and  2e <= 1 - a  when b <= -2
  ## and, when `|a| < |b|`, the pair itself:
  ##   b >= 1,  0 <= a <= b - 1:   e == 0,   r == a
  ##   b >= 1,  -b <= a <= -1:     e == -1,  r == a + b
  ##   b <= -1, 0 <= a <= -b - 1:  e == 0,   r == a
  ##   b <= -1, b <= a <= -1:      e == 1,   r == a - b
  ## and, for a negated bitvector `y` (`bvneg y`, or `0 - y`, which is how
  ## Nim's `-y` lowers) of width W read as an Int:
  ##   ubv2int(-y) == (if y == 0: 0 else: 2^W - ubv2int(y))
  ##   sbv2int(-y) == (if y == low: sbv2int(y) else: -sbv2int(y))
  ## and (RFC-0005 S8aj) one window further up, `|b| <= a < 2|b|`:
  ##   b >= 1,  b <= a <= 2b - 1:         e == 1,   r == a - b
  ##   b <= -1, -b <= a <= -2b - 1:       e == -1,  r == a + b
  ## Each holds for every `a` and `b` (a theorem of the Euclidean pair, or
  ## of two's complement, not a constraint on the input), so asserting them
  ## beside the query leaves its models exactly as they were. `tests/tsymex_rfc0005_s8ad_remainder.nim`
  ## checks every one against Z3's own `div` on a grid of numerals.
  ##
  ## Why: Z3 relates `a div b` to `a` only through the product `b*e`, i.e.
  ## its nonlinear core. Under a sequence query, or with `b` a `bv2int`
  ## (a width-stamped scan offset divided by a bitvector parameter,
  ## `truncDivInt`), that core did not refute `start < 0 and y > 1 and
  ## start div y == start` within 40M steps -- nor its theory-free
  ## re-check (`checkCapped` step 1b) -- so the verdict was `sxUnknown`
  ## (`beSolverUndef`). The bounds make that refutation linear. The
  ## negation facts serve the remainder's twin, `start mod y <= -y`: `-y`
  ## is the bitvector negation of the parameter, and Z3 did not connect its
  ## `bv2int` to `y`'s beside the remainder within 40M steps either. The
  ## `|a| < |b|` pair is for Z3 4.13.4 (symex-mingw): with `start < 0`,
  ## `truncDivInt`'s quotient is `start` only at `e == start == -1` with
  ## `r == 0`, and 4.13.4 did not find `r == y - 1` there within 40M steps.
  ## The window above is for unchecked arithmetic: `wrapIntToWidth` wraps
  ## an Int sum as `lo + (r - lo) mod 2^W`, and a sum of two in-range
  ## operands that overflows puts `r - lo` in `[2^W, 2^(W+1))`, just past
  ## the `|a| < |b|` pair (an underflow lands in `negSmall`). With a
  ## `bv2int(y + 1)` operand (`start >= 0 and y > 1 and start + (y + 1) ==
  ## start`, UNSAT) neither 5.1 nor 4.13.4 refuted it within 40M steps;
  ## with this pair it is 0.45M offline. Linking `bv2int(y + 1)` to
  ## `bv2int(y)` (and likewise for `-`, `*`, shifts) did not decide it
  ## and made other queries dearer, so it is not asserted. (RFC-0005 S8bd:
  ## it is, for a `+`/`-` numeral, between two views the query already
  ## holds -- `bvOffsetLinks`.)
  ensureIntDivDeclKinds()
  let kinds = intDivDeclKinds
  let (idiv, imod) = (kinds.idiv, kinds.imod)
  let zero = mkInt(ctx, 0)
  let one = mkInt(ctx, 1)
  let two = mkInt(ctx, 2)
  var seen: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    for a in args: stack.add a
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    proc negated(ctx: Z3Context; x: Z3AnyAst): Option[Z3AnyAst] =
      ## `y` when `x` is `bvneg y` or `0 - y`.
      if getAstKind(x) != akApp: return none(Z3AnyAst)
      let (d, xs) = unpackApp(x)
      let xk = ord(Z3_get_decl_kind(ctx.raw, d))
      if xk == kinds.bvneg and xs.len == 1: return some(xs[0])
      if xk == kinds.bvsub and xs.len == 2 and getAstKind(xs[0]) == akNumeral and
         $Z3_get_numeral_string(ctx.raw, xs[0].raw) == "0":
        return some(xs[1])
      none(Z3AnyAst)
    let yNeg = if (k == kinds.bv2nat or k == kinds.sbv2int) and args.len == 1:
                 negated(ctx, args[0])
               else: none(Z3AnyAst)
    if yNeg.isSome:
      # `bv2int(-y)`, unsigned or signed (see the doc comment).
      let signed = k == kinds.sbv2int and kinds.sbv2int != kinds.bv2nat
      let yRaw = yNeg.get.raw
      let ySort = ctx.checkErr Z3_get_sort(ctx.raw, yRaw)
      let w = int(Z3_get_bv_sort_size(ctx.raw, ySort))
      let yInt = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, yRaw, signed))
      let tInt = wrap[Z3Int](ctx, t.raw)
      proc bvNum(text: string): RawZ3Ast =
        ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring, ySort)
      if signed:
        # `low` of width W is the bit pattern 2^(W-1) (W <= 64 here).
        let isLow = wrap[Z3Bool](ctx, checkedEq(ctx, yRaw,
          bvNum($(1'u64 shl (w - 1)))))
        result.add tInt == ite(isLow, yInt, zero - yInt)
      else:
        let isZero = wrap[Z3Bool](ctx, checkedEq(ctx, yRaw, bvNum("0")))
        let twoWText = if w >= 64: "18446744073709551616" else: $(1'u64 shl w)
        let twoW = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw,
          twoWText.cstring, ctx.checkErr Z3_mk_int_sort(ctx.raw)))
        result.add tInt == ite(isZero, zero, twoW - yInt)
      continue
    if (k != idiv and k != imod) or args.len != 2 or getSortKind(t) != skInt:
      continue
    let e = wrap[Z3Int](ctx, t.raw)
    let a = wrap[Z3Int](ctx, args[0].raw)
    let b = wrap[Z3Int](ctx, args[1].raw)
    # `|a| < |b|`: the quotient is 0 or +-1 and the pair is linear in `a`.
    let posSmall = (b >= one) and (zero <= a) and (a <= b - one)
    let negSmall = (b >= one) and (zero - b <= a) and (a <= zero - one)
    let posSmallN = (b <= zero - one) and (zero <= a) and (a <= zero - one - b)
    let negSmallN = (b <= zero - one) and (b <= a) and (a <= zero - one)
    # S8aj: `|b| <= a < 2|b|`, the quotient is +-1 (see the doc comment).
    let posNext = (b >= one) and (b <= a) and (a <= two * b - one)
    let posNextN = (b <= zero - one) and (zero - b <= a) and
                   (a <= zero - two * b - one)
    if k == imod:
      result.add implies(posNext, e == a - b)
      result.add implies(posNextN, e == a + b)
      result.add implies(b >= one, (zero <= e) and (e <= b - one))
      result.add implies(b <= zero - one, (zero <= e) and (e <= zero - one - b))
      result.add implies((b != zero) and (a >= zero), e <= a)
      result.add implies(posSmall, e == a)
      result.add implies(negSmall, e == a + b)
      result.add implies(posSmallN, e == a)
      result.add implies(negSmallN, e == a - b)
      continue
    result.add implies(posSmall, e == zero)
    result.add implies(negSmall, e == zero - one)
    result.add implies(posSmallN, e == zero)
    result.add implies(negSmallN, e == one)
    result.add implies(posNext, e == one)
    result.add implies(posNextN, e == zero - one)
    let twoE = two * e
    result.add implies((b >= one) and (a >= zero), (zero <= e) and (e <= a))
    result.add implies((b >= two) and (a >= zero), twoE <= a)
    result.add implies((b >= one) and (a < zero), (a <= e) and (e <= zero - one))
    result.add implies((b >= two) and (a < zero), a <= twoE + one)
    result.add implies((b <= zero - one) and (a >= zero),
                       (zero - a <= e) and (e <= zero))
    result.add implies((b <= zero - two) and (a >= zero), zero - a <= twoE)
    result.add implies((b <= zero - one) and (a < zero),
                       (one <= e) and (e <= zero - a))
    result.add implies((b <= zero - two) and (a < zero), twoE <= one - a)

const factsFirstRLimit* = 1_000_000'u
  ## RFC-0005 S8ay (item 6). The budget of `checkCapped`'s facts-first
  ## check (step 1c's uncapped half, run before step 1). Small on purpose:
  ## it only lets a refutation that needs no string search answer before
  ## the full-theory search; one it cannot finish here is still tried
  ## with the whole budget after step 1. S8aw's join refutations took a
  ## few thousand units on Z3 5.1 and 4.13.4.
proc bvOffsetLinks*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8bd. For every Int view `bv2int(x + c)` or `bv2int(x - c)`
  ## in `roots` (`c` a bit-vector numeral, `bvadd` in either operand
  ## order) whose operand's own view `bv2int(x)` is in `roots` too, read
  ## the same way (unsigned, or Z3's one-argument signed `bv2int` where it
  ## has one), the exact two's-complement link between the two views, at
  ## width W:
  ##   unsigned:  ubv2int(x + c) == (let v = ubv2int(x) + c;
  ##                                 if v >= 2^W: v - 2^W else: v)
  ##              ubv2int(x - c) == (let v = ubv2int(x) - c;
  ##                                 if v < 0: v + 2^W else: v)
  ##   signed:    sbv2int(x +- c) == (let v = sbv2int(x) +- c;
  ##                                  if v > high: v - 2^W
  ##                                  elif v < low: v + 2^W else: v)
  ## with `c` read the same way as `x`. Each is a theorem of bit-vector
  ## arithmetic (a definition of the wrap, not a constraint on the input),
  ## so asserting them beside the query leaves its models as they were.
  ## `tests/tsymex_rfc0005_s8bd_remainder.nim` checks every one against
  ## Z3's own `bv2int` on a grid of numerals.
  ##
  ## Why: a string index `i` that is a bit-vector (an `int` parameter whose
  ## `i + 1` can overflow) meets `s.len` through two Int views, `bv2int(i)`
  ## (`i < s.len`) and `bv2int(i + 1)` (`i + 1 > s.len`), and Z3 relates
  ## the two only by bit-blasting the conversion. `i >= 0 and i < s.len and
  ## s[i] == 'a' and i + 1 > s.len` ran ~41M units to `sxUnknown`
  ## (`beSolverUndef`) on both Z3 versions, in both integer encodings; the
  ## character read was not the cost (without it, the same). The label
  ## query replayed offline from its SMT-LIB text decides in 0.77M units
  ## on 5.1 and 2.77M on 4.13.4, but in the walker's context it ran past
  ## the whole budget; with this link, 2.8k and 4.0k offline.
  ##
  ## Only a pair whose both views are in the query is linked. RFC-0005 S8aj
  ## measured the general link (`bv2int(y + 1)` to a `bv2int(y)` the query
  ## did not hold) and rejected it: `(start + y) div (y + 1) > start` went
  ## from 6.6M to 31.6M units on 5.1. There `y` is only compared as a
  ## bit-vector (`y > 1`), so its Int view is new to the query, and the
  ## link would bring it in; here both views are already terms Z3 must
  ## reconcile, and the link states how.
  ensureIntDivDeclKinds()
  let kinds = intDivDeclKinds
  let signedKind = kinds.sbv2int != kinds.bv2nat
  var viewed: HashSet[(int, bool)]
  var views: seq[tuple[t, arg: Z3AnyAst, signed: bool]]
  var seen: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    for a in args: stack.add a
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    if args.len == 1 and (k == kinds.bv2nat or (signedKind and k == kinds.sbv2int)):
      let signed = signedKind and k == kinds.sbv2int
      viewed.incl (astId(ctx, args[0].raw), signed)
      views.add (t: t, arg: args[0], signed: signed)
  if views.len < 2: return
  let intSort = ctx.checkErr Z3_mk_int_sort(ctx.raw)
  proc intText(text: string): Z3Int =
    wrap[Z3Int](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring, intSort))
  proc pow2(e: int): string =
    ## 2^e as decimal text, 1 <= e <= 64.
    if e >= 64: "18446744073709551616" else: $(1'u64 shl e)
  for v in views:
    if getAstKind(v.arg) != akApp: continue
    let (d, xs) = unpackApp(v.arg)
    if xs.len != 2: continue
    let ak = ord(Z3_get_decl_kind(ctx.raw, d))
    var x, c: Z3AnyAst
    var plus: bool
    if ak == kinds.bvadd and isNumeralAst(ctx, xs[1].raw):
      (x, c, plus) = (xs[0], xs[1], true)
    elif ak == kinds.bvadd and isNumeralAst(ctx, xs[0].raw):
      (x, c, plus) = (xs[1], xs[0], true)
    elif ak == kinds.bvsub and isNumeralAst(ctx, xs[1].raw):
      (x, c, plus) = (xs[0], xs[1], false)
    else: continue
    if isNumeralAst(ctx, x.raw): continue
    if (astId(ctx, x.raw), v.signed) notin viewed: continue
    let w = int(Z3_get_bv_sort_size(ctx.raw,
                  ctx.checkErr Z3_get_sort(ctx.raw, x.raw)))
    if w < 1 or w > 64: continue
    let cu = parseBiggestUInt($Z3_get_numeral_string(ctx.raw, c.raw))
    let cText =
      if v.signed and cu >= (1'u64 shl (w - 1)):
        "-" & (if w == 64: $((not cu) + 1) else: $((1'u64 shl w) - cu))
      else: $cu
    let xInt = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw,
                                                         v.signed))
    let tInt = wrap[Z3Int](ctx, v.t.raw)
    let cInt = intText(cText)
    let span = intText(pow2(w))
    let sum = if plus: xInt + cInt else: xInt - cInt
    if v.signed:
      let hi = intText($((1'u64 shl (w - 1)) - 1))
      let lo = intText("-" & pow2(w - 1))
      result.add tInt == ite(sum > hi, sum - span,
                             ite(sum < lo, sum + span, sum))
    else:
      let zero = intText("0")
      result.add tInt == ite(sum >= span, sum - span,
                             ite(sum < zero, sum + span, sum))

var int2bvDeclKind* {.threadvar.}: int
  ## RFC-0005 S8bu. The `Z3_decl_kind` ordinal (+ 1) of `int2bv`, read off a
  ## probe term as `intDivDeclKinds` are.
var eqDeclKind* {.threadvar.}: int
  ## RFC-0005 S8bu. The same, of `=`.


proc bvIntInverseFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0005 S8bu. Facts that let Z3 invert the signed Int view `sbv2int`
  ## of the bit-vectors in `roots`, each a theorem of two's complement (the
  ## view is injective, and `int2bv` takes its argument mod 2^W), so
  ## asserting them beside the query leaves its models as they were:
  ##   * for every `int2bv_W(t)` term in `roots` whose `t` is `sbv2int(x)`,
  ##     with `x` of width W:  int2bv_W(t) == x;
  ##   * for every equality `a == b` in `roots` whose `a` is `sbv2int(x)`
  ##     and `b` is `sbv2int(y)`, `x` and `y` of one width:
  ##     a == b  implies  x == y;
  ## where a term "is" a view when it is one once each `select(store(h, i,
  ## v), i)` in it is read as `v` (`peelSelect`; a theorem of arrays, so
  ## each fact stays one): an `int` stored into a heap cell and read back
  ## out of it is that store's view.
  ## Neither brings a term the query does not hold: an `int2bv` of every
  ## view (the first form for every view, before) made Z3 bit-blast Int
  ## arithmetic, and `tsymex_rfc0005_s8ad_remainder`'s quotient queries
  ## stopped advancing Z3's step counter; the second form for every pair of
  ## views took 4.13.4 past those queries' step pins. `tests/tsymex_rfc0005_s8bu_term.nim`
  ## checks both forms valid at width 8. A view is found as the term
  ## `Z3_mk_bv2int(x, true)` builds: Z3 shares equal terms, so the view the
  ## walker built (`bvTermToZ3Int`) and the one built here are the same AST,
  ## whether the linked Z3 keeps the signed `bv2int` as one operator or
  ## expands it (to an `ite` over the unsigned one, as Z3 5.1 and 4.13.4 do).
  ##
  ## Why: an `int` stored in an Int-sorted heap (`intHeapCell`) crosses the
  ## sort boundary through the signed view, and a callee's result read back
  ## from it is linked to a bit-vector either by `sbv2int(r) == sbv2int(k)`
  ## or by `r == int2bv(sbv2int(k))`. With `r != k` both are UNSAT, but Z3
  ## refutes them only through the injectivity of the expanded `ite`, which
  ## neither 5.1 nor 4.13.4 found within 3M units; with these facts each
  ## decides in a few hundred (the unsigned view needs none: Z3 asserts
  ## `int2bv(ubv2int(x)) == x` itself). Under the then-unbounded default
  ## `queryRLimit` the walk never terminated (S8bs's int-field and
  ## `seq[int]` SUTs).
  ensureIntDivDeclKinds()
  if int2bvDeclKind == 0 or eqDeclKind == 0:
    # RFC-0005 batch 7: probed in a context of its own (S8bp's
    # `probeContext`), not the walk's.
    let pc = probeContext()
    let probe = mkIntVar(pc, "__s8bu_int2bv_probe")
    let t = pc.checkErr Z3_mk_int2bv(pc.raw, 8, probe.raw)
    int2bvDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, t)))) + 1
    let pa = mkIntVar(pc, "__s8bu_eq_probe_a")
    let pb = mkIntVar(pc, "__s8bu_eq_probe_b")
    let e = checkedEq(pc, pa.raw, pb.raw)
    eqDeclKind = ord(Z3_get_decl_kind(pc.raw,
      Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, e)))) + 1
  let bv2nat = intDivDeclKinds.bv2nat
  var seen: HashSet[int]
  var args1: seq[Z3AnyAst]
  var backs: seq[Z3AnyAst]   ## the `int2bv` terms
  var eqs: seq[Z3AnyAst]     ## the equalities
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    for a in args: stack.add a
    let k = ord(Z3_get_decl_kind(ctx.raw, decl))
    if args.len == 1 and k == bv2nat and not isNumeralAst(ctx, args[0].raw):
      args1.add args[0]
    elif args.len == 1 and k + 1 == int2bvDeclKind:
      backs.add t
    elif args.len == 2 and k + 1 == eqDeclKind:
      eqs.add t
  var done: HashSet[int]
  var views: seq[tuple[x, sv: Z3AnyAst; w: cuint]]
  for x in args1:
    let xid = astId(ctx, x.raw)
    if xid in done: continue
    done.incl xid
    let sv = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw, true))
    if astId(ctx, sv.raw) notin seen: continue
    views.add (x: x, sv: sv,
               w: Z3_get_bv_sort_size(ctx.raw, ctx.checkErr Z3_get_sort(ctx.raw, x.raw)))
  if views.len == 0: return
  var viewIx: Table[int, int]   ## a view's AST id -> its index in `views`
  for i, v in views: viewIx[astId(ctx, v.sv.raw)] = i
  template viewOf(t: Z3AnyAst): int =
    ## The index in `views` of the view `t` is (`peelSelect`), else -1.
    viewIx.getOrDefault(astId(ctx, peelSelect(ctx, t.raw)), -1)
  for t in backs:
    let (_, args) = unpackApp(t)
    let w = Z3_get_bv_sort_size(ctx.raw, ctx.checkErr Z3_get_sort(ctx.raw, t.raw))
    let i = viewOf(args[0])
    if i >= 0 and views[i].w == w:
      result.add wrap[Z3Bool](ctx, checkedEq(ctx, t.raw, views[i].x.raw))
  var paired: HashSet[(int, int)]
  for t in eqs:
    let (_, args) = unpackApp(t)
    let i = viewOf(args[0])
    let j = viewOf(args[1])
    if i < 0 or j < 0 or i == j or views[i].w != views[j].w: continue
    if (i, j) in paired: continue
    paired.incl (i, j)
    let eq = checkedEq(ctx, views[i].x.raw, views[j].x.raw)
    result.add wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_implies(ctx.raw, t.raw, eq))

var bvExtDeclKinds* {.threadvar.}: tuple[ready: bool, zext, sext, iteK: int]
  ## RFC-0016 INT-62. The `Z3_decl_kind` ordinals of `zero_extend`,
  ## `sign_extend` and `ite`, read off probe terms (as `intDivDeclKinds`).

const maxViewRangeFacts* = 64
  ## RFC-0016 INT-62. The most views `bvViewRangeFacts` ranges in one query
  ## (two facts each).

proc bvViewRangeFacts*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0016 INT-62. For every signed Int view `v = sbv2int(x)` in `roots`
  ## (an `int` as Int arithmetic sees it, `bvTermToZ3Int`) whose `x` has a
  ## range its own structure gives, `lo <= v and v <= hi`. The range of a
  ## `W`-bit term, read through each `select(store(a, i, y), i)` as `y`
  ## (`peelSelect`, a theorem of arrays):
  ##   - a numeral: its signed value;
  ##   - a builtin set's `card` over `n` bits (`bsCard`): [0, n];
  ##   - a zero extension of a `w`-bit term, `w` < W: [0, 2^w - 1];
  ##   - a sign extension of a `w`-bit term, `w` < W:
  ##     [-2^(w-1), 2^(w-1) - 1];
  ##   - `bvadd` / `bvsub` of ranged operands: the integer sum's or
  ##     difference's range, when it lies in W bits' signed range (then the
  ##     operation does not wrap, and its value is the integer one);
  ##   - `ite(c, a, b)` of ranged arms: the union.
  ## Anything else (an input, a product, a sum that may wrap) has none.
  ## Bounds are kept within [-2^62, 2^62]. Each fact is a theorem of two's
  ## complement (and, for `card`, of counting: at most `n` of `n` bits are
  ## set), so the query's models are its own (as `bitSetCardFacts`').
  ## `cardFreeAbstraction` asserts them beside a query whose counts it has
  ## replaced by free variables: there they are what an `int`
  ## accumulator's overflow side needs, `acc + c1[1] + 2 + card(x2)`
  ## leaving the `int` range being linear arithmetic over ranged views.
  ## Without the ranges Z3 refuted that side only by bit-blasting the
  ## 256-bit set beside the seq element (about 4M units for each of two
  ## sides once a `set[char]` row joined a `seq` row). They are not added to
  ## every query: beside the set's own bit-blast they did not make the
  ## packed program's sides cheaper than about 150k units each.
  ensureIntDivDeclKinds()
  if not bvExtDeclKinds.ready:
    let pc = probeContext()
    let v = mkBitVecVar[8](pc, "__int62_ext_probe")
    let v2 = mkBitVecVar[8](pc, "__int62_ext_probe2")
    proc kindOf(a: RawZ3Ast): int =
      ord(Z3_get_decl_kind(pc.raw, Z3_get_app_decl(pc.raw, Z3_to_app(pc.raw, a))))
    bvExtDeclKinds = (ready: true,
      zext: kindOf(pc.checkErr Z3_mk_zero_ext(pc.raw, 8, v.raw)),
      sext: kindOf(pc.checkErr Z3_mk_sign_ext(pc.raw, 8, v.raw)),
      iteK: kindOf(checkedIte(pc,
        pc.checkErr(Z3_mk_bvslt(pc.raw, v.raw, v2.raw)), v.raw, v2.raw)))
  let bv2nat = intDivDeclKinds.bv2nat
  var seen: HashSet[int]
  var args1: seq[RawZ3Ast]
  var stack: seq[RawZ3Ast]
  for r in roots: stack.add r.raw
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, t)
    let n = int(Z3_get_app_num_args(ctx.raw, app))
    for i in 0 ..< n: stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
    if n == 1 and ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw,
        app))) == bv2nat:
      args1.add Z3_get_app_arg(ctx.raw, app, 0)
  const lim = 1'i64 shl 62
    # Every bound is kept within [-2^62, 2^62], so two bounds add or
    # subtract without overflowing an `int64`.
  type Rng = tuple[ok: bool, lo, hi: int64]
  var memo = initTable[int, Rng]()
  proc fit(lo, hi: int64; w: int): Rng =
    ## `[lo, hi]` when it lies in the signed range of `w` bits and in
    ## [-2^62, 2^62]: then the bit-vector operation that produced it did
    ## not wrap, and its value is the integer one. At 63 bits the top is
    ## 2^62 - 1, one below `lim`: 2^62 is that width's sign bit.
    let top = if w >= 64: lim else: min(lim, (1'i64 shl (w - 1)) - 1)
    let bot = if w >= 64: -lim else: -(1'i64 shl (w - 1))
    if lo >= bot and hi <= top: (true, lo, hi) else: (false, 0'i64, 0'i64)
  proc rangeOf(t0: RawZ3Ast; depth: int): Rng =
    let t = peelSelect(ctx, t0)
    let id = astId(ctx, t)
    if id in memo: return memo[id]
    chargeWalkerTerms(1)
    result = (false, 0'i64, 0'i64)
    if Z3_get_sort_kind(ctx.raw, Z3_get_sort(ctx.raw, t)) != Z3_BV_SORT:
      memo[id] = result
      return
    let w = int(Z3_get_bv_sort_size(ctx.raw, Z3_get_sort(ctx.raw, t)))
    let isCard = isBitSetCard(ctx, id)
    if w > 64 and not isCard:
      memo[id] = result
      return
    if isCard:
      result = (true, 0'i64, int64(bitSetCardSets[id].n))
    elif Z3_is_numeral_ast(ctx.raw, t):
      var u: uint64
      if Z3_get_numeral_uint64(ctx.raw, t, addr u):
        let v = if w < 64 and u >= (1'u64 shl (w - 1)): int64(u) - (1'i64 shl w)
                elif w == 64: cast[int64](u)
                else: int64(u)
        result = fit(v, v, w)
    elif depth < 32 and Z3_get_ast_kind(ctx.raw, t) == Z3_APP_AST:
      let app = Z3_to_app(ctx.raw, t)
      let k = ord(Z3_get_decl_kind(ctx.raw, Z3_get_app_decl(ctx.raw, app)))
      let n = int(Z3_get_app_num_args(ctx.raw, app))
      template arg(i: int): RawZ3Ast = Z3_get_app_arg(ctx.raw, app, cuint(i))
      if n == 1 and (k == bvExtDeclKinds.zext or k == bvExtDeclKinds.sext):
        let iw = int(Z3_get_bv_sort_size(ctx.raw, Z3_get_sort(ctx.raw, arg(0))))
        if iw >= 1 and iw < w and iw <= 62:
          result =
            if k == bvExtDeclKinds.zext: (true, 0'i64, (1'i64 shl iw) - 1)
            else: (true, -(1'i64 shl (iw - 1)), (1'i64 shl (iw - 1)) - 1)
      elif k == intDivDeclKinds.bvadd and n >= 1:
        result = (true, 0'i64, 0'i64)
        for i in 0 ..< n:
          let r = rangeOf(arg(i), depth + 1)
          if not r.ok:
            result = (false, 0'i64, 0'i64)
            break
          result = fit(result.lo + r.lo, result.hi + r.hi, w)
          if not result.ok: break
      elif k == intDivDeclKinds.bvsub and n == 2:
        let x = rangeOf(arg(0), depth + 1)
        let y = rangeOf(arg(1), depth + 1)
        if x.ok and y.ok: result = fit(x.lo - y.hi, x.hi - y.lo, w)
      elif k == bvExtDeclKinds.iteK and n == 3:
        let x = rangeOf(arg(1), depth + 1)
        let y = rangeOf(arg(2), depth + 1)
        if x.ok and y.ok: result = (true, min(x.lo, y.lo), max(x.hi, y.hi))
    memo[id] = result
  var done: HashSet[int]
  for x in args1:
    if result.len >= 2 * maxViewRangeFacts: break
    let xid = astId(ctx, x)
    if xid in done: continue
    done.incl xid
    if Z3_is_numeral_ast(ctx.raw, x): continue   # the rewriter folds it
    # Held from the start: a bare handle in a reference-counted context is
    # freed by the next API call.
    let v = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x, true))
    if astId(ctx, v.raw) notin seen: continue   # only the views the query holds
    let r = rangeOf(x, 0)
    if not r.ok: continue
    result.add v >= mkBigInt(ctx, $r.lo)
    result.add v <= mkBigInt(ctx, $r.hi)

proc cardFreeAbstraction*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3Bool] =
  ## RFC-0016 INT-62. `roots` and their `int` views' ranges
  ## (`bvViewRangeFacts`) with each builtin set's `card` term replaced by a
  ## fresh bit-vector of its width, or nothing when `roots` count no set's
  ## members. A model of `roots` is one of the result with each fresh
  ## variable read as its count, so the result's models are a SUPERSET of
  ## the query's and its UNSAT is the query's own (as S8bj's query without
  ## the recursive definitions). The range facts are taken before the
  ## replacement, so each count's `[0, n]` stays beside its variable, and
  ## the 256-bit set and its adder tree are no longer in the formula: an
  ## `int` accumulator's overflow side over a count is linear arithmetic
  ## over ranged views. Before, every query of a packed program after a
  ## `set[char]` row bit-blasted that row's set again (100-200k units each,
  ## against a few thousand without it).
  if bitSetCardIds.len == 0: return
  var seen: HashSet[int]
  var stack: seq[RawZ3Ast]
  var froms, tos: seq[RawZ3Ast]
  var held: seq[Z3AnyAst]
  for r in roots: stack.add r.raw
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if isBitSetCard(ctx, id):
      froms.add t
      # Held (`held`): a bare handle in a reference-counted context is
      # freed by the next API call.
      held.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_fresh_const(ctx.raw,
        "__int62_card", Z3_get_sort(ctx.raw, t)))
      tos.add held[^1].raw
      continue
    if Z3_get_ast_kind(ctx.raw, t) != Z3_APP_AST: continue
    let app = Z3_to_app(ctx.raw, t)
    for i in 0 ..< int(Z3_get_app_num_args(ctx.raw, app)):
      stack.add Z3_get_app_arg(ctx.raw, app, cuint(i))
  if froms.len == 0: return
  for r in @roots & bvViewRangeFacts(ctx, roots):
    result.add wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r.raw,
      cuint(froms.len), cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))

const recFactsRLimit* = 100_000'u
  ## RFC-0005 S8bt. The budget of `checkCapped`'s check without the
  ## recursive `replace` definitions (S8bj ran it under `factsFirstRLimit`).
  ## The facts' refutations take at most a few thousand units (2,060 for the
  ## slowest S8bt pin, Z3 5.1); a query they do not refute ran the larger
  ## budget out for nothing (`s8bb_replace`'s `a|ab` pin: 0.4 s became 7 s).

proc byteDomainLeaves*(ctx: Z3Context; roots: openArray[Z3Bool]): seq[Z3String] =
  ## RFC-0005 S8cn. The string constants with a byte-domain constraint `x in
  ## (\x00..\xff)*` among `roots` (`allocateSym`'s `itString` arm).
  let kinds = seqCapKinds()
  let byteRe = star(range(mkString(ctx, "\x00"), mkString(ctx, "\xff")))
  let byteReId = astId(ctx, byteRe.raw)
  for r in roots:
    let ra = toAnyAst(r)
    if getAstKind(ra) == akApp and
       ord(Z3_get_decl_kind(ctx.raw, unpackApp(ra).decl)) == kinds.inRe:
      let args = unpackApp(ra).args
      if astId(ctx, args[1].raw) == byteReId and getAstKind(args[0]) == akApp and
         ord(Z3_get_decl_kind(ctx.raw, unpackApp(args[0]).decl)) == kinds.uninterp and
         unpackApp(args[0]).args.len == 0:
        result.add wrap[Z3String](ctx, args[0].raw)

proc queryBytes*(text: string): seq[char] =
  ## RFC-0005 S8cn. The bytes a query's SMT-LIB text names: each integer a
  ## `str.to_code` term is compared to (a regex's class boundaries live in
  ## `define-funs-rec` bodies, which the AST API does not open), then each
  ## string literal's. Candidates only: what step 1e does with them is
  ## checked against the whole query.
  var seen: set[char]
  template add(c: int) =
    let b = c
    if b in 0 .. 255 and chr(b) notin seen:
      seen.incl chr(b)
      result.add chr(b)
  const toCode = "str.to_code"
  var i = text.find(toCode)
  while i >= 0:
    var k = i + toCode.len
    var depth = 0
    while k < text.len:
      if text[k] == '(': inc depth
      elif text[k] == ')':
        if depth == 0: break
        dec depth
        if depth == 0:
          inc k
          break
      inc k
    # `k` is at the `)` that closes the `str.to_code`.
    inc k
    while k < text.len and text[k] in Whitespace: inc k
    var v = 0
    var digits = 0
    while k < text.len and text[k] in Digits and digits < 4:
      v = v * 10 + ord(text[k]) - ord('0')
      inc digits
      inc k
    if digits > 0: add(v)
    i = text.find(toCode, k)
  i = 0
  while i < text.len:
    if text[i] == '"':
      inc i
      while i < text.len and text[i] != '"':
        if text.continuesWith("\\u{", i):
          let close = text.find('}', i)
          if close < 0: return
          var v = 0
          for d in text[i + 3 ..< close]:
            if d in HexDigits: v = v * 16 + parseHexInt($d)
          add(v)
          i = close + 1
        else:
          add(ord(text[i]))
          inc i
    inc i

const probeCandidates* = 1024
  ## RFC-0005 S8cn. Step 1e's bound on the assignments it tries.
const probeRLimit* = 200_000'u
  ## RFC-0005 S8cn. Step 1e's budget for one assignment. With every string
  ## fixed the query is evaluation, not search (S8bt's `s == "c"`: instant on
  ## both Z3s, against past 20M units free).

proc probeAssignments*(lens: seq[seq[int]]; alphabet: seq[char]):
    seq[seq[string]] =
  ## RFC-0005 S8cn. Up to `probeCandidates` assignments of strings to the
  ## leaves. A leaf takes each length in its `lens` in turn, up to 256 strings
  ## of that length over `alphabet`, then the other single bytes.
  var perLeaf: seq[seq[string]]
  for ls in lens:
    var cands: seq[string]
    for l in ls:
      var layer = @[""]
      for _ in 1 .. l:
        var next: seq[string]
        for w in layer:
          for c in alphabet:
            if next.len < 256: next.add w & c
        layer = next
      cands.add layer
    if 1 in ls:
      for b in 0 .. 255:
        if chr(b) notin alphabet: cands.add $chr(b)
    perLeaf.add cands
  result = @[newSeq[string]()]
  for cands in perLeaf:
    var next: seq[seq[string]]
    for a in result:
      for w in cands:
        if next.len < probeCandidates: next.add a & w
    result = next

proc checkExact*(ctx: Z3Context; query: openArray[Z3Bool];
                settings: SymexSettings; rlimit: uint):
                tuple[status: Z3Status, s: Z3Solver, m: Z3Model,
                      why: string] =
  ## RFC-0005 S8k. Decide `query` (every assertion of one walker query)
  ## with each string / seq leaf capped at `maxSeqLen` elements. `s` is the
  ## solver that answered (for its statistics), `m` its model in `ctx` for
  ## `zsSat`; `why` says why a `zsUnknown` is one, for the caller's
  ## `beSolverUndef` message. With no seq leaf (or `maxSeqLen == 0`,
  ## unlimited) this is exactly the pre-S8k one-shot `check()` under
  ## `rlimit`. Otherwise each byte test takes its character form
  ## (`seqLenCaps`' `byteEqs`), and the query's budget is
  ## `seqQueryRLimit` when that is the smaller bound. Steps 1 and 3, the
  ## model search, run under half of it each, so a query that finds no
  ## model spends at most the budget searching; steps 1b and 2 run under
  ## all of it:
  ##   0. (RFC-0005 S8ay) step 1c's uncapped half -- the query with no
  ##      sequence theory plus `seqRangeFacts` -- under `factsFirstRLimit`.
  ##      An UNSAT is the query's own and returns at once; anything else
  ##      goes on to (1). After a SAT here (RFC-0005 S8by), (1b) and (1c)'s
  ##      uncapped half are known SAT and do not run, nor does (1c)'s
  ##      capped half when the model makes the caps true as well.
  ##   1. a fresh one-shot `check()` with every cap ASSERTED. A model is a
  ##      model of the uncapped query.
  ##   1b. after (1) is NOT `zsSat` (`zsUnsat`, or `zsUnknown` -- RFC-0005
  ##      S8aq: step 1's OWN solve running out of budget no longer skips
  ##      this), or after an unknown in both (1) and (3): the query with
  ##      NO sequence theory (`querySolver`'s `seqTheory = false`): its
  ##      models are a superset of the real ones, so its UNSAT is the
  ##      query's own. It decides the UNSATs whose contradiction is
  ##      arithmetic over lengths and indices without any string search,
  ##      and without step 2's unsat core, which may name the cap although
  ##      the query's own bounds refute it too (Z3's cores are not
  ##      minimal).
  ##   1c. after (1b), whenever (1) was NOT `zsSat` (RFC-0005 S8ai: a query
  ##      holding a `seq.last_indexof` too; RFC-0005 S8aq: including when
  ##      (1) merely ran out of budget, same reasoning as (1b) -- a facts
  ##      UNSAT does not depend on what (1)'s own solve decided): the
  ##      theory-free query with the range each length and index term has
  ##      in the theory (`seqRangeFacts`, RFC-0005 S8v). An UNSAT is the
  ##      query's own, the facts being valid. Otherwise the caps are
  ##      ASSERTED beside them: an UNSAT then means the caps refute every
  ##      model the facts leave, so the cap took part: `zsUnknown`, with no
  ##      sequence-theory check (RFC-0005 S8r). A `seq.last_indexof` query
  ##      skips that capped half and goes on to (3), which may find a model
  ##      past the cap.
  ##   2. if (1) is UNSAT: a fresh solver with the caps behind one
  ##      assumption literal, checked under it, and its unsat core read.
  ##      Without the literal in the core the query is UNSAT on its own;
  ##      with it, only the cap refuted it (a longer term may satisfy the
  ##      query): `zsUnknown`, and no uncapped query is ever run -- its
  ##      models, if any, are exactly the long ones Z3 cannot be bounded
  ##      on.
  ##   3. the uncapped one-shot `check()` (the pre-S8k query) decides when
  ##      (1) ran out of budget -- asserted length caps can slow a query
  ##      Z3 answers quickly without them -- and, in place of (2), for a
  ##      query holding a `seq.last_indexof` that (1c) did not decide
  ##      (below).
  ##   1e. (RFC-0005 S8cn) after an unknown in both (1) and (3) and no
  ##      refutation in (1b): the whole query with each byte-domain string
  ##      pinned, for a bounded set of candidate strings. Only a model of
  ##      the whole query answers, so this moves a decline to SAT and nothing
  ##      else. A query that finds no model can so spend half its budget
  ##      again.
  ## Z3's cost on a string query is not a function of the query alone: it
  ## also follows what its CONTEXT already holds, and every query of one
  ## walk shares one context. The same lowered `s[0..2] == "aaa"` label
  ## query was SAT at once as a program's only search and ran past 20M
  ## units as the last search of `tsymex_r1b_shortcircuit_oob`; running
  ## (1b) before (3) moved a `parseInt` raise query across 20M; and a
  ## four-iteration pair-loop query with its ten caps asserted, SAT in
  ## 3.9 s from its own text, ran 100 s to 20M units in the walker, with
  ## the uncapped query SAT 23 s later (the half-and-half split above is
  ## from that case). RFC-0005 S8o measured where the state lives (Z3
  ## 5.1, SMT-LIB text loaded into solvers with `random_seed = 0`): a
  ## FRESH context reproduces a query's unit count exactly, before or
  ## after 80M units of unrelated work in other contexts (33,858,060
  ## both times), so no state is process-wide; a second solver in the
  ## SAME context, on the same text, went from past 40M to SAT in 3.25M
  ## (and in another case to SAT in 31.7M). Z3 keeps what a check built
  ## -- terms, skolems, rewriter caches -- in the context, and later
  ## checks there start from it. That is Z3's, and deterministic for a
  ## given SUT and Z3 build.
  ## RFC-0005 S8bm measured how far it reaches: B1-1's target query (the
  ## same text in every run) took 172,215 units in step 1 as one walk
  ## ran, 3,365,417 with S8ay's facts-first check before it, 11,771,578
  ## without it as the process's second walk, and 5,280,185 with one
  ## unrelated Int constant created before each step 1 -- Z3's search
  ## follows the context's term order, not only its query (Z3 5.1). So
  ## step 1, the model search nearly every SAT query ends in, runs in a
  ## fresh context of its own (`ownContextSolver`): its cost is the
  ## query's (5,711,742 there, with and without the facts-first check),
  ## and nothing the walk did before -- a facts-first check, an earlier
  ## query -- moves it.
  ## The translation costs a few milliseconds per query.
  ## RFC-0005 S8bp: so does every other step, each in a fresh context of
  ## its own (`ownContextSolver`, `ownContextCheck`): the facts-first
  ## check, (1b), (1c), (2), (3), and the query with no string (`plain`);
  ## batch 7: S8bj's query without the `replace` definitions too.
  ## They moved with the walk's context too: with thirty unrelated
  ## constants made before each query, a factoring search in (1c) took
  ## 350,726 units against 114,891, (2) 231,590 against 401,123, and the
  ## no-string query 92,799 against 124,550 (Z3 5.1); (3) 464,636 against
  ## 207,893 (4.13.4). The theory-free steps are not small when the query
  ## holds such a search. So no step's cost depends on what the walk did
  ## before it, and a query declines under its budget in every walk or in
  ## none.
  ## Why two solver modes: Z3 answers a check under assumptions with its
  ## incremental core, not the one-shot preprocessing pipeline, and that
  ## core is both much slower on bit-vector-heavy queries (one the
  ## one-shot solver finished in seconds exhausted 20M units) and wrong on
  ## `seq.last_indexof` over a term fixed to a constant: with `s == "abc"`
  ## asserted it takes `seq.last_indexof(s, "bc")` to be -4294967292, not
  ## 1 (probed on the pinned Z3; a bare `(check-sat-assuming (true))` or a
  ## `push` is enough). So every model comes from a one-shot check, and
  ## the incremental core is consulted only to tell an UNSAT's cause.
  # RFC-0005 S8ad: every step decides the query with the linear bounds of
  # its Int quotients beside it (`divRangeFacts`): theorems, so the models
  # are the query's own.
  # RFC-0005 S8bd: and with the exact link between the Int views of `x`
  # and `x +- c` where the query holds both (`bvOffsetLinks`): theorems too.
  when defined(symexQueryStats):
    # RFC-0005 S8bp: unrelated walk state, for the isolation suite.
    for k in 0 ..< symexPerturbConsts:
      discard mkIntVar(ctx, "__s8bp_perturb_" & $perturbSerial)
      inc perturbSerial
  template counted(name: string; check: untyped): Z3Status =
    ## `check` (an `ownContextCheck`), recorded as step `name` in the
    ## instrumented build (RFC-0005 S8bp, `symexStepStats`).
    when defined(symexQueryStats):
      let before = ownContextUnits
      let r = check
      symexStepStats.add SymexStepStat(step: name, status: $r,
                                       units: ownContextUnits - before)
      r
    else:
      check
  # RFC-0005 S8bp: and with a string's regex memberships, one of them
  # negated, as one (`mergeMemberships`; the same models).
  # RFC-0005 S8bu: and with each signed Int view's inverse,
  # `x == int2bv(sbv2int(x))` (`bvIntInverseFacts`): theorems too.
  # RFC-0005 S8bv: and the part identities of its `card` terms
  # (`bitSetCardFacts`), theorems too.
  # RFC-0016 INT-61: and the structural bounds of its string lengths
  # (`seqLenBoundFacts`), theorems too.
  # RFC-0016 INT-59: a query a float interval refutes (`fpIntervalRefutes`)
  # is asked as `false`: the same UNSAT, with no bit-blast.
  let query = if fpIntervalRefutes(ctx, query): @[mkBool(ctx, false)]
              else: @query
  var rootsIn = mergeMemberships(ctx, @query & divRangeFacts(ctx, query) &
    bvOffsetLinks(ctx, query) & bvIntInverseFacts(ctx, query) &
    bitSetCardFacts(ctx, query) & seqLenBoundFacts(ctx, query))
  let qto = settings.budget.queryTimeoutMs   # RFC-0005 S8bu
  # RFC-0005 S8bq: a query that counts a builtin set's members runs under
  # `seqQueryRLimit` too, when that is the smaller bound: its bit count can
  # be pigeonhole-hard, and an unbounded check of one did not return.
  let cardBounded = settings.budget.seqQueryRLimit != 0 and
    (rlimit == 0 or settings.budget.seqQueryRLimit < rlimit) and
    queryMentionsBitSetCard(ctx, rootsIn)
  let rlimit = if cardBounded: settings.budget.seqQueryRLimit else: rlimit
  # RFC-0005 S8bj: the query without the recursive `replace` definitions
  # (`regexRecDefConds`), under the small budget of step 0: a superset of
  # the real models, so an UNSAT is the query's own.
  # RFC-0005 S8bt: the values' facts (`regexRecFactConds`) are asserted
  # there only. Every step after it decides the query with each value `r`
  # replaced by its term (`r == term` read off its definition) and the
  # definitions and facts left out: the same models (the facts are true of
  # every term's value), and exactly the query S8bb / S8bj's run and step
  # tables put to Z3, whose model search the indirection through `r` and
  # the facts slowed (`tsymex_rfc0005_s8bb_replace`'s symbolic receivers:
  # 1.3 s became 11 s).
  if regexRecDefConds.len > 0:
    var defIds = initHashSet[int]()
    for d in regexRecDefConds: defIds.incl astId(ctx, d.raw)
    var factIds = initHashSet[int]()
    for f in regexRecFactConds: factIds.incl astId(ctx, f.raw)
    var abstracted, rest: seq[Z3Bool]
    for r in rootsIn:
      let id = astId(ctx, r.raw)
      if id notin defIds:
        abstracted.add r
        if id notin factIds: rest.add r
    if abstracted.len < rootsIn.len:
      let pre = if rlimit == 0: recFactsRLimit else: min(rlimit, recFactsRLimit)
      # RFC-0005 S8bp, S8bt: in a context of its own, as every step: a check
      # leaves state in its context that changes how later checks there
      # search (this one, however short, took `s8bb_replace`'s `x*` pin from
      # 4 s to 20 s in the walk's). A translated query keeps its recursive
      # functions' definitions (probed on both pinned Z3s).
      let sAbs = ownContextSolver(ctx, abstracted, pre)
      if counted("regexDefsFree", ownContextCheck(sAbs)) == zsUnsat:
        return (zsUnsat, sAbs, nil, "")
      # A nested replace's term mentions the inner value: definitions are
      # added inner first, so each term is resolved against the earlier
      # ones before it stands in.
      # RFC-0016 CRH-07: a `Z3_substitute` result has no reference until it
      # is wrapped, and Z3 frees it at the next call that returns an AST.
      # `held` owns each resolved term for as long as `tos` names it; the
      # raw one was freed before it was substituted into the roots, and the
      # roots built over it were later released into freed nodes (a SIGSEGV
      # at `byteLeafIds`' dec_ref when a second definition, `count` over a
      # `replace` value, named the first).
      var froms, tos: seq[RawZ3Ast]
      var held: seq[Z3AnyAst]
      for d in regexRecDefConds:
        let app = Z3_to_app(ctx.raw, d.raw)
        var t = Z3_get_app_arg(ctx.raw, app, 1)
        if froms.len > 0:
          held.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_substitute(ctx.raw, t,
            cuint(froms.len),
            cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
            cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
          t = held[^1].raw
        froms.add Z3_get_app_arg(ctx.raw, app, 0)
        tos.add t
      rootsIn = @[]
      for r in rest:
        rootsIn.add wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw,
          r.raw, cuint(froms.len),
          cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
          cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
  # RFC-0016 INT-62: a query that counts a builtin set's members is asked
  # first with each count a fresh variable in its range
  # (`cardFreeAbstraction`), under the small budget of step 0: a superset
  # of the real models, so an UNSAT is the query's own, and no bit-blast of
  # the set.
  block:
    let cardFree = cardFreeAbstraction(ctx, query)
    if cardFree.len > 0:
      let pre = if rlimit == 0: recFactsRLimit else: min(rlimit, recFactsRLimit)
      let sAbs = ownContextSolver(ctx, cardFree, pre)
      if counted("cardFree", ownContextCheck(sAbs)) == zsUnsat:
        return (zsUnsat, sAbs, nil, "")
  template plain(): untyped =
    let s = ownContextSolver(ctx, rootsIn, rlimit)
    let r = counted("plain", ownContextCheck(s))
    when defined(symexTestInjectWalkerFault):
      injectShapeFault("solver")   # RFC-0005 S8ce: the solver live
    return (r, s, (if r == zsSat: translate(s.model(), ctx) else: nil),
            (if r == zsUnknown:
               undefReason(s, qto) &
                 (if cardBounded: " (the query counts a builtin set's " &
                    "members, so it ran under seqQueryRLimit = " &
                    $settings.budget.seqQueryRLimit & ")" else: "")
             else: ""))
  let cap = settings.budget.maxSeqLen
  if cap <= 0: plain()
  let (caps, lastIndex, byteEqs, lens) = seqLenCaps(ctx, rootsIn, cap)
  if caps.len == 0: plain()
  # Every step below decides the query with each byte equality in its
  # character form (`seqLenCaps`): the same predicate, so the same models.
  var roots = newSeq[Z3Bool](rootsIn.len)
  if byteEqs.len == 0:
    for i, r in rootsIn: roots[i] = r
  else:
    var froms = newSeq[RawZ3Ast](byteEqs.len)
    var tos = newSeq[RawZ3Ast](byteEqs.len)
    for i, e in byteEqs:
      froms[i] = e.old.raw
      tos[i] = e.new.raw
    for i, r in rootsIn:
      roots[i] = wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r.raw,
        cuint(froms.len), cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
  # RFC-0005 S8y: without the byte-domain constraints the rest of the
  # query implies (`dropImpliedByteDomains`; same models). After
  # `seqLenCaps`, which reads them to find the byte leaves.
  roots = dropImpliedByteDomains(ctx, roots)
  let sq = settings.budget.seqQueryRLimit
  let seqBounded = sq != 0 and (rlimit == 0 or sq < rlimit)
  let rl = if seqBounded: sq else: rlimit
  # Steps 1 and 3 are the model search; between them they spend at most
  # `rl`, half each (`0`, unbounded, stays unbounded).
  let rlHalf = if rl == 0: 0'u else: max(1'u, rl div 2)
  proc z3Why(s: Z3Solver): string =
    result = undefReason(s, qto)
    if seqBounded:
      result.add " (the query mentions a string / seq, so it ran under " &
        "seqQueryRLimit = " & $sq & ")"
  let capText = "no model with every string / seq at most " & $cap &
    " elements (maxSeqLen); a longer one was not searched"
  # RFC-0005 S8ay (item 6): step 1c's UNCAPPED half runs FIRST, under a
  # small budget (`factsFirstRLimit`). It is theory-free: the query with no
  # sequence theory plus `seqRangeFacts`, every fact valid in the theory,
  # so its models are a superset of the real ones and an UNSAT is the
  # query's own -- exactly what (1b) and (1c)'s uncapped half conclude
  # after step 1, nothing more (and it subsumes (1b): the same query with
  # more assertions). Before S8ay a query only step 1c refutes paid step
  # 1's full-theory search to its half budget first: S8aw's join walks
  # spent 10,000,930 units (about 20 s on Z3 5.1) before step 1c answered
  # in a few thousand. Anything else (SAT, or unknown in the small budget)
  # falls through to the unchanged order below; unknown runs (1b) and (1c)
  # with their full budget, so no verdict is lost, and SAT skips what it
  # already answers (RFC-0005 S8by, below).
  # RFC-0005 S8ba: with each length at most `high(int)` (`nimLenFacts`):
  # true of every real input, so an UNSAT is still the query's own.
  let facts = seqRangeFacts(ctx, roots) & nimLenFacts(ctx, lens)
  # RFC-0005 S8by: a facts-first SAT is (1c)'s uncapped answer, and so
  # (1b)'s: (1c) is the same query under a larger budget, (1b) a subset of
  # it, and a budget never turns a SAT into an UNSAT. Neither is run after
  # one (in a context of its own each is the same search to the same SAT:
  # 295,900 + 311,463 of `lastNl`'s 1,106,184 units on Z3 5.1). Where the
  # facts-first model makes every cap true as well (`capsHold`), it is a
  # model of (1c)'s capped half too, which is then not run either.
  var factsSat, capsHold = false
  block factsFirst:
    when defined(symexQueryStats):
      if symexFactsFirstOff: break factsFirst   # RFC-0005 S8bm
    let pre = if rl == 0: factsFirstRLimit else: min(rl, factsFirstRLimit)
    let sPre = ownContextSolver(ctx, roots & facts, pre, seqTheory = false)
    let rPre = counted("factsFirst", ownContextCheck(sPre))
    if rPre == zsUnsat:
      return (zsUnsat, sPre, nil, "")
    if rPre == zsSat:
      factsSat = true
      # Every assertion of the capped half, evaluated under the model in
      # its own context: all true, whichever way the evaluator reads a
      # string operation, means that query has a model.
      let m = sPre.model()
      capsHold = true
      for c in roots & facts & caps:
        if m.eval(translate(c, sPre.ctx)).toBoolOpt != some(true):
          capsHold = false
          break
  # Step 1: the caps asserted, one-shot, in a context of its own
  # (RFC-0005 S8bm, `ownContextSolver`): its search is the query's, the
  # same whether or not the facts-first check (or anything else) ran in
  # the walk's context before it.
  let s1 = ownContextSolver(ctx, roots & caps, rlHalf)
  let r1 = counted("1", ownContextCheck(s1))
  if r1 == zsSat: return (zsSat, s1, translate(s1.model(), ctx), "")
  # Step 1b: the query with no sequence theory. Its models include every
  # real one, so an UNSAT here is the query's own (the cap took no part);
  # it cannot run into a long-string search, having none. It decides the
  # UNSATs whose contradiction is arithmetic over lengths and indices,
  # which an unsat core (step 2) can wrongly attribute to the cap: Z3's
  # cores are not minimal, and `len(s) <= maxSeqLen` bounds a length as
  # well as the query's own `len(s) <= 1000` does. After an unknown in
  # (1) it runs only once (3) has failed too (see the doc comment).
  template theoryFreeUnsat(): (bool, Z3Solver) =
    let sTf = ownContextSolver(ctx, roots, rl, seqTheory = false)
    (counted("1b", ownContextCheck(sTf)) == zsUnsat, sTf)
  # RFC-0005 S8aq: (1b) and (1c) below no longer gate on `r1 == zsUnsat`
  # specifically. `r1` can only be `zsUnsat` or `zsUnknown` here (`zsSat`
  # already returned), and a `zsUnknown` -- step 1's capped, full-theory
  # solve merely ran OUT OF BUDGET, not refuted -- used to skip both and
  # fall straight to step 3 with whatever budget remained: step 1c's
  # facts, cheap and theory-free, were never tried for a query that needed
  # them precisely because the full theory was too slow to finish in time.
  # Both checks are sound regardless of why `r1` is not `zsSat`: a
  # theory-free (1b) or facts-based (1c) UNSAT is the query's own, since
  # their models are a superset of the real ones and the facts are valid
  # in the theory, independent of what step 1's OWN solve did or did not
  # decide. (`tsymex_rfc0005_s8aq_remainder.nim`, S8ai's own two
  # not-pinned-end-to-end cases: `s[7] == ':' and rfind < 7` and `':' in s
  # and rfind == -1`, both cancelled at step 1 under the tight budget.)
  if r1 != zsSat and not factsSat:   # RFC-0005 S8by: else known SAT
    let (tfUnsat, s1b) = theoryFreeUnsat()
    if tfUnsat: return (zsUnsat, s1b, nil, "")
  if r1 != zsSat:
    # Step 1c (RFC-0005 S8r): the caps against the query with no sequence
    # theory. (1b) found no theory-free refutation of the query alone; if
    # the caps now refute it, the cap takes part in the only refutation
    # visible without a string search: decline as step 2 would on a core
    # naming the cap, without running the sequence theory at all. Step 2's
    # incremental core does not see the caps during preprocessing (they
    # sit behind its assumption literal), and on Z3 4.13.4 it searched the
    # long strings itself: `len(s) > 1000` under the 128 cap took 2.3M
    # units and 1 GB to refute, and its sibling ran out of memory without
    # reaching a 20M `rlimit` (`tsymex_163rev_intoffset_range`, the corpus
    # shard 2 runner loss).
    # RFC-0005 S8v: with the range the theory gives each length and index
    # term (`seqRangeFacts`), so a cap conflict that runs through one of
    # them (`str.indexof` below -1) is seen here, not searched for in (2).
    # The facts are checked first WITHOUT the caps: they alone can refute
    # the query (a scan's closed form `i > len(s)`, `tsymex_q1_scanlift`
    # Q1-1b, needs `str.indexof`'s upper bound), and that UNSAT, every fact
    # being valid, is the query's own; asserted beside the caps it would
    # read as the cap's (a decline where step 2's core found none).
    # RFC-0005 S8ae: the facts also link the theory's functions (an
    # `indexof` found implies `contains`, and so on), so a query refuted
    # only through such a link is decided here as its own UNSAT, not
    # declined on the cap below.
    # RFC-0005 S8ai: a query holding a `seq.last_indexof` takes this step
    # too (it went straight to the uncapped step 3, the one place the
    # uncapped sequence theory still ran), with `last_indexof`'s links.
    # Step 1c is one-shot and theory-free, so the incremental core's wrong
    # `seq.last_indexof` value (below) does not reach it; only step 2 is
    # still skipped for such a query. Such a query takes only the uncapped
    # half (an UNSAT that is its own): the capped half would decline one
    # that is SAT only past the cap, which step 3 decides
    # (`tsymex_rfc0005_s8o_termination` (4), `t.len > 10` under a cap of 8).
    # (`facts` is computed above, for the facts-first check; RFC-0005 S8ba:
    # with each length at most `high(int)`, `nimLenFacts`.)
    # (RFC-0005 S8by: neither half after a facts-first SAT whose model
    # satisfies the caps, nor the uncapped half after any facts-first SAT.)
    if facts.len > 0 and not factsSat:
      let sTr = ownContextSolver(ctx, roots & facts, rl, seqTheory = false)
      if counted("1c", ownContextCheck(sTr)) == zsUnsat:
        return (zsUnsat, sTr, nil, "")
    if not lastIndex and not capsHold:
      let sTc = ownContextSolver(ctx, roots & facts & caps, rl,
                                 seqTheory = false)
      if counted("1c-capped", ownContextCheck(sTc)) == zsUnsat:
        return (zsUnknown, s1, nil, capText)
  var all = caps[0]
  for i in 1 ..< caps.len: all = all and caps[i]
  if r1 == zsUnsat and not lastIndex:
    # Step 1d (RFC-0005 batch 8): the caps are implied. If the query with no
    # sequence theory, plus the facts (a superset of the real models), has no
    # model breaking a cap, every real model keeps to the caps, so step 1's
    # UNSAT is the query's own. Step 2 cannot say so: its core is not minimal,
    # and may name the cap though the query bounds every length itself (S8bx's
    # `setLen` pin, `len(s) <= 8` and `n <= 12`, on Z3 4.13.4 in S8bp's own
    # context).
    let pre = if rl == 0: factsFirstRLimit else: min(rl, factsFirstRLimit)
    let sIm = ownContextSolver(ctx, roots & facts & @[not all], pre,
                               seqTheory = false)
    if counted("1d", ownContextCheck(sIm)) == zsUnsat:
      return (zsUnsat, s1, nil, "")
    # Step 2: is the UNSAT the query's own?
    let s2 = ownContextSolver(ctx, roots, rl)
    let capLit = mkBoolVar(s2.ctx, "__s8k_seq_len_cap")
    s2.add implies(capLit, translate(all, s2.ctx))
    let r2 = counted("2", ownContextCheck(s2, [capLit]))
    return case r2
      of zsUnsat:
        if s2.getUnsatCore().len == 0: (zsUnsat, s2, nil, "")
        else: (zsUnknown, s1, nil, capText)
      of zsUnknown:
        (zsUnknown, s2, nil, capText & "; whether the query is UNSAT on " &
                             "its own was not decided: " & z3Why(s2))
      of zsSat:
        # SAT under the assumption although step 1 found the capped query
        # UNSAT: the two Z3 solvers disagree, and neither answer is used.
        (zsUnknown, s1, nil, "Z3's one-shot and incremental solvers " &
                             "disagree on this query under maxSeqLen = " &
                             $cap)
  # Step 3: the uncapped one-shot query.
  let s3 = ownContextSolver(ctx, roots, rl - rlHalf)
  let r3 = counted("3", ownContextCheck(s3))
  case r3
  of zsSat: (zsSat, s3, translate(s3.model(), ctx), "")
  of zsUnsat: (zsUnsat, s3, nil, "")
  of zsUnknown:
    if r1 == zsUnsat:
      (zsUnknown, s3, nil, capText & "; the uncapped query (it holds a " &
                           "seq.last_indexof) was not decided: " & z3Why(s3))
    else:
      # RFC-0005 S8by: a facts-first SAT means (1b) cannot refute, so it is not
      # run; RFC-0005 S8cn: step 1e still may find the model.
      let (tfUnsat, s1b) = if factsSat: (false, s3) else: theoryFreeUnsat()
      if tfUnsat: (zsUnsat, s1b, nil, "")
      else:
        # Step 1e (RFC-0005 S8cn): both searches ran out, on a query that may
        # have a model a search does not find and an evaluation does. S8bt's
        # `bt_limit_replace` on Z3 4.13.4, in its own context (S8bp), spends
        # the budget on one free byte over a regex's recursive step function,
        # with or without the byte-domain membership, while `s == "c"` is
        # instant. So try a bounded number of concrete strings: each length
        # the theory-free query gives a leaf (its models hold every real one),
        # plus 0..3 for a lone leaf, over the bytes the query's text names.
        # Each is the whole query plus the pins, so an answer is a model of
        # the query; this moves a decline to SAT and nothing else. A leaf
        # with no byte domain, or the budget (`rlHalf div 2` in all), ends it.
        let leaves = byteDomainLeaves(ctx, roots)
        var found: Z3Model = nil
        var sPin: Z3Solver = s3
        if leaves.len > 0:
          let sLen = ownContextSolver(ctx, roots & facts & caps, rlHalf div 2,
                                      seqTheory = false)
          if counted("1e-len", ownContextCheck(sLen)) == zsSat:
            let m = translate(sLen.model(), ctx)
            var lens: seq[seq[int]]
            for x in leaves:
              # A theory-free model's length may be an `ite` over its opaque
              # string values, which names no length.
              let lt = m.eval(x.len)
              var ls: seq[int]
              if Z3_is_numeral_ast(ctx.raw, lt.raw): ls.add int(lt.toInt64)
              if leaves.len == 1 or ls.len == 0:
                for extra in (if leaves.len == 1: 0 else: 1) .. (if leaves.len == 1: 3 else: 1):
                  if extra notin ls: ls.add extra
              lens.add ls
            var alphabet = queryBytes($s3)
            for b in 0 .. 255:
              if alphabet.len >= 12: break
              if chr(b) notin alphabet: alphabet.add chr(b)
            var left = int64(rlHalf div 2)
            for pins in probeAssignments(lens, alphabet):
              if rl != 0 and left <= 0: break
              var pinned = @roots
              for k, x in leaves: pinned.add(x == mkString(ctx, pins[k]))
              # The caller's budget holds here too: a query it cuts off stays
              # a decline, however small the budget.
              let sC = ownContextSolver(ctx, pinned,
                if rl != 0: min(probeRLimit, uint(left)) else: probeRLimit)
              let rC = counted("1e", ownContextCheck(sC))
              let st = sC.getStatistics()
              if st.contains("rlimit count"):
                left -= (if st.isInt("rlimit count"): int64(st.getInt("rlimit count"))
                         else: int64(st.getFloat("rlimit count")))
              if rC == zsSat:
                found = translate(sC.model(), ctx)
                sPin = sC
                break
        if found != nil: (zsSat, sPin, found, "")
        else: (zsUnknown, s3, nil, z3Why(s3))

const
  limitWorldRLimit* = 1_000_000'u
    ## RFC-0005 S8cf. The budget of one `limitWorldRefuted` check. It refutes
    ## on the error value alone (a few thousand units); a query it does not
    ## refute has a model with a long subject, which Z3 need not find, and
    ## running out reads the same.
  limitWorldTimeoutMs = 3000'u
    ## RFC-0005 S8cf. Its clock: Z3's sequence solver can stop advancing the
    ## step count on `(a|a)*[bc]` against a long literal (probed), so the
    ## step bound alone need not end the check. The cut only makes the query
    ## `zsUnknown`.
  limitWorldSites = 8
    ## RFC-0005 S8cf. The most calls `limitWorldRefuted` splits on, one check
    ## each; a query reading more is `zsUnknown` past their safe lengths.

const
  pointRounds = 8
    ## RFC-0005 S8cf. The candidates `pointCheck` tries one at a time.
  pointRLimit = 2_000_000'u
    ## RFC-0005 S8cf. One round's budget: its query holds no automaton, so a
    ## round that needs more is one the exact encoding should have a go at.
  pointTimeoutMs = 5000'u
  pointTableLen = 4
    ## RFC-0005 S8cf. The longest subject of `pointTable`'s candidates.
  pointTableBytes = 5
    ## RFC-0005 S8cf. Its alphabet's size: at most 781 subjects.

proc stringConstants*(ctx: Z3Context; query: openArray[Z3Bool]): seq[string] =
  ## RFC-0005 S8cf. The string literals `query` holds.
  var seen: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in query: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if Z3_is_string(ctx.raw, t.raw):
      var b = ""
      for cp in getStringContents(wrap[Z3String](ctx, t.raw)):
        if cp in 0 .. 255: b.add char(cp)
      result.add b
    elif getAstKind(t) == akApp:
      let (_, args) = unpackApp(t)
      for a in args: stack.add a

proc holdsIn*(m: Z3Model; b: Z3Bool): bool =
  ## RFC-0005 S8cf. `b` is true in `m`.
  let ev = m.eval(b, modelCompletion = true)
  Z3_get_bool_value(ev.ctx.raw, ev.raw) == Z3_L_TRUE

proc pointValue*(st: RegexPointSite; subject, by: string; start: int): RegexPoint =
  ## RFC-0005 S8cf. `concreteEntry`, within the safe length: past it the real
  ## call can stop at a limit, and the point has no value of its own.
  if subject.len > st.safe: return RegexPoint()
  concreteEntry(st.sp, st.pr, subject, start, by)

proc pointLit*(st: RegexPointSite; p: RegexPoint): Z3AnyAst =
  ## RFC-0005 S8cf. The value `p` as a term.
  if st.sp.entry == "replace": toAnyAst(mkString(p.s))
  elif st.sp.entry in ["match", "contains", "startsWith", "endsWith"]:
    toAnyAst(mkBool(p.b))
  else: toAnyAst(mkInt(p.i))

proc foldPinnedPoints*(ctx: Z3Context; roots: seq[Z3Bool]): seq[Z3Bool] =
  ## RFC-0016 S8co (PRC-33). `roots` with every regex call whose operands
  ## the roots pin to literals (`subject == "..."` at the top or under an
  ## `and`; a numeral start; a literal `by`) replaced by its value at that
  ## point (`pointValue`, the automaton the formulas are verified against),
  ## its definitions dropped. A scratch solve (`concreteScratchCheck`) that
  ## kept the exact term searched Z3's membership of a marked split of a
  ## concrete subject: on the 8.37 JIT languages of `tsymex_0016_s8co_skipcount`
  ## 2 s at 8 bytes, 16 s at 18, undecided within its bound past that, so
  ## the walk did not end within 900 s (the interpreter declines those
  ## languages, so the call was a fresh value there and the solve trivial).
  ## `pointCheck`'s `pinned` block does the same for the walker's queries.
  if regexPointSites.len == 0: return roots
  ensureByteDomainKinds()
  let bk = byteDomainKinds
  var lits = initTable[int, RawZ3Ast]()
  var stack: seq[Z3AnyAst]
  for r in roots: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    if getAstKind(t) != akApp: continue
    let (decl, args) = unpackApp(t)
    let dk = ord(Z3_get_decl_kind(ctx.raw, decl))
    if dk == bk.andK:
      for a in args: stack.add a
    elif dk == bk.eq and args.len == 2:
      if Z3_is_string(ctx.raw, args[1].raw):
        lits[astId(ctx, args[0].raw)] = args[1].raw
      elif Z3_is_string(ctx.raw, args[0].raw):
        lits[astId(ctx, args[1].raw)] = args[0].raw
  if lits.len == 0: return roots
  var ff, tt: seq[RawZ3Ast]
  var folded, dropped: HashSet[int]
  for st in regexPointSites:
    let xid = astId(ctx, st.exact.raw)
    if xid in folded: continue
    let id = astId(ctx, st.subject.raw)
    if id notin lits: continue
    let lit = literalStringBytes(wrap[Z3String](ctx, lits[id]))
    let startS = simplify(st.start)
    if not lit.ok or not isNumeralAst(ctx, startS.raw): continue
    var by = ""
    if st.sp.entry == "replace":
      let b = literalStringBytes(st.by)
      if not b.ok: continue
      by = b.s
    let p = pointValue(st, lit.s, by,
                       int(parseBiggestInt(getNumeralString(startS))))
    if not p.ok: continue
    folded.incl xid
    ff.add st.exact.raw
    tt.add keepRaw(pointLit(st, p))
    for d in st.defs: dropped.incl d
  if ff.len == 0: return roots
  for r in roots:
    if astId(ctx, r.raw) in dropped: continue
    result.add wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r.raw,
      cuint(ff.len), cast[ptr UncheckedArray[RawZ3Ast]](ff[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](tt[0].addr)))

proc pointEq*(st: RegexPointSite; v: Z3AnyAst; p: RegexPoint): Z3Bool =
  ## RFC-0005 S8cf. `v` is the value `p`.
  wrap[Z3Bool](v.ctx, checkedEq(v.ctx, v.raw, pointLit(st, p).raw))

proc pointSitesIn*(ctx: Z3Context; query: openArray[Z3Bool]): seq[int] =
  ## RFC-0005 S8cf. The `regexPointSites` whose value `query` reads.
  if regexPointSites.len == 0: return
  var byId = initTable[int, seq[int]]()
  for i, st in regexPointSites:
    if not st.light: byId.mgetOrPut(astId(ctx, st.exact.raw), @[]).add i
  var seen, hit: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in query: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if id in byId:
      for i in byId[id]: hit.incl i
    if getAstKind(t) != akApp: continue
    let (_, args) = unpackApp(t)
    for a in args: stack.add a
  for i in 0 ..< regexPointSites.len:
    if i in hit: result.add i

proc pointCheck*(ctx: Z3Context; query: openArray[Z3Bool];
                sites: seq[int]; decided: var bool):
                tuple[status: Z3Status, s: Z3Solver, m: Z3Model, why: string] =
  ## RFC-0005 S8cf (items 8, 9, 10). `query` with each call's value a fresh
  ## `v` and its definition gone: a superset of the real runs. So:
  ##   * UNSAT is the query's own;
  ##   * a model whose every call's `v` is what `concreteEntry` computes at
  ##     the model's operands is a model of the query;
  ##   * otherwise the point is a valid lemma, `operands == c -> v == value`,
  ##     and the search goes on, `pointRounds` times.
  ## Past those rounds `pointTable` asks once for a subject among short
  ## strings over the query's and the pattern's own bytes, all their values
  ## stated at once: a search for a value (`r == "x-"`) has no other way to
  ## one. Not `decided` leaves the query to `checkExact`, unless a call's
  ## encoding was declined: then the verdict is `zsUnknown`.
  decided = false
  var vs: seq[Z3AnyAst]
  var froms, tos: seq[RawZ3Ast]
  var dropped: HashSet[int]
  var declined = false
  for i in sites:
    let st = regexPointSites[i]
    declined = declined or st.declined
    for d in st.defs: dropped.incl d
    let sort = Z3_get_sort(ctx.raw, st.exact.raw)
    let name = regexFreshName("__regexPointValue")
    let sym = Z3_mk_string_symbol(ctx.raw, name.cstring)
    let v = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw, sym, sort))
    vs.add v
    froms.add st.exact.raw
    tos.add v.raw
  var roots: seq[Z3Bool]
  for r in query:
    if astId(ctx, r.raw) in dropped: continue
    roots.add wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r.raw,
      cuint(froms.len), cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
  let savedTimeout = queryTimeoutMsCur
  defer: queryTimeoutMsCur = savedTimeout
  # RFC-0016 INT-59: the cut applies under a run clock only. With none
  # (the pin settings) the step bound alone ends the check, so its answer
  # is the same on every host.
  if queryTimeoutMsCur > pointTimeoutMs:
    queryTimeoutMsCur = pointTimeoutMs
  var stopWhy = "the search found no point whose value the query accepts"
  proc operands(st: RegexPointSite; m: Z3Model):
      tuple[ok: bool, s, by: string, start: int] =
    result.s = evalStrBytes(m, st.subject)
    if st.sp.entry == "replace": result.by = evalStrBytes(m, st.by)
    let ev = m.eval(st.start, modelCompletion = true)
    if not isNumeralAst(ctx, ev.raw): return
    result.start = int(parseBiggestInt(getNumeralString(ev)))
    result.ok = true
  proc atPoint(st: RegexPointSite; s, by: string; start: int): Z3Bool =
    result = st.subject == mkString(s) and st.start == mkInt(start)
    if st.sp.entry == "replace": result = result and st.by == mkString(by)
  # A subject the query pins to a literal has its values now, and folds the
  # facts over it: Z3 4.13.4 ran out of its budget on those memberships.
  block pinned:
    ensureByteDomainKinds()
    let bk = byteDomainKinds
    var lits = initTable[int, RawZ3Ast]()
    var stack: seq[Z3AnyAst]
    for r in roots: stack.add toAnyAst(r)
    while stack.len > 0:
      let t = stack.pop()
      if getAstKind(t) != akApp: continue
      let (decl, args) = unpackApp(t)
      let dk = ord(Z3_get_decl_kind(ctx.raw, decl))
      if dk == bk.andK:
        for a in args: stack.add a
      elif dk == bk.eq and args.len == 2:
        if Z3_is_string(ctx.raw, args[1].raw):
          lits[astId(ctx, args[0].raw)] = args[1].raw
        elif Z3_is_string(ctx.raw, args[0].raw):
          lits[astId(ctx, args[1].raw)] = args[0].raw
    var pins = roots
    var ff, tt: seq[RawZ3Ast]
    var eqs: seq[Z3Bool]
    for k, i in sites:
      let st = regexPointSites[i]
      let id = astId(ctx, st.subject.raw)
      if id notin lits: break pinned
      let lit = literalStringBytes(wrap[Z3String](ctx, lits[id]))
      let startS = simplify(st.start)
      if not lit.ok or not isNumeralAst(ctx, startS.raw): break pinned
      var by = ""
      if st.sp.entry == "replace":
        let b = literalStringBytes(st.by)
        if not b.ok: break pinned
        by = b.s
      let p = pointValue(st, lit.s, by,
                         int(parseBiggestInt(getNumeralString(startS))))
      if not p.ok: break pinned
      eqs.add pointEq(st, vs[k], p)
      eqs.add st.subject == mkString(lit.s)
      ff.add st.subject.raw
      tt.add lits[id]
    # Every other call on a pinned subject has its value here too, so what
    # defines it need not be searched: a call whose fresh terms the rest of
    # the query still names keeps its encoding, or a model of the rest need
    # not extend to it. The search reads the rest of `query` as it stands.
    var queryIds: HashSet[int]
    for r in query: queryIds.incl astId(ctx, r.raw)
    type Lifted = tuple[exact, value: RawZ3Ast, defs: seq[int]]
    var lifted: seq[Lifted]
    # RFC-0016 CRH-07: owns each lifted value for as long as `lifted` names
    # it raw (the `pointLit` temporary was released at the end of its
    # statement, leaving a stale handle for the substitutions below).
    var liftedHeld: seq[Z3AnyAst]
    for i, st in regexPointSites:
      if i in sites: continue
      var onPath = false
      for d in st.defs: onPath = onPath or d in queryIds
      if not onPath: continue
      let id = astId(ctx, st.subject.raw)
      if id notin lits: continue
      let lit = literalStringBytes(wrap[Z3String](ctx, lits[id]))
      let startS = simplify(st.start)
      if not lit.ok or not isNumeralAst(ctx, startS.raw): continue
      let p = pointValue(st, lit.s, "",
                         int(parseBiggestInt(getNumeralString(startS))))
      if not p.ok: continue
      liftedHeld.add pointLit(st, p)
      lifted.add (st.exact.raw, liftedHeld[^1].raw, st.defs)
      ff.add st.subject.raw
      tt.add lits[id]
    let kinds = seqCapKinds()
    proc constsOf(r: Z3AnyAst): HashSet[string] =
      var seen: HashSet[int]
      var work = @[r]
      while work.len > 0:
        let t = work.pop()
        let id = astId(ctx, t.raw)
        if id in seen or getAstKind(t) != akApp: continue
        seen.incl id
        let (decl, args) = unpackApp(t)
        if args.len == 0:
          if ord(Z3_get_decl_kind(ctx.raw, decl)) == kinds.uninterp:
            result.incl $Z3_get_symbol_string(ctx.raw,
                                              Z3_get_decl_name(ctx.raw, decl))
        for a in args: work.add a
    proc subst(r: RawZ3Ast; a, b: var seq[RawZ3Ast]): Z3Bool =
      ## Owned at once (CRH-07): a `Z3_substitute` result has no reference
      ## until it is wrapped.
      if a.len == 0: return wrap[Z3Bool](ctx, r)
      wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r, cuint(a.len),
        cast[ptr UncheckedArray[RawZ3Ast]](a[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](b[0].addr)))
    while true:
      var gone = dropped
      var fs = froms
      var ts = tos
      for l in lifted:
        for d in l.defs: gone.incl d
        fs.add l.exact
        ts.add l.value
      pins = @[]
      for r in query:
        if astId(ctx, r.raw) in gone: continue
        pins.add simplify(subst(subst(r.raw, fs, ts).raw, ff, tt))
      var live: HashSet[string]
      for r in pins: live = live + constsOf(toAnyAst(r))
      var keep: seq[Lifted]
      for l in lifted:
        var shared = false
        for r in query:
          if astId(ctx, r.raw) in l.defs:
            let c = constsOf(toAnyAst(subst(r.raw, ff, tt)))
            for n in c:
              if n in live: shared = true
        if not shared: keep.add l
      if keep.len == lifted.len: break
      lifted = keep
    let sv = ownContextSolver(ctx, pins & eqs, pointRLimit)
    case ownContextCheck(sv)
    of zsUnsat:
      decided = true
      return (zsUnsat, sv, nil, "")
    of zsSat:
      decided = true
      return (zsSat, sv, translate(sv.model(), ctx), "")
    of zsUnknown: discard
  block rounds:
    for round in 0 ..< pointRounds:
      let sv = ownContextSolver(ctx, roots, pointRLimit)
      case ownContextCheck(sv)
      of zsUnsat:
        decided = true
        return (zsUnsat, sv, nil, "")
      of zsUnknown:
        stopWhy = "Z3: " & sv.reasonUnknown()
        break rounds
      of zsSat: discard
      let m = translate(sv.model(), ctx)
      var all = true
      for k, i in sites:
        let st = regexPointSites[i]
        let o = operands(st, m)
        if not o.ok: break rounds
        let p = pointValue(st, o.s, o.by, o.start)
        if not p.ok:
          stopWhy = "the automaton does not read the point"
          break rounds
        let want = pointEq(st, vs[k], p)
        if not holdsIn(m, want):
          all = false
          roots.add implies(atPoint(st, o.s, o.by, o.start), want)
      if all:
        decided = true
        return (zsSat, sv, m, "")
  # The table: one call's subject over short strings.
  let k0 = 0
  let st0 = regexPointSites[sites[k0]]
  var bytes: seq[char]
  proc addByte(c: char) =
    if c notin bytes and bytes.len < pointTableBytes: bytes.add c
  # The query's own text first: the facts' UTF-8 ranges hold bytes too.
  let lits = stringConstants(ctx, query)
  for lit in lits:
    for c in lit:
      if c in {' '..'~'}: addByte(c)
  var body = st0.sp.pattern          # past its start options: `(*UTF8)`
  while body.startsWith("(*") and ')' in body:
    body = body[body.find(')') + 1 .. ^1]
  for c in body:
    if c in {'a'..'z', 'A'..'Z', '0'..'9'}: addByte(c)
  for lit in lits:
    for c in lit: addByte(c)
  addByte('a')
  var words = @[""]
  var at = 0
  while at < words.len:
    let w = words[at]
    inc at
    if w.len < pointTableLen:
      for c in bytes: words.add w & c
  var opts: seq[Z3Bool]
  let isReplace = st0.sp.entry == "replace"
  let byLit = literalStringBytes(st0.by)
  let startSimp = simplify(st0.start)
  if isNumeralAst(ctx, startSimp.raw) and (byLit.ok or not isReplace):
    let start = int(parseBiggestInt(getNumeralString(startSimp)))
    for w in words:
      let p = pointValue(st0, w, byLit.s, start)
      if p.ok:
        opts.add st0.subject == mkString(w) and pointEq(st0, vs[k0], p)
  if opts.len > 0:
    var any = opts[0]
    for i in 1 ..< opts.len: any = any or opts[i]
    let sv = ownContextSolver(ctx, roots & @[any], pointRLimit * 2)
    if ownContextCheck(sv) == zsSat:
      let m = translate(sv.model(), ctx)
      var all = true
      for k, i in sites:
        let st = regexPointSites[i]
        let o = operands(st, m)
        if not o.ok: all = false; break
        let p = pointValue(st, o.s, o.by, o.start)
        if not p.ok or not holdsIn(m, pointEq(st, vs[k], p)):
          all = false
          break
      if all:
        decided = true
        return (zsSat, sv, m, "")
  if declined:
    decided = true
    result.status = zsUnknown
    result.why = "a regex call whose encoding is past its size cap, read at " &
      "points: " & stopWhy

proc limitSitesIn*(ctx: Z3Context; query: openArray[Z3Bool]): seq[int] =
  ## RFC-0005 S8cf. The `regexLimitSites` whose value `query` reads.
  if regexLimitSites.len == 0: return
  var byId = initTable[int, seq[int]]()
  for i, st in regexLimitSites:
    byId.mgetOrPut(astId(ctx, st.exact.raw), @[]).add i
  var seen: HashSet[int]
  var hit: HashSet[int]
  var stack: seq[Z3AnyAst]
  for r in query: stack.add toAnyAst(r)
  while stack.len > 0:
    let t = stack.pop()
    let id = astId(ctx, t.raw)
    if id in seen: continue
    seen.incl id
    chargeWalkerTerms(1)
    if id in byId:
      for i in byId[id]: hit.incl i
    if getAstKind(t) != akApp: continue
    let (_, args) = unpackApp(t)
    for a in args: stack.add a
  for i in 0 ..< regexLimitSites.len:
    if i in hit: result.add i

proc limitReason*(ctx: Z3Context; sites: seq[int]): string =
  var xs: seq[string]
  for i in sites:
    let st = regexLimitSites[i]
    xs.add st.what & " past " & $st.safe & " bytes"
  "a regex call can stop at one of PCRE's own limits (PCRE_ERROR_MATCHLIMIT," &
    " PCRE_ERROR_RECURSIONLIMIT, PCRE_ERROR_JIT_STACKLIMIT, or match() off " &
    "the machine stack), which the query does not exclude: " & xs.join("; ")

proc limitWorldRefuted*(ctx: Z3Context; query: openArray[Z3Bool];
                       sites: seq[int]): bool =
  ## RFC-0005 S8cf. True when `query`, already UNSAT with every call read
  ## exactly, is UNSAT with each call in turn stopped at a limit. That call's
  ## value is gone from its check, which keeps it clear of the exact term's
  ## search; the other calls are their error value or their exact one, a
  ## superset of the real runs.
  if sites.len > limitWorldSites: return false
  proc swap(r: Z3Bool; a, b: RawZ3Ast): Z3Bool =
    var froms = [a]
    var tos = [b]
    wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r.raw, 1,
      cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
  let savedTimeout = queryTimeoutMsCur
  defer: queryTimeoutMsCur = savedTimeout
  # RFC-0016 INT-59: the cut applies under a run clock only. With none
  # (the pin settings) the step bound alone ends the check, so its answer
  # is the same on every host.
  if queryTimeoutMsCur > limitWorldTimeoutMs:
    queryTimeoutMsCur = limitWorldTimeoutMs
  for k in sites:
    let stopped = regexLimitSites[k]
    var roots: seq[Z3Bool]
    for r in query:
      if astId(ctx, r.raw) notin stopped.guarded:
        roots.add swap(r, stopped.exact.raw, stopped.err.raw)
    for c in stopped.errConds: roots.add c
    roots.add len(stopped.subject) > mkInt(stopped.safe)
    for j in sites:
      if j == k: continue
      let other = regexLimitSites[j]
      let ab = mkBoolVar(ctx, regexFreshName("__regexLimitHit"))
      let v = wrap[Z3AnyAst](ctx, checkedIte(ctx, ab.raw, other.err.raw,
                                             other.exact.raw))
      var next: seq[Z3Bool]
      for r in roots:
        next.add(if astId(ctx, r.raw) in other.guarded: ab or r
                 else: swap(r, other.exact.raw, v.raw))
      roots = next
      for c in other.errConds: roots.add c
      roots.add (not ab) or (len(other.subject) > mkInt(other.safe))
    let s = ownContextSolver(ctx, roots, limitWorldRLimit)
    if ownContextCheck(s) != zsUnsat: return false
  true

proc checkCapped*(ctx: Z3Context; query: openArray[Z3Bool];
                 settings: SymexSettings; rlimit0: uint):
                 tuple[status: Z3Status, s: Z3Solver, m: Z3Model,
                       why: string] =
  ## RFC-0005 S8cf (SOUNDNESS). `checkExact` reads every regex call as a
  ## match or a miss. A call past its safe length may instead stop at one of
  ## PCRE's own limits (`RegexLimitSite`), so:
  ##   * a model whose subjects are all within their safe lengths stands; one
  ##     past them is searched again with the lengths asserted, and without
  ##     such a model the query is `zsUnknown`;
  ##   * an UNSAT stands only if the query stays UNSAT with those calls
  ##     stopped at a limit (`limitWorldRefuted`), else `zsUnknown`.
  ## A query with no such call is `checkExact` alone.
  # RFC-0016 K7. Under a `walkRLimit` the query runs under at most what the
  # walk has left (at least 1: the work is spent and the walk stops, so it
  # decides nothing it need not), so one query cannot overshoot the total.
  # RFC-0016 W3-z R9: and, in a tail walk, under what its own budget has left.
  let rlimit = workLeftRLimit(rlimit0)
  let sites = limitSitesIn(ctx, query)
  let points = pointSitesIn(ctx, query)
  var decided = false
  if points.len > 0: result = pointCheck(ctx, query, points, decided)
  if not decided: result = checkExact(ctx, query, settings, rlimit)
  if sites.len == 0: return
  case result.status
  of zsSat:
    var over = false
    for i in sites:
      let st = regexLimitSites[i]
      let l = result.m.eval(len(st.subject))
      if not isNumeralAst(ctx, l.raw) or
         parseBiggestInt(getNumeralString(l)) > st.safe:
        over = true
    if not over: return
    var guarded = @query
    for i in sites:
      let st = regexLimitSites[i]
      guarded.add len(st.subject) <= mkInt(st.safe)
    let r2 = checkExact(ctx, guarded, settings, rlimit)
    if r2.status == zsSat: return r2
    result = r2
    result.status = zsUnknown
    result.m = nil
    result.why = limitReason(ctx, sites)
  of zsUnsat:
    if not limitWorldRefuted(ctx, query, sites):
      result.status = zsUnknown
      result.why = limitReason(ctx, sites)
  else: discard

const satModelsKept* = 4
  ## RFC-0016 int6 D1d. The SAT models `refuteStatus` keeps (`satModels`):
  ## the walk's most recent, newest last.

const satModelVisits* = walkerContextUnits div walkerTermUnits
  ## RFC-0016 int6 D1d. The term visits `satByModel` may spend evaluating a
  ## query's roots that its kept models were not found for: what the fixed
  ## cost of the search it would save is charged (`walkerContextUnits`), so
  ## trying the models never costs more than that. A root past what is left
  ## ends the try (a large new root, a const table's lookup, is the shape).


var satModels* {.threadvar.}: seq[SatModel]
  ## RFC-0016 int6 D1d. Emptied at each run's start and end, so no model
  ## (nor the context it holds) outlives its run (RFC-0016 S8cj).

proc modelHolds*(ctx: Z3Context; m: Z3Model; root: Z3Bool): bool =
  ## RFC-0016 int6 D1d. `root` is true in `m`, completed (`holdsIn`), charged
  ## a visit per distinct term of it (Z3's evaluator visits each once).
  chargeWalkerTerms(queryTermCount(ctx, [root]))
  chargeWalkWork()
  holdsIn(m, root)

proc satByModel*(ctx: Z3Context; query: openArray[Z3Bool]): bool =
  ## RFC-0016 int6 D1d. Some kept model satisfies every root of `query`: the
  ## query is SAT, with no search. The roots the model's own query lacked (a
  ## fork's arm, the facts a step added) are evaluated first, newest first,
  ## so a model that does not fit costs only those. The rest are evaluated
  ## once per model, the first time it fits: a step may have searched a
  ## rewritten query (`checkExact`'s, each with the same models by its own
  ## argument, or a recursive value's definition substituted away), and the
  ## evaluation makes the reuse rest on the model alone. A model that fails
  ## its own query's roots is dropped.
  var left = satModelVisits
  var i = satModels.high
  while i >= 0:
    if satModels[i].m.ctx.raw != ctx.raw:
      dec i
      continue
    var ok = true
    for j in countdown(query.high, 0):
      if astId(ctx, query[j].raw) in satModels[i].ids: continue
      let n = queryTermCount(ctx, [query[j]])
      if n > left:
        return false
      left -= n
      chargeWalkerTerms(n)
      chargeWalkWork()
      if not holdsIn(satModels[i].m, query[j]):
        ok = false
        break
    if ok and not satModels[i].checked:
      for r in satModels[i].held:
        if not modelHolds(ctx, satModels[i].m, r):
          ok = false
          break
      if ok: satModels[i].checked = true
      else:
        satModels.delete(i)
        dec i
        continue
    if ok:
      return true
    dec i
  false

proc keepSatModel*(ctx: Z3Context; m: Z3Model; query: openArray[Z3Bool]) =
  ## RFC-0016 int6 D1d. Keeps `m`, the model `checkCapped` found for
  ## `query`, the oldest kept dropped past `satModelsKept`.
  if m == nil: return
  var kept = SatModel(m: m, held: @query)
  for r in query: kept.ids.incl astId(ctx, r.raw)
  if satModels.len >= satModelsKept: satModels.delete(0)
  satModels.add kept

proc refuteStatus*(ctx: Z3Context; query: openArray[Z3Bool];
                  settings: SymexSettings; rlimit0: uint): Z3Status =
  ## RFC-0016 int6 D1d. `checkCapped(..).status` for a caller that acts only
  ## on `zsUnsat` (a pruning check: `loopArmInfeasible`, `pathInfeasible`,
  ## `pruneFactsHold`, `decideUndefined`, a variant field outside its
  ## branch). A query a kept model satisfies is SAT without a search
  ## (`satByModel`); a SAT search's model is kept for the next.
  ##
  ## Why: a check's fixed cost is a fresh Z3 context (`ownContextSolver`),
  ## the default solver's set-up and the per-query passes, about 5 ms
  ## whatever the query (`walkerContextUnits`), and a fresh
  ## context is what makes a search a function of its query alone (RFC-0005
  ## S8bm: the walk's context moved B1-1's target query from 172,215 units
  ## to 3,365,417 and 11,771,578; a reused context recycles the ids of freed
  ## terms, so it carries the same history). So the cost is not cut by
  ## sharing a context but by not searching: at a fork the parent's model
  ## satisfies one arm, and only the other is searched. Every search that
  ## does run is the one it was. A satisfying model is a model, so the
  ## verdict is the search's or the search's `zsUnknown`, and these callers
  ## read both alike (not refuted); only the units and the wall time move.
  # A walk out of work refutes nothing more: a search would run under what is
  # left (`workLeftRLimit`, 1 unit) yet still pay its context, and the walk
  # stops at its next `shouldStop`. `zsUnknown` is what these callers read as
  # not refuted (the arm is kept), so no search runs and no model decides.
  # Measured (int6 D1d, k9cg FilterIt at unroll 5): 7,217 such searches ran
  # between the cap and the walk's end, 1,000.0M -> 1,237.2M units.
  if walkWorkExhausted: return zsUnknown
  if satByModel(ctx, query): return zsSat
  let r = checkCapped(ctx, query, settings, rlimit0)
  if r.status == zsSat: keepSatModel(ctx, r.m, query)
  r.status

proc globalRoots*(base: openArray[Z3Bool]): seq[Z3Bool] =
  ## The run-wide pools every walker query asserts beside its path's own
  ## facts. Each is definitional or true of every real input, so asserting
  ## it anywhere prunes no real execution. RFC-0005 S8ag: `base` is the
  ## rest of the query; the splits it (or a pool) reaches add their axioms
  ## (`indexSplitRoots`). RFC-0005 S8n split it out of
  ## `pathRoots` so the concolic scratch solves (`concreteBranchOutcome`,
  ## `concretelyInfeasible`) see the same pools: without the closure
  ## axioms a closure call's result was free there, and every `if` on one
  ## was ambiguous.
  var roots: seq[Z3Bool]
  # RFC-0005 S7 (§2.4): the parseInt digits-gate pool that was drained here is
  # GONE. It asserted `startsWith(s,"-") => toInt(tail) >= 0` into EVERY check
  # run-wide, so a `parseInt` lowered on one path pruned a sibling path that
  # never called it (a false `sxUnsat`), and on its own path it deleted the
  # `"-<non-digit>"` inputs Nim RAISES on instead of routing them. That case
  # is now part of `iekStrToInt`'s raise predicate. What remains below is the
  # audited cross-path list, pinned against this proc's source by
  # `tests/tsymex_rfc0005_s7_closure.nim`.
  # Phase 15 C2b (ADR-0009 D6): drain the GROUND closure-call axioms
  # (`implies(branch_conds_i, r == v_i)`) into every check. RFC-0005 S7: `r`
  # is a fresh constant PER CALL OCCURRENCE (was the funcSym applied to the
  # occurrence's `(env, args)`, which equated two calls with equal arguments
  # even across an intervening heap write -- a false `sxUnsat`). Each axiom
  # mentions only its own occurrence's `r`, so it is DEFINITIONAL: it never
  # prunes a model of any other symbol, only fixes `r`. Admission: minted
  # only from `taint == {}` body sub-paths (a tainted arm is dropped and
  # recorded, `ceClosureBodyUncertain`).
  for c in currentClosureCallAxioms:
    roots.add c
  # RFC-0005 S8as: the entry values' type facts (`globalEntryFacts`).
  for c in pointerFacts:          # RFC-0016 INT-83: the casts' facts
    roots.add c
  for c in crossSortFacts:        # RFC-0016 INT-90: two views of one address
    roots.add c
  for c in globalEntryFacts:
    roots.add c
  # Round-4 Slice B (ADR-0026): drain the strip decomposition constraints
  # into every check — definitional clauses over per-occurrence fresh
  # strings (see `stripDecompConds`' doc for the soundness argument).
  for c in stripDecompConds:
    roots.add c
  # RFC-0005 S8bj: the recursive `replace` values' definitions.
  for c in regexRecDefConds:
    roots.add c
  # RFC-0005 S8bt: and their facts.
  for c in regexRecFactConds:
    roots.add c
  # RFC-0005 S8f: every allocated table's / set's size is at least its
  # number of distinct present key terms (`ContainerCardRegistry`). True of
  # every real table for any values of the terms, so it prunes only
  # unrealizable models (`t.len == 0 and t.hasKey("a")`), never a real
  # input; and every model that satisfies it is the one the extractors
  # render.
  let cardConds = containerCardConds()
  for c in cardConds:
    roots.add c
  # RFC-0005 S8ag: the axioms of each one-character `str.indexof` split the
  # query reaches, with their chain facts. Definitional over each split's
  # own fresh constants (`indexSplitRoots`), so they prune no model.
  var reach = @base
  reach.add roots
  for c in indexSplitRoots(currentContext(), reach):
    roots.add c
  # RFC-0016 INT-82: an allocation is no object of the entry state. True of
  # every real execution (the entry state predates the walk), so it prunes no
  # real input (`refProvenanceRoots`).
  reach.add roots
  for c in refProvenanceRoots(currentContext(), reach):
    roots.add c
  roots

proc pathRoots*(path: Path; extra: openArray[Z3Bool] = []): seq[Z3Bool] =
  ## Every assertion a walker query of `path` is issued with, as `trySolve`
  ## has always made them (RFC-0005 S8k factored it out so the
  ## loop-iteration feasibility check asks the same question). RFC-0005
  ## S8ag: `extra` (that check's arm) joins the query here, ahead of
  ## `globalRoots`, so a split only the arm reaches has its axioms.
  var roots: seq[Z3Bool]
  for c in path.pc:
    roots.add c
  # Phase 16 ADR-0012: defect-survivor feasibility facts (the `not overflow`/
  # `not divByZero`/`not parseIntRaise` negations) are asserted alongside `pc`,
  # so the effective path condition (pc ++ defectSurvivorPc) is identical to the
  # pre-ADR-0012 behaviour for every non-closure path. The split only changes
  # which of these a closure's return-axiom uses as its implication guard.
  for c in path.defectSurvivorPc:
    roots.add c
  roots.add extra
  roots.add globalRoots(roots)
  when defined(symexTestInjectWalkerFault):
    injectShapeFault("roots")  # RFC-0005 S8ce: the query's roots held
  roots

proc trySolve*(ctx: Z3Context,
              path: Path,
              params: seq[IRParam],
              settings: SymexSettings = defaultSymexSettings(),
              initialEnv: Env = initOrderedTable[string, SymVal]()
              ): tuple[status: SymexStatusKind, witness: RawWitness,
                       undefWhy: string] =
  ## `undefWhy` (RFC-0005 S8k) says why an `sxUnknown` is one, for the
  ## caller's `beSolverUndef` message: the `maxSeqLen` cap, or Z3's own
  ## `reason_unknown` (an exhausted `queryRLimit`, an incomplete theory).
  let roots = pathRoots(path)
  inc symexZ3CallCount
  when defined(symexQueryStats):
    let unitsBefore = ownContextUnits   # RFC-0005 S8bp
  let (r, s, model, why) = checkCapped(ctx, roots, settings,
                                       settings.budget.queryRLimit)
  when defined(symexQueryStats):
    if not symexQueryStatsPaused:
      # Counted from the same sources `pathRoots` collects, so it tracks
      # them by construction rather than by a hand-maintained tally.
      recordQueryStat(s, roots.len,
        (case r
         of zsSat: "sat"
         of zsUnsat: "unsat"
         else: "unknown"), unitsBefore)
  case r
  of zsSat:
    let m = model
    # Use initialEnv when provided — mutations may have rebound params
    # to post-store SymVals; the witness wants the pre-call value.
    let envForExtract = if initialEnv.len > 0: initialEnv else: path.env
    # ADR-0013 D5 (Slice 2): snapshot the WINNING path's heaps so the witness
    # serializer can select a ref-to-variant pointee's active-arm field values.
    currentVariantHeaps = path.heaps
    currentWinningGlobals = @[]                     ## RFC-0005 S8bn
    for k in path.env.keys:
      if isGlobalEnvName(k): currentWinningGlobals.add k
    var wit = extractWitness(m, envForExtract, params)
    (wit.pins, wit.pinsComplete) = modelPins(m, envForExtract, params)   ## RFC-0016 K10b
    (status: sxSat, witness: wit, undefWhy: "")
  of zsUnsat:
    (status: sxUnsat, witness: RawWitness(), undefWhy: "")
  of zsUnknown:
    (status: sxUnknown, witness: RawWitness(), undefWhy: why)

const defaultLoopPruneRLimit* = 250_000'u
  ## RFC-0005 S8k. The Z3 `rlimit` each loop-iteration feasibility check
  ## (`loopArmInfeasible`) runs under, unless the caller's `queryRLimit` is
  ## smaller. A check that runs out is `zsUnknown`, which never prunes: the
  ## arm is walked exactly as before S8k, so the bound trades pruning power
  ## for time and nothing else. Small on purpose: the check runs once per
  ## unrolled iteration per path, and a concretely-decided guard never
  ## reaches the solver at all (it simplifies to a literal first).


var ctxPruneLog* {.threadvar.}: seq[PruneFact]
  ## RFC-0005 S8as/S8ax. Every drop a feasibility check against the path's
  ## own facts decided (`loopArmInfeasible`, `pathInfeasible`, and a cache
  ## hit's re-check, `pruneFactsHold`), in walk order. Such a drop depends on
  ## the caller's context, not only on the arguments, so a call whose walk
  ## dropped one returned a summary true only where the dropped facts are
  ## still infeasible. S8as made such a call uncacheable (it counted the
  ## drops); S8ax keys its summary on them instead: the call cache stores,
  ## per drop, the facts the callee's walk added beyond the caller's
  ## (`CallCacheEntry.pruneFacts`), and a hit replays the summary only where
  ## each is still UNSAT under the replaying caller's facts. `fib(n)` under
  ## `n in 3..4` cached `fib(n - 2)`'s one returned path from inside
  ## `fib(n - 1)`'s frame (where `n - 2 < 2` had been dropped): replayed at
  ## the outer call without the check it was a false `sxUnsat` (S8as).
  ## Reset per run.

proc logPrune*(path: Path; extra: openArray[Z3Bool]) =
  ## RFC-0005 S8ax. Record a context-dependent drop (`ctxPruneLog`).
  ctxPruneLog.add PruneFact(pc: path.pc, dsp: path.defectSurvivorPc,
                            extra: @extra)

func loopPruneRLimit*(settings: SymexSettings): uint =
  ## RFC-0005 S8k. `defaultLoopPruneRLimit`, or the caller's `queryRLimit`
  ## when that is set and smaller (a caller's budget is never exceeded).
  let q = settings.budget.queryRLimit
  if q != 0 and q < defaultLoopPruneRLimit: q else: defaultLoopPruneRLimit

proc loopArmInfeasible*(ctx: Z3Context; path: Path; arm: Z3Bool;
                       settings: SymexSettings): bool =
  ## RFC-0005 S8k. True only when `path`'s full query (`pathRoots`) plus
  ## `arm` is UNSAT on its own -- the arm of a loop guard no real execution
  ## on this path can take. A literal `arm` is decided without the solver;
  ## `zsUnknown` (the budget, or an UNSAT only the `maxSeqLen` cap caused)
  ## is `false`: an undecided arm is walked. Sound for pruning: the pruned
  ## arm's every later query would carry the same UNSAT constraints, so no
  ## finding and no model is lost; what is lost are declines an infeasible
  ## arm would have recorded, which is the precision S8k is after.
  case guardLiteral(arm)   # RFC-0005 S8bv: not its printed form
  of glFalse: return true
  of glTrue: return false
  of glOpen: discard
  result = refuteStatus(ctx, pathRoots(path, [arm]), settings,
                        loopPruneRLimit(settings)) == zsUnsat
  if result: logPrune(path, [arm])   # RFC-0005 S8as/S8ax

proc pathInfeasible*(ctx: Z3Context; path: Path;
                    settings: SymexSettings): bool =
  ## RFC-0005 S8an. True only when `path`'s full query (`pathRoots`) is
  ## UNSAT: no real execution reaches it. Bounded and sound for pruning
  ## exactly as `loopArmInfeasible` is (an undecided query keeps the path).
  result = refuteStatus(ctx, pathRoots(path), settings,
                        loopPruneRLimit(settings)) == zsUnsat
  if result: logPrune(path, [])   # RFC-0005 S8as/S8ax

var symexIfArmsPruned* {.threadvar.}: int
  ## RFC-0005 S8as. Counts the `if` arms (and else paths) the `wmExplore`
  ## walk dropped as infeasible inside a recursive frame (`ifArmInfeasible`).
  ## Always on, like `symexLoopIterations`; tests reset it and read it.

var symexIfArmsChecked* {.threadvar.}: int
  ## RFC-0005 S8ax. Counts the `if` arms (and else paths) `ifArmInfeasible`
  ## sent to the solver. Always on; tests reset it and read it.

proc unwrittenIndependent*(ctx: Z3Context; path: Path; v: SymVal;
                          extra: openArray[Z3Bool];
                          settings: SymexSettings): bool =
  ## RFC-0005 S8bw (item 2). True when `v`, an element read at a symbolic
  ## index, is the same whatever the unwritten parts it mentions hold, on
  ## every execution of `path` under `extra`: the query with `v` differing
  ## from its copy over fresh stand-ins of those parts is UNSAT
  ## (`gArr[k] = 5` then `gArr[k]` reads an `ite` over every element, the
  ## unwritten ones included, and is 5 on every path). Bounded as the loop
  ## pruning check is; an undecided query is a dependence.
  var froms, tos: seq[RawZ3Ast]
  var keep: seq[Z3AnyAst]
  for a in glUnwrittenAsts:
    froms.add a.raw
    keep.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_fresh_const(ctx.raw,
      "__glUnwrittenAlt", ctx.checkErr Z3_get_sort(ctx.raw, a.raw)))
    tos.add keep[^1].raw
  if froms.len == 0: return true
  var leaves: seq[RawZ3Ast]
  svAsts(v, leaves)
  var diffs: seq[RawZ3Ast]
  for l in leaves:
    let alt = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_substitute(ctx.raw, l,
      cuint(froms.len), cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
      cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
    keep.add alt
    keep.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_not(ctx.raw,
      checkedEq(ctx, l, alt.raw)))
    diffs.add keep[^1].raw
  if diffs.len == 0: return true
  let differs = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_or(ctx.raw,
    cuint(diffs.len), cast[ptr UncheckedArray[RawZ3Ast]](diffs[0].addr)))
  var arm = differs
  for c in extra: arm = arm and c
  loopArmInfeasible(ctx, path, arm, settings)

proc unwrittenLeafSplit*(ctx: Z3Context; path: Path; v: SymVal;
                        extra: openArray[Z3Bool];
                        settings: SymexSettings): SymVal =
  ## RFC-0005 S8bz (item 3). The aggregate `v`, an element read, with each
  ## scalar leaf that mentions an unwritten part but is the same whatever
  ## those parts hold (`unwrittenIndependent`'s query) over fresh stand-ins of
  ## them: the read of that leaf observes nothing. Any other leaf keeps its
  ## mention. Each leaf is asked in the sort the value holds it, not a heap
  ## cell's (`svLeafTerms`): the `Int` view's `ubv_to_int` is past the budget
  ## of this bounded query.
  var froms, tos: seq[RawZ3Ast]
  var keep: seq[Z3AnyAst]
  for a in glUnwrittenAsts:
    froms.add a.raw
    keep.add wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_fresh_const(ctx.raw,
      "__glUnwrittenAlt", ctx.checkErr Z3_get_sort(ctx.raw, a.raw)))
    tos.add keep[^1].raw
  if froms.len == 0: return v
  var inRange = mkBool(true)
  for c in extra: inRange = inRange and c
  proc go(sv: SymVal): SymVal =
    result = sv
    case sv.kind
    of svTuple:
      for i in 0 ..< sv.fields.len: result.fields[i] = go(sv.fields[i])
    of svArray:
      for i in 0 ..< sv.arrElems.len: result.arrElems[i] = go(sv.arrElems[i])
    of svVariant:
      for i in 0 ..< sv.vPlainFields.len:
        result.vPlainFields[i] = go(sv.vPlainFields[i])
      for t, fs in sv.vArmFields:
        for i in 0 ..< fs.len: result.vArmFields[t][i] = go(fs[i])
      result.vDisc = new(SymVal)
      result.vDisc[] = go(sv.vDisc[])
    of svBV8, svBV16, svBV32, svBV64, svInt, svBool, svFloat32, svFloat64,
       svString:
      if unwrittenIn(sv).len == 0: return
      let l = rawAnyAstOf(sv)
      let alt = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_substitute(ctx.raw, l,
        cuint(froms.len), cast[ptr UncheckedArray[RawZ3Ast]](froms[0].addr),
        cast[ptr UncheckedArray[RawZ3Ast]](tos[0].addr)))
      let differs = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_not(ctx.raw,
        checkedEq(ctx, l, alt.raw)))
      if loopArmInfeasible(ctx, path, differs and inRange, settings):
        result = svWithRaw(ctx, sv, alt)
    else: discard
  go(v)

var symexLoopIterations* {.threadvar.}: int
  ## RFC-0005 S8k. Counts the loop bodies the `wmExplore` k-unroll walks
  ## (one per feasible iteration per path). Always on, like
  ## `symexZ3CallCount`; tests reset it and read it to pin that feasibility
  ## pruning keeps nested loops linear in their trip counts.

# ---- the per-run reset ----------------------------------------------------

proc resetWalkSolveState*(settings: SymexSettings) =
  ## RFC-0016 INT-34 B5. The per-run reset of every threadvar of this module
  ## that holds run state, called by `resetSymexRunState` (the statements it
  ## held for them, in their order there). The rest are not per-run: the
  ## thread's running totals (`ownContextUnits`, `symexZ3CallCount`, the
  ## counters a suite resets itself), the linked Z3's decl kinds (probed once
  ## per thread), and the stall deadline `beginStallDeadline` arms per walk.
  queryTimeoutMsCur = settings.budget.queryTimeoutMs   ## RFC-0005 S8bu
  queryTimedOutFlag = false                            ## RFC-0005 S8bu
  nativeStackCutFlag = false                           ## RFC-0005 S8ca
  walkUnitsBase = ownContextUnits                      ## RFC-0016 K7
  walkerWorkBase = walkerWorkUnits
  satModels = @[]
  walkRLimitCur = settings.budget.walkRLimit
  walkWorkExhausted = false
  walkStalled = false                                  ## RFC-0016 INT-57
  tailUnitsCeil = 0                                    ## RFC-0016 W3-z R9
  tailWorkExhausted = false
  tailUnitsRun = 0                                     ## RFC-0016 W3-z int4r
  extractionErrors = @[]   ## Phase 15 F7: reset per-run float-extraction error sink
  unknownExnWarnings = @[]        ## Phase 15 E4: reset unknown-exn-type warning sink
  currentClosureCallAxioms = @[]         ## Phase 15 C2b: reset ground-axiom sink
  ctxPruneLog = @[]                              ## RFC-0005 S8ax
  currentVariantHeaps = initTable[string, Z3AnyAst]() ## ADR-0013 D5 (Slice 2)
  currentWinningGlobals = @[]                         ## RFC-0005 S8bn
  ptrLeafAims = initTable[int64, PtrLeafAim]()        ## RFC-0005 S8bn
  heapWitnessNominalRegistry = initTable[string, IRType]()  ## Cluster H H_witness

# RFC-0016 S8ck-r (INF-04): this module's per-thread state goes back to
# default on `releaseSymexThreadState` (src/nelli/thread_state.nim), so
# a thread that exits leaks none of it. A threadvar added to this module
# is named here, or tsymex_0016_s8ckr_threadstate_audit fails.
import ../thread_state

proc releaseThreadState() {.nimcall, gcsafe, raises: [].} =
  releaseToDefault(
    currentVariantHeaps, currentWinningGlobals,
    heapWitnessNominalRegistry, currentClosureCallAxioms,
    extractionErrors, unknownExnWarnings, ptrLeafAims,
    symexTargetSolveStats, ownContextUnits, symexZ3CallCount, satModels,
    seqCapDeclKinds, byteDomainKinds, deepTermsLeftAlone,
    theoryFreeNeedsSimple, queryTimeoutMsCur, nativeStackCutFlag,
    queryTimedOutFlag, walkerWorkBase, walkUnitsBase, walkRLimitCur,
    walkWorkExhausted, tailUnitsCeil, tailWorkExhausted, tailUnitsRun,
    intDivDeclKinds, int2bvDeclKind, eqDeclKind, ctxPruneLog,
    symexIfArmsPruned, symexIfArmsChecked, symexLoopIterations,
    eqsSplitCaps, fpIntervalDeclKinds, stallDeadline, walkStalled,
    bvExtDeclKinds)
  when defined(symexQueryStats):
    releaseToDefault(
      symexQueryStats, symexQueryStatsPaused, symexFactsFirstOff,
      symexStepStats, symexPerturbConsts, perturbSerial, symexEqsSplits)

registerThreadStateRelease(releaseThreadState)
