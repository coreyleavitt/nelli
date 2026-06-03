## Symex IR + public result/target/settings types.
##
## NB: imports of std/tables / std/sequtils / std/strutils live near
## the bottom of the file (right above the rendering helpers); the
## rest of this module is type definitions only.

import std/tables
export tables
##
## The architecture (per [docs/SYMEX_PLAN.md](../../../docs/SYMEX_PLAN.md))
## is a classic front-end / back-end split:
##
##   typed Nim AST  ─[dsl_parser]→  SymexProgram (this file)
##                                       │
##                                       └─[runtime]→  SymexResult
##
## The IR is intentionally small. Each phase widens it; this file
## carries only the Phase-1 fragment (int/bool, arithmetic +
## comparison, `if` / `block` / target labels). Later phases extend
## with `let`, `assign`, `return`, composite types, function calls,
## loops, etc.
##
## `ref object` is used for the variant nodes so the parser can
## construct them with ordinary heap allocation; the runtime walks
## them without ever needing to mutate the structure (it's an
## immutable view).

type
  IRBinop* = enum
    bAdd, bSub, bMul, bDiv, bMod
    bAnd, bOr, bXor              ## bool×bool→bool, or bitwise on integers —
                                 ## the runtime dispatches by operand type
    bShl, bShr                   ## bit-shifts on integers; sign-aware shr
                                 ## maps to ashr (signed) / lshr (unsigned)
    bEq, bNe                     ## polymorphic equality
    bLt, bLe, bGt, bGe           ## comparison; signed vs unsigned by IRType

  IRUnop* = enum
    uNot                         ## boolean negation
    uNeg                         ## arithmetic negation

  IRTypeKind* = enum
    itInt    ## Any fixed-width Nim integer
    itBool
    itString ## Phase 5: Nim `string`, encoded as Z3String.
    itTuple  ## Records: tuples (anonymous or named) and objects.
             ## Both lower to `svTuple` with per-field SymVals.
    itArray  ## Static `array[N, T]` — Phase 4 supports primitive `T`
             ## and tuples-of-primitive `T`; nested arrays defer to #142.
    itSeq    ## Phase 5: dynamic `seq[T]` via Z3 array theory.
    itTable  ## Phase 5: `Table[K, V]` via two Z3 arrays (data + present).
    itSet    ## Phase 5: `HashSet[T]` via `Z3Array[T, Z3Bool]`.
    itVariant ## Phase 11: Nim variant object — a tagged sum type.
              ## Discriminator + per-arm field records, modelled
              ## structurally rather than flattened. See PHASE11_PLAN.md.
    itMultiVariant ## Phase 14 (ADR-0003 D1): Nim variant object with
              ## MULTIPLE `nnkRecCase` blocks — a product of tagged sum
              ## axes. Single-recCase objects keep using `itVariant`;
              ## `itMultiVariant` requires `mvAxes.len >= 2` (asserted by
              ## `mkMultiVariant`). The two kinds are intentionally
              ## structurally disjoint: canonical encodings differ
              ## (`Vr:` vs `MVr:`), cache partitions are disjoint by
              ## design.

  VariantArm* = object
    ## One arm of an `itVariant`. The tag ordinal is the
    ## discriminator value that selects this arm; the field
    ## names + types describe the record valid under that tag.
    tagOrdinal*: int
    tagName*:    string
    fieldNames*: seq[string]
    fieldTypes*: seq[IRType]
    isElse*:     bool
      ## Phase 14 cycle A2 (forward-compat): true iff this arm is the
      ## `else:` branch of an `nnkRecCase`. Walker-time arm membership
      ## constraint for an else-arm is `AND(disc != other.tagOrdinal)`
      ## over the non-else arms on the same axis — computed lazily,
      ## never materialized as a tag-set seq (catastrophic for non-
      ## enum discriminator types per A3). Default false preserves
      ## Phase 11 behavior for every existing `VariantArm` literal.

  VariantAxis* = object
    ## Phase 14 (ADR-0003 D1). One discriminator axis of an
    ## `itMultiVariant`. Each `nnkRecCase` block in a multi-recCase
    ## object becomes one `VariantAxis`.
    discName*:     string
    discTy*:       IRType
    arms*:         seq[VariantArm]
    discTags*: seq[tuple[name: string, ord: int]]
      ## Phase 14 cycle A2. Full (name, ordinal) domain of `discTy`'s
      ## enum, populated by typebridge. The walker uses ordinals to
      ## bound the disc range when an `else:` arm is present on this
      ## axis; the witness emitter uses names to render `of <tagName>:`
      ## branches for else-covered ordinals.

  IRType* = ref object  ## ref because itTuple/itArray/itVariant recurse.
    case kind*: IRTypeKind
    of itInt:
      width*: int
      signed*: bool
    of itBool:
      discard
    of itTuple:
      fields*: seq[IRType]
      fieldNames*: seq[string]   ## "" for positional / anonymous; nominal
                                 ## name for named-tuples and objects.
      objectName*: string        ## "" for tuple types; the nominal name
                                 ## (e.g., "Point") for object types — the
                                 ## witness constructor uses it.
    of itArray:
      elemTy*: IRType
      size*: int
    of itString:
      discard
    of itSeq:
      seqElemTy*: IRType
    of itTable:
      tabKeyTy*: IRType
      tabValTy*: IRType
    of itSet:
      setElemTy*: IRType
    of itVariant:
      vDiscName*:        string    # discriminator field name (any name, not just "kind")
      vDiscTy*:          IRType    # must be itInt (the enum's int representation)
      vArms*:            seq[VariantArm]   # arm-specific fields ONLY
      vDiscTags*:        seq[tuple[name: string, ord: int]]
        ## Phase 14 cycle A2. The disc enum's full (name, ordinal)
        ## domain, populated by typebridge. The walker uses the
        ## ordinals to bound the disc range when an `else:` arm is
        ## present (the non-else arms' equalities don't cover the
        ## full legal enum range). The witness emitter uses the
        ## names to render `of <tagName>:` branches for else-covered
        ## ordinals — variant construction needs static enum literals,
        ## which the of-arm tagNames alone don't supply.
      vObjectName*:      string
      vPlainFieldNames*: seq[string]
                                    # Phase 11 post-cycle-12: plain
                                    # (non-recCase) fields shared
                                    # across arms. Excluded from
                                    # arm.fieldNames so they're
                                    # allocated once and survive
                                    # discriminator reassignment.
      vPlainFieldTypes*: seq[IRType]
    of itMultiVariant:
      mvObjectName*:      string
      mvPlainFieldNames*: seq[string]
        ## Same role as `vPlainFieldNames` in `itVariant`: plain
        ## (non-recCase) prefix fields shared across all axes.
      mvPlainFieldTypes*: seq[IRType]
      mvAxes*:            seq[VariantAxis]
        ## One entry per `nnkRecCase` block. Invariant: `mvAxes.len
        ## >= 2`; enforced by `mkMultiVariant`. The parser emits
        ## `itVariant` (not `itMultiVariant`) for single-recCase
        ## objects.

  IRExprKind* = enum
    iekIntLit, iekBoolLit, iekVar, iekBinop, iekUnop
    iekField     ## Phase 4: positional field access into a tuple/object.
    iekIndex     ## Phase 4: array index access; `arr[idx]`.
    iekArrayLit  ## Phase 4: static array literal `[a, b, c]`.
    iekSeqLen    ## Phase 5: `s.len` on a `seq[T]`. Returns Z3Int.
    iekStrLit    ## Phase 5: string literal (Z3String constant).
    iekContains  ## Phase 5: `x in s` / `t.contains(k)`. Returns Z3Bool.
    iekSeqAdd    ## #145: `s.add(v)` — returns new svSeq.
    iekSeqDel    ## #145: `s.del(i)` — Nim swap-with-last semantics.
    iekSeqInsert ## #145: `s.insert(v, i)` — shift later elements.
    iekSeqPop    ## #143: `s.pop()` — returns the popped value;
                 ## a separate isAssign updates the seq.
    iekTableSet  ## #145: returns new svTable with `[k]=v`.
    iekTableDel  ## #145: returns new svTable with k absent.
    iekSetIncl   ## #145: returns new svSet with elem included.
    iekSetExcl   ## #145: returns new svSet with elem excluded.

  IRExpr* = ref object
    case kind*: IRExprKind
    of iekIntLit:
      ival*: int64
    of iekBoolLit:
      bval*: bool
    of iekVar:
      vname*: string
    of iekBinop:
      bop*: IRBinop
      lhs*, rhs*: IRExpr
    of iekUnop:
      uop*: IRUnop
      operand*: IRExpr
    of iekField:
      obj*:        IRExpr
      fieldIx*:    int
      fieldName*:  string   ## for diagnostics; runtime dispatches by index
    of iekIndex:
      arr*:  IRExpr
      idx*:  IRExpr
    of iekArrayLit:
      lelems*: seq[IRExpr]
      lelemTy*: IRType
    of iekSeqLen:
      lenObj*: IRExpr
    of iekStrLit:
      sval*: string
    of iekContains:
      container*: IRExpr
      key*: IRExpr
    of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
      mutRecv*: IRExpr
      mutArg*:  IRExpr
    of iekSeqDel:
      delSeq*: IRExpr
      delIdx*: IRExpr
    of iekSeqInsert:
      insSeq*: IRExpr
      insVal*: IRExpr
      insIdx*: IRExpr
    of iekSeqPop:
      popSeq*: IRExpr
    of iekTableSet:
      tabRecv*: IRExpr
      tabKey*:  IRExpr
      tabVal*:  IRExpr

  IRStmtKind* = enum
    isBlock
    isIf
    isLet
    isAssign          ## #145: env reassignment for mutations
                      ## (s = newSeq, t = newTable, etc.)
    isWhile           ## Phase 6: bounded loop k-unrolled per
                      ## `SymexSettings.maxLoopUnwind`.
    isBreak           ## Phase 6: terminate enclosing loop body.
    isContinue        ## Phase 6: skip to next iteration's guard.
    isReturn          ## `return [expr]` — terminate this path; in callees
                      ## the optional value binds the call's return symbol
    isAssert          ## `symexAssert(cond)` — under a label target,
                      ## tighten path condition with cond; under
                      ## `tAssertionViolation`, fork to search for
                      ## `not cond` reachability
    isCall            ## A-normalised call to a user-defined proc; lookup
                      ## via `SymexProgram.procs[callee]`, walk the body
                      ## under arg bindings, bind retval to the named
                      ## fresh symbol if non-void
    isVariantField    ## Phase 11 cycle 5: A-normalised variant
                      ## arm-field access `let r = obj.field`. The
                      ## walker forks: in-arm path adds `disc IN
                      ## matchingTags` to pc and binds `r`; out-of-
                      ## arm path adds the negation and (under
                      ## stkFieldDefect target) is solved for a
                      ## witness.
    isVariantReassign ## Phase 11 cycle 6: `obj.kind = tagLiteral` —
                      ## reassigns the discriminator of a variant
                      ## variable in env. The walker updates vDisc
                      ## to the literal tag's BV constant and zero-
                      ## initialises the new arm's primitive fields
                      ## (Nim's runtime semantics).
    isVariantReassignSymbolic ## Phase 14 cycle A4 (ADR-0003 D4).
                      ## `obj.kind = symbolicRhs` — walker forks one
                      ## path per arm-ordinal of the discriminator's
                      ## enum domain; each path is constrained
                      ## `rhsExpr == k_ord`. Existing arm-field
                      ## SymVals are PRESERVED across the fork
                      ## (no zero-init — that's the static-tag
                      ## path's job per ADR-0003 D4).
    isIndex           ## A-normalised array index `let r = arr[idx]`.
                      ## Symbolic indexes fork the path: in-bounds path
                      ## adds `0 <= idx < N` to pc and binds r to the
                      ## ite-chain over elements; OOB path adds the
                      ## negation and (if target = stkIndexError) records
                      ## a witness.
    isTargetLabel     ## `symexTarget("name")`
    isUnsupported     ## any AST kind the Phase-1 parser doesn't model

  IRBranch* = object
    cond*: IRExpr     ## guard for this arm (already negation-folded for elif)
    body*: IRStmt

  IRStmt* = ref object
    case kind*: IRStmtKind
    of isBlock:
      stmts*: seq[IRStmt]
    of isIf:
      branches*: seq[IRBranch]
      elseBody*: IRStmt          ## nil if no `else:` clause
    of isLet:
      lname*: string
      lty*: IRType
      lvalue*: IRExpr
    of isAssign:
      aname*: string
      avalue*: IRExpr
    of isWhile:
      wcond*: IRExpr
      wbody*: IRStmt
    of isBreak, isContinue:
      discard
    of isReturn:
      retExpr*: IRExpr   ## nil for void returns; callees use this to
                         ## carry the value back to the caller
    of isCall:
      callee*: string
      cargs*: seq[IRExpr]
      retName*: string   ## "" for void; else the fresh let-name the
                         ## return value binds to
      retTy*: IRType     ## return type; tBool() sentinel when void
      opaque*: bool      ## #137: when true, the walker doesn't
                         ## resolve the body — fresh retSym + path
                         ## uncertainty. Used for IO / effectful
                         ## stdlib procs.
    of isIndex:
      ixRetName*: string
      ixArr*:     IRExpr
      ixIdx*:     IRExpr
      ixElemTy*:  IRType
    of isVariantField:
      vfRetName*:       string
      vfRecv*:          IRExpr
      vfFieldName*:     string
      vfFieldTy*:       IRType
      vfMatchingTags*:  seq[int]  ## tag ordinals of arms containing
                                  ## `vfFieldName`
    of isVariantReassign:
      vrObjName*:       string    ## the variant variable in env
      vrNewTag*:        int       ## the new tag ordinal
      vrTagName*:       string    ## diagnostic, e.g. "skSquare"
    of isVariantReassignSymbolic:
      vrsObjName*:      string    ## the variant variable in env
      vrsDiscName*:     string    ## which axis (itMultiVariant); ""
                                    ## for single-axis itVariant
      vrsRhs*:          IRExpr    ## the symbolic RHS expression
    of isAssert:
      acond*: IRExpr
    of isTargetLabel:
      tname*: string
    of isUnsupported:
      reason*: string            ## human-readable diagnostic

  IRParam* = object
    name*: string
    ty*: IRType
    rangeLo*: int64
    rangeHi*: int64
    hasRange*: bool
    isVar*: bool       ## #140: var T param — callee mutations propagate
                       ## back to the caller's binding on return.

  ProcSig* = object
    name*:    string
    params*:  seq[IRParam]
    body*:    IRStmt
    retTy*:   IRType   ## tBool() sentinel for void; the runtime keys
                       ## off `isVoid` rather than the type itself
    isVoid*:  bool

  SymexProgram* = object
    params*: seq[IRParam]
    body*: IRStmt
    procs*: Table[string, ProcSig]   ## transitively reachable callees

# ---- Public symex-level types -----------------------------------------------

type
  SymexTargetKind* = enum
    stkLabel               ## reach a `symexTarget("name")`
    stkAssertionViolation  ## falsify any `symexAssert(cond)` on any path
    stkIndexError          ## find an array OOB index reachable on any
                           ## `arr[i]` access (Phase 4 cycle 8)
    stkFieldDefect         ## Phase 11 cycle 5: find a variant
                           ## arm-field access whose discriminator is
                           ## not in the field's arm set — the SUT
                           ## would raise FieldDefect at runtime.

  SymexTarget* = object
    case kind*: SymexTargetKind
    of stkLabel:
      label*: string
    of stkAssertionViolation:
      discard
    of stkIndexError:
      discard
    of stkFieldDefect:
      discard

  SymexStatusKind* = enum
    sxSat       ## witness found
    sxUnsat     ## target proved unreachable / no violation possible
    sxUnknown   ## solver gave up, or every path hit an `isUnsupported` node

  Interval* = object
    ## Closed integer interval `[lo, hi]`. Used by the abstraction
    ## layer (ADR-0001) for range tracking and BV-window containment.
    lo*, hi*: int64

  AbstractionEvidence* = enum
    aeTypeRange    ## "from typedesc range[lo..hi] (or Natural/Positive)"
    aeNumericFold  ## "from interval-composing arithmetic"
    aeVariantDisc  ## Phase 14 A6: variant discriminator promoted to
                   ## Z3Int under `isOptimised` (ADR-0003 D6 mandatory).

  AbstractionEntry* = object
    name*:        string
    interval*:    Interval
    evidence*:    AbstractionEvidence
    derivation*:  string

  AbstractionLog* = seq[AbstractionEntry]

  SymexErrorInfo* = object
    ## Phase 14 cycle C4. Structured Z3-error record. Captured
    ## when `runSymex` catches a typed `Z3Error` at its top level.
    ## `kind` is the typed-subclass name (e.g. "Z3MemoryError"); a
    ## bare `Z3Error` not in any subclass lands here as "Z3Error".
    kind*: string
    msg*:  string

  CallStat* = object
    name*:      string
    walked*:    int   ## times this callee's body was actually walked
    cacheHits*: int   ## times the call was served from the summary cache

  CallStats* = seq[CallStat]

  SymexResult*[T] = object
    abstractions*: AbstractionLog
    callStats*:    CallStats   ## per-callee walk + cache-hit counts
    fromCache*:    bool
      ## Phase 14 cycle C1. `true` iff this result was served from
      ## the verdict cache (`:unsat`/`:unk` suffix) or the witness
      ## cache (`:sat` suffix) without re-running `runSymex`. When
      ## true, `abstractions` and `callStats` are `@[]` — those
      ## fields record THIS run's exploration, which didn't happen.
    case status*: SymexStatusKind
    of sxSat:
      witness*: T
    of sxUnsat, sxUnknown:
      discard

  IntegerSemantics* = enum
    isExact      ## BV[W] always. Phase 1 default.
    isOptimised  ## BV[W] + selective Z3Int abstraction (Phase 2 lands this).
    isLoose      ## Z3Int everywhere, unsound. Research-only.

  SymexSettings* = object
    integerSemantics*: IntegerSemantics
    queryRLimit*: uint
      ## Z3 logical step count bound. `0` (default) is unbounded —
      ## Z3's documented behavior. Non-zero enforces a deterministic
      ## resource limit: same SUT + Z3 build + budget → identical
      ## outcomes across machines (unlike wall-clock `timeout`, which
      ## is what the pre-Phase-13 `queryTimeoutMs` field's name
      ## suggested but was never actually wired). Wired into
      ## `runtime.nim:trySolve` via `Z3_solver_set_params`. Phase 13.
    maxFrontierSize*: int
    maxCallDepth*: int
    maxLoopUnwind*: int    ## Phase-6 loop unrolling cap; >= 1
    acceptUnknownAsCovered*: bool
      ## Phase 7. When `assertCoveredBy` receives `sxUnknown` from the
      ## solver (timeout, unwind exhaustion, opaque-call uncertainty),
      ## the default is to raise — we cannot *prove* coverage. Setting
      ## this to `true` downgrades UNKNOWN to a soft pass for
      ## environments that treat UNKNOWN as "best-effort attempted".

# ---- Constructors -----------------------------------------------------------
#
# Plain constructor procs over the variant types. The parser builds the
# IR at macro time using these (or the generated NimNode equivalent);
# the runtime consumes the IR built by the emitted code at runtime.

proc mkIntLit*(v: int64): IRExpr =
  IRExpr(kind: iekIntLit, ival: v)

proc mkBoolLit*(v: bool): IRExpr =
  IRExpr(kind: iekBoolLit, bval: v)

proc mkVar*(name: string): IRExpr =
  IRExpr(kind: iekVar, vname: name)

proc mkBinop*(op: IRBinop, lhs, rhs: IRExpr): IRExpr =
  IRExpr(kind: iekBinop, bop: op, lhs: lhs, rhs: rhs)

proc mkUnop*(op: IRUnop, operand: IRExpr): IRExpr =
  IRExpr(kind: iekUnop, uop: op, operand: operand)

proc mkField*(obj: IRExpr, fieldIx: int, fieldName: string = ""): IRExpr =
  IRExpr(kind: iekField, obj: obj, fieldIx: fieldIx, fieldName: fieldName)

proc mkIndex*(arr, idx: IRExpr): IRExpr =
  IRExpr(kind: iekIndex, arr: arr, idx: idx)

proc mkArrayLit*(elems: seq[IRExpr], elemTy: IRType): IRExpr =
  IRExpr(kind: iekArrayLit, lelems: elems, lelemTy: elemTy)

proc mkSeqLen*(obj: IRExpr): IRExpr =
  IRExpr(kind: iekSeqLen, lenObj: obj)

proc mkStrLit*(s: string): IRExpr =
  IRExpr(kind: iekStrLit, sval: s)

proc mkContains*(container, key: IRExpr): IRExpr =
  IRExpr(kind: iekContains, container: container, key: key)

proc mkSeqAdd*(recv, val: IRExpr): IRExpr =
  IRExpr(kind: iekSeqAdd, mutRecv: recv, mutArg: val)
proc mkSeqDel*(seqx, idx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqDel, delSeq: seqx, delIdx: idx)
proc mkSeqInsert*(seqx, val, idx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqInsert, insSeq: seqx, insVal: val, insIdx: idx)
proc mkSeqPop*(seqx: IRExpr): IRExpr =
  IRExpr(kind: iekSeqPop, popSeq: seqx)
proc mkTableSet*(recv, key, val: IRExpr): IRExpr =
  IRExpr(kind: iekTableSet, tabRecv: recv, tabKey: key, tabVal: val)
proc mkTableDel*(recv, key: IRExpr): IRExpr =
  IRExpr(kind: iekTableDel, mutRecv: recv, mutArg: key)
proc mkSetIncl*(recv, elem: IRExpr): IRExpr =
  IRExpr(kind: iekSetIncl, mutRecv: recv, mutArg: elem)
proc mkSetExcl*(recv, elem: IRExpr): IRExpr =
  IRExpr(kind: iekSetExcl, mutRecv: recv, mutArg: elem)

proc mkAssign*(name: string, value: IRExpr): IRStmt =
  IRStmt(kind: isAssign, aname: name, avalue: value)

proc mkWhile*(cond: IRExpr, body: IRStmt): IRStmt =
  IRStmt(kind: isWhile, wcond: cond, wbody: body)

proc mkBreak*(): IRStmt = IRStmt(kind: isBreak)
proc mkContinue*(): IRStmt = IRStmt(kind: isContinue)

proc mkBlock*(stmts: seq[IRStmt]): IRStmt =
  IRStmt(kind: isBlock, stmts: stmts)

proc mkIf*(branches: seq[IRBranch], elseBody: IRStmt = nil): IRStmt =
  IRStmt(kind: isIf, branches: branches, elseBody: elseBody)

proc mkLet*(name: string, ty: IRType, value: IRExpr): IRStmt =
  IRStmt(kind: isLet, lname: name, lty: ty, lvalue: value)

# IRType constructors — used by the parser/typebridge and by tests.
proc tBool*(): IRType =
  IRType(kind: itBool)

proc tInt*(width: int = 64, signed: bool = true): IRType =
  IRType(kind: itInt, width: width, signed: signed)

proc tUInt*(width: int): IRType =
  IRType(kind: itInt, width: width, signed: false)

proc tTuple*(fields: seq[IRType], fieldNames: seq[string] = @[],
             objectName: string = ""): IRType =
  ## `fieldNames.len` must equal `fields.len` or be empty (positional).
  doAssert fieldNames.len == 0 or fieldNames.len == fields.len
  let names = if fieldNames.len > 0: fieldNames
              else: newSeq[string](fields.len)   ## all-""
  IRType(kind: itTuple, fields: fields, fieldNames: names, objectName: objectName)

proc tArray*(elemTy: IRType, size: int): IRType =
  IRType(kind: itArray, elemTy: elemTy, size: size)

proc tString*(): IRType =
  IRType(kind: itString)

proc tSeq*(elemTy: IRType): IRType =
  IRType(kind: itSeq, seqElemTy: elemTy)

proc tTable*(keyTy, valTy: IRType): IRType =
  IRType(kind: itTable, tabKeyTy: keyTy, tabValTy: valTy)

proc tSet*(elemTy: IRType): IRType =
  IRType(kind: itSet, setElemTy: elemTy)

proc tVariant*(objectName, discName: string, discTy: IRType,
               arms: seq[VariantArm],
               plainFieldNames: seq[string] = @[],
               plainFieldTypes: seq[IRType] = @[],
               discTags: seq[tuple[name: string, ord: int]] = @[]): IRType =
  ## Phase 11 + Phase 14 (A2). Tagged sum type — Nim variant object.
  ##
  ## `plainFieldNames`/`plainFieldTypes` carry the always-present
  ## prefix from `nnkRecCase`-bearing objects' plain `nnkIdentDefs`
  ## members — allocated ONCE and shared across all arms.
  ##
  ## `discOrdinals` is the disc enum's full ordinal domain. Required
  ## when any arm has `isElse=true` so the walker can derive the
  ## legal disc range. Empty for exhaustive-`of` variants without
  ## `else:` (the per-arm equality disjunction is then sufficient).
  IRType(kind: itVariant, vObjectName: objectName,
         vDiscName: discName, vDiscTy: discTy, vArms: arms,
         vDiscTags: discTags,
         vPlainFieldNames: plainFieldNames,
         vPlainFieldTypes: plainFieldTypes)

proc mkMultiVariant*(objectName: string,
                     axes: seq[VariantAxis],
                     plainFieldNames: seq[string] = @[],
                     plainFieldTypes: seq[IRType] = @[]): IRType =
  ## Phase 14 (ADR-0003 D1). Constructor for multi-recCase variants.
  ## Asserts `axes.len >= 2` — single-recCase objects MUST use
  ## `tVariant` instead. The two IR kinds are intentionally disjoint
  ## (see itMultiVariant doc).
  doAssert axes.len >= 2,
    "mkMultiVariant requires axes.len >= 2; single-axis objects " &
    "must use tVariant. Got axes.len = " & $axes.len
  IRType(kind: itMultiVariant, mvObjectName: objectName,
         mvAxes: axes,
         mvPlainFieldNames: plainFieldNames,
         mvPlainFieldTypes: plainFieldTypes)

proc `==`*(a, b: IRType): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of itBool, itString: true
  of itInt:  a.width == b.width and a.signed == b.signed
  of itTuple:
    if a.fields.len != b.fields.len: return false
    if a.objectName != b.objectName: return false
    for i, f in a.fields:
      if f != b.fields[i]: return false
      if a.fieldNames[i] != b.fieldNames[i]: return false
    true
  of itArray: a.size == b.size and a.elemTy == b.elemTy
  of itSeq:   a.seqElemTy == b.seqElemTy
  of itTable: a.tabKeyTy == b.tabKeyTy and a.tabValTy == b.tabValTy
  of itSet:   a.setElemTy == b.setElemTy
  of itVariant:
    if a.vObjectName != b.vObjectName: return false
    if a.vDiscName != b.vDiscName: return false
    if a.vDiscTy != b.vDiscTy: return false
    if a.vPlainFieldNames != b.vPlainFieldNames: return false
    if a.vPlainFieldTypes.len != b.vPlainFieldTypes.len: return false
    for j, ft in a.vPlainFieldTypes:
      if ft != b.vPlainFieldTypes[j]: return false
    if a.vArms.len != b.vArms.len: return false
    for i, arm in a.vArms:
      if arm.tagOrdinal != b.vArms[i].tagOrdinal: return false
      if arm.tagName    != b.vArms[i].tagName:    return false
      if arm.fieldNames != b.vArms[i].fieldNames: return false
      if arm.fieldTypes.len != b.vArms[i].fieldTypes.len: return false
      for j, ft in arm.fieldTypes:
        if ft != b.vArms[i].fieldTypes[j]: return false
      if arm.isElse != b.vArms[i].isElse: return false
    if a.vDiscTags != b.vDiscTags: return false
    true
  of itMultiVariant:
    if a.mvObjectName      != b.mvObjectName:      return false
    if a.mvPlainFieldNames != b.mvPlainFieldNames: return false
    if a.mvPlainFieldTypes.len != b.mvPlainFieldTypes.len: return false
    for j, ft in a.mvPlainFieldTypes:
      if ft != b.mvPlainFieldTypes[j]: return false
    if a.mvAxes.len != b.mvAxes.len: return false
    for i, ax in a.mvAxes:
      let bx = b.mvAxes[i]
      if ax.discName     != bx.discName:     return false
      if ax.discTy       != bx.discTy:       return false
      if ax.discTags != bx.discTags: return false
      if ax.arms.len     != bx.arms.len:     return false
      for k, arm in ax.arms:
        let barm = bx.arms[k]
        if arm.tagOrdinal != barm.tagOrdinal: return false
        if arm.tagName    != barm.tagName:    return false
        if arm.fieldNames != barm.fieldNames: return false
        if arm.fieldTypes.len != barm.fieldTypes.len: return false
        for j, ft in arm.fieldTypes:
          if ft != barm.fieldTypes[j]: return false
        if arm.isElse != barm.isElse: return false
    true

proc `$`*(t: IRType): string =
  if t.isNil: return "nil"
  case t.kind
  of itBool: "bool"
  of itInt:
    let prefix = if t.signed: "i" else: "u"
    prefix & $t.width
  of itTuple:
    var s = if t.objectName.len > 0: t.objectName & "{" else: "("
    for i, f in t.fields:
      if i > 0: s.add ", "
      if t.fieldNames[i].len > 0: s.add t.fieldNames[i] & ":"
      s.add $f
    s & (if t.objectName.len > 0: "}" else: ")")
  of itArray:
    "array[" & $t.size & ", " & $t.elemTy & "]"
  of itString:
    "string"
  of itSeq:
    "seq[" & $t.seqElemTy & "]"
  of itTable:
    "Table[" & $t.tabKeyTy & ", " & $t.tabValTy & "]"
  of itSet:
    "HashSet[" & $t.setElemTy & "]"
  of itVariant:
    var plainStr = ""
    for i, fn in t.vPlainFieldNames:
      plainStr.add fn & ": " & $t.vPlainFieldTypes[i] & "; "
    var armsStr = ""
    for i, arm in t.vArms:
      if i > 0: armsStr.add " | "
      armsStr.add arm.tagName & "("
      for j, fn in arm.fieldNames:
        if j > 0: armsStr.add ", "
        armsStr.add fn & ": " & $arm.fieldTypes[j]
      armsStr.add ")"
    t.vObjectName & "{" & plainStr & t.vDiscName & ": " & $t.vDiscTy &
      " ⇒ " & armsStr & "}"
  of itMultiVariant:
    var plainStr = ""
    for i, fn in t.mvPlainFieldNames:
      plainStr.add fn & ": " & $t.mvPlainFieldTypes[i] & "; "
    var axesStr = ""
    for i, ax in t.mvAxes:
      if i > 0: axesStr.add " × "
      var armsStr = ""
      for j, arm in ax.arms:
        if j > 0: armsStr.add " | "
        armsStr.add (if arm.isElse: "else" else: arm.tagName)
      axesStr.add ax.discName & ": " & $ax.discTy & " ⇒ {" & armsStr & "}"
    t.mvObjectName & "{" & plainStr & axesStr & "}"

proc mkReturn*(): IRStmt =
  IRStmt(kind: isReturn, retExpr: nil)

proc mkReturnVal*(e: IRExpr): IRStmt =
  IRStmt(kind: isReturn, retExpr: e)

proc mkCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: false)

proc mkOpaqueCall*(callee, retName: string, args: seq[IRExpr], retTy: IRType): IRStmt =
  IRStmt(kind: isCall, callee: callee, cargs: args,
         retName: retName, retTy: retTy, opaque: true)

proc mkVariantFieldStmt*(retName: string, recv: IRExpr, fieldName: string,
                         fieldTy: IRType, matchingTags: seq[int]): IRStmt =
  IRStmt(kind: isVariantField, vfRetName: retName, vfRecv: recv,
         vfFieldName: fieldName, vfFieldTy: fieldTy,
         vfMatchingTags: matchingTags)

proc mkVariantReassign*(objName: string, newTag: int,
                        tagName: string): IRStmt =
  IRStmt(kind: isVariantReassign, vrObjName: objName,
         vrNewTag: newTag, vrTagName: tagName)

proc mkVariantReassignSymbolic*(objName, discName: string,
                                rhs: IRExpr): IRStmt =
  ## Phase 14 cycle A4a (ADR-0003 D4). Symbolic-RHS variant disc
  ## reassignment: `discName == ""` selects the only axis on a
  ## single-axis itVariant; non-empty names a specific axis on an
  ## itMultiVariant.
  IRStmt(kind: isVariantReassignSymbolic,
         vrsObjName: objName, vrsDiscName: discName, vrsRhs: rhs)

proc mkIndexStmt*(retName: string, arr, idx: IRExpr, elemTy: IRType): IRStmt =
  IRStmt(kind: isIndex, ixRetName: retName, ixArr: arr,
         ixIdx: idx, ixElemTy: elemTy)

proc mkAssert*(cond: IRExpr): IRStmt =
  IRStmt(kind: isAssert, acond: cond)

proc mkBranch*(cond: IRExpr, body: IRStmt): IRBranch =
  IRBranch(cond: cond, body: body)

proc mkTargetLabel*(name: string): IRStmt =
  IRStmt(kind: isTargetLabel, tname: name)

proc mkUnsupported*(reason: string): IRStmt =
  IRStmt(kind: isUnsupported, reason: reason)

# ---- Defaults ---------------------------------------------------------------

proc defaultSymexSettings*(): SymexSettings =
  ## Phase 2 endpoint: `isOptimised` is now the default. Range-typed
  ## parameters auto-promote to Z3Int when the abstraction-soundness
  ## proof holds; everything else falls back to BV[W]. `isExact` is
  ## available as an explicit override for users who want the
  ## abstraction layer's static analysis itself off the trust chain.
  SymexSettings(
    integerSemantics: isOptimised,
    queryRLimit: 0,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5,
  )

proc tLabel*(name: string): SymexTarget =
  SymexTarget(kind: stkLabel, label: name)

proc tAssertionViolation*(): SymexTarget =
  SymexTarget(kind: stkAssertionViolation)

proc tIndexError*(): SymexTarget =
  SymexTarget(kind: stkIndexError)

proc tFieldDefect*(): SymexTarget =
  ## Phase 11 cycle 5. Symex searches for an input that drives a
  ## variant arm-field access while the discriminator's value is
  ## outside the field's arm set — i.e. an input the SUT would
  ## answer with a `FieldDefect` at runtime.
  SymexTarget(kind: stkFieldDefect)

proc optimisedSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isOptimised`.
  ## (`defaultSymexSettings()` will flip to optimised at the end of
  ## Phase 2 once the abstraction layer has shipped end-to-end.)
  result = defaultSymexSettings()
  result.integerSemantics = isOptimised

proc looseSymexSettings*(): SymexSettings =
  ## Convenience: settings with `integerSemantics: isLoose` (UNSOUND
  ## — research/educational only; see ADR-0001).
  result = defaultSymexSettings()
  result.integerSemantics = isLoose

# ---- Rendering --------------------------------------------------------------
#
# Canonical S-expression form for the IR. Used by Layer-1 isolation
# tests (per ADR-0002) to assert on the parser's output without going
# through the runtime — the renderer is the test-side oracle.

import std/sequtils
import std/strutils

proc render*(e: IRExpr): string =
  if e == nil: return "nil"
  case e.kind
  of iekIntLit:  $e.ival
  of iekBoolLit: $e.bval
  of iekVar:     e.vname
  of iekBinop:   "(" & $e.bop & " " & render(e.lhs) & " " & render(e.rhs) & ")"
  of iekUnop:    "(" & $e.uop & " " & render(e.operand) & ")"
  of iekField:
    let suffix = if e.fieldName.len > 0: "." & e.fieldName else: "[" & $e.fieldIx & "]"
    render(e.obj) & suffix
  of iekIndex:   render(e.arr) & "[" & render(e.idx) & "]"
  of iekArrayLit:
    var inner = ""
    for i, c in e.lelems:
      if i > 0: inner.add ","
      inner.add render(c)
    "[" & inner & "]"
  of iekSeqLen:
    render(e.lenObj) & ".len"
  of iekStrLit:
    "\"" & e.sval & "\""
  of iekContains:
    render(e.key) & " in " & render(e.container)
  of iekSeqAdd:    render(e.mutRecv) & ".add(" & render(e.mutArg) & ")"
  of iekSeqDel:    render(e.delSeq) & ".del(" & render(e.delIdx) & ")"
  of iekSeqInsert: render(e.insSeq) & ".insert(" & render(e.insVal) &
                   "," & render(e.insIdx) & ")"
  of iekSeqPop:    render(e.popSeq) & ".pop()"
  of iekTableSet:  render(e.tabRecv) & "[" & render(e.tabKey) & "]:=" &
                   render(e.tabVal)
  of iekTableDel:  render(e.mutRecv) & ".del(" & render(e.mutArg) & ")"
  of iekSetIncl:   render(e.mutRecv) & ".incl(" & render(e.mutArg) & ")"
  of iekSetExcl:   render(e.mutRecv) & ".excl(" & render(e.mutArg) & ")"

proc render*(s: IRStmt): string =
  if s == nil: return "nil"
  case s.kind
  of isBlock:
    "{" & s.stmts.mapIt(render(it)).join(";") & "}"
  of isIf:
    var arms = ""
    for br in s.branches:
      arms.add "[" & render(br.cond) & "=>" & render(br.body) & "]"
    if s.elseBody != nil:
      arms.add "[else=>" & render(s.elseBody) & "]"
    "if(" & arms & ")"
  of isLet:
    "let(" & s.lname & ":" & $s.lty & "=" & render(s.lvalue) & ")"
  of isAssign:
    s.aname & ":=" & render(s.avalue)
  of isWhile:
    "while(" & render(s.wcond) & "){" & render(s.wbody) & "}"
  of isBreak:    "break"
  of isContinue: "continue"
  of isReturn:
    if s.retExpr == nil: "return"
    else: "return(" & render(s.retExpr) & ")"
  of isAssert:       "assert(" & render(s.acond) & ")"
  of isCall:
    var argstr = ""
    for i, a in s.cargs:
      if i > 0: argstr.add ","
      argstr.add render(a)
    let lhs = if s.retName.len > 0: s.retName & ":=" else: ""
    "call(" & lhs & s.callee & "(" & argstr & "))"
  of isIndex:
    "index(" & s.ixRetName & ":=" & render(s.ixArr) & "[" & render(s.ixIdx) & "])"
  of isVariantField:
    "vfield(" & s.vfRetName & ":=" & render(s.vfRecv) & "." &
      s.vfFieldName & ")"
  of isVariantReassign:
    "vreassign(" & s.vrObjName & ".kind:=" & s.vrTagName &
      ")"
  of isVariantReassignSymbolic:
    "vreassignSym(" & s.vrsObjName & "." &
      (if s.vrsDiscName.len == 0: "kind" else: s.vrsDiscName) &
      ":=" & render(s.vrsRhs) & ")"
  of isTargetLabel:  "target(" & s.tname & ")"
  of isUnsupported:  "unsupported(" & s.reason & ")"
