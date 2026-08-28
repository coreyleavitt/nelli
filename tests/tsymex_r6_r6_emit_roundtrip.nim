## Round-6 R6 (post-0.4.0 remediation slice, finding N4) -- fail-safe emit
## round-trip audit. NO WALKER VERSION BUMP: this file is pure test
## infrastructure over macro-time -> runtime IR serialization; it exercises
## no verdict surface (no `symexFind`/`symexAssume`, no walker code path).
##
## ---------------------------------------------------------------------
## THE FINDING (N4, Critical-by-class)
## ---------------------------------------------------------------------
## `IRType`/`IRStmt`/`IRExpr` are constructed at MACRO TIME (dsl_parser.nim)
## and reconstructed at RUNTIME by hand-written `emitIRType`/`emitStmt`/
## `emitExpr` (dsl_parser.nim), which positionally rebuild each variant via
## `mk*`/`t*` constructor calls baked into a `NimNode` tree. Adding a field
## to a variant requires touching the type def, the constructor, AND the
## emit call site -- with NO compiler-enforced link between them. A
## forgotten emit argument compiles cleanly; the field just silently
## reverts to its zero value the moment the emitted code runs. This is not
## hypothetical: it has already happened twice --
##   1. `IRStmt.retIntOffsetPositions` (isCall) -- the B5 slice.
##   2. `IRType.seqUnsupportedFieldReason` (itSeq) -- Bug #2 / "the B5
##      lesson" (see the comment at dsl_parser.nim's `itSeq` emit arm).
## A prior correctness pass audited every field added this round as
## currently-serialized (no THIRD live gap found then) -- but the CLASS was
## unfixed: nothing stops the NEXT field from silently reverting.
##
## ---------------------------------------------------------------------
## OPTION A vs OPTION B (feasibility probe, time-boxed)
## ---------------------------------------------------------------------
## Option A (reflection-driven emit -- generate the `mk*`/`t*` call trees
## structurally from the type definition, e.g. via macro-time `getTypeImpl`
## walking of the `nnkRecCase` shape) was evaluated and REJECTED for this
## slice. Evidence:
##   - Zero prior art: no `fieldPairs`/`getTypeImpl`-driven CODE GENERATION
##     exists anywhere in this codebase (`dsl_typebridge.nim`/`detect.nim`
##     walk `nnkRecCase` shapes to CLASSIFY a Nim AST into an `IRType`, the
##     opposite direction -- neither touches `mk*`/`t*` constructors).
##   - Decisively: constructor SELECTION for at least 5 of the ~24 IRStmt/
##     16 IRType kinds is VALUE-dependent, not structurally derivable from
##     the type alone -- `itSeq` picks `tSeq` vs `tUnsupportedFieldSeq` on
##     `seqUnsupportedFieldReason.len > 0`; `isCall` picks `mkCall` vs
##     `mkOpaqueCall` on `.opaque`; `isDeref`/`isDerefWrite` pick one of
##     THREE constructors on `.dField.len > 0` and `.dPtrFamily`; `isRaise`
##     picks `mkRaise` vs `mkReraise` on `.raiseIsReraise`. A structural
##     reflection macro cannot infer this branching from the type shape --
##     it would still need per-kind hand-written override logic for exactly
##     these kinds.
##   - CRITICALLY, this undercuts Option A's value proposition for THIS
##     codebase's actual risk profile: BOTH historical incidents
##     (`retIntOffsetPositions` in `isCall`, `seqUnsupportedFieldReason` in
##     `itSeq`) live in kinds with value-dependent constructor selection --
##     precisely the kinds a reflection macro could NOT have automated
##     anyway, since they'd still need hand-written emit logic. A "mostly
##     generated, with escape-hatch overrides for the irregular kinds"
##     hybrid is possible in principle, but re-introduces the exact
##     "forgot to update the hand-written part" risk N4 exists to close --
##     for precisely the highest-risk kinds.
##   - `itVariant`/`itMultiVariant`/`isTry` use a SECOND, structurally
##     distinct serialization idiom (named-field `nnkObjConstr` for the
##     auxiliary `VariantArm`/`VariantAxis`/`ExceptHandler` object types,
##     not `mk*`/`t*` calls at all) that a reflection generator would need
##     wholly separate support for.
## Conclusion: ship Option B alone. Option A is recorded as design debt --
## a well-scoped hybrid generator (auto-derive the ~19 purely-positional
## kinds, hand-maintain the ~5 value-dependent ones under the SAME
## exhaustiveness discipline this file establishes) may be worth revisiting
## if the type keeps growing, but is out of scope for this slice.
##
## ---------------------------------------------------------------------
## OPTION B: sentinel round-trip audit (what this file does)
## ---------------------------------------------------------------------
## For every variant KIND of `IRType`/`IRStmt`/`IRExpr` (every distinct
## `emitIRType`/`emitStmt`/`emitExpr` case arm; shared-arm kind GROUPS such
## as Cluster S's `StrOpKinds` get one full round-trip test per DISTINCT
## CODE PATH plus full literal-kind coverage in the exhaustiveness gate
## below), this file:
##   1. Builds a sentinel value with every field set to a distinguishing
##      non-zero/non-default value via the real `mk*`/`t*` constructors.
##   2. Round-trips it through the REAL `emitIRType`/`emitStmt`/`emitExpr`
##      (imported from `nelli/smt/dsl_parser`, not reimplemented) via a
##      `static[T]`-parameterized macro that forces the compiler to
##      evaluate the sentinel construction at compile time (mirroring how
##      `dsl_parser.nim`'s own macros build these values at MACRO TIME),
##      then splices the emitted `NimNode` into an ordinary runtime `let`
##      binding -- so the `mk*`/`t*` reconstruction calls execute at ACTUAL
##      PROGRAM RUNTIME, exactly as they do when a real DSL macro's
##      generated proc runs. This is the real macro round trip, not a
##      same-process copy.
##   3. Asserts FULL field-by-field deep equality (`fieldwiseEq`, defined
##      below) between the pre-round-trip sentinel and the post-round-trip
##      reconstruction -- deliberately NOT reusing `IRType`'s own `==`
##      (types.nim:2107), which is documented to skip `isPlaceholder` and
##      (undocumented, discovered while building this file) ALSO skips
##      `nominalId`/`nameIsRefAlias` -- exactly the kind of silent gap a
##      completeness audit must not inherit from the thing it's auditing.
## A missed emit field now fails THIS test at the next `nimble test`,
## instead of surfacing as a walk-time mystery (crash, or a silently wrong
## verdict) three slices later.
##
## The ONE known, INTENTIONAL non-round-tripping field --
## `IRType.nameIsRefAlias` (witness-codegen-only per the `itTuple` emit
## arm's own comment, dsl_parser.nim) -- is explicitly PINNED as a named
## exception (see "itTuple: KNOWN non-round-tripping field" below), not
## silently excluded from the audit.
##
## ---------------------------------------------------------------------
## EXHAUSTIVENESS GATE
## ---------------------------------------------------------------------
## Three `case` statements with NO `else`, one per kind enum
## (`IRTypeKind`/`IRExprKind`/`IRStmtKind`), each `of` branch commented
## with the test(s) covering it. Nim's compiler REJECTS a non-exhaustive
## `case` over an enum -- so a future PR that adds a new kind and forgets
## to extend this file fails to COMPILE, not just fails a test that might
## not get run.
##
## ---------------------------------------------------------------------
## RED evidence (meta -- see the slice's final report)
## ---------------------------------------------------------------------
## This slice's RED is not "the feature doesn't exist yet" (nothing new is
## being built) but "does this test catch the injected historical bug
## class?" -- verified by temporarily deleting the `retIntOffsetPositions`
## argument from `emitStmt`'s `isCall` arm (re-introducing the exact B5
## regression) and confirming this file's `isCall` test fails, then
## restoring. See the slice's commit message / final report for the
## transcript.

import std/unittest
import nelli/smt/types
import nelli/smt/dsl_parser

# ---------------------------------------------------------------------------
# Round-trip macros. `static[T]` forces the compiler to evaluate the
# argument expression at compile time (CTFE) -- exactly the "macro time"
# regime `dsl_parser.nim`'s real classify/parse macros build these IR
# values under -- then the macro body calls the REAL `emitIRType`/
# `emitStmt`/`emitExpr` and returns the resulting NimNode, which the CALLER
# then compiles as ordinary source. `const` of these ref-object types is
# rejected by Nim ("invalid type for const"), so the sentinel value cannot
# be pre-bound to a shared symbol -- each sentinel is instead built by a
# small zero-argument proc, called once normally (the "expected" value,
# built entirely at ordinary runtime) and once as the macro argument (the
# "reconstructed" value, forced through the emit round trip).
# ---------------------------------------------------------------------------

macro roundtripType(v: static[IRType]): untyped = emitIRType(v)
macro roundtripExpr(v: static[IRExpr]): untyped = emitExpr(v)
macro roundtripStmt(v: static[IRStmt]): untyped = emitStmt(v)

# ---------------------------------------------------------------------------
# fieldwiseEq -- an independent, byte-for-byte-in-spirit deep comparator.
# Deliberately NOT `IRType`'s own `==` (types.nim) -- see the header note.
# Every field of every kind is compared explicitly; nothing is skipped
# silently. The ONE deliberate skip (`nameIsRefAlias`, documented
# non-round-tripping) is NOT skipped here either -- it participates in the
# general comparison like any other field, and the one test that sets it
# to a sentinel (`itTuple: KNOWN non-round-tripping field`) asserts the
# reconstructed value directly rather than through `fieldwiseEq`, so that
# test's PASS proves the documented degrade, not a silent audit gap.
# ---------------------------------------------------------------------------

proc fieldwiseEq(a, b: IRType): bool
proc fieldwiseEq(a, b: IRExpr): bool
proc fieldwiseEq(a, b: IRStmt): bool

proc fieldwiseEqTypeSeq(a, b: seq[IRType]): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if not fieldwiseEq(a[i], b[i]): return false
  true

proc fieldwiseEqExprSeq(a, b: seq[IRExpr]): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if not fieldwiseEq(a[i], b[i]): return false
  true

proc fieldwiseEqStmtOpt(a, b: IRStmt): bool =
  ## Nil-safe comparison for an OPTIONAL child (elseBody / tryFinally / a
  ## bare deref's absent bodies never apply here, but isIf/isTry do use it).
  (a == nil and b == nil) or (a != nil and b != nil and fieldwiseEq(a, b))

proc fieldwiseEqExprOpt(a, b: IRExpr): bool =
  ## Nil-safe comparison for an OPTIONAL child (raiseMsg / hofInit).
  (a == nil and b == nil) or (a != nil and b != nil and fieldwiseEq(a, b))

proc fieldwiseEqTypeOpt(a, b: IRType): bool =
  ## Nil-safe comparison for an OPTIONAL child (isDeref/isDerefWrite's
  ## `dObjTy`/`dwObjTy`, nil for a bare (non-field) deref/write).
  (a == nil and b == nil) or (a != nil and b != nil and fieldwiseEq(a, b))

proc fieldwiseEqParam(a, b: IRParam): bool =
  a.name == b.name and fieldwiseEq(a.ty, b.ty) and a.rangeLo == b.rangeLo and
    a.rangeHi == b.rangeHi and a.hasRange == b.hasRange and a.isVar == b.isVar and
    a.isStringBacked == b.isStringBacked and a.isIntOffset == b.isIntOffset

proc fieldwiseEqParams(a, b: seq[IRParam]): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if not fieldwiseEqParam(a[i], b[i]): return false
  true

proc fieldwiseEqVariantArm(a, b: VariantArm): bool =
  a.tagOrdinal == b.tagOrdinal and a.tagName == b.tagName and
    a.fieldNames == b.fieldNames and a.isElse == b.isElse and
    fieldwiseEqTypeSeq(a.fieldTypes, b.fieldTypes)

proc fieldwiseEqVariantArms(a, b: seq[VariantArm]): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if not fieldwiseEqVariantArm(a[i], b[i]): return false
  true

proc fieldwiseEqExceptHandlers(a, b: seq[ExceptHandler]): bool =
  if a.len != b.len: return false
  for i in 0 ..< a.len:
    if a[i].typeIds != b[i].typeIds: return false
    if not fieldwiseEq(a[i].body, b[i].body): return false
  true

proc fieldwiseEq(a, b: IRType): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of itBool, itString, itFloat32, itFloat64: true
  of itInt: a.width == b.width and a.signed == b.signed
  of itUninterp: a.uninterpName == b.uninterpName
  of itDistinct: a.distinctName == b.distinctName and fieldwiseEq(a.distinctBase, b.distinctBase)
  of itRef: fieldwiseEq(a.refPointeeTy, b.refPointeeTy)
  of itPtr: fieldwiseEq(a.ptrPointeeTy, b.ptrPointeeTy)
  of itArray: a.size == b.size and fieldwiseEq(a.elemTy, b.elemTy)
  of itSeq:
    # Round-6 re-review (item 3, walker v114): `seqUnsupportedFieldKind` was
    # not compared here either -- the checker's own silent gap that let
    # `emitIRType`'s matching omission go unnoticed. Both fields now compared.
    fieldwiseEq(a.seqElemTy, b.seqElemTy) and
      a.seqUnsupportedFieldReason == b.seqUnsupportedFieldReason and
      a.seqUnsupportedFieldKind == b.seqUnsupportedFieldKind
  of itTable: fieldwiseEq(a.tabKeyTy, b.tabKeyTy) and fieldwiseEq(a.tabValTy, b.tabValTy)
  of itSet: fieldwiseEq(a.setElemTy, b.setElemTy)
  of itTuple:
    a.objectName == b.objectName and a.nominalId == b.nominalId and
      a.isPlaceholder == b.isPlaceholder and a.nameIsRefAlias == b.nameIsRefAlias and
      a.fieldNames == b.fieldNames and fieldwiseEqTypeSeq(a.fields, b.fields)
  of itVariant:
    a.vDiscName == b.vDiscName and fieldwiseEq(a.vDiscTy, b.vDiscTy) and
      a.vObjectName == b.vObjectName and a.vPlainFieldNames == b.vPlainFieldNames and
      fieldwiseEqTypeSeq(a.vPlainFieldTypes, b.vPlainFieldTypes) and
      a.vDiscTags == b.vDiscTags and fieldwiseEqVariantArms(a.vArms, b.vArms)
  of itMultiVariant:
    if a.mvObjectName != b.mvObjectName: return false
    if a.mvPlainFieldNames != b.mvPlainFieldNames: return false
    if not fieldwiseEqTypeSeq(a.mvPlainFieldTypes, b.mvPlainFieldTypes): return false
    if a.mvAxes.len != b.mvAxes.len: return false
    for i in 0 ..< a.mvAxes.len:
      let ax = a.mvAxes[i]
      let bx = b.mvAxes[i]
      if ax.discName != bx.discName: return false
      if not fieldwiseEq(ax.discTy, bx.discTy): return false
      if ax.discTags != bx.discTags: return false
      if not fieldwiseEqVariantArms(ax.arms, bx.arms): return false
    true

proc fieldwiseEq(a, b: IRExpr): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of iekIntLit: a.ival == b.ival
  of iekFloatLit: a.fval == b.fval and a.fwidth == b.fwidth
  of iekConvIntToFloat, iekConvFloatToInt:
    fieldwiseEq(a.convOperand, b.convOperand) and a.convWidth == b.convWidth
  of iekConvIntWidth:
    fieldwiseEq(a.ciwOperand, b.ciwOperand) and a.ciwSrcWidth == b.ciwSrcWidth and
      a.ciwSrcSigned == b.ciwSrcSigned and a.ciwTgtWidth == b.ciwTgtWidth and
      a.ciwTgtSigned == b.ciwTgtSigned
  of iekConvIntReinterpret:
    # Item 7b (round-6 re-review): this arm was MISSING entirely -- the
    # `auditIRExprKindCoverage` exhaustiveness gate below has no `else`, so
    # `iekConvIntReinterpret` (A1 adjudication, walker v116) existing in
    # `IRExprKind` with no covering arm here made this file FAIL TO COMPILE,
    # exactly the "N4-class audit working as designed" catch this file's own
    # header describes -- a new IR kind that forgets to extend the audit
    # fails the BUILD, not a test that might not get run.
    fieldwiseEq(a.cirOperand, b.cirOperand) and a.cirWidth == b.cirWidth and
      a.cirTgtSigned == b.cirTgtSigned
  of iekMathCall: a.mathOp == b.mathOp and fieldwiseEqExprSeq(a.mathArgs, b.mathArgs)
  of iekBoolLit: a.bval == b.bval
  of iekVar: a.vname == b.vname
  of iekBinop: a.bop == b.bop and fieldwiseEq(a.lhs, b.lhs) and fieldwiseEq(a.rhs, b.rhs)
  of iekUnop: a.uop == b.uop and fieldwiseEq(a.operand, b.operand)
  of iekField: fieldwiseEq(a.obj, b.obj) and a.fieldIx == b.fieldIx and a.fieldName == b.fieldName
  of iekIndex: fieldwiseEq(a.arr, b.arr) and fieldwiseEq(a.idx, b.idx)
  of iekArrayLit: fieldwiseEqExprSeq(a.lelems, b.lelems) and fieldwiseEq(a.lelemTy, b.lelemTy)
  of iekTupleLit: fieldwiseEqExprSeq(a.telems, b.telems) and fieldwiseEq(a.ttupleTy, b.ttupleTy)
  of iekVariantLit:
    fieldwiseEq(a.vlVariantTy, b.vlVariantTy) and a.vlTagOrd == b.vlTagOrd and
      a.vlTagName == b.vlTagName and fieldwiseEqExprSeq(a.vlArmFields, b.vlArmFields) and
      fieldwiseEqExprSeq(a.vlPlainFields, b.vlPlainFields)
  of iekSeqLen: fieldwiseEq(a.lenObj, b.lenObj) and a.lenLoc == b.lenLoc
  of iekSeqSlice:
    fieldwiseEq(a.ssBase, b.ssBase) and fieldwiseEq(a.ssLo, b.ssLo) and fieldwiseEq(a.ssHi, b.ssHi)
  of iekStrLit: a.sval == b.sval
  of iekContains: fieldwiseEq(a.container, b.container) and fieldwiseEq(a.key, b.key)
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    fieldwiseEq(a.mutRecv, b.mutRecv) and fieldwiseEq(a.mutArg, b.mutArg)
  of iekSeqDel: fieldwiseEq(a.delSeq, b.delSeq) and fieldwiseEq(a.delIdx, b.delIdx)
  of iekSeqInsert:
    fieldwiseEq(a.insSeq, b.insSeq) and fieldwiseEq(a.insVal, b.insVal) and
      fieldwiseEq(a.insIdx, b.insIdx)
  of iekSeqPop: fieldwiseEq(a.popSeq, b.popSeq)
  of iekTableSet:
    fieldwiseEq(a.tabRecv, b.tabRecv) and fieldwiseEq(a.tabKey, b.tabKey) and
      fieldwiseEq(a.tabVal, b.tabVal)
  of StrOpKinds:
    # Fix-slice item 5 (round-6 re-review): `strRetTy` compared too -- the
    # NEW field this fix-slice added to close `degradeStrArm`'s name-keyed
    # (not total) return-type mapping. Left uncompared here, THIS audit
    # would have the exact silent-gap shape it exists to catch (the B5/
    # itSeq historical incidents documented at this file's own header).
    a.strOp == b.strOp and fieldwiseEqExprSeq(a.strArgs, b.strArgs) and
      fieldwiseEq(a.strRetTy, b.strRetTy)
  of iekGetCurrentExn, iekGetCurrentExnMsg: true
  of iekBorrowOp:
    a.borrowOp == b.borrowOp and fieldwiseEq(a.borrowLhs, b.borrowLhs) and
      fieldwiseEq(a.borrowRhs, b.borrowRhs) and
      a.borrowReturnsDistinct == b.borrowReturnsDistinct and
      a.borrowDistinctName == b.borrowDistinctName
  of iekLambda:
    a.lambdaSite == b.lambdaSite and fieldwiseEqParams(a.lambdaParams, b.lambdaParams) and
      fieldwiseEq(a.lambdaBody, b.lambdaBody) and a.lambdaCaptures == b.lambdaCaptures and
      fieldwiseEq(a.lambdaRetTy, b.lambdaRetTy)
  of iekClosureCall: a.ccCallee == b.ccCallee and fieldwiseEqExprSeq(a.ccArgs, b.ccArgs)
  of iekSeqLit: fieldwiseEqExprSeq(a.seqLitElems, b.seqLitElems) and fieldwiseEq(a.seqLitElemTy, b.seqLitElemTy)
  of iekHofCall:
    a.hofOp == b.hofOp and fieldwiseEq(a.hofSeq, b.hofSeq) and
      fieldwiseEq(a.hofClosure, b.hofClosure) and fieldwiseEq(a.hofRetElemTy, b.hofRetElemTy) and
      fieldwiseEqExprOpt(a.hofInit, b.hofInit)
  of iekNil: fieldwiseEq(a.nilPointee, b.nilPointee)

proc fieldwiseEq(a, b: IRStmt): bool =
  if a.isNil or b.isNil: return a.isNil and b.isNil
  if a.kind != b.kind: return false
  case a.kind
  of isBlock:
    if a.stmts.len != b.stmts.len: return false
    for i in 0 ..< a.stmts.len:
      if not fieldwiseEq(a.stmts[i], b.stmts[i]): return false
    true
  of isIf:
    if a.branches.len != b.branches.len: return false
    for i in 0 ..< a.branches.len:
      if not fieldwiseEq(a.branches[i].cond, b.branches[i].cond): return false
      if not fieldwiseEq(a.branches[i].body, b.branches[i].body): return false
    fieldwiseEqStmtOpt(a.elseBody, b.elseBody)
  of isLet:
    a.lname == b.lname and fieldwiseEq(a.lty, b.lty) and fieldwiseEq(a.lvalue, b.lvalue) and
      a.lIsIntOffsetLocal == b.lIsIntOffsetLocal
  of isAssign: a.aname == b.aname and fieldwiseEq(a.avalue, b.avalue)
  of isWhile:
    # Item 3 (round-6 fix round 3): `wHasAssumedBound` (N20, 9dbc3df) was
    # missing from this comparison -- the sentinel used the field's own
    # `false` default, so a dropped/reverted emit argument would have been
    # invisible to `fieldwiseEq` regardless. Verified `emitStmt`'s `isWhile`
    # arm (dsl_parser.nim) DOES pass `newLit(s.wHasAssumedBound)` to
    # `mkWhile` -- no live emit gap, this was a test-coverage gap only.
    fieldwiseEq(a.wcond, b.wcond) and fieldwiseEq(a.wbody, b.wbody) and
      a.wHasAssumedBound == b.wHasAssumedBound
  of isBreak, isContinue: true
  of isReturn: fieldwiseEqExprOpt(a.retExpr, b.retExpr)
  of isCall:
    a.callee == b.callee and fieldwiseEqExprSeq(a.cargs, b.cargs) and a.retName == b.retName and
      fieldwiseEq(a.retTy, b.retTy) and a.opaque == b.opaque and
      a.retIntOffsetPositions == b.retIntOffsetPositions
  of isIndex:
    a.ixRetName == b.ixRetName and fieldwiseEq(a.ixArr, b.ixArr) and fieldwiseEq(a.ixIdx, b.ixIdx) and
      fieldwiseEq(a.ixElemTy, b.ixElemTy) and a.ixLoc == b.ixLoc
  of isIndexAssign:
    # Item 2 (round-6 fix round 3): was entirely missing from this file --
    # the exhaustiveness gate below had no `else`, so this file FAILED TO
    # COMPILE, exactly the "N4-class audit working as designed" catch this
    # file's own header describes (see the `iekConvIntReinterpret` item 7b
    # precedent above).
    a.iaRecvName == b.iaRecvName and fieldwiseEq(a.iaIdx, b.iaIdx) and
      fieldwiseEq(a.iaVal, b.iaVal) and a.iaLoc == b.iaLoc
  of isSeqPop:
    # Item 2 (round-6 fix round 3): see isIndexAssign's comment immediately
    # above -- same missing-arm gap, same N14 (9dbc3df) origin.
    a.spRecvName == b.spRecvName and a.spRetName == b.spRetName and
      a.spLoc == b.spLoc
  of isVariantField:
    a.vfRetName == b.vfRetName and fieldwiseEq(a.vfRecv, b.vfRecv) and
      a.vfFieldName == b.vfFieldName and fieldwiseEq(a.vfFieldTy, b.vfFieldTy) and
      a.vfMatchingTags == b.vfMatchingTags
  of isVariantReassign:
    a.vrObjName == b.vrObjName and a.vrNewTag == b.vrNewTag and a.vrTagName == b.vrTagName
  of isVariantReassignSymbolic:
    a.vrsObjName == b.vrsObjName and a.vrsDiscName == b.vrsDiscName and
      fieldwiseEq(a.vrsRhs, b.vrsRhs)
  of isVariantConstructSym:
    a.vcsResultVar == b.vcsResultVar and fieldwiseEq(a.vcsVariantTy, b.vcsVariantTy) and
      fieldwiseEq(a.vcsDiscExpr, b.vcsDiscExpr) and a.vcsTagSet == b.vcsTagSet and
      fieldwiseEqExprSeq(a.vcsPlainFields, b.vcsPlainFields) and a.vcsLoc == b.vcsLoc
  of isAssert, isAssume: fieldwiseEq(a.acond, b.acond)
  of isTargetLabel: a.tname == b.tname
  of isRaise:
    a.raiseTypeId == b.raiseTypeId and a.raiseIsReraise == b.raiseIsReraise and
      fieldwiseEqExprOpt(a.raiseMsg, b.raiseMsg)
  of isTry:
    fieldwiseEq(a.tryBody, b.tryBody) and
      fieldwiseEqExceptHandlers(a.tryHandlers, b.tryHandlers) and
      fieldwiseEqStmtOpt(a.tryFinally, b.tryFinally)
  of isDeref:
    a.dRetName == b.dRetName and fieldwiseEq(a.dPtr, b.dPtr) and
      fieldwiseEq(a.dElemTy, b.dElemTy) and a.dPtrFamily == b.dPtrFamily and
      a.dField == b.dField and fieldwiseEqTypeOpt(a.dObjTy, b.dObjTy)
  of isNew: a.nRetName == b.nRetName and fieldwiseEq(a.nRefTy, b.nRefTy)
  of isDerefWrite:
    fieldwiseEq(a.dwPtr, b.dwPtr) and fieldwiseEq(a.dwValue, b.dwValue) and
      fieldwiseEq(a.dwElemTy, b.dwElemTy) and a.dwPtrFamily == b.dwPtrFamily and
      a.dwField == b.dwField and fieldwiseEqTypeOpt(a.dwObjTy, b.dwObjTy)
  of isUnsupported: a.reason == b.reason
  of isUnsafeCast: a.ucReason == b.ucReason

# ---------------------------------------------------------------------------
# IRType sentinels + round-trip tests
# ---------------------------------------------------------------------------

proc sIntType(): IRType = tInt(37, false)
proc sBoolType(): IRType = tBool()
proc sStringType(): IRType = tString()
proc sFloat32Type(): IRType = tFloat32()
proc sFloat64Type(): IRType = tFloat64()
proc sUninterpType(): IRType = tUninterp("SentinelSort")
proc sDistinctType(): IRType = tDistinct("Meters", tInt(41, true))
proc sRefType(): IRType = tRef(tInt(23, false))
proc sPtrType(): IRType = tPtr(tFloat64())
proc sArrayType(): IRType = tArray(tInt(13, true), 77)
proc sSeqType(): IRType = tSeq(tInt(9, true))
proc sUnsupportedFieldSeqType(): IRType =
  ## Bug #2 / "the B5 lesson" field -- the historically-dropped one.
  ## `kind` is set to a NON-default `SymexErrorKind` (default is
  ## `seNestedSeqUnsupported` -- see `tUnsupportedFieldSeq`'s own default
  ## param) so a round-trip that silently reverts to the default is
  ## observable (item 3, walker v114: `emitIRType` used to drop this field).
  tUnsupportedFieldSeq(tInt(9, true), "sentinel scoped-decline reason",
                        kind = feUnsupportedOp)
proc sTableType(): IRType = tTable(tString(), tInt(64, true))
proc sSetType(): IRType = tSet(tInt(64, true))
proc sTupleType(): IRType =
  tTuple(@[tInt(64, true), tString()], @["fa", "fb"], "SentObj", "sentNomId",
         isPlaceholder = true)
proc sVariantType(): IRType =
  tVariant("SentShape", "kind", tInt(64, true),
    @[VariantArm(tagOrdinal: 0, tagName: "skCircle",
                  fieldNames: @["radius"], fieldTypes: @[tInt(64, true)],
                  isElse: false),
      VariantArm(tagOrdinal: 1, tagName: "elseArm",
                  fieldNames: @[], fieldTypes: @[],
                  isElse: true)],
    plainFieldNames = @["id"], plainFieldTypes = @[tString()],
    discTags = @[(name: "skCircle", ord: 0), (name: "skSquare", ord: 1)])
proc sMultiVariantType(): IRType =
  mkMultiVariant("SentMulti",
    @[VariantAxis(discName: "axisA", discTy: tInt(64, true),
                   arms: @[VariantArm(tagOrdinal: 0, tagName: "a0",
                                       fieldNames: @["fa0"], fieldTypes: @[tInt(64, true)],
                                       isElse: false)],
                   discTags: @[(name: "a0", ord: 0)]),
      VariantAxis(discName: "axisB", discTy: tInt(64, true),
                   arms: @[VariantArm(tagOrdinal: 1, tagName: "b1",
                                       fieldNames: @["fb1"], fieldTypes: @[tString()],
                                       isElse: false)],
                   discTags: @[(name: "b1", ord: 1)])],
    plainFieldNames = @["shared"], plainFieldTypes = @[tBool()])

suite "R6 emit round-trip -- IRType kinds":
  test "itInt":
    check fieldwiseEq(sIntType(), roundtripType(sIntType()))
  test "itBool":
    check fieldwiseEq(sBoolType(), roundtripType(sBoolType()))
  test "itString":
    check fieldwiseEq(sStringType(), roundtripType(sStringType()))
  test "itFloat32 / itFloat64 (shared discard arm)":
    check fieldwiseEq(sFloat32Type(), roundtripType(sFloat32Type()))
    check fieldwiseEq(sFloat64Type(), roundtripType(sFloat64Type()))
  test "itUninterp":
    check fieldwiseEq(sUninterpType(), roundtripType(sUninterpType()))
  test "itDistinct (recursive base)":
    check fieldwiseEq(sDistinctType(), roundtripType(sDistinctType()))
  test "itRef (recursive pointee)":
    check fieldwiseEq(sRefType(), roundtripType(sRefType()))
  test "itPtr (recursive pointee)":
    check fieldwiseEq(sPtrType(), roundtripType(sPtrType()))
  test "itArray (recursive elemTy + size)":
    check fieldwiseEq(sArrayType(), roundtripType(sArrayType()))
  test "itSeq (plain)":
    check fieldwiseEq(sSeqType(), roundtripType(sSeqType()))
  test "itSeq scoped-decline placeholder (Bug #2 / the B5 lesson -- seqUnsupportedFieldReason)":
    let reconstructed = roundtripType(sUnsupportedFieldSeqType())
    check fieldwiseEq(sUnsupportedFieldSeqType(), reconstructed)
    check reconstructed.seqUnsupportedFieldReason == "sentinel scoped-decline reason"
  test "itSeq scoped-decline placeholder -- seqUnsupportedFieldKind (item 3, walker v114)":
    ## `emitIRType`'s `itSeq` arm emitted `tUnsupportedFieldSeq(elemTy, reason)`
    ## without the `kind` argument, so every round trip silently reverted to
    ## `tUnsupportedFieldSeq`'s default (`seNestedSeqUnsupported`), discarding
    ## an operation-level origin's real classification (N4-style fail-silent
    ## class). Pin the non-default sentinel kind survives the round trip.
    let reconstructed = roundtripType(sUnsupportedFieldSeqType())
    check reconstructed.seqUnsupportedFieldKind == feUnsupportedOp
  test "itTable (recursive key + value)":
    check fieldwiseEq(sTableType(), roundtripType(sTableType()))
  test "itSet (recursive elemTy)":
    check fieldwiseEq(sSetType(), roundtripType(sSetType()))
  test "itTuple (fields, fieldNames, objectName, nominalId, isPlaceholder)":
    check fieldwiseEq(sTupleType(), roundtripType(sTupleType()))
  test "itTuple: KNOWN non-round-tripping field -- nameIsRefAlias reverts to false (documented, witness-codegen-only; NOT a silent gap -- pinned deliberately)":
    let reconstructed = roundtripType(tTuple(@[tInt(64, true)], @["f"], "Obj",
                                              "nomid", isPlaceholder = true,
                                              nameIsRefAlias = true))
    check reconstructed.nameIsRefAlias == false
    check reconstructed.isPlaceholder == true       ## DOES round-trip (H_witness fix)
    check reconstructed.nominalId == "nomid"         ## DOES round-trip (Cluster H Step C fix)
  test "itVariant (discriminator, arms incl. else-arm, discTags, plain fields)":
    check fieldwiseEq(sVariantType(), roundtripType(sVariantType()))
  test "itMultiVariant (multiple axes, each with its own arms/discTags)":
    check fieldwiseEq(sMultiVariantType(), roundtripType(sMultiVariantType()))

  test "exhaustiveness gate: every IRTypeKind is covered above (no `else` -- a new kind fails to compile)":
    proc auditIRTypeKindCoverage(k: IRTypeKind) =
      case k
      of itInt: discard                ## "itInt"
      of itBool: discard                ## "itBool"
      of itString: discard              ## "itString"
      of itFloat32, itFloat64: discard  ## "itFloat32 / itFloat64"
      of itUninterp: discard            ## "itUninterp"
      of itDistinct: discard            ## "itDistinct"
      of itRef: discard                 ## "itRef"
      of itPtr: discard                 ## "itPtr"
      of itArray: discard               ## "itArray"
      of itSeq: discard                 ## "itSeq" + scoped-decline test
      of itTable: discard               ## "itTable"
      of itSet: discard                 ## "itSet"
      of itTuple: discard               ## "itTuple" + nameIsRefAlias pin
      of itVariant: discard             ## "itVariant"
      of itMultiVariant: discard        ## "itMultiVariant"
    auditIRTypeKindCoverage(itBool)  ## formality: silence the unused-proc warning

# ---------------------------------------------------------------------------
# IRExpr sentinels + round-trip tests
# ---------------------------------------------------------------------------

proc sIntLit(): IRExpr = mkIntLit(123456789'i64)
proc sFloatLit(): IRExpr = mkFloatLit(12345.25'f64, 32)
proc sConvIntToFloat(): IRExpr = mkConvIntToFloat(mkIntLit(9), 32)
proc sConvFloatToInt(): IRExpr = mkConvFloatToInt(mkFloatLit(9.5, 64), 32)
proc sConvIntWidth(): IRExpr = mkConvIntWidth(mkVar("w"), 8, true, 64, false)
proc sConvIntReinterpret(): IRExpr = mkConvIntReinterpret(mkVar("w2"), 32, false)
proc sMathCall(): IRExpr = mkMathCall("sentinelMathOp", @[mkIntLit(1), mkIntLit(2)])
proc sBoolLit(): IRExpr = mkBoolLit(true)
proc sVar(): IRExpr = mkVar("sentinelVarName")
proc sBinop(): IRExpr = mkBinop(bAdd, mkIntLit(11), mkVar("sentinelBinopVar"))
proc sUnop(): IRExpr = mkUnop(uNeg, mkIntLit(5))
proc sBorrowOp(): IRExpr =
  mkBorrowOp(bXor, mkIntLit(5), mkVar("distSentinel"), true, "Meters")
proc sField(): IRExpr = mkField(mkVar("obj"), 3, "sentinelFieldName")
proc sIndex(): IRExpr = mkIndex(mkVar("arr"), mkIntLit(2))
proc sArrayLit(): IRExpr = mkArrayLit(@[mkIntLit(1), mkIntLit(2)], tInt(64, true))
proc sTupleLit(): IRExpr =
  let ty = tTuple(@[tInt(64, true), tString()], @["a", "b"])
  mkTupleLit(@[mkIntLit(1), mkStrLit("x")], ty)
proc sVariantLit(): IRExpr =
  let ty = tVariant("SentShape2", "kind", tInt(64, true),
    @[VariantArm(tagOrdinal: 0, tagName: "skCircle",
                  fieldNames: @["radius"], fieldTypes: @[tInt(64, true)], isElse: false)],
    plainFieldNames = @["id"], plainFieldTypes = @[tString()])
  mkVariantLit(ty, 0, "skCircle", @[mkIntLit(9)], @[mkStrLit("pid")])
proc sSeqLen(): IRExpr = mkSeqLen(mkVar("s"), "sentinel.nim:1:2: s.len")
proc sSeqSlice(): IRExpr = mkSeqSlice(mkVar("data"), mkIntLit(1), mkIntLit(4))
proc sStrLit(): IRExpr = mkStrLit("sentinelString")
proc sContains(): IRExpr = mkContains(mkVar("s"), mkVar("k"))
proc sSeqAdd(): IRExpr = mkSeqAdd(mkVar("s"), mkIntLit(9))
proc sSeqDel(): IRExpr = mkSeqDel(mkVar("s"), mkIntLit(2))
proc sSeqInsert(): IRExpr = mkSeqInsert(mkVar("s"), mkIntLit(7), mkIntLit(1))
proc sSeqPop(): IRExpr = mkSeqPop(mkVar("s"))
proc sTableSet(): IRExpr = mkTableSet(mkVar("t"), mkStrLit("k"), mkIntLit(1))
proc sTableDel(): IRExpr = mkTableDel(mkVar("t"), mkStrLit("k"))
proc sSetIncl(): IRExpr = mkSetIncl(mkVar("st"), mkIntLit(4))
proc sSetExcl(): IRExpr = mkSetExcl(mkVar("st"), mkIntLit(4))
proc sStrOpPlain(): IRExpr = mkStrOp(iekStrLen, "len", @[mkVar("s")])
proc sStrOpWithArgsAndOp(): IRExpr =
  mkStrOp(iekRadixFmt, "toHex:16:2", @[mkVar("n")])
proc sStrOpUnsupportedWithRetTy(): IRExpr =
  ## Fix-slice item 5: `strRetTy` -- the NEW field `degradeStrArm`
  ## (runtime.nim) reads to type an `iekStrUnsupported` placeholder from the
  ## call expression's own classified type instead of a per-name lookup. A
  ## non-default (non-`itString`) sentinel makes a silently-reverted field
  ## observable, mirroring `sUnsupportedFieldSeqType`'s own idiom above.
  mkStrOp(iekStrUnsupported, "sentinelUnmodeledCall", @[mkVar("recv")],
          retTy = tInt(64, true))
proc sGetCurrentExn(): IRExpr = mkGetCurrentExn()
proc sGetCurrentExnMsg(): IRExpr = mkGetCurrentExnMsg()
proc sLambda(): IRExpr =
  mkLambda(99999'i64, 7,
    @[IRParam(name: "p1", ty: tInt(16, false), rangeLo: -5, rangeHi: 99,
              hasRange: true, isVar: true, isStringBacked: true, isIntOffset: true)],
    mkReturnVal(mkVar("p1")), @["capA", "capB"], tString())
proc sClosureCall(): IRExpr = mkClosureCall("sentinelClosureCallee", @[mkIntLit(3)])
proc sSeqLit(): IRExpr = mkSeqLit(@[mkIntLit(1), mkIntLit(2)], tInt(64, true))
proc sHofCallWithInit(): IRExpr =
  mkHofCall("fold", mkVar("xs"), mkVar("f"), tInt(32, true), mkIntLit(0))
proc sHofCallNoInit(): IRExpr =
  mkHofCall("map", mkVar("ys"), mkVar("g"), tString())
proc sNilLit(): IRExpr = mkNil(tRef(tInt(64, true)))

suite "R6 emit round-trip -- IRExpr kinds":
  test "iekIntLit":
    check fieldwiseEq(sIntLit(), roundtripExpr(sIntLit()))
  test "iekFloatLit":
    check fieldwiseEq(sFloatLit(), roundtripExpr(sFloatLit()))
  test "iekConvIntToFloat":
    check fieldwiseEq(sConvIntToFloat(), roundtripExpr(sConvIntToFloat()))
  test "iekConvFloatToInt":
    check fieldwiseEq(sConvFloatToInt(), roundtripExpr(sConvFloatToInt()))
  test "iekConvIntWidth":
    check fieldwiseEq(sConvIntWidth(), roundtripExpr(sConvIntWidth()))
  test "iekConvIntReinterpret (item 7b -- was missing from this audit entirely)":
    check fieldwiseEq(sConvIntReinterpret(), roundtripExpr(sConvIntReinterpret()))
  test "iekMathCall":
    check fieldwiseEq(sMathCall(), roundtripExpr(sMathCall()))
  test "iekBoolLit":
    check fieldwiseEq(sBoolLit(), roundtripExpr(sBoolLit()))
  test "iekVar":
    check fieldwiseEq(sVar(), roundtripExpr(sVar()))
  test "iekBinop":
    check fieldwiseEq(sBinop(), roundtripExpr(sBinop()))
  test "iekUnop":
    check fieldwiseEq(sUnop(), roundtripExpr(sUnop()))
  test "iekBorrowOp":
    check fieldwiseEq(sBorrowOp(), roundtripExpr(sBorrowOp()))
  test "iekField":
    check fieldwiseEq(sField(), roundtripExpr(sField()))
  test "iekIndex":
    check fieldwiseEq(sIndex(), roundtripExpr(sIndex()))
  test "iekArrayLit":
    check fieldwiseEq(sArrayLit(), roundtripExpr(sArrayLit()))
  test "iekTupleLit":
    check fieldwiseEq(sTupleLit(), roundtripExpr(sTupleLit()))
  test "iekVariantLit":
    check fieldwiseEq(sVariantLit(), roundtripExpr(sVariantLit()))
  test "iekSeqLen":
    check fieldwiseEq(sSeqLen(), roundtripExpr(sSeqLen()))
  test "iekSeqSlice":
    check fieldwiseEq(sSeqSlice(), roundtripExpr(sSeqSlice()))
  test "iekStrLit":
    check fieldwiseEq(sStrLit(), roundtripExpr(sStrLit()))
  test "iekContains":
    check fieldwiseEq(sContains(), roundtripExpr(sContains()))
  test "iekSeqAdd":
    check fieldwiseEq(sSeqAdd(), roundtripExpr(sSeqAdd()))
  test "iekSeqDel":
    check fieldwiseEq(sSeqDel(), roundtripExpr(sSeqDel()))
  test "iekSeqInsert":
    check fieldwiseEq(sSeqInsert(), roundtripExpr(sSeqInsert()))
  test "iekSeqPop":
    check fieldwiseEq(sSeqPop(), roundtripExpr(sSeqPop()))
  test "iekTableSet":
    check fieldwiseEq(sTableSet(), roundtripExpr(sTableSet()))
  test "iekTableDel":
    check fieldwiseEq(sTableDel(), roundtripExpr(sTableDel()))
  test "iekSetIncl":
    check fieldwiseEq(sSetIncl(), roundtripExpr(sSetIncl()))
  test "iekSetExcl":
    check fieldwiseEq(sSetExcl(), roundtripExpr(sSetExcl()))
  test "StrOpKinds shared arm -- plain (iekStrLen)":
    check fieldwiseEq(sStrOpPlain(), roundtripExpr(sStrOpPlain()))
  test "StrOpKinds shared arm -- with strOp payload (iekRadixFmt)":
    let reconstructed = roundtripExpr(sStrOpWithArgsAndOp())
    check fieldwiseEq(sStrOpWithArgsAndOp(), reconstructed)
    check reconstructed.kind == iekRadixFmt
    check reconstructed.strOp == "toHex:16:2"
  test "StrOpKinds shared arm -- strRetTy (fix-slice item 5, iekStrUnsupported non-default type)":
    let reconstructed = roundtripExpr(sStrOpUnsupportedWithRetTy())
    check fieldwiseEq(sStrOpUnsupportedWithRetTy(), reconstructed)
    check reconstructed.strRetTy.kind == itInt
    check reconstructed.strRetTy.width == 64
    check reconstructed.strRetTy.signed == true
  test "iekGetCurrentExn":
    check fieldwiseEq(sGetCurrentExn(), roundtripExpr(sGetCurrentExn()))
  test "iekGetCurrentExnMsg":
    check fieldwiseEq(sGetCurrentExnMsg(), roundtripExpr(sGetCurrentExnMsg()))
  test "iekLambda (params via emitParam idiom, body, captures, retTy)":
    check fieldwiseEq(sLambda(), roundtripExpr(sLambda()))
  test "iekClosureCall":
    check fieldwiseEq(sClosureCall(), roundtripExpr(sClosureCall()))
  test "iekSeqLit":
    check fieldwiseEq(sSeqLit(), roundtripExpr(sSeqLit()))
  test "iekHofCall (with hofInit -- fold)":
    check fieldwiseEq(sHofCallWithInit(), roundtripExpr(sHofCallWithInit()))
  test "iekHofCall (hofInit nil -- map/filter)":
    let reconstructed = roundtripExpr(sHofCallNoInit())
    check fieldwiseEq(sHofCallNoInit(), reconstructed)
    check reconstructed.hofInit == nil
  test "iekNil":
    check fieldwiseEq(sNilLit(), roundtripExpr(sNilLit()))

  test "exhaustiveness gate: every IRExprKind is covered above (no `else` -- a new kind fails to compile)":
    proc auditIRExprKindCoverage(k: IRExprKind) =
      case k
      of iekIntLit: discard                    ## "iekIntLit"
      of iekFloatLit: discard                   ## "iekFloatLit"
      of iekConvIntToFloat: discard              ## "iekConvIntToFloat"
      of iekConvFloatToInt: discard              ## "iekConvFloatToInt"
      of iekConvIntWidth: discard                ## "iekConvIntWidth"
      of iekConvIntReinterpret: discard          ## "iekConvIntReinterpret" (item 7b)
      of iekMathCall: discard                    ## "iekMathCall"
      of iekBoolLit: discard                     ## "iekBoolLit"
      of iekVar: discard                         ## "iekVar"
      of iekBinop: discard                       ## "iekBinop"
      of iekUnop: discard                        ## "iekUnop"
      of iekBorrowOp: discard                     ## "iekBorrowOp"
      of iekField: discard                       ## "iekField"
      of iekIndex: discard                       ## "iekIndex"
      of iekArrayLit: discard                    ## "iekArrayLit"
      of iekTupleLit: discard                    ## "iekTupleLit"
      of iekVariantLit: discard                  ## "iekVariantLit"
      of iekSeqLen: discard                      ## "iekSeqLen"
      of iekSeqSlice: discard                    ## "iekSeqSlice"
      of iekStrLit: discard                      ## "iekStrLit"
      of iekContains: discard                    ## "iekContains"
      of iekSeqAdd: discard                      ## "iekSeqAdd"
      of iekSeqDel: discard                      ## "iekSeqDel"
      of iekSeqInsert: discard                   ## "iekSeqInsert"
      of iekSeqPop: discard                      ## "iekSeqPop"
      of iekTableSet: discard                    ## "iekTableSet"
      of iekTableDel: discard                    ## "iekTableDel"
      of iekSetIncl: discard                     ## "iekSetIncl"
      of iekSetExcl: discard                     ## "iekSetExcl"
      of iekStrLen, iekStrAt, iekStrSubstr, iekStrFind, iekStrRfind,
         iekStrContains, iekStrStartsWith, iekStrEndsWith, iekStrReplace,
         iekStrReplaceAll, iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe,
         iekStrReplaceRe, iekStrBytes, iekStrConcat, iekIntToStr, iekStrToInt,
         iekRadixFmt, iekStrUnsupported, iekStrToLower, iekStrToUpper,
         iekRuneToStr, iekStrStrip, iekStrInOptionRegion:
        discard  ## "StrOpKinds shared arm" (2 tests: plain + strOp payload)
      of iekGetCurrentExn: discard               ## "iekGetCurrentExn"
      of iekGetCurrentExnMsg: discard            ## "iekGetCurrentExnMsg"
      of iekLambda: discard                      ## "iekLambda"
      of iekClosureCall: discard                 ## "iekClosureCall"
      of iekSeqLit: discard                      ## "iekSeqLit"
      of iekHofCall: discard                     ## "iekHofCall" (2 tests: with/without hofInit)
      of iekNil: discard                         ## "iekNil"
    auditIRExprKindCoverage(iekIntLit)  ## formality: silence the unused-proc warning

# ---------------------------------------------------------------------------
# IRStmt sentinels + round-trip tests
# ---------------------------------------------------------------------------

proc sBlock(): IRStmt = mkBlock(@[mkAssign("a", mkIntLit(1)), mkBreak()])
proc sIfWithElse(): IRStmt =
  mkIf(@[mkBranch(mkBoolLit(true), mkBlock(@[mkContinue()]))],
       mkBlock(@[mkBreak()]))
proc sIfNoElse(): IRStmt =
  mkIf(@[mkBranch(mkBoolLit(false), mkReturn())])
proc sLet(): IRStmt = mkLet("sentinelLet", tInt(64, true), mkIntLit(42), isIntOffsetLocal = true)
proc sAssign(): IRStmt = mkAssign("sentinelAssign", mkBoolLit(true))
proc sWhile(): IRStmt =
  ## `hasAssumedBound = true` (item 3, round-6 fix round 3): the field
  ## defaults to `false`, so leaving it at the default here would make a
  ## silently-dropped emit argument unobservable -- the exact class of gap
  ## this file's header (B5/`itSeq`) exists to catch.
  mkWhile(mkBoolLit(true), mkBlock(@[mkBreak()]), hasAssumedBound = true)
proc sBreak(): IRStmt = mkBreak()
proc sContinue(): IRStmt = mkContinue()
proc sReturnVal(): IRStmt = mkReturnVal(mkIntLit(7))
proc sReturnVoid(): IRStmt = mkReturn()
proc sAssert(): IRStmt = mkAssert(mkBinop(bLt, mkVar("x"), mkIntLit(10)))
proc sAssume(): IRStmt = mkAssume(mkBinop(bGe, mkVar("y"), mkIntLit(3)))
proc sCallWithOffsets(): IRStmt =
  ## The historically-dropped B5 field: `retIntOffsetPositions`.
  mkCall("sentinelCallee", "sentinelRet", @[mkIntLit(1), mkVar("arg2")],
         tInt(64, true), retIntOffsetPositions = @[0, 2])
proc sOpaqueCall(): IRStmt =
  mkOpaqueCall("sentinelOpaque", "retOp", @[mkStrLit("s")], tString())
proc sVariantFieldStmt(): IRStmt =
  mkVariantFieldStmt("sentVF", mkVar("obj"), "radius", tInt(64, true), @[0, 2, 5])
proc sVariantReassign(): IRStmt = mkVariantReassign("sentObj", 3, "skSquare")
proc sVariantReassignSymbolic(): IRStmt =
  mkVariantReassignSymbolic("sentObj2", "axisA", mkVar("symDisc"))
proc sVariantConstructSym(): IRStmt =
  let vty = tVariant("SentShape3", "kind", tInt(64, true),
    @[VariantArm(tagOrdinal: 0, tagName: "skA",
                  fieldNames: @["f1"], fieldTypes: @[tInt(64, true)], isElse: false)],
    plainFieldNames = @["id"], plainFieldTypes = @[tString()])
  mkVariantConstructSym("sentRes", vty, mkVar("symTag"), @[0, 1],
                         @[mkStrLit("pid")], "sentinel.nim:1:2: sentinel loc")
proc sIndexStmt(): IRStmt =
  mkIndexStmt("sentIx", mkVar("arr"), mkIntLit(2), tInt(32, false), "sentinel.nim:9:9")
proc sIndexAssignStmt(): IRStmt =
  ## N14 (9dbc3df) / item 2 (round-6 fix round 3): every field at a
  ## distinguishing non-default value -- `iaRecvName` distinct from
  ## `sIndexStmt`'s `ixRetName`, `iaIdx`/`iaVal` distinct literals so a
  ## swapped-argument emit bug would be observable, `iaLoc` non-empty.
  mkIndexAssignStmt("sentIaRecv", mkIntLit(3), mkIntLit(99),
                     "sentinel.nim:10:10: sentIaRecv[3] = 99")
proc sSeqPopStmt(): IRStmt =
  ## N14 (9dbc3df) / item 2 (round-6 fix round 3): `spRecvName` and
  ## `spRetName` set to distinct sentinel names (a swapped-argument emit bug
  ## would otherwise be invisible to `fieldwiseEq`), `spLoc` non-empty.
  mkSeqPopStmt("sentSpRecv", "sentSpRet", "sentinel.nim:11:11: sentSpRet := sentSpRecv.pop()")
proc sTargetLabel(): IRStmt = mkTargetLabel("sentLabel")
proc sRaiseWithMsg(): IRStmt = mkRaise("ValueError", mkStrLit("boom"))
proc sReraise(): IRStmt = mkReraise()
proc sTryFull(): IRStmt =
  mkTry(mkBlock(@[mkAssign("a", mkIntLit(1))]),
        @[ExceptHandler(typeIds: @["ValueError", "KeyError"], body: mkBlock(@[mkBreak()])),
          ExceptHandler(typeIds: @[], body: mkReturn())],  ## bare catch-all
        mkBlock(@[mkContinue()]))
proc sTryNoFinally(): IRStmt =
  mkTry(mkBlock(@[mkAssert(mkBoolLit(true))]),
        @[ExceptHandler(typeIds: @["OSError"], body: mkBreak())])
proc sDerefBare(): IRStmt = mkDeref("sentDeref", mkVar("ptr1"), tInt(64, true))
proc sPtrDeref(): IRStmt = mkPtrDeref("sentPtrDeref", mkVar("ptr2"), tFloat64())
proc sFieldDeref(): IRStmt =
  mkFieldDeref("sentFieldDeref", mkVar("obj1"), tInt(64, true),
               tTuple(@[tInt(64, true)], @["f"], "Obj", "objNomId"), "f", ptrFamily = true)
proc sNewT(): IRStmt = mkNewT("sentNew", tRef(tInt(64, true)))
proc sDerefWriteBare(): IRStmt =
  mkDerefWrite(mkVar("wptr"), mkIntLit(9), tInt(64, true), ptrFamily = true)
proc sFieldDerefWrite(): IRStmt =
  mkFieldDerefWrite(mkVar("wobj"), mkBoolLit(true), tBool(),
                     tTuple(@[tBool()], @["b"], "WObj", "wObjId"), "b", ptrFamily = false)
proc sUnsupportedStmt(): IRStmt = mkUnsupported("sentinel unsupported reason")
proc sUnsafeCast(): IRStmt = mkUnsafeCast("cast[ptr T]")

suite "R6 emit round-trip -- IRStmt kinds":
  test "isBlock":
    check fieldwiseEq(sBlock(), roundtripStmt(sBlock()))
  test "isIf (with elseBody)":
    check fieldwiseEq(sIfWithElse(), roundtripStmt(sIfWithElse()))
  test "isIf (elseBody nil)":
    let reconstructed = roundtripStmt(sIfNoElse())
    check fieldwiseEq(sIfNoElse(), reconstructed)
    check reconstructed.elseBody == nil
  test "isLet":
    check fieldwiseEq(sLet(), roundtripStmt(sLet()))
  test "isAssign":
    check fieldwiseEq(sAssign(), roundtripStmt(sAssign()))
  test "isWhile":
    check fieldwiseEq(sWhile(), roundtripStmt(sWhile()))
  test "isBreak":
    check fieldwiseEq(sBreak(), roundtripStmt(sBreak()))
  test "isContinue":
    check fieldwiseEq(sContinue(), roundtripStmt(sContinue()))
  test "isReturn (with value)":
    check fieldwiseEq(sReturnVal(), roundtripStmt(sReturnVal()))
  test "isReturn (void, retExpr nil)":
    let reconstructed = roundtripStmt(sReturnVoid())
    check fieldwiseEq(sReturnVoid(), reconstructed)
    check reconstructed.retExpr == nil
  test "isAssert":
    check fieldwiseEq(sAssert(), roundtripStmt(sAssert()))
  test "isAssume":
    check fieldwiseEq(sAssume(), roundtripStmt(sAssume()))
  test "isCall (non-opaque, WITH retIntOffsetPositions -- the B5 historical field)":
    let reconstructed = roundtripStmt(sCallWithOffsets())
    check fieldwiseEq(sCallWithOffsets(), reconstructed)
    check reconstructed.retIntOffsetPositions == @[0, 2]
  test "isCall (opaque)":
    check fieldwiseEq(sOpaqueCall(), roundtripStmt(sOpaqueCall()))
  test "isVariantField":
    check fieldwiseEq(sVariantFieldStmt(), roundtripStmt(sVariantFieldStmt()))
  test "isVariantReassign":
    check fieldwiseEq(sVariantReassign(), roundtripStmt(sVariantReassign()))
  test "isVariantReassignSymbolic":
    check fieldwiseEq(sVariantReassignSymbolic(), roundtripStmt(sVariantReassignSymbolic()))
  test "isVariantConstructSym":
    check fieldwiseEq(sVariantConstructSym(), roundtripStmt(sVariantConstructSym()))
  test "isIndex":
    check fieldwiseEq(sIndexStmt(), roundtripStmt(sIndexStmt()))
  test "isIndexAssign (N14, item 2 -- was entirely missing from this audit)":
    check fieldwiseEq(sIndexAssignStmt(), roundtripStmt(sIndexAssignStmt()))
  test "isSeqPop (N14, item 2 -- was entirely missing from this audit)":
    check fieldwiseEq(sSeqPopStmt(), roundtripStmt(sSeqPopStmt()))
  test "isTargetLabel":
    check fieldwiseEq(sTargetLabel(), roundtripStmt(sTargetLabel()))
  test "isRaise (with message)":
    check fieldwiseEq(sRaiseWithMsg(), roundtripStmt(sRaiseWithMsg()))
  test "isRaise (bare re-raise)":
    let reconstructed = roundtripStmt(sReraise())
    check fieldwiseEq(sReraise(), reconstructed)
    check reconstructed.raiseIsReraise == true
    check reconstructed.raiseMsg == nil
  test "isTry (handlers incl. bare catch-all, WITH finally)":
    check fieldwiseEq(sTryFull(), roundtripStmt(sTryFull()))
  test "isTry (finally nil)":
    let reconstructed = roundtripStmt(sTryNoFinally())
    check fieldwiseEq(sTryNoFinally(), reconstructed)
    check reconstructed.tryFinally == nil
  test "isDeref (bare ref deref -- mkDeref)":
    check fieldwiseEq(sDerefBare(), roundtripStmt(sDerefBare()))
  test "isDeref (bare ptr deref -- mkPtrDeref)":
    check fieldwiseEq(sPtrDeref(), roundtripStmt(sPtrDeref()))
  test "isDeref (field deref -- mkFieldDeref)":
    check fieldwiseEq(sFieldDeref(), roundtripStmt(sFieldDeref()))
  test "isNew":
    check fieldwiseEq(sNewT(), roundtripStmt(sNewT()))
  test "isDerefWrite (bare -- mkDerefWrite)":
    check fieldwiseEq(sDerefWriteBare(), roundtripStmt(sDerefWriteBare()))
  test "isDerefWrite (field write -- mkFieldDerefWrite)":
    check fieldwiseEq(sFieldDerefWrite(), roundtripStmt(sFieldDerefWrite()))
  test "isUnsupported":
    check fieldwiseEq(sUnsupportedStmt(), roundtripStmt(sUnsupportedStmt()))
  test "isUnsafeCast":
    check fieldwiseEq(sUnsafeCast(), roundtripStmt(sUnsafeCast()))

  test "exhaustiveness gate: every IRStmtKind is covered above (no `else` -- a new kind fails to compile)":
    proc auditIRStmtKindCoverage(k: IRStmtKind) =
      case k
      of isBlock: discard                        ## "isBlock"
      of isIf: discard                            ## "isIf" (2 tests: with/without elseBody)
      of isLet: discard                           ## "isLet"
      of isAssign: discard                        ## "isAssign"
      of isWhile: discard                         ## "isWhile"
      of isBreak: discard                         ## "isBreak"
      of isContinue: discard                      ## "isContinue"
      of isReturn: discard                        ## "isReturn" (2 tests: with/without value)
      of isAssert: discard                        ## "isAssert"
      of isAssume: discard                        ## "isAssume"
      of isCall: discard                          ## "isCall" (2 tests: opaque + retIntOffsetPositions)
      of isVariantField: discard                  ## "isVariantField"
      of isVariantReassign: discard               ## "isVariantReassign"
      of isVariantReassignSymbolic: discard        ## "isVariantReassignSymbolic"
      of isVariantConstructSym: discard            ## "isVariantConstructSym"
      of isIndex: discard                         ## "isIndex"
      of isIndexAssign: discard                   ## "isIndexAssign" (item 2, N14)
      of isSeqPop: discard                        ## "isSeqPop" (item 2, N14)
      of isTargetLabel: discard                   ## "isTargetLabel"
      of isRaise: discard                         ## "isRaise" (2 tests: msg + bare re-raise)
      of isTry: discard                           ## "isTry" (2 tests: with/without finally)
      of isDeref: discard                         ## "isDeref" (3 tests: bare ref/ptr/field)
      of isNew: discard                           ## "isNew"
      of isDerefWrite: discard                    ## "isDerefWrite" (2 tests: bare + field)
      of isUnsupported: discard                   ## "isUnsupported"
      of isUnsafeCast: discard                    ## "isUnsafeCast"
    auditIRStmtKindCoverage(isBlock)  ## formality: silence the unused-proc warning
