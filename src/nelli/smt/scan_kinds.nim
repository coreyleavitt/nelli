## RFC-0016 K2F-1 / K2F-3 (RFC section 8.1). The node-kind lists every
## over-approximating scan shares: the inert leaves, the kinds that run no code,
## and the structural kinds whose effect is their children's. A scan lists its
## own arms for the kinds that carry an effect, recurses through the structural
## kinds, and answers conservatively (may write, may raise, open, unknown) for
## any kind in none of the lists.
import std/macros

const mayScanLeafKinds* = {nnkEmpty, nnkIdent, nnkType, nnkCharLit .. nnkNilLit,
                          nnkCommentStmt}
  ## RFC-0016 K2F-1. The leaves a "may" scan (`mayRearm`, `mayResizeSeq`,
  ## `mayWriteRoot`, `scanShapeReceiverMutated`) reads as inert: a literal, a
  ## name that is not a symbol (a pragma word), a type. A symbol is each scan's
  ## own arm.

const mayScanNoCodeKinds* = {nnkTypeSection, nnkTypeDef, nnkMixinStmt,
  nnkBindStmt, nnkTypeOfExpr, nnkUsingStmt, nnkStaticStmt, nnkRefTy, nnkPtrTy,
  nnkVarTy, nnkProcTy, nnkTupleTy, nnkObjectTy, nnkDistinctTy, nnkEnumTy,
  nnkIteratorTy, nnkStaticTy, nnkConstTy, nnkTupleClassTy, nnkTypeClassTy,
  nnkMutableTy, nnkFormalParams, nnkGenericParams}
  ## RFC-0016 K2F-1. Kinds that hold names but run no code at run time: a type
  ## or its declaration, a name-lookup declaration, an unevaluated `typeof`, a
  ## `static:` block, a routine's parameter list.

const mayScanStructuralKinds* = {nnkStmtList, nnkStmtListExpr, nnkBlockStmt,
  nnkBlockExpr, nnkIfStmt, nnkIfExpr, nnkElifBranch, nnkElifExpr, nnkElse,
  nnkElseExpr, nnkWhenStmt, nnkCaseStmt, nnkOfBranch, nnkWhileStmt, nnkForStmt,
  nnkReturnStmt, nnkBreakStmt, nnkContinueStmt, nnkDiscardStmt, nnkYieldStmt,
  nnkVarSection, nnkLetSection, nnkConstSection, nnkConstDef, nnkIdentDefs,
  nnkVarTuple, nnkTryStmt, nnkHiddenTryStmt, nnkExceptBranch, nnkFinally,
  nnkDefer, nnkRaiseStmt, nnkBracket, nnkCurly, nnkPar, nnkTupleConstr,
  nnkObjConstr, nnkExprColonExpr, nnkExprEqExpr, nnkBracketExpr, nnkDotExpr,
  nnkCheckedFieldExpr, nnkDerefExpr, nnkHiddenDeref, nnkAddr, nnkHiddenAddr,
  nnkConv, nnkHiddenStdConv, nnkHiddenSubConv, nnkCast, nnkChckRange,
  nnkChckRange64, nnkChckRangeF, nnkStringToCString, nnkCStringToString,
  nnkObjUpConv, nnkObjDownConv, nnkRange, nnkAsgn, nnkFastAsgn, nnkCall,
  nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit,
  nnkHiddenCallConv, nnkPragma, nnkPragmaBlock, nnkPragmaExpr,
  nnkOpenSymChoice, nnkClosedSymChoice} + RoutineNodes
  ## RFC-0016 K2F-1 (RFC section 8.1). The kinds that have no effect of their
  ## own: what they may do is what their children may, so a "may" scan
  ## recurses into them. A routine definition runs nothing, but its body is
  ## scanned all the same (each scan's own `RoutineNodes` arm, or the
  ## children): over-approximating a body that never runs costs only
  ## precision. A kind in none of the three sets (`asm`, a closure-iterator
  ## state node, any kind Nim adds) answers "may": the scan never looked at it.
