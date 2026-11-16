## RFC-0016 review D4. The error-kind properties (substitution class,
## severity) live in ONE compile-time table beside the enum
## (`errorkind.kindInfo`, an `array[SymexErrorKind, KindInfo]`), and callers
## read it through `classOf` / `severity` instead of assigning a severity
## literal per call site.
##
##   * characterization: every kind's (class, severity), a literal table taken
##     from the behaviour before the refactor (class from the old `classOf`
##     `case`, severity from what each emission site wrote);
##   * single source: a text census that no `src/` file outside
##     `errorkind.nim` assigns a severity literal (`severity: sevX`,
##     `severity = sevX`, `severity: if ..`);
##   * totality: `kindInfo` is an `array[SymexErrorKind, _]`, so a member
##     without a row does not compile; here it is checked to cover the enum.
import std/[unittest, strutils, os]
import nelli/smt/errorkind
import nelli/smt/types

const expected: seq[(SymexErrorKind, DegradeClass, SymexErrorSeverity)] = @[
    (ekZ3Error, dcNoAnswer, sevError),
    (ekZ3MemoryError, dcNoAnswer, sevError),
    (ekZ3InternalError, dcNoAnswer, sevError),
    (ekZ3SolverError, dcNoAnswer, sevError),
    (feUnsupportedOp, dcSubstituted, sevError),
    (feExtractionFailed, dcNoAnswer, sevError),
    (feConvDomainExcluded, dcNoAnswer, sevError),
    (seUnsupportedStringOp, dcNoAnswer, sevError),
    (seUnsupportedRegex, dcNoAnswer, sevError),
    (seZ3StringIncomplete, dcFreshSymbol, sevError),
    (seZ3VersionMissing, dcFreshSymbol, sevError),
    (seBytesSymbolicLength, dcNoAnswer, sevError),
    (seBytesLengthTooLarge, dcNoAnswer, sevError),
    (seByteIndexUnsupported, dcNoAnswer, sevError),
    (seByteIterUnsupported, dcSubstituted, sevError),
    (seUnsupportedTableValType, dcNoAnswer, sevError),
    (seUnsupportedSetCharInterop, dcNoAnswer, sevError),
    (seNestedSeqUnsupported, dcNoAnswer, sevError),
    (seParseIntPreE, dcNoAnswer, sevError),
    (eeUninterpRefExtraction, dcNoAnswer, sevHint),
    (eeRaiseUnimplemented, dcNoAnswer, sevError),
    (eeTryUnimplemented, dcNoAnswer, sevError),
    (eeRaiseOutsideHandler, dcOmitted, sevError),
    (eeNotInHandler, dcNoAnswer, sevError),
    (eeUnknownExnType, dcSubstituted, sevWarning),
    (geInstantiationCapped, dcSubstituted, sevError),
    (geConceptViolation, dcNoAnswer, sevError),
    (geUnresolvedGeneric, dcNoAnswer, sevError),
    (geDistinctBijectivitySkipped, dcNoAnswer, sevHint),
    (geDistinctBarrier, dcSubstituted, sevError),
    (ceNotImplemented, dcNoAnswer, sevError),
    (ceUnsupportedCapture, dcNoAnswer, sevError),
    (ceUnsupportedHof, dcSubstituted, sevError),
    (ceClosureUnknownCallee, dcSubstituted, sevError),
    (ceInlineBudgetExceeded, dcSubstituted, sevError),
    (heDepthExhausted, dcOmitted, sevError),
    (heUnsafeCast, dcOmitted, sevError),
    (hePtrArith, dcNoAnswer, sevError),
    (hePtrFamily, dcNoAnswer, sevHint),
    (heFreshnessCapExceeded, dcNoAnswer, sevHint),
    (heUnsupportedVarRef, dcNoAnswer, sevError),
    (heUnsupportedOwnership, dcNoAnswer, sevError),
    (heUnresolvedRef, dcNoAnswer, sevError),
    (geVtableDispatch, dcNoAnswer, sevError),
    (ceClosureBodyUncertain, dcFreshSymbol, sevError),
    (weInternalWalkerFault, dcNoAnswer, sevError),
    (beBudgetExhausted, dcFabricated, sevError),
    (feUnsupportedExprKind, dcNoAnswer, sevError),
    (feUnsupportedParamType, dcNoAnswer, sevError),
    (feUnsupportedWitnessType, dcNoAnswer, sevError),
    (heNewFieldZeroUnsupported, dcFreshSymbol, sevError),
    (seUnsupportedTableKeyType, dcNoAnswer, sevError),
    (seUnsupportedCompoundSortLeaf, dcSubstituted, sevError),
    (beBudgetExhaustedAssumedBound, dcFabricated, sevError),
    (feOpaqueCallUnmodelled, dcSubstituted, sevError),
    (feEnumOrdinalUnresolved, dcSubstituted, sevError),
    (feTransparentArgNotInert, dcNoAnswer, sevError),
    (feTransparentResultUsed, dcNoAnswer, sevError),
    (feGlobalReadUnmodelled, dcSubstituted, sevError),
    (seVariantFieldOnDeclinedCtor, dcOmitted, sevError),
    (feUnsupportedStmtKind, dcSubstituted, sevError),
    (weRecursionCycleCut, dcSubstituted, sevError),
    (eeHandlerReraiseUnmodelled, dcOmitted, sevError),
    (ceClosureBodyDiverged, dcOmitted, sevError),
    (weBreakOutsideLoop, dcOmitted, sevError),
    (beSolverUndef, dcNoAnswer, sevError),
    (heUnsupportedPointeeRead, dcFreshSymbol, sevError),
    (seRuneDecodeSymbolic, dcSubstituted, sevError),
    (beBudgetExhaustedPrune, dcOmitted, sevError),
    (beBudgetExhaustedUnmodelled, dcSubstituted, sevError),
    (feUnsupportedOpHavoc, dcFreshSymbol, sevError),
    (feUnsupportedOpAborted, dcNoAnswer, sevError),
    (seParseIntLaxSyntax, dcFreshSymbol, sevError),
    (feReplayTimedOut, dcFreshSymbol, sevHint),
    (feReplayCrashed, dcFreshSymbol, sevHint),
    (feReplayDeclined, dcFreshSymbol, sevHint),
    (feReplayRefuted, dcFreshSymbol, sevHint),
    (ceCaptureByRefUnmodelled, dcSubstituted, sevError),
    (feConvFloatToIntUndefined, dcFreshSymbol, sevError),
    (eeFinallyReturnOnRaise, dcOmitted, sevError),
    (eeFinallyJumpOnRaise, dcOmitted, sevError),
    (feGlobalHavoc, dcFreshSymbol, sevError),
    (feOpaqueEffectHavoc, dcFreshSymbol, sevError),
    (feUncheckedDiscBytes, dcFreshSymbol, sevError),
    (feLocalPragma, dcSubstituted, sevError),
    (feEvalOrderUnmodelled, dcNoAnswer, sevError),
    (feTableIterOrder, dcFreshSymbol, sevError),
    (seRecursiveValueDepth, dcNoAnswer, sevError),
    (feGlobalRouteUnproved, dcSubstituted, sevError),
    (feCheckOption, dcSubstituted, sevError),
    (feOverflowCheckOption, dcSubstituted, sevError),
    (heNilDerefMayBeCaught, dcNoAnswer, sevError),
    (feFloatWidth, dcNoAnswer, sevError),
    (ubUnsignedDivZero, dcOmitted, sevError),
    (ubIntMinModMinusOne, dcOmitted, sevError),
    (ubSignedOverflow, dcOmitted, sevError),
    (ubIndeterminateRead, dcOmitted, sevError),
    (ubSignedDivZero, dcOmitted, sevError),
    (ubFloatToIntRange, dcOmitted, sevError),
    (ubTailUnverified, dcOmitted, sevError),
    (ubArrayOutOfBounds, dcOmitted, sevError),
    (ubInvalidObjConversion, dcOmitted, sevError),
    (ubInactiveVariantField, dcOmitted, sevError),
    (feHostUnadmitted, dcNoAnswer, sevError),
    (feUnadmitted, dcOmitted, sevError),
    (feDefectExcluded, dcOmitted, sevError),
  ]

suite "D4: error-kind table":
  test "every kind's class is the pre-refactor class":
    check expected.len == ord(high(SymexErrorKind)) + 1
    var seen: set[SymexErrorKind]
    for (k, _, _) in expected:
      check k notin seen     # one literal row per kind: a zero-tuple row in
      seen.incl k            # the table cannot hide behind a repeated entry
    check seen == {low(SymexErrorKind) .. high(SymexErrorKind)}
    for (k, c, s) in expected:
      check classOf(k) == c
      check severity(k) == s
      check kindInfo[k] == (class: c, severity: s)
  test "the table is total over the enum (compile-time)":
    static:
      doAssert kindInfo.len == ord(high(SymexErrorKind)) + 1
      for k in SymexErrorKind: doAssert kindInfo[k].severity in {sevHint, sevWarning, sevError}
    check true
  test "the named overrides":
    check declineSeverity == sevError
    check demotedSeverity == sevHint
    check severity(eeUnknownExnType) != declineSeverity
  test "no src file outside errorkind.nim assigns a severity literal":
    let dir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
    var offenders: seq[string]
    for f in walkDirRec(dir):
      if not f.endsWith(".nim") or f.endsWith("errorkind.nim"): continue
      var n = 0
      for line in readFile(f).splitLines:
        inc n
        let i = line.find('#')
        let code = if i >= 0: line[0 ..< i] else: line
        let j = code.find("severity")
        if j < 0: continue
        var rest = code[j + "severity".len .. ^1].strip()
        if rest.startsWith("=="): continue
        if not (rest.startsWith(":") or rest.startsWith("=")): continue
        rest = rest.strip(chars = {':', '=', ' '})
        if rest.startsWith("sevHint") or rest.startsWith("sevWarning") or
           rest.startsWith("sevError") or rest.startsWith("if "):
          offenders.add f.extractFilename & ":" & $n
    check offenders == newSeq[string]()
