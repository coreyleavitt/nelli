## RFC-0005 (soundness channels) slice S6b -- classify `feUnsupportedOp`, the
## heap/halt sites, `eeUnknownExnType`, and every kind still at S1's ⊤
## default that is neither genuinely no-answer nor owned by S7 (§5 row S6,
## second half; §3.1's substitution rule; §3.2's split discipline).
## Walker 144 -> 145.
##
## What the site-by-site audit found (the classes are pinned in suite (a),
## the site counts in suite (d)):
##
## `feUnsupportedOp` was ONE kind at ~30 sites spanning THREE classes.
##   - FRESH (`feUnsupportedOpHavoc`, `dcFreshSymbol`): the site binds a
##     fresh, otherwise unconstrained symbol of the right sort and drops
##     nothing -- the Int-sorted reinterpret conversion, the iteSV merges of
##     uninterpreted refs / seqs / strings / tables / sets, the closure-env
##     leaf conjunct, bool ordering (`a < b` on bools), and the three
##     composite call-result bindings (explicit `return`, implicit-result
##     fallthrough, untouched result without a zero default) that leave the
##     per-call `retSym` free. Every value reality can produce is a model of
##     the fresh symbol, so an UNSAT over such a run is a real UNSAT.
##   - SUBSTITUTED (the original `feUnsupportedOp`, `dcSubstituted`): the
##     site forwards an operand, drops a write or a raise fork, or evaluates
##     a composite comparison by name (a user `==`/`<` overload's raise is
##     dropped) -- the variant/closure merges, `retBindEq`'s vacuous true,
##     slices, table set / insert / pop, `contains`, `borrow`, the variant
##     reassign, the closure sink, the parser's unregistered callees.
##   - NO ANSWER (`feUnsupportedOpAborted`, `dcNoAnswer`): the `runSymex`
##     boundary's `SymexUnsupportedOpError` abort -- the walk stopped.
## Heap/halt: `heDepthExhausted` (the path is dropped), `heUnsafeCast` (the
## walker arm returns `@[]`), `weBreakOutsideLoop`,
## `seVariantFieldOnDeclinedCtor`, `eeRaiseOutsideHandler` and
## `eeHandlerReraiseUnmodelled` are HALTS: `dcOmitted`, token discarded.
## `heNewFieldZeroUnsupported` leaves an untouched composite heap cell at a
## fresh address unconstrained: `dcFreshSymbol`.
##
## `eeUnknownExnType` (DECISION: classify and taint, not inert). The raise's
## type is not in the hierarchy table, so routing guesses: every NAMED
## handler is skipped and the boundary classifies it as a non-defect. Both
## guesses are wrong for real programs -- `except ValueError` catches a
## `ref ValueError` returned from a helper (the old walk reported a false
## `sxUnsat` for that handler's target), and a bare `except:` past a skipped
## inner handler is reached only in the walk (a false `sxSat`). So it is
## `dcSubstituted`: recorded once through `degrade` (`dsUnknownExn`, still
## `sevWarning` for its consumers, admitted to the run coordinate by
## `taintsRun`'s one carve-out) and its token joined onto the path exactly
## where the guess is acted on (a named handler skipped, or a boundary
## finding). A bare `except:` reached without skipping a named handler is
## exact and stays a clean `sxSat`.
##
## VERDICTS FLIP in this slice, and only through the two fresh-symbol kinds:
## a dead target over a run whose only degrades are `feUnsupportedOpHavoc`
## / `heNewFieldZeroUnsupported` now reports `sxUnsat` (suite (b), each via
## `checkUnsatOverTaintOnly`). The guards in suite (c) pin that nothing
## else moved: a live target through a fresh symbol is a candidate
## (`sxUnknown`, never `sxSat`), substituted/halt/abort runs stay
## `sxUnknown`, and the unknown-exception repros no longer lie.
import std/[unittest, strutils, os, math]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import audit_scan_utils

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc severityOf(errs: seq[SymexErrorInfo]; k: SymexErrorKind): SymexErrorSeverity =
  for e in errs:
    if e.kind == k: return e.severity
  raiseAssert "no " & $k

const depthOne = block:
  var s = defaultSymexSettings()
  s.budget.maxHeapDepth = 1
  s

# =============================================================================
# SUTs
# =============================================================================

# ---- fresh: bool ordering -----------------------------------------------------

proc s6bBoolOrderDead(a, b: bool; n: int) =
  if a < b:
    discard
  if n == 5 and n == 6:
    symexTarget("s6b_bool_order_dead")

proc s6bBoolOrderLive(a, b: bool) =
  if a < b:
    symexTarget("s6b_bool_order_live")

proc s6bBoolOrderFresh(a: bool) =
  ## Two orderings over the same operand get two INDEPENDENT fresh symbols,
  ## so the walk knows nothing about their correlation (reality reaches the
  ## target at a=false). It must report a candidate, never a verdict.
  let x = a < true
  let y = a < false
  if x and not y:
    symexTarget("s6b_bool_order_fresh")

# ---- fresh: composite result through a callee --------------------------------

proc s6bMkSeq(n: int): seq[int] =
  result = @[n, n]

proc s6bRetSeq(n: int): seq[int] =
  return @[n]

proc s6bSeqResultDead(n: int) =
  let s = s6bMkSeq(n)
  discard s
  if n == 5 and n == 6:
    symexTarget("s6b_seq_result_dead")

proc s6bSeqResultLive(n: int) =
  let s = s6bMkSeq(n)
  if s.len == 3:
    symexTarget("s6b_seq_result_live")

proc s6bSeqReturnDead(n: int) =
  let s = s6bRetSeq(n)
  discard s
  if n == 5 and n == 6:
    symexTarget("s6b_seq_return_dead")

proc s6bSeqFresh(n: int) =
  let s1 = s6bRetSeq(n)
  let s2 = s6bMkSeq(n)
  if s1.len != s2.len:
    symexTarget("s6b_seq_fresh")

proc s6bMaybeFloat(n: int): float =
  if n > 0:
    result = 1.5

proc s6bFloatZeroDead(n: int) =
  let f = s6bMaybeFloat(n)
  discard f
  if n == 5 and n == 6:
    symexTarget("s6b_float_zero_dead")

# ---- fresh: iteSV string merge ------------------------------------------------

proc s6bStrIndexDead(i, n: int) =
  let arr = ["a", "b", "c"]
  if i >= 0 and i < 3:
    let s = arr[i]
    discard s
  if n == 5 and n == 6:
    symexTarget("s6b_str_index_dead")

proc s6bStrIndexLive(i: int) =
  let arr = ["a", "b", "c"]
  if i >= 0 and i < 3:
    if arr[i] == "zzz":
      symexTarget("s6b_str_index_live")

# ---- substituted: tuple equality by name ---------------------------------------

proc s6bTupleEqDead(a, b: (int, int); n: int) =
  if a == b:
    discard
  if n == 5 and n == 6:
    symexTarget("s6b_tuple_eq_dead")

# ---- no answer: the boundary abort ---------------------------------------------

proc s6bLn(x: float) =
  if ln(x) > 1.0:
    symexTarget("s6b_ln")

# ---- heNewFieldZeroUnsupported --------------------------------------------------

type S6bBox = ref object
  items: seq[int]
  v: int

proc s6bNewSeqFieldDead(n: int) =
  let b = S6bBox(v: n)
  discard b
  if n == 5 and n == 6:
    symexTarget("s6b_new_seq_field_dead")

proc s6bNewSeqFieldLive(n: int) =
  let b = S6bBox(v: n)
  if b.items.len > 0:
    symexTarget("s6b_new_seq_field_live")

# ---- halts --------------------------------------------------------------------

type S6bNode = ref object
  next: S6bNode
  v: int

proc s6bDeepDead(n: int) =
  let a = S6bNode(v: n)
  let b = S6bNode(next: a, v: 1)
  if b.next.v == 3:
    discard
  if n == 5 and n == 6:
    symexTarget("s6b_deep_dead")

proc s6bUnsafeCastDead(n: int) =
  var x = n
  let q = addr x
  discard q
  if n == 5 and n == 6:
    symexTarget("s6b_unsafe_cast_dead")

# ---- eeUnknownExnType -----------------------------------------------------------

proc s6bMkErr(): ref ValueError =
  newException(ValueError, "x")

proc s6bUnknownExnCaught(n: int) =
  try:
    if n > 0:
      raise s6bMkErr()
  except ValueError:
    symexTarget("s6b_unknown_exn_caught")

proc s6bUnknownExnBare(n: int) =
  try:
    if n > 0:
      raise s6bMkErr()
  except:
    symexTarget("s6b_unknown_exn_bare")

proc s6bUnknownExnFabricated(n: int) =
  try:
    try:
      if n > 0:
        raise s6bMkErr()
    except ValueError:
      discard
  except:
    symexTarget("s6b_unknown_exn_fabricated")

template show(r: untyped) =
  checkpoint($r.status & " " & $kindNames(r.errors))

# =============================================================================
# oracles
# =============================================================================

suite "RFC-0005 S6b -- oracles":

  test "oracle: n == 5 and n == 6 is a genuine contradiction":
    for n in [-1, 0, 5, 6, 7]:
      check not (n == 5 and n == 6)

  test "oracle: bool ordering is reachable (false < true)":
    check false < true
    check (false < true) and not (false < false)

  test "oracle: s6bMkSeq's length is 2 (the live target is really dead; the walk may only call it a candidate)":
    for n in [-3, 0, 3]:
      check s6bMkSeq(n).len == 2
      check s6bRetSeq(n).len == 1

  test "oracle: an object-constructed ref's untouched seq field is empty":
    check S6bBox(v: 3).items.len == 0

  test "oracle: a ValueError returned by a helper IS caught by except ValueError":
    var caught = false
    try:
      raise s6bMkErr()
    except ValueError:
      caught = true
    check caught

  test "oracle: the inner except ValueError swallows it; the outer bare except never runs":
    var outer = false
    try:
      try:
        raise s6bMkErr()
      except ValueError:
        discard
    except:
      outer = true
    check not outer

# =============================================================================
# (a) the classification: one word per kind, each derived from the site
# =============================================================================

const freshKinds = [feUnsupportedOpHavoc, heNewFieldZeroUnsupported]
const substKinds = [feUnsupportedOp, seByteIterUnsupported, eeUnknownExnType,
                    geInstantiationCapped, geDistinctBarrier, hePtrArith,
                    feOpaqueCallUnmodelled, feEnumOrdinalUnresolved,
                    feGlobalReadUnmodelled, feUnsupportedStmtKind,
                    weRecursionCycleCut]
const haltKinds = [heDepthExhausted, heUnsafeCast, weBreakOutsideLoop,
                   seVariantFieldOnDeclinedCtor, eeRaiseOutsideHandler,
                   eeHandlerReraiseUnmodelled]

suite "RFC-0005 S6b (a) -- classOf rows":

  test "feUnsupportedOpHavoc (fresh symbol, nothing dropped) is dcFreshSymbol: {scSpurious} on both":
    check classOf(feUnsupportedOpHavoc) == dcFreshSymbol
    check channels(feUnsupportedOpHavoc) == (path: {scSpurious}, run: {scSpurious})

  test "feUnsupportedOp (forwarded operand / dropped write, raise or fork) is dcSubstituted: ⊤ on both":
    check classOf(feUnsupportedOp) == dcSubstituted
    check channels(feUnsupportedOp) ==
      (path: {scSpurious, scIncomplete}, run: {scSpurious, scIncomplete})

  test "feUnsupportedOpAborted (the runSymex boundary abort) is dcNoAnswer":
    check classOf(feUnsupportedOpAborted) == dcNoAnswer

  test "heNewFieldZeroUnsupported (untouched cell at a fresh address) is dcFreshSymbol":
    check classOf(heNewFieldZeroUnsupported) == dcFreshSymbol

  test "every substituting kind is dcSubstituted":
    for k in substKinds:
      checkpoint($k)
      check classOf(k) == dcSubstituted

  test "every halt kind is dcOmitted: {} on the path, {scIncomplete} on the run":
    for k in haltKinds:
      checkpoint($k)
      check classOf(k) == dcOmitted
      check channels(k) == (path: {}, run: {scIncomplete})

  test "ONLY the fresh kinds can license sxUnsat":
    for k in freshKinds:
      check scIncomplete notin runTaint(classOf(k))
    for k in substKinds: check scIncomplete in runTaint(classOf(k))
    for k in haltKinds: check scIncomplete in runTaint(classOf(k))
    check scIncomplete in runTaint(classOf(feUnsupportedOpAborted))

  test "the splits are TAIL appends (ordinal stability, §3.2)":
    check ord(feUnsupportedOpHavoc) == ord(beBudgetExhaustedUnmodelled) + 1
    check ord(feUnsupportedOpAborted) == ord(feUnsupportedOpHavoc) + 1

  test "taintsRun: every sevError, plus the eeUnknownExnType warning -- no other warning or hint":
    check taintsRun(SymexErrorInfo(kind: feUnsupportedOp, severity: sevError, msg: "e"))
    check taintsRun(SymexErrorInfo(kind: eeUnknownExnType, severity: sevWarning, msg: "w"))
    check not taintsRun(SymexErrorInfo(kind: geDistinctBijectivitySkipped,
                                       severity: sevWarning, msg: "w"))
    check not taintsRun(SymexErrorInfo(kind: hePtrFamily, severity: sevHint, msg: "h"))
    check runTaintOf(@[SymexErrorInfo(kind: eeUnknownExnType, severity: sevWarning,
                                      msg: "w")]) == {scSpurious, scIncomplete}

  test "checkUnsatOverTaintOnly rejects every non-fresh S6b kind, the eeUnknownExnType WARNING included":
    for k in @substKinds & @haltKinds & @[feUnsupportedOpAborted]:
      checkpoint($k)
      let r = SymexResult[int](status: sxUnsat,
        errors: @[SymexErrorInfo(kind: k, severity: sevError, msg: "m")])
      expect AssertionDefect:
        checkUnsatOverTaintOnly(r)
    let w = SymexResult[int](status: sxUnsat,
      errors: @[SymexErrorInfo(kind: eeUnknownExnType, severity: sevWarning, msg: "w")])
    expect AssertionDefect:
      checkUnsatOverTaintOnly(w)

  test "checkUnsatOverTaintOnly admits the fresh kinds":
    for k in freshKinds:
      checkpoint($k)
      checkUnsatOverTaintOnly(SymexResult[int](status: sxUnsat,
        errors: @[SymexErrorInfo(kind: k, severity: sevError, msg: "m")]))

# =============================================================================
# (b) the payoff: a dead target over a fresh-only run is sxUnsat
# =============================================================================

suite "RFC-0005 S6b (b) -- fresh-symbol sites license sxUnsat":

  test "bool ordering: dead target is sxUnsat (feUnsupportedOpHavoc)":
    let r = symexFind(s6bBoolOrderDead, tLabel("s6b_bool_order_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    check not r.errors.hasKind(feUnsupportedOp)
    checkUnsatOverTaintOnly(r)

  test "composite result (implicit-result fallthrough): dead target is sxUnsat":
    let r = symexFind(s6bSeqResultDead, tLabel("s6b_seq_result_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    checkUnsatOverTaintOnly(r)

  test "composite result (explicit return): dead target is sxUnsat":
    let r = symexFind(s6bSeqReturnDead, tLabel("s6b_seq_return_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    checkUnsatOverTaintOnly(r)

  test "untouched result without a zero default: dead target is sxUnsat":
    let r = symexFind(s6bFloatZeroDead, tLabel("s6b_float_zero_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    checkUnsatOverTaintOnly(r)

  test "iteSV string merge (array index fold): dead target is sxUnsat":
    let r = symexFind(s6bStrIndexDead, tLabel("s6b_str_index_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    checkUnsatOverTaintOnly(r)

  test "heNewFieldZeroUnsupported: dead target is sxUnsat":
    let r = symexFind(s6bNewSeqFieldDead, tLabel("s6b_new_seq_field_dead"))
    show r
    check r.errors.hasKind(heNewFieldZeroUnsupported)
    checkUnsatOverTaintOnly(r)

# =============================================================================
# (c) guards: what must NOT flip
# =============================================================================

suite "RFC-0005 S6b (c) -- guards":

  test "a live target through a fresh bool ordering is a candidate: sxUnknown, never sxSat":
    let r = symexFind(s6bBoolOrderLive, tLabel("s6b_bool_order_live"))
    show r
    check r.status == sxUnknown

  test "two independent fresh orderings: a candidate, never sxUnsat (the introduction invariant)":
    ## RFC-0005 S10: the candidate is now REPLAYED (rule 3), and reality
    ## reaches the target (a=false: `false < true` and not `false < false`),
    ## so it reports sxSat -- never sxUnsat, and only via a confirmed replay
    ## (the path is tainted, so rules 1-2 decided sxUnknown).
    let r = symexFind(s6bBoolOrderFresh, tLabel("s6b_bool_order_fresh"))
    show r
    check r.status == sxSat
    check rfc0005UnvetoedStatus == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "a target decided only by the havoc retSym is a candidate: sxUnknown, never sxSat":
    let r = symexFind(s6bSeqResultLive, tLabel("s6b_seq_result_live"))
    show r
    check r.status == sxUnknown

  test "two havoc retSyms are independent: a candidate, confirmed by replay":
    ## Pre-S10 sxUnknown. RFC-0005 S10: reality reaches the target on every
    ## input (`@[n].len != @[n, n].len`), so the replayed candidate is
    ## confirmed -> sxSat, with rules 1-2 having decided sxUnknown.
    let r = symexFind(s6bSeqFresh, tLabel("s6b_seq_fresh"))
    show r
    check r.status == sxSat
    check rfc0005UnvetoedStatus == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "a target decided only by the merged string is a candidate: sxUnknown":
    let r = symexFind(s6bStrIndexLive, tLabel("s6b_str_index_live"))
    show r
    check r.status == sxUnknown

  test "an untouched new-ref seq field is a candidate: sxUnknown, never sxSat":
    let r = symexFind(s6bNewSeqFieldLive, tLabel("s6b_new_seq_field_live"))
    show r
    check r.errors.hasKind(heNewFieldZeroUnsupported)
    check r.status == sxUnknown

  test "substituted: tuple equality by name keeps feUnsupportedOp; a dead target stays sxUnknown":
    let r = symexFind(s6bTupleEqDead, tLabel("s6b_tuple_eq_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOp)
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    check r.status == sxUnknown

  test "no answer: the boundary abort records feUnsupportedOpAborted and is sxUnknown":
    let r = symexFind(s6bLn, tLabel("s6b_ln"))
    show r
    check r.errors.hasKind(feUnsupportedOpAborted)
    check not r.errors.hasKind(feUnsupportedOp)
    check r.status == sxUnknown

  test "halt: heap depth exhaustion keeps a dead target sxUnknown":
    let r = symexFind(s6bDeepDead, tLabel("s6b_deep_dead"), depthOne)
    show r
    check r.errors.hasKind(heDepthExhausted)
    check r.status == sxUnknown

  test "halt: an unsafe cast keeps a dead target sxUnknown":
    let r = symexFind(s6bUnsafeCastDead, tLabel("s6b_unsafe_cast_dead"))
    show r
    check r.errors.hasKind(heUnsafeCast)
    check r.status == sxUnknown

  test "unknown exception type: the skipped named handler's target is never sxUnsat (was a false sxUnsat)":
    let r = symexFind(s6bUnknownExnCaught, tLabel("s6b_unknown_exn_caught"))
    show r
    check r.errors.hasKind(eeUnknownExnType)
    check r.errors.severityOf(eeUnknownExnType) == sevWarning
    check r.status == sxUnknown

  test "unknown exception type: a bare except past a skipped named handler is never sxSat (was a false sxSat)":
    let r = symexFind(s6bUnknownExnFabricated, tLabel("s6b_unknown_exn_fabricated"))
    show r
    check r.errors.hasKind(eeUnknownExnType)
    check r.status == sxUnknown

  test "unknown exception type: a bare except reached WITHOUT a skipped handler is exact: clean sxSat":
    let r = symexFind(s6bUnknownExnBare, tLabel("s6b_unknown_exn_bare"))
    show r
    check r.errors.hasKind(eeUnknownExnType)
    check r.status == sxSat

# =============================================================================
# (d) structural: the site-audit table, pinned against the source
# =============================================================================

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

proc hasIdent(line, ident: string): bool =
  var i = line.find(ident)
  while i >= 0:
    let before = i == 0 or not isIdentChar(line[i - 1])
    let j = i + ident.len
    let after = j >= line.len or not isIdentChar(line[j])
    if before and after: return true
    i = line.find(ident, i + 1)
  false

proc codeLinesWith(path, ident: string): seq[string] =
  ## Non-comment lines naming `ident` as a whole identifier (message strings
  ## spell kinds as `(kind)`, which is excluded).
  for raw in readFile(path).splitLines():
    let t = raw.strip()
    if t.len == 0 or isCommentLine(t): continue
    if ("(" & ident & ")") in t: continue
    if t.hasIdent(ident): result.add t

proc runtimeFiles(): seq[string] =
  for f in walkFiles(smtDir / "runtime*.nim"): result.add f

suite "RFC-0005 S6b (d) -- structural: the audited emission sites":

  test "feUnsupportedOpHavoc sites match the S6b audit (a new site must re-audit its class)":
    ## reinterpret, uninterp merge, seq merge, string/table/set merge (the
    ## group arm's kind choice), closure-env conjunct x2, bool ordering, and
    ## the three composite call-result bindings. RFC-0005 S7 added the
    ## eleventh: `applyClosureGround`'s composite zero-default fallthrough
    ## (the per-occurrence closure result left free on that arm, recorded
    ## through `closureDegrade`; was `feUnsupportedOp` in the closure sink).
    var sites: seq[string]
    for f in runtimeFiles(): sites.add codeLinesWith(f, $feUnsupportedOpHavoc)
    checkpoint($sites)
    check sites.len == 11

  test "feUnsupportedOpAborted is emitted only at the runSymex boundary":
    var sites: seq[string]
    for f in runtimeFiles(): sites.add codeLinesWith(f, $feUnsupportedOpAborted)
    checkpoint($sites)
    check sites.len == 1

  test "eeUnknownExnType is recorded through the degrade funnel exactly once":
    var sites: seq[string]
    for f in runtimeFiles(): sites.add codeLinesWith(f, $eeUnknownExnType)
    checkpoint($sites)
    check sites.len == 1 and "w.degrade(eeUnknownExnType," in sites[0] and
      "dsUnknownExn" in sites[0]

  test "every dcOmitted kind's walker degrade is a HALT across runtime*.nim: token discarded":
    var omitted = 0
    for f in runtimeFiles():
      for raw in readFile(f).splitLines():
        let t = raw.strip()
        if t.len == 0 or isCommentLine(t): continue
        for k in SymexErrorKind:
          if classOf(k) != dcOmitted: continue
          if ("degrade(" & $k & ",") in t:
            inc omitted
            checkpoint(f & ": " & t)
            check t.startsWith("discard w.degrade(")
    check omitted >= 6

suite "RFC-0005 S6b -- walker version pin":

  test "walker version floor >= 145 (S6b classifies feUnsupportedOp and the halts)":
    check parseInt(symexWalkerVersion) >= 145
