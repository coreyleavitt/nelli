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
import std/[unittest, strutils, os, math, sets, tables]
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
#
# RFC-0005 S8p binds a `seq` result (`retBindEq`'s svSeq arm), S8s an
# `array` one and S8u a `Table`, `HashSet`, `ref` or `ptr` one: every kind a
# callee can return through the composite-result site now binds, so these
# pins check the bound result (exact verdicts, no errors). The free-retSym
# guards in (c) moved to the untouched-result site (`s6bMaybeVariant`, a
# type with no modelled zero). A callee returning a closure faults before
# reaching the site (`allocateSym(itUninterp)`, reported by S8u).

proc s6bMkTab(t: Table[string, int]): Table[string, int] =
  result = t

proc s6bRetTab(t: Table[string, int]): Table[string, int] =
  return t

proc s6bTabResultDead(t: Table[string, int]; n: int) =
  let s = s6bMkTab(t)
  discard s
  if n == 5 and n == 6:
    symexTarget("s6b_seq_result_dead")

proc s6bTabResultLive(t: Table[string, int]; n: int) =
  ## Real Nim: s.len == t.len always; only the free retSym separates them.
  let s = s6bMkTab(t)
  if s.len != t.len:
    symexTarget("s6b_seq_result_live")

proc s6bTabReturnDead(t: Table[string, int]; n: int) =
  let s = s6bRetTab(t)
  discard s
  if n == 5 and n == 6:
    symexTarget("s6b_seq_return_dead")

proc s6bTabFresh(t: Table[string, int]; n: int) =
  ## Real Nim: s1.len == s2.len == t.len, so s1.len != s2.len + 1 on every
  ## input.
  let s1 = s6bRetTab(t)
  let s2 = s6bMkTab(t)
  if s1.len != s2.len + 1:
    symexTarget("s6b_seq_fresh")

type
  S6bVK = enum s6bA, s6bB
  S6bV = object
    ## Two `case` sections: a multi-variant. RFC-0005 S8n gave the
    ## single-case variant its zero value, S8p the multi-variant with an
    ## explicit ordinal-0 arm on every axis and S8s one whose ordinal 0
    ## falls in an `else` arm, so this site needs a type that still has
    ## none: a `HashSet[string]` arm field, whose element has no backed
    ## cell sort (a `HashSet[int]` field until RFC-0005 S8u gave the empty
    ## set as its zero; an enum field with no ordinal 0 until S8z modelled
    ## its zero memory, ordinal 0).
    case k: S6bVK
    of s6bB: b: int
    else: a: HashSet[string]
    case j: S6bVK
    of s6bA: c: int
    of s6bB: d: int

proc s6bMaybeVariant(n: int): S6bV =
  ## RFC-0005 S8f: a multi-variant result has no modelled zero default (a
  ## `float` one did until walker 154 gave `defaultZero` its float arm, a
  ## single-case variant until S8n, a multi-variant with an explicit
  ## ordinal-0 arm on every axis until S8p). Never assigned: the pin is
  ## about the untouched path alone.
  discard n

proc s6bMaybeVariantLive(n: int) =
  ## RFC-0005 S8u (was over a free `Table` retSym). Real Nim: the untouched
  ## result's `k` is its zero, `s6bA`, so the target is never reached; only
  ## the free retSym separates them.
  let f = s6bMaybeVariant(n)
  if f.k == s6bB:
    symexTarget("s6b_seq_result_live")

proc s6bMaybeVariantFresh(n: int) =
  ## RFC-0005 S8u (was over two free `Table` retSyms). Real Nim: both
  ## results are the zero value, so `f.k == g.k` on every input.
  let f = s6bMaybeVariant(n)
  let g = s6bMaybeVariant(n)
  if f.k == g.k:
    symexTarget("s6b_seq_fresh")

proc s6bFloatZeroDead(n: int) =
  let f = s6bMaybeVariant(n)
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

type S6bDist = object
  ## RFC-0005 S8at: an object with a `seq[(int, int)]` part, which no
  ## heap cell holds (a seq of tuples is backed nowhere, a stated
  ## decline). The by-value case object this was (S8ar) is a cell
  ## value since S8at. RFC-0005 S8bc: a seq of tuples is backed now, so
  ## the part is a `seq[seq[int]]`.
  x: int
  ys: seq[seq[int]]  # RFC-0005 S8bc: a seq of seqs (a seq of tuples is backed since S8bc)
type S6bBox = ref object
  ## RFC-0005 S8ap: `items` was a `seq[int]`, which a constructor now
  ## zero-writes (a leaf-split heap cell). RFC-0005 S8at zeroes a by-value
  ## case object too; an object with a seq-of-tuples part has no
  ## construction-time zero (`zeroIRExprForType`), so it keeps these pins on
  ## `heNewFieldZeroUnsupported`.
  items: S6bDist
  v: int

proc s6bNewSeqFieldDead(n: int) =
  let b = S6bBox(v: n)
  discard b
  if n == 5 and n == 6:
    symexTarget("s6b_new_seq_field_dead")

proc s6bNewSeqFieldLive(n: int) =
  let b = S6bBox(v: n)
  if b.items.x > 0:
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

  test "oracle: s6bMkTab keeps the table's length (the live target is really dead; the walk may only call it a candidate)":
    var t = initTable[string, int]()
    for n in [-3, 0, 3]:
      t[$n] = n
      check s6bMkTab(t).len == t.len
      check s6bRetTab(t).len != s6bMkTab(t).len + 1

  test "oracle: an object-constructed ref's untouched distinct field is zero":
    check S6bBox(v: 3).items.x == 0

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
# RFC-0005 S8c: `hePtrArith` left `substKinds` -- retired, its only producer
# keyed on a user-only `inc(ptr)` overload.
const substKinds = [feUnsupportedOp, seByteIterUnsupported, eeUnknownExnType,
                    geInstantiationCapped, geDistinctBarrier,
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

  test "composite result (implicit-result fallthrough): a Table result is bound, the dead target exactly sxUnsat (RFC-0005 S8u)":
    let r = symexFind(s6bTabResultDead, tLabel("s6b_seq_result_dead"))
    show r
    check r.status == sxUnsat
    check r.errors.len == 0

  test "composite result (explicit return): a Table result is bound, the dead target exactly sxUnsat (RFC-0005 S8u)":
    let r = symexFind(s6bTabReturnDead, tLabel("s6b_seq_return_dead"))
    show r
    check r.status == sxUnsat
    check r.errors.len == 0

  test "untouched result without a zero default: the free retSym declines, never sxSat":
    ## RFC-0005 S8z: no type both allocates free without a decline of its
    ## own and lacks a modelled zero any more (S8z gave an enum with no
    ## ordinal 0 its zero, this pin's previous field; a `range` excluding
    ## 0 cannot be a result's untouched field in Nim). The remaining
    ## no-zero field, an unbacked `HashSet[string]`, allocates with its
    ## `seUnsupportedSetCharInterop` (dcNoAnswer), so the run is honestly
    ## sxUnknown: never the unsound sxUnsat, and no longer taint-only.
    let r = symexFind(s6bFloatZeroDead, tLabel("s6b_float_zero_dead"))
    show r
    check r.errors.hasKind(feUnsupportedOpHavoc)
    check r.errors.hasKind(seUnsupportedSetCharInterop)
    check r.status == sxUnknown

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
    check rfc0005RawStatus == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "a target decided only by the havoc retSym is a candidate: sxUnknown, never sxSat":
    ## RFC-0005 S8u: over the untouched result with no modelled zero (a
    ## bound `Table` result is exact: `s.len != t.len` is sxUnsat, below).
    let r = symexFind(s6bMaybeVariantLive, tLabel("s6b_seq_result_live"))
    show r
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "a bound Table result decides its own target: sxUnsat (RFC-0005 S8u)":
    let r = symexFind(s6bTabResultLive, tLabel("s6b_seq_result_live"))
    show r
    check r.status == sxUnsat
    check r.errors.len == 0

  test "two havoc retSyms are independent: a candidate, never sxUnsat":
    ## Pre-S10 sxUnknown. RFC-0005 S10: reality reaches the target on every
    ## input (`n != n + 1`), so the replayed candidate is
    ## confirmed -> sxSat, with rules 1-2 having decided sxUnknown.
    ## (RFC-0005 S8p/S8s: over `Table` results; a `seq` and an `array`
    ## result are bound. S8u binds a `Table` too, so this is over two
    ## untouched results with no modelled zero.)
    ## RFC-0005 S8z: no type both allocates free without a decline of its
    ## own and lacks a modelled zero any more (S8z gave an enum with no
    ## ordinal 0 its zero, this pin's previous field; a `range` excluding
    ## 0 cannot be a result's untouched field in Nim). The remaining
    ## no-zero field, an unbacked `HashSet[string]`, allocates with its
    ## `seUnsupportedSetCharInterop` (dcNoAnswer), so the replay is not
    ## reached: an honest sxUnknown, never sxUnsat.
    let r = symexFind(s6bMaybeVariantFresh, tLabel("s6b_seq_fresh"))
    show r
    check r.status == sxUnknown
    check rfc0005RawStatus == sxUnknown
    check r.errors.hasKind(feUnsupportedOpHavoc)

  test "two bound Table results agree: exact sxSat (RFC-0005 S8u)":
    let r = symexFind(s6bTabFresh, tLabel("s6b_seq_fresh"))
    show r
    check r.status == sxSat
    check rfc0005RawStatus == sxSat
    check r.errors.len == 0

  test "a target decided only by the merged string is a candidate: sxUnknown":
    let r = symexFind(s6bStrIndexLive, tLabel("s6b_str_index_live"))
    show r
    check r.status == sxUnknown

  test "an untouched new-ref distinct field (a seq one until RFC-0005 S8ap) is a candidate: sxUnknown, never sxSat":
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
    ## RFC-0005 S8l added the twelfth: `completeReturn`'s bare `return` of
    ## an untouched result with no zero default (the per-call `retSym` left
    ## free, a superset of the zero value Nim returns -- the fresh class of
    ## the `isCall` arm's untouched-result twin; pinned sxUnsat-licensing in
    ## `tsymex_rfc0005_s8l_exits.nim`). The composite-return site moved
    ## from the `isReturn` arm into `completeReturn` unchanged. RFC-0005 S8u
    ## added the thirteenth and fourteenth, both fresh: `lower`'s
    ## `iekZeroValue` arm for a type with no modelled zero (a fresh value of
    ## the type, a superset of Nim's `default(T)`), and `retBindEq`'s
    ## kind-mismatch backstop (was a raise; `retSym` left free). The
    ## call-return drains now also take a kind mismatch
    ## (`retBindKindsAgree`) through their existing site. RFC-0005 S8aa
    ## removed the first: an Int-sorted same-width reinterpret is modelled
    ## (`lowerConvIntReinterpret` reduces into the target window), so 13.
    var sites: seq[string]
    for f in runtimeFiles(): sites.add codeLinesWith(f, $feUnsupportedOpHavoc)
    checkpoint($sites)
    check sites.len == 13

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
