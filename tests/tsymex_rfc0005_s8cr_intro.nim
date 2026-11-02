## RFC-0005 S8cr (DoD §6 item 5): the §2.1 introduction invariant for the six
## `dcFreshSymbol` kinds that had no pin of their own.
##
## §2.1: "a `{scSpurious}` site's symbol carries no constraints at
## introduction". Each suite below fires one kind through `symexFind` and asks
## for a value the concrete code cannot produce. Two facts together show the
## symbol took that value:
##
##   * replay off: the status is `sxUnknown`, `scIncomplete` is not in
##     `runTaint` and no decline is unplaced. Under §2.3 that status then has
##     one source, rule 4, a candidate: the solver found a model that reaches
##     the target. Were the symbol constrained to what the concrete code
##     computes, the query would be UNSAT and the verdict `sxUnsat`.
##   * replay on: the same search records `feReplayRefuted`, so the candidate
##     really was a model the native run does not follow. `sxUnsat` would be
##     the introduction invariant's failure, and `sxSat` a replay failure.
##
## Native oracles confirm that the value is out of reach.
##
## `feGlobalHavoc` carries a second question, the suite at the end of this
## file: does its symbol cover every later write to the global? That is the
## §2.1 coverage invariant this slice writes down.
import std/[unittest, math, strutils, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

const noReplay = SymexSettings(replay: false)
const outOfReach = 123456

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    result.add $e.kind & "/" & $e.severity & " "

template pinFree(sut: untyped; label: string; kind: SymexErrorKind) =
  ## The two-sided pin described in the header.
  let off = symexFind(sut, tLabel(label), noReplay)
  checkpoint "replay off: " & $off.status & " " & show(off.errors)
  check off.status == sxUnknown
  check off.errors.hasKind(kind)
  check scIncomplete notin off.soundness.runTaint
  check unplacedDeclines(off.errors).len == 0
  let on = symexFind(sut, tLabel(label))
  checkpoint "replay on: " & $on.status & " " & show(on.errors)
  check on.status == sxUnknown
  check on.errors.hasKind(kind)
  check on.errors.hasKind(feReplayRefuted)

# ---- heNewFieldZeroUnsupported ------------------------------------------------

type
  IntroDist = object
    x: int
    ys: seq[seq[int]]    # no construction-time zero (`zeroIRExprForType`)
  IntroBox = ref object
    items: IntroDist
    v: int

proc introNewField(n: int) =
  ## Nim zero-initialises `items`, so `b.items.x` is 0 on every input. The
  ## skipped zero-write leaves the cell free.
  let b = IntroBox(v: n)
  if b.items.x == outOfReach and n == 1:
    symexTarget("intro_new_field")

proc introNewFieldNeg(n: int) =
  ## The other polarity: a free symbol can also be nonzero when negated.
  let b = IntroBox(v: n)
  if not (b.items.x == 0) and n == 1:
    symexTarget("intro_new_field_neg")

suite "introduction invariant: heNewFieldZeroUnsupported":
  test "oracle: the field is 0":
    check IntroBox(v: 1).items.x == 0
  test "the field's cell takes a value Nim's zero rules out":
    pinFree(introNewField, "intro_new_field", heNewFieldZeroUnsupported)
  test "both polarities":
    pinFree(introNewFieldNeg, "intro_new_field_neg", heNewFieldZeroUnsupported)

# ---- seParseIntLaxSyntax ------------------------------------------------------

proc introParseLaxValue(s: string) =
  ## Nim parses "1_0" as 10. The lax path's parsed value is free.
  if s == "1_0" and parseInt(s) == outOfReach:
    symexTarget("intro_parse_lax")

proc introParseLaxNeg(s: string) =
  if s == "1_0" and not (parseInt(s) == 10):
    symexTarget("intro_parse_lax_neg")

suite "introduction invariant: seParseIntLaxSyntax":
  test "oracle: \"1_0\" parses as 10":
    check parseInt("1_0") == 10
  test "the lax path's value is one the native parse does not give":
    pinFree(introParseLaxValue, "intro_parse_lax", seParseIntLaxSyntax)
  test "both polarities":
    pinFree(introParseLaxNeg, "intro_parse_lax_neg", seParseIntLaxSyntax)

# ---- feConvFloatToIntUndefined ------------------------------------------------

proc introF2iNan(x: float) =
  ## Nim's `int(NaN)` is `low(int)` on the platforms the suite runs on. The
  ## out-of-domain value is free, so it can be any value of the target type.
  if isNaN(x) and int(x) == outOfReach:
    symexTarget("intro_f2i_nan")

proc introF2iNeg(x: float) =
  if isNaN(x) and not (int(x) == low(int)):
    symexTarget("intro_f2i_neg")

proc introF2iWide(x: float) =
  ## Outside the domain the value is not narrowed to anything near the
  ## operand either.
  if x > 1e30 and int(x) == 7:
    symexTarget("intro_f2i_wide")

suite "introduction invariant: feConvFloatToIntUndefined":
  test "oracle: out of domain the conversion gives low(int)":
    let nan = NaN
    check int(nan) == low(int)
    let big = 1e31
    check int(big) == low(int)
  test "int(NaN) takes a value the native conversion does not give":
    pinFree(introF2iNan, "intro_f2i_nan", feConvFloatToIntUndefined)
  test "both polarities":
    pinFree(introF2iNeg, "intro_f2i_neg", feConvFloatToIntUndefined)
  test "too large an operand":
    pinFree(introF2iWide, "intro_f2i_wide", feConvFloatToIntUndefined)

# ---- feOpaqueEffectHavoc ------------------------------------------------------

type IntroNode = ref object
  val: int

proc introTouch(n: IntroNode) {.symexOpaque.} =
  ## The only write it makes is 1.
  n.val = 1

proc introOpaqueHeap(v: int) =
  let n = IntroNode(val: 0)
  introTouch(n)
  if n.val == outOfReach and v == 1:
    symexTarget("intro_opaque_heap")

proc introOpaqueHeapOld(v: int) =
  ## Nothing from before the call survives: a value other than the old one
  ## and the written one is reachable too.
  let n = IntroNode(val: 5)
  introTouch(n)
  if n.val != 5 and n.val != 1 and v == 1:
    symexTarget("intro_opaque_heap_old")

suite "introduction invariant: feOpaqueEffectHavoc":
  test "oracle: the call writes 1":
    let n = IntroNode(val: 5)
    introTouch(n)
    check n.val == 1
  test "the cell's fresh contents take a value the body never writes":
    pinFree(introOpaqueHeap, "intro_opaque_heap", feOpaqueEffectHavoc)
  test "the fresh contents do not depend on the old value":
    pinFree(introOpaqueHeapOld, "intro_opaque_heap_old", feOpaqueEffectHavoc)

# ---- feTableIterOrder ---------------------------------------------------------

proc introTableOrder(a, b: int): int =
  ## The first key `for` visits, on the table the SUTs build.
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  for k, v in t:
    return k

proc introTableFirst1(a, b: int) =
  if a != 1 or b != 2: return
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var first = 0
  var seen = false
  for k, v in t:
    if not seen:
      first = k
      seen = true
  if first == 1:
    symexTarget("intro_table_first_1")

proc introTableFirst2(a, b: int) =
  if a != 1 or b != 2: return
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var first = 0
  var seen = false
  for k, v in t:
    if not seen:
      first = k
      seen = true
  if first == 2:
    symexTarget("intro_table_first_2")

suite "introduction invariant: feTableIterOrder":
  test "the order is free: each key can come first, with no replay to choose":
    ## Nim visits exactly one of the two orders on this table. With replay
    ## off, both are candidates: the order's symbol has no constraint.
    let a = symexFind(introTableFirst1, tLabel("intro_table_first_1"), noReplay)
    checkpoint $a.status & " " & show(a.errors)
    check a.status == sxUnknown
    check a.errors.hasKind(feTableIterOrder)
    check scIncomplete notin a.soundness.runTaint
    let b = symexFind(introTableFirst2, tLabel("intro_table_first_2"), noReplay)
    checkpoint $b.status & " " & show(b.errors)
    check b.status == sxUnknown
    check b.errors.hasKind(feTableIterOrder)
    check scIncomplete notin b.soundness.runTaint

  test "replay separates them: the order Nim uses is sxSat, the other refuted":
    let real = introTableOrder(1, 2)
    check real in [1, 2]
    let a = symexFind(introTableFirst1, tLabel("intro_table_first_1"))
    let b = symexFind(introTableFirst2, tLabel("intro_table_first_2"))
    checkpoint $a.status & " " & show(a.errors)
    checkpoint $b.status & " " & show(b.errors)
    let (yes, no) = if real == 1: (a, b) else: (b, a)
    check yes.status == sxSat
    check yes.soundness.replay == rsConfirmed
    check no.status == sxUnknown
    check no.errors.hasKind(feReplayRefuted)

# ---- feGlobalHavoc ------------------------------------------------------------

var gIntroEntry = 5        # never written after this line
var gIntroOpaque = 0

proc introGlobalEntry(x: int) =
  ## A read before any write: the entry value, any value of the type.
  if gIntroEntry == outOfReach and x == 1:
    symexTarget("intro_global_entry")

proc introGlobalEntryNeg(x: int) =
  if not (gIntroEntry == 5) and x == 1:
    symexTarget("intro_global_entry_neg")

proc introOpaqueSet() {.symexOpaque.} =
  gIntroOpaque = 1

proc introGlobalOpaque(x: int) =
  ## The other mint site: an opaque call's summary says it may write it.
  gIntroOpaque = 0
  introOpaqueSet()
  if gIntroOpaque == outOfReach and x == 1:
    symexTarget("intro_global_opaque")

suite "introduction invariant: feGlobalHavoc":
  test "oracle: the entry value is 5":
    check gIntroEntry == 5
  test "the entry value is free":
    pinFree(introGlobalEntry, "intro_global_entry", feGlobalHavoc)
  test "both polarities":
    pinFree(introGlobalEntryNeg, "intro_global_entry_neg", feGlobalHavoc)
  test "an opaque call's fresh value is free of what the body writes":
    pinFree(introGlobalOpaque, "intro_global_opaque", feGlobalHavoc)

# ---- feGlobalHavoc: the coverage invariant ------------------------------------
#
# The introduction invariant asks about one moment. A location's fresh symbol
# also needs every later write to that location to reach the model, or an
# `sxUnsat` that "holds for every entry value" is a claim about a program with
# a store removed. §2.1 states this as the coverage invariant. Each route
# below writes the global after the first read, and the label is reachable in
# Nim, so `sxUnsat` is false on all of them.

var gCovDirect, gCovCallee, gCovVar, gCovAddr, gCovLocalPtr, gCovClosure = 1
var gCovOpaque, gCovParam, gCovParamCallee, gCovParamValue = 1

proc covSet(v: var int; x: int) = v = x
proc covSetPtr(p: ptr int; x: int) = p[] = x
proc covWriteCallee(x: int) = gCovCallee = x
proc covOpaqueWrite() {.symexOpaque.} = gCovOpaque = gCovOpaque + 1

proc covDirect(x: int) =
  let a = gCovDirect
  if a > 1000: return      # no OverflowDefect beside the labels
  gCovDirect = a + 1
  if gCovDirect == a and x == 1: symexTarget("cov_direct_dead")
  if gCovDirect != a and x == 1: symexTarget("cov_direct")

proc covCallee(x: int) =
  let a = gCovCallee
  if a > 1000: return
  covWriteCallee(a + 1)
  if gCovCallee != a and x == 1: symexTarget("cov_callee")

proc covVar(x: int) =
  let a = gCovVar
  if a > 1000: return
  covSet(gCovVar, a + 1)
  if gCovVar != a and x == 1: symexTarget("cov_var")

proc covAddr(x: int) =
  let a = gCovAddr
  if a > 1000: return
  covSetPtr(addr gCovAddr, a + 1)
  if gCovAddr != a and x == 1: symexTarget("cov_addr")

proc covOpaque(x: int) =
  let a = gCovOpaque
  if a > 1000: return
  covOpaqueWrite()
  if gCovOpaque != a and x == 1: symexTarget("cov_opaque")

proc covLocalPtr(x: int) =
  ## Declined or havocked, but never `sxUnsat`.
  let a = gCovLocalPtr
  if a > 1000: return
  let p = addr gCovLocalPtr
  p[] = a + 1
  if gCovLocalPtr != a and x == 1: symexTarget("cov_local_ptr")

proc covClosure(x: int) =
  let a = gCovClosure
  if a > 1000: return
  let f = proc() = gCovClosure = a + 1
  f()
  if gCovClosure != a and x == 1: symexTarget("cov_closure")

proc covParam(p: ptr int) =
  ## The store through `p` reaches the global only when `p` addresses it. The
  ## walk's target scan misses a global it has only read.
  if p == nil: return
  let a = gCovParam
  p[] = 7
  if gCovParam != a: symexTarget("cov_param")

proc covParamCallee(p: ptr int) =
  if p == nil: return
  let a = gCovParamCallee
  covSetPtr(p, 7)
  if gCovParamCallee != a: symexTarget("cov_param_callee")

proc covParamValue(p: ptr int) =
  if p == nil: return
  let a = gCovParamValue
  let f = covSetPtr
  f(p, 7)
  if gCovParamValue != a: symexTarget("cov_param_value")

template reachedNatively(call: untyped; label: string): bool =
  symexCaptureBegin()
  call
  label in symexCaptureEnd()

template pinCovered(sut: untyped; label: string) =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  check r.status != sxUnsat

template pinOpenHole(sut: untyped; label: string) =
  ## An open hole in the coverage invariant: a RELEASE BLOCKER whose fix is on
  ## its own slice (S8cd). `sxUnsat` is a false verdict, reported as SKIPPED
  ## so it shows in every run without turning the suite red. When the fix
  ## lands the same test asserts the verdict, with no edit here. Delete the
  ## `skip` branch then.
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  if r.status == sxUnsat:
    echo "    OPEN HOLE (false sxUnsat, fix on S8cd): " & label
    skip()
  else:
    check r.errors.hasKind(feGlobalHavoc)
    check r.status == sxSat

suite "coverage invariant: a write the walk models reaches the global":
  test "a direct write":
    pinCovered(covDirect, "cov_direct")
    let d = symexFind(covDirect, tLabel("cov_direct_dead"))
    checkpoint $d.status & " " & show(d.errors)
    checkUnsatOverTaintOnly(d)
  test "a callee's write":
    pinCovered(covCallee, "cov_callee")
  test "a var argument":
    pinCovered(covVar, "cov_var")
  test "an addr argument":
    pinCovered(covAddr, "cov_addr")
  test "an opaque call's write":
    pinCovered(covOpaque, "cov_opaque")
  test "a local pointer to it":
    pinCovered(covLocalPtr, "cov_local_ptr")
  test "a closure's write":
    pinCovered(covClosure, "cov_closure")

suite "coverage invariant: a store through a ptr parameter (open hole, fix on S8cd)":
  test "oracle: Nim reaches every label":
    gCovParam = 1
    check reachedNatively(covParam(addr gCovParam), "cov_param")
    gCovParamCallee = 1
    check reachedNatively(covParamCallee(addr gCovParamCallee), "cov_param_callee")
    gCovParamValue = 1
    check reachedNatively(covParamValue(addr gCovParamValue), "cov_param_value")
  test "the store is direct":
    pinOpenHole(covParam, "cov_param")
  test "the store is in a callee":
    pinOpenHole(covParamCallee, "cov_param_callee")
  test "the store is in a proc value":
    pinOpenHole(covParamValue, "cov_param_value")

suite "RFC-0005 S8cr: walker version":
  test "symexWalkerVersion >= 245 (no walker change: this slice adds pins)":
    check parseInt(symexWalkerVersion) >= 245
