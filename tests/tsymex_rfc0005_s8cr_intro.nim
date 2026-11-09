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
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cr_intro_b`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 64 s).

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
# RFC-0016 K10a-float: nothing introduces this kind any more. An out-of-range
# float -> int conversion is `ubFloatToIntRange`, a halt (see
# `tsymex_0016_k10af_float`), so there is no fresh value to take a free value.

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
