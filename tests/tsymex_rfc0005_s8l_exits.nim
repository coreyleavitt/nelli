## RFC-0005 (soundness channels) slice S8l -- S8j's exit remainder.
## Walker 158 -> 159.
##
## S8j reported five defects whose mechanism lay outside its design. Each
## is a claim the real SUT contradicts. Every expected value was probed
## against the real compiler (Nim 2.2.10, debug build); the probe output is
## quoted beside the test, and where c and cpp disagree the test says so.
##   (1) `finally` runs on a `return` exit -- in a callee, at top level, from
##       an `except` arm -- with `result` already set; a raise inside the
##       `finally` replaces the return, nested `finally`s unwind innermost
##       first, and a `return` inside a `finally` overrides;
##   (2) `defer:` is the `finally` of the rest of its block;
##   (3) a named `ref object` case variant;
##   (4) variant reads through a named `ref` alias;
##   (5) an inline `ref` to a multi-variant object;
##   (6) the walker version floor.
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with `tsymex_rfc0005_s8l_exits_b`.
## Split so that each part compiles and runs in under 60 s on the Windows legs
## (the whole file took 60 s).
import std/[unittest, strutils, sequtils, sets]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (1) finally on a return exit --------------------------------------------
#
# Probe (c and cpp identical unless noted):
#   calleeFin(4)        -> the finally runs, and sees result == 4
#   finMod(4) == 5      -- `result = result + 1` in the finally is returned
#   finRaise(3)         -> ValueError "fin" (the finally's raise replaces the
#                          return); finRaise(2) == 2
#   nested(3) == 6      -- the inner finally runs first (result 3 -> 6), then
#                          the outer, which sees 6
#   retInFin(7) == 99   -- a return inside the finally overrides;
#   retInFin(2) == 2
#   retInExcept(0) == 5 -- a return from an `except` arm runs the finally,
#                          which sees result == 5
#   raiseInExcept(0)    -> KeyError, and the finally ran first
#   bareRet(4) == 4     -- a bare `return` runs the finally with the result
#                          assigned before it
#   `try: raise ValueError finally: return 7`: c re-raises ValueError, cpp
#   returns 7 -- the backends disagree (see the decline test below).

proc calleeFin(x: int): int =
  try:
    return x
  finally:
    symexTarget("s8l_cfin")

proc callsFin(x: int) =
  discard calleeFin(x)

proc calleeFinSees(x: int): int =
  try:
    return x
  finally:
    if result == 4: symexTarget("s8l_cfin_sees")

proc callsFinSees(x: int) =
  discard calleeFinSees(x)

proc finMod(x: int): int =
  try:
    return x
  finally:
    result = result + 1

proc callsFinMod(x: int) =
  if finMod(x) == 5: symexTarget("s8l_finmod")

proc callsFinModNot(x: int) =
  ## finMod(x) == x + 1 always: equality with x is impossible. (The guard
  ## keeps `high(int) + 1`'s OverflowDefect off the path.)
  if x < 1000 and finMod(x) == x: symexTarget("s8l_finmod_not")

proc finRaise(x: int): int =
  try:
    return x
  finally:
    if x == 3: raise newException(ValueError, "fin")

proc callsFinRaise(x: int) =
  try:
    discard finRaise(x)
  except ValueError:
    symexTarget("s8l_finraise")

proc callsFinRaiseRet(x: int) =
  ## On x == 3 the return is replaced by the raise: finRaise never returns 3.
  try:
    if finRaise(x) == 3: symexTarget("s8l_finraise_ret")
  except ValueError:
    discard

proc nestedFin(x: int): int =
  try:
    try:
      return x
    finally:
      result = result * 2
  finally:
    if result == 6: symexTarget("s8l_nested_outer")

proc callsNested(x: int) =
  if nestedFin(x) == 6: symexTarget("s8l_nested_ret")

proc retInFin(x: int): int =
  try:
    return x
  finally:
    if x > 5: return 99

proc callsRetInFin(x: int) =
  let r = retInFin(x)
  if r == 99: symexTarget("s8l_retinfin")
  if r == 7: symexTarget("s8l_retinfin_7")   # unreachable: 7 > 5 returns 99

proc retInExcept(x: int): int =
  try:
    if x == 0: raise newException(ValueError, "a")
    result = 1
  except ValueError:
    return 5
  finally:
    if result == 5: symexTarget("s8l_exfin")

proc callsRetInExcept(x: int) =
  discard retInExcept(x)

proc raiseInExcept(x: int) =
  try:
    if x == 0: raise newException(ValueError, "a")
  except ValueError:
    raise newException(KeyError, "k")
  finally:
    if x == 0: symexTarget("s8l_rexfin")   # reached only on the raising arm

proc bareRet(x: int): int =
  result = x
  try:
    if x > 0: return
    result = 3
  finally:
    if result == 4: symexTarget("s8l_bare_fin")

proc callsBareRet(x: int) =
  if bareRet(x) == 4: symexTarget("s8l_bare_ret")

# A bare `return` before `result` is assigned returns its zero value (Nim
# zero-initialises `result`; probed: bareZero(1) == 0, bareZero(0) == 5).
# The walker binds the callee's `retSym` to the return type's zero default
# there (`completeReturn`); before S8l that path left it free. A variant
# result has no modelled zero default, so the per-call `retSym` stays free
# on that path and the site records `feUnsupportedOpHavoc` (a fresh symbol
# ranging over the whole type, zero included -- RFC-0005 S6b's class).
proc bareZero(x: int): int =
  if x > 0: return
  result = 5

proc callsBareZero(x: int) =
  let r = bareZero(x)
  if x > 0 and r != 0: symexTarget("s8l_bare_zero_dead")
  if x > 0 and r == 0: symexTarget("s8l_bare_zero")

type
  BareVK = enum bvA, bvB
  BareV = object
    case k: BareVK
    of bvA: a: int
    of bvB: b: int

proc bareVariant(x: int): BareV =
  if x > 0: return
  result = BareV(k: bvB, b: 3)

proc callsBareVariant(x: int) =
  let v = bareVariant(x)
  discard v
  if x == 5 and x == 6: symexTarget("s8l_bare_variant_dead")

type
  BareMV = object
    ## Two `case` sections: a multi-variant with a `HashSet[string]` arm
    ## field (no backed cell sort), which has no modelled zero value.
    ## (RFC-0005 S8n gave single-case variants one, S8p multi-variants with
    ## an explicit ordinal-0 arm on every axis, S8s those whose ordinal 0
    ## falls in an `else` arm, S8u those with a `HashSet[int]` arm field,
    ## and S8z those with an enum field that has no ordinal 0, this pin's
    ## previous shape.)
    case k: BareVK
    of bvB: b: int
    else: a: HashSet[string]
    case j: BareVK
    of bvA: c: int
    of bvB: d: int

proc bareMultiVariant(x: int): BareMV =
  ## Never assigned: the pin is about the bare return alone.
  if x > 0: return

proc callsBareMultiVariant(x: int) =
  let v = bareMultiVariant(x)
  discard v
  if x == 5 and x == 6: symexTarget("s8l_bare_mv_dead")

# Top level: the SUT itself returns through its own finally.
proc topFin(x: int): int =
  try:
    return x * 2
  finally:
    if result == 10: symexTarget("s8l_topfin")

proc topFinRaise(x: int): int =
  try:
    return x
  finally:
    if x == 3: raise newException(ValueError, "topfin")

proc topFinBare(x: int) =
  try:
    if x > 0: return
  finally:
    if x == 9: symexTarget("s8l_topfin_bare")

proc retInRaisedFin(x: int): int =
  try:
    if x == 1: raise newException(ValueError, "a")
  finally:
    return 7

proc callsRetInRaisedFin(x: int) =
  try:
    if retInRaisedFin(x) == 7: symexTarget("s8l_raisedfin_ret")
  except ValueError:
    symexTarget("s8l_raisedfin_raise")

suite "S8l (1) finally runs on a return exit":
  test "oracle":
    check finMod(4) == 5
    expect ValueError:
      discard finRaise(3)
    check finRaise(2) == 2
    check nestedFin(3) == 6
    check retInFin(7) == 99 and retInFin(2) == 2
    check retInExcept(0) == 5
    expect KeyError:
      raiseInExcept(0)
    check bareRet(4) == 4
    expect ValueError:
      discard topFinRaise(3)

  test "a callee's finally runs on its return (was a false sxUnsat)":
    let r = symexFind(callsFin, tLabel("s8l_cfin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(callsFin(r.witness[0]), "s8l_cfin")

  test "the callee's finally sees the returned result":
    let r = symexFind(callsFinSees, tLabel("s8l_cfin_sees"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(callsFinSees(r.witness[0]), "s8l_cfin_sees")

  test "a finally's write to result is the returned value":
    let r = symexFind(callsFinMod, tLabel("s8l_finmod"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(callsFinMod(r.witness[0]), "s8l_finmod")
    let u = symexFind(callsFinModNot, tLabel("s8l_finmod_not"))
    checkpoint($u.status & " " & show(u.errors))
    check u.status == sxUnsat

  test "a raise in the finally replaces the return":
    let r = symexFind(callsFinRaise, tLabel("s8l_finraise"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(callsFinRaise(r.witness[0]), "s8l_finraise")
    let u = symexFind(callsFinRaiseRet, tLabel("s8l_finraise_ret"))
    checkpoint($u.status & " " & show(u.errors))
    check u.status == sxUnsat

  test "nested finallys unwind innermost first":
    let r = symexFind(nestedFin, tLabel("s8l_nested_outer"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces((discard nestedFin(r.witness[0])), "s8l_nested_outer")
    let c = symexFind(callsNested, tLabel("s8l_nested_ret"))
    checkpoint($c.status & " " & show(c.errors))
    check c.status == sxSat
    if c.status == sxSat:
      check c.witness[0] == 3

  test "a return inside the finally overrides":
    let r = symexFind(callsRetInFin, tLabel("s8l_retinfin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] > 5
      check reproduces(callsRetInFin(r.witness[0]), "s8l_retinfin")
    let u = symexFind(callsRetInFin, tLabel("s8l_retinfin_7"))
    checkpoint($u.status & " " & show(u.errors))
    check u.status == sxUnsat

  test "a return from an except arm runs the finally":
    let r = symexFind(callsRetInExcept, tLabel("s8l_exfin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(callsRetInExcept(r.witness[0]), "s8l_exfin")

  test "a raise from an except arm runs the finally":
    let r = symexFind(raiseInExcept, tLabel("s8l_rexfin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 0
    let k = symexFind(raiseInExcept, tRaisedExn("KeyError"))
    checkpoint($k.status & " " & show(k.errors))
    check k.status == sxRaised
    if k.status == sxRaised:
      check k.raisedWitness[0] == 0

  test "a bare return runs the finally with the assigned result":
    let r = symexFind(callsBareRet, tLabel("s8l_bare_fin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let c = symexFind(callsBareRet, tLabel("s8l_bare_ret"))
    checkpoint($c.status & " " & show(c.errors))
    check c.status == sxSat
    if c.status == sxSat:
      check c.witness[0] == 4

  test "a bare return before result is assigned returns the zero value":
    check bareZero(1) == 0
    check bareZero(0) == 5
    let r = symexFind(callsBareZero, tLabel("s8l_bare_zero"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(callsBareZero(r.witness[0]), "s8l_bare_zero")
    let d = symexFind(callsBareZero, tLabel("s8l_bare_zero_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a bare return of a variant returns its zero value (re-pinned by RFC-0005 S8n)":
    # S8l pinned `feUnsupportedOpHavoc` here: the variant had no modelled
    # zero value. Nim zero-initialises it (`k == bvA`, `a == 0`), which S8n
    # models, so the dead label is a clean sxUnsat.
    let r = symexFind(callsBareVariant, tLabel("s8l_bare_variant_dead"))
    checkpoint($r.status & " " & show(r.errors))
    check not r.errors.anyIt(it.kind == feUnsupportedOpHavoc)
    check r.status == sxUnsat

  test "a bare return of a result with no zero default is a fresh symbol (feUnsupportedOpHavoc)":
    ## RFC-0005 S8z: no type both allocates free without a decline of its
    ## own and lacks a modelled zero any more (S8z gave an enum with no
    ## ordinal 0 its zero, this pin's previous field; a `range` excluding
    ## 0 cannot be a result's untouched field in Nim). The remaining
    ## no-zero field, an unbacked `HashSet[string]`, allocates with its
    ## `seUnsupportedSetCharInterop` (dcNoAnswer), so the run is honestly
    ## sxUnknown: never the unsound sxUnsat, and no longer taint-only.
    let r = symexFind(callsBareMultiVariant, tLabel("s8l_bare_mv_dead"))
    checkpoint($r.status & " " & show(r.errors))
    check r.errors.anyIt(it.kind == feUnsupportedOpHavoc)
    check r.errors.anyIt(it.kind == seUnsupportedSetCharInterop)
    check r.status == sxUnknown

  test "top level: the finally sees the returned result (was sxUnknown feGlobalReadUnmodelled)":
    let r = symexFind(topFin, tLabel("s8l_topfin"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
      check reproduces((discard topFin(r.witness[0])), "s8l_topfin")

  test "top level: a raise in the finally replaces the return":
    let r = symexFind(topFinRaise, tRaisedExn("ValueError"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedWitness[0] == 3

  test "top level: a bare return runs the finally":
    let r = symexFind(topFinBare, tLabel("s8l_topfin_bare"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9

  test "a return inside a finally on a raised exit is a recorded decline (c and cpp disagree)":
    let r = symexFind(callsRetInRaisedFin, tLabel("s8l_raisedfin_raise"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    # The non-raising path returns 7 on both backends.
    let s = symexFind(callsRetInRaisedFin, tLabel("s8l_raisedfin_ret"))
    checkpoint($s.status & " " & show(s.errors))
    check s.status == sxSat
    if s.status == sxSat:
      check s.witness[0] != 1

# The concolic walker reads the top-level returned paths: the finally's
# decision is recorded on the trace. Real Nim: concFin(5, 1) returns 10 and
# the finally's `y > 0` decision is taken.

proc concFin(x, y: int): int =
  try:
    return x * 2
  finally:
    if y > 0: result = result + 1

suite "S8l (1b) the concolic walker runs the finally on a top-level return":
  test "oracle":
    check concFin(5, 1) == 11
    check concFin(5, 0) == 10

  test "the finally's decision is recorded":
    let trace = @[integerChoice(5, -1000, 1000, 0), integerChoice(1, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concFin, trace, bindings)
    checkpoint("branchTrace.len=" & $r.branchTrace.len)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

# ---- (2) defer ------------------------------------------------------------------
#
# Probe (c and cpp identical):
#   deferRet(4) == 8   -- the defer runs after the return and sees result == 8
#   deferRaise(4)      -> ValueError, and the defer ran first
#   deferMod(4) == 104 -- `defer: result = result + 100` is returned
#   twoDefers(1)       -- the later defer runs first ("d2", then "d1")

proc deferRet(x: int): int =
  defer:
    if result == 8: symexTarget("s8l_defer_ret")
  if x > 0: return x * 2
  result = 1

proc deferRaise(x: int) =
  defer:
    if x == 4: symexTarget("s8l_defer_raise")
  if x > 0: raise newException(ValueError, "d")

proc deferMod(x: int): int =
  defer: result = result + 100
  return x

proc callsDeferMod(x: int) =
  if deferMod(x) == 104: symexTarget("s8l_defer_mod")

proc twoDefers(x: int): int =
  defer: result = result * 2
  defer: result = result + 1
  return x

proc callsTwoDefers(x: int) =
  ## (x + 1) * 2 == 10 at x == 4; (x * 2) + 1 is odd, never 10.
  if twoDefers(x) == 10: symexTarget("s8l_two_defers")

proc deferEnd(x: int) =
  var y = x
  if y > 0:
    defer: y = y + 1
  if y == 6: symexTarget("s8l_defer_end")

suite "S8l (2) defer is the finally of the rest of its block":
  test "oracle":
    check deferRet(4) == 8
    expect ValueError:
      deferRaise(4)
    check deferMod(4) == 104
    check twoDefers(4) == 10

  test "a return under a defer runs it (was feUnsupportedStmtKind)":
    let r = symexFind(deferRet, tLabel("s8l_defer_ret"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces((discard deferRet(r.witness[0])), "s8l_defer_ret")

  test "a raise under a defer runs it":
    let r = symexFind(deferRaise, tLabel("s8l_defer_raise"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let e = symexFind(deferRaise, tRaisedExn("ValueError"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxRaised

  test "a defer's write to result is returned":
    let r = symexFind(callsDeferMod, tLabel("s8l_defer_mod"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4

  test "two defers run in reverse order":
    let r = symexFind(callsTwoDefers, tLabel("s8l_two_defers"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(callsTwoDefers(r.witness[0]), "s8l_two_defers")

  test "a defer at the end of its block runs at once":
    let r = symexFind(deferEnd, tLabel("s8l_defer_end"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] in [5, 6]
      check reproduces(deferEnd(r.witness[0]), "s8l_defer_end")

# ---- (3) a named `ref object` case variant -----------------------------------
#
# Before S8l `VB = ref object case ...` (and `VRef = ref VObj`, section 4)
# was classified as a VALUE variant with the `ref` erased: `p != nil` was a
# walker fault (weInternalWalkerFault, "composite prototype for integer
# literal kind=svVariant"), and its constructor a recorded decline. It is
# now the ADR-0013 heap variant an inline `ref VObj` already was.
#
# Probe:
#   wrong-arm read and write through the ref  -> FieldDefect
#   `p.k = bkB` on a `bkA` cell (a `new(VB)` one included) -> FieldDefect
#     "assignment to discriminant changes object branch"
#   `p.k = bkA` on a `bkA` cell                -> no raise
#   `VB(k: bkB, b: x)`                         -> no raise
#   `of cA, cC: a` : `p.a = 5; p.k = cC`       -> p.a == 5 (kept)
#   `new VB`                                   -> k == bkA, a == 0

type
  BK = enum bkA, bkB
  VB = ref object
    case k: BK
    of bkA: a: int
    of bkB: b: int
  CK = enum cA, cB, cC
  VC = ref object
    case k: CK
    of cA, cC: a: int
    of cB: b: int

  BoolV = ref object
    case on: bool
    of true: t: int
    of false: f: int

# ---- (5) an inline ref to a multi-variant object ------------------------------
#
# Every field access through an inline `ref MV` (two `case` axes) was a
# recorded decline (`heRefVariantUnsupported`, "Slice 4 deferred"), and an
# inline `ref MV` OBJECT FIELD was a Z3 sort error (its placeholder pointee
# and the full multi-variant named two `Ref_` sorts). Each axis is now a
# single-axis heap variant of its own (`runtime_heap.mvAxisView`): its own
# discriminator heap, its arm fields checked against it alone.
#
# Probe:
#   wrong-arm read on either axis                -> FieldDefect
#   `p.b = bkQ` on a `bkP` cell                   -> FieldDefect
#   `new(MV)`                                     -> a == akX, b == bkP, x == 0

type
  MAK = enum akX, akY
  MBK = enum bkP, bkQ
  MV = object
    id: int
    case a: MAK
    of akX: x: int
    of akY: y: int
    case b: MBK
    of bkP: pp: int
    of bkQ: qq: int
  MRef = ref MV
  MHolder = object
    m: ref MV
