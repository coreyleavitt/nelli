## RFC-0005 (soundness channels) slice S8n -- the precision remainder.
##
## Four places the walker (or the witness bridge) gave up on code whose
## behaviour is fully determined. Every expected value was probed against
## the real compiler (Nim 2.2.10, debug build) by the oracle test of each
## suite, which runs the SUT itself.
##   (1) a concolic `if` whose condition is a closure call that returns
##       normally is decided, not ambiguous;
##   (2) `renderAsChoices` (and so `assertCoveredBy`) accepts `ref` / `ptr`
##       witnesses;
##   (3) a callee reading `result` before writing it reads the zero value;
##   (4) a closure returning a variant object;
##   (5) the walker version floor.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/choice
import nelli/int128
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (1) concolic closure conditions -------------------------------------------
#
# Real Nim: `pred(7)` is true and `pred(2)` false, so the `if` takes its arm
# on x == 7 and skips it on x == 2, and `y > 3` is decided after it either
# way. Before S8n the closure's result was defined only by the ground
# closure axioms, which `concreteBranchOutcome`'s scratch solves never saw:
# the result was free, the decision ambiguous, and the walk stopped there.

proc concClosure(x, y: int) =
  let pred = proc (v: int): bool =
    if v == 0: return false
    v > 5
  if pred(x): symexTarget("s8n_conc_hi")
  if y > 3: symexTarget("s8n_conc_y")

proc concClosureInt(x: int) =
  let twice = proc (v: int): int = v * 2
  if twice(x) == 14: symexTarget("s8n_conc_int")

let concBindings2 = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                      ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]

suite "S8n (1) a concolic closure condition that returns is decided":
  test "oracle":
    symexCaptureBegin()
    concClosure(7, 5); concClosureInt(7)
    let hits = symexCaptureEnd()
    check "s8n_conc_hi" in hits
    check "s8n_conc_y" in hits
    check "s8n_conc_int" in hits

  test "a true closure condition takes its arm (was ambiguous)":
    let trace = @[integerChoice(7, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let r = concolicCollect(concClosure, trace, concBindings2)
    checkpoint("branchTrace.len=" & $r.branchTrace.len &
               " ambiguous=" & $r.counters.ambiguousBranches)
    for b in r.branchTrace: checkpoint("armTaken=" & $b.armTaken)
    check r.pcSatByConcreteInputs
    check r.counters.ambiguousBranches == 0
    # The closure body's `v == 0` (not taken), the outer `if` (taken), then
    # `y > 3` (taken).
    check r.branchTrace.len == 3
    if r.branchTrace.len == 3:
      check r.branchTrace[0].armTaken == -1
      check r.branchTrace[1].armTaken == 0
      check r.branchTrace[2].armTaken == 0

  test "a false closure condition skips its arm (was ambiguous)":
    let trace = @[integerChoice(2, -1000, 1000, 0), integerChoice(1, -1000, 1000, 0)]
    let r = concolicCollect(concClosure, trace, concBindings2)
    checkpoint("branchTrace.len=" & $r.branchTrace.len &
               " ambiguous=" & $r.counters.ambiguousBranches)
    check r.pcSatByConcreteInputs
    check r.counters.ambiguousBranches == 0
    check r.branchTrace.len == 3
    if r.branchTrace.len == 3:
      check r.branchTrace[1].armTaken == -1
      check r.branchTrace[2].armTaken == -1

  test "an int-valued closure result in a comparison is decided":
    let trace = @[integerChoice(7, -1000, 1000, 0)]
    let r = concolicCollect(concClosureInt, trace,
      @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)])
    checkpoint("branchTrace.len=" & $r.branchTrace.len &
               " ambiguous=" & $r.counters.ambiguousBranches)
    check r.pcSatByConcreteInputs
    check r.counters.ambiguousBranches == 0
    check r.branchTrace.len == 1
    if r.branchTrace.len == 1:
      check r.branchTrace[0].armTaken == 0

# ---- (2) renderAsChoices over ref / ptr witnesses --------------------------------
#
# Before S8n `renderAsChoices` had no `ref` / `ptr` arm, so a SUT with a ref
# parameter could not be passed to `assertCoveredBy` (nor run as a `symex`
# phase) at all: `{.error: "renderAsChoices: unsupported witness shape".}`
# at compile time. A ref renders as one integer tag, then its pointee:
#   0      nil
#   1      a cell not rendered before, followed by the pointee's choices
#   k + 2  the k-th cell already rendered (0-based, in rendering order):
#          an alias or a cycle, with nothing after it
# The tag's bounds are [0, 1 + cells rendered so far], so a tree-shaped
# witness is all 0 / 1 tags. Identity is kept, so the encoding is total over
# cyclic witnesses and two witnesses that differ only in aliasing render
# differently.

type
  S8nNode = ref object
    v: int
    next: S8nNode
  S8nObj = object
    a: int

proc tagOf(c: ChoiceNode): int64 =
  doAssert c.kind == ckInteger
  toInt64(c.intVal)

proc refParam(p: S8nNode; x: int) =
  if p != nil and p.v == x and x == 4: symexTarget("s8n_refparam")

proc ptrParam(p: ptr S8nObj; x: int) =
  if p != nil and p.a == x and x == 6: symexTarget("s8n_ptrparam")

suite "S8n (2) renderAsChoices over ref and ptr witnesses":
  test "nil renders as tag 0":
    let cs = renderAsChoices(S8nNode(nil))
    check cs.len == 1
    check tagOf(cs[0]) == 0

  test "a cell renders as tag 1 and its pointee's fields":
    let n = S8nNode(v: 7, next: nil)
    let cs = renderAsChoices(n)
    # [1, v=7, next: 0]
    check cs.len == 3
    check tagOf(cs[0]) == 1
    check tagOf(cs[1]) == 7
    check tagOf(cs[2]) == 0

  test "a cycle renders as a back-reference, not an endless walk":
    let n = S8nNode(v: 3)
    n.next = n
    let cs = renderAsChoices(n)
    # [1, v=3, next: back-reference to cell 0 = tag 2]
    check cs.len == 3
    check tagOf(cs[0]) == 1
    check tagOf(cs[1]) == 3
    check tagOf(cs[2]) == 2

  test "aliasing is kept: two params on one cell differ from two equal cells":
    let n = S8nNode(v: 5)
    let aliased = renderAsChoices((n, n))
    let distinct2 = renderAsChoices((n, S8nNode(v: 5)))
    # aliased: [1, 5, 0, 2]; distinct: [1, 5, 0, 1, 5, 0]
    check aliased.len == 4
    check tagOf(aliased[3]) == 2
    check distinct2.len == 6
    check tagOf(distinct2[3]) == 1

  test "rendering is deterministic":
    let n = S8nNode(v: 1, next: S8nNode(v: 2))
    let a = renderAsChoices(n)
    let b = renderAsChoices(n)
    check a.len == b.len
    for i in 0 ..< a.len: check tagOf(a[i]) == tagOf(b[i])

  test "a ptr renders like a ref":
    var o = S8nObj(a: 9)
    let cs = renderAsChoices(addr o)
    check cs.len == 2
    check tagOf(cs[0]) == 1
    check tagOf(cs[1]) == 9
    let np: ptr S8nObj = nil
    check renderAsChoices(np).len == 1

  test "assertCoveredBy accepts a ref-param SUT (was a compile-time error)":
    assertCoveredBy(refParam, tLabel("s8n_refparam"))
    assertCoveredBy(ptrParam, tLabel("s8n_ptrparam"))

# ---- (3) a callee reading `result` before writing it ---------------------------
#
# Real Nim zero-initialises `result` before the body runs: rrAdd(5) == 105,
# rrAdd(-3) == 100, rrFlag(false) is false. Before S8n the read of an unbound
# `result` was `feGlobalReadUnmodelled` on the caller.

proc rrAdd(x: int): int =
  ## `x < 1000` keeps `result += x` clear of OverflowDefect, which real Nim
  ## raises (and the walker reports) for `x` near `high(int)`.
  result += 100
  if x > 0 and x < 1000: result += x

proc rrFlag(b: bool): bool =
  if b: result = not result

proc resultRead(x: int) =
  let r = rrAdd(x)
  if r == 105: symexTarget("s8n_rr_sum")
  if r == 100 and x == -3: symexTarget("s8n_rr_base")
  if r < 100: symexTarget("s8n_rr_dead")

proc resultReadBool(b: bool) =
  if rrFlag(b): symexTarget("s8n_rrb_true")
  if rrFlag(b) and not b: symexTarget("s8n_rrb_dead")

proc resultReadClosure(x: int) =
  let f = proc (y: int): int =
    if y > 1000 or y < -1000: return   # no OverflowDefect below
    result += y
    result *= 2
  if f(x) == 10: symexTarget("s8n_rrc_ten")
  if f(x) mod 2 != 0: symexTarget("s8n_rrc_dead")

suite "S8n (3) a callee reading result before writing it reads zero":
  test "oracle":
    check rrAdd(5) == 105
    check rrAdd(-3) == 100
    check rrFlag(true)
    check not rrFlag(false)
    symexCaptureBegin()
    resultRead(5); resultRead(-3); resultReadBool(true); resultReadClosure(5)
    let hits = symexCaptureEnd()
    check "s8n_rr_sum" in hits
    check "s8n_rr_base" in hits
    check "s8n_rrb_true" in hits
    check "s8n_rrc_ten" in hits

  test "result += reads zero (was feGlobalReadUnmodelled)":
    let r = symexFind(resultRead, tLabel("s8n_rr_sum"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
      check reproduces(resultRead(r.witness[0]), "s8n_rr_sum")
    let b = symexFind(resultRead, tLabel("s8n_rr_base"))
    checkpoint($b.status & " " & show(b.errors))
    check b.status == sxSat
    let d = symexFind(resultRead, tLabel("s8n_rr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a bool result read before any write is false":
    let r = symexFind(resultReadBool, tLabel("s8n_rrb_true"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == true
    let d = symexFind(resultReadBool, tLabel("s8n_rrb_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a closure reading result before writing it":
    let r = symexFind(resultReadClosure, tLabel("s8n_rrc_ten"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(resultReadClosure, tLabel("s8n_rrc_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (4) a closure returning a variant -------------------------------------------
#
# Real Nim: g(7) is `S8nV(k: nvB, b: 7)`, g(-3) is `S8nV(k: nvA, a: 3)`, and
# the bare `return` of h leaves `result` zero-initialised: discriminator
# `nvA` (ordinal 0) and `a == 0`.

type
  S8nVK = enum nvA, nvB
  S8nV = object
    case k: S8nVK
    of nvA: a: int
    of nvB: b: int

proc closVariant(x: int) =
  let g = proc (y: int): S8nV =
    if y > 0:
      result = S8nV(k: nvB, b: y)
    elif y > -1000:   # `-y` of low(int) is an OverflowDefect in real Nim
      result = S8nV(k: nvA, a: -y)
    else:
      result = S8nV(k: nvA, a: 0)
  let v = g(x)
  if v.k == nvB and v.b == 7: symexTarget("s8n_closvar_b")
  if v.k == nvA and v.a == 3: symexTarget("s8n_closvar_a")
  if v.k == nvB and x <= 0: symexTarget("s8n_closvar_dead")

proc closVariantZero(x: int) =
  let h = proc (y: int): S8nV =
    if y > 0: return
    result = S8nV(k: nvB, b: 9)
  let v = h(x)
  if v.k == nvA and v.a == 0 and x == 1: symexTarget("s8n_closvar_zero")
  if v.k == nvB and x > 0: symexTarget("s8n_closvar_zero_dead")

suite "S8n (4) a closure returning a variant":
  test "oracle":
    symexCaptureBegin()
    closVariant(7); closVariant(-3); closVariantZero(1)
    let hits = symexCaptureEnd()
    check "s8n_closvar_b" in hits
    check "s8n_closvar_a" in hits
    check "s8n_closvar_zero" in hits

  test "the variant result reaches the caller (was seUnsupportedCompoundSortLeaf)":
    let r = symexFind(closVariant, tLabel("s8n_closvar_b"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
    let a = symexFind(closVariant, tLabel("s8n_closvar_a"))
    checkpoint($a.status & " " & show(a.errors))
    check a.status == sxSat
    if a.status == sxSat:
      check a.witness[0] == -3
    let d = symexFind(closVariant, tLabel("s8n_closvar_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a bare return yields the variant's zero value (was feUnsupportedOpHavoc)":
    let r = symexFind(closVariantZero, tLabel("s8n_closvar_zero"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    let d = symexFind(closVariantZero, tLabel("s8n_closvar_zero_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (5) walker version floor ---------------------------------------------------

suite "S8n (5) walker version":
  test "walker version is at least 162":
    check parseInt(symexWalkerVersion) >= 162
