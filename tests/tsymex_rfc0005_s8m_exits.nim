## RFC-0005 (soundness channels) slice S8m -- S8l's remainder.
## Walker 159 -> 160.
##
## S8l reported six defects whose mechanism lay outside its design. Each is a
## claim the real SUT contradicts, or a verdict no check stands behind. Every
## expected value was probed against the real compiler (Nim 2.2.10, debug
## build); the probe output is quoted beside the test, and where c and cpp
## disagree the test says so.
##   (1) `break` / `continue` leave through every enclosing `finally` (and
##       `defer`) innermost first; a labelled `break` leaves its `block`;
##       `continue` in a `for` loop still advances it;
##   (2) a Z3 sort mismatch is a recorded walker fault (`sxUnknown`), never a
##       silent verdict;
##   (3) a `ref` local assigned from a param, and a same-type `cast`, keep
##       the pointer's heap identity;
##   (4) an uninitialised `var p: ref T` local is nil;
##   (5) a closure's bare `return` returns the zero value;
##   (6) the walker version floor.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

const loopK = SymexSettings(budget: ResourceBudget(maxLoopUnwind: 3))
  ## Every loop below runs at most three times. The k-unroll forks the exit
  ## and the body on every iteration without a feasibility check, so nested
  ## loops grow as a power of the bound; 3 covers every trip count here.

proc deadModuloUnroll[T](r: SymexResult[T]): bool =
  ## A label past a loop is never `sxSat` when it is dead. The k-unroll has
  ## no per-iteration feasibility check, so the infeasible "guard still
  ## true" paths taint the run with `beBudgetExhausted` and the honest
  ## verdict is `sxUnknown` for that reason alone -- any other recorded kind
  ## would be a decline this slice did not mean to leave.
  if r.status == sxUnsat: return true
  if r.status != sxUnknown: return false
  for e in r.errors:
    if e.kind != beBudgetExhausted: return false
  true

# ---- (1) break / continue through finally; labelled blocks ------------------
#
# Probe (c and cpp identical unless noted):
#   `for i in 0..1: (try: (if i < 5: continue) finally: echo i)` prints 0, 1
#   a `break` out of a `try` in a `while` runs the `finally` first
#   nested finallys on a `continue`: the inner runs first, then the outer
#   `block outer: (try: break outer finally: echo "fin"); echo "unreached"`
#     prints "fin" and never "unreached"
#   `break inner` of a `block inner:` inside a loop leaves only the block
#   `break outer` out of two nested `for`s leaves both
#   `defer` in a loop body runs on `continue`
#   a `break` from an `except` arm, raised inside an inner loop, leaves the
#     OUTER loop (the one enclosing the `try`)
#   `for i in 0..2: (try: return 5 finally: break); result += 100` == 105:
#     a `break` in the finally cancels the return
#   `for i in 0..1: (try: raise ValueError finally: break)`: c re-raises the
#     ValueError, cpp swallows it and continues after the loop; a `continue`
#     there overflows the call depth under c. The backends disagree.
#   `for v in [1, 2, 3]: (if v == x: break)` leaves the unrolled loop

proc contFor(x: int) =
  for i in 0..1:
    try:
      if i < 5: continue
    finally:
      if i == 1 and x == 3: symexTarget("s8m_contfor")

proc contForPlain(x: int) =
  ## `continue` must still advance `i`: the walker used to skip the loop's
  ## increment and replay `i == 0` until the unroll bound.
  for i in 0..2:
    if i == 0: continue
    if i == 2 and x == 1: symexTarget("s8m_contfor_plain")

proc contSeq(s: seq[int]; x: int) =
  for v in s:
    if v < 0: continue
    if v == x and x == 4: symexTarget("s8m_contseq")

proc brkWhile(x: int) =
  var i = 0
  while i < 3:
    inc i
    try:
      if i == 2: break
    finally:
      if i == 2 and x == 4: symexTarget("s8m_brkwhile")

proc brkWhileAfter(x: int) =
  ## After the break, `i` is 2: the loop never reached 3.
  var i = 0
  while i < 3:
    inc i
    try:
      if i == 2: break
    finally:
      discard
  if i == 3 and x == 1: symexTarget("s8m_brkwhile_dead")
  if i == 2 and x == 1: symexTarget("s8m_brkwhile_after")

proc nestedCont(x: int) =
  var i = 0
  var log = 0
  while i < 1:
    inc i
    try:
      try:
        if x > 0: continue
      finally:
        log = log * 10 + 1
    finally:
      log = log * 10 + 2
  if log == 12 and x == 5: symexTarget("s8m_nested_cont")
  if log == 21: symexTarget("s8m_nested_cont_dead")

proc blkBreak(x: int) =
  block outer:
    try:
      if x > 0: break outer
    finally:
      if x == 7: symexTarget("s8m_blkbreak")
    if x > 0: symexTarget("s8m_blkbreak_dead")

proc blkInner(x: int) =
  var i = 0
  while i < 2:
    inc i
    block inner:
      if x > 0: break inner
    if i == 2 and x == 1: symexTarget("s8m_blkinner")

proc lblOuter(x: int) =
  block outer:
    for i in 0..1:
      for j in 0..1:
        if x > 0: break outer
      if x > 0: symexTarget("s8m_lblouter_dead")
  if x == 6: symexTarget("s8m_lblouter")

proc deferCont(x: int) =
  for i in 0..1:
    defer:
      if i == 0 and x == 2: symexTarget("s8m_defercont")
    if i == 0: continue

proc exArmBreak(x: int) =
  var hits = 0
  for i in 0..2:
    try:
      for j in 0..1:
        if x == 9: raise newException(ValueError, "v")
    except ValueError:
      break
    hits += 1
  if x == 9 and hits == 0: symexTarget("s8m_exarm")
  if x == 9 and hits > 0: symexTarget("s8m_exarm_dead")

proc exArmBreakFin(x: int) =
  for i in 0..2:
    try:
      if x == 9: raise newException(ValueError, "v")
    except ValueError:
      break
    finally:
      if x == 9 and i == 0: symexTarget("s8m_exarm_fin")

proc brkCancelsReturn(x: int): int =
  result = 0   # a callee reading `result` before any write is a separate gap
  for i in 0..2:
    try:
      if x > 0: return 5
    finally:
      break
  result += 100

proc callsBrkCancels(x: int) =
  let r = brkCancelsReturn(x)
  if r == 105 and x == 3: symexTarget("s8m_brk_cancels")
  if r == 5: symexTarget("s8m_brk_cancels_dead")

proc brkOnRaise(x: int) =
  for i in 0..1:
    try:
      if x == 1: raise newException(ValueError, "r")
    finally:
      break
  if x == 1: symexTarget("s8m_brk_on_raise")

proc retInLoopFin(x: int): int =
  ## A `return` still leaves through the loop's `finally`.
  for i in 0..1:
    try:
      if x > 0: return 7
    finally:
      if x == 2: result = result + 1

proc callsRetInLoopFin(x: int) =
  if retInLoopFin(x) == 8: symexTarget("s8m_ret_loop_fin")

proc arrBreak(x: int) =
  let a = [1, 2, 3]
  var seen = 0
  for v in a:
    if v == x: break
    seen += 1
  if seen == 1 and x == 2: symexTarget("s8m_arrbreak")
  if seen == 3 and x == 2: symexTarget("s8m_arrbreak_dead")

proc arrCont(x: int) =
  let a = [1, 2, 3]
  var sum = 0
  for v in a:
    if v == x: continue
    sum += v
  if sum == 4 and x == 2: symexTarget("s8m_arrcont")

suite "S8m (1) break and continue through finally; labelled blocks":
  test "oracle":
    check brkCancelsReturn(3) == 105
    check brkCancelsReturn(0) == 100
    check retInLoopFin(2) == 8
    symexCaptureBegin()
    contFor(3); contForPlain(1); brkWhile(4); brkWhileAfter(1)
    nestedCont(5); blkBreak(7); blkInner(1); lblOuter(6); deferCont(2)
    exArmBreak(9); exArmBreakFin(9); arrBreak(2); arrCont(2)
    contSeq(@[-1, 4], 4)
    let hits = symexCaptureEnd()
    for l in ["s8m_contfor", "s8m_contfor_plain", "s8m_brkwhile",
              "s8m_brkwhile_after", "s8m_nested_cont", "s8m_blkbreak",
              "s8m_blkinner", "s8m_lblouter", "s8m_defercont", "s8m_exarm",
              "s8m_exarm_fin", "s8m_arrbreak", "s8m_arrcont", "s8m_contseq"]:
      check l in hits
    for l in ["s8m_brkwhile_dead", "s8m_nested_cont_dead",
              "s8m_blkbreak_dead", "s8m_lblouter_dead", "s8m_exarm_dead",
              "s8m_arrbreak_dead"]:
      check l notin hits

  test "continue in a for loop runs the finally (was a false sxUnsat)":
    let r = symexFind(contFor, tLabel("s8m_contfor"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(contFor(r.witness[0]), "s8m_contfor")

  test "continue in a for loop advances the loop":
    let r = symexFind(contForPlain, tLabel("s8m_contfor_plain"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 1
    let s = symexFind(contSeq, tLabel("s8m_contseq"), loopK)
    checkpoint($s.status & " " & show(s.errors))
    check s.status == sxSat
    if s.status == sxSat:
      check reproduces(contSeq(s.witness[0], s.witness[1]), "s8m_contseq")

  test "break out of a while runs the finally":
    let r = symexFind(brkWhile, tLabel("s8m_brkwhile"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let a = symexFind(brkWhileAfter, tLabel("s8m_brkwhile_after"), loopK)
    checkpoint($a.status & " " & show(a.errors))
    check a.status == sxSat
    let d = symexFind(brkWhileAfter, tLabel("s8m_brkwhile_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)

  test "nested finallys run innermost first on a continue":
    let r = symexFind(nestedCont, tLabel("s8m_nested_cont"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(nestedCont, tLabel("s8m_nested_cont_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)

  test "a labelled break leaves its block through the finally":
    let r = symexFind(blkBreak, tLabel("s8m_blkbreak"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
    let d = symexFind(blkBreak, tLabel("s8m_blkbreak_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a break of an inner block leaves only the block":
    let r = symexFind(blkInner, tLabel("s8m_blkinner"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 1

  test "a labelled break leaves both loops (was a false sxSat)":
    let d = symexFind(lblOuter, tLabel("s8m_lblouter_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)
    let r = symexFind(lblOuter, tLabel("s8m_lblouter"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6

  test "defer runs on a continue":
    let r = symexFind(deferCont, tLabel("s8m_defercont"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2

  test "a break in an except arm leaves the loop enclosing the try":
    let r = symexFind(exArmBreak, tLabel("s8m_exarm"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(exArmBreak, tLabel("s8m_exarm_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)
    let f = symexFind(exArmBreakFin, tLabel("s8m_exarm_fin"), loopK)
    checkpoint($f.status & " " & show(f.errors))
    check f.status == sxSat

  test "a break in a finally cancels the return":
    let r = symexFind(callsBrkCancels, tLabel("s8m_brk_cancels"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
    let d = symexFind(callsBrkCancels, tLabel("s8m_brk_cancels_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)

  test "a break in a finally on a raised exit declines (backends disagree)":
    let r = symexFind(brkOnRaise, tLabel("s8m_brk_on_raise"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, eeFinallyJumpOnRaise)

  test "a return still leaves through the loop's finally":
    let r = symexFind(callsRetInLoopFin, tLabel("s8m_ret_loop_fin"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2

  test "break and continue in an unrolled array loop":
    let r = symexFind(arrBreak, tLabel("s8m_arrbreak"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2
    let d = symexFind(arrBreak, tLabel("s8m_arrbreak_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let c = symexFind(arrCont, tLabel("s8m_arrcont"), loopK)
    checkpoint($c.status & " " & show(c.errors))
    check c.status == sxSat
    if c.status == sxSat:
      check c.witness[0] == 2

# ---- (2) a Z3 sort mismatch is a recorded walker fault ------------------------
#
# Mechanism (reproduced at a58dc08 with S8l's bool-discriminator fold removed,
# so `BoolV(on: true, t: x)` stored a BV into the Bool discriminator array):
#   c:   `sxUnsat []`                         -- no error recorded at all
#   cpp: `sxUnknown [ekZ3Error: ... domain sort (_ BitVec 64) and parameter
#         sort Bool do not match]`
# nim-z3's `checkErr` raises `Z3SortMismatchError` at the store, and on the C
# backend that raise, unwinding through the walker's `walkBlock` frames, is
# lost: the run carries on as if the store had not happened. The IR below is
# the same shape without the parser: an int literal stored through a
# `ref bool`, whose heap array has a Bool range.

proc boolCellProg(targetDead: bool): SymexProgram =
  let tail =
    if targetDead: mkIf(@[IRBranch(cond: mkBoolLit(false),
                                   body: mkTargetLabel("hit"))])
    else: mkTargetLabel("hit")
  SymexProgram(params: @[], body: mkBlock(@[
    mkNewT("p", tRef(tBool())),
    mkDerefWrite(mkVar("p"), mkIntLit(1), tBool()),
    tail]))

proc countUncheckedRaw(src: string): int =
  ## Raw `Z3_mk_store`/`select`/`ite`/`eq` calls outside the checked
  ## constructors' own bodies and the deliberate test-hook probe.
  var inHelpers = false
  for line in src.splitLines():
    let t = line.strip()
    if t.startsWith("# ---- RFC-0005 S8m: sort-checked Z3 term construction"):
      inHelpers = true
    elif inHelpers and t.startsWith("var convFloatToIntBoundConds"):
      inHelpers = false
    if inHelpers or t.startsWith("#") or "[s8m-unchecked-probe]" in line:
      continue
    for f in ["Z3_mk_store(", "Z3_mk_select(", "Z3_mk_ite(", "Z3_mk_eq("]:
      if f in line and not line.strip().startsWith("##"): inc result

suite "S8m (2) a Z3 sort mismatch is a recorded walker fault":
  test "an ill-sorted heap store is weInternalWalkerFault, never a verdict (was a silent sxUnsat on c)":
    let raw = runSymex(boolCellProg(false),
                       SymexTarget(kind: stkLabel, label: "hit"))
    checkpoint($raw.status & " " & show(raw.errors))
    check raw.status == sxUnknown
    var sortMsg = false
    for e in raw.errors:
      if e.kind == weInternalWalkerFault and "Z3 sort mismatch" in e.msg:
        sortMsg = true
    check sortMsg

  test "the error path cannot yield sxUnsat":
    # The label sits behind `if false`: dead whatever the heap holds. The
    # fault's class voids an UNSAT claim on the run (`scIncomplete`), so
    # the verdict is sxUnknown, not the sxUnsat the dead label would earn.
    let raw = runSymex(boolCellProg(true),
                       SymexTarget(kind: stkLabel, label: "hit"))
    checkpoint($raw.status & " " & show(raw.errors))
    check raw.status == sxUnknown
    check scIncomplete in runTaint(classOf(weInternalWalkerFault))
    check scSpurious in pathTaint(classOf(weInternalWalkerFault))

  test "a Z3 API error nobody checked is still counted for the run":
    let (counted, code) = rfc0005S8mUncheckedZ3Error()
    checkpoint($counted & " " & code)
    check counted >= 1
    check code.len > 0

  test "audit: every raw store/select/ite/eq goes through a sort check":
    const here = currentSourcePath.parentDir
    var n = 0
    for f in ["runtime.nim", "runtime_heap.nim", "runtime_strings.nim",
              "runtime_floats.nim", "runtime_exceptions.nim",
              "runtime_closures.nim"]:
      n += countUncheckedRaw(readFile(here / ".." / "src" / "nelli" / "smt" / f))
    check n == 0

# ---- (3) ref locals and same-type casts keep heap identity -------------------
#
# Probe (c and cpp identical):
#   refAssign(P(a: 3), 3) reaches the label; refAssign(nil, 3) does not
#   refAlias(p, 1): the write through `q` is the write through `p`
#   refCast(P(a: 3), 3) reaches the label: `cast[ref S8mObj](p)` is `p`
# Before S8m every one of these was `weInternalWalkerFault`: the uninitialised
# `q` was declined and left unbound, the cast was a declined expression whose
# dummy was an int, and `q != nil` then hit `eqBV`'s `a.kind == b.kind`
# assert (`runtime.nim:4608`).

type
  S8mObj = object
    a: int
  S8mOther = object
    b: float

proc refAssign(p: ref S8mObj; x: int) =
  var q: ref S8mObj
  if p != nil:
    q = p
  if q != nil:
    if q.a == x and x == 3: symexTarget("s8m_refassign")
  if q != nil and p == nil: symexTarget("s8m_refassign_dead")

proc refAlias(p: ref S8mObj; x: int) =
  var q: ref S8mObj
  if p != nil:
    q = p
    q.a = 41
    if p.a == 41 and x == 1: symexTarget("s8m_refalias")
    if p.a != 41: symexTarget("s8m_refalias_dead")

proc refCast(p: ref S8mObj; x: int) =
  let q = cast[ref S8mObj](p)
  if q != nil:
    if q.a == x and x == 3: symexTarget("s8m_refcast")
  if q != p: symexTarget("s8m_refcast_dead")

proc refCastOther(p: ref S8mObj; x: int) =
  let q = cast[ref S8mOther](p)
  if q != nil and x == 2: symexTarget("s8m_refcast_other")

# ---- (4) an uninitialised ref local is nil ------------------------------------
#
# Probe (c and cpp identical):
#   `var p: ref S8mObj; p == nil` is true
#   `var p: ref S8mObj; p.a = 1` is a nil access (SIGSEGV in a default debug
#     build; the walker models every nil access as NilAccessDefect, R5)
# Before S8m the declaration was `feUnsupportedStmtKind`.

proc uninitNil(x: int) =
  var p: ref S8mObj
  if p == nil and x == 2: symexTarget("s8m_uninit_nil")
  if p != nil: symexTarget("s8m_uninit_nil_dead")

proc uninitWrite(x: int) =
  var p: ref S8mObj
  if x == 2:
    p.a = 1

proc uninitNew(x: int) =
  var p: ref S8mObj
  if x > 0:
    p = new(S8mObj)
    p.a = x
  if p != nil and p.a == 4: symexTarget("s8m_uninit_new")
  if p == nil and x > 0: symexTarget("s8m_uninit_new_dead")

# ---- (5) a closure's bare return returns the zero value -----------------------
#
# Probe (c and cpp identical): closRet(-1) and closRet(1) both reach their
# labels -- f(-1) == 7, f(1) == 0 (Nim zero-initialises `result`).
# Before S8m a closure descent had no `retTy`, so the bare-return path joined
# the frame unbound, and `applyClosureGround` took its LAST BRANCH CONDITION
# (`y > 0`) for the value binding: `y > 0` became a ground axiom of the whole
# run, and `f(-1) == 7` was a false `sxUnsat`.

proc closRet(x: int) =
  let f = proc (y: int): int =
    if y > 0: return
    result = 7
  let r = f(x)
  if r == 7 and x == -1: symexTarget("s8m_closret_seven")
  if r == 0 and x == 1: symexTarget("s8m_closret_zero")
  if r != 0 and x == 1: symexTarget("s8m_closret_dead")

type
  S8mVK = enum svkA, svkB
  S8mV = object
    case k: S8mVK
    of svkA: a: int
    of svkB: b: int

proc closRetVariant(x: int) =
  ## A variant result's bare return. At S8m it had no modelled zero value
  ## and was `completeReturn`'s havoc site (`feUnsupportedOpHavoc`); RFC-0005
  ## S8n models it (Nim zero-initialises the variant: `k == svkA`, `a == 0`).
  let g = proc (y: int): S8mV =
    if y > 0: return
    result = S8mV(k: svkB, b: 3)
  let v = g(x)
  discard v
  if x == 5 and x == 6: symexTarget("s8m_closret_variant_dead")

suite "S8m (3) ref locals and same-type casts":
  test "oracle":
    var o = new(S8mObj)
    o.a = 3
    symexCaptureBegin()
    refAssign(o, 3); refAssign(nil, 3); refCast(o, 3)
    var o2 = new(S8mObj)
    refAlias(o2, 1)
    let hits = symexCaptureEnd()
    check "s8m_refassign" in hits
    check "s8m_refalias" in hits
    check "s8m_refcast" in hits
    check "s8m_refassign_dead" notin hits
    check "s8m_refcast_dead" notin hits

  test "a ref local assigned from a param keeps its identity (was weInternalWalkerFault)":
    let r = symexFind(refAssign, tLabel("s8m_refassign"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] != nil
      check r.witness[1] == 3
      check reproduces(refAssign(r.witness[0], r.witness[1]), "s8m_refassign")
    let d = symexFind(refAssign, tLabel("s8m_refassign_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a write through the local is a write through the param":
    let r = symexFind(refAlias, tLabel("s8m_refalias"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(refAlias(r.witness[0], r.witness[1]), "s8m_refalias")
    let d = symexFind(refAlias, tLabel("s8m_refalias_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a same-type ref cast is the identity (was weInternalWalkerFault)":
    let r = symexFind(refCast, tLabel("s8m_refcast"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(refCast(r.witness[0], r.witness[1]), "s8m_refcast")
    let d = symexFind(refCast, tLabel("s8m_refcast_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a cast to a different pointee is a recorded decline, never a fault":
    let r = symexFind(refCastOther, tLabel("s8m_refcast_other"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, feUnsupportedExprKind)
    check not hasKind(r.errors, weInternalWalkerFault)

suite "S8m (4) an uninitialised ref local is nil":
  test "oracle":
    symexCaptureBegin()
    uninitNil(2); uninitNew(4)
    let hits = symexCaptureEnd()
    check "s8m_uninit_nil" in hits
    check "s8m_uninit_new" in hits

  test "the local is nil (was feUnsupportedStmtKind)":
    let r = symexFind(uninitNil, tLabel("s8m_uninit_nil"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2
    let d = symexFind(uninitNil, tLabel("s8m_uninit_nil_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a write through it raises NilAccessDefect":
    let r = symexFind(uninitWrite, tNilAccess())
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "NilAccessDefect"
      check r.raisedWitness[0] == 2

  test "assigned a fresh cell on one branch, nil on the other":
    let r = symexFind(uninitNew, tLabel("s8m_uninit_new"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(uninitNew, tLabel("s8m_uninit_new_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

suite "S8m (5) a closure's bare return":
  test "oracle":
    symexCaptureBegin()
    closRet(-1); closRet(1)
    let hits = symexCaptureEnd()
    check "s8m_closret_seven" in hits
    check "s8m_closret_zero" in hits
    check "s8m_closret_dead" notin hits

  test "the bare-return guard is not an axiom of the run (was a false sxUnsat)":
    let r = symexFind(closRet, tLabel("s8m_closret_seven"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == -1
      check reproduces(closRet(r.witness[0]), "s8m_closret_seven")

  test "the bare return returns zero":
    let r = symexFind(closRet, tLabel("s8m_closret_zero"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 1
    let d = symexFind(closRet, tLabel("s8m_closret_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a variant result's bare return is its zero value (re-pinned by S8n)":
    let r = symexFind(closRetVariant, tLabel("s8m_closret_variant_dead"))
    checkpoint($r.status & " " & show(r.errors))
    # S8m pinned `feUnsupportedOpHavoc` + sxUnknown here: no variant zero
    # value, and a variant closure result substituted on the calling side.
    # RFC-0005 S8n models both (the zero value per real Nim, see
    # `tsymex_rfc0005_s8n_precision` (4)), so the dead label is a verdict.
    check not hasKind(r.errors, feUnsupportedOpHavoc)
    check r.status == sxUnsat

# ---- (6) walker version floor ---------------------------------------------------

suite "S8m (6) walker version":
  test "walker version is at least 160":
    check parseInt(symexWalkerVersion) >= 160
