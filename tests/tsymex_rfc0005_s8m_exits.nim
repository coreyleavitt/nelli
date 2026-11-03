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
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with `tsymex_rfc0005_s8m_exits_b`,
## `tsymex_rfc0005_s8m_exits_c`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 66 s).

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

proc retInLoopFin(x: int): int =
  ## A `return` still leaves through the loop's `finally`.
  for i in 0..1:
    try:
      if x > 0: return 7
    finally:
      if x == 2: result = result + 1

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
