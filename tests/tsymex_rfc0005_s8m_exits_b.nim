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
## RFC-0005 S8cm: part 2 of 3 of this suite, with `tsymex_rfc0005_s8m_exits`,
## `tsymex_rfc0005_s8m_exits_c`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 66 s).

import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import ./s8cu_helpers
import audit_scan_utils

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

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
  test "defer runs on a continue":
    let r = pinFind(deferCont, tLabel("s8m_defercont"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2

  test "a break in an except arm leaves the loop enclosing the try":
    let r = pinFind(exArmBreak, tLabel("s8m_exarm"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = pinFind(exArmBreak, tLabel("s8m_exarm_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)
    let f = pinFind(exArmBreakFin, tLabel("s8m_exarm_fin"), loopK)
    checkpoint($f.status & " " & show(f.errors))
    check f.status == sxSat

  test "a break in a finally cancels the return":
    let r = pinFind(callsBrkCancels, tLabel("s8m_brk_cancels"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
    let d = pinFind(callsBrkCancels, tLabel("s8m_brk_cancels_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check deadModuloUnroll(d)

  test "a break in a finally on a raised exit declines (backends disagree)":
    let r = pinFind(brkOnRaise, tLabel("s8m_brk_on_raise"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, eeFinallyJumpOnRaise)

  test "a return still leaves through the loop's finally":
    let r = pinFind(callsRetInLoopFin, tLabel("s8m_ret_loop_fin"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2

  test "break and continue in an unrolled array loop":
    let r = pinFind(arrBreak, tLabel("s8m_arrbreak"), loopK)
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 2
    let d = pinFind(arrBreak, tLabel("s8m_arrbreak_dead"), loopK)
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let c = pinFind(arrCont, tLabel("s8m_arrcont"), loopK)
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

const
  rawBuilders = ["Z3_mk_store(", "Z3_mk_select(", "Z3_mk_ite(", "Z3_mk_eq("]
  checkedBegin = "# ---- [s8m-checked-builders-begin]"
  checkedEnd = "# ---- [s8m-checked-builders-end]"
  checkedHome = "z3check.nim"
    ## The one file whose marked region holds the four checked builders.

proc uncheckedRawSites(label, src: string; exempt: bool): seq[string] =
  ## Raw `Z3_mk_store`/`select`/`ite`/`eq` calls in code (comments and
  ## strings blanked by `codeOf`), less the line tagged
  ## `[s8m-unchecked-probe]` (the deliberate test-hook probe) and, when
  ## `exempt`, the checked builders' own region. That region is bounded by
  ## two markers, each of which must be present exactly once and in order:
  ## a missing marker is reported as a site, so a moved or renamed builder
  ## block fails the audit instead of silently widening (a lost end marker)
  ## or dropping (a lost start marker) the exempt span. The end marker the
  ## audit had read until K9e, `var convFloatToIntBoundConds` in
  ## `runtime.nim`, vanished at 5219dd1d, and the audit then skipped every
  ## line of `runtime.nim` after its start marker without failing.
  let srcLines = src.splitLines()
  let code = codeOf(src).splitLines()
  doAssert code.len == srcLines.len, label & ": codeOf changed the line count"
  var lo, hi = -1
  var begins, ends = 0
  for i, line in srcLines:
    let t = line.strip()
    if t.startsWith(checkedBegin):
      inc begins
      lo = i
    elif t.startsWith(checkedEnd):
      inc ends
      hi = i
  if exempt:
    if begins != 1 or ends != 1 or lo > hi:
      result.add label & ": the checked-builder markers are missing, " &
        "repeated or out of order (begin " & $begins & ", end " & $ends & ")"
      return
  elif begins + ends > 0:
    result.add label & ": a checked-builder marker outside " & checkedHome
    return
  for i, line in code:
    if exempt and i > lo and i < hi: continue
    if "[s8m-unchecked-probe]" in srcLines[i]: continue
    for f in rawBuilders:
      if f in line:
        result.add label & ":" & $(i + 1) & ": " & srcLines[i].strip()

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
    # Over the whole runtime family (`audit_scan_utils.runtimeFamilyFiles`),
    # never a hand-picked list: a file cut out of `runtime.nim` stays in
    # scope. The list read here until K9e named six files and missed
    # `string_lower_support.nim` when D3c-7 moved code into it.
    var sites: seq[string]
    var builders = 0
    for (label, path) in runtimeFamilySources():
      let src = readFile(path)
      let home = path.extractFilename == checkedHome
      sites.add uncheckedRawSites(label, src, home)
      if home:
        for f in rawBuilders: builders += src.count(f)
    for s in sites: checkpoint s
    check sites.len == 0
    # The exempt region is the builders, not a span that grew around them:
    # each raw builder is named exactly once in its home file.
    check builders == rawBuilders.len

  test "audit: a lost or stray marker fails, never narrows the audit":
    const body = "  ctx.checkErr Z3_mk_ite(a, b, c, d)\n"
    let marked = checkedBegin & "\n" & body & checkedEnd & "\n"
    check uncheckedRawSites("ok", marked, true).len == 0
    check uncheckedRawSites("noEnd", checkedBegin & "\n" & body, true).len == 1
    check uncheckedRawSites("noBegin", body & checkedEnd & "\n", true).len == 1
    check uncheckedRawSites("none", body, true).len == 1
    check uncheckedRawSites("swapped", checkedEnd & "\n" & body &
                            checkedBegin & "\n", true).len == 1
    check uncheckedRawSites("stray", marked, false).len == 1
    check uncheckedRawSites("plain", body, false).len == 1
    check uncheckedRawSites("comment", "# Z3_mk_eq(x)\n", false).len == 0
