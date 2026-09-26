## RFC-0005 (soundness channels) slice S9 -- delete both blanket vetoes
## (§2.5). Walker 151 -> 152.
##
## `capForcedUnknown` (any parse-time `sevError`) and `closureForcedUnknown`
## (any closure-sink `sevError`) forced `sxUnknown` on the whole run, whatever
## the path that found the answer had passed. S8 made the question they
## insured against answerable -- every decline names its anchor -- so S9
## deletes both and answers it. Suites:
##   (a) the veto companions through `symexFindAllWitnesses` (the S0 pins
##       carry the `symexFind` half);
##   (b) capture by reference: a closure reads a captured `var` as it stands
##       at the CALL, not at construction (the S7 handoff's `capMutNeg`,
##       fixed before the closure veto goes -- the veto never caught it:
##       the false SAT carried no record at all);
##   (c) the reach join: a parse-time decline no walked path reached is a
##       diagnostic (`sevHint`), not a run taint; a reached one keeps its
##       `sevError`;
##   (d) dedup keys on message AND anchor, so twin declines with one message
##       keep one walk record each (the join above reads them);
##   (e) an unplaced decline (§2.5 point 4) still blocks both directions;
##   (f) the walker version floor.
import std/[unittest, macros, strutils, options, sequtils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/dsl_parser
import nelli/smt/canonicalize

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn`.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  let av = parsed.annotationViolationsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`,
                 annotationViolations: `av`)

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & "@" & $e.scope
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc anchoredAt(errs: seq[SymexErrorInfo]; k: SymexErrorKind; m: int;
                sev: SymexErrorSeverity): int =
  ## How many records of kind `k` and severity `sev` sit at marker `m`.
  for e in errs:
    if e.kind == k and e.severity == sev and e.scope.kind == dskSiteAnchored and
       e.scope.markerId == m:
      inc result

proc findingFor(fs: seq[SymexFinding]; desc: string): Option[SymexFinding] =
  for f in fs:
    if f.targetDesc == desc: return some(f)
  none(SymexFinding)

# =============================================================================
# SUTs
# =============================================================================

proc s9CapCompanion(x: int) =
  ## A reached cast decline on a path disjoint from the witness (the walker
  ## forks `if` arms without a feasibility check, so the infeasible arm IS
  ## walked: the decline is reached, and taints only that path).
  if x > 5:
    if x < 3:
      let y = cast[int32](x) + 1
      discard y
  if x == 42:
    symexTarget("s9_cap_companion")

proc s9ClosureCompanion(xs: seq[int], x: int) =
  ## `filter` over a symbolic-length seq: `ceUnsupportedHof`, on the
  ## `x == 7` path only.
  if x == 7:
    let kept = xs.filter(proc(v: int): bool = v > 0)
    discard kept
  if x == 42:
    symexTarget("s9_closure_companion")

proc s9CapMutNeg(x: int) =
  ## The S7 handoff's `capMutNeg`: `k` is written AFTER the closure is built;
  ## Nim closures capture by reference, so `f()` is 5 and the label is dead.
  var k = 0
  let f = proc(): int = k
  k = 5
  if f() != 5:
    symexTarget("s9_capmut_neg")

proc s9CapMutPos(x: int) =
  ## The positive twin: `f()` reads `k == x`, so the label is live at x == 7
  ## (a by-value snapshot reads 0 and calls it dead -- a false UNSAT).
  var k = 0
  let f = proc(): int = k
  k = x
  if f() == 7:
    symexTarget("s9_capmut_pos")

proc s9CapBranch(x: int) =
  ## A write on one arm only: whenever `x > 10`, `f()` is `x`, never 0.
  var k = 0
  let f = proc(): int = k
  if x > 10:
    k = x
  if x > 10:
    if f() == 0:
      symexTarget("s9_capbranch")

proc s9Apply(g: proc(): int): int = g()

proc s9CapEscaped(x: int) =
  ## The closure is applied by a CALLEE, where the captured `var` is not in
  ## scope by name: its current value cannot be read, so the application is
  ## an honest decline (`ceCaptureByRefUnmodelled`), never the stale 0.
  var k = 0
  let f = proc(): int = k
  k = 5
  if s9Apply(f) != 5:
    symexTarget("s9_capescaped")

proc s9BodyWrite(x: int) =
  ## The closure body WRITES the captured `var`: the write is not carried
  ## back to the caller, so the application declines rather than leaving
  ## `k == 0` behind it.
  var k = 0
  let f = proc(v: int) = k = v
  f(x)
  if k != x:
    symexTarget("s9_bodywrite")

proc s9CapLet(x: int) =
  ## A `let` capture cannot change after construction: by value is exact,
  ## applied here or by a callee.
  let k = x
  let f = proc(): int = k
  if f() == 3:
    symexTarget("s9_caplet")

proc s9CapLetEscaped(x: int) =
  let k = x
  let f = proc(): int = k
  if s9Apply(f) == 3:
    symexTarget("s9_capletescaped")

proc s9DeadHandler(x: int) =
  ## The decline sits in a handler no raise is routed to: no walked path
  ## reaches its marker, and the label behind it is dead.
  try:
    if x == 4:
      discard
  except ValueError:
    let y = cast[int32](x) + 1
    if y == 1:
      symexTarget("s9_dead_handler")

proc s9ReachedDead(x: int) =
  ## The decline IS reached, and the label is dead: the reached decline's
  ## run coordinate still blocks `sxUnsat`.
  let y = cast[int32](x) + 1
  discard y
  if x > 5:
    if x < 3:
      symexTarget("s9_reached_dead")

proc s9TwinClassA(x: int) =
  ## Two Class-A declines with one message, one per arm: both are reached.
  if x > 0:
    let y = cast[int32](x) + 1
    discard y
  else:
    let y = cast[int32](x) + 1
    discard y
  if x == 3:
    symexTarget("s9_twin_a")

proc s9TwinClassB(x: int) =
  ## Two Class-B declines with one message, both reached.
  var f = float(x)
  f /= 2.0
  f /= 2.0
  if f > 1.0:
    symexTarget("s9_twin_b")

proc s9Clean(x: int) =
  if x == 9:
    symexTarget("s9_clean")

proc s9CleanDead(x: int) =
  if x > 5:
    if x < 3:
      symexTarget("s9_clean_dead")

# =============================================================================
# Oracles -- the same computation executed for real in Nim (house rule)
# =============================================================================

suite "RFC-0005 S9 -- oracles":

  test "closures capture by reference: the SUTs' premises hold in Nim":
    block:
      var k = 0
      let f = proc(): int = k
      k = 5
      check f() == 5
    block:
      var k = 0
      let f = proc(v: int) = k = v
      f(11)
      check k == 11
    block:
      var k = 0
      let f = proc(): int = k
      k = 5
      check s9Apply(f) == 5

# =============================================================================
# (a) the veto companions through symexFindAllWitnesses
# =============================================================================

suite "RFC-0005 S9 (a) -- the veto companions report sat through both consumers":

  test "symexFind: a reached cast decline off the witness path is sxSat":
    let r = symexFind(s9CapCompanion, tLabel("s9_cap_companion"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 42
    check r.errors.hasKind(feUnsupportedExprKind)

  test "symexFindAllWitnesses: the cap companion is sfSat":
    let db = inMemoryDatabase()
    let f = symexFindAllWitnesses(s9CapCompanion, db).findingFor(
      "label(\"s9_cap_companion\")")
    check f.isSome
    check f.get.status == sfSat

  test "symexFindAllWitnesses: the closure companion is sfSat":
    let db = inMemoryDatabase()
    let f = symexFindAllWitnesses(s9ClosureCompanion, db).findingFor(
      "label(\"s9_closure_companion\")")
    check f.isSome
    check f.get.status == sfSat

# =============================================================================
# (b) capture by reference
# =============================================================================

suite "RFC-0005 S9 (b) -- a closure reads its captured var at the call":

  test "capMutNeg: a write after construction is seen -- the label is dead, sxUnsat":
    let r = symexFind(s9CapMutNeg, tLabel("s9_capmut_neg"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "capMutPos: the written value is the one read -- sxSat at x == 7":
    let r = symexFind(s9CapMutPos, tLabel("s9_capmut_pos"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 7

  test "a write on one arm is seen on that arm -- sxUnsat":
    let r = symexFind(s9CapBranch, tLabel("s9_capbranch"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)

  test "applied by a callee: an honest decline, never the stale snapshot's sxSat":
    let r = symexFind(s9CapEscaped, tLabel("s9_capescaped"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(ceCaptureByRefUnmodelled)

  test "a body that writes a captured var declines, never the lost write's sxSat":
    let r = symexFind(s9BodyWrite, tLabel("s9_bodywrite"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(ceCaptureByRefUnmodelled)

  test "ceCaptureByRefUnmodelled is dcSubstituted (the stand-in is a stale value)":
    check classOf(ceCaptureByRefUnmodelled) == dcSubstituted

  test "a let capture is exact by value, in scope or applied by a callee":
    let r1 = symexFind(s9CapLet, tLabel("s9_caplet"))
    checkpoint($r1.status & " " & show(r1.errors))
    check r1.status == sxSat
    check r1.witness[0] == 3
    check not r1.errors.hasKind(ceCaptureByRefUnmodelled)
    let r2 = symexFind(s9CapLetEscaped, tLabel("s9_capletescaped"))
    checkpoint($r2.status & " " & show(r2.errors))
    check not r2.errors.hasKind(ceCaptureByRefUnmodelled)
    check r2.status != sxUnsat

# =============================================================================
# (c) the reach join
# =============================================================================

suite "RFC-0005 S9 (c) -- an unreached decline is a diagnostic; a reached one taints":

  test "an unreached decline behind a dead label: sxUnsat, the record kept as sevHint":
    let prog = progOf(s9DeadHandler)
    check prog.parseErrors.len == 1
    let m = prog.parseErrors[0].scope.markerId
    let r = symexFind(s9DeadHandler, tLabel("s9_dead_handler"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnsat
    checkUnsatOverTaintOnly(r)
    check r.errors.anchoredAt(feUnsupportedExprKind, m, sevHint) == 1
    check r.errors.anchoredAt(feUnsupportedExprKind, m, sevError) == 0

  test "a reached decline behind a dead label: sxUnknown, the parse record still sevError":
    let prog = progOf(s9ReachedDead)
    let m = prog.parseErrors[0].scope.markerId
    let r = runSymex(prog, tLabel("s9_reached_dead"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.errors.anchoredAt(feUnsupportedExprKind, m, sevError) == 2

# =============================================================================
# (d) dedup keys on message AND anchor
# =============================================================================

suite "RFC-0005 S9 (d) -- twin declines keep one walk record each":

  test "Class A: two same-message casts, both reached -- each marker joins its own reach record":
    let prog = progOf(s9TwinClassA)
    check prog.parseErrors.len == 2
    let m1 = prog.parseErrors[0].scope.markerId
    let m2 = prog.parseErrors[1].scope.markerId
    check m1 != m2
    check prog.parseErrors[0].msg == prog.parseErrors[1].msg
    let r = runSymex(prog, tLabel("s9_twin_a"))
    checkpoint($r.status & " " & show(r.errors))
    check r.errors.anchoredAt(feUnsupportedExprKind, m1, sevError) == 2
    check r.errors.anchoredAt(feUnsupportedExprKind, m2, sevError) == 2

  test "Class B: two same-message markers, both reached -- two anchored walk records":
    let r = runSymex(progOf(s9TwinClassB), tLabel("s9_twin_b"))
    checkpoint($r.status & " " & show(r.errors))
    var markers: seq[int]
    for e in r.errors:
      if e.kind == feUnsupportedStmtKind and e.severity == sevError and
         e.scope.kind == dskSiteAnchored and e.scope.markerId notin markers:
        markers.add e.scope.markerId
    check markers.len == 2

# =============================================================================
# (e) an unplaced decline still blocks both directions (§2.5 point 4)
# =============================================================================

suite "RFC-0005 S9 (e) -- reach undecidable: an unplaced decline blocks sat and unsat":

  test "control: the clean SUTs are sxSat / sxUnsat":
    check runSymex(progOf(s9Clean), tLabel("s9_clean")).status == sxSat
    check runSymex(progOf(s9CleanDead), tLabel("s9_clean_dead")).status == sxUnsat

  test "an unplaced sevError suppresses a clean hit (reach unknown -> sxUnknown)":
    var prog = progOf(s9Clean)
    prog.parseErrors.add SymexErrorInfo(kind: feUnsupportedExprKind,
      severity: sevError, msg: "S9 test: an unplaced decline",
      scope: DeclineScope(kind: dskUnplaced))
    let r = runSymex(prog, tLabel("s9_clean"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown

  test "an unplaced over-approximating decline blocks sxUnsat though its class alone would not":
    check scIncomplete notin runTaint(classOf(ceClosureBodyUncertain))
    var prog = progOf(s9CleanDead)
    prog.parseErrors.add SymexErrorInfo(kind: ceClosureBodyUncertain,
      severity: sevError, msg: "S9 test: an unplaced fresh-symbol decline",
      scope: DeclineScope(kind: dskUnplaced))
    let r = runSymex(prog, tLabel("s9_clean_dead"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown

# =============================================================================
# (f) walker version floor
# =============================================================================

suite "RFC-0005 S9 (f) -- walker version":

  test "walker version floor >= 152 (S9 moves verdicts: the vetoes, the reach join, capture by reference)":
    check parseInt(symexWalkerVersion) >= 152
