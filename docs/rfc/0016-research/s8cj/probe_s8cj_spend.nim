## RFC-0016 S8cj item 1 probe (not a suite): where does a fresh thread's
## spend on one query come from? One query, a fresh Z3 context each time,
## with and without prior work of three kinds: Z3 work on another thread,
## malloc-only work (no Z3) on another thread, malloc-only work on the
## same thread. Prints one line per measurement.
import std/[strutils, options, os]
import z3
import nelli/symex
import nelli/smt/runtime

proc c_malloc(size: csize_t): pointer {.importc: "malloc", header: "<stdlib.h>".}
proc c_free(p: pointer) {.importc: "free", header: "<stdlib.h>".}
when defined(s8cjArena1):
  proc mallopt(param: cint; value: cint): cint {.importc, header: "<malloc.h>".}
  const M_ARENA_MAX = -8.cint
  doAssert mallopt(M_ARENA_MAX, 1) == 1

const bound = 50_000_000'u

proc units(s: Z3Solver): int =
  let st = s.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc solveQ(): tuple[units: int, status: string] =
  ## The S8by scratch query, pure Z3, fresh context, `random_seed = 0`.
  let ctx = newContext()
  let x = mkIntVar(ctx, "x")
  let y = mkIntVar(ctx, "y")
  let one = mkInt(ctx, 1)
  let lim = mkInt(ctx, 2000)
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("rlimit", bound)
  p.set("random_seed", 0'u)
  s.setParams(p)
  for f in [x > one, y > one, x < lim, y < lim, x * y == mkInt(ctx, 1_022_117),
            x > one]:
    s.add f
  let r = s.check()
  (units(s), $r)

proc scratchQ(): tuple[units: int, outcome: string] =
  ## The same query through nelli's `concreteBranchOutcome` (own context).
  let ctx = newContext()
  let x = mkIntVar(ctx, "x")
  let y = mkIntVar(ctx, "y")
  let one = mkInt(ctx, 1)
  let lim = mkInt(ctx, 2000)
  let facts = @[x > one, y > one, x < lim, y < lim,
                x * y == mkInt(ctx, 1_022_117)]
  let settings = SymexSettings(budget: ResourceBudget(queryRLimit: bound))
  let before = ownContextUnits
  let o = concreteBranchOutcome(ctx, @[], x > one, settings, facts)
  (ownContextUnits - before, $o)

var line {.threadvar.}: string
var outp: string   # written by one thread at a time, joined before read

proc report(tag: string) =
  let q = solveQ()
  let sc = scratchQ()
  outp = tag & ": z3 units=" & $q.units & " (" & q.status & "); nelli units=" &
    $sc.units & " (" & sc.outcome & ")"

proc measure(tag: string) {.thread.} =
  {.cast(gcsafe).}: report(tag)

proc z3Work() {.thread.} =
  ## S8by's perturbation: 3000 unrelated constants and a factoring search.
  {.cast(gcsafe).}:
    let ctx = newContext()
    var keep: seq[Z3Int]
    for k in 0 ..< 3000: keep.add mkIntVar(ctx, "s8cj_unrelated_" & $k)
    let p = mkIntVar(ctx, "p")
    let q = mkIntVar(ctx, "q")
    let x = mkIntVar(ctx, "x")
    let s = newSolver(ctx)
    let sp = newParams(ctx)
    sp.set("rlimit", 2_000_000'u)
    s.setParams(sp)
    s.add p > mkInt(ctx, 1)
    s.add q > mkInt(ctx, 1)
    s.add p * q == mkInt(ctx, 4093 * 4099)
    s.add p < x
    discard s.check()
    outp = "z3Work: " & $s.check() & " units=" & $units(s)

proc mallocWork(keepEvery: int): seq[pointer] =
  ## No Z3: allocate many small blocks, free all but every `keepEvery`-th.
  var all: seq[pointer]
  for k in 0 ..< 200_000:
    all.add c_malloc(csize_t(16 + (k mod 7) * 24))
  for k, p in all:
    if keepEvery > 0 and k mod keepEvery == 0: result.add p
    else: c_free(p)

var leaked: seq[pointer]   # kept alive on purpose (heap holes)

proc mallocOnly() {.thread.} =
  {.cast(gcsafe).}:
    leaked = mallocWork(97)
    outp = "mallocOnly: kept " & $leaked.len & " blocks"

proc sameThread() {.thread.} =
  ## On one thread: solve, perturb the heap with malloc only, solve again.
  {.cast(gcsafe).}:
    let a = solveQ()
    let b = solveQ()
    let kept = mallocWork(97)
    let c = solveQ()
    let d = solveQ()
    for p in kept: c_free(p)
    let e = solveQ()
    outp = "sameThread: " & $a.units & " " & $b.units & " | malloc-perturbed " &
      $c.units & " " & $d.units & " | freed " & $e.units

proc run[T](fn: proc (a: T) {.thread.}; a: T) =
  var th: Thread[T]
  createThread(th, fn, a)
  joinThread(th)
  echo outp

proc run(fn: proc () {.thread.}) =
  var th: Thread[void]
  createThread(th, fn)
  joinThread(th)
  echo outp

echo "Z3 ", z3FullVersion(), when defined(s8cjArena1): " (M_ARENA_MAX=1)" else: ""
report("main #1"); echo outp
report("main #2"); echo outp
run(measure, "thread fresh #1")
run(measure, "thread fresh #2")
run(mallocOnly)
run(measure, "thread after malloc-only thread #1")
run(measure, "thread after malloc-only thread #2")
report("main after malloc-only thread"); echo outp
run(z3Work)
run(measure, "thread after z3 work #1")
run(measure, "thread after z3 work #2")
report("main after z3 work"); echo outp
run(sameThread)
run(measure, "thread last")
report("main last"); echo outp
