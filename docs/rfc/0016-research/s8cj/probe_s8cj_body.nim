# RFC-0016 S8cj probe body (included by tests/probe_s8cj_m*.nim, which set
# `mode`). One process per mode: pure-Z3 spend on one query, fresh context
# each time, measured on the main thread and on a fresh thread, before and
# after one kind of prior Z3 work.
import std/[strutils, options]
import z3
import nelli/symex
import nelli/smt/runtime

const bound = 50_000_000'u

proc units(s: Z3Solver): int =
  let st = s.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc solveQ(): tuple[units: int, status: string] =
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

var outp: string

proc measure(tag: string) {.thread.} =
  {.cast(gcsafe).}:
    let q = solveQ()
    outp = tag & ": z3 units=" & $q.units & " (" & q.status & ")"

proc factoring(extraConsts: int; rlimit: uint; checks: int): string =
  let ctx = newContext()
  var keep: seq[Z3Int]
  for k in 0 ..< extraConsts: keep.add mkIntVar(ctx, "s8cj_unrelated_" & $k)
  let p = mkIntVar(ctx, "p")
  let q = mkIntVar(ctx, "q")
  let x = mkIntVar(ctx, "x")
  let s = newSolver(ctx)
  let sp = newParams(ctx)
  sp.set("rlimit", rlimit)
  sp.set("random_seed", 0'u)
  s.setParams(sp)
  s.add p > mkInt(ctx, 1)
  s.add q > mkInt(ctx, 1)
  s.add p * q == mkInt(ctx, 4093 * 4099)
  s.add p < x
  result = "factoring(consts=" & $extraConsts & ", rlimit=" & $rlimit & "):"
  for i in 1 .. checks:
    let r = s.check()
    result.add " " & $r & "@" & $units(s)

proc constsOnly() {.thread.} =
  {.cast(gcsafe).}:
    let ctx = newContext()
    var keep: seq[Z3Int]
    for k in 0 ..< 3000: keep.add mkIntVar(ctx, "s8cj_unrelated_" & $k)
    outp = "3000 constants, no solver"

proc factoringThread(a: tuple[consts: int; rlimit: uint; checks: int]) {.thread.} =
  {.cast(gcsafe).}: outp = factoring(a.consts, a.rlimit, a.checks)

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

proc mainQ(tag: string) =
  let q = solveQ()
  echo tag, ": z3 units=", q.units, " (", q.status, ")"

echo "Z3 ", z3FullVersion(), " mode ", mode
mainQ("main before")
run(measure, "thread before")
case mode
of 1: run(constsOnly)
of 2: run(factoringThread, (0, 2_000_000'u, 1))
of 3: run(factoringThread, (0, 50_000_000'u, 1))
of 4: echo factoring(0, 2_000_000'u, 1), " [main thread]"
of 5: run(factoringThread, (3000, 2_000_000'u, 1))
of 6:
  for i in 1 .. 6:
    let sc = scratchQ()
    echo "nelli scratch #", i, ": units=", sc.units, " (", sc.outcome, ")"
of 7: run(factoringThread, (0, 100_000'u, 1))
of 8: run(factoringThread, (3000, 2_000_000'u, 2))
of 9:
  # Address shift only: leak one odd-sized block between solves, main thread.
  proc c_malloc(size: csize_t): pointer {.importc: "malloc", header: "<stdlib.h>".}
  var leaks: seq[pointer]
  for sz in [8, 24, 40, 56, 72, 104, 136, 200, 1000, 4096, 8192, 65536]:
    leaks.add c_malloc(csize_t(sz))
    let a = solveQ()
    let b = solveQ()
    echo "after leaking ", sz, " bytes: ", a.units, " ", b.units
of 11: run(factoringThread, (3000, 50_000_000'u, 1))
of 12: run(factoringThread, (300, 2_000_000'u, 1))
of 13: run(factoringThread, (30, 2_000_000'u, 1))
of 14:
  for i in 1 .. 3:
    let sc = scratchQ()
    echo "nelli scratch #", i, ": units=", sc.units, " (", sc.outcome, ")"
    mainQ("main after nelli scratch #" & $i)
else: discard
mainQ("main after")
run(measure, "thread after")
run(measure, "thread after #2")
mainQ("main after #2")
