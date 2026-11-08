## RFC-0016 S8cj item 1 probe (not a suite): what moves a fresh thread's
## spend on one query. One compile; the process re-executes itself once per
## mode (`S8CJ_MODE`), so every mode is a fresh process. Each measurement
## prints the units, Z3's process-wide estimated allocation size, and the
## raw addresses of the query's two constants (pointer order would show
## here if the search read it).
import std/[strutils, options, os, osproc, dynlib]
import z3
import nelli/symex
import nelli/smt/runtime

type AllocSizeFn = proc (): uint64 {.cdecl.}
var allocSizeFn: AllocSizeFn

proc Z3_get_estimated_alloc_size(): uint64 =
  ## Looked up at run time: libz3 is dlopen'd by softlink, not linked.
  if allocSizeFn == nil:
    discard z3FullVersion()   # make sure libz3 is loaded
    for name in ["libz3.so", "libz3.so.5", "libz3.so.5.1", "libz3.so.5.1.0.0",
                 "libz3.so.4", "libz3.so.4.13", "libz3.so.4.13.4"]:
      let h = loadLib(name)
      if h != nil:
        let p = symAddr(h, "Z3_get_estimated_alloc_size")
        if p != nil:
          allocSizeFn = cast[AllocSizeFn](p)
          break
    if allocSizeFn == nil:
      stderr.writeLine "Z3_get_estimated_alloc_size: not found"
      return 0
  allocSizeFn()
proc c_malloc(size: csize_t): pointer {.importc: "malloc", header: "<stdlib.h>".}
proc c_free(p: pointer) {.importc: "free", header: "<stdlib.h>".}
proc mallopt(param: cint; value: cint): cint {.importc, header: "<malloc.h>".}
const M_ARENA_MAX = -8.cint
const M_MMAP_THRESHOLD = -3.cint

const bound = 50_000_000'u

proc units(s: Z3Solver): int =
  let st = s.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc alloc(): string = "alloc=" & $Z3_get_estimated_alloc_size()

proc hex(p: pointer): string = "0x" & toHex(cast[uint](p))

proc solveQ(): string =
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
  "z3=" & $units(s) & "(" & $r & ") x=" & hex(cast[pointer](x.raw)) &
    " y=" & hex(cast[pointer](y.raw)) & (if cast[uint](x.raw) < cast[uint](y.raw): " x<y" else: " x>y")

proc buildFacts(ctx: Z3Context): tuple[x: Z3Int, facts: seq[Z3Bool], cond: Z3Bool] =
  let x = mkIntVar(ctx, "x")
  let y = mkIntVar(ctx, "y")
  let one = mkInt(ctx, 1)
  let lim = mkInt(ctx, 2000)
  (x, @[x > one, y > one, x < lim, y < lim, x * y == mkInt(ctx, 1_022_117)], x > one)

proc scratchQ(): string =
  ## The same query through nelli's `concreteBranchOutcome` (own context).
  let ctx = newContext()
  let (_, facts, cond) = buildFacts(ctx)
  let settings = SymexSettings(budget: ResourceBudget(queryRLimit: bound))
  let before = ownContextUnits
  let o = concreteBranchOutcome(ctx, @[], cond, settings, facts)
  "nelli=" & $(ownContextUnits - before) & "(" & $o & ")"

proc translateQ(): string =
  ## Bisect (a): the query built in one context, translated into a fresh
  ## one in `queryTermOrder` (as `ownContextSolver` does), `querySolver`
  ## there, one check. No nelli per-thread setup is touched.
  let ctx = newContext()
  let (_, facts, cond) = buildFacts(ctx)
  let roots = facts & @[cond]
  let prev = currentContext()
  let own = newContext()
  setCurrentContext(prev)
  let order = queryTermOrder(ctx, roots)
  var at: seq[(int, int)]
  let terms = newAstVector(ctx)
  for i, t in order:
    at.add (astId(ctx, t.raw), i)
    terms.add t
  let made = translate(terms, own)
  var inOwn = newSeq[Z3Bool](roots.len)
  for i, c in roots:
    let id = astId(ctx, c.raw)
    for (k, j) in at:
      if k == id: inOwn[i] = wrap[Z3Bool](own, made[j])
  let s = querySolver(own, inOwn, bound)
  let r = s.check()
  "translate=" & $units(s) & "(" & $r & ")"

proc inCtxQ(): string =
  ## Bisect (b): `querySolver` in the context the query was built in, no
  ## translation, one check.
  let ctx = newContext()
  let (_, facts, cond) = buildFacts(ctx)
  let s = querySolver(ctx, facts & @[cond], bound)
  let r = s.check()
  "inctx=" & $units(s) & "(" & $r & ")"

var outp: string   # written by one thread at a time, joined before read

type Step = enum sPure, sNelli, sTranslate, sInCtx, sRelease
type Plan = tuple[tag: string, steps: set[Step]]

proc report(tag: string; steps: set[Step]) =
  var parts: seq[string]
  if sPure in steps: parts.add solveQ()
  if sTranslate in steps: parts.add translateQ()
  if sInCtx in steps: parts.add inCtxQ()
  if sNelli in steps: parts.add scratchQ()
  if sRelease in steps: setCurrentContext(nil)
  outp = tag & ": " & parts.join(" ") & " " & alloc()

proc measure(p: Plan) {.thread.} =
  {.cast(gcsafe).}: report(p.tag, p.steps)

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
    outp = "z3Work: " & $s.check() & " units=" & $units(s) & " " & alloc()

proc mallocWork(keepEvery: int): seq[pointer] =
  var all: seq[pointer]
  for k in 0 ..< 200_000:
    all.add c_malloc(csize_t(16 + (k mod 7) * 24))
  for k, p in all:
    if keepEvery > 0 and k mod keepEvery == 0: result.add p
    else: c_free(p)

var leaked: seq[pointer]

proc mallocOnly() {.thread.} =
  {.cast(gcsafe).}:
    leaked = mallocWork(97)
    outp = "mallocOnly: kept " & $leaked.len & " blocks " & alloc()

proc run(p: Plan) =
  var th: Thread[Plan]
  createThread(th, measure, p)
  joinThread(th)
  echo outp

proc run(fn: proc () {.thread.}) =
  var th: Thread[void]
  createThread(th, fn)
  joinThread(th)
  echo outp

proc main(tag: string; steps: set[Step]) =
  report(tag, steps); echo outp

proc child(mode: string) =
  echo "== mode ", mode, " Z3 ", z3FullVersion(), " ", alloc()
  case mode
  of "15":   # six fresh threads, pure then nelli, nothing else
    main("main", {sPure, sNelli})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sNelli}))
    main("main after", {sPure, sNelli})
  of "15r":  # mode 15, each thread releasing its current context before exit
    main("main", {sPure, sNelli})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sNelli, sRelease}))
    main("main after", {sPure, sNelli})
  of "15p":  # six fresh threads, pure only
    main("main", {sPure})
    for i in 1 .. 6: run(("thread #" & $i, {sPure}))
    main("main after", {sPure, sNelli})
  of "16":   # probe 1 minus the nelli path
    main("main #1", {sPure}); main("main #2", {sPure})
    run(("thread fresh #1", {sPure})); run(("thread fresh #2", {sPure}))
    run(mallocOnly)
    run(("thread after malloc-only #1", {sPure})); run(("thread after malloc-only #2", {sPure}))
    main("main after malloc-only", {sPure})
    run(z3Work)
    run(("thread after z3 work #1", {sPure})); run(("thread after z3 work #2", {sPure}))
    main("main after z3 work", {sPure})
    main("main last (nelli too)", {sPure, sNelli})
  of "17":   # live contexts on the main thread, no threads
    main("main", {sPure, sNelli})
    var live: seq[Z3Context]
    for n in [1, 2, 4, 8, 16, 32, 64]:
      while live.len < n: live.add newContext()
      main("main with " & $n & " live contexts", {sPure, sNelli})
    live.setLen(0)
    main("main after freeing them", {sPure, sNelli})
  of "18a":  # bisect: translate-only on six fresh threads
    main("main", {sPure, sTranslate})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sTranslate}))
    main("main after", {sPure, sTranslate, sNelli})
  of "18b":  # bisect: querySolver in the build context on six fresh threads
    main("main", {sPure, sInCtx})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sInCtx}))
    main("main after", {sPure, sInCtx, sNelli})
  of "19":   # main thread only: a large malloc/free (mmap threshold) then measure
    main("main", {sPure, sNelli})
    for mb in [1, 4, 32]:
      c_free(c_malloc(csize_t(mb * 1024 * 1024)))
      main("main after free(malloc(" & $mb & "MB))", {sPure, sNelli})
  of "20":   # mode 15 under M_ARENA_MAX=1
    doAssert mallopt(M_ARENA_MAX, 1) == 1
    main("main", {sPure, sNelli})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sNelli}))
    main("main after", {sPure, sNelli})
  of "21":   # mode 15 with a fixed mmap threshold (no dynamic adjustment)
    doAssert mallopt(M_MMAP_THRESHOLD, 128 * 1024) == 1
    main("main", {sPure, sNelli})
    for i in 1 .. 6: run(("thread #" & $i, {sPure, sNelli}))
    main("main after", {sPure, sNelli})
  else:
    echo "unknown mode"

let mode = getEnv("S8CJ_MODE")
if mode.len > 0:
  child(mode)
else:
  var modes = getEnv("S8CJ_MODES", "15,15r,15p,16,17,18a,18b,19,20,21").split(',')
  for m in modes:
    putEnv("S8CJ_MODE", m)
    let (o, rc) = execCmdEx(quoteShell(getAppFilename()),
                            options = {poStdErrToStdOut})
    stdout.write o
    echo "== mode ", m, " rc=", rc
