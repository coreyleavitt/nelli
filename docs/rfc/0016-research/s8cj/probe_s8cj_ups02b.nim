# RFC-0016 S8cj item 2 probe, second round: the `mk_unique` reduction on
# every (Z3, backend) row, with the parameter variants under the names the
# smt solver accepts (`arith.nl.*`, unprefixed, as solver params) and the
# nlsat module's own (`nlsat.*`, reachable only as global params). Each
# variant parses into a fresh context; the VERIFY message (stderr) lands
# between the markers.
import std/[strutils, times, monotimes]
import z3

proc units(s: Z3Solver): int =
  let st = s.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc variant(name, smt2: string; rlimit: uint; solverParams: seq[(string, string)] = @[];
             globalParams: seq[(string, string)] = @[]) =
  stderr.writeLine "--- begin " & name
  stderr.flushFile
  for (k, v) in globalParams: Z3_global_param_set(k.cstring, v.cstring)
  let t0 = getMonoTime()
  var line: string
  try:
    let ctx = newContext()
    let s = newSolver(ctx)
    let p = newParams(ctx)
    p.set("rlimit", rlimit)
    p.set("random_seed", 0'u)
    for (k, v) in solverParams:
      if v in ["true", "false"]: p.set(k, v == "true")
      elif k == "random_seed": p.set(k, uint(parseInt(v)))
      else: p.set(k, v)
    s.setParams(p)
    for a in parseSmt2String(ctx, smt2): s.add a
    let r = s.check()
    let why = if r == zsUnknown: " (" & s.reasonUnknown() & ")" else: ""
    line = $r & why & " units=" & $units(s)
  except CatchableError as e:
    line = "EXCEPTION " & $e.name & ": " & e.msg
  let ms = (getMonoTime() - t0).inMilliseconds
  if globalParams.len > 0: Z3_global_param_reset_all()
  stderr.writeLine "--- end " & name & ": " & line & " wall=" & $ms & "ms"
  stderr.flushFile

const decls = "(declare-const p Int) (declare-const q Int) (declare-const x Int)\n"
const full = decls &
  "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207)) (assert (< p x))\n"
const three = "(declare-const p Int) (declare-const q Int)\n" &
  "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207))\n"
const prime = "(declare-const p Int) (declare-const q Int)\n" &
  "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777213))\n"
const bounded = three & "(assert (< p 200000)) (assert (< q 200000))\n"

stderr.writeLine "Z3 " & z3FullVersion()
variant("full/50M", full, 50_000_000'u)
variant("three/50M", three, 50_000_000'u)
variant("three/5M", three, 5_000_000'u)
variant("prime/50M", prime, 50_000_000'u)
variant("bounded-200k/50M", bounded, 50_000_000'u)
variant("three/50M/arith.nl.nra=false", three, 50_000_000'u, @[("arith.nl.nra", "false")])
variant("three/50M/arith.nl.grobner=false", three, 50_000_000'u, @[("arith.nl.grobner", "false")])
variant("three/50M/arith.nl.order=false", three, 50_000_000'u, @[("arith.nl.order", "false")])
variant("three/50M/random_seed=1", three, 50_000_000'u, @[("random_seed", "1")])
variant("three/50M/global nlsat.reorder=false", three, 50_000_000'u, @[], @[("nlsat.reorder", "false")])
variant("three/50M/global nlsat.simplify_conflicts=false", three, 50_000_000'u, @[], @[("nlsat.simplify_conflicts", "false")])
variant("three/50M/global nlsat.factor=false", three, 50_000_000'u, @[], @[("nlsat.factor", "false")])
variant("three/50M/global nlsat.seed=7", three, 50_000_000'u, @[], @[("nlsat.seed", "7")])
variant("three/50M again (globals reset)", three, 50_000_000'u)
