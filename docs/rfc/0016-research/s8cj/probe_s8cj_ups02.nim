# RFC-0016 S8cj item 2 probe: reduce the `mk_unique` VERIFY failure to
# SMT-LIB text. Each variant is parsed into a fresh context and checked
# under `rlimit`; the VERIFY message (stderr) lands between the markers.
import std/[strutils]
import z3

proc units(s: Z3Solver): int =
  let st = s.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc variant(name, smt2: string; rlimit: uint; seed = true; extra: seq[(string, bool)] = @[]) =
  stderr.writeLine "--- begin " & name
  stderr.flushFile
  let ctx = newContext()
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("rlimit", rlimit)
  if seed: p.set("random_seed", 0'u)
  for (k, v) in extra: p.set(k, v)
  s.setParams(p)
  for a in parseSmt2String(ctx, smt2): s.add a
  let r = s.check()
  let why = if r == zsUnknown: " (" & s.reasonUnknown() & ")" else: ""
  stderr.writeLine "--- end " & name & ": " & $r & why & " units=" & $units(s)
  stderr.flushFile

const decls = "(declare-const p Int) (declare-const q Int) (declare-const x Int)\n"
const full = decls &
  "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207)) (assert (< p x))\n"

variant("full/50M", full, 50_000_000'u)
variant("full/50M/no-seed", full, 50_000_000'u, seed = false)
variant("no-x", decls & "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207))\n", 50_000_000'u)
variant("no-lower-bounds", decls & "(assert (= (* p q) 16777207)) (assert (< p x))\n", 50_000_000'u)
variant("x-bounded", full & "(assert (< x 100000))\n", 50_000_000'u)
variant("small-product", decls & "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 1022117)) (assert (< p x))\n", 50_000_000'u)
variant("prime-product", decls & "(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777213)) (assert (< p x))\n", 50_000_000'u)
variant("full/5M", full, 5_000_000'u)
variant("full/50M/nlsat.reorder=false", full, 50_000_000'u, extra = @[("nlsat.reorder", false)])
variant("full/50M/arith.nl.nra=false", full, 50_000_000'u, extra = @[("smt.arith.nl.nra", false)])
