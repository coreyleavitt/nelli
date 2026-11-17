## K8c planted defect 3: NOT a defect, a control. libz3 throws a C++ exception
## internally (a probe over a non-propositional goal finds its answer by throwing
## (probe.cpp `is_non_propositional_predicate`) and catching it itself). Under ASan
## the interposed `__cxa_throw` calls the real one it resolved at process start;
## that lookup finds nothing when the executable does not link libstdc++ (the C
## backend does not; only libz3, loaded later, does), and ASan aborts with
## `CHECK failed: asan_interceptors.cpp ... real___cxa_throw != 0`. Every test
## that makes Z3 throw dies that way, so the job links libstdc++ into the
## executable (scripts/asan-slice.sh). This must EXIT CLEANLY: a self-test that
## passes while every real test aborts is a gap.
import z3
import z3/ffi

proc main() =
  let ctx = newContext()
  let i = ctx.mkIntVar("i")
  let zero = ctx.mkInt(0)
  let g = Z3_mk_goal(ctx.raw, false, false, false)
  Z3_goal_inc_ref(ctx.raw, g)
  Z3_goal_assert(ctx.raw, g, Z3_mk_gt(ctx.raw, i.raw, zero.raw))
  let pr = Z3_mk_probe(ctx.raw, "is-propositional")
  Z3_probe_inc_ref(ctx.raw, pr)
  # an arithmetic predicate is not propositional: the probe finds it by throwing
  # (is_non_propositional_predicate in probe.cpp, the frame of the CHECK abort)
  let v = Z3_probe_apply(ctx.raw, pr, g)
  doAssert v == 0.0, "the probe should report a non-propositional goal"
  Z3_probe_dec_ref(ctx.raw, pr)
  Z3_goal_dec_ref(ctx.raw, g)
  echo "z3 threw and recovered"
main()
