# S8cj research notes: thread-history spend (PRC-32, CI-03, INT-04) and Z3 5.1's `mk_unique` check (UPS-02, PND-10)

Base `4717fcea` (main), branch `rfc-0016-s8cj`, 2026-11-07. Everything below
ran in the podman image `localhost/nelli-dev:latest` (openSUSE Tumbleweed,
glibc 2.43, `libz3-5_1-5.1.0-1.1` from the distro build), c backend. Nothing
ran on cpp or on Z3 4.13.4 yet. Probe sources and the raw logs are in
`s8cj/` beside this file; the probes were run from `tests/` by
`scripts/dt-bounded.sh c tests/probe_s8cj_m<N>.nim 600` and are not suites
(no `unittest`, not registered).

## Item 1: a fresh thread's spend on one query

### The query and the two measurements

One query, S8by's scratch solve: `x > 1, y > 1, x < 2000, y < 2000,
x * y == 1022117` beside `x > 1` (SAT). Two ways of running it, both in a
fresh Z3 context every time, `rlimit = 50M`, `random_seed = 0`:

- **pure Z3** (`solveQ`): `newContext()`, `newSolver`, the six assertions,
  `check()`, read `rlimit count` from the solver's statistics;
- **nelli path** (`scratchQ`): `concreteBranchOutcome(ctx, @[], x > 1,
  settings, facts)`, which is two `ownContextSolver` solves (the query
  translated into a context of its own in `queryTermOrder`), units read as
  the growth of `ownContextUnits`.

### Probe matrix (c, Z3 5.1.0.0)

Each mode is one process. "before" is the pure-Z3 spend on the main thread
and on a fresh thread before the perturbation; "after" is the same on the
main thread and on two fresh threads after it.

| Mode | Perturbation (on a fresh thread unless noted) | Pure Z3 before (main / thread) | Pure Z3 after (main / threads) | Notes |
|---|---|---|---|---|
| 1 | 3000 unrelated Int constants, no solver | 72,089 / 72,053 | 72,053 / 72,053, 72,053 | no change |
| 2 | factoring search `p>1, q>1, p*q == 4093*4099, p<x`, rlimit 2M, one check | 72,089 / 72,053 | 72,053 / 72,053, 72,053 | search canceled at 2,000,027; no change; **no VERIFY message** |
| 3 | the same search, rlimit 50M, one check | 72,089 / 72,053 | 72,053 / 72,053, 72,053 | **`Failed to verify: m_cache.mk_unique(p) == p` (nlsat_solver.cpp:3178)**, then `unknown` at 50,000,027; no change in the spend |
| 5 | 3000 constants plus the search, rlimit 2M, one check | 72,089 / 72,053 | 72,053 / 72,053, 72,053 | VERIFY message **before** 2M units this time; no change |
| 8 | 3000 constants plus the search, rlimit 2M, two checks | 72,089 / 72,053 | 72,053 / 72,053, 72,053 | VERIFY; `unknown` at 2,000,027 and 4,000,027; no change |
| 9 | main thread: leak one block of 8, 24, 40, 56, 72, 104, 136, 200, 1000, 4096, 8192, 65536 bytes, two solves after each | 72,089 / 72,053 | 72,053 after every leak (24 solves) | heap-address shifts do not move the pure query |
| 14 | main thread: nelli path three times, pure Z3 after each | 72,089 / 72,053 | 72,053 every time; nelli path 72,124 all three | the nelli path alone, on the main thread, is stable and moves nothing |

Modes 4, 6, 7, 11, 12, 13 are written (`probe_s8cj_body.nim`) and not run.

**Probe 1** (`probe_s8cj_spend.nim`, run before the matrix, one process; each
"thread" line is a fresh thread running pure Z3 then the nelli path):

| Step | Pure Z3 | Nelli path |
|---|---|---|
| main #1 | 72,089 | 72,124 |
| main #2 | 72,089 | 72,124 |
| thread fresh #1 | 72,053 | 72,124 |
| thread fresh #2 | 72,053 | 72,124 |
| *malloc-only thread: 200,000 blocks of 16-160 bytes, 2062 kept* | | |
| thread after malloc-only #1 | 72,053 | 72,124 |
| thread after malloc-only #2 | 72,053 | **19,758,774** |
| main after malloc-only | 72,053 | **16,304,701** |
| *z3Work thread: 3000 constants plus the factoring search, rlimit 2M, two checks; VERIFY message; `unknown` at 4,000,027* | | |
| thread after z3 work #1 | **876,223** | 19,281,922 |
| thread after z3 work #2 | 876,223 | 15,649,702 |
| main after z3 work | 876,223 | 16,004,828 |
| sameThread (one thread: solve, solve, malloc-perturb, solve, solve, free, solve) | 876,223 ×5 | |
| thread last | 876,223 | 17,036,235 |
| main last | 876,223 | 14,819,740 |

All outcomes were `zsSat` / `some(true)` throughout; only the spend moved.

### Facts established

1. **The pure query is reproducible within a process history, address-independent, and not thread-specific.** Only the process's first solve differs (72,089 against 72,053, a 36-unit one-time initialisation effect; S8by's "72,162 against 72,126" is the same 36 units). Fresh threads, exited threads, 3000 interned symbols, canceled and completed nonlinear searches, the VERIFY failure and twelve heap-address shifts all leave it at 72,053.
2. **Something process-wide does move it**, and both measurements at once: in probe 1 the pure query went to 876,223 on the main thread as well as on fresh threads, and stayed there for the rest of the process. 876,223 is within 73 units of S8by's "876,296 ... by the order the query's constants were made in", so the moved state makes Z3 search as if `y` came before `x`.
3. **The nelli path is far more exposed than the pure one**: from 72,124 to 14.8M-19.7M, a different number on every call once moved (the pure query stays at one number once moved). It moved first (before the z3Work thread), and it moved on the main thread too, which S8by's note said stayed put.
4. **The move needs a combination.** Neither the malloc-only thread, nor the 3000-constant search, nor the nelli path alone (mode 14, main thread), nor the VERIFY failure moves anything on its own. In probe 1 the nelli path had run on fresh threads (four of them) before the malloc-only thread; in mode 14 it ran on the main thread only.
5. **The "function of the query alone" claims** (S8bm, S8bp, `queryTermOrder`'s doc comment, `concreteScratchCheck`'s doc comment, `tsymex_rfc0005_s8by_remainder.nim` header item (1) and (3)) are correct only within one process history, as S8by's remainder note already said. `s8by_remainder:189` (`check r.units == base.units`) compares two fresh threads after a settle sequence; it is deterministic in modes 1-14 and not in probe 1, so it fails whenever the process reaches the moved state, which the sweep's load evidently reaches (CI-03) and a cpp build reaches more often (INT-04). Nothing was changed in the test yet.
6. **nelli sets no Z3 global state.** `Z3_global_param_set`, `Z3_toggle_warning_messages`, `Z3_open_log`, `Z3_enable_trace` and `Z3_reset_memory` are called nowhere in `src/nelli`; `setGlobalParam` appears only in a comment (`runtime.nim:14165`). Every solver gets `random_seed = 0` and `rlimit`; no tactic configuration is set. Contexts are `Z3_mk_context_rc` with nim-z3's no-op error handler.

### The mechanism (second round, 2026-11-07, base `f560f280`)

Probe `s8cj/probe_s8cj_hist.nim` (one compile; the binary re-executes
itself once per mode, so every mode is a fresh process) prints, at every
measurement, the units, Z3's process-wide allocation counter
(`Z3_get_estimated_alloc_size`, looked up with `dynlib` since nim-z3 does
not bind it) and the raw addresses of `x` and `y`. Logs:
`s8cj/hist-{c,cpp}-z3-5.1.log`, `s8cj/hist-c-z3-4.13.4.log`. "pure" is
`solveQ` (Z3's own term order), "own" the own-context order (`scratchQ`,
or `translateQ`, which is `queryTermOrder` + `translate` + `querySolver`
with no nelli per-thread setup and gives the same figure minus the 71
units of the second, UNSAT, solve).

| Mode | What | Result (Z3 5.1, c) |
|---|---|---|
| 15 | six fresh threads, pure then own, nothing else | counter +17.3 MB per thread (each exited thread leaks its last `newContext()` through nim-z3's `currentZ3Ctx` threadvar); own moves at thread 4 (86.7 MB: 5,855,052), pure at thread 5 (104 MB: 876,228 then 876,223); main moves too |
| 15r | mode 15 with `setCurrentContext(nil)` before each thread exits | counter stays at 17.5-17.9 MB; **nothing moves** across six threads (72,053 / 72,124 every time) |
| 15p | six fresh threads, pure only | same as 15: the nelli path is not needed |
| 16 | probe 1 without the nelli path | malloc-only thread: counter unchanged, nothing moves; z3Work: +18.7 MB to 106 MB, pure moves to 876,223 for the rest of the process |
| 17 | **main thread only**, 1/2/4/8/16/32/64 live contexts | 1-2 live (34-52 MB): pure 72,053 (not the first-solve 72,089), own 72,124; 4 live (86 MB): own 5,856,872; 8-64 live (155 MB-1.1 GB): pure 876,223, own 5,854,994; **after freeing them (17.4 MB): 72,089 / 72,124 again** |
| 18a | `translateQ` on six threads | follows the own figure (5,854,923) |
| 18b | `querySolver` in the build context, no translation | follows the pure figure (876,223) |
| 19 | main thread, `free(malloc(1/4/32 MB))` | nothing (not Z3's allocations, not counted) |
| 20 | mode 15 under `mallopt(M_ARENA_MAX, 1)` | same as 15 |
| 21 | mode 15 with `M_MMAP_THRESHOLD` fixed | same as 15 |

`x < y` in every row: the addresses never mattered. Z3 4.13.4 (c) is the
same picture with its own figures: pure 26,653 (17 MB) / 26,622 (34-87 MB)
/ 24,968-23,883 (104 MB and above); own 26,693 / 913,469-930,289 (86 MB) /
911,591 (104 MB and above); mode 17 restores 26,653 / 26,693 on freeing.
S8by's "23,956 and 911,593 on 4.13.4" are these two regimes. cpp (Z3 5.1)
is identical to c, with thread 4 of mode 15 giving the own figure
19,683,525: the varying 14.8M-19.7M of probe 1.

**Where Z3 reads it (source, 5.1.0 tag).** The counter is
`memory::get_allocation_size()`; the tactic layer exposes it as the
`memory` probe (`tactic/probe.cpp`, megabytes), and the `max_memory`
parameter of a tactic is checked against it. nelli's solvers are
`Z3_mk_solver`, the strategic solver, which runs the tactic for the goal's
detected logic on the first check. For this query that is `mk_qfnia_tactic`
(`tactic/smtlogics/qfnia_tactic.cpp`):

- the preamble's `cofactor_term_ite` runs under `max_memory = 20` MB inside
  `skip_if_failed`: above 20 MB it is skipped. That is the 72,089 against
  72,053 regime (and S8by's "72,162 against 72,126"): the "one-time
  initialisation effect" of the first round was the process crossing 20 MB
  with its second context;
- the first branch of the `or_else`, `mk_qfnia_sat_solver` (`nla2bv`, then
  bit-blasting and a SAT solver under `max_memory = 100` MB, `max_conflicts
  = 500`), fails above 100 MB and the portfolio falls to `try_for(smt, 2000
  ms)`, then `try_for(nlsat, 3000 ms)`, then `smt` unbounded. That is the
  876k / 5.85M regime: the smt core's nonlinear search instead of the
  bit-blasted one, in either term order. Between about 86 and 100 MB the
  SAT stage starts and fails mid-run when its own allocations cross the
  line, at a point that depends on the exact count: hence the own order
  moving earlier than the pure one (its two contexts allocate more) and the
  varying figures (5,855,052 / 5,856,872 / 19,683,525) at the boundary;
- the portfolio also has **wall-clock** stages (`try_for` 2000 and 3000
  ms), so on a slow enough machine the unit count is not even a function of
  (query, process memory).

`mk_qfnra_tactic` chooses its whole sub-solver by the same probe (30 / 80 /
300 / 600 MB), `mk_qfbv_tactic` gates a simplification at 300 MB, and
`qflia`'s preamble has the same 20 MB `cofactor_term_ite`; nelli's BV64
lowering (`isOptimised`) and plain Int queries go through those. In any
process of real size (a walk's context alone is far above 100 MB) the
portfolio's bit-blasting stage never runs, and what the small test
processes measure is a different strategy from what a run uses.

### Conclusions

1. **Trigger:** the process's Z3 allocation count at the moment of the
   solve, read by the default solver's tactic strategy. Not threads, not
   addresses, not malloc arenas or mmap thresholds, not the VERIFY failure,
   not nelli's per-thread setup, not translation. Deterministic and
   reversible (mode 17).
2. **Not nelli-controllable in substance**: the count is every live Z3
   context in the process, nelli's and anyone else's (a consumer's own
   solvers, other threads), and the strategy's wall-clock stages are Z3's.
   The alternative, a solver built from an explicit tactic (`smt`, or
   `Z3_mk_simple_solver`), would make the spend memory-independent at the
   price of losing the portfolio's bit-blasting stage, which is what decides
   factoring queries in 72k rather than 876k-5.85M units, and of a walker
   version bump for every budget-sensitive verdict; S8r already runs the
   theory-free checks on the simple solver where 4.13.4 needs it. Not taken
   here; recorded under PRC-32 as the design alternative.
3. **Nelli-controllable in part, and fixed:** what grew the count in the
   tests and in any consumer with short-lived threads is a run's context
   outliving the run. `resetSymexRunState` makes the walk's context the
   thread's current one and nothing restored the previous one, so the
   context lived until the thread's next run or for ever on an exited
   thread (17 MB empty, plus the walk). `runSymex` now restores the
   previous current context after `runSymexCaught` returns and
   `runConcolicCollectImpl` restores it on every exit (`defer`, which
   CR-13's goto-exception caveat does not reach: neither entry has a
   nested `try`). Pinned by `tests/tsymex_0016_s8cj_runctx.nim` (RED on
   `f560f280`: the context stayed current; GREEN after).
4. **The invariant `s8by_remainder:189` can defend:** the outcome under a
   bound above both figures is the query's; the spend is equal between two
   fresh threads in the same process state. The test's threads now release
   their contexts before exiting (`setCurrentContext(nil)`, as mode 15r),
   so every comparison runs at one count and `check r.units == base.units`
   is exact rather than lucky. The header's items (1) and (3), and the doc
   comments of `queryTermOrder`, `ownContextSolver` and
   `concreteScratchCheck`, now say "the query and the process's Z3 memory"
   where they said "the query alone".
5. **Verdict trust is unchanged:** every outcome in every row was `zsSat`
   / `some(true)`; an rlimit cut is a cap (`zsUnknown` → `none(bool)` /
   decline), never a flipped verdict. What moves is precision under a
   budget, which already has one process-external axis (INT-43: the Z3
   build) and now has two more (process memory, and wall clock on a slow
   machine). A budget that is a multiple of the moved figure is the only
   budget that means the same thing in a test process and in a run.

## Item 2: Z3 5.1's `mk_unique` check (UPS-02, PND-10)

### Reproduced

Z3 5.1.0.0, c backend, podman image, pure Z3 through nim-z3, no nelli code:

```
(declare-const p Int) (declare-const q Int) (declare-const x Int)
(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207)) (assert (< p x))
(check-sat)
```

(`16777207 = 4093 * 4099`; the query is trivially SAT: `p = 4093, q = 4099,
x = 4094`.) With `rlimit = 50M` and `random_seed = 0` (mode 3):

```
ASSERTION VIOLATION
File: .../src/nlsat/nlsat_solver.cpp
Line: 3178
Failed to verify: m_cache.mk_unique(p) == p
5.1.0.0
Please file an issue ...
```

and the check returns `unknown` at 50,000,027 units. With `rlimit = 2M` the
message does not appear (mode 2, canceled first); with 3000 unused constants
declared before `p`, `q`, `x` it appears before 2M units (modes 5, 8). It
reproduced in every one of the four runs that reached it. S8by observed it on
`x * y` with `x, y < 200000`; S8by also reports 4.13.4 deciding the mode-3
query in 191,361 units, so on 5.1 this is a decision regression as well as
an internal-check failure.

**Reduction (`probe_s8cj_ups02.nim`, SMT-LIB text parsed with
`parseSmt2String`, Z3 5.1, c; log `s8cj/ups02-c-z3-5.1.log`):**

| Variant | Assertions | rlimit | VERIFY message | Result |
|---|---|---|---|---|
| full | `p>1, q>1, p*q = 16777207, p<x` | 50M | yes | `unknown (canceled)` at 50,000,027 |
| full, no `random_seed` | same | 50M | yes | same |
| **no-x** | `p>1, q>1, p*q = 16777207` | 50M | **yes** | `unknown (canceled)` at 50,000,020 |
| no-lower-bounds | `p*q = 16777207, p<x` | 50M | no | `sat` in 128 units |
| x-bounded | full plus `x < 100000` | 50M | yes | `unknown` at 50,000,034 |
| small-product | `p>1, q>1, p*q = 1022117, p<x` | 50M | yes | `unknown` at 50,000,027 |
| prime-product | `p>1, q>1, p*q = 16777213, p<x` (UNSAT, 2^24-3 is prime) | 50M | yes | `unknown` at 50,000,027 |
| full | same as full | 5M | yes | `unknown` at 5,000,027 |
| `nlsat.reorder = false` | | | not run | `Z3_EXCEPTION: unknown parameter 'nlsat.reorder'` as a solver param; the probe stopped here, so `smt.arith.nl.nra = false` did not run either |

So the standalone reproduction is **three assertions**:

```
(declare-const p Int) (declare-const q Int)
(assert (> p 1)) (assert (> q 1)) (assert (= (* p q) 16777207))
(check-sat)
```

Z3 5.1.0.0 prints the VERIFY failure and returns `unknown` at any rlimit from
5M to 50M, for a composite product (SAT: 4093 * 4099), for the smaller
composite 1022117 (SAT: S8by's own query decides it in 72k units once `p` and
`q` are bounded above), and for a prime (UNSAT). The lower bounds `p > 1,
q > 1` are necessary; without them Z3 answers at once. The message appears
once per check, early (before 5M units); the search then runs to its bound.
Not yet run: Z3 4.13.4 (`-i z3-4.13.4`; S8by reports 191,361 units there, no
message), cpp, the Z3 nightly, the parameter variants under their right
names (the nlsat parameters are reachable from the smt solver as
`smt.arith.nl.*`; `nlsat.*` is the tactic's module). The draft `UPS-02.md`
is not written; its body is the table above plus the source reading below.

### Where the check is, and what a failure does (from the 5.1.0 source)

- The two `VERIFY(m_cache.mk_unique(p) == p)` sites are both in
  `nlsat::solver::imp::reinit_cache(atom*)` (ineq-atom and root-atom
  branches), called from the no-argument `reinit_cache()`, whose only
  callers are in `reorder(unsigned sz, var const* p)` (twice, around
  `m_cache.reset()`). So the failure is in nlsat's variable reordering: after
  the cache is reset, an atom's polynomial is no longer the cache's unique
  representative, i.e. two atoms hold structurally equal polynomials as
  different objects.
- `VERIFY` is compiled into release builds (`util/debug.h`): it calls
  `notify_assertion_violation` (the message) and then
  `invoke_exit_action(ERR_UNREACHABLE)`. The default exit action is
  `exit`; **`Z3_mk_context_rc` sets it to `throw_exception`**
  (`api_context.cpp`), and nim-z3 makes every context with
  `Z3_mk_context_rc`, so in nelli a failed VERIFY throws
  `default_exception("unreachable")`.
- The throw unwinds through `nra_solver::check` (catches `z3_exception`;
  returns `l_undef` only if the limit is canceled, otherwise rethrows),
  `theory_lra` (no catch), `smt::context` (catches only `oom_exception`,
  around setup, not the search), to `_solver_check` in `api_solver.cpp`:
  `set_reason_unknown(ex)`, then `handle_exception(ex)` (sets the API error
  code `Z3_EXCEPTION`) **only if the limit is not canceled**, and returns
  `Z3_L_UNDEF` either way.
- Two `catch (...) { }` in `nla_grobner.cpp` (`grobner::operator()`) swallow
  everything, but the VERIFY is in nlsat, not grobner.

**PND-10, as far as the source shows.** The observed sequence (message, then
`unknown` at the bound with no API error) is the canceled path: the VERIFY
fires during `reorder` while the search is being cut by the rlimit, so the
exception is swallowed and the result is `l_undef`. A verdict *after* the
message is therefore `unknown` — `sxUnknown` in nelli, a decline. A
not-canceled VERIFY failure would set `Z3_EXCEPTION`, which nim-z3's
`checkErr` raises as `Z3OperationError`; `runSymex` turns a run that saw one
into `sxUnknown + ekZ3Error`. Caveat for the final answer: the own contexts
(`ownContextSolver` → `newContext()`) carry nim-z3's no-op handler rather than
`nelliZ3ErrorHandler`, so an error whose raise the C backend loses (S8ce) is
not counted there; and the Z3 5.1 release ships with `exit` as the default
action for any context not made with `_rc` (not nelli's case). Whether a
VERIFY failure can precede a `sat`/`unsat` in the same check (the exception
caught and the search continued inside Z3) has one candidate site, grobner's
`catch (...)`, which the nlsat site does not pass through. So: the verdict
after the message is not trusted because it is never a verdict; it is
`unknown`. This is a reading, not yet a test.


### Second round: the matrix (`s8cj/probe_s8cj_ups02b.nim`)

Solver params take the smt solver's names unprefixed (`arith.nl.nra`,
not `smt.arith.nl.nra`; `nlsat.*` is not a solver param at all and is
reachable only through `Z3_global_param_set`). `three` is the three-
assertion reduction; `prime` its UNSAT twin (16777213); `bounded-200k`
adds `p, q < 200000` (S8by's shape). Logs `s8cj/ups02b-*.log`.

| Variant (rlimit 50M unless noted) | Z3 5.1 (c) | Z3 4.13.4 (c) |
|---|---|---|
| full (with `p < x`) | VERIFY; `unknown (canceled)` 50,000,027, 30.7 s | `sat` 2,438,387, 1.5 s |
| three | VERIFY; `unknown (canceled)` 50,000,020, 27.8 s | `sat` 2,175,259, 1.4 s |
| three, rlimit 5M | VERIFY; `unknown (canceled)` 5,000,020, 2.5 s | `sat` 2,175,259 |
| prime (UNSAT) | VERIFY; `unknown (canceled)` 50,000,020 | `unknown (canceled)` 50,000,020, 24 s |
| bounded-200k | VERIFY; `unknown (canceled)` 50,000,034 | `sat` 22,300,690, 7.8 s |
| `arith.nl.nra = false` | VERIFY; `unknown (incomplete (theory arithmetic))` 444,699, 0.14 s | `sat` 2,175,259 |
| `arith.nl.grobner = false` | VERIFY; `unknown (canceled)` 50,000,020 | `sat` 2,175,259 |
| **`arith.nl.order = false`** | **three VERIFY messages; `unknown (unreachable)` 741,565, 0.2 s** | `sat` 2,175,259 |
| `random_seed = 1` | (c run: probe error, string given) cpp run: VERIFY; `unknown (unreachable)` 41,475,772, 12.8 s | `sat` 2,175,259 |
| global `nlsat.reorder = false` | VERIFY; `unknown (canceled)` 50,000,020 | `sat` 2,179,719 |
| global `nlsat.simplify_conflicts = false` | VERIFY; `unknown (canceled)` | `sat` 2,180,593 |
| global `nlsat.factor = false` | VERIFY; `unknown (canceled)` | `sat` 2,173,455 |
| global `nlsat.seed = 7` | VERIFY; `unknown (canceled)` | `sat` 2,172,712 |

So on 5.1 the failure is in every configuration that reaches nlsat,
`nlsat.reorder = false` included (the `reorder` site is reached from
elsewhere too, or the global did not reach the embedded solver); `arith.nl.order = false`
shows the **not-canceled path**: the VERIFY's exception reaches the API's
check before the limit is cut and comes back as `unknown` with
`reason_unknown = "unreachable"` at 741k units, with no `Z3_EXCEPTION`
raised through nim-z3's `check()` (which does not read the error code
after `Z3_solver_check`). 4.13.4 decides every SAT variant and prints
nothing; it decides the UNSAT prime no better than 5.1 (both cut at 50M).
Decision regression on 5.1 confirmed on every SAT variant. cpp (Z3 5.1,
`s8cj/ups02b-cpp-z3-5.1.log`) agrees with c row by row.

**PND-10, answered with a test.** Either path gives `unknown`: canceled
(the message, then the bound) or `unreachable` (the message, then the
exception). Neither is a verdict, so a verdict "after the message" does not
exist in one check; nelli maps both to `sxUnknown` (a decline).
`tests/tsymex_0016_s8cj_mkunique.nim` pins it through `symexFind` on `if p
> 1 and q > 1 and p * q == 16777207`, under `queryRLimit = 20M`, with fd 2
captured for the run: (1) never `sxUnsat` (the target is reachable); (2)
where the message was printed in this process, `sxUnknown`; (3) a `sxSat`
(4.13.4) carries a witness checked natively.

## Status of the slice

- Source: `runSymex` and `runConcolicCollectImpl` restore the previous
  current context (conclusion 3); doc comments of `queryTermOrder`,
  `ownContextSolver`, `concreteScratchCheck` corrected. No verdict changes,
  no walker version bump.
- Tests: `tsymex_rfc0005_s8by_remainder` (threads release their contexts,
  header corrected), new `tsymex_0016_s8cj_runctx` (RED then GREEN) and
  `tsymex_0016_s8cj_mkunique` (PND-10), both registered.
- `docs/rfc/0016-research/UPS-02.md` drafted (not filed).
- RFC rows PRC-32, CI-03, UPS-02, PND-10, INT-04, INT-43 updated.
- Not run: the Z3 nightly and the `z3` binary (item 2); every cpp pass of
  the tests (the coordinator runs cpp in the landing check).

## Test results (c backend, podman)

| Test | Z3 | Result |
|---|---|---|
| `tsymex_0016_s8cj_runctx` at `f560f280` (before the source fix) | 5.1 | RED: `Check failed: probe.ctxAfter` (the run's context stayed current), rc=1 |
| `tsymex_0016_s8cj_runctx` after the fix | 5.1 | GREEN, rc=0 |
| `tsymex_0016_s8cj_mkunique` | 5.1 | rc=0 (run before the test echoed its observation, so whether the message was printed in that process is not in the log; the matrix says it is, on every 5.1 check of this shape) |
| `tsymex_0016_s8cj_mkunique` | 4.13.4 | rc=0; `status=sxRaised`, the target query `Z3: canceled` under `queryRLimit = 20M`, no message. The walk's target query is not the bare reduction (nelli's lowering adds the overflow conditions of `p * q`, and the raise path reaches the label first), so (3) did not fire on 4.13.4 either; (1) held |
| `tsymex_rfc0005_s8by_remainder` with the released contexts | 5.1 | all 12 checks `[OK]`, rc=0 |
