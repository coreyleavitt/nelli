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

### Hypotheses, with the evidence

- **Rejected: heap layout / malloc arenas.** Mode 9 (twelve address shifts, no change) and probe 1's `sameThread` row (malloc perturbation on the solving thread, no change). Z3's nonlinear search on this query is not pointer-ordered. The first-solve 36 units is initialisation, not addresses.
- **Rejected: Z3 global params, nelli-set.** Fact 6.
- **Rejected: the `mk_unique` failure or the 3000 constants as the trigger.** Modes 3, 5, 8.
- **Open, leading: Z3 process-wide state reached by nelli's per-thread setup across several threads.** The nelli path's first use on a thread builds per-thread probe contexts (`probeContext()` in `ensureIntDivDeclKinds`, `theoryFreeSimple`, the `seqCapKinds` probes) that live for the thread; probe 1 created four such threads, then the malloc-only thread, and the fifth nelli thread moved. Candidates inside Z3 that are process-wide and fed by allocation or by live contexts: the `memory` module's allocation counters and high-watermark checks (`memory::get_allocation_size`, `above_high_watermark`), which some heuristics read; the global `rational`/`mpq` manager; `symbol` table growth. The varying-per-call figure (14.8M-19.7M) is the strongest clue: something read during the search that is not a function of the query, such as a memory statistic or a timer.
- **Open: translation.** The nelli path differs from the pure one only by `translate` into the own context (one `ast_translation` over `queryTermOrder`'s vector) and `querySolver`'s params; the moved pure query (876k, one fixed number) and the moved nelli path (14-19M, varying) differ in kind, so the translation step, not just Z3, is involved in the larger figure.

### Next experiments, in order

1. **Mode 15:** probe 1 without the malloc-only thread and without z3Work: six fresh threads each running pure Z3 then the nelli path. Does the nelli path move by thread repetition alone? (Isolates "several threads' per-thread setup" from "malloc thread".)
2. **Mode 16:** probe 1 without the nelli path (pure Z3 on threads, then the malloc-only thread, then z3Work). Does the pure 876k move need the nelli path to have run?
3. With the minimal trigger known, bisect the nelli path: (a) `ownContextSolver` with `translate` but `newSolver` params only; (b) `querySolver` in the walk context with no translation; (c) `probeContext()` alone on N threads, then the pure query. Expose `Z3_get_estimated_alloc_size` in nim-z3 (not in `ffi.nim` today) and print it at each step: if the move tracks the counter, it is the memory-accounting hypothesis.
4. Run the trigger under `MALLOC_ARENA_MAX=1` (`mallopt(M_ARENA_MAX, 1)` is already in `probe_s8cj_spend.nim` under `-d:s8cjArena1`) and on cpp, then on Z3 4.13.4 (`-i z3-4.13.4`), since S8by reports 4.13.4 moving alike (26,695 to 911,593).
5. Only then the fix: if the moved state is a Z3 statistic or counter, the design choice is between a fresh *process*-equivalent reset (`Z3_reset_memory` is only legal with no live contexts, so not in a walk) and accepting history-dependence with budgets set at a multiple of the moved figure; `s8by_remainder:189` then pins what is invariant, which the matrix says is: outcome under a bound above both figures, and spend equality between two fresh threads *in the same process state* (modes 1-14), never across a state move. INT-43's 1.66× between Z3 builds is a separate axis (same query, different build) and is not explained by anything here.

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

## Status of the slice

- No source or test change; no walker version bump. `s8by_remainder:189`
  unchanged (its invariant is named under "Next experiments" item 5).
- RFC rows not yet edited: PRC-32, CI-03, UPS-02, PND-10, INT-04, INT-43.
